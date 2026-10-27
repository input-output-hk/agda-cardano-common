{-# OPTIONS --guardedness #-}

-- Actual outbound/coordinator executions plus one startup execution for each
-- selected physical handler. New handle/promise writes are retained in O;
-- they are not erased through the older pre-handshake wrapper invariant.
module ConnectionManagement.Properties.MuxHandlerSupervision (Result : Set) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Protocol)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.OutboundHandlerSupervision as Base
import ConnectionManagement.Properties.HandlerSupervision as Handler
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.CMShutdown as CloseProof
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.MuxHandlerSupervision as Model
module W = Model Result
module Startup = W.Startup
import ConnectionManagement.Properties.MuxStartup as StartupProperties
module StartupProof = StartupProperties Result
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply

STrace : Startup.State → Startup.State → Set
STrace p q = Σ (List Startup.Action) (λ as → Startup.Executes p as q)
record Paths (before after : W.State) : Set where
  constructor paths
  field machine : Base.OTrace (W.source before) (W.source after)
        coordinator : Base.CTrace (B.shutdown (W.base before)) (B.shutdown (W.base after))
        last-wait : Handler.LastValid (B.shutdown (W.base before)) → Handler.LastValid (B.shutdown (W.base after))
        startups : ∀ selected → STrace (W.startupAt selected before) (W.startupAt selected after)
open Paths public

fromFrame : Maybe W.Frame → Startup.State
fromFrame nothing = Startup.initial
fromFrame (just f) = W.startup f
startup-view : ∀ selected s → W.startupAt selected s ≡ fromFrame (lookup selected (W.frames s))
startup-view selected s with lookup selected (W.frames s)
... | nothing = refl
... | just f = refl
same-frames : ∀ before after → W.frames before ≡ W.frames after →
  ∀ selected → W.startupAt selected before ≡ W.startupAt selected after
same-frames before after eq selected = trans (startup-view selected before)
  (trans (cong fromFrame (cong (lookup selected) eq)) (sym (startup-view selected after)))
startup-found : ∀ selected s f → lookup selected (W.frames s) ≡ just f → W.startupAt selected s ≡ W.startup f
startup-found selected s f found = trans (startup-view selected s) (cong fromFrame found)
startup-missing : ∀ selected s → lookup selected (W.frames s) ≡ nothing → W.startupAt selected s ≡ Startup.initial
startup-missing selected s missing = trans (startup-view selected s) (cong fromFrame missing)
put-same : ∀ owner f s → W.startupAt owner (W.setFrame owner f s) ≡ W.startup f
put-same owner f s = trans (startup-view owner (W.setFrame owner f s)) (cong fromFrame (lookup-put owner f (W.frames s)))
put-other : ∀ owner selected f s → selected ≢ owner →
  W.startupAt selected (W.setFrame owner f s) ≡ W.startupAt selected s
put-other owner selected f s apart = trans (startup-view selected (W.setFrame owner f s))
  (trans (cong fromFrame (lookup-put-other owner selected f (W.frames s) apart)) (sym (startup-view selected s)))

trace-left : ∀ {p p′ q} → p ≡ p′ → STrace p′ q → STrace p q
trace-left refl path = path
trace-right : ∀ {p q q′} → q ≡ q′ → STrace p q → STrace p q′
trace-right refl path = path
same-startups : ∀ before after → W.frames before ≡ W.frames after →
  ∀ selected → STrace (W.startupAt selected before) (W.startupAt selected after)
same-startups before after eq selected = trace-right (same-frames before after eq selected) ([] , Startup.done)
idle : ∀ s → Paths s s
idle s = paths ([] , O.done) ([] , Close.done) (λ wait → wait) (λ selected → [] , Startup.done)

-- Updating one capture exposes one actual startup trace, or stutters for a
-- different selected worker. No equality of complete source machines is used.
put-startups : ∀ owner f s → STrace (W.startupAt owner s) (W.startup f) →
  ∀ selected → STrace (W.startupAt selected s) (W.startupAt selected (W.setFrame owner f s))
put-startups owner f s path selected with selected ≟ owner
... | yes refl = trace-right (sym (put-same owner f s)) path
... | no apart = trace-right (sym (put-other owner selected f s apart)) ([] , Startup.done)
put-paths : ∀ owner f s → STrace (W.startupAt owner s) (W.startup f) → Paths s (W.setFrame owner f s)
put-paths owner f s path = paths ([] , O.done) ([] , Close.done) (λ wait → wait) (put-startups owner f s path)
source-paths : ∀ action s {c} → O.advance action (W.source s) ≡ just c → Paths s (W.setSource c s)
source-paths action s {c} eq = paths (action ∷ [] , O.next eq O.done) ([] , Close.done) (λ wait → wait)
  (same-startups s (W.setSource c s) refl)
base-paths : ∀ s b → Base.Paths (W.base s) b → Paths s (record s { base = b })
base-paths s b (Base.paths op cp wait) = paths op cp wait (same-startups s (record s { base = b }) refl)
birth-paths : ∀ birth s → Paths s (W.noteBirth birth s)
birth-paths nothing s = idle s
birth-paths (just (w , origin)) s = paths ([] , O.done) ([] , Close.done) (λ wait → wait)
  (same-startups s (W.noteBirth (just (w , origin)) s) refl)

append-startup : ∀ {p as q bs r} → Startup.Executes p as q → Startup.Executes q bs r → Startup.Executes p (as ++ bs) r
append-startup Startup.done tail = tail
append-startup (Startup.next eq path) tail = Startup.next eq (append-startup path tail)
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) (cs , cp) wait first) (paths (bs , oq) (ds , cq) next second) =
  paths (as ++ bs , O.append op oq) (cs ++ ds , Handler.append-close cp cq)
    (λ valid → next (wait valid))
    (λ selected → let left = first selected; right = second selected in
      proj₁ left ++ proj₁ right , append-startup (proj₂ left) (proj₂ right))

inherit-projects : ∀ action s {s′} → W.inherit action s ≡ just s′ → Paths s s′
inherit-projects action s eq with W.baseAllowed action s ∧ W.birthFresh (W.birth action (W.base s)) (W.origins s)
... | false = case eq of λ ()
... | true with B.step action (W.base s) in advanced
...   | nothing = case eq of λ ()
...   | just b = case just-injective eq of λ { refl →
  compose (base-paths s b (Base.step-projects action (W.base s) advanced))
    (birth-paths (W.birth action (W.base s)) (record s { base = b })) }

negotiate-projects : ∀ w ps flow s {s′} → W.negotiateReturned w ps flow s ≡ just s′ → Paths s s′
negotiate-projects w ps flow s eq with lookup w (B.threads (W.base s)) |
  lookup w (W.origins s) | lookup w (W.frames s) in absent
... | just t | just origin | nothing with H.phase t
...   | H.handshaking = case just-injective eq of λ { refl →
  put-paths w (W.frame (H.captured t) origin ps flow W.returnedSuccess Startup.initial) s
    (trace-left (startup-missing w s absent) ([] , Startup.done)) }
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.maskedSetup = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.caughtCancellation err = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.cancellationPublished err = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.bodyExited err = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.finalizing err = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
negotiate-projects w ps flow s eq | nothing | origin | previous = case eq of λ ()
negotiate-projects w ps flow s eq | just t | nothing | previous = case eq of λ ()
negotiate-projects w ps flow s eq | just t | just origin | just previous = case eq of λ ()

allocate-projects : ∀ w hid mid s {s′} → W.allocate w hid mid s ≡ just s′ → Paths s s′
allocate-projects w hid mid s eq with lookup w (W.frames s) in found
... | nothing = case eq of λ ()
... | just f with W.progress f
...   | W.returnedSuccess with O.advance (O.inbound (M.igStep (W.allocationAction f hid mid))) (W.source s) in advanced
...     | nothing = case eq of λ ()
...     | just c = case just-injective eq of λ { refl →
  compose (source-paths (O.inbound (M.igStep (W.allocationAction f hid mid))) s advanced)
    (put-paths w (record f { progress = W.handleAllocated hid mid }) (W.setSource c s)
      (trace-left (startup-found w (W.setSource c s) f found) ([] , Startup.done))) }
allocate-projects w hid mid s eq | just f | W.handleAllocated oldHandle oldMux = case eq of λ ()
allocate-projects w hid mid s eq | just f | W.promisePublished oldHandle oldMux = case eq of λ ()

publish-projects : ∀ w s {s′} → W.publish w s ≡ just s′ → Paths s s′
publish-projects w s eq with lookup w (W.frames s) in found
... | nothing = case eq of λ ()
... | just f with W.progress f
...   | W.handleAllocated hid mid with O.advance
  (O.inbound (M.handlerPublication w (Shared.negotiated hid (W.flow f)) M.resultWritten)) (W.source s) in advanced |
  Startup.step Startup.observePublication (W.startup f) in progressed
...     | just c | just next = case just-injective eq of λ { refl →
  compose (source-paths (O.inbound (M.handlerPublication w (Shared.negotiated hid (W.flow f)) M.resultWritten)) s advanced)
    (put-paths w (record f { progress = W.promisePublished hid mid; startup = next }) (W.setSource c s)
      (trace-left (startup-found w (W.setSource c s) f found)
        (Startup.observePublication ∷ [] , Startup.next progressed Startup.done))) }
publish-projects w s eq | just f | W.handleAllocated hid mid | nothing | startupResult = case eq of λ ()
publish-projects w s eq | just f | W.handleAllocated hid mid | just c | nothing = case eq of λ ()
publish-projects w s eq | just f | W.returnedSuccess = case eq of λ ()
publish-projects w s eq | just f | W.promisePublished hid mid = case eq of λ ()

startup-projects : ∀ w action s {s′} → W.advanceStartup w action s ≡ just s′ → Paths s s′
startup-projects w action s eq with lookup w (W.frames s) in found
... | nothing = case eq of λ ()
... | just f with W.progress f | W.startupAllowed action s
...   | W.promisePublished hid mid | true with Startup.step action (W.startup f) in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl →
  put-paths w (record f { startup = next }) s
    (trace-left (startup-found w s f found) (action ∷ [] , Startup.next advanced Startup.done)) }
startup-projects w action s eq | just f | W.returnedSuccess | allowed = case eq of λ ()
startup-projects w action s eq | just f | W.handleAllocated hid mid | allowed = case eq of λ ()
startup-projects w action s eq | just f | W.promisePublished hid mid | false = case eq of λ ()

step-projects : ∀ a s {s′} → W.step a s ≡ just s′ → Paths s s′
step-projects (W.run action) s eq = inherit-projects action s eq
step-projects (W.negotiate w ps flow) s eq = negotiate-projects w ps flow s eq
step-projects (W.allocateHandle w hid mid) s eq = allocate-projects w hid mid s eq
step-projects (W.publishSuccess w) s eq = publish-projects w s eq
step-projects (W.startupStep w action) s eq = startup-projects w action s eq
exec-projects : ∀ {s actions s′} → W.Executes s actions s′ → Paths s s′
exec-projects {s = s} W.done = idle s
exec-projects (W.next {s = s} {a = a} eq path) = compose (step-projects a s eq) (exec-projects path)

-- True initialization retains the original outbound configuration and starts
-- every selected worker at an empty, unadopted startup state.
initial-base : ∀ c {s} → W.initial c ≡ just s → B.initial c ≡ just (W.base s)
initial-base c eq with IG.handles (IG.execution (M.inboundGovernor (O.core c))) |
  IG.muxes (IG.execution (M.inboundGovernor (O.core c))) | B.initial c
... | [] | [] | just b = case just-injective eq of λ { refl → refl }
... | h ∷ hs | muxes | base = case eq of λ ()
... | [] | m ∷ ms | base = case eq of λ ()
... | [] | [] | nothing = case eq of λ ()
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c initialized = Base.initial-source c (initial-base c initialized)
initial-startup : ∀ c {s} → W.initial c ≡ just s → ∀ selected → W.startupAt selected s ≡ Startup.initial
initial-startup c eq selected with IG.handles (IG.execution (M.inboundGovernor (O.core c))) |
  IG.muxes (IG.execution (M.inboundGovernor (O.core c))) | B.initial c
... | [] | [] | just b = case just-injective eq of λ { refl → refl }
... | h ∷ hs | muxes | base = case eq of λ ()
... | [] | m ∷ ms | base = case eq of λ ()
... | [] | [] | nothing = case eq of λ ()

startup-from-initial : ∀ {c start actions s} → W.initial c ≡ just start →
  W.Executes start actions s → ∀ selected → STrace Startup.initial (W.startupAt selected s)
startup-from-initial {c} initialized path selected =
  trace-left (sym (initial-startup c initialized selected)) (startups (exec-projects path) selected)
monitoring-from-initial : ∀ {c start actions s} → W.initial c ≡ just start →
  W.Executes start actions s → ∀ selected muxer demuxer →
  Startup.phase (W.startupAt selected s) ≡ Startup.monitoring muxer demuxer →
  StartupProof.Pair muxer demuxer (Startup.pool (W.startupAt selected s)) ×
  StartupProof.PoolTrace Startup.Pool.initial (Startup.pool (W.startupAt selected s))
monitoring-from-initial initialized path selected muxer demuxer phase with startup-from-initial initialized path selected
... | actions , execution = StartupProof.monitoring-from-initial muxer demuxer execution phase

-- Closing still depends on the original physical handler-result table. Startup
-- engine results do not replace its observed Async results or widen the census.
closed-from-initial : ∀ {c start actions s} → W.initial c ≡ just start →
  W.Executes start actions s → Close.phase (B.shutdown (W.base s)) ≡ Close.closed →
  Close.remaining (B.shutdown (W.base s)) ≡ [] × Handler.PhysicalWait (B.shutdown (W.base s))
closed-from-initial {c} initialized path closed with exec-projects path
... | paths sourceTrace (actions , cp) wait startupTraces =
  proj₁ (CloseProof.closed-from-initial
    (subst (λ first → Close.Executes first actions _) (Base.initial-coordinator c (initial-base c initialized)) cp) closed) ,
  wait (Base.initial-last c (initial-base c initialized)) closed

-- All new allocation/publication writers remain in the actual O trace, so
-- capture and supply obligations retain their existing precise premises.
captures-preserves : ∀ {s actions s′} → Capture.Captures (W.source s) →
  W.Executes s actions s′ → Capture.Captures (W.source s′)
captures-preserves valid path = Capture.exec-preserves valid (proj₂ (machine (exec-projects path)))
runtime-supply-preserves : ∀ {s actions s′} → Supply.Valid (W.source s) →
  W.Executes s actions s′ → Supply.Valid (W.source s′)
runtime-supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
from-initial-captures : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start →
  W.Executes start actions s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = captures-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) path
from-initial-supply : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start →
  SupplyBounds (M.world c) → W.Executes start actions s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounded path = runtime-supply-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounded)) path

-- One actual source publication and one startup observation occur together.
-- The retained frame fixes the original key, origin, descriptors and flow;
-- nothing here reinterprets the current mutable CM entry as its birth identity.
record Publication (w : WorkerId) (before after : W.State) : Set where
  constructor publication
  field
    originalFrame : W.Frame
    allocatedHandle : HandleId
    allocatedMux : MuxId
    sourceAfter : O.Configuration
    startupAfter : Startup.State
    found : lookup w (W.frames before) ≡ just originalFrame
    allocated-before : W.progress originalFrame ≡ W.handleAllocated allocatedHandle allocatedMux
    actual-publication : O.advance
      (O.inbound (M.handlerPublication w (Shared.negotiated allocatedHandle (W.flow originalFrame)) M.resultWritten))
      (W.source before) ≡ just sourceAfter
    actual-startup-observation : Startup.step Startup.observePublication (W.startup originalFrame) ≡ just startupAfter
    after-shape : after ≡ W.setFrame w
      (record originalFrame { progress = W.promisePublished allocatedHandle allocatedMux; startup = startupAfter })
      (W.setSource sourceAfter before)
open Publication public

publication-observation : ∀ w s {s′} → W.step (W.publishSuccess w) s ≡ just s′ → Publication w s s′
publication-observation w s eq with lookup w (W.frames s) in found
... | nothing = case eq of λ ()
... | just f with W.progress f in progress
...   | W.handleAllocated hid mid with O.advance
  (O.inbound (M.handlerPublication w (Shared.negotiated hid (W.flow f)) M.resultWritten)) (W.source s) in advanced |
  Startup.step Startup.observePublication (W.startup f) in progressed
...     | just c | just next = case just-injective eq of λ { refl →
  publication f hid mid c next found progress advanced progressed refl }
publication-observation w s eq | just f | W.handleAllocated hid mid | nothing | startupResult = case eq of λ ()
publication-observation w s eq | just f | W.handleAllocated hid mid | just c | nothing = case eq of λ ()
publication-observation w s eq | just f | W.returnedSuccess = case eq of λ ()
publication-observation w s eq | just f | W.promisePublished hid mid = case eq of λ ()

-- A mux child's result publication cannot fabricate its parent's Async result:
-- the physical parent registry is unchanged by every startup-only transition.
startup-parent-registry : ∀ w action s {s′} → W.step (W.startupStep w action) s ≡ just s′ →
  B.threads (W.base s′) ≡ B.threads (W.base s)
startup-parent-registry w action s eq with lookup w (W.frames s)
... | nothing = case eq of λ ()
... | just f with W.progress f | W.startupAllowed action s
...   | W.promisePublished hid mid | true with Startup.step action (W.startup f)
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → refl }
startup-parent-registry w action s eq | just f | W.returnedSuccess | allowed = case eq of λ ()
startup-parent-registry w action s eq | just f | W.handleAllocated hid mid | allowed = case eq of λ ()
startup-parent-registry w action s eq | just f | W.promisePublished hid mid | false = case eq of λ ()
