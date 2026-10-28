{-# OPTIONS --guardedness #-}

-- Actual typed dequeue/source-monitor effects and selected physical-pool traces.
-- Monitor finish is separate from parent Async result, pool close and buffer IO.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxResultMonitor (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (does)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain hiding (job; worker)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import Data.Nat as Nat
import ConnectionManagement.MuxResultMonitor as Monitor
module W = Monitor isBearerClosed
import ConnectionManagement.MuxProtocolJobs as P
module U = P.U
module Pool = P.Pool
import ConnectionManagement.Properties.MuxProtocolJobs as Base
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply

record Paths (before after : W.State) : Set where
  constructor paths
  field machine : Base.OTrace (W.source before) (W.source after)
        pools : ∀ selected → Base.PTrace (W.poolAt selected before) (W.poolAt selected after)
open Paths public
from-base : ∀ before after → Base.Paths (W.base before) (W.base after) → Paths before after
from-base before after path = paths (Base.machine path) (Base.pools path)
idle : ∀ s → Paths s s
idle s = from-base s s (Base.idle (W.base s))
pc-paths : ∀ w pc s → Paths s (W.setPC w pc s)
pc-paths w pc s = from-base s (W.setPC w pc s) (Base.idle (W.base s))
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) first) (paths (bs , oq) second) = paths
  (as ++ bs , O.append op oq) (λ selected → let left = first selected; right = second selected in
    proj₁ left ++ proj₁ right , Base.append-pools (proj₂ left) (proj₂ right))
source-step : ∀ action s {c} → O.advance (O.inbound (M.igStep action)) (W.source s) ≡ just c → Paths s (W.setSource c s)
source-step action s eq = from-base s (W.setSource _ s) (Base.source-step (O.inbound (M.igStep action)) (W.base s) eq)
via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → Paths s s′
via-projects action s eq with O.advance (O.inbound (M.igStep action)) (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → source-step action s advanced }
inherit-projects : ∀ action s {s′} → W.inherit action s ≡ just s′ → Paths s s′
inherit-projects action s eq with W.delegateAllowed action s
... | false = case eq of λ ()
... | true with P.step action (W.base s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → from-base s (record s { base = p }) (Base.step-projects action (W.base s) advanced) }
select-projects : ∀ w s {s′} → W.selectHead w s ≡ just s′ → Paths s s′
select-projects w s eq with W.pcAt w s | W.ownerContext w s
... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s)
...   | just m | true | item ∷ rest with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → from-base s _ (Base.pool-step w f Pool.consumeCompletion (W.base s) advanced) }
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopping | _ = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopped | _ = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.failed err | _ = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.readActive tr = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterStart n = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.forkPending n = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterFailure = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.tracerFailed n = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
select-projects w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
select-projects w s eq | W.waiting | nothing = case eq of λ ()
select-projects w s eq | W.selected item | _ = case eq of λ ()
select-projects w s eq | W.responderTracing result | _ = case eq of λ ()
select-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
select-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
select-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
select-projects w s eq | W.finished outcome | _ = case eq of λ ()

pc-after : ∀ w pc {before after} → Paths before after → Paths before (W.setPC w pc after)
pc-after w pc {after = after} path = compose path (pc-paths w pc after)
protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → Paths s s′
protocol-source-projects w mid Mux.responderJob n outcome s eq with W.muxAt mid s
... | nothing = case eq of λ ()
... | just m with W.legacyMatches n outcome (Mux.completions m)
...   | false = case eq of λ ()
...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → pc-after w (W.responderTracing outcome) (via-projects (IG.monitorCompletion mid) s advanced) }
protocol-source-projects w mid Mux.initiatorJob n clean s eq = case just-injective eq of λ { refl → pc-paths w (W.initiatorTracing clean) s }
protocol-source-projects w mid Mux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → pc-after w (W.initiatorTracing (errored err)) (via-projects (IG.recordMuxFailure mid err) s advanced) }
handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → Paths s s′
handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
...   | true | just m with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned = protocol-source-projects w mid dir n outcome s eq
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopping | _ = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopped | _ = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.failed err | _ = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.readActive tr = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterStart k = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.forkPending k = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterFailure = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.tracerFailed k = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | nothing | _ = case eq of λ ()
handle-protocol-projects w dir n gen outcome s eq | just _ | nothing = case eq of λ ()
record-finish-projects : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → Paths s s′
record-finish-projects w outcome s eq with W.ownerContext w s
... | nothing = case eq of λ ()
... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → pc-after w (W.deadReady outcome) (via-projects (W.statusAction outcome mid) s advanced) }
handle-projects : ∀ w s {s′} → W.handleHead w s ≡ just s′ → Paths s s′
handle-projects w s eq with W.pcAt w s
... | W.selected (Types.protocolCompletion dir n gen outcome) = handle-protocol-projects w dir n gen outcome s eq
... | W.selected (Types.infraMuxer err) = record-finish-projects w (W.failed err) s eq
... | W.selected (Types.infraDemuxer err) = record-finish-projects w (W.demuxFinish w err s) s eq
... | W.waiting = case eq of λ ()
... | W.responderTracing _ = case eq of λ ()
... | W.initiatorTracing _ = case eq of λ ()
... | W.deadReady _ = case eq of λ ()
... | W.deadTracing _ = case eq of λ ()
... | W.finished _ = case eq of λ ()
trace-projects : ∀ sample w s {s′} → W.traceSource sample w s ≡ just s′ → Paths s s′
trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s
... | true | just (f , mid) with sample
...   | true = via-projects (IG.sampleTracer mid) s eq
...   | false = via-projects (IG.commitTracer mid) s eq
trace-projects sample w s eq | false | _ = case eq of λ ()
trace-projects sample w s eq | true | nothing = case eq of λ ()
finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → Paths s s′
finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
... | just m with Mux.callback m
...   | Mux.returned = case just-injective eq of λ { refl → pc-paths w (W.waiting) s }
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
... | just m with Mux.callback m
...   | Mux.afterFailure = case just-injective eq of λ { refl → pc-paths w (W.deadReady (W.failed err)) s }
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | Mux.returned = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
... | just m with Mux.callback m
...   | Mux.returned = case just-injective eq of λ { refl → pc-paths w (W.waiting) s }
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
... | just m with Mux.callback m
...   | Mux.returned = case just-injective eq of λ { refl → pc-paths w (W.deadReady (W.failed err)) s }
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.readActive tr = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.commitTrace active tr = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.afterStart n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.forkPending n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.afterFailure = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | Mux.tracerFailed n = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing clean | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.responderTracing (errored err) | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.initiatorTracing result | nothing = case eq of λ ()
finish-protocol-projects w s eq | W.waiting | _ = case eq of λ ()
finish-protocol-projects w s eq | W.selected item | _ = case eq of λ ()
finish-protocol-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
finish-protocol-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
finish-protocol-projects w s eq | W.finished outcome | _ = case eq of λ ()

start-dead-projects : ∀ w s {s′} → W.startDead w s ≡ just s′ → Paths s s′
start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
...   | just m with W.finishMatches outcome (Mux.status m) | W.deadAction outcome (Mux.callback m) mid
...     | true | just action with W.viaSource action s in advanced
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → pc-after w (W.deadTracing outcome) (via-projects action s advanced) }
start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
start-dead-projects w s eq | W.deadReady outcome | nothing = case eq of λ ()
start-dead-projects w s eq | W.waiting | _ = case eq of λ ()
start-dead-projects w s eq | W.selected item | _ = case eq of λ ()
start-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
start-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
start-dead-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
start-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()
finish-dead-projects : ∀ w s {s′} → W.finishMux w s ≡ just s′ → Paths s s′
finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
...   | just m with Mux.callback m | W.finishMatches outcome (Mux.status m)
...     | Mux.returned | true = case just-injective eq of λ { refl → pc-paths w (W.finished outcome) s }
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.readActive tr | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.commitTrace active tr | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterStart n | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.forkPending n | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterFailure | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.tracerFailed n | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.returned | false = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
finish-dead-projects w s eq | W.deadTracing outcome | nothing = case eq of λ ()
finish-dead-projects w s eq | W.waiting | _ = case eq of λ ()
finish-dead-projects w s eq | W.selected item | _ = case eq of λ ()
finish-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
finish-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
finish-dead-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
finish-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()

step-projects : ∀ action s {s′} → W.step action s ≡ just s′ → Paths s s′
step-projects (W.run action) s eq = inherit-projects action s eq
step-projects (W.consume w) s eq = select-projects w s eq
step-projects (W.handleSelected w) s eq = handle-projects w s eq
step-projects (W.sampleTracer w) s eq = trace-projects true w s eq
step-projects (W.commitTracer w) s eq = trace-projects false w s eq
step-projects (W.finishProtocolTrace w) s eq = finish-protocol-projects w s eq
step-projects (W.beginDead w) s eq = start-dead-projects w s eq
step-projects (W.finishDead w) s eq = finish-dead-projects w s eq
exec-projects : ∀ {s actions s′} → W.Executes s actions s′ → Paths s s′
exec-projects {s = s} W.done = idle s
exec-projects (W.next {s = s} {a = action} eq path) = compose (step-projects action s eq) (exec-projects path)
initial-base : ∀ c {s} → W.initial c ≡ just s → P.initial c ≡ just (W.base s)
initial-base c eq with P.initial c
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c initialized = Base.initial-source c (initial-base c initialized)
initial-pool : ∀ c {s} → W.initial c ≡ just s → ∀ selected → W.poolAt selected s ≡ Pool.initial
initial-pool c initialized selected = Base.initial-pool c (initial-base c initialized) selected
pool-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → Base.PTrace Pool.initial (W.poolAt selected s)
pool-from-initial {c} initialized path selected = Base.trace-left (sym (initial-pool c initialized selected)) (pools (exec-projects path) selected)
captures-preserves : ∀ {s actions s′} → Capture.Captures (W.source s) → W.Executes s actions s′ → Capture.Captures (W.source s′)
captures-preserves valid path = Capture.exec-preserves valid (proj₂ (machine (exec-projects path)))
supply-preserves : ∀ {s actions s′} → Supply.Valid (W.source s) → W.Executes s actions s′ → Supply.Valid (W.source s′)
supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
from-initial-captures : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → W.Executes start actions s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = captures-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) path
from-initial-supply : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → SupplyBounds (M.world c) → W.Executes start actions s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounded path = supply-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounded)) path

-- Exact local PC updates retain the captured typed value independently of any
-- subsequent result publication, job deregistration or new generation.
pcOf : Maybe W.PC → W.PC
pcOf nothing = W.waiting
pcOf (just pc) = pc
pc-view : ∀ w s → W.pcAt w s ≡ pcOf (lookup w (W.pcs s))
pc-view w s with lookup w (W.pcs s)
... | nothing = refl
... | just pc = refl
pc-put : ∀ w pc s → W.pcAt w (W.setPC w pc s) ≡ pc
pc-put w pc s = trans (pc-view w (W.setPC w pc s)) (cong pcOf (lookup-put w pc (W.pcs s)))
via-observation : ∀ action s {s′} → W.viaSource action s ≡ just s′ →
  O.advance (O.inbound (M.igStep action)) (W.source s) ≡ just (W.source s′)
via-observation action s eq with O.advance (O.inbound (M.igStep action)) (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → refl }
record Dequeue (w : WorkerId) (before after : W.State) : Set where
  constructor dequeue
  field ownerFrame : U.Frame
        capturedMux : MuxId
        head : Types.TypedResult
        tail : List Types.TypedResult
        poolAfter : Pool.State
        waiting-before : W.pcAt w before ≡ W.waiting
        context-before : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        original-queue : Pool.completions (W.poolAt w before) ≡ head ∷ tail
        actual-consumption : Pool.step Pool.consumeCompletion (W.poolAt w before) ≡ just poolAfter
        after-shape : after ≡ W.setPC w (W.selected head) (W.setPool w ownerFrame poolAfter before)
        captured-after : W.pcAt w after ≡ W.selected head
        source-unchanged : W.source after ≡ W.source before
open Dequeue public
consume-observation : ∀ w s {s′} → W.step (W.consume w) s ≡ just s′ → Dequeue w s s′
consume-observation w s eq with W.pcAt w s in waiting | W.ownerContext w s in context
... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s) in originalQueue
...   | just m | true | item ∷ rest with Mux.status m | Mux.callback m
...     | Mux.ready | Mux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → dequeue f mid item rest next waiting context originalQueue advanced refl
  (pc-put w (W.selected item) (W.setPool w f next s)) refl }

consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopping | _ = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.stopped | _ = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.failed err | _ = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.readActive tr = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterStart n = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.forkPending n = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.afterFailure = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | Mux.ready | Mux.tracerFailed n = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
consume-observation w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
consume-observation w s eq | W.waiting | nothing = case eq of λ ()
consume-observation w s eq | W.selected item | _ = case eq of λ ()
consume-observation w s eq | W.responderTracing result | _ = case eq of λ ()
consume-observation w s eq | W.initiatorTracing result | _ = case eq of λ ()
consume-observation w s eq | W.deadReady outcome | _ = case eq of λ ()
consume-observation w s eq | W.deadTracing outcome | _ = case eq of λ ()
consume-observation w s eq | W.finished outcome | _ = case eq of λ ()


-- These witnesses retain actual primitive source writes. Clean initiator trace
-- return is an IG-ignored local boundary, not an old PSA-cell update.
data ProtocolWrite (mid : MuxId) (n : Nat.ℕ) (before after : W.State) : Mux.JobDirection → RunResult → Set where
  responderWrite : ∀ m outcome → W.muxAt mid before ≡ just m → W.legacyMatches n outcome (Mux.completions m) ≡ true →
    O.advance (O.inbound (M.igStep (IG.monitorCompletion mid))) (W.source before) ≡ just (W.source after) →
    ProtocolWrite mid n before after Mux.responderJob outcome
  initiatorCleanWrite : W.source after ≡ W.source before → ProtocolWrite mid n before after Mux.initiatorJob clean
  initiatorErrorWrite : ∀ err → O.advance (O.inbound (M.igStep (IG.recordMuxFailure mid err)))
    (W.source before) ≡ just (W.source after) → ProtocolWrite mid n before after Mux.initiatorJob (errored err)
protocol-source-observation : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → ProtocolWrite mid n s s′ dir outcome
protocol-source-observation w mid Mux.responderJob n outcome s eq with W.muxAt mid s in muxFound
... | nothing = case eq of λ ()
... | just m with W.legacyMatches n outcome (Mux.completions m) in matches
...   | false = case eq of λ ()
...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → responderWrite m outcome muxFound matches (via-observation (IG.monitorCompletion mid) s advanced) }
protocol-source-observation w mid Mux.initiatorJob n clean s eq = case just-injective eq of λ { refl → initiatorCleanWrite refl }
protocol-source-observation w mid Mux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → initiatorErrorWrite err (via-observation (IG.recordMuxFailure mid err) s advanced) }
record ProtocolHandle (w : WorkerId) (dir : Mux.JobDirection) (n : Nat.ℕ) (gen : RunId) (outcome : RunResult)
  (before after : W.State) : Set where
  constructor protocolHandle
  field ownerFrame : U.Frame
        capturedMux : MuxId
        physicalJob : JobId
        capturedJob : Types.ProtocolJob
        observedMux : Mux.Mux
        context-before : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        captured-generation : W.findCaptured w dir n gen outcome (P.jobs (W.base before)) ≡ just (physicalJob , capturedJob)
        mux-matches : does (Types.mux capturedJob ≟ capturedMux) ≡ true
        mux-before : W.muxAt capturedMux before ≡ just observedMux
        status-ready : Mux.status observedMux ≡ Mux.ready
        callback-before : Mux.callback observedMux ≡ Mux.returned
        actual-handler : W.protocolSource w capturedMux dir n outcome before ≡ just after
        actual-write : ProtocolWrite capturedMux n before after dir outcome
open ProtocolHandle public

protocol-handle-observation : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → ProtocolHandle w dir n gen outcome s s′
protocol-handle-observation w dir n gen outcome s eq with W.ownerContext w s in context | W.findCaptured w dir n gen outcome (P.jobs (W.base s)) in captured
... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) in matches | W.muxAt mid s in muxFound
...   | true | just m with Mux.status m in statusFound | Mux.callback m in callbackFound
...     | Mux.ready | Mux.returned = protocolHandle f mid j job m context captured matches muxFound statusFound callbackFound eq
  (protocol-source-observation w mid dir n outcome s eq)
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopping | _ = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.stopped | _ = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.failed err | _ = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.readActive tr = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterStart k = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.forkPending k = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.afterFailure = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | Mux.ready | Mux.tracerFailed k = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | nothing | _ = case eq of λ ()
protocol-handle-observation w dir n gen outcome s eq | just _ | nothing = case eq of λ ()


via-pool-unchanged : ∀ action s {s′} → W.viaSource action s ≡ just s′ →
  ∀ selected → W.poolAt selected s′ ≡ W.poolAt selected s
via-pool-unchanged action s eq selected with O.advance (O.inbound (M.igStep action)) (W.source s)
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → refl }
record StatusWrite (w : WorkerId) (outcome : W.Finish) (before after : W.State) : Set where
  constructor statusWrite
  field ownerFrame : U.Frame
        capturedMux : MuxId
        context-before : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        actual-status-write : O.advance (O.inbound (M.igStep (W.statusAction outcome capturedMux)))
          (W.source before) ≡ just (W.source after)
        pending-dead-after : W.pcAt w after ≡ W.deadReady outcome
        pools-unchanged : ∀ selected → W.poolAt selected after ≡ W.poolAt selected before
open StatusWrite public
status-observation : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → StatusWrite w outcome s s′
status-observation w outcome s eq with W.ownerContext w s in context
... | nothing = case eq of λ ()
... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → statusWrite f mid context
  (via-observation (W.statusAction outcome mid) s advanced)
  (pc-put w (W.deadReady outcome) next) (via-pool-unchanged (W.statusAction outcome mid) s advanced) }

-- The registered MiniProtocolJob count belongs to THIS handling state. It is
-- neither a count cached at dequeue nor a count of currently running slots.
data DemuxDecision (w : WorkerId) (err : ErrorId) (before : W.State) : W.Finish → Set where
  normalDemux : isBearerClosed err ∧ does (W.miniCount w before Nat.≟ Nat.zero) ≡ true →
    DemuxDecision w err before W.normal
  failedDemux : isBearerClosed err ∧ does (W.miniCount w before Nat.≟ Nat.zero) ≡ false →
    DemuxDecision w err before (W.failed err)
demux-decision : ∀ w err s → DemuxDecision w err s (W.demuxFinish w err s)
demux-decision w err s with isBearerClosed err ∧ does (W.miniCount w s Nat.≟ Nat.zero) in choice
... | true = normalDemux choice
... | false = failedDemux choice
data HandleChoice (w : WorkerId) (before after : W.State) : Types.TypedResult → Set where
  protocolChoice : ∀ dir n gen outcome → ProtocolHandle w dir n gen outcome before after →
    HandleChoice w before after (Types.protocolCompletion dir n gen outcome)
  muxerChoice : ∀ err → StatusWrite w (W.failed err) before after → HandleChoice w before after (Types.infraMuxer err)
  demuxerChoice : ∀ err outcome → DemuxDecision w err before outcome → StatusWrite w outcome before after →
    HandleChoice w before after (Types.infraDemuxer err)
record Handle (w : WorkerId) (before after : W.State) : Set where
  constructor handled
  field capturedHead : Types.TypedResult
        selected-before : W.pcAt w before ≡ W.selected capturedHead
        registered-at-handle : List JobId
        captured-jobs-at-handle : Store JobId Types.ProtocolJob
        mini-protocol-count : Nat.ℕ
        current-registered : registered-at-handle ≡ Pool.registered (W.poolAt w before)
        current-job-captures : captured-jobs-at-handle ≡ P.jobs (W.base before)
        actual-count : W.countMini w registered-at-handle captured-jobs-at-handle ≡ mini-protocol-count
        late-count : W.miniCount w before ≡ mini-protocol-count
        captured-choice : HandleChoice w before after capturedHead
        actual-effects : Paths before after
open Handle public
handle-observation : ∀ w s {s′} → W.step (W.handleSelected w) s ≡ just s′ → Handle w s s′
handle-observation w s eq with W.pcAt w s in selectedBefore
... | W.selected (Types.protocolCompletion dir n gen outcome) =
  handled (Types.protocolCompletion dir n gen outcome) selectedBefore
    (Pool.registered (W.poolAt w s)) (P.jobs (W.base s)) (W.miniCount w s) refl refl refl refl
    (protocolChoice dir n gen outcome (protocol-handle-observation w dir n gen outcome s eq))
    (handle-protocol-projects w dir n gen outcome s eq)
... | W.selected (Types.infraMuxer err) =
  handled (Types.infraMuxer err) selectedBefore
    (Pool.registered (W.poolAt w s)) (P.jobs (W.base s)) (W.miniCount w s) refl refl refl refl
    (muxerChoice err (status-observation w (W.failed err) s eq))
    (record-finish-projects w (W.failed err) s eq)
... | W.selected (Types.infraDemuxer err) =
  handled (Types.infraDemuxer err) selectedBefore
    (Pool.registered (W.poolAt w s)) (P.jobs (W.base s)) (W.miniCount w s) refl refl refl refl
    (demuxerChoice err (W.demuxFinish w err s) (demux-decision w err s) (status-observation w (W.demuxFinish w err s) s eq))
    (record-finish-projects w (W.demuxFinish w err s) s eq)
... | W.waiting = case eq of λ ()
... | W.responderTracing _ = case eq of λ ()
... | W.initiatorTracing _ = case eq of λ ()
... | W.deadReady _ = case eq of λ ()
... | W.deadTracing _ = case eq of λ ()
... | W.finished _ = case eq of λ ()

-- For protocol errors finishProtocolTrace observes ExceptionExit return before
-- Dead; the remaining Dead/(protocol DeltaQ)/return-or-throw boundary is this
-- separate finish input. Infra errors have no DeltaQ step in the pinned source.
-- The certificate retains only the actual callback/status and local PC change.
record Finished (w : WorkerId) (before after : W.State) : Set where
  constructor finishedMonitor
  field ownerFrame : U.Frame
        capturedMux : MuxId
        outcome : W.Finish
        observedMux : Mux.Mux
        tracing-before : W.pcAt w before ≡ W.deadTracing outcome
        context-before : W.ownerContext w before ≡ just (ownerFrame , capturedMux)
        mux-before : W.muxAt capturedMux before ≡ just observedMux
        actual-dead-return : Mux.callback observedMux ≡ Mux.returned
        actual-status-match : W.finishMatches outcome (Mux.status observedMux) ≡ true
        after-shape : after ≡ W.setPC w (W.finished outcome) before
        finished-after : W.pcAt w after ≡ W.finished outcome
        base-unchanged : W.base after ≡ W.base before
open Finished public
finish-observation : ∀ w s {s′} → W.step (W.finishDead w) s ≡ just s′ → Finished w s s′
finish-observation w s eq with W.pcAt w s in tracingBefore | W.ownerContext w s in context
... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s in muxFound
...   | just m with Mux.callback m in callbackFound | W.finishMatches outcome (Mux.status m) in matched
...     | Mux.returned | true = case just-injective eq of λ { refl →
  finishedMonitor f mid outcome m tracingBefore context muxFound callbackFound matched refl (pc-put w (W.finished outcome) s) refl }

finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.readActive tr | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.commitTrace active tr | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterStart n | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.forkPending n | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.afterFailure | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.tracerFailed n | _ = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | just m | Mux.returned | false = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
finish-observation w s eq | W.deadTracing outcome | nothing = case eq of λ ()
finish-observation w s eq | W.waiting | _ = case eq of λ ()
finish-observation w s eq | W.selected item | _ = case eq of λ ()
finish-observation w s eq | W.responderTracing result | _ = case eq of λ ()
finish-observation w s eq | W.initiatorTracing result | _ = case eq of λ ()
finish-observation w s eq | W.deadReady outcome | _ = case eq of λ ()
finish-observation w s eq | W.finished outcome | _ = case eq of λ ()
