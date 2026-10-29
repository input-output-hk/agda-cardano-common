{-# OPTIONS --guardedness #-}

-- Source and actual physical-pool projections through explicit DeltaQ outcomes.
-- These are finite-execution safety facts, not source refinement or progress.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxDeltaQ (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxDeltaQ as Delta
module D = Delta isBearerClosed
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
module P = D.P
module Pool = D.Pool
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindFacts
module Base = UnwindFacts isBearerClosed
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
module Exit = ExitFacts isBearerClosed
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
open import ConnectionManagement.IGTypes using (clean; errored)
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close

Paths : D.State → D.State → Set
Paths p q = Base.Paths (D.base p) (D.base q)
idle : ∀ s → Paths s s
idle s = Base.idle (D.base s)
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose {p} {q} {r} = Base.compose {p = D.base p} {q = D.base q} {r = D.base r}
mark-projects : ∀ w t pc s → Paths s (D.mark w t pc s)
mark-projects w t pc s = idle s
inherit-projects : ∀ action s {s′} → D.inherit action s ≡ just s′ → Paths s s′
inherit-projects action s eq with D.allowed action s
... | false = case eq of λ ()
... | true with R.step action (D.base s) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → Base.step-projects action (D.base s) advanced }
begin-projects : ∀ w s {s′} → D.begin w s ≡ just s′ → Paths s s′
begin-projects w s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.entryPhase t ∧ D.ready w t s
...   | true = case just-injective eq of λ { refl → idle s }
...   | false = case eq of λ ()
complete-projects : ∀ w s {s′} → D.complete w s ≡ just s′ → Paths s s′
complete-projects w s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.ready w t s
...   | D.invoked | true with R.step (D.finishAction w (D.payload t)) (D.base s) in advanced
...     | nothing = case eq of λ ()
...     | just r = case just-injective eq of λ { refl → Base.step-projects (D.finishAction w (D.payload t)) (D.base s) advanced }
complete-projects w s eq | just t | D.captured | _ = case eq of λ ()
complete-projects w s eq | just t | D.muxInvoked | _ = case eq of λ ()
complete-projects w s eq | just t | D.muxReturned | _ = case eq of λ ()
complete-projects w s eq | just t | D.returned | _ = case eq of λ ()
complete-projects w s eq | just t | D.throwing | _ = case eq of λ ()
complete-projects w s eq | just t | D.invoked | false = case eq of λ ()
apply-fault-projects : ∀ w plan ack s {s′} → D.applyFault w plan ack s ≡ just s′ → Paths s s′
apply-fault-projects w plan ack s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with R.enact (D.delivery ack plan) (D.base s) in advanced
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → Base.enact-projects (D.delivery ack plan) (D.base s) advanced }
throw-projects : ∀ w result ack s {s′} → D.throw w result ack s ≡ just s′ → Paths s s′
throw-projects w result ack s eq with D.faultPlan w result s
... | nothing = case eq of λ ()
... | just plan = apply-fault-projects w plan ack s eq
begin-initiator-projects : ∀ w s {s′} → D.beginInitiator w s ≡ just s′ → Paths s s′
begin-initiator-projects w s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.initiatorReady w t s
...   | D.captured | true = case just-injective eq of λ { refl → idle s }
...   | D.captured | false = case eq of λ ()
...   | D.muxInvoked | _ = case eq of λ ()
...   | D.muxReturned | _ = case eq of λ ()
...   | D.invoked | _ = case eq of λ ()
...   | D.returned | _ = case eq of λ ()
...   | D.throwing | _ = case eq of λ ()
return-initiator-projects : ∀ w s {s′} → D.returnInitiator w s ≡ just s′ → Paths s s′
return-initiator-projects w s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.initiatorReady w t s
...   | D.muxInvoked | true with D.payload t
...     | Types.protocolCompletion Mux.initiatorJob n gen clean = case just-injective eq of λ { refl → idle s }
...     | Types.protocolCompletion Mux.initiatorJob n gen (errored err) with R.step (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) in advanced
...       | nothing = case eq of λ ()
...       | just r = case just-injective eq of λ { refl → Base.step-projects (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) advanced }
return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob n gen outcome = case eq of λ ()
return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.infraMuxer err = case eq of λ ()
return-initiator-projects w s eq | just t | D.muxInvoked | true | Types.infraDemuxer err = case eq of λ ()
return-initiator-projects w s eq | just t | D.muxInvoked | false = case eq of λ ()
return-initiator-projects w s eq | just t | D.captured | _ = case eq of λ ()
return-initiator-projects w s eq | just t | D.muxReturned | _ = case eq of λ ()
return-initiator-projects w s eq | just t | D.invoked | _ = case eq of λ ()
return-initiator-projects w s eq | just t | D.returned | _ = case eq of λ ()
return-initiator-projects w s eq | just t | D.throwing | _ = case eq of λ ()
throw-initiator-projects : ∀ w result ack s {s′} → D.throwInitiator w result ack s ≡ just s′ → Paths s s′
throw-initiator-projects w result ack s eq with D.initiatorFaultPlan w result s
... | nothing = case eq of λ ()
... | just plan = apply-fault-projects w plan ack s eq
step-projects : ∀ action s {s′} → D.step action s ≡ just s′ → Paths s s′
step-projects (D.run action) s eq = inherit-projects action s eq
step-projects (D.beginDeltaQ w) s eq = begin-projects w s eq
step-projects (D.observeReturn w) s eq = complete-projects w s eq
step-projects (D.observeException w err) s eq = throw-projects w err false s eq
step-projects (D.beginInitiatorTrace w) s eq = begin-initiator-projects w s eq
step-projects (D.observeInitiatorReturn w) s eq = return-initiator-projects w s eq
step-projects (D.observeInitiatorException w err) s eq = throw-initiator-projects w err false s eq
step-projects (D.deliverShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery e w = throw-projects w (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady e w = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
step-projects (D.deliverInitiatorShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery e w = throw-initiator-projects w (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady e w = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
exec-projects : ∀ {s actions s′} → D.Executes s actions s′ → Paths s s′
exec-projects (D.done {s = s}) = idle s
exec-projects (D.next {s = s} {s₁ = t} {s₂ = u} {a = a} eq tail) = compose {p = s} {q = t} {r = u} (step-projects a s eq) (exec-projects tail)
initial-base : ∀ c {s} → D.initial c ≡ just s → R.initial c ≡ just (D.base s)
initial-base c eq with R.initial c
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → D.initial c ≡ just s → D.source s ≡ c
initial-source c eq = Base.initial-source c (initial-base c eq)
pool-from-initial : ∀ {c start actions s} → D.initial c ≡ just start → D.Executes start actions s →
  ∀ w → ProtocolFacts.PTrace Pool.initial (D.poolAt w s)
pool-from-initial {c} initialized path w = ProtocolFacts.trace-left
  (sym (Exit.initial-pool c (Base.initial-base c (initial-base c initialized)) w))
  (Exit.pools (exec-projects path) w)
from-initial-captures : ∀ {c start actions s} → D.initial (O.initial c) ≡ just start → D.Executes start actions s → Capture.Captures (D.source s)
from-initial-captures {c} initialized path = Capture.exec-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c))
  (proj₂ (Exit.machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → D.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  D.Executes start actions s → Supply.Valid (D.source s)
from-initial-supply {c} initialized bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounds))
  (proj₂ (Exit.machine (exec-projects path)))
whole-closed-from-initial : ∀ {c start actions s} → D.initial c ≡ just start → D.Executes start actions s →
  ∀ w → Pool.phase (D.poolAt w s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (D.poolAt w s) → Base.PoolFacts.Terminal (D.poolAt w s) j
whole-closed-from-initial initialized path w closed = Base.PoolFacts.from-initial
  (proj₂ (pool-from-initial initialized path w)) closed

-- Successful entry changes only ticket metadata. It cannot consume another FIFO
-- result, finish an old trace or commit any source counter/notification effects.
begin-keeps-base : ∀ w s {s′} → D.begin w s ≡ just s′ → D.base s′ ≡ D.base s
begin-keeps-base w s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.entryPhase t ∧ D.ready w t s
...   | true = case just-injective eq of λ { refl → refl }
...   | false = case eq of λ ()

-- The fault plan retains the real published owner, callback and current-pool
-- registration certificate from the existing selector, rather than synthesizing
-- a successful callback or normal pool exit for the new throwing outcome.
fault-selection : ∀ w result s {plan} → D.faultPlan w result s ≡ just plan →
  Base.Selection w result (λ _ _ → just R.poolBody) (D.base s) plan
fault-selection w result s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.ready w t s
...   | D.invoked | true = Base.selection-observation w result (λ _ _ → just R.poolBody) (D.base s) eq
...   | D.invoked | false = case eq of λ ()
...   | D.captured | _ = case eq of λ ()
...   | D.muxInvoked | _ = case eq of λ ()
...   | D.muxReturned | _ = case eq of λ ()
...   | D.returned | _ = case eq of λ ()
...   | D.throwing | _ = case eq of λ ()
apply-local-keeps-underlying : ∀ w fs s {s′} → D.applyFault w (R.local fs) false s ≡ just s′ →
  R.base (D.base s′) ≡ R.base (D.base s)
apply-local-keeps-underlying w fs s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t = case just-injective eq of λ { refl → refl }
throw-keeps-underlying : ∀ w result s {s′} → D.throw w result false s ≡ just s′ →
  R.base (D.base s′) ≡ R.base (D.base s)
throw-keeps-underlying w result s eq with D.faultPlan w result s in planned
... | nothing = case eq of λ ()
... | just plan with fault-selection w result s planned
...   | selected rewrite Base.Selection.plan-shape selected = apply-local-keeps-underlying w _ s eq


-- Retain the actual nested dispatcher call at the physical CM collective wait,
-- instead of substituting registry absence, cleanupDone or delivery receipt.
inherited-observation : ∀ action s {s′} → D.step (D.run action) s ≡ just s′ →
  Σ R.State (λ r → R.step action (D.base s) ≡ just r ×
    s′ ≡ D.deltaQState r (D.note action r (D.tickets s)))
inherited-observation action s eq with D.allowed action s
... | false = case eq of λ ()
... | true with R.step action (D.base s) in advanced
...   | nothing = case eq of λ ()
...   | just r = r , refl , sym (just-injective eq)
physical-wait : ∀ s {s′} → D.step (D.run (R.run (X.run (W.shutdownStep Close.finishClose)))) s ≡ just s′ →
  Exit.PhysicalWait (R.base (D.base s)) (R.base (D.base s′))
physical-wait s eq with inherited-observation (R.run (X.run (W.shutdownStep Close.finishClose))) s eq
... | r , advanced , refl = Base.physical-wait (D.base s) advanced

-- During the callback no inherited action attributed to this owner can resume
-- its controller. Independent child/other-owner actions keep their own guards.
invoked-blocks-controller : ∀ action s w → D.actor action s ≡ just w → D.free w s ≡ false →
  D.step (D.run action) s ≡ nothing
invoked-blocks-controller action s w actor busy rewrite actor | busy = refl
