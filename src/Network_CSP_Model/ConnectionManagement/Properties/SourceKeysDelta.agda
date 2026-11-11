{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through DeltaQ observation: own actions mark tickets and
-- run own monitor or fault plans of the lower layer, which have no root.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysDelta (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxDeltaQ as Delta
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysUnwind as UnwindKeys
private
  module D = Delta isBearerClosed
  module R = D.R
  module W = D.W
  module M = D.M
  module Lower = UnwindKeys isBearerClosed

rootD : D.Action → Maybe O.Action
rootD (D.run a) = Lower.rootR a
rootD _ = nothing
Same : D.State → D.State → Set
Same s s′ = KeySame (D.source s) (D.source s′)
Nil : Maybe O.Action → O.Configuration → O.Configuration → Set
Nil r c c′ = r ≡ nothing → Effect r c c′ → KeySame c c′
nil : ∀ r {c c′} → r ≡ nothing → Effect r c c′ → KeySame c c′
nil .nothing refl e = e

inherit-keys : ∀ a s {s′} → D.inherit a s ≡ just s′ → Effect (Lower.rootR a) (D.source s) (D.source s′)
inherit-keys a s eq with D.allowed a s
... | false = case eq of λ ()
... | true with R.step a (D.base s) in stepped
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → Lower.step-keysR a (D.base s) stepped }
begin-keys : ∀ w s {s′} → D.begin w s ≡ just s′ → Same s s′
begin-keys w s eq with lookup w (D.tickets s)
... | just t with D.entryPhase t ∧ D.ready w t s
...   | true = case just-injective eq of λ { refl → same-refl _ }
...   | false = case eq of λ ()
begin-keys w s eq | nothing = case eq of λ ()
begin-initiator-keys : ∀ w s {s′} → D.beginInitiator w s ≡ just s′ → Same s s′
begin-initiator-keys w s eq with lookup w (D.tickets s)
... | just t with D.phase t | D.initiatorReady w t s
...   | D.captured | true = case just-injective eq of λ { refl → same-refl _ }
begin-initiator-keys w s eq | just t | D.captured | false = case eq of λ ()
begin-initiator-keys w s eq | just t | D.muxInvoked | _ = case eq of λ ()
begin-initiator-keys w s eq | just t | D.muxReturned | _ = case eq of λ ()
begin-initiator-keys w s eq | just t | D.invoked | _ = case eq of λ ()
begin-initiator-keys w s eq | just t | D.returned | _ = case eq of λ ()
begin-initiator-keys w s eq | just t | D.throwing | _ = case eq of λ ()
begin-initiator-keys w s eq | nothing = case eq of λ ()
return-initiator-keys : ∀ w s {s′} → D.returnInitiator w s ≡ just s′ → Same s s′
return-initiator-keys w s eq with lookup w (D.tickets s)
... | just t with D.phase t | D.initiatorReady w t s
...   | D.muxInvoked | true with D.payload t
...     | Types.protocolCompletion Mux.initiatorJob _ _ clean = case just-injective eq of λ { refl → same-refl _ }
...     | Types.protocolCompletion Mux.initiatorJob _ _ (errored _) with R.step (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) in stepped
...       | nothing = case eq of λ ()
...       | just r = case just-injective eq of λ { refl → Lower.step-keysR (D.wrapMonitor (M.finishProtocolTrace w)) (D.base s) stepped }
return-initiator-keys w s eq | just t | D.muxInvoked | true | Types.infraMuxer _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.muxInvoked | true | Types.infraDemuxer _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.muxInvoked | true | Types.protocolCompletion Mux.responderJob _ _ _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.captured | _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.muxInvoked | false = case eq of λ ()
return-initiator-keys w s eq | just t | D.muxReturned | _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.invoked | _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.returned | _ = case eq of λ ()
return-initiator-keys w s eq | just t | D.throwing | _ = case eq of λ ()
return-initiator-keys w s eq | nothing = case eq of λ ()
finish-root : ∀ w p → Lower.rootR (D.finishAction w p) ≡ nothing
finish-root w (Types.protocolCompletion _ _ _ clean) = refl
finish-root w (Types.protocolCompletion _ _ _ (errored _)) = refl
finish-root w (Types.infraMuxer _) = refl
finish-root w (Types.infraDemuxer _) = refl
complete-keys : ∀ w s {s′} → D.complete w s ≡ just s′ → Same s s′
complete-keys w s eq with lookup w (D.tickets s)
... | just t with D.phase t | D.ready w t s
...   | D.invoked | true with R.step (D.finishAction w (D.payload t)) (D.base s) in stepped
...     | nothing = case eq of λ ()
...     | just r = case just-injective eq of λ { refl → nil _ (finish-root w (D.payload t))
  (Lower.step-keysR (D.finishAction w (D.payload t)) (D.base s) stepped) }
complete-keys w s eq | just t | D.captured | _ = case eq of λ ()
complete-keys w s eq | just t | D.muxInvoked | _ = case eq of λ ()
complete-keys w s eq | just t | D.muxReturned | _ = case eq of λ ()
complete-keys w s eq | just t | D.invoked | false = case eq of λ ()
complete-keys w s eq | just t | D.returned | _ = case eq of λ ()
complete-keys w s eq | just t | D.throwing | _ = case eq of λ ()
complete-keys w s eq | nothing = case eq of λ ()

fault-root : ∀ w result s {plan} → D.faultPlan w result s ≡ just plan → Lower.planRoot plan ≡ nothing
fault-root w result s eq with lookup w (D.tickets s)
... | just t with D.phase t | D.ready w t s
...   | D.invoked | true = Lower.start-root w result _ (D.base s) eq
fault-root w result s eq | just t | D.captured | _ = case eq of λ ()
fault-root w result s eq | just t | D.muxInvoked | _ = case eq of λ ()
fault-root w result s eq | just t | D.muxReturned | _ = case eq of λ ()
fault-root w result s eq | just t | D.invoked | false = case eq of λ ()
fault-root w result s eq | just t | D.returned | _ = case eq of λ ()
fault-root w result s eq | just t | D.throwing | _ = case eq of λ ()
fault-root w result s eq | nothing = case eq of λ ()
initiator-fault-root : ∀ w result s {plan} → D.initiatorFaultPlan w result s ≡ just plan → Lower.planRoot plan ≡ nothing
initiator-fault-root w result s eq with lookup w (D.tickets s)
... | just t with D.phase t | D.initiatorReady w t s
...   | D.muxInvoked | true = Lower.start-root w result _ (D.base s) eq
initiator-fault-root w result s eq | just t | D.captured | _ = case eq of λ ()
initiator-fault-root w result s eq | just t | D.muxInvoked | false = case eq of λ ()
initiator-fault-root w result s eq | just t | D.muxReturned | _ = case eq of λ ()
initiator-fault-root w result s eq | just t | D.invoked | _ = case eq of λ ()
initiator-fault-root w result s eq | just t | D.returned | _ = case eq of λ ()
initiator-fault-root w result s eq | just t | D.throwing | _ = case eq of λ ()
initiator-fault-root w result s eq | nothing = case eq of λ ()
delivery-root : ∀ b plan → Lower.planRoot (D.delivery b plan) ≡ Lower.planRoot plan
delivery-root true plan = refl
delivery-root false plan = refl
apply-keys : ∀ w plan b s {s′} → Lower.planRoot plan ≡ nothing → D.applyFault w plan b s ≡ just s′ → Same s s′
apply-keys w plan b s rooted eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with R.enact (D.delivery b plan) (D.base s) in enacted
...   | nothing = case eq of λ ()
...   | just r = case just-injective eq of λ { refl → nil _ (trans (delivery-root b plan) rooted)
  (Lower.enact-keys (D.delivery b plan) (D.base s) enacted) }
throw-keys : ∀ w result b s {s′} → D.throw w result b s ≡ just s′ → Same s s′
throw-keys w result b s eq with D.faultPlan w result s in planned
... | nothing = case eq of λ ()
... | just plan = apply-keys w plan b s (fault-root w result s planned) eq
throw-initiator-keys : ∀ w result b s {s′} → D.throwInitiator w result b s ≡ just s′ → Same s s′
throw-initiator-keys w result b s eq with D.initiatorFaultPlan w result s in planned
... | nothing = case eq of λ ()
... | just plan = apply-keys w plan b s (initiator-fault-root w result s planned) eq

step-keysD : ∀ a s {s′} → D.step a s ≡ just s′ → Effect (rootD a) (D.source s) (D.source s′)
step-keysD (D.run a) s eq = inherit-keys a s eq
step-keysD (D.beginDeltaQ w) s eq = begin-keys w s eq
step-keysD (D.observeReturn w) s eq = complete-keys w s eq
step-keysD (D.observeException w err) s eq = throw-keys w err false s eq
step-keysD (D.beginInitiatorTrace w) s eq = begin-initiator-keys w s eq
step-keysD (D.observeInitiatorReturn w) s eq = return-initiator-keys w s eq
step-keysD (D.observeInitiatorException w err) s eq = throw-initiator-keys w err false s eq
step-keysD (D.deliverShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery _ w = throw-keys w (R.async err) true s eq
step-keysD (D.deliverShutdown err) s eq | Close.initial = case eq of λ ()
step-keysD (D.deliverShutdown err) s eq | Close.reading = case eq of λ ()
step-keysD (D.deliverShutdown err) s eq | Close.awaitResults = case eq of λ ()
step-keysD (D.deliverShutdown err) s eq | Close.closed = case eq of λ ()
step-keysD (D.deliverShutdown err) s eq | Close.sendReady _ _ = case eq of λ ()
step-keysD (D.deliverInitiatorShutdown err) s eq with Close.phase (W.shutdown (R.base (D.base s)))
... | Close.awaitDelivery _ w = throw-initiator-keys w (R.async err) true s eq
step-keysD (D.deliverInitiatorShutdown err) s eq | Close.initial = case eq of λ ()
step-keysD (D.deliverInitiatorShutdown err) s eq | Close.reading = case eq of λ ()
step-keysD (D.deliverInitiatorShutdown err) s eq | Close.awaitResults = case eq of λ ()
step-keysD (D.deliverInitiatorShutdown err) s eq | Close.closed = case eq of λ ()
step-keysD (D.deliverInitiatorShutdown err) s eq | Close.sendReady _ _ = case eq of λ ()
