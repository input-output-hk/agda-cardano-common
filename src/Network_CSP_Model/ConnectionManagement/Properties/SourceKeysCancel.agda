{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through exit-cancellation observations: they edit only
-- handler exit frames and the CM shutdown coordinator.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysCancel (isBearerClosed : ErrorId → Bool) where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysExit as ExitKeys
private
  module X = Cancellation isBearerClosed
  module W = ConnectionManagement.MuxHandlerExit isBearerClosed
  module Lower = ExitKeys isBearerClosed

rootX : X.Action → Maybe O.Action
rootX (X.run a) = Lower.rootW a
rootX _ = nothing
Same : X.State → X.State → Set
Same s s′ = KeySame (X.source s) (X.source s′)

deliver-keys : ∀ window w err s {s′} → X.deliver window w err s ≡ just s′ → Same s s′
deliver-keys window w err s eq with lookup w (W.exits s)
... | nothing = case eq of λ ()
... | just f with X.target window err (W.phase f)
...   | nothing = case eq of λ ()
...   | just pc = case just-injective eq of λ { refl → same-refl _ }
threw-keys : ∀ w err s {s′} → X.traceThrew w err s ≡ just s′ → Same s s′
threw-keys w err s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.errorTracing _ _ = case just-injective eq of λ { refl → same-refl _ }
threw-keys w err s eq | just f | W.bufferScope _ = case eq of λ ()
threw-keys w err s eq | just f | W.classifying _ = case eq of λ ()
threw-keys w err s eq | just f | W.peerRethrow _ = case eq of λ ()
threw-keys w err s eq | just f | W.nodeDelivery _ = case eq of λ ()
threw-keys w err s eq | just f | W.nodeRethrow _ = case eq of λ ()
threw-keys w err s eq | just f | W.bodyExited _ = case eq of λ ()
threw-keys w err s eq | just f | W.finalizing _ = case eq of λ ()
threw-keys w err s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
threw-keys w err s eq | just f | W.resultAvailable _ _ = case eq of λ ()
threw-keys w err s eq | nothing = case eq of λ ()
shutdown-keys : ∀ window err s {s′} → X.shutdownDelivery window err s ≡ just s′ → Same s s′
shutdown-keys window err s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with X.deliver window w err s in delivered
...   | nothing = case eq of λ ()
...   | just next = same-trans (deliver-keys window w err s delivered) (Lower.control-keys Close.acknowledgeDelivery next eq)
shutdown-keys window err s eq | Close.initial = case eq of λ ()
shutdown-keys window err s eq | Close.reading = case eq of λ ()
shutdown-keys window err s eq | Close.awaitResults = case eq of λ ()
shutdown-keys window err s eq | Close.closed = case eq of λ ()
shutdown-keys window err s eq | Close.sendReady _ _ = case eq of λ ()

step-keysX : ∀ a s {s′} → X.step a s ≡ just s′ → Effect (rootX a) (X.source s) (X.source s′)
step-keysX (X.run a) s eq = Lower.step-keysW a s eq
step-keysX (X.observeCancellation window w err) s eq = deliver-keys window w err s eq
step-keysX (X.deliverShutdown window err) s eq = shutdown-keys window err s eq
step-keysX (X.observeErrorTraceException w err) s eq = threw-keys w err s eq
