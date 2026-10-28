{-# OPTIONS --guardedness #-}

-- Observed interruptible operations in the masked post-mux handler. The
-- buffer provider's mask is a contract; pure policy/rethrow stages are not
-- fabricated delivery points. Pin: ConnectionHandler.hs:294-309,378-380,450-452.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxExitCancellation (isBearerClosed : ErrorId → Bool) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CMShutdown as Close
private
  module W = Exit isBearerClosed
State : Set
State = W.State
initial : O.Configuration → Maybe State
initial = W.initial
source : State → O.Configuration
source = W.source
poolAt : WorkerId → State → W.Pool.State
poolAt = W.poolAt

data Window : Set where
  bufferBlock errorTraceBlock nodeSendBlock : Window

-- Buffer cancellation leaves provider unwind outstanding. In contrast a
-- thrown classifier trace/send leaves that handler, without reclassification.
target : Window → ErrorId → W.Phase → Maybe W.Phase
target bufferBlock err (W.bufferScope _) = just (W.bufferScope (W.G.asyncExit err))
target errorTraceBlock err (W.errorTracing _ _) = just (W.bodyExited (W.asyncException err))
target nodeSendBlock err (W.nodeDelivery _) = just (W.bodyExited (W.asyncException err))
target _ _ _ = nothing
deliver : Window → WorkerId → ErrorId → State → Maybe State
deliver window w err s with lookup w (W.exits s)
... | nothing = nothing
... | just f with target window err (W.phase f)
...   | nothing = nothing
...   | just pc = just (record s { exits = W.edit w f pc s })

-- A synchronous exception thrown FROM the catch handler's tracer escapes that
-- classifier. Neither the old peer wrapper nor a node send has happened yet.
traceThrew : WorkerId → ErrorId → State → Maybe State
traceThrew w err s with lookup w (W.exits s)
... | just f with W.phase f
...   | W.errorTracing _ _ = just (record s { exits = W.edit w f (W.bodyExited (W.syncException err)) s })
...   | _ = nothing
traceThrew w err s | nothing = nothing
shutdownDelivery : Window → ErrorId → State → Maybe State
shutdownDelivery window err s with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with deliver window w err s
...   | nothing = nothing
...   | just next = W.control Close.acknowledgeDelivery next
shutdownDelivery window err s | _ = nothing

data Action : Set where
  run : W.Action → Action
  observeCancellation : Window → WorkerId → ErrorId → Action
  deliverShutdown : Window → ErrorId → Action
  observeErrorTraceException : WorkerId → ErrorId → Action
step : Action → State → Maybe State
step (run action) s = W.step action s
step (observeCancellation window w err) s = deliver window w err s
step (deliverShutdown window err) s = shutdownDelivery window err s
step (observeErrorTraceException w err) s = traceThrew w err s

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
