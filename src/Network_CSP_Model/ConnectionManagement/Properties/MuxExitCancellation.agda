{-# OPTIONS --guardedness #-}

-- Real source/pool histories and exact observed cancellation/acknowledgment.
-- The named interruptible operation is an input contract, not a mask theorem.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxExitCancellation (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain using (WorkerId; EntryId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseFacts
import ConnectionManagement.Rules.MuxJobTypes as Types
private
  module X = Cancellation isBearerClosed
  module W = Exit isBearerClosed
  module Base = ExitFacts isBearerClosed
  module Pool = W.Pool
module PoolFacts = CloseFacts Types.TypedResult true
Paths : X.State → X.State → Set
Paths = Base.Paths

delivery-projects : ∀ window w err s {s′} → X.deliver window w err s ≡ just s′ → Paths s s′
delivery-projects window w err s eq with lookup w (W.exits s)
... | nothing = case eq of λ ()
... | just f with X.target window err (W.phase f)
...   | nothing = case eq of λ ()
...   | just pc = case just-injective eq of λ { refl → Base.metadata s (W.edit w f pc s) }
trace-projects : ∀ w err s {s′} → X.traceThrew w err s ≡ just s′ → Paths s s′
trace-projects w err s eq with lookup w (W.exits s)
... | nothing = case eq of λ ()
... | just f with W.phase f
...   | W.errorTracing _ _ = case just-injective eq of λ { refl → Base.metadata s (W.edit w f (W.bodyExited (W.syncException err)) s) }
...   | W.bufferScope _ = case eq of λ ()
...   | W.classifying _ = case eq of λ ()
...   | W.peerRethrow _ = case eq of λ ()
...   | W.nodeDelivery _ = case eq of λ ()
...   | W.nodeRethrow _ = case eq of λ ()
...   | W.bodyExited _ = case eq of λ ()
...   | W.finalizing _ = case eq of λ ()
...   | W.cleanupComplete _ _ = case eq of λ ()
...   | W.resultAvailable _ _ = case eq of λ ()
shutdown-projects : ∀ window err s {s′} → X.shutdownDelivery window err s ≡ just s′ → Paths s s′
shutdown-projects window err s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with X.deliver window w err s in delivered
...   | nothing = case eq of λ ()
...   | just next = Base.compose (delivery-projects window w err s delivered) (Base.control-projects Close.acknowledgeDelivery next eq)
shutdown-projects window err s eq | Close.initial = case eq of λ ()
shutdown-projects window err s eq | Close.reading = case eq of λ ()
shutdown-projects window err s eq | Close.sendReady _ _ = case eq of λ ()
shutdown-projects window err s eq | Close.awaitResults = case eq of λ ()
shutdown-projects window err s eq | Close.closed = case eq of λ ()
step-projects : ∀ action s {s′} → X.step action s ≡ just s′ → Paths s s′
step-projects (X.run action) s eq = Base.step-projects action s eq
step-projects (X.observeCancellation window w err) s eq = delivery-projects window w err s eq
step-projects (X.deliverShutdown window err) s eq = shutdown-projects window err s eq
step-projects (X.observeErrorTraceException w err) s eq = trace-projects w err s eq
exec-projects : ∀ {s actions s′} → X.Executes s actions s′ → Paths s s′
exec-projects X.done = Base.idle _
exec-projects (X.next {s = s} {a = action} eq tail) = Base.compose (step-projects action s eq) (exec-projects tail)
from-initial-captures : ∀ {c start actions s} → X.initial (O.initial c) ≡ just start → X.Executes start actions s → Capture.Captures (X.source s)
from-initial-captures {c} initialized path = Capture.exec-preserves
  (subst Capture.Captures (sym (Base.initial-source (O.initial c) initialized)) (Capture.initial-valid c))
  (proj₂ (Base.machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → X.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  X.Executes start actions s → Supply.Valid (X.source s)
from-initial-supply {c} initialized bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (Base.initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounds))
  (proj₂ (Base.machine (exec-projects path)))
pool-from-initial : ∀ {c start actions s} → X.initial c ≡ just start → X.Executes start actions s →
  ∀ selected → ProtocolFacts.PTrace Pool.initial (X.poolAt selected s)
pool-from-initial {c} initialized path selected = ProtocolFacts.trace-left
  (sym (Base.initial-pool c initialized selected)) (Base.pools (exec-projects path) selected)
whole-closed-from-initial : ∀ {c start actions s} → X.initial c ≡ just start → X.Executes start actions s →
  ∀ selected → Pool.phase (X.poolAt selected s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (X.poolAt selected s) → PoolFacts.Terminal (X.poolAt selected s) j
whole-closed-from-initial initialized path selected closed = PoolFacts.from-initial (proj₂ (pool-from-initial initialized path selected)) closed

record Delivery (window : X.Window) (w : WorkerId) (err : ErrorId) (before after : X.State) : Set where
  constructor delivery
  field previous : W.Frame
        successor : W.Phase
        found : lookup w (W.exits before) ≡ just previous
        observed-window : X.target window err (W.phase previous) ≡ just successor
        after-shape : after ≡ record before { exits = W.edit w previous successor before }
delivery-observation : ∀ window w err s {s′} → X.step (X.observeCancellation window w err) s ≡ just s′ → Delivery window w err s s′
delivery-observation window w err s eq with lookup w (W.exits s) in found
... | nothing = case eq of λ ()
... | just f with X.target window err (W.phase f) in selected
...   | nothing = case eq of λ ()
...   | just pc = delivery f pc found selected (sym (just-injective eq))
record ShutdownDelivery (window : X.Window) (err : ErrorId) (before after : X.State) : Set where
  constructor shutdownDelivery
  field entry : EntryId
        worker : WorkerId
        intermediate : X.State
        awaiting : Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker
        actual-delivery : X.deliver window worker err before ≡ just intermediate
        actual-acknowledgment : W.control Close.acknowledgeDelivery intermediate ≡ just after
shutdown-observation : ∀ window err s {s′} → X.step (X.deliverShutdown window err) s ≡ just s′ → ShutdownDelivery window err s s′
shutdown-observation window err s eq with Close.phase (W.shutdown s) in awaited
... | Close.awaitDelivery e w with X.deliver window w err s in delivered
...   | nothing = case eq of λ ()
...   | just next = shutdownDelivery e w next awaited delivered eq
shutdown-observation window err s eq | Close.initial = case eq of λ ()
shutdown-observation window err s eq | Close.reading = case eq of λ ()
shutdown-observation window err s eq | Close.sendReady _ _ = case eq of λ ()
shutdown-observation window err s eq | Close.awaitResults = case eq of λ ()
shutdown-observation window err s eq | Close.closed = case eq of λ ()

lift : ∀ {s actions s′} → W.Executes s actions s′ → X.Executes s (map X.run actions) s′
lift W.done = X.done
lift (W.next eq tail) = X.next eq (lift tail)
append : ∀ {s as t bs u} → X.Executes s as t → X.Executes t bs u → X.Executes s (as ++ bs) u
append X.done tail = tail
append (X.next eq rest) tail = X.next eq (append rest tail)
physical-wait : ∀ s {s′} → X.step (X.run (W.shutdownStep Close.finishClose)) s ≡ just s′ → Base.PhysicalWait s s′
physical-wait s eq = Base.physical-wait-observation s eq
