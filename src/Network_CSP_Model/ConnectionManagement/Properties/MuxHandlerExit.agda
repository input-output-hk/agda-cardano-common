{-# OPTIONS --guardedness #-}

-- All real source/pool effects of the exit adapter, and the exact physical
-- observation used by its CM final wait. Buffer and policy observations remain
-- input contracts; this is not a source-refinement or universal-progress proof.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxHandlerExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain hiding (local)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxHandlerExit as Exit
private
  module W = Exit isBearerClosed
private
  module G = W.G
private
  module Pool = W.Pool
private
  module U = W.U
private
  module P = W.P
import ConnectionManagement.Properties.MuxGroupShutdown as GroupFacts
private
  module Base = GroupFacts isBearerClosed
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseFacts
import ConnectionManagement.Rules.MuxJobTypes as Types
module PoolFacts = CloseFacts Types.TypedResult true
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Properties.HandlerSupervision as HandlerFacts
import ConnectionManagement.Properties.CMShutdown as CloseProof

record Paths (before after : W.State) : Set where
  constructor paths
  field machine : ProtocolFacts.OTrace (W.source before) (W.source after)
        pools : ∀ selected → ProtocolFacts.PTrace (W.poolAt selected before) (W.poolAt selected after)
open Paths public
idle : ∀ s → Paths s s
idle s = paths ([] , O.done) (λ selected → [] , Pool.done)
from-base : ∀ before after → Base.Paths (W.base before) (W.base after) → Paths before after
from-base before after p = paths (Base.machine p) (Base.pools p)
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) first) (paths (bs , oq) second) = paths
  (as ++ bs , O.append op oq) (λ selected → let left = first selected; right = second selected in
    proj₁ left ++ proj₁ right , ProtocolFacts.append-pools (proj₂ left) (proj₂ right))
metadata : ∀ s fs → Paths s (record s { exits = fs })
metadata s fs = paths ([] , O.done) (λ selected → [] , Pool.done)
source-step : ∀ action s {c} → O.advance action (W.source s) ≡ just c → Paths s (W.setSource c s)
source-step action s eq = from-base s _ (Base.from-protocol (W.base s) _
  (ProtocolFacts.source-step action (G.protocolState (W.base s)) eq))
shutdown-metadata : ∀ s pc → Paths s (W.setShutdown pc s)
shutdown-metadata s pc = paths ([] , O.done) (λ selected → [] , Pool.done)
control-projects : ∀ action s {s′} → W.control action s ≡ just s′ → Paths s s′
control-projects action s eq with Close.step (Shared.cm (W.shared s)) (λ w → W.resultReady w s) action (W.shutdown s) in stepped
... | nothing = case eq of λ ()
... | just pc = case just-injective eq of λ { refl → shutdown-metadata s pc }
enact-projects : ∀ plan s {s′} → W.enact plan s ≡ just s′ → Paths s s′
enact-projects (W.local fs) s eq = case just-injective eq of λ { refl → metadata s fs }
enact-projects (W.machine action fs) s eq with O.advance action (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → compose (source-step action s advanced) (metadata (W.setSource c s) fs) }
enact-projects (W.inherited action) s eq with G.step action (W.base s) in advanced
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → from-base s _ (Base.step-projects action (W.base s) advanced) }
enact-projects (W.coordinator action) s eq = control-projects action s eq
enact-projects (W.muxDelivery w err) s eq with G.step (G.abortOwner w err) (W.base s) in advanced
... | nothing = case eq of λ ()
... | just g = compose (from-base s (record s { base = g }) (Base.step-projects (G.abortOwner w err) (W.base s) advanced))
  (control-projects Close.acknowledgeDelivery (record s { base = g }) eq)
enact-projects (W.timeWaitDelivery w err) s eq with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = compose (compose
  (source-step (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) s advanced)
  (metadata (W.setSource c s) (W.noteCleanup w (Cleanup.interruptTimeWait err) s)))
  (control-projects Close.acknowledgeDelivery (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq)
step-projects : ∀ action s {s′} → W.step action s ≡ just s′ → Paths s s′
step-projects action s eq with W.choose action s
... | nothing = case eq of λ ()
... | just plan = enact-projects plan s eq
exec-projects : ∀ {s actions s′} → W.Executes s actions s′ → Paths s s′
exec-projects W.done = idle _
exec-projects (W.next {s = s} {a = action} eq tail) = compose (step-projects action s eq) (exec-projects tail)
initial-base : ∀ c {s} → W.initial c ≡ just s → G.initial c ≡ just (W.base s)
initial-base c eq with G.initial c in initialized
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c eq = Base.initial-source c (initial-base c eq)
initial-pool : ∀ c {s} → W.initial c ≡ just s → ∀ selected → W.poolAt selected s ≡ Pool.initial
initial-pool c eq = Base.initial-pool c (initial-base c eq)
pool-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → ProtocolFacts.PTrace Pool.initial (W.poolAt selected s)
pool-from-initial {c} initialized path selected = ProtocolFacts.trace-left (sym (initial-pool c initialized selected)) (pools (exec-projects path) selected)
from-initial-captures : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → W.Executes start actions s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = Capture.exec-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) (proj₂ (machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  W.Executes start actions s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounds)) (proj₂ (machine (exec-projects path)))
whole-closed-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → Pool.phase (W.poolAt selected s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (W.poolAt selected s) → PoolFacts.Terminal (W.poolAt selected s) j
whole-closed-from-initial initialized path selected closed = PoolFacts.from-initial (proj₂ (pool-from-initial initialized path selected)) closed

-- The source and result oracle are retained at the ACTUAL final wait, rather
-- than guessed from the later cleanup heap or the coordinator's closed flag.
record Control (action : Close.Action) (before after : W.State) : Set where
  constructor control
  field successor : Close.State
        actual-step : Close.step (Shared.cm (W.shared before)) (λ w → W.resultReady w before) action (W.shutdown before) ≡ just successor
        after-shape : after ≡ W.setShutdown successor before
open Control public
control-observation : ∀ action s {s′} → W.control action s ≡ just s′ → Control action s s′
control-observation action s eq with Close.step (Shared.cm (W.shared s)) (λ w → W.resultReady w s) action (W.shutdown s) in stepped
... | nothing = case eq of λ ()
... | just pc = control pc stepped (sym (just-injective eq))
finish-close-observation : ∀ s {s′} → W.step (W.shutdownStep Close.finishClose) s ≡ just s′ →
  CloseProof.FinalWait (W.shutdown s′)
finish-close-observation s eq with control-observation Close.finishClose s eq
... | control pc stepped refl = HandlerFacts.make-wait (Shared.cm (W.shared s)) (λ w → W.resultReady w s) (W.shutdown s) stepped

-- A published result records the body outcome separately from any finally
-- exception. It requires the actual cleanupDone boundary and never writes the
-- source or a completion queue in order to manufacture that result.
record Publication (w : WorkerId) (before after : W.State) : Set where
  constructor publication
  field previous : W.Frame
        body : W.BodyResult
        outcome : Shared.CleanupOutcome
        observed : Shared.CleanupOutcome
        frame-found : lookup w (W.exits before) ≡ just previous
        previous-phase : W.phase previous ≡ W.cleanupComplete body observed
        cleanup-found : lookup w (Shared.cleanups (W.shared before)) ≡ just (Shared.cleanupDone outcome)
        outcome-matches : W.sameCleanup observed outcome ≡ true
        after-shape : after ≡ record before { exits = W.edit w previous (W.resultAvailable body outcome) before }
publication-observation : ∀ w s {s′} → W.step (W.publishAsyncResult w) s ≡ just s′ → Publication w s s′
publication-observation w s eq with lookup w (W.exits s) in found | lookup w (Shared.cleanups (W.shared s)) in cleaned
... | just f | just (Shared.cleanupDone outcome) with W.phase f in pc
...   | W.cleanupComplete body observed with W.sameCleanup observed outcome in matches
...     | false = case eq of λ ()
...     | true = publication f body outcome observed found pc cleaned matches (sym (just-injective eq))
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.bufferScope _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.classifying _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.errorTracing _ _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.peerRethrow _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.nodeDelivery _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.nodeRethrow _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.bodyExited _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.finalizing _ = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupDone outcome) | W.resultAvailable _ _ = case eq of λ ()
publication-observation w s eq | just f | just Shared.cleanupAcquire = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupSelect _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupClose _ _ _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupPublish _ _ _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupRestore _ _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupWaiting _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupFinalize _ _) = case eq of λ ()
publication-observation w s eq | just f | just (Shared.cleanupCount _) = case eq of λ ()
publication-observation w s eq | just f | nothing = case eq of λ ()
publication-observation w s eq | nothing | _ = case eq of λ ()

-- Retain the wrapper call and its exact result table alongside the primitive
-- certificate. This does not assert that all historical or future children end.
record PhysicalWait (before after : W.State) : Set where
  constructor physicalWait
  field actual-step : W.step (W.shutdownStep Close.finishClose) before ≡ just after
        primitive-wait : CloseProof.FinalWait (W.shutdown after)
        physical-oracle : CloseProof.available primitive-wait ≡ (λ w → W.resultReady w before)
        observed-results : CloseProof.Observed (λ w → W.resultReady w before) (W.shutdown after)
physical-wait-observation : ∀ s {s′} → W.step (W.shutdownStep Close.finishClose) s ≡ just s′ → PhysicalWait s s′
physical-wait-observation s eq with control-observation Close.finishClose s eq
... | control pc stepped refl = physicalWait eq witness refl (CloseProof.observed-at-wait witness)
  where
  witness : CloseProof.FinalWait pc
  witness = HandlerFacts.make-wait (Shared.cm (W.shared s)) (λ w → W.resultReady w s) (W.shutdown s) stepped

-- Lift inherited initialized paths without specializing the full controller
-- reduction at a concrete exception classifier in every acceptance endpoint.
wrap : G.State → W.State
wrap g = W.handlerExitState g []
allSafe : List G.Action → Bool
allSafe [] = true
allSafe (a ∷ as) = W.delegateAllowed a ∧ allSafe as
lift-step : ∀ a g {g′} → W.delegateAllowed a ≡ true → G.step a g ≡ just g′ →
  W.step (W.run a) (wrap g) ≡ just (wrap g′)
lift-step a g safe eq with W.delegateAllowed a
... | false = case safe of λ ()
... | true with G.step a g
...   | nothing = case eq of λ ()
...   | just g′ = case just-injective eq of λ { refl → refl }
lift-path : ∀ {g actions g′} → G.Executes g actions g′ → allSafe actions ≡ true →
  W.Executes (wrap g) (map W.run actions) (wrap g′)
lift-path G.done safe = W.done
lift-path (G.next {s = g} {a = a} eq tail) safe with W.delegateAllowed a in allowed
... | false = case safe of λ ()
... | true = W.next (lift-step a g allowed eq) (lift-path tail safe)
append : ∀ {s as t bs u} → W.Executes s as t → W.Executes t bs u → W.Executes s (as ++ bs) u
append W.done tail = tail
append (W.next eq rest) tail = W.next eq (append rest tail)
