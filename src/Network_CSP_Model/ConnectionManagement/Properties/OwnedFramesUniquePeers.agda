{-# OPTIONS --guardedness #-}

-- All peer-supervision source writers preserve the four caller-table keys.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesUniquePeers
  (isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (put-unique; delete-unique)
open import ConnectionManagement.Properties.OutboundKeys using
  (Unique; unique-tables; acquireFrames; releaseFrames; acquireResults; releaseResults; advance-unique)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Machine as I
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Properties.OwnedFramesGovernorLift as GovernorLift
import ConnectionManagement.Properties.PeerSupervisionCM as SupervisionLift
import ConnectionManagement.PeerSupervision as Supervision
private
  module PS = Supervision isIOManagerError
  module GP = PS.GP
  module LiftG = GovernorLift isIOManagerError
  module LiftPS = SupervisionLift isIOManagerError

-- Detachment deletes an acquiring binding without changing the other tables.
delete-acquire : ∀ c w → Unique c → Unique (record c { acquiring = delete w (O.acquiring c) })
delete-acquire c w u = unique-tables (delete-unique w (O.acquiring c) (acquireFrames u))
  (releaseFrames u) (acquireResults u) (releaseResults u)

-- Release detachment uses the same first-binding deletion operation.
delete-release : ∀ c w → Unique c → Unique (record c { releasing = delete w (O.releasing c) })
delete-release c w u = unique-tables (acquireFrames u)
  (delete-unique w (O.releasing c) (releaseFrames u)) (acquireResults u) (releaseResults u)

-- All cancellation-start contexts either fail or delete one caller binding.
start-unique : ∀ w err context c {f d} → Cancel.start w err context c ≡ just (f , d) → Unique c → Unique d
start-unique w err Cancel.protectedCleanup c eq u = case eq of λ ()
start-unique w err Cancel.ordinary c eq u with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire c w u }
start-unique w err Cancel.ordinary c eq u | nothing | just active = case just-injective eq of λ { refl → delete-release c w u }
start-unique w err Cancel.ordinary c eq u | nothing | nothing = case just-injective eq of λ { refl → u }
start-unique w err Cancel.ordinary c eq u | just _ | just _ = case eq of λ ()
start-unique w err Cancel.forkedBeforeHandoff c eq u with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire c w u }
start-unique w err Cancel.forkedBeforeHandoff c eq u | nothing | nothing = case eq of λ ()
start-unique w err Cancel.forkedBeforeHandoff c eq u | nothing | just _ = case eq of λ ()
start-unique w err Cancel.forkedBeforeHandoff c eq u | just _ | just _ = case eq of λ ()
start-unique w err Cancel.interruptibleOpen c eq u with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire c w u }
start-unique w err Cancel.interruptibleOpen c eq u | nothing | nothing = case eq of λ ()
start-unique w err Cancel.interruptibleOpen c eq u | nothing | just _ = case eq of λ ()
start-unique w err Cancel.interruptibleOpen c eq u | just _ | just _ = case eq of λ ()

-- The exceptional acquired result is a put, preserving existing uniqueness.
acquired-put : ∀ c w value → Unique c → Unique (record c { acquired = put w value (O.acquired c) })
acquired-put c w value u = unique-tables (acquireFrames u) (releaseFrames u)
  (put-unique w value (O.acquired c) (acquireResults u)) (releaseResults u)

private
  -- Component lifts retain all real source writers and enumerate every GP step.
  module G = LiftG.StepLift Unique
    (λ c g control u → unique-tables (acquireFrames u) (releaseFrames u) (acquireResults u) (releaseResults u))
    (λ w req c eq u → advance-unique (O.beginAcquire w req) c eq u)
    (λ w key c eq u → advance-unique (O.beginRelease w key) c eq u)
    (λ mid c eq u → advance-unique (O.inbound (I.igStep (IG.monitorCompletion mid))) c eq u)
    (λ _ → ⊤)
    (λ a c permission eq u → advance-unique a c eq u)
    start-unique (λ c world u → unique-tables (acquireFrames u) (releaseFrames u) (acquireResults u) (releaseResults u)) acquired-put

  -- Every subsystem permission is trivial because all raw O actions preserve Unique.
  g-allowed : ∀ a → G.Allowed a
  g-allowed (GP.run (Sub.core _)) = tt
  g-allowed (GP.run Sub.publishPublicState) = tt
  g-allowed (GP.run (Sub.sampleTime _)) = tt
  g-allowed (GP.run (Sub.applyAt _)) = tt
  g-allowed (GP.run (Sub.setTargets _)) = tt
  g-allowed (GP.run (Sub.selectMonitor _)) = tt
  g-allowed (GP.run Sub.selectCompletion) = tt
  g-allowed (GP.run Sub.selectTargets) = tt
  g-allowed (GP.run Sub.selectWakeup) = tt
  g-allowed (GP.run Sub.registerWakeup) = tt
  g-allowed (GP.run Sub.expireWakeup) = tt
  g-allowed (GP.run Sub.cancelWakeup) = tt
  g-allowed (GP.run Sub.publishCounters) = tt
  g-allowed (GP.run Sub.traceSelection) = tt
  g-allowed (GP.run (Sub.selectPolicy _)) = tt
  g-allowed (GP.run (Sub.forkJob _ _ _)) = tt
  g-allowed (GP.run Sub.registerJob) = tt
  g-allowed (GP.run Sub.finishLaunch) = tt
  g-allowed (GP.run (Sub.jobStep _ _)) = tt
  g-allowed (GP.run (Sub.enqueueCompletion _ _)) = tt
  g-allowed (GP.run (Sub.deregisterJob _)) = tt
  g-allowed (GP.run (Sub.protocolResult _ _ _)) = tt
  g-allowed (GP.run (Sub.publishInitiatorResult _ _)) = tt
  g-allowed (GP.run (Sub.pollPeer _ _)) = tt
  g-allowed (GP.run (Sub.monitorStep _ _)) = tt
  g-allowed (GP.run (Sub.monitorFinished _)) = tt
  g-allowed (GP.run (Sub.observeInitiatorFailure _)) = tt
  g-allowed (GP.handoff _) = tt
  g-allowed (GP.beginClose _) = tt
  g-allowed GP.requestCancel = tt
  g-allowed GP.join = tt
  g-allowed GP.finishClose = tt
  g-allowed (GP.deliverCancellation _) = tt
  g-allowed (GP.deliverOpenCancellation _) = tt
  g-allowed (GP.cleanup _ _) = tt
  g-allowed (GP.bodyUnwound _) = tt
  g-allowed (GP.recoverCloseFailure _) = tt
  g-allowed (GP.deregisterCancelled _) = tt
  g-allowed (GP.publishAsyncResult _) = tt

-- All governor transitions, including recovery and cleanup, preserve Unique.
governor-unique : ∀ a s {t} → GP.step a s ≡ just t → Unique (GP.cm s) → Unique (GP.cm t)
governor-unique a s = G.step-preserves a s (g-allowed a)

private
  -- The existing PS lift covers fork, detach, polls, scopes and monitor exits.
  module P = LiftPS.Lift Unique governor-unique start-unique

-- Every successful peer action preserves four-table uniqueness without premises on ownership.
peer-unique : ∀ a s {t} → PS.step a s ≡ just t → Unique (PS.cm s) → Unique (PS.cm t)
peer-unique = P.step-preserves
