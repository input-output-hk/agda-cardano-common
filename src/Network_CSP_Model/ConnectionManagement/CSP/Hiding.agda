{-# OPTIONS --guardedness #-}

-- One explicit observation policy over the SAME machine, using the dependency's
-- hiding operator/laws. This is not a validated API abstraction or parallel model.
module ConnectionManagement.CSP.Hiding where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro; all-exec-inv)
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.HandlerLifecycle as Life
open import CSP.Operators channel-≟ using (EventSet; _∖_)
open EventSet
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
open import Semantics.LTS {E = Channel} {I = ExtI Channel} using (Event√)
open import CSP.Laws.Traces.TraceLawsHide channel-≟
  using (HideTr; hnil; hkeep; hdrop; Hide-trace-intro; Hide-trace-elim)

-- Hide map/entry/promise transactions and local allocation/continuation steps.
-- Fork/close outcomes, handler boundary inputs, time readiness, and CM return
-- labels remain visible. They are diagnostic observations, not wire protocols.
internal : Action → Bool
internal (admissionStep _ Server.fork) = false
internal (admissionStep _ Server.failFork) = false
internal (admissionStep _ Server.close) = false
internal (admissionStep _ _) = true
internal (handshakeStep _ Handshake.returnResult) = false
internal (handshakeStep _ _) = true
internal (cleanupStep _ Cleanup.closeHandlerSocket) = false
internal (cleanupStep _ (Cleanup.failSocketClose _)) = false
internal (cleanupStep _ Cleanup.timeWaitElapsed) = false
internal (cleanupStep _ (Cleanup.interruptTimeWait _)) = false
internal (cleanupStep _ _) = true
internal (handlerPublication _ _ _) = false
internal (handlerExit _) = false
internal (handlerStep _ Life.publishAsyncFailure) = true
internal (handlerStep _ Life.monitorReturned) = true
internal (handlerStep _ Life.monitorThrew) = true
internal (handlerStep _ Life.rethrow) = true
internal (handlerStep _ _) = false
internal (remoteStep (Remote.transactPruning _ _)) = false
internal (remoteStep (Remote.pruneCancellationDelivered _)) = false
internal (remoteStep Remote.returnToIG) = false
internal (remoteStep _) = true
internal (releaseStep (Release.cancellationDelivered _)) = false
internal (releaseStep Release.returnToIG) = false
internal (releaseStep _) = true
internal (igStep (IG.captureTime _)) = false
internal (igStep IG.deactivateIG) = false
internal (igStep (IG.installHandle _ _ _ _ _)) = false
internal (igStep (IG.expireTimer _)) = false
internal (igStep (IG.startOnDemand _ _)) = false
internal (igStep (IG.finishProtocol _ _ _)) = false
internal (igStep (IG.finishStop _)) = false
internal (igStep _) = true

internalSet : EventSet
internalSet .mem (_ , action) a = internal a ≡ true
internalSet .dec (_ , action) a = internal a ≟ true

HiddenProcess : Configuration → Proc
HiddenProcess c = Process c ∖ internalSet

project : List Action → List Action
project [] = []
project (a ∷ as) with internal a
... | true = project as
... | false = a ∷ project as

projection : ∀ as → HideTr internalSet (map label as) (map label (project as))
projection [] = hnil
projection (a ∷ as) with internal a in eq
... | true = hdrop eq (projection as)
... | false = hkeep (λ yes → false-not-true (trans (sym eq) yes)) (projection as)
  where
  false-not-true : false ≡ true → ⊥
  false-not-true ()

hidden-trace : ∀ {c as c′} → Executes c as c′ →
  traces (HiddenProcess c) (map label (project as))
hidden-trace {c} {as} path = Hide-trace-intro internalSet (Process c) (exec-intro path) (projection as)

-- Every hidden trace comes from an actual machine execution, related by the
-- dependency's de-hiding relation. The hidden endpoint need not equal Process c′.
hidden-trace-inv : ∀ {c} {es : List (Event√ ⊤)} → traces (HiddenProcess c) es →
  Σ (List Action) (λ as → Σ Configuration (λ c′ →
    Executes c as c′ × HideTr internalSet (map label as) es))
hidden-trace-inv {c} (_ , tr) with Hide-trace-elim internalSet (Process c) tr
... | raw , P , rawTrace , projectionProof with all-exec-inv rawTrace
...   | as , c′ , refl , _ , execution = as , c′ , execution , projectionProof
