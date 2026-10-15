{-# OPTIONS --guardedness #-}

-- Preparation is reference evidence; lifecycle transitions may attach and then
-- close the handler without destroying that evidence. No progress is asserted.
module ConnectionManagement.CSP.HandlerLifecycleInterference where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerGovernorInterference
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerGovernorInterference using (raw-prepared; release-batch-covered)
import ConnectionManagement.Properties.HandlerAllIGInterference as AllIG
import ConnectionManagement.Properties.HandlerRuntimeInterference as Runtime
import ConnectionManagement.CSP.HandlerIGInterference as Start
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.InboundRelease as R
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

request-covered : Interference Life.requestActions
request-covered = more release (more release (more release empty))
requested-prepared : Prepared child₀ (ident 0) G.mid (world Release.requested) (inboundGovernor Release.requested)
requested-prepared = prepared-exec request-covered Life.request-path
  (prepared-exec release-batch-covered Release.batch-path Start.registered-prepared)
requested-unattached : handlerLifecycles Release.requested ≡ []
requested-unattached = refl

unwind-covered : Interference Life.unwindActions
unwind-covered = more lifecycle (more release (more lifecycle (more lifecycle
  (more (runtime AllIG.ig) (more (runtime AllIG.ig) (more lifecycle
  (more (runtime (AllIG.runtime Runtime.exit)) empty)))))))
cleanup-covered : Interference Life.cleanupActions
cleanup-covered = more (runtime (AllIG.runtime Runtime.cleanup))
  (more (runtime (AllIG.runtime Runtime.cleanup)) (more (runtime (AllIG.runtime Runtime.cleanup))
  (more (runtime (AllIG.runtime Runtime.cleanup)) (more (runtime (AllIG.runtime Runtime.cleanup))
  (more (runtime (AllIG.runtime Runtime.cleanup)) (more (runtime (AllIG.runtime Runtime.cleanup)) empty))))))
cleanup-entered-prepared : Prepared child₀ (ident 0) G.mid (world Life.cleanupEntered) (inboundGovernor Life.cleanupEntered)
cleanup-entered-prepared = prepared-exec unwind-covered Life.unwind-path requested-prepared
finalized-prepared : Prepared child₀ (ident 0) G.mid (world Life.doneCleanup) (inboundGovernor Life.doneCleanup)
finalized-prepared = prepared-exec cleanup-covered Life.cleanup-path cleanup-entered-prepared
unwind-csp : Process Release.requested ⟹⟨ map label Life.unwindActions ⟩ Process Life.cleanupEntered
unwind-csp = exec-intro Life.unwind-path
unwind-reachable : Σ Configuration (λ c′ → Process Life.cleanupEntered ≡ Process c′ ×
  Prepared child₀ (ident 0) G.mid (world c′) (inboundGovernor c′))
unwind-reachable = raw-prepared unwind-covered requested-prepared unwind-csp
unwind-cleanup-csp : Process Release.requested ⟹⟨ map label (Life.unwindActions ++ Life.cleanupActions) ⟩ Process Life.doneCleanup
unwind-cleanup-csp = exec-intro (exec-append Life.unwind-path Life.cleanup-path)

-- The original socket is closed and map binding gone, yet its identity remains.
final-socket : lookup (ident 0) (sockets (world Life.doneCleanup)) ≡ just closed
final-socket = refl
final-map : mapCell (cm (world Life.doneCleanup)) ≡ full []
final-map = refl

-- Preparation also survives delivery while pool closure is still outstanding.
attached-prepared : Prepared child₀ (ident 0) G.mid (world Life.attached) (inboundGovernor Life.attached)
attached-prepared = prepared-step (handlerStep child₀ (L.attach Life.cancelError)) lifecycle Release.requested refl requested-prepared
received-prepared : Prepared child₀ (ident 0) G.mid (world Life.received) (inboundGovernor Life.received)
received-prepared = prepared-step (releaseStep (R.cancellationDelivered child₀)) release Life.attached refl attached-prepared
