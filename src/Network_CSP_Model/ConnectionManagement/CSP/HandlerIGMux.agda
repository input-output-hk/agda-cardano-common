{-# OPTIONS --guardedness #-}

-- Concrete raw traces instantiate the general runtime reference invariant.
module ConnectionManagement.CSP.HandlerIGMux where

open import Data.List using (List; map; drop; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Data.Maybe.Properties using (just-injective)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement
import ConnectionManagement.Properties.HandlerIGMux as Proof
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.HandlerOutcomes as O
import ConnectionManagement.CSP.IGRuntime as Runtime
open import ConnectionManagement.CSP.IGRegistration using (registered; mid)
open import ConnectionManagement.CSP.HandlerAttachment using (newlyAttached; created-chain)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Reuse the checked path after its known attachment boundary.
after-head : ∀ {c c₁ c′ a as} → Executes c (a ∷ as) c′ → advance a c ≡ just c₁ → Executes c₁ as c′
after-head (next eq rest) known with just-injective (trans (sym eq) known)
... | refl = rest

sync-initial : TrackedChain child₀ O.s₀
sync-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
sync-path : Executes O.s₀ (drop 1 O.syncActions) O.s₁₁
sync-path = after-head O.sync-path refl
sync-coverage : ManagementActions (drop 1 O.syncActions)
sync-coverage = (igMux Proof.jobFinished (igMux Proof.jobResult (igMux Proof.completion (igMux Proof.sample (igMux Proof.trace (igMux Proof.command (igMux Proof.sample (igMux Proof.trace (lifecycle (lifecycle (lifecycle empty)))))))))))
sync-chain : TrackedChain child₀ O.s₁₁
sync-chain = exec-preserves sync-coverage sync-path child₀ sync-initial
sync-csp : Process O.s₀ ⟹⟨ map label (drop 1 O.syncActions) ⟩ Process O.s₁₁
sync-csp = exec-intro sync-path

normal-initial : TrackedChain child₀ O.n₀
normal-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
normal-path : Executes O.n₀ (drop 1 O.normalActions) O.n₈
normal-path = after-head O.normal-path refl
normal-coverage : ManagementActions (drop 1 O.normalActions)
normal-coverage = (igMux Proof.command (igMux Proof.stopped (igMux Proof.sample (igMux Proof.trace (lifecycle (lifecycle (lifecycle (exit empty))))))))
normal-chain : TrackedChain child₀ O.n₈
normal-chain = exec-preserves normal-coverage normal-path child₀ normal-initial
normal-csp : Process O.n₀ ⟹⟨ map label (drop 1 O.normalActions) ⟩ Process O.n₈
normal-csp = exec-intro normal-path

async-initial : TrackedChain child₀ Life.attached
async-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
async-path : Executes Life.attached (drop 1 Life.unwindActions) Life.cleanupEntered
async-path = after-head Life.unwind-path refl
async-coverage : ManagementActions (drop 1 Life.unwindActions)
async-coverage = (release (lifecycle (lifecycle (igMux Proof.sample (igMux Proof.trace (lifecycle (exit empty)))))))
async-chain : TrackedChain child₀ Life.cleanupEntered
async-chain = exec-preserves async-coverage async-path child₀ async-initial
async-csp : Process Life.attached ⟹⟨ map label (drop 1 Life.unwindActions) ⟩ Process Life.cleanupEntered
async-csp = exec-intro async-path

startStart startEnd : Configuration
startStart = tracked L.monitoring registered
startEnd = tracked L.monitoring Runtime.jobRunning
start-initial : TrackedChain child₀ startStart
start-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
startActions : List Action
startActions = igStep (IG.monitorCommand mid) ∷ igStep (IG.startOnDemand mid 1) ∷ igStep (IG.sampleTracer mid) ∷ igStep (IG.commitTracer mid) ∷ igStep (IG.finishStart mid) ∷ igStep (IG.forkResponder mid) ∷ []
start-path : Executes startStart startActions startEnd
start-path = next {c₁ = tracked L.monitoring Runtime.commandRead} refl (next {c₁ = tracked L.monitoring Runtime.callbackEntered} refl (next {c₁ = tracked L.monitoring Runtime.activeSampled} refl (next {c₁ = tracked L.monitoring Runtime.traceCommitted} refl (next {c₁ = tracked L.monitoring Runtime.statusRunning} refl (next refl done)))))
start-chain : TrackedChain child₀ startEnd
start-chain = exec-preserves (igMux Proof.command (igMux Proof.demand (igMux Proof.sample (igMux Proof.trace (igMux Proof.started (igMux Proof.fork empty)))))) start-path child₀ start-initial
start-csp : Process startStart ⟹⟨ map label startActions ⟩ Process startEnd
start-csp = exec-intro start-path

cleanStart cleanEnd : Configuration
cleanStart = tracked L.monitoring Runtime.jobRunning
cleanEnd = tracked L.monitoring Runtime.resultConsumed
clean-initial : TrackedChain child₀ cleanStart
clean-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
cleanActions : List Action
cleanActions = igStep (IG.finishProtocol mid 1 clean) ∷ igStep (IG.publishJobResult mid 1) ∷ igStep (IG.monitorCompletion mid) ∷ []
clean-path : Executes cleanStart cleanActions cleanEnd
clean-path = next {c₁ = tracked L.monitoring Runtime.jobFinished} refl (next {c₁ = tracked L.monitoring Runtime.resultPublished} refl (next refl done))
clean-chain : TrackedChain child₀ cleanEnd
clean-chain = exec-preserves (igMux Proof.jobFinished (igMux Proof.jobResult (igMux Proof.completion empty))) clean-path child₀ clean-initial
clean-csp : Process cleanStart ⟹⟨ map label cleanActions ⟩ Process cleanEnd
clean-csp = exec-intro clean-path

overlapStart overlapEnd : Configuration
overlapStart = tracked L.monitoring Runtime.overlapConfig
overlapEnd = tracked L.monitoring Runtime.overlapDone
overlap-initial : TrackedChain child₀ overlapStart
overlap-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
overlapActions : List Action
overlapActions = igStep (IG.commitTracer mid) ∷ []
overlap-path : Executes overlapStart overlapActions overlapEnd
overlap-path = next refl done
overlap-chain : TrackedChain child₀ overlapEnd
overlap-chain = exec-preserves (igMux Proof.trace empty) overlap-path child₀ overlap-initial
overlap-csp : Process overlapStart ⟹⟨ map label overlapActions ⟩ Process overlapEnd
overlap-csp = exec-intro overlap-path

faultStart faultEnd : Configuration
faultStart = tracked L.monitoring Runtime.missingDescriptorInput
faultEnd = tracked L.monitoring Runtime.missingDescriptorFault
fault-initial : TrackedChain child₀ faultStart
fault-initial = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
faultActions : List Action
faultActions = igStep (IG.commitTracer mid) ∷ []
fault-path : Executes faultStart faultActions faultEnd
fault-path = next refl done
fault-chain : TrackedChain child₀ faultEnd
fault-chain = exec-preserves (igMux Proof.trace empty) fault-path child₀ fault-initial
fault-csp : Process faultStart ⟹⟨ map label faultActions ⟩ Process faultEnd
fault-csp = exec-intro fault-path

