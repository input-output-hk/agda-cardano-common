{-# OPTIONS --guardedness #-}

-- Reference preservation through successful and exceptional cleanup traces.
module ConnectionManagement.CSP.HandlerCleanup where

open import Data.List using (List; map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerCleanup
open import ConnectionManagement.Properties.HandlerAttachment using (CreationPremises; advance-creates)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using
  (cleanupEntered; cleanupSnapshot; term; selected; waiting; cleanupActions; cleanup-path; doneCleanup; mapTaken; socketClosed)
open import ConnectionManagement.CSP.Fixtures using (binding; childLease)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Cleanup as C
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-cleanup-preserves : ∀ {c as P} → CleanupActions as →
  Process c ⟹⟨ map label as ⟩ P → ∀ q → TrackedChain q c →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-cleanup-preserves only reach q chain with exec-inv reach
... | c′ , same , path = c′ , same , exec-preserves only path q chain

raw-attachment-cleanup-creates : ∀ {w err c as P} →
  CreationPremises w (world c) (inboundGovernor c) → CleanupActions as →
  Process c ⟹⟨ map label (handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-attachment-cleanup-creates {w} {err} {c} premises only reach with exec-inv reach
... | c′ , same , next attached rest = c′ , same ,
  exec-preserves only rest w (advance-creates w err c premises attached)

-- Existing async-exit fixture, certified without assuming source reachability.
entry-chain : TrackedChain child₀ cleanupEntered
entry-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }

cleanup-coverage : CleanupActions cleanupActions
cleanup-coverage = cleanup (cleanup (cleanup (cleanup (cleanup (cleanup (cleanup empty))))))
finished-chain : TrackedChain child₀ doneCleanup
finished-chain = exec-preserves cleanup-coverage cleanup-path child₀ entry-chain
cleanup-csp : Process cleanupEntered ⟹⟨ map label cleanupActions ⟩ Process doneCleanup
cleanup-csp = exec-intro cleanup-path

-- Closing can fail before map publication. Restoration leaves the original
-- entry allocated and the socket recorded with uncertain close status.
closeError : ErrorId
closeError = errorId 91
closeFailed restored : Configuration
closeFailed = cleanupSnapshot cleanupEntered term (taken child₀)
  (closeUncertain closeError) (cleanupRestore childLease closeError)
restored = cleanupSnapshot cleanupEntered term (full binding)
  (closeUncertain closeError) (cleanupDone (cleanupError closeError))
closeFailureActions : List Action
closeFailureActions = cleanupStep child₀ C.takeCleanupMap ∷ cleanupStep child₀ C.selectCleanupEntry ∷
  cleanupStep child₀ (C.failSocketClose closeError) ∷ cleanupStep child₀ C.restoreCleanupMap ∷ []
close-failure-path : Executes cleanupEntered closeFailureActions restored
close-failure-path = next {c₁ = mapTaken} refl (next {c₁ = selected} refl (next {c₁ = closeFailed} refl (next refl done)))
restored-chain : TrackedChain child₀ restored
restored-chain = exec-preserves (cleanup (cleanup (cleanup (cleanup empty)))) close-failure-path child₀ entry-chain
close-failure-csp : Process cleanupEntered ⟹⟨ map label closeFailureActions ⟩ Process restored
close-failure-csp = exec-intro close-failure-path

-- Interruption still runs the final termination/purge transaction before the
-- error outcome; the old entry remains allocated after map membership is lost.
interrupted errorCount errorDone : Configuration
interrupted = cleanupSnapshot cleanupEntered term (full binding) closed (cleanupFinalize term (cleanupError closeError))
errorCount = cleanupSnapshot cleanupEntered (terminated nothing) (full []) closed (cleanupCount (cleanupError closeError))
errorDone = cleanupSnapshot cleanupEntered (terminated nothing) (full []) closed (cleanupDone (cleanupError closeError))
interruptActions : List Action
interruptActions = cleanupStep child₀ C.takeCleanupMap ∷ cleanupStep child₀ C.selectCleanupEntry ∷
  cleanupStep child₀ C.closeHandlerSocket ∷ cleanupStep child₀ C.publishCleanupMap ∷
  cleanupStep child₀ (C.interruptTimeWait closeError) ∷ cleanupStep child₀ C.finishTimeWait ∷
  cleanupStep child₀ C.readCleanupCounters ∷ []
interrupt-path : Executes cleanupEntered interruptActions errorDone
interrupt-path = next {c₁ = mapTaken} refl (next {c₁ = selected} refl
  (next {c₁ = socketClosed} refl (next {c₁ = waiting} refl (next {c₁ = interrupted} refl
  (next {c₁ = errorCount} refl (next refl done))))))
interrupted-chain : TrackedChain child₀ errorDone
interrupted-chain = exec-preserves (cleanup (cleanup (cleanup (cleanup (cleanup (cleanup (cleanup empty)))))))
  interrupt-path child₀ entry-chain
interrupt-csp : Process cleanupEntered ⟹⟨ map label interruptActions ⟩ Process errorDone
interrupt-csp = exec-intro interrupt-path

-- Observable scope checks: reference validity does not imply open or mapped.
finished-socket-closed : lookup (ident 0) (sockets (world doneCleanup)) ≡ just closed
finished-socket-closed = refl
finished-map-empty : mapCell (cm (world doneCleanup)) ≡ full []
finished-map-empty = refl
restored-socket-uncertain : lookup (ident 0) (sockets (world restored)) ≡ just (closeUncertain closeError)
restored-socket-uncertain = refl
interrupted-outcome : lookup child₀ (cleanups (world errorDone)) ≡ just (cleanupDone (cleanupError closeError))
interrupted-outcome = refl
