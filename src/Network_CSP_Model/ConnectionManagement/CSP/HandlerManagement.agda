{-# OPTIONS --guardedness #-}

-- Raw reference preservation through release and remote operations with pruning.
module ConnectionManagement.CSP.HandlerManagement where

open import Data.List using (List; map; []; _∷_)
open import Data.Integer using (+_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain hiding (remote)
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.Properties.HandlerManagement
open import ConnectionManagement.Properties.HandlerAttachment using (CreationPremises; advance-creates)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (exec-inv; exec-intro)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked; pAttached; pChecked; pRequested; pDelivered)
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.RemoteState as Remote
import ConnectionManagement.CSP.Pruning as Pruning
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.RemoteState as RS
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

raw-management-preserves : ∀ {c as P} → ManagementActions as →
  Process c ⟹⟨ map label as ⟩ P → ∀ q → TrackedChain q c →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain q c′)
raw-management-preserves only reach q chain with exec-inv reach
... | c′ , same , path = c′ , same , exec-preserves only path q chain

raw-attachment-management-creates : ∀ {w err c as P} →
  CreationPremises w (world c) (inboundGovernor c) → ManagementActions as →
  Process c ⟹⟨ map label (handlerStep w (L.attach err) ∷ as) ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × TrackedChain w c′)
raw-attachment-management-creates {w} {err} {c} premises only reach with exec-inv reach
... | c′ , same , next attached rest = c′ , same ,
  exec-preserves only rest w (advance-creates w err c premises attached)

-- Stop before IG.commitDecision: general IG steps are outside this theorem.
r₀ r₁ r₂ r₃ r₄ r₅ r₆ : Configuration
r₀ = tracked L.monitoring Release.b₆
r₁ = tracked L.monitoring Release.written
r₂ = tracked L.monitoring Release.counted
r₃ = tracked L.monitoring Release.requested
r₄ = tracked L.poolClosing Release.delivered
r₅ = tracked L.poolClosing Release.checked
r₆ = tracked L.poolClosing Release.returned
releaseActions : List Action
releaseActions = releaseStep R.transact ∷ releaseStep R.readCounters ∷ releaseStep R.requestCancellation ∷
  releaseStep (R.cancellationDelivered child₀) ∷ releaseStep R.checkAssertion ∷ releaseStep R.returnToIG ∷ []
release-path : Executes r₀ releaseActions r₆
release-path = next {c₁ = r₁} refl (next {c₁ = r₂} refl (next {c₁ = r₃} refl
  (next {c₁ = r₄} refl (next {c₁ = r₅} refl (next refl done)))))
release-start-chain : TrackedChain child₀ r₀
release-start-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
release-end-chain : TrackedChain child₀ r₆
release-end-chain = exec-preserves (release (release (release (release (release (release empty))))))
  release-path child₀ release-start-chain
release-csp : Process r₀ ⟹⟨ map label releaseActions ⟩ Process r₆
release-csp = exec-intro release-path

-- Local over-limit fixture: outbound acquisition reachability is not claimed.
pruneStart : Configuration
pruneStart = tracked L.monitoring Remote.p₀
pruneActions : List Action
pruneActions = remoteStep (RS.transactPruning 0 (+ 0 ∷ [])) ∷ remoteStep RS.checkAssertion ∷
  remoteStep RS.requestPruneCancellation ∷ remoteStep (RS.pruneCancellationDelivered child₀) ∷ []
prune-path : Executes pruneStart pruneActions pDelivered
prune-path = next {c₁ = pAttached} refl (next {c₁ = pChecked} refl (next {c₁ = pRequested} refl (next refl done)))
prune-start-chain : TrackedChain child₀ pruneStart
prune-start-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
prune-end-chain : TrackedChain child₀ pDelivered
prune-end-chain = exec-preserves (remote (remote (remote (remote empty)))) prune-path child₀ prune-start-chain
prune-csp : Process pruneStart ⟹⟨ map label pruneActions ⟩ Process pDelivered
prune-csp = exec-intro prune-path
terminated-but-retained : lookup (ident 0) (entries (cm (world pDelivered))) ≡ just (terminated nothing)
terminated-but-retained = refl

-- One atomic transaction writes two victims and the surviving owner's promotion.
multiStart multiEnd : Configuration
multiStart = tracked L.monitoring Pruning.multi
multiEnd = tracked L.monitoring Pruning.committed
multi-path : Executes multiStart (remoteStep (RS.transactPruning 0 Pruning.draws) ∷ []) multiEnd
multi-path = next refl done
multi-start-chain : TrackedChain child₀ multiStart
multi-start-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }
multi-end-chain : TrackedChain child₀ multiEnd
multi-end-chain = exec-preserves (remote empty) multi-path child₀ multi-start-chain
multi-csp : Process multiStart ⟹⟨ map label (remoteStep (RS.transactPruning 0 Pruning.draws) ∷ []) ⟩ Process multiEnd
multi-csp = exec-intro multi-path
