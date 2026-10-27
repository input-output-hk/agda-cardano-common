{-# OPTIONS --guardedness #-}

-- Mux monitor, job and tracer actions retain every existing handler chain.
module ConnectionManagement.Properties.HandlerIGMux where

open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)
open import ConnectionManagement.Properties.HandlerIGBoundary using (queue-chain)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

-- All runtime updates preserve the key, even when they change the queue.
finish : ∀ ig mid old new s {ig′ q captured} →
  lookup mid (IG.muxes (IG.execution ig)) ≡ just old → M.key new ≡ M.key old →
  IG.setMux mid new ig ≡ ig′ → Chain q captured s ig → Chain q captured s ig′
finish ig mid old new s found same refl chain =
  anchors-preserve-chain (setMux-preserves mid old new ig found same) chain

-- Re-export the same coverage API; share the source-rule effect proof.
open import ConnectionManagement.Properties.MuxRetention public using
  (CoveredMux; sample; trace; started; fork; command; completion; demand; jobFinished; jobResult; stopped)
import ConnectionManagement.Properties.MuxRetention as Retention

worker-chain : ∀ a → CoveredMux a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain a covered ig queue s eq = anchors-preserve-chain (Retention.worker-anchors a covered ig queue eq)

mode-chain : ∀ mode a → CoveredMux a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain mode a covered ig queue s eq chain =
  anchors-preserve-chain (Retention.mode-anchors mode a covered ig queue eq) chain

step-preserves : ∀ a → CoveredMux a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)
