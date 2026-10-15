{-# OPTIONS --guardedness #-}

-- IG control-loop actions may alter membership, timers and queue, but retain
-- installed handles and muxes. This is reference safety, not progress.
module ConnectionManagement.Properties.HandlerIGLoop where

open import Data.Bool using (true; false)
open import Data.Nat using (_≤?_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerIGBoundary using (queue-chain)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.IGBatch as Batch
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

stable-chain : ∀ {ig ig′ q mid s} →
  IG.handles (IG.execution ig′) ≡ IG.handles (IG.execution ig) →
  IG.muxes (IG.execution ig′) ≡ IG.muxes (IG.execution ig) →
  Chain q mid s ig → Chain q mid s ig′
stable-chain handlesSame muxesSame = anchors-preserve-chain
  (record { handlesSame = handlesSame
          ; muxesRetained = λ mid m found → m , trans (cong (lookup mid) muxesSame) found , refl })

open import ConnectionManagement.Properties.LoopRetention public using (CoveredLoop; deactivate; flush; capture; inactivity; select; read; idleTimer; finish; poll; expire; read-engine)
import ConnectionManagement.Properties.LoopRetention as Retention

worker-chain : ∀ a → CoveredLoop a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain a covered ig queue s eq chain =
  anchors-preserve-chain (Retention.worker-anchors a covered ig queue eq) chain

mode-chain : ∀ mode a → CoveredLoop a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain noResponderMode a covered ig queue s () chain
mode-chain responderMode a covered ig queue s eq chain = worker-chain a covered ig queue s eq chain

step-preserves : ∀ a → CoveredLoop a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)
