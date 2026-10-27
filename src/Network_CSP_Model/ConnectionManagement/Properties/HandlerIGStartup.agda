{-# OPTIONS --guardedness #-}

-- Startup, restart and failed-start stop requests retain original references.
module ConnectionManagement.Properties.HandlerIGStartup where

open import Data.Bool using (true; false)
open import Data.List using (_++_; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)
open import ConnectionManagement.Properties.HandlerIGBoundary using (control-chain; queue-chain)
open import ConnectionManagement.Properties.MuxStartReferences using (one-key; bundle-key)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

open import ConnectionManagement.Properties.StartupRetention public using (CoveredStartup; start; restart; failedStop)
import ConnectionManagement.Properties.StartupRetention as Retention

worker-chain : ∀ a → CoveredStartup a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain a covered ig queue s eq chain =
  anchors-preserve-chain (Retention.worker-anchors a covered ig queue eq) chain

mode-chain : ∀ mode a → CoveredStartup a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain mode a covered ig queue s eq chain =
  anchors-preserve-chain (Retention.mode-anchors mode a covered ig queue eq) chain

step-preserves : ∀ a → CoveredStartup a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)
