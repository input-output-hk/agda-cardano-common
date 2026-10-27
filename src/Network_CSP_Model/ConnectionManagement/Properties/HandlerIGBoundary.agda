{-# OPTIONS --guardedness #-}

-- Decision publication and fresh installation retain existing reference chains.
-- Other IG actions, including mux execution and responder restart, are separate.
module ConnectionManagement.Properties.HandlerIGBoundary where

open import Data.Bool using (true; false)
open import Data.List using (map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put; Store)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.HandlerReferences
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

open import ConnectionManagement.Properties.IGTableRetention public using (fresh-lookup)

-- This helper describes only table growth; the actual rule enforces freshness.
extend-chain : ∀ hid hd mid m {q captured s ig} →
  lookup hid (IG.handles (IG.execution ig)) ≡ nothing →
  lookup mid (IG.muxes (IG.execution ig)) ≡ nothing → Chain q captured s ig →
  Chain q captured s (record ig { execution = record (IG.execution ig)
    { handles = put hid hd (IG.handles (IG.execution ig)); muxes = put mid m (IG.muxes (IG.execution ig)) } })
extend-chain hid hd mid m {ig = ig} noHandle noMux chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = fresh-lookup hid _ hd _ (IG.handles (IG.execution ig)) noHandle (handleFound chain)
  ; handleMux = handleMux chain
  ; muxFound = fresh-lookup mid _ m _ (IG.muxes (IG.execution ig)) noMux (muxFound chain)
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

-- Publication may replace all governor membership, but leaves the engine intact.
control-chain : ∀ old n pc {q mid s ig} → Chain q mid s ig →
  Chain q mid s (IG.runtimeState old n pc (IG.execution ig))
control-chain old n pc chain = anchors-preserve-chain
  (record { handlesSame = refl; muxesRetained = λ mid m found → m , found , refl }) chain

-- Queue updates do not alter handler resources or negotiation results.
queue-chain : ∀ queue {q mid s ig} → Chain q mid s ig →
  Chain q mid (record s { inboundInfo = queue }) ig
queue-chain queue chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

open import ConnectionManagement.Properties.IGBoundaryRetention public using (CoveredIG; decision; install; installOutbound)
import ConnectionManagement.Properties.IGBoundaryRetention as Retention
open import ConnectionManagement.Properties.HandlerTableRetention using (retains-chain)

worker-chain : ∀ a → CoveredIG a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain a covered ig queue s eq = retains-chain (Retention.worker-retains a covered ig queue eq)

mode-chain : ∀ mode a → CoveredIG a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain mode a covered ig queue s eq chain =
  retains-chain (Retention.mode-retains mode a covered ig queue eq) chain

step-preserves : ∀ a → CoveredIG a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)
