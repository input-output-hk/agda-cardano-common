{-# OPTIONS --guardedness #-}

-- Publication and handler-exit boundaries preserve existing reference chains.
-- Cleanup execution, negotiation consumers and IG updates remain separate.
module ConnectionManagement.Properties.HandlerBoundaries where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerCapture using (exit-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.Cleanup as C
import ConnectionManagement.Rules.IGRegistration as IG

-- Changing cleanup control state does not change any original reference.
cleanup-chain : ∀ w pc {q mid s ig} → Chain q mid s ig → Chain q mid (C.setCleanup w pc s) ig
cleanup-chain w pc chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

-- A fresh promise write cannot replace the result used by an existing chain.
fresh-result-chain : ∀ p result {q mid s ig} → lookup p (handshakeResults s) ≡ nothing →
  Chain q mid s ig → Chain q mid (record s { handshakeResults = put p result (handshakeResults s) }) ig
fresh-result-chain p result {s = s} absent chain with handlerPromise (originalHandler chain) ≟ p
... | yes same = case trans (sym absent) (subst (λ k → lookup k (handshakeResults s) ≡ _) same (promiseFound chain)) of λ ()
... | no different = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain
  ; promiseFound = trans (lookup-put-other p (handlerPromise (originalHandler chain)) result (handshakeResults s) different) (promiseFound chain)
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

publication-chain : ∀ w result s {s′ q mid ig} → H.publishBoundary w result s ≡ just (H.published s′) →
  Chain q mid s ig → Chain q mid s′ ig
publication-chain w result s eq chain with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = case eq of λ ()
...   | true with lookup (handlerPromise h) (handshakeResults s) in found
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = fresh-result-chain (handlerPromise h) result found chain

exit-chain : ∀ w s {s′ q mid ig} → C.beginCleanupBoundary w s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
exit-chain w s eq chain with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
... | just _ | nothing with just-injective eq
...   | refl = cleanup-chain w cleanupAcquire chain

publication-preserves : ∀ w result outcome c {c′} → advance (handlerPublication w result outcome) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
publication-preserves w result outcome c eq q (f , found , chain)
  with any (λ v → does (v ≟ w)) (publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary w result (world c) in published | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published s) | resultWritten with just-injective eq
...     | refl = f , found , publication-chain w result (world c) published chain
publication-preserves w result outcome c eq q (f , found , chain) | false | just (H.published s) | duplicateWrite = case eq of λ ()
publication-preserves w result outcome c eq q (f , found , chain) | false | just H.writerBlocked | resultWritten = case eq of λ ()
publication-preserves w result outcome c eq q (f , found , chain) | false | just H.writerBlocked | duplicateWrite with just-injective eq
... | refl = f , found , chain

exit-preserves : ∀ w c {c′} → advance (handlerExit w) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
exit-preserves w c eq q (f , found , chain) with L.mayExit w (handlerLifecycles c)
... | false = case eq of λ ()
... | true with C.beginCleanupBoundary w (world c) in entered
...   | nothing = case eq of λ ()
...   | just s with just-injective eq
...     | refl with exit-retains w (handlerLifecycles c) q f found
...       | g , retained , same = g , retained , subst (λ mid → Chain q mid s (inboundGovernor c)) (sym same)
  (exit-chain w (world c) entered chain)

-- Explicit coverage, extending rather than changing the lifecycle-only API.
data HandlerActions : List Action → Set where
  empty : HandlerActions []
  lifecycle : ∀ {w a as} → HandlerActions as → HandlerActions (handlerStep w a ∷ as)
  publication : ∀ {w result outcome as} → HandlerActions as → HandlerActions (handlerPublication w result outcome ∷ as)
  exit : ∀ {w as} → HandlerActions as → HandlerActions (handlerExit w ∷ as)

handler-exec-preserves : ∀ {c as c′} → HandlerActions as → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
handler-exec-preserves empty done q chain = chain
handler-exec-preserves (lifecycle {w} {a} only) (next {c = c} eq rest) q chain =
  handler-exec-preserves only rest q (handler-step-preserves w a c eq q chain)
handler-exec-preserves (publication {w} {result} {outcome} only) (next {c = c} eq rest) q chain =
  handler-exec-preserves only rest q (publication-preserves w result outcome c eq q chain)
handler-exec-preserves (exit {w} only) (next {c = c} eq rest) q chain =
  handler-exec-preserves only rest q (exit-preserves w c eq q chain)
