{-# OPTIONS --guardedness #-}

-- Cleanup retains original references even when socket and entry values change.
module ConnectionManagement.Properties.HandlerCleanup where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.HandlerReferences hiding (exec-preserves)
open import ConnectionManagement.Properties.HandlerBoundaries using (publication-preserves; exit-preserves)
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

-- The three fields cleanup may update; presence, not the old resource value,
-- is the invariant. Handler and negotiated-result stores remain unchanged.
reframe : ∀ {q mid s ig} c′ ss pcs →
  (∀ e → Present e (entries (cm s)) → Present e (entries c′)) →
  (∀ sock → Present sock (sockets s) → Present sock ss) →
  Chain q mid s ig → Chain q mid (record s { cm = c′; sockets = ss; cleanups = pcs }) ig
reframe c′ ss pcs ep sp chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain
  ; entryPresent = ep _ (entryPresent chain); socketPresent = sp _ (socketPresent chain) }

-- Preserve existing helper signatures while sharing the source-rule analysis.
open import ConnectionManagement.Properties.CleanupRetention public using (take-entries; put-entries; finish-present)
import ConnectionManagement.Properties.CleanupRetention as Retention

select-preserves : ∀ w h l decision s {q mid ig} →
  Chain q mid s ig → Chain q mid (Cleanup.selectCleanup w h l decision s) ig
select-preserves w h l decision s = Retention.retains-chain (Retention.select-retains w h l decision s)

cleanup-preserves : ∀ {q mid ig} action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
cleanup-preserves action w h p s eq = Retention.retains-chain (Retention.worker-retains action w h p s eq)

-- Lift from a selected cleanup worker to the actual dispatcher.
step-preserves : ∀ w a c {c′} → advance (cleanupStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with Cleanup.stepCleanup w a (world c) in stepped
... | nothing = case eq of λ ()
... | just s with just-injective eq
...   | refl = f , found , worker-chain w a (world c) stepped chain
  where
  worker-chain : ∀ w a s {s′ q mid ig} → Cleanup.stepCleanup w a s ≡ just s′ →
    Chain q mid s ig → Chain q mid s′ ig
  worker-chain w a s eq chain with lookup w (handlers s) | lookup w (cleanups s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | nothing = case eq of λ ()
  ... | just h | just p = cleanup-preserves a w h p s eq chain

-- Includes all cleanup outcomes, with arbitrary actors at every step.
data CleanupActions : List Action → Set where
  empty : CleanupActions []
  lifecycle : ∀ {w a as} → CleanupActions as → CleanupActions (handlerStep w a ∷ as)
  publication : ∀ {w result outcome as} → CleanupActions as → CleanupActions (handlerPublication w result outcome ∷ as)
  exit : ∀ {w as} → CleanupActions as → CleanupActions (handlerExit w ∷ as)
  cleanup : ∀ {w a as} → CleanupActions as → CleanupActions (cleanupStep w a ∷ as)

exec-preserves : ∀ {c as c′} → CleanupActions as → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
exec-preserves empty done q chain = chain
exec-preserves (lifecycle {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (handler-step-preserves w a c eq q chain)
exec-preserves (publication {w} {result} {outcome} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (publication-preserves w result outcome c eq q chain)
exec-preserves (exit {w} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (exit-preserves w c eq q chain)
exec-preserves (cleanup {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (step-preserves w a c eq q chain)
