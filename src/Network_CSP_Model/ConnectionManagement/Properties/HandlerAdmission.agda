{-# OPTIONS --guardedness #-}

-- Existing chains survive admission; this does not establish a new chain.
module ConnectionManagement.Properties.HandlerAdmission where

open import Data.Nat using (suc; _≤?_)
open import Data.List using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerCleanup using (take-entries; put-entries)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.CM as CM

-- Transport unchanged immutable stores and retained mutable resource identities.
reframe : ∀ {q mid s ig} s′ → handlers s′ ≡ handlers s →
  handshakeResults s′ ≡ handshakeResults s →
  (∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))) →
  (∀ sock → Present sock (sockets s) → Present sock (sockets s′)) →
  Chain q mid s ig → Chain q mid s′ ig
reframe s′ hs ps ep sp chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain; keyMatches = keyMatches chain
  ; handlerFound = trans (cong (lookup _) hs) (handlerFound chain)
  ; promiseFound = trans (cong (lookup _) ps) (promiseFound chain)
  ; entryPresent = ep _ (entryPresent chain); socketPresent = sp _ (socketPresent chain) }

-- The absent child guard protects all already-published handler records.
fresh-handler-chain : ∀ w h {q mid s ig} → lookup w (handlers s) ≡ nothing →
  Chain q mid s ig → Chain q mid (record s { handlers = put w h (handlers s) }) ig
fresh-handler-chain w h {q} {s = s} absent chain with q ≟ w
... | yes same = case trans (sym absent) (subst (λ k → lookup k (handlers s) ≡ _) same (handlerFound chain)) of λ ()
... | no different = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain; keyMatches = keyMatches chain
  ; promiseFound = promiseFound chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain
  ; handlerFound = trans (lookup-put-other w q h (handlers s) different) (handlerFound chain) }

open import ConnectionManagement.Properties.AdmissionRetention public using
  (fresh-present; existing-present; selected-present)
import ConnectionManagement.Properties.AdmissionRetention as Retention
import ConnectionManagement.Properties.HandlerStateRetention as StateRetention

-- Preserve the old chain theorem through the shared admission effects.
worker-chain : ∀ {q mid ig} act w a s {s′} → S.stepWorker w a act s ≡ just s′ →
  Chain q mid s ig → Chain q mid s′ ig
worker-chain act w a s eq = StateRetention.retains-chain (Retention.worker-retains act w a s eq)

-- The dispatcher changes the world only; lifecycle frames and IG stay intact.
step-preserves : ∀ w a c {c′} → advance (admissionStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves w a c eq q (f , found , chain) with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with S.stepWorker w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = f , found , worker-chain a w a₀ (world c) stepped chain
