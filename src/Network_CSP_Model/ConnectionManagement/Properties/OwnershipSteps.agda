{-# OPTIONS --guardedness #-}

-- Preservation through the actual cleanup socket-close dispatcher actions.
-- This is a first family of cases, not full dispatcher preservation.
module ConnectionManagement.Properties.OwnershipSteps where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
import ConnectionManagement.Rules.Cleanup as Cleanup
open import ConnectionManagement.Machine using (Configuration; world; advance; Action; cleanupStep)

-- Replacing an existing binding with the same projected claim preserves the
-- whole census. No uniqueness assumption is needed for this first-match update.
project-put-same : ∀ {K V A : Set} ⦃ _ : DecEq K ⦄ (f : K × V → List A) k old new xs →
  lookup k xs ≡ just old → f (k , new) ≡ f (k , old) →
  concatMap f (put k new xs) ≡ concatMap f xs
project-put-same f k old new [] () eq
project-put-same f k old new ((q , v) ∷ xs) found eq with k ≟ q
... | yes refl with found
...   | refl = cong (λ prefix → prefix ++ concatMap f xs) eq
project-put-same f k old new ((q , v) ∷ xs) found eq | no _ =
  cong (λ rest → f (q , v) ++ rest) (project-put-same f k old new xs found eq)

-- Socket updates do not appear in the census; continuation updates keep a lease.
close-state : WorkerId → HandlerStart → Lease → ConnMap → CleanupTail → State → State
close-state w h l m tail s = Cleanup.setCleanup w (cleanupPublish l m tail)
  (record s { sockets = put (handlerSocket h) closed (sockets s) })

fail-state : WorkerId → HandlerStart → Lease → ConnMap → CleanupTail → ErrorId → State → State
fail-state w h l m tail err s = Cleanup.setCleanup w (cleanupRestore l err)
  (record s { sockets = put (handlerSocket h) (closeUncertain err) (sockets s) })

close-preserves : ∀ w h l m tail s →
  lookup w (cleanups s) ≡ just (cleanupClose l m tail) → Ownership s →
  Ownership (close-state w h l m tail s)
close-preserves w h l m tail s found own =
  subst (Owns (mapCell (cm s))) (sym census) own
  where
  census : claims (close-state w h l m tail s) ≡ claims s
  census = cong (λ rest → concatMap admissionClaim (admissions s) ++ rest)
    (project-put-same cleanupClaim w (cleanupClose l m tail) (cleanupPublish l m tail)
      (cleanups s) found refl)

fail-preserves : ∀ w h l m tail err s →
  lookup w (cleanups s) ≡ just (cleanupClose l m tail) → Ownership s →
  Ownership (fail-state w h l m tail err s)
fail-preserves w h l m tail err s found own =
  subst (Owns (mapCell (cm s))) (sym census) own
  where
  census : claims (fail-state w h l m tail err s) ≡ claims s
  census = cong (λ rest → concatMap admissionClaim (admissions s) ++ rest)
    (project-put-same cleanupClaim w (cleanupClose l m tail) (cleanupRestore l err)
      (cleanups s) found refl)

-- Invert the real rule family, including all disabled continuation/action pairs.
close-worker : ∀ w h p s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p Cleanup.closeHandlerSocket s ≡ just s′ →
  Ownership s → Ownership s′
close-worker w h cleanupAcquire s found () own
close-worker w h (cleanupSelect l) s found () own
close-worker w h (cleanupPublish l m tail) s found () own
close-worker w h (cleanupRestore l err) s found () own
close-worker w h (cleanupWaiting st) s found () own
close-worker w h (cleanupFinalize st outcome) s found () own
close-worker w h (cleanupCount outcome) s found () own
close-worker w h (cleanupDone outcome) s found () own
close-worker w h (cleanupClose l m tail) s found eq own =
  subst Ownership (just-injective eq) (close-preserves w h l m tail s found own)

fail-worker : ∀ w h p err s {s′} → lookup w (cleanups s) ≡ just p →
  Cleanup.stepWorker w h p (Cleanup.failSocketClose err) s ≡ just s′ →
  Ownership s → Ownership s′
fail-worker w h cleanupAcquire err s found () own
fail-worker w h (cleanupSelect l) err s found () own
fail-worker w h (cleanupPublish l m tail) err s found () own
fail-worker w h (cleanupRestore l oldError) err s found () own
fail-worker w h (cleanupWaiting st) err s found () own
fail-worker w h (cleanupFinalize st outcome) err s found () own
fail-worker w h (cleanupCount outcome) err s found () own
fail-worker w h (cleanupDone outcome) err s found () own
fail-worker w h (cleanupClose l m tail) err s found eq own =
  subst Ownership (just-injective eq) (fail-preserves w h l m tail err s found own)

open import Function using (case_of_)

-- The statements below include the actual machine dispatch and its lookups.
close-advance : ∀ w c {c′} →
  advance (cleanupStep w Cleanup.closeHandlerSocket) c ≡ just c′ →
  Ownership (world c) → Ownership (world c′)
close-advance w c eq own
  with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just h | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p Cleanup.closeHandlerSocket (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Ownership (world config)) (just-injective eq)
      (close-worker w h p (world c) found stepped own)

fail-advance : ∀ w err c {c′} →
  advance (cleanupStep w (Cleanup.failSocketClose err)) c ≡ just c′ →
  Ownership (world c) → Ownership (world c′)
fail-advance w err c eq own
  with lookup w (handlers (world c)) | lookup w (cleanups (world c)) in found
... | nothing | _ = case eq of λ ()
... | just h | nothing = case eq of λ ()
... | just h | just p with Cleanup.stepWorker w h p (Cleanup.failSocketClose err) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ = subst (λ config → Ownership (world config)) (just-injective eq)
      (fail-worker w h p err (world c) found stepped own)
