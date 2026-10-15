{-# OPTIONS --guardedness #-}

-- Reuse the exact lease-census invariant for steps retaining the current lease.
module ConnectionManagement.Properties.OwnershipNeutral where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.Properties.OwnershipSteps using (project-put-same)
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CM as CM

admission-neutral : ∀ w a p s → lookup w (admissions s) ≡ just a →
  admissionLease p ≡ admissionLease (pc a) → Ownership s → Ownership (Server.setPC w a p s)
admission-neutral w a p s found same own = subst (Owns (mapCell (cm s))) (sym census) own
  where
  census : claims (Server.setPC w a p s) ≡ claims s
  census = cong (_++ concatMap cleanupClaim (cleanups s))
    (project-put-same admissionClaim w a (record a { pc = p }) (admissions s) found (cong (claim w) same))

cleanup-neutral : ∀ w old p s → lookup w (cleanups s) ≡ just old →
  cleanupLease p ≡ cleanupLease old → Ownership s → Ownership (Cleanup.setCleanup w p s)
cleanup-neutral w old p s found same own = subst (Owns (mapCell (cm s))) (sym census) own
  where
  census : claims (Cleanup.setCleanup w p s) ≡ claims s
  census = cong (concatMap admissionClaim (admissions s) ++_)
    (project-put-same cleanupClaim w old p (cleanups s) found (cong (claim w) same))

-- Inserting an absent, lease-free handler continuation also preserves the census.
project-put-empty : ∀ {K V A : Set} ⦃ _ : DecEq K ⦄ (f : K × V → List A) k v xs →
  lookup k xs ≡ nothing → f (k , v) ≡ [] → concatMap f (put k v xs) ≡ concatMap f xs
project-put-empty f k v [] found empty rewrite empty = refl
project-put-empty f k v ((q , old) ∷ xs) found empty with k ≟ q
... | yes _ = case found of λ ()
... | no _ = cong (f (q , old) ++_) (project-put-empty f k v xs found empty)

cleanup-new : ∀ w s → lookup w (cleanups s) ≡ nothing → Ownership s →
  Ownership (Cleanup.setCleanup w cleanupAcquire s)
cleanup-new w s found own = subst (Owns (mapCell (cm s))) (sym census) own
  where
  census : claims (Cleanup.setCleanup w cleanupAcquire s) ≡ claims s
  census = cong (concatMap admissionClaim (admissions s) ++_)
    (project-put-empty cleanupClaim w cleanupAcquire (cleanups s) found refl)

-- Entry selection changes the heap/supply but never the map ownership cell.
fresh-cell : ∀ r c {e c′} → CM.freshInbound r c ≡ just (CM.selected e c′) → mapCell c′ ≡ mapCell c
fresh-cell r c eq with lookup (ident (nextEntry c)) (entries c)
... | just _ = case eq of λ ()
... | nothing with just-injective eq
...   | refl = refl

existing-cell : ∀ e st r c {e′ c′} → CM.existingInbound e st r c ≡ just (CM.selected e′ c′) → mapCell c′ ≡ mapCell c
existing-cell e reservedOutbound r c refl = refl
existing-cell e (unnegotiated _ _ _) r c refl = refl
existing-cell e (outboundUni _ _ _) r c ()
existing-cell e (outboundDup _ _ _ _) r c ()
existing-cell e (outboundIdle _ _ _ _) r c ()
existing-cell e (inboundIdle _ _ _ _) r c ()
existing-cell e (inboundActive _ _ _ _) r c ()
existing-cell e (duplexActive _ _ _) r c ()
existing-cell e (terminating _ _ _) r c eq = fresh-cell r c eq
existing-cell e (terminated _) r c eq = fresh-cell r c eq

selected-cell : ∀ l r c {e c′} → CM.selectInbound l r c ≡ just (CM.selected e c′) → mapCell c′ ≡ mapCell c
selected-cell l r c eq with mapCell c in cell
... | full _ = case eq of λ ()
... | taken w with owner l ≟ w
...   | no _ = case eq of λ ()
...   | yes _ with lookupConnection (key r) (savedMap l)
...     | nothing = trans (fresh-cell r c eq) cell
...     | just e with lookup e (entries c)
...       | nothing = case eq of λ ()
...       | just st = trans (existing-cell e st r c eq) cell

replace-cm : ∀ s c′ → mapCell c′ ≡ mapCell (cm s) → Ownership s → Ownership (record s { cm = c′ })
replace-cm s c′ eq own = subst (λ cell → Owns cell (claims s)) (sym eq) own
