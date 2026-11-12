{-# OPTIONS --safe --guardedness #-}

-- Honest requests are canonical when their EB table fits the wire ceiling.
-- The premise also applies to locally forged bodies; fetchBody alone does not
-- constrain the forge/store path.
open import Cardano_network.Params using (Params)
module Cardano_network.Parametric.Leios.ChunksCanonical (p : Params) where

open import Data.Bool using (T)
open import Data.List using (List; []; _∷_; _++_; concat; length; applyUpTo)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _≤ᵇ_; _<ᵇ_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Cardano_network.Replay.LeiosFetchWords
  using (canonical; canonicalFrom; canonical-lower; canonical-bound; canonical-tail; ∧-intro)
open import Cardano_network.Parametric.Leios.LeiosParams p

-- Relax the initial lower bound without changing strict ordering or the cap.
canonical-weaken : ∀ lo hi xs → lo ≤ hi → T (canonicalFrom hi xs) → T (canonicalFrom lo xs)
canonical-weaken lo hi [] low can = tt
canonical-weaken lo hi (x ∷ xs) low can =
  ∧-intro {a = lo ≤ᵇ x} {b = (x <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc x) xs}
    (N.≤⇒≤ᵇ (N.≤-trans low (canonical-lower hi x xs can)))
    (∧-intro {a = x <ᵇ maxTxs} {b = canonicalFrom (suc x) xs}
      (N.<⇒<ᵇ (canonical-bound hi x xs can)) (canonical-tail hi x xs can))

-- A canonical concatenation gives a canonical prefix and a canonical suffix.
canonical-split : ∀ lo xs ys → T (canonicalFrom lo (xs ++ ys)) →
  T (canonicalFrom lo xs) × T (canonical ys)
canonical-split lo [] ys can = tt , canonical-weaken 0 lo ys z≤n can
canonical-split lo (x ∷ xs) ys can =
  ∧-intro {a = lo ≤ᵇ x} {b = (x <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc x) xs}
    (N.≤⇒≤ᵇ (canonical-lower lo x (xs ++ ys) can))
    (∧-intro {a = x <ᵇ maxTxs} {b = canonicalFrom (suc x) xs}
      (N.<⇒<ᵇ (canonical-bound lo x (xs ++ ys) can)) (proj₁ rest)) , proj₂ rest
  where
  -- Recurse after removing the shared head of the concatenation.
  rest = canonical-split (suc x) xs ys (canonical-tail lo x (xs ++ ys) can)

-- Every component of a canonical concatenation is itself canonical.
canonical-chunks : ∀ xss → T (canonical (concat xss)) → All (λ xs → T (canonical xs)) xss
canonical-chunks [] can = []
canonical-chunks (xs ∷ xss) can = proj₁ parts ∷ canonical-chunks xss (proj₂ parts)
  where
  -- Split at the first chunk boundary.
  parts = canonical-split 0 xs (concat xss) can

-- Increasing tabulations below the cap satisfy the Boolean canonical predicate.
canonical-tabulate : ∀ n (f : ℕ → ℕ) lo → lo ≤ f 0 →
  (∀ i → i < n → f i < maxTxs) → (∀ i → suc (f i) ≤ f (suc i)) →
  T (canonicalFrom lo (applyUpTo f n))
canonical-tabulate zero f lo low bounded increasing = tt
canonical-tabulate (suc n) f lo low bounded increasing =
  ∧-intro {a = lo ≤ᵇ f 0} {b = (f 0 <ᵇ maxTxs) Data.Bool.∧ canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
    (N.≤⇒≤ᵇ low)
    (∧-intro {a = f 0 <ᵇ maxTxs} {b = canonicalFrom (suc (f 0)) (applyUpTo (λ i → f (suc i)) n)}
      (N.<⇒<ᵇ (bounded 0 (s≤s z≤n)))
      (canonical-tabulate n (λ i → f (suc i)) (suc (f 0)) (increasing 0)
        (λ i lt → bounded (suc i) (s≤s lt)) (λ i → increasing (suc i))))

-- All body offsets are ordered and below maxTxs when the table fits the cap.
allOffsets-canonical : ∀ lp h → length (LeiosParams.ebTxs lp h) ≤ maxTxs →
  T (canonical (allOffsets lp h))
allOffsets-canonical lp h bounded = canonical-tabulate (length (LeiosParams.ebTxs lp h))
  (λ i → i) 0 N.≤-refl (λ i lt → N.≤-trans lt bounded) (λ i → N.≤-refl)

-- Partitioning the complete ordered offset list preserves canonicity per request.
txChunks-canonical : ∀ lp h → length (LeiosParams.ebTxs lp h) ≤ maxTxs →
  All (λ bm → T (canonical bm)) (txChunks lp h)
txChunks-canonical lp h bounded = canonical-chunks (txChunks lp h)
  (subst (λ xs → T (canonical xs))
    (sym (chunksOf-concat {xs = allOffsets lp h} (LeiosParams.chunk-pos lp)))
    (allOffsets-canonical lp h bounded))
