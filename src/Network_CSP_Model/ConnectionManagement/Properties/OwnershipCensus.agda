{-# OPTIONS --guardedness #-}

-- List-context lemmas for adding/removing the unique lease claim. These concern
-- the local first-match store update, not a new transition semantics.
module ConnectionManagement.Properties.OwnershipCensus where

open import Data.List using (List; []; _∷_; _++_; concatMap)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷-injectiveʳ)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Store using (lookup; put)

-- Replacing an existing binding changes precisely one projected list segment.
Splice : ∀ {A : Set} → List A → List A → List A → List A → Set
Splice old new before after = Σ _ (λ pre → Σ _ (λ post →
  before ≡ pre ++ (old ++ post) × after ≡ pre ++ (new ++ post)))

put-splice : ∀ {K V A : Set} ⦃ _ : DecEq K ⦄ (f : K × V → List A) k old new xs →
  lookup k xs ≡ just old →
  Splice (f (k , old)) (f (k , new)) (concatMap f xs) (concatMap f (put k new xs))
put-splice f k old new [] ()
put-splice f k old new ((q , v) ∷ xs) found with k ≟ q
... | yes refl with found
...   | refl = [] , concatMap f xs , refl , refl
put-splice f k old new ((q , v) ∷ xs) found | no _
  with put-splice f k old new xs found
... | pre , post , before , after = f (q , v) ++ pre , post ,
  trans (cong (f (q , v) ++_) before) (sym (++-assoc (f (q , v)) pre _)) ,
  trans (cong (f (q , v) ++_) after) (sym (++-assoc (f (q , v)) pre _))

prefix-splice : ∀ {A : Set} (prefix : List A) {old new before after} →
  Splice old new before after → Splice old new (prefix ++ before) (prefix ++ after)
prefix-splice prefix (pre , post , before , after) = prefix ++ pre , post ,
  trans (cong (prefix ++_) before) (sym (++-assoc prefix pre _)) ,
  trans (cong (prefix ++_) after) (sym (++-assoc prefix pre _))

suffix-splice : ∀ {A : Set} {old new before after} (suffix : List A) →
  Splice old new before after → Splice old new (before ++ suffix) (after ++ suffix)
suffix-splice {old = old} {new} suffix (pre , post , before , after) = pre , post ++ suffix ,
  trans (cong (_++ suffix) before) (trans (++-assoc pre _ suffix) (cong (pre ++_) (++-assoc old post suffix))) ,
  trans (cong (_++ suffix) after) (trans (++-assoc pre _ suffix) (cong (pre ++_) (++-assoc new post suffix)))

-- Empty and singleton census equations force the surrounding context empty.
insert-empty : ∀ {A : Set} (pre post : List A) x → pre ++ post ≡ [] →
  pre ++ (x ∷ post) ≡ x ∷ []
insert-empty [] .[] x refl = refl
insert-empty (_ ∷ _) post x ()

remove-single : ∀ {A : Set} (pre post : List A) x y → pre ++ (x ∷ post) ≡ y ∷ [] →
  pre ++ post ≡ []
remove-single [] post x y eq = ∷-injectiveʳ eq
remove-single (p ∷ pre) post x y eq = impossible pre post x (∷-injectiveʳ eq)
  where
  impossible : ∀ pre post x → pre ++ (x ∷ post) ≡ [] → (p ∷ pre) ++ post ≡ []
  impossible [] post x ()
  impossible (_ ∷ _) post x ()

acquire-census : ∀ {A : Set} {before after : List A} x →
  Splice [] (x ∷ []) before after → before ≡ [] → after ≡ x ∷ []
acquire-census x (pre , post , before , after) empty =
  trans after (insert-empty pre post x (trans (sym before) empty))

release-census : ∀ {A : Set} {before after : List A} x y →
  Splice (x ∷ []) [] before after → before ≡ y ∷ [] → after ≡ []
release-census x y (pre , post , before , after) single =
  trans after (remove-single pre post x y (trans (sym before) single))
