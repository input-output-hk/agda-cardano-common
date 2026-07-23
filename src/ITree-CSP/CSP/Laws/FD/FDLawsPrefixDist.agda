{-# OPTIONS --guardedness #-}

-- ⊓-distribution for prefix:  a →₀ (P ⊓ Q)  ≈FD  (a →₀ P) ⊓ (a →₀ Q).
--
-- This is FD-only: it is not even a weak-bisim law (the two sides differ in initial
-- stability — the left offers `a` immediately while the right must first resolve the
-- internal choice).  So it goes the FD-direct route, which needs a failures /
-- divergences decomposition of prefix (built here, reusable) composed with the ⊓
-- decomposition from FDLawsIChoiceAssoc.
--
-- KEY fact: the offered events of a prefix node do NOT depend on its continuation,
-- so refusals after the empty trace are continuation-independent (`prefix₀-refuses`).

open import Level using (Level)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.FDLawsPrefixDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (stable-no-τ)
open import CSP.Laws.Bisim.Congruence   E-≟ using (pc-just)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)

private
  variable
    ℓr ℓx : Level
    A : Set ℓ
    R : Set ℓr

-------------------------------------------------------------------------------------
-- Prefix is stable, and every big-step out of it is either empty or peels the event.
-------------------------------------------------------------------------------------

prefix₀-stable : (e : E A) (C : PTree E (ExtI E) R) → isStable (Prefix₀ e C)
prefix₀-stable e C _ _ = refl

prefix₀-⟹-inv : (e : E A) (C : PTree E (ExtI E) R)
                {s : List (Event√ R)} {W : PTree E (ExtI E) R}
              → (Prefix₀ e C) ⟹⟨ s ⟩ W
              → (W ≡ Prefix₀ e C × s ≡ [])
              ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                   (s ≡ evl (evLabel A e x) ∷ t × C ⟹⟨ t ⟩ W))
prefix₀-⟹-inv e C ⟹-refl              = inj₁ (refl , refl)
prefix₀-⟹-inv e C (⟹-τ (sSil ()) _)
prefix₀-⟹-inv e C (⟹-τ (sTau refl ()) _)
prefix₀-⟹-inv e C (⟹-ev (sRet ()) _)
prefix₀-⟹-inv {A = A} e C (⟹-ev (sVis {at = at} {a = x} refl br) rest)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = inj₂ (x , _ , refl , rest)

-------------------------------------------------------------------------------------
-- Offers / refusals of a prefix are CONTINUATION-INDEPENDENT.
-------------------------------------------------------------------------------------

prefix₀-offers : (e : E A) (C D : PTree E (ExtI E) R) {l : Event√ R}
               → Offers (Prefix₀ e C) l → Offers (Prefix₀ e D) l
prefix₀-offers e C D (_ , sRet ())
prefix₀-offers {A = A} e C D (W , sVis {at = at} {a = x} refl br) with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = D , sVis {at = A , e} {a = x} refl (pc-just e D x)

prefix₀-refuses : (e : E A) (C D : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                → Refuses (Prefix₀ e C) X → Refuses (Prefix₀ e D) X
prefix₀-refuses e C D (_ , noOff) =
  prefix₀-stable e D , λ l Xl off → noOff l Xl (prefix₀-offers e D C off)

-------------------------------------------------------------------------------------
-- Failures of prefix:  { ([] , refusing) } ∪ { a∷s : failure of the continuation }.
-------------------------------------------------------------------------------------

prefix₀-failures→ : (e : E A) (C : PTree E (ExtI E) R)
                    {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                  → failures (Prefix₀ e C) s X
                  → ((s ≡ []) × Refuses (Prefix₀ e C) X)
                  ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                       (s ≡ evl (evLabel A e x) ∷ t × failures C t X))
prefix₀-failures→ e C (W , pw , ref) with prefix₀-⟹-inv e C pw
... | inj₁ (refl , refl)          = inj₁ (refl , ref)
... | inj₂ (x , t , refl , reach) = inj₂ (x , t , refl , (W , reach , ref))

prefix₀-failures-nil : (e : E A) (C : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                     → Refuses (Prefix₀ e C) X → failures (Prefix₀ e C) [] X
prefix₀-failures-nil e C ref = Prefix₀ e C , ⟹-refl , ref

prefix₀-failures-cons : (e : E A) (C : PTree E (ExtI E) R) (x : A)
                        {t : List (Event√ R)} {X : Event√ R → Set ℓx}
                      → failures C t X → failures (Prefix₀ e C) (evl (evLabel A e x) ∷ t) X
prefix₀-failures-cons {A = A} e C x (W , reach , ref) =
  W , ⟹-ev (sVis {at = A , e} {a = x} refl (pc-just e C x)) reach , ref

-------------------------------------------------------------------------------------
-- Divergences of prefix:  { a∷s : divergence of the continuation }  (prefix itself,
-- being stable, never diverges at the empty trace).
-------------------------------------------------------------------------------------

prefix₀-div→ : (e : E A) (C : PTree E (ExtI E) R) {s : List (Event√ R)}
             → divergences (Prefix₀ e C) s
             → Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                 (s ≡ evl (evLabel A e x) ∷ t × divergences C t)
prefix₀-div→ e C d with prefix₀-⟹-inv e C (d .IsDivergence.reach)
... | inj₁ (eqW , _) =
        ⊥-elim (stable-no-τ (prefix₀-stable e C)
                  (subst Diverges eqW (d .IsDivergence.divwit) .Diverges.step))
... | inj₂ (x , t , eqPrefix , reach) =
        x , t ++ d .IsDivergence.suffix
          , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) eqPrefix)
          , record { prefix  = t                       ; suffix = d .IsDivergence.suffix
                   ; split   = refl                     ; witness = d .IsDivergence.witness
                   ; reach   = reach                     ; divwit = d .IsDivergence.divwit }

prefix₀-div-cons : (e : E A) (C : PTree E (ExtI E) R) (x : A) {t : List (Event√ R)}
                 → divergences C t → divergences (Prefix₀ e C) (evl (evLabel A e x) ∷ t)
prefix₀-div-cons {A = A} e C x d = record
  { prefix  = evl (evLabel A e x) ∷ d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix
  ; split   = cong (evl (evLabel A e x) ∷_) (d .IsDivergence.split)
  ; witness = d .IsDivergence.witness
  ; reach   = ⟹-ev (sVis {at = A , e} {a = x} refl (pc-just e C x)) (d .IsDivergence.reach)
  ; divwit  = d .IsDivergence.divwit }

-------------------------------------------------------------------------------------
-- Lift the failures and divergence decompositions to failures⊥.
-------------------------------------------------------------------------------------

prefix₀-failures⊥→ : (e : E A) (C : PTree E (ExtI E) R)
                     {s : List (Event√ R)} {B : Event√ R → Set ℓr}
                   → failures⊥ (Prefix₀ e C) s B
                   → ((s ≡ []) × Refuses (Prefix₀ e C) B)
                   ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                        (s ≡ evl (evLabel A e x) ∷ t × failures⊥ C t B))
prefix₀-failures⊥→ e C (inj₁ f) with prefix₀-failures→ e C f
... | inj₁ (eqs , ref)          = inj₁ (eqs , ref)
... | inj₂ (x , t , eqs , fC)   = inj₂ (x , t , eqs , inj₁ fC)
prefix₀-failures⊥→ e C (inj₂ d) with prefix₀-div→ e C d
... | (x , t , eqs , dC)        = inj₂ (x , t , eqs , inj₂ dC)

prefix₀-failures⊥-nil : (e : E A) (C : PTree E (ExtI E) R) {B : Event√ R → Set ℓr}
                      → Refuses (Prefix₀ e C) B → failures⊥ (Prefix₀ e C) [] B
prefix₀-failures⊥-nil e C ref = inj₁ (prefix₀-failures-nil e C ref)

prefix₀-failures⊥-cons : (e : E A) (C : PTree E (ExtI E) R) (x : A)
                         {t : List (Event√ R)} {B : Event√ R → Set ℓr}
                       → failures⊥ C t B → failures⊥ (Prefix₀ e C) (evl (evLabel A e x) ∷ t) B
prefix₀-failures⊥-cons e C x (inj₁ fC) = inj₁ (prefix₀-failures-cons e C x fC)
prefix₀-failures⊥-cons e C x (inj₂ dC) = inj₂ (prefix₀-div-cons e C x dC)

-------------------------------------------------------------------------------------
-- The distribution law, assembled by routing each behaviour to the matching side.
-------------------------------------------------------------------------------------

module _ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) (P Q : PTree E (ExtI E) R) where

  private
    L = Prefix₀ e (P ⊓ Q)
    Rt = (Prefix₀ e P) ⊓ (Prefix₀ e Q)

  dist-F⊥→ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ L s B → failures⊥ Rt s B
  dist-F⊥→ f with prefix₀-failures⊥→ e (P ⊓ Q) f
  ... | inj₁ (refl , ref) =
          ⊓-failures⊥←l (Prefix₀ e P) (Prefix₀ e Q)
            (prefix₀-failures⊥-nil e P (prefix₀-refuses e (P ⊓ Q) P ref))
  ... | inj₂ (x , t , refl , fbot) with ⊓-failures⊥→ P Q fbot
  ...   | inj₁ fP = ⊓-failures⊥←l (Prefix₀ e P) (Prefix₀ e Q) (prefix₀-failures⊥-cons e P x fP)
  ...   | inj₂ fQ = ⊓-failures⊥←r (Prefix₀ e P) (Prefix₀ e Q) (prefix₀-failures⊥-cons e Q x fQ)

  dist-F⊥← : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ Rt s B → failures⊥ L s B
  dist-F⊥← f with ⊓-failures⊥→ (Prefix₀ e P) (Prefix₀ e Q) f
  ... | inj₁ fP with prefix₀-failures⊥→ e P fP
  ...   | inj₁ (refl , ref)        = prefix₀-failures⊥-nil e (P ⊓ Q) (prefix₀-refuses e P (P ⊓ Q) ref)
  ...   | inj₂ (x , t , refl , fb) = prefix₀-failures⊥-cons e (P ⊓ Q) x (⊓-failures⊥←l P Q fb)
  dist-F⊥← f | inj₂ fQ with prefix₀-failures⊥→ e Q fQ
  ...   | inj₁ (refl , ref)        = prefix₀-failures⊥-nil e (P ⊓ Q) (prefix₀-refuses e Q (P ⊓ Q) ref)
  ...   | inj₂ (x , t , refl , fb) = prefix₀-failures⊥-cons e (P ⊓ Q) x (⊓-failures⊥←r P Q fb)

  dist-D→ : ∀ {s} → divergences L s → divergences Rt s
  dist-D→ d with prefix₀-div→ e (P ⊓ Q) d
  ... | (x , t , refl , dbot) with ⊓-div→ P Q dbot
  ...   | inj₁ dP = ⊓-div←l (Prefix₀ e P) (Prefix₀ e Q) (prefix₀-div-cons e P x dP)
  ...   | inj₂ dQ = ⊓-div←r (Prefix₀ e P) (Prefix₀ e Q) (prefix₀-div-cons e Q x dQ)

  dist-D← : ∀ {s} → divergences Rt s → divergences L s
  dist-D← d with ⊓-div→ (Prefix₀ e P) (Prefix₀ e Q) d
  ... | inj₁ dP with prefix₀-div→ e P dP
  ...   | (x , t , refl , db) = prefix₀-div-cons e (P ⊓ Q) x (⊓-div←l P Q db)
  dist-D← d | inj₂ dQ with prefix₀-div→ e Q dQ
  ...   | (x , t , refl , db) = prefix₀-div-cons e (P ⊓ Q) x (⊓-div←r P Q db)

  ⟶₀-⊓-dist-FD : (Prefix₀ e (P ⊓ Q)) ≈FD ((Prefix₀ e P) ⊓ (Prefix₀ e Q))
  ⟶₀-⊓-dist-FD = (dist-F⊥← , dist-D←) , (dist-F⊥→ , dist-D→)
