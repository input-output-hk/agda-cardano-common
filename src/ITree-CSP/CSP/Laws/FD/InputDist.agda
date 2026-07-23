{-# OPTIONS --guardedness #-}

-- input-dist (TPC 1.11 / UCS 2.11):  ?x:A → (P ⊓ Q) = (?x:A → P) ⊓ (?x:A → Q).
-- The VALUE-DEPENDENT generalisation of ⟶₀-⊓-dist-FD: the continuations P, Q : A → PTree
-- may depend on the input value x.  In this spike `Prefix e P` IS `?x:A → P(x)`, so the
-- law is  Prefix e (λ x → P x ⊓ Q x) ≈FD (Prefix e P) ⊓ (Prefix e Q).
--
-- FD-direct (the two sides differ in initial stability — left offers the input
-- immediately, right first resolves the ⊓), mirroring the constant-continuation proof:
-- a value-dependent failures/divergence decomposition of prefix (offers/refusals are
-- continuation-INDEPENDENT; the cons-case continuation is `P x`) composed with the ⊓
-- decomposition.

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

module CSP.Laws.FD.InputDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
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
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)

private
  variable
    ℓr ℓx : Level
    A : Set ℓ
    R : Set ℓr

-- the prefix offers value x ⇒ the (value-dependent) continuation P x.
pfx-cont-just : (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
              → Prefix-cont e P (A , e) x ≡ just (P x)
pfx-cont-just {A = A} e P x with E-≟ (A , e) (A , e)
... | yes refl = refl
... | no ¬eq   = ⊥-elim (¬eq refl)

pfx-stable : (e : E A) (P : A → PTree E (ExtI E) R) → isStable (Prefix e P)
pfx-stable e P _ _ = refl

-- every big-step out of a prefix is empty or peels the input event (cont = P x).
pfx-⟹-inv : (e : E A) (P : A → PTree E (ExtI E) R)
             {s : List (Event√ R)} {W : PTree E (ExtI E) R}
           → (Prefix e P) ⟹⟨ s ⟩ W
           → (W ≡ Prefix e P × s ≡ [])
           ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                (s ≡ evl (evLabel A e x) ∷ t × (P x) ⟹⟨ t ⟩ W))
pfx-⟹-inv e P ⟹-refl              = inj₁ (refl , refl)
pfx-⟹-inv e P (⟹-τ (sSil ()) _)
pfx-⟹-inv e P (⟹-τ (sTau refl ()) _)
pfx-⟹-inv e P (⟹-ev (sRet ()) _)
pfx-⟹-inv {A = A} e P (⟹-ev (sVis {at = at} {a = x} refl br) rest)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = inj₂ (x , _ , refl , rest)

-- offers / refusals are continuation-INDEPENDENT.
pfx-offers : (e : E A) (P D : A → PTree E (ExtI E) R) {l : Event√ R}
           → Offers (Prefix e P) l → Offers (Prefix e D) l
pfx-offers e P D (_ , sRet ())
pfx-offers {A = A} e P D (W , sVis {at = at} {a = x} refl br) with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = D x , sVis {at = A , e} {a = x} refl (pfx-cont-just e D x)

pfx-refuses : (e : E A) (P D : A → PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
            → Refuses (Prefix e P) X → Refuses (Prefix e D) X
pfx-refuses e P D (_ , noOff) =
  pfx-stable e D , λ l Xl off → noOff l Xl (pfx-offers e D P off)

-- failures of prefix: {([], refusing)} ∪ {x∷t : failure of P x}.
pfx-failures→ : (e : E A) (P : A → PTree E (ExtI E) R)
                {s : List (Event√ R)} {X : Event√ R → Set ℓx}
              → failures (Prefix e P) s X
              → ((s ≡ []) × Refuses (Prefix e P) X)
              ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                   (s ≡ evl (evLabel A e x) ∷ t × failures (P x) t X))
pfx-failures→ e P (W , pw , ref) with pfx-⟹-inv e P pw
... | inj₁ (refl , refl)          = inj₁ (refl , ref)
... | inj₂ (x , t , refl , reach) = inj₂ (x , t , refl , (W , reach , ref))

pfx-failures-nil : (e : E A) (P : A → PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                 → Refuses (Prefix e P) X → failures (Prefix e P) [] X
pfx-failures-nil e P ref = Prefix e P , ⟹-refl , ref

pfx-failures-cons : (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
                    {t : List (Event√ R)} {X : Event√ R → Set ℓx}
                  → failures (P x) t X → failures (Prefix e P) (evl (evLabel A e x) ∷ t) X
pfx-failures-cons {A = A} e P x (W , reach , ref) =
  W , ⟹-ev (sVis {at = A , e} {a = x} refl (pfx-cont-just e P x)) reach , ref

-- divergences of prefix: {x∷t : divergence of P x}.
pfx-div→ : (e : E A) (P : A → PTree E (ExtI E) R) {s : List (Event√ R)}
         → divergences (Prefix e P) s
         → Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
             (s ≡ evl (evLabel A e x) ∷ t × divergences (P x) t)
pfx-div→ e P d with pfx-⟹-inv e P (d .IsDivergence.reach)
... | inj₁ (eqW , _) =
        ⊥-elim (stable-no-τ (pfx-stable e P)
                  (subst Diverges eqW (d .IsDivergence.divwit) .Diverges.step))
... | inj₂ (x , t , eqPrefix , reach) =
        x , t ++ d .IsDivergence.suffix
          , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) eqPrefix)
          , record { prefix  = t                   ; suffix = d .IsDivergence.suffix
                   ; split   = refl                 ; witness = d .IsDivergence.witness
                   ; reach   = reach                 ; divwit = d .IsDivergence.divwit }

pfx-div-cons : (e : E A) (P : A → PTree E (ExtI E) R) (x : A) {t : List (Event√ R)}
             → divergences (P x) t → divergences (Prefix e P) (evl (evLabel A e x) ∷ t)
pfx-div-cons {A = A} e P x d = record
  { prefix  = evl (evLabel A e x) ∷ d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix
  ; split   = cong (evl (evLabel A e x) ∷_) (d .IsDivergence.split)
  ; witness = d .IsDivergence.witness
  ; reach   = ⟹-ev (sVis {at = A , e} {a = x} refl (pfx-cont-just e P x)) (d .IsDivergence.reach)
  ; divwit  = d .IsDivergence.divwit }

-- lift to failures⊥.
pfx-failures⊥→ : (e : E A) (P : A → PTree E (ExtI E) R)
                 {s : List (Event√ R)} {B : Event√ R → Set ℓr}
               → failures⊥ (Prefix e P) s B
               → ((s ≡ []) × Refuses (Prefix e P) B)
               ⊎ (Σ[ x ∈ A ] Σ[ t ∈ List (Event√ R) ]
                    (s ≡ evl (evLabel A e x) ∷ t × failures⊥ (P x) t B))
pfx-failures⊥→ e P (inj₁ f) with pfx-failures→ e P f
... | inj₁ (eqs , ref)        = inj₁ (eqs , ref)
... | inj₂ (x , t , eqs , fC) = inj₂ (x , t , eqs , inj₁ fC)
pfx-failures⊥→ e P (inj₂ d) with pfx-div→ e P d
... | (x , t , eqs , dC)      = inj₂ (x , t , eqs , inj₂ dC)

pfx-failures⊥-nil : (e : E A) (P : A → PTree E (ExtI E) R) {B : Event√ R → Set ℓr}
                  → Refuses (Prefix e P) B → failures⊥ (Prefix e P) [] B
pfx-failures⊥-nil e P ref = inj₁ (pfx-failures-nil e P ref)

pfx-failures⊥-cons : (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
                     {t : List (Event√ R)} {B : Event√ R → Set ℓr}
                   → failures⊥ (P x) t B → failures⊥ (Prefix e P) (evl (evLabel A e x) ∷ t) B
pfx-failures⊥-cons e P x (inj₁ fC) = inj₁ (pfx-failures-cons e P x fC)
pfx-failures⊥-cons e P x (inj₂ dC) = inj₂ (pfx-div-cons e P x dC)

-------------------------------------------------------------------------------------
-- the law, assembled exactly as ⟶₀-⊓-dist-FD but with value-dependent continuations.
-------------------------------------------------------------------------------------
module _ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) (P Q : A → PTree E (ExtI E) R) where

  private
    PQ : A → PTree E (ExtI E) R
    PQ x = P x ⊓ Q x

  dist-F⊥→ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ (Prefix e PQ) s B → failures⊥ ((Prefix e P) ⊓ (Prefix e Q)) s B
  dist-F⊥→ f with pfx-failures⊥→ e PQ f
  ... | inj₁ (refl , ref) =
          ⊓-failures⊥←l (Prefix e P) (Prefix e Q) (pfx-failures⊥-nil e P (pfx-refuses e PQ P ref))
  ... | inj₂ (x , t , refl , fbot) with ⊓-failures⊥→ (P x) (Q x) fbot
  ...   | inj₁ fP = ⊓-failures⊥←l (Prefix e P) (Prefix e Q) (pfx-failures⊥-cons e P x fP)
  ...   | inj₂ fQ = ⊓-failures⊥←r (Prefix e P) (Prefix e Q) (pfx-failures⊥-cons e Q x fQ)

  dist-F⊥← : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ ((Prefix e P) ⊓ (Prefix e Q)) s B → failures⊥ (Prefix e PQ) s B
  dist-F⊥← f with ⊓-failures⊥→ (Prefix e P) (Prefix e Q) f
  ... | inj₁ fP with pfx-failures⊥→ e P fP
  ...   | inj₁ (refl , ref)        = pfx-failures⊥-nil e PQ (pfx-refuses e P PQ ref)
  ...   | inj₂ (x , t , refl , fb) = pfx-failures⊥-cons e PQ x (⊓-failures⊥←l (P x) (Q x) fb)
  dist-F⊥← f | inj₂ fQ with pfx-failures⊥→ e Q fQ
  ...   | inj₁ (refl , ref)        = pfx-failures⊥-nil e PQ (pfx-refuses e Q PQ ref)
  ...   | inj₂ (x , t , refl , fb) = pfx-failures⊥-cons e PQ x (⊓-failures⊥←r (P x) (Q x) fb)

  dist-D→ : ∀ {s} → divergences (Prefix e PQ) s → divergences ((Prefix e P) ⊓ (Prefix e Q)) s
  dist-D→ d with pfx-div→ e PQ d
  ... | (x , t , refl , db) with ⊓-div→ (P x) (Q x) db
  ...   | inj₁ dP = ⊓-div←l (Prefix e P) (Prefix e Q) (pfx-div-cons e P x dP)
  ...   | inj₂ dQ = ⊓-div←r (Prefix e P) (Prefix e Q) (pfx-div-cons e Q x dQ)

  dist-D← : ∀ {s} → divergences ((Prefix e P) ⊓ (Prefix e Q)) s → divergences (Prefix e PQ) s
  dist-D← d with ⊓-div→ (Prefix e P) (Prefix e Q) d
  ... | inj₁ dP with pfx-div→ e P dP
  ...   | (x , t , refl , db) = pfx-div-cons e PQ x (⊓-div←l (P x) (Q x) db)
  dist-D← d | inj₂ dQ with pfx-div→ e Q dQ
  ...   | (x , t , refl , db) = pfx-div-cons e PQ x (⊓-div←r (P x) (Q x) db)

  input-dist : (Prefix e (λ x → P x ⊓ Q x)) ≈FD ((Prefix e P) ⊓ (Prefix e Q))
  input-dist = (dist-F⊥← , dist-D←) , (dist-F⊥→ , dist-D→)
