{-# OPTIONS --guardedness #-}

-- SPIKE: the failures-divergences (FD) model on the pure-react LTS, mirroring
-- PTree_Relations.FailuresDivergences.  Extracts traces / failures / divergences and
-- defines the divergence-strict refinement ⊑FD and FD-equivalence ≈FD.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary using (IsEquivalence; Setoid; Preorder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees

module Semantics.FailuresDivergences {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I}
  using (Event√; Label; _─[_]─►_; sRet; sSil; sVis; sTau)
open import Semantics.Failures {ℓ} {ℓe} {ℓi} {E} {I}    using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.Refusals {ℓ} {ℓe} {ℓi} {E} {I}    using (Refuses; Offers)
open import Semantics.DRBisim  {ℓ} {ℓe} {ℓi} {E} {I}    using (Diverges; div-diverges)
import Semantics.Stability     {ℓ} {ℓe} {ℓi} {E} {I} as St

-------------------------------------------------------------------------------------
-- Divergences (divergence-strict): s ∈ div(P) iff some prefix of s weakly reaches a
-- divergent state.
-------------------------------------------------------------------------------------

record IsDivergence {ℓr} {R : Set ℓr}
                    (P : PTree E I R) (s : List (Event√ R))
                  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  field
    prefix  : List (Event√ R)
    suffix  : List (Event√ R)
    split   : s ≡ prefix ++ suffix
    witness : PTree E I R
    reach   : P ⟹⟨ prefix ⟩ witness
    divwit  : Diverges witness

divergences : ∀ {ℓr} {R : Set ℓr} → PTree E I R → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
divergences P s = IsDivergence P s

-- divergences are extension-closed: s ∈ div(P) ⇒ s ++ t ∈ div(P)
div-extension-closed : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} {s t : List (Event√ R)}
                     → IsDivergence P s → IsDivergence P (s ++ t)
div-extension-closed {t = t} d = record
  { prefix  = d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix ++ t
  ; split   = trans (cong (_++ t) (d .IsDivergence.split))
                    (++-assoc (d .IsDivergence.prefix) (d .IsDivergence.suffix) t)
  ; witness = d .IsDivergence.witness
  ; reach   = d .IsDivergence.reach
  ; divwit  = d .IsDivergence.divwit
  }

-- every divergence prefix is a trace
div-prefix-is-trace : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} {s : List (Event√ R)}
                    → (d : IsDivergence P s) → traces P (d .IsDivergence.prefix)
div-prefix-is-trace d = d .IsDivergence.witness , d .IsDivergence.reach

-- a diverging process has the empty trace as a divergence
empty-div : ∀ {ℓr} {R : Set ℓr} {P : PTree E I R} → Diverges P → IsDivergence P []
empty-div {P = P} dP = record
  { prefix = [] ; suffix = [] ; split = refl ; witness = P ; reach = ⟹-refl ; divwit = dP }

-------------------------------------------------------------------------------------
-- The FD model: divergence-strict failures and refinement orders.
-------------------------------------------------------------------------------------

-- after a divergence every refusal is a failure ("chaos after divergence")
failures⊥ : ∀ {ℓr} {R : Set ℓr}
          → PTree E I R → List (Event√ R) → (Event√ R → Set ℓr)
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
failures⊥ P s B = failures P s B ⊎ divergences P s

_⊑F⊥_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
_⊑F⊥_ {ℓr = ℓr} {R = R} P Q =
  ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ Q s B → failures⊥ P s B

_⊑D_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_⊑D_ P Q = ∀ {s} → divergences Q s → divergences P s

_⊑FD_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
P ⊑FD Q = (P ⊑F⊥ Q) × (P ⊑D Q)

-- FD-equivalence: mutual refinement
_≈FD_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
P ≈FD Q = (P ⊑FD Q) × (Q ⊑FD P)

-------------------------------------------------------------------------------------
-- ⊑FD is a preorder, ≈FD an equivalence (all by subset reasoning)
-------------------------------------------------------------------------------------

⊑FD-refl : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑FD P
⊑FD-refl P = (λ f → f) , (λ d → d)

⊑FD-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑FD Q → Q ⊑FD S → P ⊑FD S
⊑FD-trans (pqF , pqD) (qsF , qsD) = (λ f → pqF (qsF f)) , (λ d → pqD (qsD d))

-------------------------------------------------------------------------------------
-- FORCE-EQUAL TREES ARE ⊑FD-INTERCHANGEABLE.
--
-- `PTree` is a COINDUCTIVE record, so it has no η: `Skip >> P` and `P` are distinct
-- terms with equal `force`.  But every LTS rule reads its source ONLY through `force`,
-- so the whole FD theory is force-invariant.  That is proved once here, generically in
-- `E`/`I`; `force-≡→⊑FD` is the bridge the CSP-layer laws use to cross the missing η.
-- The same law at the weaker/stronger orders: `⊑T` in
-- `CSP.Laws.Traces.TraceLawsGuard.force-≡→traces-⊆`, `∼` in
-- `CSP.Laws.FD.SeqLaws.sbisim-force-eq`.
-------------------------------------------------------------------------------------

-- a step reads its source only through `force`, so an equal force admits the same step
step-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q t : PTree E I R} {l : Label R}
             → force p ≡ force q → q ─[ l ]─► t → p ─[ l ]─► t
step-force-≡ eq (sRet ef)    = sRet (trans eq ef)
step-force-≡ eq (sSil ef)    = sSil (trans eq ef)
step-force-≡ eq (sVis ef ej) = sVis (trans eq ef) ej
step-force-≡ eq (sTau ef ej) = sTau (trans eq ef) ej

-- only a divergence's FIRST τ-step reads the root, so an equal force re-roots it
Diverges-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R}
                 → force p ≡ force q → Diverges q → Diverges p
Diverges-force-≡ eq d .Diverges.next = d .Diverges.next
Diverges-force-≡ eq d .Diverges.step = step-force-≡ eq (d .Diverges.step)
Diverges-force-≡ eq d .Diverges.rest = d .Diverges.rest

-- `Refuses` reads its tree only through `force` (stability is a `force` predicate and
-- every `Offers` witness is a step out of the root)
Refuses-force-≡ : ∀ {ℓr ℓx} {R : Set ℓr} {p q : PTree E I R} {B : Event√ R → Set ℓx}
                → force p ≡ force q → Refuses q B → Refuses p B
Refuses-force-≡ {p = p} {q = q} eq (st , noff) =
  St.stable-force-eq {p = p} {q = q} eq st
  , λ e Be (t′ , step) → noff e Be (t′ , step-force-≡ (sym eq) step)

-- …hence so does a failure: a non-trivial run transports its first step to the new root,
-- and a 0-step run reflects the endpoint's refusal back through the equal force
failures-force-≡ : ∀ {ℓr ℓx} {R : Set ℓr} {p q : PTree E I R}
                   {s : List (Event√ R)} {B : Event√ R → Set ℓx}
                 → force p ≡ force q → failures q s B → failures p s B
failures-force-≡ {p = p} eq (_ , ⟹-refl , ref) = p , ⟹-refl , Refuses-force-≡ eq ref
failures-force-≡ eq (w , ⟹-τ  step rest , ref) = w , ⟹-τ  (step-force-≡ eq step) rest , ref
failures-force-≡ eq (w , ⟹-ev step rest , ref) = w , ⟹-ev (step-force-≡ eq step) rest , ref

-- cross a force-equal boundary for a DIVERGENCE-BEARING run: a non-trivial run transports
-- its first step to the new root; a 0-step run re-roots the `Diverges` witness itself
cross-div-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q w : PTree E I R} {s : List (Event√ R)}
                  → force p ≡ force q → q ⟹⟨ s ⟩ w → Diverges w
                  → Σ[ w′ ∈ PTree E I R ] ((p ⟹⟨ s ⟩ w′) × Diverges w′)
cross-div-force-≡ {p = p} eq ⟹-refl           dw = p , ⟹-refl , Diverges-force-≡ eq dw
cross-div-force-≡ eq (⟹-τ  step rest) dw = _ , ⟹-τ  (step-force-≡ eq step) rest , dw
cross-div-force-≡ eq (⟹-ev step rest) dw = _ , ⟹-ev (step-force-≡ eq step) rest , dw

-- …and so does a divergence: re-root the reach, keep prefix / suffix / split untouched
div-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R} {s : List (Event√ R)}
            → force p ≡ force q → divergences q s → divergences p s
div-force-≡ eq d
  with cross-div-force-≡ eq (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | w′ , reach′ , dw′ = record
  { prefix  = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split   = d .IsDivergence.split  ; witness = w′
  ; reach   = reach′                 ; divwit  = dw′ }

-- a divergence-strict failure is force-invariant (either disjunct)
failures⊥-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R}
                  → force p ≡ force q → p ⊑F⊥ q
failures⊥-force-≡ eq (inj₁ f) = inj₁ (failures-force-≡ eq f)
failures⊥-force-≡ eq (inj₂ d) = inj₂ (div-force-≡ eq d)

-- FORCE-EQUAL TREES REFINE EACH OTHER IN THE FD MODEL.  Used to cross the missing
-- coinductive η, e.g. `Skip >> P` vs `P`.
force-≡→⊑FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → force P ≡ force Q → P ⊑FD Q
force-≡→⊑FD eq = failures⊥-force-≡ eq , div-force-≡ eq

≈FD-refl : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ≈FD P
≈FD-refl P = ⊑FD-refl P , ⊑FD-refl P

≈FD-sym : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → P ≈FD Q → Q ≈FD P
≈FD-sym (pq , qp) = qp , pq

≈FD-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ≈FD Q → Q ≈FD S → P ≈FD S
≈FD-trans (pq , qp) (qs , sq) = ⊑FD-trans pq qs , ⊑FD-trans sq qp

-------------------------------------------------------------------------------------
-- Demonstrator: div is "chaos after []" — divergent at the empty trace, hence refuses
-- everything there in the FD model (this is what distinguishes div from deadlock).
-------------------------------------------------------------------------------------

div-divergence : ∀ {ℓr} {R : Set ℓr} → divergences (div {E = E} {I = I} {R = R}) []
div-divergence = empty-div div-diverges

div-chaos : ∀ {ℓr} {R : Set ℓr} {B : Event√ R → Set ℓr}
          → failures⊥ (div {E = E} {I = I} {R = R}) [] B
div-chaos = inj₂ div-divergence

-- failures-divergences equivalence is an equivalence relation:
≈FD-isEquivalence : ∀ {ℓr} {R : Set ℓr} → IsEquivalence (_≈FD_ {R = R})
≈FD-isEquivalence = record
  { refl  = λ {x} → ≈FD-refl x
  ; sym   = ≈FD-sym
  ; trans = ≈FD-trans
  }

≈FD-setoid : ∀ {ℓr} (R : Set ℓr) → Setoid _ _
≈FD-setoid R = record
  { Carrier       = PTree E I R
  ; _≈_           = _≈FD_
  ; isEquivalence = ≈FD-isEquivalence
  }

⊑FD-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑FD-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≈FD_
  ; _≲_        = _⊑FD_
  ; isPreorder = record
      { isEquivalence = ≈FD-isEquivalence
      ; reflexive     = proj₁
      ; trans         = ⊑FD-trans
      }
  }
