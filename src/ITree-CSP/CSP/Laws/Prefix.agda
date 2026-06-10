{-
  Trace and failures/divergences laws for Prefix (_⟶_, _⟶₀_) and trigger.
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Data.List using (List; _++_; _∷_; []; [_])
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Bool using (Bool; true; false)
open import Class.DecEq using (DecEq)
open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences

module CSP.Laws.Prefix
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces
open Failures

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open import CSP.Laws.BasicProcesses {ℓ} {ℓe} {E} E-≟

-----------------------------------------------------------------------------
-- Trace lemmas
-- (from CSP.Laws.Traces, lines 239–351)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Prefix
-- traces [a → P] = {⟨⟩} ∪ {t : traces [P] • ⟨a⟩ ̂  t}

Prefix-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (ch : E A) (P : A → ITree E (ExtI I) R)
  {s : List (Event√ E R)}
  → traces (Prefix ch P) s
  → s ≡ [] ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
      (s ≡ evl (evLabel A ch a) ∷ s') × traces (P a) s')

Prefix-trace ch P (_ , bNil) = inj₁ refl
Prefix-trace {A = A} ch P (._ , bStep (sVis {at = at} {a = a} refl eq-j) big-step)
    with E-≟ (A , ch) at
-- Branch: The event doesn't match the prefix.
-- Prefix definition says result is 'nothing', but bStep says 'just t''.
... | no  _ = ⊥-elim (case eq-j of λ ())

-- Branch: The event matches!
... | yes refl =
    -- Now (A, ch) ≡ (A', ch'). Agda unifies A and ch'.
    -- eq-j now implies: just (P a) ≡ just t', so t' ≡ P a.
    let t'-is-P : _ ≡ P a
        t'-is-P = just-injective (sym eq-j)
    in inj₂ (a , _ , refl , (_ , subst (λ t → t ═⟨ _ ⟩═► _) t'-is-P big-step))

Prefix-trace ch P (_ , bTau (sSil ()) _)
Prefix-trace ch P (_ , bStep (sRet ()) _)

-- For simplified prefix, the response is ignored but it is stilled recorded in traces
Prefix₀-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (ch : E A) (Px : ITree E (ExtI I) R)
  {s : List (Event√ E R)}
  → traces (Prefix₀ ch Px) s
  → s ≡ [] ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
      (s ≡ evl (evLabel A ch a) ∷ s') × traces Px s')
Prefix₀-trace ch Px = Prefix-trace ch (λ _ → Px)

------------------------------------------------------------------------
-- Introduction direction for `Prefix-trace`.  Lift a trace of the
-- continuation `P a` into a trace of `Prefix ch P` prefixed with the
-- corresponding `evl (evLabel A ch a)` event.
------------------------------------------------------------------------
Prefix-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (P : A → ITree E (ExtI I) R) (a : A)
    {s : List (Event√ E R)}
  → traces (P a) s
  → traces (Prefix ch P) (evl (evLabel A ch a) ∷ s)
Prefix-trace-intro ch P a (T , bs) =
  T , bStep (sVis {at = _ , ch} {a = a} refl (Prefix-cont-just ch P a)) bs

------------------------------------------------------------------------
-- Specialisation for the discarded-payload variant `_⟶₀_`.
------------------------------------------------------------------------
Prefix₀-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (Px : ITree E (ExtI I) R) (a : A)
    {s : List (Event√ E R)}
  → traces Px s
  → traces (Prefix₀ ch Px) (evl (evLabel A ch a) ∷ s)
Prefix₀-trace-intro ch Px a = Prefix-trace-intro ch (λ _ → Px) a

------------------------------------------------------------------------
-- Monotonicity of Prefix under _⊑ᵀ_.  Monotone in the continuation.
------------------------------------------------------------------------
⟶-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
              (ch : E A) {P P′ : A → ITree E (ExtI I) R}
            → (∀ a → P a ⊑ᵀ P′ a)
            → (Prefix ch P) ⊑ᵀ (Prefix ch P′)
⟶-mono-⊑ᵀ ch {P} {P′} P⊑P′ {s = s} tr-rhs
  with Prefix-trace ch P′ tr-rhs
... | inj₁ s≡[] = subst (λ s′ → traces (Prefix ch P) s′) (sym s≡[]) (_ , bNil)
... | inj₂ (a , s′ , eq-s , tr-cont)
    = subst (λ s′ → traces _ s′) (sym eq-s)
            (Prefix-trace-intro ch P a (P⊑P′ a tr-cont))

⟶₀-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
               (ch : E A) {Px Px′ : ITree E (ExtI I) R}
             → Px ⊑ᵀ Px′
             → (Prefix₀ ch Px) ⊑ᵀ (Prefix₀ ch Px′)
⟶₀-mono-⊑ᵀ ch Px⊑Px′ = ⟶-mono-⊑ᵀ ch (λ _ → Px⊑Px′)

-----------------------------------------------------------------------------------------
-- trigger

trigger-trace : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
  (e : E A) {s : List (Event√ E A)}
  → traces (trigger {ℓi = ℓi} {I = I} e) s
  → s ≡ []
  ⊎ (∃ λ (a : A) → s ≡ evl (evLabel A e a) ∷ [])
  ⊎ (∃ λ (a : A) → s ≡ evl (evLabel A e a) ∷ √ a ∷ [])

trigger-trace e (_ , bNil) = inj₁ refl
trigger-trace e (._ , bStep {el = el} (sVis {at = at} {a = a} refl eq-j) big-step)
  with E-≟ (_ , e) at
... | no _ = ⊥-elim (case eq-j of λ ())
... | yes refl =
    let
      -- The next state is Ret a
      t'-is-Ret : _ ≡ Ret a
      t'-is-Ret = just-injective (sym eq-j)

      -- Get the trace of the remainder from our Ret-trace lemma
      ret-tr : traces (Ret a) _
      ret-tr = _ , subst (λ t → t ═⟨ _ ⟩═► _) t'-is-Ret big-step
    in
    case Ret-trace ret-tr of λ where
      (inj₁ s'≡[]) →
        inj₂ (inj₁ (a , cong (λ x → evl (evLabel _ e a) ∷ x) s'≡[]))
      (inj₂ s'≡√)  →
        inj₂ (inj₂ (a , cong (λ x → evl (evLabel _ e a) ∷ x) s'≡√))

trigger-trace e (_ , bTau (sSil ()) _)

-----------------------------------------------------------------------------
-- FD lemmas
-- (from CSP.Laws.FailuresDivergences, lines 262–521)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Prefix  ch ⟶ P
-- `force (Prefix ch P) = vis cont`, so:
--   • Prefix ch P is stable;
--   • it makes no τ-step and no `√`-step;
--   • the only ev-steps are `evl (evLabel A ch a)` to `P a`.
-- Failures decompose as `[]`-with-residual-refusal, or an ev-step into `P a`.
-- Divergences decompose as an ev-step into a divergence of `P a` (Prefix
-- itself does not diverge since it is stable).

Prefix-isStable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                  {ch : E A} {P : A → ITree E (ExtI I) R}
                → isStable (Prefix {I = I} ch P)
Prefix-isStable = tt₀

Prefix-no-τ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
              {ch : E A} {P : A → ITree E (ExtI I) R}
              {Q : ITree E (ExtI I) R}
            → Prefix ch P ─[ τ ]─► Q → ⊥
Prefix-no-τ tr = τ-from-force-vis-impossible refl tr

Prefix-no-√ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
              {ch : E A} {P : A → ITree E (ExtI I) R}
              {x : R} {Q : ITree E (ExtI I) R}
            → Prefix ch P ─[ ev (√ x) ]─► Q → ⊥
Prefix-no-√ (sRet eq) = case eq of λ ()

¬-Divergent-Prefix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                     {ch : E A} {P : A → ITree E (ExtI I) R}
                   → ¬ Divergent (Prefix ch P)
¬-Divergent-Prefix d = Prefix-no-τ (Divergent.step d)

-- The single ev-step `Prefix ch P` admits.  Uses `Prefix-cont-just`
-- from `CSP.Definitions.Operators` to feed `sVis`'s second equation.
Prefix-step : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
              (ch : E A) (P : A → ITree E (ExtI I) R) (a : A)
            → Prefix ch P ─[ ev (evl (evLabel A ch a)) ]─► P a
Prefix-step {A = A} ch P a =
  sVis {at = A , ch} {a = a} refl (Prefix-cont-just ch P a)

-- Refusal sets of `Prefix ch P` exclude every `evl (evLabel A ch a)`.  This
-- is the concrete refusal characterisation: instead of the opaque
-- `Prefix ch P ref B`, we expose that no `ch`-labelled event is in `B`.
Prefix-ref-no-ch :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    {ch : E A} {P : A → ITree E (ExtI I) R}
    {B : Event√ E R → Set ℓB}
  → Prefix ch P ref B
  → ∀ (a : A) → ¬ B (evl (evLabel A ch a))
Prefix-ref-no-ch (ref-tick step _) _ _ = Prefix-no-√ step
Prefix-ref-no-ch {A = A} {ch = ch} {P = P} (ref-stable _ noev) a Bch =
  noev (evl (evLabel A ch a)) Bch (Prefix-step ch P a)

-- Converse: if `B` excludes every `ch`-labelled event, then `B` is a
-- refusal of `Prefix ch P`.  Other events (`√` and non-`ch` visibles) are
-- ruled out by inversion: `Prefix` makes no `√`-step, and only `ch` is an
-- enabled visible event.
ref-Prefix :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    {ch : E A} {P : A → ITree E (ExtI I) R}
    {B : Event√ E R → Set ℓB}
  → (∀ (a : A) → ¬ B (evl (evLabel A ch a)))
  → Prefix ch P ref B
ref-Prefix {A = A} {ch = ch} {P = P} {B = B} no-ch =
  ref-stable {P = Prefix ch P} (Prefix-isStable {ch = ch} {P = P}) noev
  where
    noev : ∀ e → B e → ∀ {Q : ITree E (ExtI _) _} → ¬ (Prefix ch P ─[ ev e ]─► Q)
    noev (√ _) _ step = Prefix-no-√ step
    noev (evl (evLabel A' e' a')) Be
         (sVis {at = at} {a = a'} refl eq-j)
         with E-≟ (A , ch) at
    ... | yes refl = no-ch a' Be
    ... | no _     with eq-j
    ...               | ()

-- Decomposition of a weak bigstep out of `Prefix ch P`: either zero events
-- (witness still `Prefix ch P`) or a single ev-step into `P a` followed by
-- the residual bigstep on `P a`.  Mirrors `Prefix-trace` but tracks the
-- target witness, which we need for both failures and divergences.
Prefix-bigstep-decomp :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (P : A → ITree E (ExtI I) R)
    {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
  → Prefix ch P ═⟨ s ⟩═► Q
  → (s ≡ [] × Q ≡ Prefix ch P)
  ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
        s ≡ evl (evLabel A ch a) ∷ s' × (P a ═⟨ s' ⟩═► Q))
Prefix-bigstep-decomp ch P bNil = inj₁ (refl , refl)
Prefix-bigstep-decomp ch P (bTau τ-step _) = ⊥-elim (Prefix-no-τ τ-step)
Prefix-bigstep-decomp ch P (bStep {el = √ _} step _) = ⊥-elim (Prefix-no-√ step)
Prefix-bigstep-decomp {A = A} ch P
    (bStep {el = evl (evLabel _ _ _)}
           (sVis {at = at} {a = a} refl eq-j) rest)
    with E-≟ (A , ch) at
... | no _     = ⊥-elim (case eq-j of λ ())
... | yes refl =
    let t'≡Pa = just-injective (sym eq-j)
    in inj₂ (a , _ , refl , subst (λ T → T ═⟨ _ ⟩═► _) t'≡Pa rest)

-- Failure-trace decomposition for Prefix.  The empty case exposes the
-- concrete refusal characterisation `∀ a → ¬ B (evl (evLabel A ch a))`,
-- not the opaque `Prefix ch P ref B`.  The non-empty case exposes a
-- residual failure of `P a`.
Prefix-failures-trace :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (P : A → ITree E (ExtI I) R)
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → failures (Prefix ch P) s B
  → (s ≡ [] × (∀ (a : A) → ¬ B (evl (evLabel A ch a))))
  ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
        s ≡ evl (evLabel A ch a) ∷ s' × failures (P a) s' B)
Prefix-failures-trace ch P (Q , reach , refusal)
    with Prefix-bigstep-decomp ch P reach
... | inj₁ (s≡[] , refl) = inj₁ (s≡[] , Prefix-ref-no-ch refusal)
... | inj₂ (a , s' , s≡∷ , reach') =
      inj₂ (a , s' , s≡∷ , (Q , reach' , refusal))

-- Divergence-trace decomposition for Prefix.  The empty-prefix case is
-- impossible since `Prefix ch P` is stable.
Prefix-divergences-trace :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (P : A → ITree E (ExtI I) R)
    {s : List (Event√ E R)}
  → divergences (Prefix ch P) s
  → ∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
        s ≡ evl (evLabel A ch a) ∷ s' × divergences (P a) s'
Prefix-divergences-trace ch P
    record { prefix = pre ; suffix = suf ; split = sp
           ; witness = w ; reach = reach ; divwit = dw }
    with Prefix-bigstep-decomp ch P reach
... | inj₁ (refl , refl) = ⊥-elim (¬-Divergent-Prefix dw)
... | inj₂ (a , s'pre , pre≡∷ , reach') =
      a , (s'pre ++ suf) ,
        trans sp (cong (_++ suf) pre≡∷) ,
        record { prefix = s'pre ; suffix = suf ; split = refl
               ; witness = w ; reach = reach' ; divwit = dw }

-- Prefix₀ is `Prefix ch (λ _ → Px)`; the lemmas above instantiate directly.
Prefix₀-failures-trace :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (Px : ITree E (ExtI I) R)
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → failures (Prefix₀ ch Px) s B
  → (s ≡ [] × (∀ (a : A) → ¬ B (evl (evLabel A ch a))))
  ⊎ (∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
        s ≡ evl (evLabel A ch a) ∷ s' × failures Px s' B)
Prefix₀-failures-trace ch Px = Prefix-failures-trace ch (λ _ → Px)

Prefix₀-divergences-trace :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (ch : E A) (Px : ITree E (ExtI I) R)
    {s : List (Event√ E R)}
  → divergences (Prefix₀ ch Px) s
  → ∃ λ (a : A) → ∃ λ (s' : List (Event√ E R)) →
        s ≡ evl (evLabel A ch a) ∷ s' × divergences Px s'
Prefix₀-divergences-trace ch Px = Prefix-divergences-trace ch (λ _ → Px)

------------------------------------------------------------------------
-- Monotonicity of Prefix under _⊑F⊥_, _⊑D_, _⊑FD_.
-- Monotone in the continuation.
------------------------------------------------------------------------

-- Helper: lift a failure of P a into a failure of Prefix ch P.
private
  Prefix-failures-intro :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {ch : E A} {P : A → ITree E (ExtI I) R}
      (a : A) {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → failures (P a) s B
    → failures (Prefix ch P) (evl (evLabel A ch a) ∷ s) B
  Prefix-failures-intro {ch = ch} {P = P} a (Q , reach , refusal) =
    Q , bStep (Prefix-step ch P a) reach , refusal

  -- Lift a divergence of P a into a divergence of Prefix ch P.
  Prefix-divergences-intro :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {ch : E A} {P : A → ITree E (ExtI I) R}
      (a : A) {s : List (Event√ E R)}
    → divergences (P a) s
    → divergences (Prefix ch P) (evl (evLabel A ch a) ∷ s)
  Prefix-divergences-intro {ch = ch} {P = P} a d =
    record { prefix  = evl (evLabel _ ch a) ∷ d .IsDivergence.prefix
           ; suffix  = d .IsDivergence.suffix
           ; split   = cong (evl (evLabel _ ch a) ∷_) (d .IsDivergence.split)
           ; witness = d .IsDivergence.witness
           ; reach   = bStep (Prefix-step ch P a) (d .IsDivergence.reach)
           ; divwit  = d .IsDivergence.divwit
           }

-- Helper: lift failures⊥ of P a into failures⊥ of Prefix ch P (with prepended event).
private
  Prefix-failures⊥-intro :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {ch : E A} {P : A → ITree E (ExtI I) R}
      (a : A) {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → failures⊥ (P a) s B
    → failures⊥ (Prefix ch P) (evl (evLabel A ch a) ∷ s) B
  Prefix-failures⊥-intro a (inj₁ fl) = inj₁ (Prefix-failures-intro a fl)
  Prefix-failures⊥-intro a (inj₂ dv) = inj₂ (Prefix-divergences-intro a dv)

⟶-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
               ⦃ _ : DecEq R ⦄
               (ch : E A) {P P′ : A → ITree E (ExtI I) R}
             → (∀ a → _⊑F⊥_ {ℓB = ℓB} (P a) (P′ a))
             → _⊑F⊥_ {ℓB = ℓB} (Prefix ch P) (Prefix ch P′)
⟶-mono-⊑F⊥ ch {P} {P′} P⊑P′ {s = s} {B = B} (inj₁ fl)
  with Prefix-failures-trace ch P′ fl
... | inj₁ (s≡[] , no-ch) =
      inj₁ (subst (λ s′ → failures (Prefix ch P) s′ B) (sym s≡[])
                  (Prefix ch P , bNil , ref-Prefix no-ch))
... | inj₂ (a , s′ , s≡∷ , fl-Pa′) =
      subst (λ s′′ → failures⊥ (Prefix ch P) s′′ B) (sym s≡∷)
            (Prefix-failures⊥-intro a (P⊑P′ a (inj₁ fl-Pa′)))
⟶-mono-⊑F⊥ ch {P} {P′} P⊑P′ {s = s} {B = B} (inj₂ dv)
  with Prefix-divergences-trace ch P′ dv
... | a , s′ , s≡∷ , dv-Pa′ =
      subst (λ s′′ → failures⊥ (Prefix ch P) s′′ B) (sym s≡∷)
            (Prefix-failures⊥-intro a (P⊑P′ a (inj₂ dv-Pa′)))

⟶-mono-⊑D : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
              ⦃ _ : DecEq R ⦄
              (ch : E A) {P P′ : A → ITree E (ExtI I) R}
            → (∀ a → P a ⊑D P′ a)
            → (Prefix ch P) ⊑D (Prefix ch P′)
⟶-mono-⊑D ch {P} {P′} P⊑P′ {s = s} dv
  with Prefix-divergences-trace ch P′ dv
... | a , s′ , s≡∷ , dv-Pa′ =
      subst (λ s′′ → divergences (Prefix ch P) s′′) (sym s≡∷)
            (Prefix-divergences-intro a (P⊑P′ a dv-Pa′))

⟶-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
               ⦃ _ : DecEq R ⦄
               (ch : E A) {P P′ : A → ITree E (ExtI I) R}
             → (∀ a → _⊑FD_ {ℓB = ℓB} (P a) (P′ a))
             → _⊑FD_ {ℓB = ℓB} (Prefix ch P) (Prefix ch P′)
⟶-mono-⊑FD ch P⊑P′ =
    ⟶-mono-⊑F⊥ ch (λ a → proj₁ (P⊑P′ a))
  , ⟶-mono-⊑D  ch (λ a → proj₂ (P⊑P′ a))

⟶₀-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                ⦃ _ : DecEq R ⦄
                (ch : E A) {Px Px′ : ITree E (ExtI I) R}
              → _⊑F⊥_ {ℓB = ℓB} Px Px′
              → _⊑F⊥_ {ℓB = ℓB} (Prefix₀ ch Px) (Prefix₀ ch Px′)
⟶₀-mono-⊑F⊥ ch Px⊑Px′ = ⟶-mono-⊑F⊥ ch (λ _ → Px⊑Px′)

⟶₀-mono-⊑D : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
               ⦃ _ : DecEq R ⦄
               (ch : E A) {Px Px′ : ITree E (ExtI I) R}
             → Px ⊑D Px′
             → (Prefix₀ ch Px) ⊑D (Prefix₀ ch Px′)
⟶₀-mono-⊑D ch Px⊑Px′ = ⟶-mono-⊑D ch (λ _ → Px⊑Px′)

⟶₀-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                ⦃ _ : DecEq R ⦄
                (ch : E A) {Px Px′ : ITree E (ExtI I) R}
              → _⊑FD_ {ℓB = ℓB} Px Px′
              → _⊑FD_ {ℓB = ℓB} (Prefix₀ ch Px) (Prefix₀ ch Px′)
⟶₀-mono-⊑FD ch Px⊑Px′ = ⟶-mono-⊑FD ch (λ _ → Px⊑Px′)
