{-# OPTIONS --guardedness #-}

-------------------------------------------------------------------------------------
-- HOW THE FAILURES ORDERS RELATE TO THE TRACE ORDER `⊑T`.
--
-- Short answer: `⊑F` DOES imply `⊑T` — by construction, since `_⊑F_` is Roscoe's PAIR
-- (`⊑T × ⊇F`, `Semantics.Failures`) — but NEITHER of the bare failure-containment
-- relations `⊇F` NOR `⊇F⊥`/`⊑FD` does.  Those obligations are vacuous exactly where a
-- process fails to stabilise, and `traces` here is the RAW LTS trace set — it is NOT
-- closed under the "chaos after divergence" that `failures⊥`/`divergences` build in:
--
--   * `⊇F ⟹ ⊑T` fails because a divergent residual has NO failures at all:
--     `Stop ⊇F (a ⟶ div)` but `Stop` has no `⟨a⟩` trace.  This is exactly why `_⊑F_`
--     carries a trace component at all.
--   * `⊇F⊥ ⟹ ⊑T` (hence `⊑FD ⟹ ⊑T`) fails because `divergences P s` only witnesses a
--     run on a PREFIX of `s`: `div ⊑FD Q` for EVERY `Q`, yet `div`'s only trace is `[]`.
--
-- Both refutations are machine-checked in `CSP.Examples.RefinementOrderCounterexamples`.
-- What survives is the pair of DIVERGENCE-FREE repairs below; they say exactly which
-- extra hypothesis a bare failures fact needs before it constrains traces.
--
-- The only classical input is `¬-divergent→normal` (Semantics.DRImpliesFD), the
-- development's existing convergence⇒τ-normal-form postulate; NO new postulate, and no
-- LEM instance — divergence-freedom hands the non-divergence hypothesis over directly.
-------------------------------------------------------------------------------------

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees

module Semantics.RefinementOrders {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I}
  using (Event√; √; ev; _─[_]─►_; sRet)
open import Semantics.Refusals  {ℓ} {ℓe} {ℓi} {E} {I} using (Refuses; deadlock-refuses)
open import Semantics.Failures  {ℓ} {ℓe} {ℓi} {E} {I}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; ⟹-then-τ*; traces; failures; _⊑T_; _⊑F_; _⊇F_)
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I} using (Diverges)
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (IsDivergence; divergences; failures⊥; _⊇F⊥_; _⊇D_; _⊑FD_)
open import Semantics.DRImpliesFD {ℓ} {ℓe} {ℓi} {E} {I} using (¬-divergent→normal)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- Run plumbing.
-------------------------------------------------------------------------------------

-- a run over `s ++ t` contains a run over the prefix `s` (traces are prefix-closed)
⟹-take : {p q : PTree E I R} (s : List (Event√ R)) {t : List (Event√ R)}
        → p ⟹⟨ s ++ t ⟩ q → traces p s
⟹-take []      _                = _ , ⟹-refl
⟹-take (e ∷ s) (⟹-τ  st rest) = let (r , run) = ⟹-take (e ∷ s) rest in r , ⟹-τ  st run
⟹-take (e ∷ s) (⟹-ev st rest) = let (r , run) = ⟹-take s       rest in r , ⟹-ev st run

-- append a final visible step to a τ-abstracting run
⟹-snoc-ev : {p q q′ : PTree E I R} {s : List (Event√ R)} {e : Event√ R}
           → p ⟹⟨ s ⟩ q → q ─[ ev e ]─► q′ → p ⟹⟨ s ++ (e ∷ []) ⟩ q′
⟹-snoc-ev ⟹-refl          st = ⟹-ev st ⟹-refl
⟹-snoc-ev (⟹-τ  t rest)  st = ⟹-τ  t (⟹-snoc-ev rest st)
⟹-snoc-ev (⟹-ev t rest)  st = ⟹-ev t (⟹-snoc-ev rest st)

-- a run on `s` makes its endpoint's divergence a divergence of the whole trace `s`
run-div : {P Q : PTree E I R} {s : List (Event√ R)}
        → P ⟹⟨ s ⟩ Q → Diverges Q → divergences P s
run-div {s = s} run d = record
  { prefix = s ; suffix = [] ; split = sym (++-identityʳ s)
  ; witness = _ ; reach = run ; divwit = d }

-------------------------------------------------------------------------------------
-- The trivial refusal set, and the core "a convergent run carries a failure" lemma.
-------------------------------------------------------------------------------------

-- the refusal set that refuses NOTHING: every stable state refuses it, so it is the
-- cheapest `B` with which to turn a run into a failure
∅R : {R : Set ℓr} → Event√ R → Set ℓr
∅R {ℓr = ℓr} _ = Lift ℓr ⊥

-- …and it is refused by any stable state
∅R-refuses : {t : PTree E I R} → isStable t → Refuses t (∅R {R = R})
∅R-refuses st = st , λ _ → λ { (lift ()) }

-- CORE: a run whose endpoint cannot diverge reaches a τ-normal form, so it carries a
-- failure — on `s` itself (stable endpoint) or on `s ++ ⟨√ r⟩` (terminated endpoint,
-- whose √-step lands in `deadlock`, which refuses everything).
run→failure : {Q Q′ : PTree E I R} {s : List (Event√ R)}
            → Q ⟹⟨ s ⟩ Q′ → ¬ Diverges Q′
            → failures Q s ∅R ⊎ Σ[ r ∈ R ] failures Q (s ++ (√ r ∷ [])) ∅R
run→failure run ¬d with ¬-divergent→normal ¬d
... | Q″ , τrun , inj₁ st       = inj₁ (Q″ , ⟹-then-τ* run τrun , ∅R-refuses st)
... | Q″ , τrun , inj₂ (r , eq) =
        inj₂ (r , deadlock , ⟹-snoc-ev (⟹-then-τ* run τrun) (sRet eq) , deadlock-refuses)

-------------------------------------------------------------------------------------
-- The two divergence-free repairs.
-------------------------------------------------------------------------------------

-- DELIVERABLE 3: bare failure containment DOES constrain traces once the RIGHT-HAND
-- (implementation) process is divergence-free — the honest repair of the false
-- `⊇F ⟹ ⊑T`.  Stated at `_⊇F_`, not `_⊑F_`: at `_⊑F_` it is just `proj₁` and the
-- divergence-freedom premise is dead weight, so `⊇F` is where the content lives.
-- kept private: `_⊇F_` is the weaker half of `_⊑F_` and must not be reachable as
-- ordinary API (see `Semantics.Failures`).  Unlike the paired-result pattern used
-- elsewhere, this lemma's conclusion is `_⊑T_`, not `_⊑F_`, so there is no honest
-- `_⊑F_`-stated wrapper to requote it as: at `_⊑F_` the statement degenerates to
-- `proj₁` (see above), which would misrepresent this as new content.
private
  ⊇F→⊑T-df : {P Q : PTree E I R}
            → (∀ {s : List (Event√ R)} → ¬ divergences Q s)
            → P ⊇F Q → P ⊑T Q
  ⊇F→⊑T-df dfQ pf s (Q′ , run) with run→failure run (λ d → dfQ (run-div run d))
  ... | inj₁ f          = let (P′ , r , _) = pf s          ∅R f in P′ , r
  ... | inj₂ (_ , f)    = let (_  , r , _) = pf (s ++ _)   ∅R f in ⟹-take s r

-- DELIVERABLE 1 (repaired): `⊑FD` constrains traces once the LEFT-HAND (specification)
-- process is divergence-free.  `⊇D` then propagates that to `Q`, so no LEM instance is
-- needed; the `⊇D` component is what makes this work and is genuinely USED here.
⊑FD→⊑T-df : {P Q : PTree E I R}
          → (∀ {s : List (Event√ R)} → ¬ divergences P s)
          → P ⊑FD Q → P ⊑T Q
⊑FD→⊑T-df dfP (pfF , pfD) s (Q′ , run) with run→failure run (λ d → dfP (pfD (run-div run d)))
... | inj₁ f with pfF (inj₁ f)
...   | inj₁ (P′ , r , _) = P′ , r
...   | inj₂ dv           = ⊥-elim (dfP dv)
⊑FD→⊑T-df dfP (pfF , pfD) s (Q′ , run) | inj₂ (_ , f) with pfF (inj₁ f)
...   | inj₁ (_ , r , _)  = ⟹-take s r
...   | inj₂ dv           = ⊥-elim (dfP dv)

-------------------------------------------------------------------------------------
-- Refusal saturation: when a trace refinement already IS a stable-failures one.
-------------------------------------------------------------------------------------

-- a REFUSAL-SATURATED process can refuse ANY set at EVERY trace it has — the shape a
-- specification capped with `⊓ Stop` has, since the internal choice can always decide
-- to become the everything-refusing `Stop`
Saturated : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
Saturated {ℓr = ℓr} {R = R} P =
  ∀ {s : List (Event√ R)} → traces P s → ∀ {X : Event√ R → Set ℓr} → failures P s X

-- …and against such a spec trace refinement IS stable-failures refinement: a failure
-- of `Q` supplies a trace of `Q`, which `⊑T` moves to `P`, where saturation supplies
-- the refusal.  (The trace half of `_⊑F_` is the `⊑T` hypothesis itself.)
saturated→⊑T→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
                → Saturated P → P ⊑T Q → P ⊑F Q
saturated→⊑T→⊑F sat pt = pt , λ s X (Q′ , run , _) → sat (pt s (Q′ , run))
