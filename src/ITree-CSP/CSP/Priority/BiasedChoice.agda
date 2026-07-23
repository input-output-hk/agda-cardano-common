{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- LEFT/RIGHT-BIASED external choice, DERIVED from the channel-level priority
-- operator `Priᶜ` (see `docs/specs/priority-implementation-plan.md`).
--
-- `P ⊲ Q` is external choice `P □ Q` under a priority order that makes a fixed
-- set of PREFERRED channels (the biased side's) dominate every other channel:
-- when the preferred side is concurrently offering, priority prunes the other
-- side's offers — but when the preferred side is silent/absent the other side is
-- kept (bias only suppresses a losing competitor, cf. Roscoe's `Pri`).
--
-- The two sides must offer DISTINGUISHABLE channels (decidable equality on
-- `AnyTypes E`, already required for `Priᶜ`); disjointness of the preferred set
-- from the other side's channels is what makes the pruning act only on the
-- non-preferred side.  This holds for the mux's distinct-protocol channels.
--
-- `--safe`, 0 postulates, nothing from `Classical`/`dne`.  Reuses `Priᶜ`,
-- `PriOrderC`, `finBr-□`, `_□_` — nothing here is modified.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Priority.BiasedChoice {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import Semantics.PriOrderC {ℓ} {ℓe} {E}
open import CSP.Priority.Base       {ℓ} {ℓe} {E} using (FinBr)
open import CSP.Priority.Channel E-≟
open import CSP.Priority.Closure E-≟ using (finBr-□)
open import CSP.Operators E-≟ using (_□_)
open import Data.List.Membership.DecPropositional E-≟ using (_∈?_)

------------------------------------------------------------------------
-- The bias order: preferred channels `Hchs` dominate all others.
------------------------------------------------------------------------

-- from a finite set `Hchs` of PREFERRED channels (each inhabited), build the
-- channel order where every non-preferred channel is dominated by every
-- preferred channel (preferred channels are ≤-maximal)
biasOrderᶜ : (Hchs : List (AnyTypes E))
           → (∀ {c} → c ∈ Hchs → proj₁ c)
           → PriOrderC (lsuc ℓ ⊔ ℓe)
biasOrderᶜ Hchs Hchs-inh = record
  { prop = record { _<ᶜ_ = _<b_ ; <ᶜ-irrefl = irr ; <ᶜ-trans = tr }
  ; aboveᶜ          = ab
  ; aboveᶜ-sound    = snd
  ; aboveᶜ-complete = cmp
  ; above-inhabited = inh
  }
  where
    -- a non-preferred `c` is dominated by a preferred `d`
    _<b_ : AnyTypes E → AnyTypes E → Set (lsuc ℓ ⊔ ℓe)
    c <b d = (¬ (c ∈ Hchs)) × (d ∈ Hchs)
    -- irreflexive: `c <b c` needs `c ∉ Hchs` and `c ∈ Hchs`
    irr : ∀ {c} → ¬ (c <b c)
    irr (c∉ , c∈) = c∉ c∈
    -- transitive: rebuild `c ∉ Hchs` (from first) and `e ∈ Hchs` (from second)
    tr : ∀ {c d e} → c <b d → d <b e → c <b e
    tr (c∉ , _) (_ , e∈) = c∉ , e∈
    -- dominators of `c`: all of `Hchs` if `c` non-preferred, else none
    ab : AnyTypes E → List (AnyTypes E)
    ab c = if ⌊ c ∈? Hchs ⌋ then [] else Hchs
    -- sound: a listed dominator `c′` is a preferred channel, `c` is not
    snd : ∀ {c c′} → c′ ∈ ab c → c <b c′
    snd {c} mem with c ∈? Hchs
    ... | yes _  = case mem of λ ()
    ... | no c∉  = c∉ , mem
    -- complete: `c <b c′` ⇒ `c` non-preferred ⇒ `ab c = Hchs ∋ c′`
    cmp : ∀ {c c′} → c <b c′ → c′ ∈ ab c
    cmp {c} (c∉ , c′∈) with c ∈? Hchs
    ... | yes c∈ = ⊥-elim (c∉ c∈)
    ... | no _   = c′∈
    -- every dominator is a preferred channel, hence inhabited via `Hchs-inh`
    inh : ∀ {c c′} → c′ ∈ ab c → proj₁ c′
    inh {c} mem with c ∈? Hchs
    ... | yes _ = case mem of λ ()
    ... | no _  = Hchs-inh mem

------------------------------------------------------------------------
-- The biased-choice operators.
------------------------------------------------------------------------

-- LEFT-biased: `P ⊲ Q` prefers `P` — its preferred channels `Pchs` (each
-- inhabited via `Pchs-inh`) prune `Q`'s offers when `P` concurrently competes
_⊲_ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {Pchs : List (AnyTypes E)} {Pchs-inh : ∀ {c} → c ∈ Pchs → proj₁ c}
      (P Q : PTree E (ExtI E) R) {fbP : FinBr P} {fbQ : FinBr Q}
    → PTree E (ExtI E) R
_⊲_ {Pchs = Pchs} {Pchs-inh = inh} P Q {fbP = fbP} {fbQ = fbQ}
  = Priᶜ (biasOrderᶜ Pchs inh) (P □ Q) (finBr-□ fbP fbQ)

-- RIGHT-biased: `P ⊳ Q` prefers `Q` — its preferred channels `Qchs` dominate,
-- pruning `P`'s offers when `Q` concurrently competes (operand order preserved)
_⊳_ : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {Qchs : List (AnyTypes E)} {Qchs-inh : ∀ {c} → c ∈ Qchs → proj₁ c}
      (P Q : PTree E (ExtI E) R) {fbP : FinBr P} {fbQ : FinBr Q}
    → PTree E (ExtI E) R
_⊳_ {Qchs = Qchs} {Qchs-inh = inh} P Q {fbP = fbP} {fbQ = fbQ}
  = Priᶜ (biasOrderᶜ Qchs inh) (P □ Q) (finBr-□ fbP fbQ)
