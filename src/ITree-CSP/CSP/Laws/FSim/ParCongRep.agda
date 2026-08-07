{-# OPTIONS --guardedness #-}

-- REPLICATED-INTERLEAVING failure-simulation congruences: `⦀Fin-fsim` / `⦀⋆-fsim`.
-- CONGRUENCES ONLY (`FSim → FSim`); the `⊑FD` folds live in `CSP.Laws.FD.ParallelMonoFD`
-- and are fact-shaped — see the closing note at the bottom of this module.
--
-- The FSim analogue of `CSP.Laws.Bisim.DRCongruenceRep.cong-⦀Fin` / `cong-⦀⋆`, and the
-- lemma a real compositional refinement needs: the refinement targets in this repo are
-- shaped `(⦀Fin n leaf) ∖ msgs` (see `NetworkLinkEquiv`, which discharges its entire
-- top-level result with one `cong-⦀Fin`), and walking that with FSim needs this fold
-- plus the already-available `Hide-fsim`.
--
-- CHEAPER THAN THE ≈DR VERSION: `Par-fsim` requires `Sep` on the IMPL operand pair
-- only, whereas `cong-⦀` needs three `Sep` witnesses (impl pair, mixed, spec pair).
-- So each fold step here discharges ONE separation obligation, not three, and only the
-- IMPL family needs an `OffersOnly` confinement hypothesis.
--
-- ⚠ `Sep` HERE IS `CSP.Laws.FSim.ParCong.Sep` (two-carrier, ParCong.agda:284), NOT
-- `CSP.Laws.Bisim.DRCongruence.Sep` (⊤-only, DRCongruence.agda:406).  They are
-- distinct records, so `DRCongruenceRep.sep-from-OffersOnly` — which produces the
-- latter — cannot be reused.  `sep-from-OffersOnlyᶠ` below re-proves the same
-- four-line corecursion against ParCong's record.  The `OffersOnly` layer itself IS
-- reused verbatim (`OffersOnly`, `OffersOnly-mono`, `OffersOnly-Skip`, `OffersOnly-⦀`,
-- `OffersOnly-⦀Fin`, `unionAlpha` all come straight from `DRCongruenceRep`).
--
-- POSTULATES: none local.  Inherited: `Par-Diverges→` (ParallelDivergence) via
-- `Par-fsim`.  This module does NOT import `Semantics.DRImpliesFD` (the purity rule for
-- `CSP/Laws/FSim/`); note that `ParCong` and `DRCongruenceRep` do reach it transitively
-- through their `CSP.Laws.FD.*` / interrupt dependencies, exactly as the pre-existing
-- `CSP.Laws.FSim.ParCong` and `CSP.Laws.FSim.HideCong` already do.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Process_Trees

module CSP.Laws.FSim.ParCongRep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl)
open import CSP.Laws.FSim.ParCong E-≟ using (Sep; Par-fsim; ⦀-fsim)
open import CSP.Laws.Bisim.DRCongruenceRep E-≟
  using ( Alpha; Disj; OffersOnly; OffersOnly-mono; OffersOnly-Skip
        ; OffersOnly-⦀; unionAlpha; OffersOnly-⦀Fin )

-- the result-carrier level, generalised over the `⦀⋆`/`FCell` definitions below (the
-- `⦀Fin` family binds its own `∀ {ℓr}` explicitly instead)
private
  variable
    ℓr : Level

-------------------------------------------------------------------------------------
-- The `Sep` discharge, re-proved against ParCong's two-carrier record
-------------------------------------------------------------------------------------

-- `sep-from-OffersOnly` re-proved against ParCong's two-carrier `Sep`: two
-- alphabet-confined processes whose non-sync alphabets clash on nothing can never
-- both-offer a non-sync event, now or ever.
sep-from-OffersOnlyᶠ : ∀ {ℓr} {α β : Alpha} (A : EventSet)
                       {P Q : PTree E (ExtI E) (⊤ {ℓr})}
                     → (∀ {at a} → ¬ A .mem at a → α at a → β at a → ⊥)
                     → OffersOnly α P → OffersOnly β Q → Sep A P Q
sep-from-OffersOnlyᶠ A disj ooP ooQ .Sep.now ¬cs Pst Qst =
  disj ¬cs (OffersOnly.now ooP Pst) (OffersOnly.now ooQ Qst)
sep-from-OffersOnlyᶠ A disj ooP ooQ .Sep.stepL Pst =
  sep-from-OffersOnlyᶠ A disj (OffersOnly.step ooP Pst) ooQ
sep-from-OffersOnlyᶠ A disj ooP ooQ .Sep.stepR Qst =
  sep-from-OffersOnlyᶠ A disj ooP (OffersOnly.step ooQ Qst)

-------------------------------------------------------------------------------------
-- The `⦀Fin` fold at FSim
-------------------------------------------------------------------------------------

-- `⦀Fin`-congruence at FSim: pairwise-disjoint per-index alphabets confining the IMPL
-- family, plus a pointwise FSim, give an FSim of the two folds.  By induction on `n`:
-- the `zero` fold is `Skip` (reflexivity); the `suc n` fold is closed by `⦀-fsim`,
-- whose single `Sep ∅ES` obligation comes from head-vs-tail-union disjointness.
--
-- NOTE only the IMPL family needs `OffersOnly` — `⦀-fsim` needs `Sep` on the impl
-- pair only.  `cong-⦀Fin` required confinement of BOTH families.
⦀Fin-fsim : ∀ {ℓr} {n} (αs : Fin n → Alpha)
            {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
          → (∀ i j → i ≢ j → Disj (αs i) (αs j))
          → (∀ i → OffersOnly (αs i) (f i))
          → (∀ i → FSim (⊤ {ℓr}) (f i) (g i))
          → FSim (⊤ {ℓr}) (⦀Fin n f) (⦀Fin n g)
⦀Fin-fsim {n = zero}  αs disj oof sim = fsim-refl Skip
⦀Fin-fsim {n = suc n} αs {f} {g} disj oof sim =
  ⦀-fsim (sep-from-OffersOnlyᶠ ∅ES hdDisj (oof fzero) tailF)
         (sim fzero)
         (⦀Fin-fsim (λ i → αs (fsuc i))
                    (λ i j i≢j → disj (fsuc i) (fsuc j) (λ e → i≢j (suc-injective e)))
                    (λ i → oof (fsuc i))
                    (λ i → sim (fsuc i)))
  where
  -- the impl tail fold confines to the tail-union alphabet
  tailF = OffersOnly-⦀Fin (λ i → oof (fsuc i))
  -- the head alphabet clashes with nothing in the tail union (pairwise disj + fzero ≢ fsuc j)
  hdDisj : ∀ {at a} → ¬ ∅ES .mem at a
         → αs fzero at a → unionAlpha (λ i → αs (fsuc i)) at a → ⊥
  hdDisj _ p (j , q) = disj fzero (fsuc j) (λ ()) _ _ p q

-------------------------------------------------------------------------------------
-- The `⦀⋆` (list-indexed) fold at FSim
-------------------------------------------------------------------------------------

-- a cell of the list-indexed FSim fold: an alphabet, an impl confined to it, a spec,
-- and a witness that the spec failure-simulates the impl.  The one-way analogue of
-- `DRCongruenceRep.CongCell`, whose `eq` field is `≈DR` (the wrong relation here) and
-- which carries a confinement for BOTH sides; only the impl side is confined here.
record FCell (ℓr : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  field
    alph : Alpha
    Impl : PTree E (ExtI E) (⊤ {ℓr})
    Spec : PTree E (ExtI E) (⊤ {ℓr})
    ooI  : OffersOnly alph Impl
    sim  : FSim (⊤ {ℓr}) Impl Spec

-- the pointwise union of a list of cell alphabets: membership in ANY cell's alphabet.
-- Defined by recursion (into `⊎`/`⊥`) rather than `Any` so the result stays in `Set₀`,
-- the codomain of `Alpha` (mirrors `DRCongruenceRep.unionAlphaL`).
unionAlphaF : List (FCell ℓr) → Alpha
unionAlphaF []       at a = ⊥
unionAlphaF (c ∷ cs) at a = FCell.alph c at a ⊎ unionAlphaF cs at a

-- a fold `⦀⋆ (map sel cs)` confines to the list-union of the cell alphabets, provided
-- each selected process is confined by its own cell alphabet (head injected via `inj₁`,
-- tail via `inj₂`).  The `FCell` analogue of `DRCongruenceRep.OffersOnly-⦀⋆-u`; used at
-- `sel = FCell.Impl`, the only side that needs confinement.
OffersOnly-⦀⋆-fu : (sel : FCell ℓr → PTree E (ExtI E) (⊤ {ℓr}))
                 → (∀ c → OffersOnly (FCell.alph c) (sel c))
                 → (cs : List (FCell ℓr))
                 → OffersOnly (unionAlphaF cs) (⦀⋆ (map sel cs))
OffersOnly-⦀⋆-fu sel hoo []       = OffersOnly-Skip
OffersOnly-⦀⋆-fu sel hoo (c ∷ cs) =
  OffersOnly-⦀ (OffersOnly-mono (λ _ _ p → inj₁ p) (hoo c))
               (OffersOnly-mono (λ _ _ p → inj₂ p) (OffersOnly-⦀⋆-fu sel hoo cs))

-- `⦀⋆`-congruence at FSim over a list of cells whose alphabets are pairwise disjoint
-- (`AllPairs`): by induction on the list, mirroring `⦀Fin-fsim`.  The `AllPairs` head
-- gives head-vs-each-tail-cell disjointness (an `All`), folded (via the local
-- `sepDisj`/`go`) into head-vs-tail-union, which discharges `⦀-fsim`'s SINGLE `Sep`
-- obligation (`cong-⦀⋆` needed three); the tail is the IH.
⦀⋆-fsim : (cs : List (FCell ℓr))
        → AllPairs (λ c c′ → Disj (FCell.alph c) (FCell.alph c′)) cs
        → FSim (⊤ {ℓr}) (⦀⋆ (map FCell.Impl cs)) (⦀⋆ (map FCell.Spec cs))
⦀⋆-fsim []       []ᵖ        = fsim-refl Skip
⦀⋆-fsim (c ∷ cs) (hd ∷ᵖ tl) =
  ⦀-fsim (sep-from-OffersOnlyᶠ ∅ES sepDisj (FCell.ooI c) tailI)
         (FCell.sim c)
         (⦀⋆-fsim cs tl)
  where
  -- the impl tail fold confines to the tail list-union alphabet
  tailI = OffersOnly-⦀⋆-fu FCell.Impl FCell.ooI cs
  -- the head alphabet clashes with nothing in the tail union: recurse over the
  -- head-vs-each-tail `All` and split the tail-union membership (`inj₁`/`inj₂`).
  sepDisj : ∀ {at a} → ¬ ∅ES .mem at a
          → FCell.alph c at a → unionAlphaF cs at a → ⊥
  sepDisj {at} {a} _ p q = go hd q
    where
    -- walk the head-vs-tail `All` in lockstep with the tail-union membership: `inj₁`
    -- picks out the matching cell (whose `Disj` head refutes `p`/`r` directly), `inj₂`
    -- recurses into the rest of the union.
    go : ∀ {cs′} → All (λ c′ → Disj (FCell.alph c) (FCell.alph c′)) cs′
       → unionAlphaF cs′ at a → ⊥
    go []       ()
    go (d ∷ ds) (inj₁ r) = d _ _ p r
    go (d ∷ ds) (inj₂ r) = go ds r

-------------------------------------------------------------------------------------
-- NO `⊑FD` COROLLARIES HERE — DELIBERATELY.  This module used to end with two
-- `FSim → ⊑FD` cash-out wrappers named `⦀Fin-mono-⊑FD` / `⦀⋆-mono-⊑FD`, each a
-- one-line `fsim→⊑FD (⦀…-fsim …)`.  They were RETIRED: those names now belong to the
-- FACT-SHAPED (`⊑FD → ⊑FD`) folds in `CSP.Laws.FD.ParallelMonoFD` (Layer 8), which are
-- true precongruences — they need NO `Disj` and NO `OffersOnly` (the disjointness here
-- exists only to discharge `Par-fsim`'s `Sep`, and `Par-mono-⊑FD` has no `Sep`), so
-- they are strictly more general as well as strictly more composable.  A caller that
-- genuinely holds `FSim` witnesses writes `fsim→⊑FD (⦀Fin-fsim αs disj oo sim)`
-- directly.  Please do not re-add a wrapper here; see `CSP.Laws.FD.IChoiceMonoFD`'s
-- header for the three-shape taxonomy and why shape-3 names are not worth minting.
-------------------------------------------------------------------------------------
