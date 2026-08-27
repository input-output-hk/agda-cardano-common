{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Classical descent for the FourNode-liveness endgame (campaign M0.5).
--
-- The M5 endgame transfers `⊨` of the classical response formula
-- `respondsAtoD` = `confined ⇒ G (p ⇒ F q)` (whose `⇒`/`G`/`F` are the
-- `¬`-encodings of Traces_Based §4.4) and then must DESCEND to the positive
-- `BlockLiveness⁺` shape `∀ n → ⟦ p ⟧ (drop n tr) → ◇ᵗ q (drop n tr)`.
-- Feeding the positive confinement hypothesis into that classical `⇒` yields
-- a `¬¬(G (p ⇒ F q))` fact; the existing certified postulates of Traces_Based
-- (`⟦G⟧⇒⟦G⟧⁺`, `¬G⇒F¬`) have the wrong polarity to eliminate it directly.
--
-- The descent is worked out end to end here.  ALMOST all of it is
-- constructive: `¬¬(G φ) → G φ` is triple-negation elimination (constructive,
-- because `G φ = ¬ (F ¬ φ)` is itself a negation), and the existing certified
-- `⟦G⟧⇒⟦G⟧⁺` then lands the pointwise `∀ n → ⟦ p ⇒ F q ⟧ (drop n tr)`.
-- Feeding `⟦ p ⟧` per index leaves exactly ONE irreducibly classical residue:
-- a `¬¬(F q)` on the POSITIVE `F`/`◇ᵗ` modality, which no constructive law can
-- discharge.  That single step — `⟦ ¬ ¬ (F φ) ⟧ tr → ⟦ F φ ⟧ tr` — is the ONE
-- new classical axiom this milestone budgets (postulated below, certified
-- derivable from a single `dne` in Semantics.LTL.ClassicalFromLEM; see the
-- audit convention comment there).  NB the minimal shape the descent forces is
-- `¬¬F`-elimination, NOT the `¬¬G`-elimination the design guessed — the `G`
-- layer descends constructively (recorded in the M0.5 report).
--
-- Generic (model-agnostic): parametric in E, I, R, and in the FOUR LTLᵗ
-- subformulas ψ₁ ψ₂ p q — no FourNode atom/link/`breakableSystem` content, so M5
-- instantiates `descent-⊨` directly at (breakableSystem, ¬ atom brkG1,
-- ¬ atom brkG2, atom (producedA b), atom (arrivedD b)).
------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)

open import Process_Trees using (PTree)

module Semantics.LTL.ClassicalDescent
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

-- The trace-based LTL layer: syntax, semantics, derived operators, §6.1
-- equivalences, and the existing certified `⟦G⟧⇒⟦G⟧⁺` we reuse.
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using ( Trace; LTLᵗ; ⟦_⟧; drop; _⊨_
        ; ¬_; _∨_; _⇒_; G_; F_
        ; □ᵗ; ◇ᵗ; ⟦G⟧⇒⟦G⟧⁺; F⇒◇ᵗ )

-- M0's bridge supplies the constructive packaging of the positive
-- confinement hypothesis `□ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr` into `⟦ (G ψ₁) ∨ (G ψ₂) ⟧ tr`.
open import Semantics.LTL.TraceBridge {ℓ} {ℓe} {ℓi} {E} {I}
  using ( □ᵗ-⊎⇒∨G )

------------------------------------------------------------
-- §1  The single classical axiom this milestone budgets.
--
-- Double-negation elimination for the "eventually" modality `F`.  This is the
-- one irreducibly classical step of the descent: `F φ = ⊤' U φ` is a positive
-- Σ-statement, so `¬¬(F φ) → F φ` cannot be proved constructively.  Certified
-- derivable from one `dne` (≡ LEM) in Semantics.LTL.ClassicalFromLEM — an
-- axiom in the audit sense, kept in the repo's established certified style.
------------------------------------------------------------

postulate
-- This can be derived from LEM; see ClassicalFromLEM.agda where this lemma is proved from a single dne
  ¬¬F⇒F : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
          → ⟦ ¬ ¬ (F_ φ) ⟧ tr → ⟦ F_ φ ⟧ tr

------------------------------------------------------------
-- §2  The constructive descent (built on M0's wrapper, §6.1 equivalences,
--     the existing certified `⟦G⟧⇒⟦G⟧⁺`, and the one `¬¬F⇒F` axiom).
------------------------------------------------------------

-- From `⟦ ((G ψ₁) ∨ (G ψ₂)) ⇒ G (p ⇒ F q) ⟧ tr` (the `respondsAtoD` shape)
-- and the positive confinement hypothesis `□ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr`, conclude the
-- positive per-suffix response `∀ n → ⟦ p ⟧ (drop n tr) → ◇ᵗ q (drop n tr)`.
descent : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
            {ψ₁ ψ₂ p q : LTLᵗ ℓa R} {tr : (Trace R) t}
          → ⟦ ((G_ ψ₁) ∨ (G_ ψ₂)) ⇒ (G_ (p ⇒ (F_ q))) ⟧ tr
          → (□ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr)
          → ∀ n → ⟦ p ⟧ (drop n tr) → ◇ᵗ q (drop n tr)
descent {ψ₁ = ψ₁} {ψ₂ = ψ₂} {p = p} {q = q} {tr = tr} H pos n hp =
  F⇒◇ᵗ {φ = q} (¬¬F⇒F {φ = q} nnFq)
  where
    -- M0's constructive packaging: the positive hypothesis ⇒ ⟦ confined ⟧.
    conf : ⟦ (G_ ψ₁) ∨ (G_ ψ₂) ⟧ tr
    conf = □ᵗ-⊎⇒∨G pos
    -- ⟦ ¬¬ confined ⟧ from ⟦ confined ⟧ (constructive double-negation intro).
    nnconf : ⟦ ¬ ¬ ((G_ ψ₁) ∨ (G_ ψ₂)) ⟧ tr
    nnconf = λ nc → nc conf
    -- Feed (¬¬confined, ·) to the classical `⇒`: get ⟦ ¬¬ G (p ⇒ F q) ⟧.
    nnG : ⟦ ¬ ¬ (G_ (p ⇒ (F_ q))) ⟧ tr
    nnG = λ ng → H (nnconf , ng)
    -- ⟦ ¬¬ G φ' ⟧ ⇒ ⟦ G φ' ⟧: triple-negation elimination (CONSTRUCTIVE,
    -- since G φ' = ¬ (F ¬ φ') is a negation) — no classical axiom needed.
    gG : ⟦ G_ (p ⇒ (F_ q)) ⟧ tr
    gG = λ y → nnG (λ k → k y)
    -- Pointwise form of G via the existing certified `⟦G⟧⇒⟦G⟧⁺`.
    g⁺ : ∀ m → ⟦ p ⇒ (F_ q) ⟧ (drop m tr)
    g⁺ = ⟦G⟧⇒⟦G⟧⁺ {φ = p ⇒ (F_ q)} gG
    -- ⟦ ¬¬ p ⟧ at index n from ⟦ p ⟧ (constructive double-negation intro).
    nnp : ⟦ ¬ ¬ p ⟧ (drop n tr)
    nnp = λ np → np hp
    -- Feed (¬¬p, ·) to the classical `⇒` at index n: get ⟦ ¬¬ (F q) ⟧ — the
    -- one residue the constructive layer cannot discharge, handed to `¬¬F⇒F`.
    nnFq : ⟦ ¬ ¬ (F_ q) ⟧ (drop n tr)
    nnFq = λ nfq → g⁺ n (nnp , nfq)

------------------------------------------------------------
-- §3  Corollary shaped for M5's exact seam.
--
-- Generic in the root `t` and the four subformulas; M5 instantiates at
-- (breakableSystem, ¬ atom brkG1, ¬ atom brkG2, atom (producedA b),
-- atom (arrivedD b)) — with `b` and `tr` bound outside — to obtain
-- `BlockLiveness⁺` verbatim.
------------------------------------------------------------

-- From `t ⊨ (respondsAtoD-shape)` derive the `BlockLiveness⁺`-shaped
-- per-trace positive response: run `⊨` on the trace, then descend.
descent-⊨ : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
              {ψ₁ ψ₂ p q : LTLᵗ ℓa R}
            → t ⊨ (((G_ ψ₁) ∨ (G_ ψ₂)) ⇒ (G_ (p ⇒ (F_ q))))
            → (tr : (Trace R) t) → (□ᵗ ψ₁ tr ⊎ □ᵗ ψ₂ tr)
            → ∀ n → ⟦ p ⟧ (drop n tr) → ◇ᵗ q (drop n tr)
descent-⊨ {ψ₁ = ψ₁} {ψ₂ = ψ₂} {p = p} {q = q} H tr pos =
  descent {ψ₁ = ψ₁} {ψ₂ = ψ₂} {p = p} {q = q} {tr = tr} (H tr) pos
