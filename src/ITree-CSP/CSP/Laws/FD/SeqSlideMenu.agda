{-# OPTIONS --guardedness #-}

-- seq-slide / ;-slide, MENU version (U13.8):
--   ((?x:A→P) ▷ P′) ; Q  ≈FD  (?x:A→(P;Q)) ▷ (P′ ; Q)
--
-- This is the MENU generalisation of `CSP.Laws.FD.SeqSlide.seq-slide-FD`: the
-- single-channel prefix `e ⟶ P` is replaced by the full prefix-CHOICE menu
-- `pchoice v` (an arbitrary offer map = a SET of events / multi-channel), exactly
-- as `SeqLaws.seq-step-menu-FD` generalises `SeqLaws.prefix-step-FD`.
--
-- In the spike `;` is `_>>_` (a constant-continuation bind), so the Roscoe
-- side-condition `x ∉ fv(Q)` is automatic.  The law holds as a STRONG bisim and
-- needs NO DecEq for the pointwise reasoning:
--   • VISIBLE: both nodes carry the menu offer; the bind pushes `; Q` under each
--     visible continuation `v at a`, which is exactly what the RHS already supplies
--     (`mapBind (λ _ → Q) v`).  Casing `v at a` (just/nothing) gives `refl` both.
--   • τ: the LHS slide-tag `fzero` timeout to `P′` gets `; Q`'d to `P′ ; Q`, matching
--     the RHS timeout to `P′ ; Q`; the operand-τ tag and all other ExtI indices give
--     `nothing` on both sides (the menu node has an empty τ-map ∅t).
-- The matched successors are LITERALLY the same trees (`t >> Q`, `P′ >> Q`), so each
-- is discharged by `sbisim-refl`.  Lifted to ≈FD via `drbisim→≈FD ∘ sbisim→drbisim`.

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.SeqSlideMenu {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
  using (_>>=_; _>>_; ∅t; bindV; bindT; pchoice; _▷_; ▷-slide)
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-react)
open import CSP.Laws.Traces.TraceLawsBind E-≟ using (fBind-react)
open import CSP.Laws.FD.SeqLaws E-≟ using (mapBind)
open import CSP.Laws.FD.SeqSlide E-≟ using (node-pw2)

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (P′ : PTree E (ExtI E) R) (Q : PTree E (ExtI E) S) where

  private
    K : R → PTree E (ExtI E) S
    K = λ _ → Q

    S₀ : PTree E (ExtI E) R
    S₀ = (pchoice v) ▷ P′

    -- force (pchoice v) ≡ react v ∅t   (definitional)
    force-pv : PTree.force (pchoice v) ≡ react v ∅t
    force-pv = refl

    -- force S₀ ≡ react v (▷-slide (react v ∅t) P′)
    nS : NodeKind E (ExtI E) R
    nS = react v (▷-slide (react v ∅t) P′)

    force-S₀ : PTree.force S₀ ≡ nS
    force-S₀ = force-▷-react {P = pchoice v} {Q = P′} force-pv

    -- LHS forces to a bind react node.
    force-LHS : PTree.force (S₀ >> Q) ≡ react (bindV K nS) (bindT K nS)
    force-LHS = fBind-react K S₀ force-S₀

    -- RHS forces to a slide react node over the pushed menu.
    force-RHS : PTree.force ((pchoice (mapBind K v)) ▷ (P′ >> Q))
              ≡ react (mapBind K v)
                      (▷-slide (react (mapBind K v) ∅t) (P′ >> Q))
    force-RHS = force-▷-react {P = pchoice (mapBind K v)} {Q = P′ >> Q} refl

    -- VISIBLE pointwise:  bindV K nS at a ≡ mapBind K v at a
    --   bindV K nS at a `with viewV nS at a = v at a`;
    --   mapBind K v at a = map (_>>= K) (v at a).  Both reduce by casing `v at a`.
    vis-pw : ∀ at a → bindV K nS at a ≡ mapBind K v at a
    vis-pw at a with v at a
    ... | just t  = refl
    ... | nothing = refl

    -- τ pointwise:  bindT K nS i a ≡ ▷-slide (react (mapBind K v) ∅t) (P′>>Q) i a
    --   timeout tag (pair fin, lift fzero): LHS `just (P′ >>= K) = just (P′ >> Q)`,
    --   RHS `just (P′ >> Q)`.  operand-τ tag (lift (fsuc fzero)): viewT of the menu
    --   node is ∅t = nothing, so `nothing` both sides.  All other indices: nothing.
    tau-pw : ∀ i a
           → bindT K nS i a
           ≡ ▷-slide (react (mapBind K v) ∅t) (P′ >> Q) i a
    tau-pw (_ , base _)            _ = refl
    tau-pw (_ , fin)               _ = refl
    tau-pw (_ , pair (base _) _)   _ = refl
    tau-pw (_ , pair (pair _ _) _) _ = refl
    tau-pw (_ , pair fin i) (lift fzero        , a) = refl
    tau-pw (_ , pair fin i) (lift (fsuc fzero) , a) = refl
    tau-pw (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

  seq-slide-menu-∼ : (S₀ >> Q) ∼ ((pchoice (mapBind K v)) ▷ (P′ >> Q))
  seq-slide-menu-∼ =
    node-pw2 (S₀ >> Q) ((pchoice (mapBind K v)) ▷ (P′ >> Q))
             (bindV K nS) (mapBind K v)
             (bindT K nS) (▷-slide (react (mapBind K v) ∅t) (P′ >> Q))
             force-LHS force-RHS vis-pw tau-pw

  seq-slide-menu-FD : (((pchoice v) ▷ P′) >> Q) ≈FD ((pchoice (mapBind K v)) ▷ (P′ >> Q))
  seq-slide-menu-FD = drbisim→≈FD (sbisim→drbisim seq-slide-menu-∼)
