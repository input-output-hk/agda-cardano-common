{-# OPTIONS --guardedness #-}

-- Divergence-respecting weak EXPANSION preorder `_⪰_` on the react LTS.
--
-- `t₁ ⪰ t₂` reads "t₁ is at least as fast as t₂" / "t₂ expands t₁".
-- It is the standard expansion preorder (Arun-Kumar/Hennessy/Sangiorgi)
-- adapted to this LTS, refined to be divergence-respecting so that it
-- soundly refines `≈DR`:
--
--   * fwd  : t₁'s moves are matched by t₂ as a WEAK simulation (t₂ may be
--            slower, padding with τ*).  Reuses `WSimF (Expand R)`.
--   * bwd  : t₂'s moves are matched by t₁ in AT MOST ONE step — a single
--            strong visible step for a visible move, and a single-or-zero
--            τ-step for a τ-move (the expansion asymmetry: t₁ never needs to
--            pad).  This is the `ExpBwdF` record below.
--   * div→ / div← : divergence is preserved in both directions, exactly the
--            two conditions `≈DR` demands.  Stated explicitly (as in DRbisim)
--            so that BOTH `⪰→≈DR` and `⪰-trans` go through without having to
--            reconstruct a divergence witness from the near-strong matching.
--
-- The deliverable is `⪰→≈DR : t₁ ⪰ t₂ → t₁ ≈DR t₂`: fwd of ≈DR = fwd of ⪰
-- (already a weak sim); bwd of ≈DR is obtained by WEAKENING ⪰'s near-strong
-- bwd (a single/zero step IS a weak step); div→/div← are taken verbatim.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary using (Rel)

open import Process_Trees

module Semantics.Expansion {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}

-------------------------------------------------------------------------------------
-- The near-strong "backward" half of expansion.
--
-- `ExpBwdF R TreeRel t₁ t₂` says: every move of t₂ is matched by t₁ in AT MOST
-- ONE step.
--   * a visible move of t₂ is matched by a SINGLE strong visible step of t₁;
--   * a τ-move of t₂ is matched by EITHER a single strong τ-step of t₁ (`inj₁`)
--     OR by t₁ STUTTERING (zero steps, `inj₂`), in which case t₁ is unchanged
--     and only t₂ advanced.
-- This is the expansion asymmetry: t₁ (the faster process) replies promptly.
-------------------------------------------------------------------------------------

record ExpBwdF {ℓr ℓ≈} {R : Set ℓr}
               (TreeRel : Rel (PTree E I R) ℓ≈)
               (t₁ t₂ : PTree E I R)
             : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓ≈) where
  field
    bon-ev  : ∀ {l : Event√ R} {t₂′}
            → t₂ ─[ ev l ]─► t₂′
            → Σ[ t₁′ ∈ PTree E I R ] (t₁ ─[ ev l ]─► t₁′ × TreeRel t₁′ t₂′)
    bon-tau : ∀ {t₂′}
            → t₂ ─[ τ ]─► t₂′
            → (Σ[ t₁′ ∈ PTree E I R ] (t₁ ─[ τ ]─► t₁′ × TreeRel t₁′ t₂′))
            ⊎ (TreeRel t₁ t₂′)

-------------------------------------------------------------------------------------
-- Expansion.
-------------------------------------------------------------------------------------

record Expand {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
            : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd  : WSimF  (Expand R) t₁ t₂      -- t₁'s moves matched weakly by t₂
    bwd  : ExpBwdF (Expand R) t₁ t₂      -- t₂'s moves matched by t₁ in ≤ 1 step
    div→ : Diverges t₁ → Diverges t₂
    div← : Diverges t₂ → Diverges t₁

_⪰_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_⪰_ {R = R} = Expand R

-------------------------------------------------------------------------------------
-- 1. Reflexivity.
-------------------------------------------------------------------------------------

⪰-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → t ⪰ t
⪰-refl t .Expand.fwd .WSimF.on-ev  step = _ , wev τ*-refl step τ*-refl , ⪰-refl _
⪰-refl t .Expand.fwd .WSimF.on-tau step = _ , wτ (τ*-step step τ*-refl) , ⪰-refl _
⪰-refl t .Expand.bwd .ExpBwdF.bon-ev  step = _ , step , ⪰-refl _
⪰-refl t .Expand.bwd .ExpBwdF.bon-tau step = inj₁ (_ , step , ⪰-refl _)
⪰-refl t .Expand.div→ d = d
⪰-refl t .Expand.div← d = d

-------------------------------------------------------------------------------------
-- 2. Transitivity.
--
-- The forward half is exactly the weak-bisim transitivity technique (a single step
-- of P is matched by a weak step of Q, which a weak run of S must follow).  We reuse
-- the same weak-step lifting, specialised to `Expand` (`exp-τ*-sim`, `exp-wev-sim`).
--
-- The backward half is much more direct because both bwd's are near-strong: a single
-- step of S is matched by a single (or zero) step of Q, which in turn is matched by a
-- single (or zero) step of P.  No τ*-padding is ever introduced on the P side, so the
-- composite stays near-strong — the defining feature that makes expansion compose.
-------------------------------------------------------------------------------------

-- a τ* run of Q matched by a τ* run of S, threading an Expand Q S forward (fwd half)
exp-τ*-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R}
           → Q ─[τ*]─► Q′ → Expand R Q S
           → Σ[ S′ ∈ PTree E I R ] (S ─[τ*]─► S′ × Expand R Q′ S′)
exp-τ*-sim τ*-refl           e = _ , τ*-refl , e
exp-τ*-sim (τ*-step qτ rest) e with e .Expand.fwd .WSimF.on-tau qτ
... | _ , wτ s→s₁ , e₁ with exp-τ*-sim rest e₁
...   | S′ , s₁→s′ , e′ = S′ , τ*-trans s→s₁ s₁→s′ , e′

-- a weak visible run of Q matched by a weak visible run of S (fwd half)
exp-wev-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R} {l : Event√ R}
            → Q ═[ ev l ]═► Q′ → Expand R Q S
            → Σ[ S′ ∈ PTree E I R ] (S ═[ ev l ]═► S′ × Expand R Q′ S′)
exp-wev-sim (wev q→q₁ q₁ev q₂→q′) e with exp-τ*-sim q→q₁ e
... | _ , s→s₁ , e₁ with e₁ .Expand.fwd .WSimF.on-ev q₁ev
...   | _ , wev s₁→m mev n→s₂ , e₂ with exp-τ*-sim q₂→q′ e₂
...     | S′ , s₂→s′ , e′ =
          S′ , wev (τ*-trans s→s₁ s₁→m) mev (τ*-trans n→s₂ s₂→s′) , e′

-- forward composition, as a transformation of WSimF (mirrors dr-sim-trans)
exp-fwd-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
              → WSimF (Expand R) P Q → Expand R Q S → WSimF (Expand R) P S
⪰-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
        → Expand R P Q → Expand R Q S → Expand R P S

-- backward composition, as a transformation of ExpBwdF.  Reads the moves of S,
-- routes them through the bwd of Q≈S then the bwd of P≈Q; corecursion sits guarded
-- under the Σ/⊎ results.  Takes the FULL `Expand R P Q` (not just its bwd) because
-- the stutter case (Q matches a τ of S by ZERO steps) leaves P,Q unchanged and must
-- recurse with the same `Expand R P Q` witness.
exp-bwd-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
              → Expand R P Q → Expand R Q S → ExpBwdF (Expand R) P S

exp-fwd-trans p→q e .WSimF.on-ev pev with p→q .WSimF.on-ev pev
... | _ , q-weak , e-pq with exp-wev-sim q-weak e
...   | S′ , s-weak , e-qs = S′ , s-weak , ⪰-trans e-pq e-qs
exp-fwd-trans p→q e .WSimF.on-tau pτ with p→q .WSimF.on-tau pτ
... | _ , wτ q→q′ , e-pq with exp-τ*-sim q→q′ e
...   | S′ , s→s′ , e-qs = S′ , wτ s→s′ , ⪰-trans e-pq e-qs

-- For S's moves: get them matched ≤1-step by Q (via e .bwd), then ≤1-step by P.
exp-bwd-trans e-pq e-qs .ExpBwdF.bon-ev sev
  with e-qs .Expand.bwd .ExpBwdF.bon-ev sev
... | _ , qev , e-pq′ with e-pq .Expand.bwd .ExpBwdF.bon-ev qev
...   | _ , pev , e-pq″ = _ , pev , ⪰-trans e-pq″ e-pq′
exp-bwd-trans e-pq e-qs .ExpBwdF.bon-tau sτ
  with e-qs .Expand.bwd .ExpBwdF.bon-tau sτ
-- Q makes a single τ to q′; route it through P's bwd
... | inj₁ (_ , qτ , e-q′s′) with e-pq .Expand.bwd .ExpBwdF.bon-tau qτ
...   | inj₁ (_ , pτ , e-p′q′) = inj₁ (_ , pτ , ⪰-trans e-p′q′ e-q′s′)
...   | inj₂ e-pq′             = inj₂ (⪰-trans e-pq′ e-q′s′)
-- Q stutters (zero steps): P stays put too, only S advanced — recurse with same P≈Q
exp-bwd-trans e-pq e-qs .ExpBwdF.bon-tau sτ
    | inj₂ e-qs′ = inj₂ (⪰-trans e-pq e-qs′)

⪰-trans p≈q q≈s .Expand.fwd  = exp-fwd-trans (p≈q .Expand.fwd) q≈s
⪰-trans p≈q q≈s .Expand.bwd  = exp-bwd-trans p≈q q≈s
⪰-trans p≈q q≈s .Expand.div→ d = q≈s .Expand.div→ (p≈q .Expand.div→ d)
⪰-trans p≈q q≈s .Expand.div← d = p≈q .Expand.div← (q≈s .Expand.div← d)

-------------------------------------------------------------------------------------
-- 3. ⪰ ⊆ ≈DR.
-------------------------------------------------------------------------------------

-- We build `⪰→≈DR` together with the orientation-swapped `⪯→≈DR : Expand R t₁ t₂ →
-- DRbisim R t₂ t₁`, so the bwd residuals never need the (non-guarded) `drbisim-sym`.
⪰→≈DR : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → t₁ ⪰ t₂ → t₁ ≈DR t₂
⪯→≈DR : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → t₁ ⪰ t₂ → t₂ ≈DR t₁

-- Weakening of ⪰'s near-strong bwd into a weak simulation `WSimF (DRbisim R) t₂ t₁`:
-- a single strong visible step is a weak step (wev, empty τ*); a single-or-zero τ-step
-- is a weak τ-step (one `τ*-step`, or `τ*-refl` on stutter).
exp-bwd→wsim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
             → Expand R t₁ t₂ → WSimF (DRbisim R) t₂ t₁
exp-bwd→wsim e .WSimF.on-ev s with e .Expand.bwd .ExpBwdF.bon-ev s
... | _ , p , e′ = _ , wev τ*-refl p τ*-refl , ⪯→≈DR e′
exp-bwd→wsim e .WSimF.on-tau s with e .Expand.bwd .ExpBwdF.bon-tau s
... | inj₁ (_ , p , e′) = _ , wτ (τ*-step p τ*-refl) , ⪯→≈DR e′
... | inj₂ e′           = _ , wτ τ*-refl , ⪯→≈DR e′

-- ⪰'s fwd (a weak sim) coerced to carry `DRbisim` residuals.
exp-fwd→wsim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
             → Expand R t₁ t₂ → WSimF (DRbisim R) t₁ t₂
exp-fwd→wsim e .WSimF.on-ev s with e .Expand.fwd .WSimF.on-ev s
... | _ , w , e′ = _ , w , ⪰→≈DR e′
exp-fwd→wsim e .WSimF.on-tau s with e .Expand.fwd .WSimF.on-tau s
... | _ , w , e′ = _ , w , ⪰→≈DR e′

⪰→≈DR e .DRbisim.fwd  = exp-fwd→wsim e
⪰→≈DR e .DRbisim.bwd  = exp-bwd→wsim e
⪰→≈DR e .DRbisim.div→ = e .Expand.div→
⪰→≈DR e .DRbisim.div← = e .Expand.div←

⪯→≈DR e .DRbisim.fwd  = exp-bwd→wsim e
⪯→≈DR e .DRbisim.bwd  = exp-fwd→wsim e
⪯→≈DR e .DRbisim.div→ = e .Expand.div←
⪯→≈DR e .DRbisim.div← = e .Expand.div→
