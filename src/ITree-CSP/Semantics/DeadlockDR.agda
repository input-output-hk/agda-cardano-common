{-# OPTIONS --guardedness #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import Process_Trees

module Semantics.DeadlockDR {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Deadlock  {ℓ} {ℓe} {ℓi} {E} {I}
-- `DivergenceFree` MOVED to `Semantics.DivergenceFree` (the divergence-freedom
-- calculus); re-exported here so existing importers of this module still see it.
-- The `≈DR` transfer `drbisim-divergenceFree` below stays here because it needs
-- `drbisim-trace-sim`, which lives in this module.
open import Semantics.DivergenceFree {ℓ} {ℓe} {ℓi} {E} {I}
  using (DivergenceFree) public

-- Positive deadlock-freedom over √-free reachability: every √-free-reachable state
-- has at least one enabled LTS label (visible event, τ, or √).
Progress : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Progress {R = R} t =
  ∀ {s : List Event} {t′ : PTree E I R}
  → t ⟹∖√⟨ s ⟩ t′ → Σ[ l ∈ Label R ] Σ[ t″ ∈ PTree E I R ] (t′ ─[ l ]─► t″)

-- A reachable state with an enabled move cannot be stuck.
progress⇒deadlockFree : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                      → Progress t → DeadlockFree t
progress⇒deadlockFree prog reach stuck =
  let (l , t″ , step) = prog reach in stuck step

-- Append a trailing τ-step to a √-free run.
∖√-snoc-τ : ∀ {ℓr} {R : Set ℓr} {p q q′ : PTree E I R} {s : List Event}
          → p ⟹∖√⟨ s ⟩ q → q ─[ τ ]─► q′ → p ⟹∖√⟨ s ⟩ q′
∖√-snoc-τ ∖√-refl        st = ∖√-τ st ∖√-refl
∖√-snoc-τ (∖√-τ  x rest) st = ∖√-τ x (∖√-snoc-τ rest st)
∖√-snoc-τ (∖√-ev x rest) st = ∖√-ev x (∖√-snoc-τ rest st)

-- Fold a τ* prefix into a √-free run.
τ*→∖√ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s : List Event}
      → p ─[τ*]─► q → q ⟹∖√⟨ s ⟩ r → p ⟹∖√⟨ s ⟩ r
τ*→∖√ τ*-refl           tr = tr
τ*→∖√ (τ*-step st rest) tr = ∖√-τ st (τ*→∖√ rest tr)

-- Weaken a √-free run by a weak τ.
weaken∖√-τ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s : List Event}
           → p ═[ τ ]═► q → q ⟹∖√⟨ s ⟩ r → p ⟹∖√⟨ s ⟩ r
weaken∖√-τ (wτ τs) tr = τ*→∖√ τs tr

-- Weaken a √-free run by a weak visible (evl) event.
weaken∖√-ev : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s : List Event} {e : Event}
            → p ═[ ev (evl e) ]═► q → q ⟹∖√⟨ s ⟩ r → p ⟹∖√⟨ e ∷ s ⟩ r
weaken∖√-ev (wev pre evs post) tr = τ*→∖√ pre (∖√-ev evs (τ*→∖√ post tr))

-- DR-bisimulation simulates a whole √-free run.
drbisim-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s : List Event}
                  → DRbisim R P Q → P ⟹∖√⟨ s ⟩ P′
                  → Σ[ Q′ ∈ PTree E I R ] (Q ⟹∖√⟨ s ⟩ Q′ × DRbisim R P′ Q′)
drbisim-trace-sim p≈q ∖√-refl = _ , ∖√-refl , p≈q
drbisim-trace-sim p≈q (∖√-τ pτ rest)  with p≈q .DRbisim.fwd .WSimF.on-tau pτ
... | _ , q-weak , p′≈q′ with drbisim-trace-sim p′≈q′ rest
...   | Q′ , q⟹ , p′≈Q′ = Q′ , weaken∖√-τ q-weak q⟹ , p′≈Q′
drbisim-trace-sim p≈q (∖√-ev pev rest) with p≈q .DRbisim.fwd .WSimF.on-ev pev
... | _ , q-weak , p′≈q′ with drbisim-trace-sim p′≈q′ rest
...   | Q′ , q⟹ , p′≈Q′ = Q′ , weaken∖√-ev q-weak q⟹ , p′≈Q′

-- Helper: if `t₁′` is stuck and `u ─[τ]─► u′` is simulated backwards into `t₁′`,
-- then the simulation must stay at `t₁′` (τ*-refl), giving `DRbisim u′ t₁′`.
matchτ-stuck : ∀ {ℓr} {R : Set ℓr} {u u′ t₁′ : PTree E I R}
             → IsStuck t₁′
             → WSimF (DRbisim R) u t₁′
             → u ─[ τ ]─► u′
             → DRbisim R u′ t₁′
matchτ-stuck stuck bwd uτ with bwd .WSimF.on-tau uτ
... | _ , wτ τ*-refl , u′≈t₁′ = u′≈t₁′
... | _ , wτ (τ*-step st _) , _ = ⊥-elim (stuck st)

-- Helper: if `t₁′` is stuck, then no visible/√ move of `u` can be simulated backwards.
refute-vis : ∀ {ℓr} {R : Set ℓr} {u u′ t₁′ : PTree E I R} {l : Event√ R}
           → IsStuck t₁′
           → WSimF (DRbisim R) u t₁′
           → u ─[ ev l ]─► u′
           → ⊥
refute-vis stuck bwd uev with bwd .WSimF.on-ev uev
... | _ , wev τ*-refl st _ , _ = stuck st
... | _ , wev (τ*-step st _) _ _ , _ = stuck st

-- Extract the unique τ step out of a progress witness when the target is stuck.
-- (A visible/√ step is impossible — refute-vis discharges it via stuck.)
bad-step : ∀ {ℓr} {R : Set ℓr} {t₂ t₁′ u : PTree E I R} {s : List Event}
         → Progress t₂ → IsStuck t₁′ → DRbisim R t₁′ u → t₂ ⟹∖√⟨ s ⟩ u
         → Σ[ u′ ∈ PTree E I R ] (u ─[ τ ]─► u′)
bad-step prog stuck rel reach with prog reach
... | τ      , u′ , uτ = u′ , uτ
... | ev l   , u′ , uev = ⊥-elim (refute-vis stuck (rel .DRbisim.bwd) uev)

-- From a stuck `t₁′` DR-related to a *progressing* `u`, build an infinite τ-run of
-- `u`: `Progress` hands a concrete move of `u`; a visible/√ move would force the
-- stuck `t₁′` to move (via `bwd`) — impossible; so the move is τ, the `Diverges`
-- step, and we recurse on the successor (still DR-related to the still-stuck `t₁′`).
bad : ∀ {ℓr} {R : Set ℓr} {t₂ t₁′ u : PTree E I R} {s : List Event}
    → Progress t₂ → IsStuck t₁′ → DRbisim R t₁′ u → t₂ ⟹∖√⟨ s ⟩ u
    → Diverges u
bad prog stuck rel reach .Diverges.next = proj₁ (bad-step prog stuck rel reach)
bad prog stuck rel reach .Diverges.step = proj₂ (bad-step prog stuck rel reach)
bad prog stuck rel reach .Diverges.rest =
  let u′ , uτ = bad-step prog stuck rel reach
  in bad prog stuck (drbisim-sym (matchτ-stuck stuck (rel .DRbisim.bwd) uτ)) (∖√-snoc-τ reach uτ)

-- Transfer: deadlock-freedom of `t₂` (as `Progress`) carries to any `t₁ ≈DR t₂`.
drbisim-deadlockFree : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                     → t₁ ≈DR t₂ → Progress t₂ → DeadlockFree t₁
drbisim-deadlockFree t₁≈t₂ prog reach₁ stuck
  with drbisim-trace-sim t₁≈t₂ reach₁
... | t₂′ , reach₂ , t₁′≈t₂′ =
      let divt₂′ = bad prog stuck t₁′≈t₂′ reach₂
          divt₁′ = t₁′≈t₂′ .DRbisim.div← divt₂′
      in stuck (divt₁′ .Diverges.step)

-- Coinductive liveness: some move exists (any label, incl √), and every τ / visible
-- (evl) successor is again live.  (Same shape as the refinement layer's `GoodU`.)
record Live {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    move   : Σ[ l ∈ Label R ] Σ[ t″ ∈ PTree E I R ] (t ─[ l ]─► t″)
    stepτ  : ∀ {t″}             → t ─[ τ ]─► t″             → Live t″
    stepev : ∀ {e : Event} {t″} → t ─[ ev (evl e) ]─► t″   → Live t″
open Live

-- Liveness implies Progress over √-free reachability.
Live⇒Progress : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → Live t → Progress t
Live⇒Progress live ∖√-refl        = live .move
Live⇒Progress live (∖√-τ  st rest) = Live⇒Progress (live .stepτ  st) rest
Live⇒Progress live (∖√-ev st rest) = Live⇒Progress (live .stepev st) rest

-- ≈DR transfers divergence-freedom: a √-free-reachable state of t₁ maps (by
-- trace-sim) to one of t₂, and `div→` carries any divergence of it across.
drbisim-divergenceFree : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                       → t₁ ≈DR t₂ → DivergenceFree t₂ → DivergenceFree t₁
drbisim-divergenceFree t₁≈t₂ dft₂ reach₁ div₁ with drbisim-trace-sim t₁≈t₂ reach₁
... | t₂′ , reach₂ , t₁′≈t₂′ = dft₂ reach₂ (t₁′≈t₂′ .DRbisim.div→ div₁)
