{-# OPTIONS --guardedness #-}

-- ONE-WAY coinductive characterisation of failures-divergences refinement.
--
-- `FSim R t₁ t₂` reads "the SPECIFICATION t₂ failure-simulates the IMPLEMENTATION t₁",
-- following the orientation of `Semantics.WeakSim`'s `WSim` (every t₁ step is matched
-- by a weak t₂ step), so the headline theorem is `fsim→⊑FD : FSim R Q P → P ⊑FD Q`.
--
-- Compared with `Semantics.DRImpliesFD.drbisim→⊑FD`, which consumes all four `DRbisim`
-- fields, this needs only the FORWARD simulation, ONE divergence direction, and a
-- per-state stability condition.  The `bwd` / `div←` halves of a `DRbisim` are dead
-- weight for a refinement, and providing them forces the abstract side of a proof to
-- be reflected back through the whole operator stack.
--
-- The module is POSTULATE-FREE.  In particular it does NOT go through
-- `¬-divergent→normal` (the single classical postulate of `Semantics.DRImpliesFD`):
-- the `stab` field *produces* a stable specification witness rather than merely
-- asserting the specification converges, which is exactly what removes the need to
-- classically normalise.  As a consequence this module must not — and does not —
-- import `Semantics.DRImpliesFD` or anything supplying `dne`.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Process_Trees

module Semantics.FailureSim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS                 {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim           {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakSim             {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_)

-------------------------------------------------------------------------------------
-- The record.
-------------------------------------------------------------------------------------

-- t₂ (the spec) failure-simulates t₁ (the impl)
record FSim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
          : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd  : WSimF (FSim R) t₁ t₂

    -- whenever the impl is stable, the spec can silently settle into a stable
    -- state whose offers are contained in the impl's offers.  The inclusion runs
    -- spec-offers ⊆ impl-offers (NOT the reverse): to carry a refusal from the impl
    -- to the spec one must refute `Offers t₂′ e`, and semantically the spec is the
    -- more nondeterministic process, so once settled it offers no more than the impl.
    stab : isStable t₁
         → Σ[ t₂′ ∈ PTree E I R ]
             ( t₂ ─[τ*]─► t₂′
             × isStable t₂′
             × (∀ (e : Event√ R) → Offers t₂′ e → Offers t₁ e) )

    -- only the impl→spec divergence direction is needed; that is what ⊑D consumes
    div→ : Diverges t₁ → Diverges t₂
open FSim public

-------------------------------------------------------------------------------------
-- Big-step replay (the FSim analogue of `wsim-trace-sim` / `dr-trace-sim`).
-------------------------------------------------------------------------------------

-- a failure-simulated process's big-step trace is replayed move-by-move
fsim-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
               → FSim R P Q → P ⟹⟨ s ⟩ P′
               → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × FSim R P′ Q′)
fsim-trace-sim p≲q ⟹-refl = _ , ⟹-refl , p≲q
fsim-trace-sim p≲q (⟹-τ pτ rest)  with p≲q .FSim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≲q₁ with fsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-τ qτ q⟹ , p′≲q′
fsim-trace-sim p≲q (⟹-ev pev rest) with p≲q .FSim.fwd .WSimF.on-ev pev
... | _ , qev , p₁≲q₁ with fsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-ev qev q⟹ , p′≲q′

-------------------------------------------------------------------------------------
-- Forgetting the failure data leaves a plain weak simulation, hence trace refinement.
-------------------------------------------------------------------------------------

-- drop `stab` and `div→`: a failure simulation is in particular a weak simulation
fsim→wsim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → FSim R t₁ t₂ → WSim R t₁ t₂
fsim→wsim sim .WSim.fwd .WSimF.on-ev  s with sim .FSim.fwd .WSimF.on-ev  s
... | _ , w , rel = _ , w , fsim→wsim rel
fsim→wsim sim .WSim.fwd .WSimF.on-tau s with sim .FSim.fwd .WSimF.on-tau s
... | _ , w , rel = _ , w , fsim→wsim rel

-- trace refinement, via the weak simulation
fsim→⊑T : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑T Q
fsim→⊑T sim = wsim→⊑T (fsim→wsim sim)

-------------------------------------------------------------------------------------
-- The bridge to the FD model.  Unlike `drbisim→⊑F⊥` this uses no classical principle:
-- no `¬-divergent→normal`, no `stable-≉-ret` case, no `dr-absorb-τ*`, no `⊥-elim`.
-- The `ret` case simply cannot arise, because `stab` hands back a STABLE witness and
-- a `ret` state is never stable.  (If a spec must terminate where the impl stalls,
-- `stab` is unprovable — that is the correct outcome, not a gap.)
-------------------------------------------------------------------------------------

-- divergences are respected: replay the divergence prefix, then apply div→
fsim→⊑D : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑D Q
fsim→⊑D sim d with fsim-trace-sim sim (d .IsDivergence.reach)
... | Pw , p⟹ , simw = record
        { prefix  = d .IsDivergence.prefix
        ; suffix  = d .IsDivergence.suffix
        ; split   = d .IsDivergence.split
        ; witness = Pw
        ; reach   = p⟹
        ; divwit  = simw .FSim.div→ (d .IsDivergence.divwit)
        }

-- divergence-strict failures are respected: settle the spec with `stab` and compose
-- the offer inclusion with the impl's refusal
fsim→⊑F⊥ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑F⊥ Q
fsim→⊑F⊥ sim (inj₂ dQ) = inj₂ (fsim→⊑D sim dQ)
fsim→⊑F⊥ sim (inj₁ (Qw , q⟹ , stQw , norefuse))
  with fsim-trace-sim sim q⟹
... | Pw , p⟹ , simw with simw .FSim.stab stQw
...   | Pw′ , pw→pw′ , stPw′ , incl =
        inj₁ ( Pw′
             , ⟹-then-τ* p⟹ pw→pw′
             , stPw′
             , λ e Be off → norefuse e Be (incl e off) )

-- the headline theorem: a one-way failure simulation gives ⊑FD
fsim→⊑FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → FSim R Q P → P ⊑FD Q
fsim→⊑FD sim = fsim→⊑F⊥ sim , fsim→⊑D sim

-------------------------------------------------------------------------------------
-- FSim is a preorder.  Reflexivity is immediate; transitivity needs FSim-specific
-- weak-step lifting lemmas (`fsim-τ*-sim` / `fsim-wev-sim`) because `τ*-sim`,
-- `wev-sim` and `w-sim-trans` in `Semantics.WeakBisim` are hard-coded to `Wbisim`
-- (they project `.Wbisim.fwd`) and `Semantics.WeakSim` has no `wsim-trans` to borrow.
-------------------------------------------------------------------------------------

-- reflexivity: each step is matched by itself, and a stable state settles at itself
f-sim-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → WSimF (FSim R) t t
fsim-refl  : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → FSim R t t
f-sim-refl t .WSimF.on-ev  step = _ , wev τ*-refl step τ*-refl , fsim-refl _
f-sim-refl t .WSimF.on-tau step = _ , wτ (τ*-step step τ*-refl) , fsim-refl _
fsim-refl t .FSim.fwd      = f-sim-refl t
fsim-refl t .FSim.stab  st = t , τ*-refl , st , λ _ off → off
fsim-refl t .FSim.div→  d  = d

-- a τ* run of Q is matched by a τ* run of any S that failure-simulates Q
fsim-τ*-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R}
            → Q ─[τ*]─► Q′ → FSim R Q S
            → Σ[ S′ ∈ PTree E I R ] (S ─[τ*]─► S′ × FSim R Q′ S′)
fsim-τ*-sim τ*-refl           q≲s = _ , τ*-refl , q≲s
fsim-τ*-sim (τ*-step qτ rest) q≲s with q≲s .FSim.fwd .WSimF.on-tau qτ
... | _ , wτ s→s₁ , q₁≲s₁ with fsim-τ*-sim rest q₁≲s₁
...   | S′ , s₁→s′ , q′≲s′ = S′ , τ*-trans s→s₁ s₁→s′ , q′≲s′

-- a weak visible run of Q is matched by a weak visible run of S
fsim-wev-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R} {l : Event√ R}
             → Q ═[ ev l ]═► Q′ → FSim R Q S
             → Σ[ S′ ∈ PTree E I R ] (S ═[ ev l ]═► S′ × FSim R Q′ S′)
fsim-wev-sim (wev q→q₁ q₁ev q₂→q′) q≲s with fsim-τ*-sim q→q₁ q≲s
... | _ , s→s₁ , q₁≲s₁ with q₁≲s₁ .FSim.fwd .WSimF.on-ev q₁ev
...   | _ , wev s₁→m mev n→s₂ , q₂≲s₂ with fsim-τ*-sim q₂→q′ q₂≲s₂
...     | S′ , s₂→s′ , q′≲s′ =
          S′ , wev (τ*-trans s→s₁ s₁→m) mev (τ*-trans n→s₂ s₂→s′) , q′≲s′

-- composing a single-step simulation P→Q with a failure simulation Q≲S.  Stated as a
-- transformation on `WSimF`s (mirroring `w-sim-trans`) via forward declarations rather
-- than a mutual block, so the corecursive `fsim-trans` sits under the Σ-result of the
-- simulation and stays guarded.
f-sim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
            → WSimF (FSim R) P Q → FSim R Q S → WSimF (FSim R) P S
fsim-trans  : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ t₃ : PTree E I R}
            → FSim R t₁ t₂ → FSim R t₂ t₃ → FSim R t₁ t₃

f-sim-trans p→q q≲s .WSimF.on-ev pev with p→q .WSimF.on-ev pev
... | _ , q-weak , p′≲q′ with fsim-wev-sim q-weak q≲s
...   | S′ , s-weak , q′≲s′ = S′ , s-weak , fsim-trans p′≲q′ q′≲s′
f-sim-trans p→q q≲s .WSimF.on-tau pτ with p→q .WSimF.on-tau pτ
... | _ , wτ q→q′ , p′≲q′ with fsim-τ*-sim q→q′ q≲s
...   | S′ , s→s′ , q′≲s′ = S′ , wτ s→s′ , fsim-trans p′≲q′ q′≲s′

fsim-trans p≲q q≲s .FSim.fwd = f-sim-trans (p≲q .FSim.fwd) q≲s
-- settle t₂ with the first sim, push the second sim along that τ*-run, settle t₃ with
-- it, then compose the two τ*-runs and the two offer inclusions
fsim-trans p≲q q≲s .FSim.stab st₁ with p≲q .FSim.stab st₁
... | t₂′ , t₂→t₂′ , st₂′ , incl₂ with fsim-τ*-sim t₂→t₂′ q≲s
...   | t₃′ , t₃→t₃′ , q′≲s′ with q′≲s′ .FSim.stab st₂′
...     | t₃″ , t₃′→t₃″ , st₃″ , incl₃ =
          t₃″ , τ*-trans t₃→t₃′ t₃′→t₃″ , st₃″ , λ e off → incl₂ e (incl₃ e off)
fsim-trans p≲q q≲s .FSim.div→ d = q≲s .FSim.div→ (p≲q .FSim.div→ d)
