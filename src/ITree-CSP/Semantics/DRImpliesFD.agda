{-# OPTIONS --guardedness #-}

-- The bridge ≈DR ⟹ ≈FD : divergence-respecting weak bisimulation implies
-- failures-divergences equivalence on the pure-react LTS.
--
-- The DIVERGENCES half is fully constructive (it just transports a divergence
-- along the weak simulation, using the div→/div← correspondence of DRbisim).
--
-- The FAILURES half needs ONE classical principle: a non-divergent process must
-- be able to reach a STABLE or TERMINATED (ret) state by some finite τ*-run — i.e.
-- a τ-normal-form.  (Earlier this concluded just `isStable t′`, which is UNSOUND: a
-- terminated `ret` state is non-divergent yet never stable, so it would prove ⊥.)
-- This is the only postulate in the development; it is the constructive obstruction
-- (bar induction) that makes the failures model classically flavoured.
--
-- NOTE: the postulate-free STABILITY helpers (`nothing≢just`, `stable-not-sil`,
-- `stable-not-ret`, `stable-react-τc`, `stable-no-τ`, `stable→¬div`, `stable→τ*-refl`)
-- now live in `Semantics.Stability`, and `⟹-then-τ*` in `Semantics.Failures`, so that
-- postulate-free clients can use them without importing this module.  Both are
-- re-exported below, so existing consumers of this module see no change.

open import Level using (Level; Lift; lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.DRImpliesFD
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS                 {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim           {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim             {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals            {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
  hiding (⟹-then-τ*)
open import Semantics.FailuresDivergences {ℓ} {ℓe} {ℓi} {E} {I}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
-- the one-way failure simulation this module's bridge theorems now factor through.
-- Imported with an explicit `using` (and NOT re-exported) so that the record fields
-- `fwd`/`stab`/`div→` of `FSim` do not leak into the 60 downstream modules that name this
-- one (`grep -rl DRImpliesFD --include='*.agda' src/`, minus this file); 52 of those carry
-- an actual `import Semantics.DRImpliesFD`, the rest only mention it in comments.
open import Semantics.FailureSim          {ℓ} {ℓe} {ℓi} {E} {I}
  using (FSim; fsim→⊑D; fsim→⊑F; fsim→⊑F⊥; fsim→⊑FD)
-- strong bisimulation's bridge into the DR layer, needed only for `bisim→⊑F` below
open import Semantics.Bisim               {ℓ} {ℓe} {ℓi} {E} {I} using (_∼_)
open import Semantics.StrongImpliesDR     {ℓ} {ℓe} {ℓi} {E} {I} using (sbisim→drbisim)

-- the stability helpers were moved out of this module (they are postulate-free);
-- re-exported here so that existing consumers keep seeing them
open import Semantics.Stability           {ℓ} {ℓe} {ℓi} {E} {I} public
-- likewise `⟹-then-τ*`, which now sits beside `τ*-then`/`weaken-τ`/`weaken-ev` in
-- Semantics.Failures.  It is `hiding`-ed from the import above so that this module
-- application is its single source here (two applications would make it ambiguous).
open import Semantics.Failures            {ℓ} {ℓe} {ℓi} {E} {I}
  using (⟹-then-τ*) public

-------------------------------------------------------------------------------------
-- THE one classical postulate: convergence yields a reachable τ-normal-form,
-- i.e. a state that is stable OR terminated (ret).  (Concluding `isStable t′` alone
-- is false — `Ret tt` is a non-divergent counterexample with no stable derivative.)
-------------------------------------------------------------------------------------

postulate
  ¬-divergent→normal : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                     → ¬ Diverges t
                     → Σ[ t′ ∈ PTree E I R ]
                         (t ─[τ*]─► t′ × (isStable t′ ⊎ Σ[ r ∈ R ] (PTree.force t′ ≡ ret r)))

-------------------------------------------------------------------------------------
-- DRbisim simulates τ-abstracting big-steps (the DRbisim analogue of `trace-sim`).
-------------------------------------------------------------------------------------

dr-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
             → DRbisim R P Q → P ⟹⟨ s ⟩ P′
             → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × DRbisim R P′ Q′)
dr-trace-sim pq ⟹-refl = _ , ⟹-refl , pq
dr-trace-sim pq (⟹-τ pτ rest) with pq .DRbisim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁q₁ with dr-trace-sim p₁q₁ rest
...   | Q′ , q⟹ , p′q′ = Q′ , weaken-τ qτ q⟹ , p′q′
dr-trace-sim pq (⟹-ev pev rest) with pq .DRbisim.fwd .WSimF.on-ev pev
... | _ , qev , p₁q₁ with dr-trace-sim p₁q₁ rest
...   | Q′ , q⟹ , p′q′ = Q′ , weaken-ev qev q⟹ , p′q′

-------------------------------------------------------------------------------------
-- Stable-state absorption: a stable Q stays DR-bisimilar across P's silent moves
-- and preserves P's offers.  (Both use that Q, being stable, matches a τ-move only
-- by staying put — `stable→τ*-refl`.)
-------------------------------------------------------------------------------------

dr-absorb-τ* : ∀ {ℓr} {R : Set ℓr} {Q P P′ : PTree E I R}
             → isStable Q → DRbisim R Q P → P ─[τ*]─► P′ → DRbisim R Q P′
dr-absorb-τ* stQ qp τ*-refl          = qp
dr-absorb-τ* stQ qp (τ*-step pτ rest) with qp .DRbisim.bwd .WSimF.on-tau pτ
... | Q₁ , wτ q→q₁ , p₁q₁ with stable→τ*-refl stQ q→q₁
...   | refl = dr-absorb-τ* stQ (drbisim-sym p₁q₁) rest

offers-preserved : ∀ {ℓr} {R : Set ℓr} {Q P : PTree E I R} {e : Event√ R}
                 → isStable Q → DRbisim R Q P → Offers P e → Offers Q e
offers-preserved stQ qp (P′ , pev) with qp .DRbisim.bwd .WSimF.on-ev pev
... | Q′ , wev q→qa qaev qb→q′ , _ with stable→τ*-refl stQ q→qa
...   | refl = _ , qaev

-- a stable state cannot be DR-bisimilar to a terminated (ret) state: the ret offers
-- √, but a stable (react) state offers no √, so simulating that √-step forces `force Q`
-- to be `ret`, contradicting stability.
stable-≉-ret : ∀ {ℓr} {R : Set ℓr} {Q P : PTree E I R} {r : R}
             → isStable Q → DRbisim R Q P → PTree.force P ≡ ret r → ⊥
stable-≉-ret {Q = Q} {P = P} stQ qp eqP with qp .DRbisim.bwd .WSimF.on-ev (sRet {p = P} eqP)
... | _ , wev q→qa qaev qb→q′ , _ with stable→τ*-refl stQ q→qa
...   | refl with qaev
...     | sRet eqQ = stable-not-ret {t = Q} stQ eqQ

-------------------------------------------------------------------------------------
-- ≈DR is (in each direction) a failure simulation.  This is where — and the ONLY
-- place where — the classical postulate is consumed: `stab` must hand back a STABLE
-- specification state, and manufacturing one from mere non-divergence is exactly
-- `¬-divergent→normal`.  `Semantics.FailureSim` itself stays postulate-free because
-- its `stab` field is a hypothesis there rather than something to be established.
-------------------------------------------------------------------------------------

-- forward-declared pair (no mutual block): the WSimF-level map, and the coinductive
-- translation whose corecursive call sits under the Σ-result of the simulation
dr-sim→f-sim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
             → WSimF (DRbisim R) t₁ t₂ → WSimF (FSim R) t₁ t₂
-- a DRbisim yields a failure simulation in the SAME orientation (t₁ impl, t₂ spec):
-- keep `fwd` and `div→`, drop `bwd`, and derive `stab` from `div←` + the postulate
drbisim→fsim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → DRbisim R t₁ t₂ → FSim R t₁ t₂

dr-sim→f-sim sim .WSimF.on-ev  st with sim .WSimF.on-ev  st
... | _ , w , rel = _ , w , drbisim→fsim rel
dr-sim→f-sim sim .WSimF.on-tau st with sim .WSimF.on-tau st
... | _ , w , rel = _ , w , drbisim→fsim rel

drbisim→fsim pq .FSim.fwd  = dr-sim→f-sim (pq .DRbisim.fwd)
drbisim→fsim pq .FSim.div→ = pq .DRbisim.div→
-- t₁ stable ⇒ t₁ converges ⇒ (via div←) t₂ converges ⇒ t₂ reaches a τ-normal form;
-- that form cannot be `ret` (a stable state is never DR-bisimilar to a `ret`), so it
-- is stable, and its offers are contained in t₁'s by `offers-preserved`
drbisim→fsim pq .FSim.stab st₁
  with ¬-divergent→normal (λ d₂ → stable→¬div st₁ (pq .DRbisim.div← d₂))
... | t₂′ , t₂→t₂′ , inj₁ st₂′ =
      t₂′ , t₂→t₂′ , st₂′ ,
      λ e off → offers-preserved st₁ (dr-absorb-τ* st₁ pq t₂→t₂′) off
... | t₂′ , t₂→t₂′ , inj₂ (r , eqret) =
      ⊥-elim (stable-≉-ret st₁ (dr-absorb-τ* st₁ pq t₂→t₂′) eqret)

-------------------------------------------------------------------------------------
-- The bridge, now a corollary of `Semantics.FailureSim`.  The `drbisim-sym` is forced
-- by the orientations: `drbisim→⊑D : DRbisim R P Q → P ⊑D Q` while
-- `fsim→⊑D : FSim R Q P → P ⊑D Q`, so the FSim needed has Q as its impl.
-------------------------------------------------------------------------------------

-- divergences are respected (constructive part of the bridge)
drbisim→⊑D : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑D Q
drbisim→⊑D pq = fsim→⊑D (drbisim→fsim (drbisim-sym pq))

-- divergence-strict failures are respected (the postulate is inside `drbisim→fsim`)
drbisim→⊑F⊥ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑F⊥ Q
drbisim→⊑F⊥ pq = fsim→⊑F⊥ (drbisim→fsim (drbisim-sym pq))

-- stable failures are respected (the divergence-free half of `drbisim→⊑F⊥`, useful on
-- its own when the target refinement is `⊑F` rather than `⊑F⊥`/`⊑FD`)
drbisim→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑F Q
drbisim→⊑F pq = fsim→⊑F (drbisim→fsim (drbisim-sym pq))

drbisim→⊑FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ⊑FD Q
drbisim→⊑FD pq = fsim→⊑FD (drbisim→fsim (drbisim-sym pq))

drbisim→≈FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → DRbisim R P Q → P ≈FD Q
drbisim→≈FD pq = drbisim→⊑FD pq , drbisim→⊑FD (drbisim-sym pq)

-------------------------------------------------------------------------------------
-- STRONG bisimulation also gives `⊑F`, via `Semantics.StrongImpliesDR.sbisim→drbisim`
-- (mirroring how CSP-layer call sites already compose `drbisim→≈FD (sbisim→drbisim …)`,
-- e.g. `CSP.Laws.FD.HideCombine.hide-combine-FD`).  Kept here, next to `drbisim→⊑F`,
-- since it is this module's postulate that the composed proof ultimately consumes.
-------------------------------------------------------------------------------------

-- stable failures are respected across a strong bisimulation
bisim→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → P ∼ Q → P ⊑F Q
bisim→⊑F pq = drbisim→⊑F (sbisim→drbisim pq)
