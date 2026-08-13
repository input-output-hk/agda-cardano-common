{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the WALK DESCENT ENGINE (`Praos.WalkEngine`).
--
-- `Walk.agda` reduced the R3 target `abstractLive` to the single POSITIVE
-- walk hypothesis
--
--   walkPos : (b) (tr : WTrace ⊤ abstractSystem)
--           → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
--           → ∀ n → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
--           → ⟦ F (atom arrivedD⁻) ⟧ᵂ (drop n tr)
--
-- (the classical wrapper `respondsᵂ-intro`/`abstractLive` are already green,
-- parameterised over `walkPos`).  `walkPos` is a well-founded delivery
-- descent: block `b`, once produced at A, reaches D in finitely many
-- observable steps.
--
-- THIS module delivers the WELL-FOUNDED DESCENT ENGINE `walkPosFrom` that
-- turns `walkPos` into THREE clean per-state hypotheses — mirroring exactly
-- the sanctioned `WalkConv` pattern (which delivered `absNoDiv` parameterised
-- over a measure `μτ` and a per-τ reflector `τreflect`, then instantiated
-- them).  Here the engine is parameterised over:
--
--   · a whole-trace measure  `μ : SysState → ℕ`  (instantiate = `Walk.μTot`,
--     or an AUGMENTED measure if the classification needs CS/BF peer weights —
--     the engine is measure-generic exactly so that a later augmentation à la
--     `WalkConv.posWt` does not disturb the assembly);
--   · a "still-pending" invariant  `Pr : RState → Set`  (block `b` produced,
--     not yet delivered on the intact group — the invariant that makes the
--     descent sound: it is what forbids the delivered/terminal states at which
--     neither `arrivedD`-now nor a strict decrease exists);
--   · `deliver` — the per-observable-step reflector: at a reachable, confined,
--     PENDING state, EITHER the current frame is the `recvBFBlock@D` step
--     (`arrivedD` now) OR there is a reachable successor with strictly smaller
--     `μ` still satisfying `Pr` (the STEP-LIFT + event classification — the
--     heavy `SysOracle`-cone content, via `oevB`/`otauB` + `μGk-adv-*`);
--   · `locate` — the START reachability: `drop n tr` at the `producedA` frame
--     decodes a reachable `Pr`-config (the n-step forward reachability lift).
--
-- Given these, the engine performs the WF induction on `μ (toSys r)` (mirror
-- of `WalkConv.absNoDiv-acc`), assembles the positive `F`-witness (`F φ = ⊤' U
-- φ` is a Σ — a `suc k` prepend per step), threads the confinement to suffixes
-- (definitional `drop`/`tail` restriction), and transports along the reachable
-- successor equalities.  ALL of that mechanical spine is discharged here,
-- LIGHT (no `SysOracle` cone), 0-postulate; the ENTIRE remaining R3 obligation
-- is the three heavy hypotheses `Pr`/`deliver`/`locate`.
------------------------------------------------------------------------

open import Level using ( 0ℓ; Lift; lift )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ; zero; suc; _<_ )
open import Data.Nat.Induction using ( <-wellFounded )
open import Induction.WellFounded using ( Acc; acc )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
import Data.Unit as U
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkEngine (blkA : Block₃) where

------------------------------------------------------------------------
-- The model, the reachable-config machinery, and the LTL/WTrace layer.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
  using ( abstractSystem )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom; ¬_; F_ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; dropIdx; tail; tailIdx )

open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD⁻; brkG1; brkG2 )

-- match `Walk.agda`'s positive-globally exactly (so `walkPosFrom` produces the
-- literal type of `Walk`'s `walkPos` module parameter)
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.Walk blkA
  using ( G⁺ᵂ )

-- the whole-system process type at the shared alphabet
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

------------------------------------------------------------------------
-- CONFINEMENT carried along a suffix: one intact group never breaks.
------------------------------------------------------------------------

-- the positive `⊎`-confinement usable at (a suffix) WTrace `w`
Confᵂ : {t : NetProc} → WTrace (⊤ {0ℓ}) t → Set
Confᵂ w = G⁺ᵂ (¬ atom brkG1) w ⊎ G⁺ᵂ (¬ atom brkG2) w

-- G⁺ restricts to the tail: `drop m (tail w) ≡ drop (suc m) w` DEFINITIONALLY
-- (`drop (suc n) tr = drop n (tail tr)`), so this needs no `subst`
G⁺-tail : (φ : LTLᵗ 0ℓ (⊤ {0ℓ})) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
        → G⁺ᵂ φ w → G⁺ᵂ φ (tail w)
G⁺-tail φ w g m = g (suc m)

-- confinement restricts to the tail
Conf-tail : {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → Confᵂ w → Confᵂ (tail w)
Conf-tail w (inj₁ g) = inj₁ (G⁺-tail (¬ atom brkG1) w g)
Conf-tail w (inj₂ g) = inj₂ (G⁺-tail (¬ atom brkG2) w g)

-- G⁺ restricts to an n-fold suffix `drop n w` (iterate the tail restriction;
-- `drop (suc n) w = drop n (tail w)` DEFINITIONALLY, so still no `subst`)
G⁺-dropn : (φ : LTLᵗ 0ℓ (⊤ {0ℓ})) (n : ℕ) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
         → G⁺ᵂ φ w → G⁺ᵂ φ (drop n w)
G⁺-dropn φ zero    w g = g
G⁺-dropn φ (suc n) w g = G⁺-dropn φ n (tail w) (G⁺-tail φ w g)

-- confinement restricts to `drop n w`
Conf-dropn : (n : ℕ) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → Confᵂ w → Confᵂ (drop n w)
Conf-dropn n w (inj₁ g) = inj₁ (G⁺-dropn (¬ atom brkG1) n w g)
Conf-dropn n w (inj₂ g) = inj₂ (G⁺-dropn (¬ atom brkG2) n w g)

-- transport confinement along an index equality (used at the reachable
-- successor / the located start; the `refl` match is on this function's OWN
-- fresh parameter `eq`, so it is legal even though `radec r′` is not a var)
Conf-subst : {t₁ t₂ : NetProc} (eq : t₁ ≡ t₂) {w : WTrace (⊤ {0ℓ}) t₁}
           → Confᵂ w → Confᵂ (subst (WTrace (⊤ {0ℓ})) eq w)
Conf-subst refl x = x

------------------------------------------------------------------------
-- POSITIVE `F`-witness plumbing (`F φ = ⊤' U φ`, a Σ).
------------------------------------------------------------------------

-- prepend one observable step to an `F`-witness: `drop (suc k) w = drop k
-- (tail w)` DEFINITIONALLY, so the `⟦φ⟧ᵂ` cell carries over unchanged and the
-- `< suc k` before-cells are the trivial `Lift ⊤`
F-suc : (φ : LTLᵗ 0ℓ (⊤ {0ℓ})) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
      → ⟦ F_ φ ⟧ᵂ (tail w) → ⟦ F_ φ ⟧ᵂ w
F-suc φ w (k , pf , _) = suc k , pf , λ _ _ → lift U.tt

-- transport an `F`-witness back along an index equality (same legal `refl`
-- match on the function's own `eq`)
F-transport : (φ : LTLᵗ 0ℓ (⊤ {0ℓ})) {t₁ t₂ : NetProc} (eq : t₁ ≡ t₂) (w : WTrace (⊤ {0ℓ}) t₁)
            → ⟦ F_ φ ⟧ᵂ (subst (WTrace (⊤ {0ℓ})) eq w) → ⟦ F_ φ ⟧ᵂ w
F-transport φ refl w x = x

------------------------------------------------------------------------
-- THE WELL-FOUNDED DELIVERY DESCENT (mirror of `WalkConv.absNoDiv-acc`).
--
-- Parameterised over the block `b`, the measure `μ`, the pending invariant
-- `Pr`, and the per-step reflector `dl` (= `deliver b`).  Given a reachable,
-- confined, pending `r` with `μ (toSys r)` accessible, produces the positive
-- `⟦ F (arrivedD b) ⟧ᵂ w`.
------------------------------------------------------------------------

module _
  (b : Block₃)
  (μ : SysState → ℕ)
  (Pr : RState → Set)
  (dl : (r : RState) → Pr r → (w : WTrace (⊤ {0ℓ}) (radec r)) → Confᵂ w
      → ⟦ atom arrivedD⁻ ⟧ᵂ w
      ⊎ Σ[ r′ ∈ RState ] (tailIdx w ≡ radec r′) × (μ (toSys r′) < μ (toSys r)) × Pr r′)
  where

  -- accessible form: with `μ (toSys r)` accessible, delivery from `r`
  descend-acc : (r : RState) → Pr r → (w : WTrace (⊤ {0ℓ}) (radec r)) → Confᵂ w
              → Acc _<_ (μ (toSys r)) → ⟦ F_ (atom arrivedD⁻) ⟧ᵂ w
  descend-acc r pr w cf (acc rec) with dl r pr w cf
  ... | inj₁ arr             = zero , arr , λ _ ()
  ... | inj₂ (r′ , eq , lt , pr′) =
        F-suc (atom arrivedD⁻) w
          (F-transport (atom arrivedD⁻) eq (tail w)
            (descend-acc r′ pr′
              (subst (WTrace (⊤ {0ℓ})) eq (tail w))
              (Conf-subst eq (Conf-tail w cf))
              (rec lt)))

  -- delivery from any reachable, confined, pending `r`
  descend : (r : RState) → Pr r → (w : WTrace (⊤ {0ℓ}) (radec r)) → Confᵂ w
          → ⟦ F_ (atom arrivedD⁻) ⟧ᵂ w
  descend r pr w cf = descend-acc r pr w cf (<-wellFounded (μ (toSys r)))

------------------------------------------------------------------------
-- `walkPosFrom` — the engine's headline: the three heavy hypotheses give
-- `Walk.agda`'s `walkPos` module-parameter type EXACTLY.
------------------------------------------------------------------------

walkPosFrom :
    (μ : SysState → ℕ)
    (Pr : Block₃ → RState → Set)
    (deliver : (b : Block₃) (r : RState) → Pr b r
             → (w : WTrace (⊤ {0ℓ}) (radec r)) → Confᵂ w
             → ⟦ atom arrivedD⁻ ⟧ᵂ w
             ⊎ Σ[ r′ ∈ RState ] (tailIdx w ≡ radec r′)
                 × (μ (toSys r′) < μ (toSys r)) × Pr b r′)
    (locate : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
            → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
            → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0)
  → (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem)
  → (G⁺ᵂ (¬ atom brkG1) tr ⊎ G⁺ᵂ (¬ atom brkG2) tr)
  → (n : ℕ) → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
  → ⟦ F_ (atom arrivedD⁻) ⟧ᵂ (drop n tr)
walkPosFrom μ Pr deliver locate b tr conf⊎ n prod with locate b tr n prod
... | r0 , eq0 , pr0 =
      F-transport (atom arrivedD⁻) eq0 (drop n tr)
        (descend b μ (Pr b) (deliver b) r0 pr0
          (subst (WTrace (⊤ {0ℓ})) eq0 (drop n tr))
          (Conf-subst eq0 (Conf-dropn n tr conf⊎′)))
  where
    -- the input `⊎`-confinement, re-viewed at `tr` as the engine's `Confᵂ`
    conf⊎′ : Confᵂ tr
    conf⊎′ = conf⊎
