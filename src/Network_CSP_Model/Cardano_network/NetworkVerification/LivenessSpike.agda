{-# OPTIONS --guardedness --allow-unsolved-metas #-}

------------------------------------------------------------------------
-- SPIKE MODULE — FourNode liveness feasibility (Q1 gate + Q1c BisimStable).
--
--   * DISPOSABLE.  Imported by NOTHING; deleted after the findings are
--     harvested into the real campaign.  `--allow-unsolved-metas` /
--     postulates are permitted HERE ONLY (per the spike design doc
--     docs/superpowers/specs/2026-07-15-fournode-liveness-spike-design.md).
--   * NEVER steps `breakableSystem` or any whole-node composite (the
--     documented ≈2.5 min / ≈20 GB single-step wall) — all probing is on
--     the generic layer, on `deadlock`, or on hand-built frames.
--
-- What this module SETTLES (see the report Q1/Q1c):
--
--   Q1a (read, in report): the MODEL-WIDE `Realisable R`
--     (Convergence.agda:38) quantifies `τprog : ∀ (s : PTree E I R) → …`
--     over EVERY tree of result type `R` — including `breakableSystem` and
--     all composites — so `⊨-DRWB-invariant→` (WBisimInvariant.agda:230)
--     is undischargeable for architecture A.  The PER-TREE
--     `Realisableᴿ t` (WBisimInvariantR.agda:39) restricts both fields to
--     states REACHABLE from `t` (`t ↠ s`); its theorem
--     `⊨-DRWB-invariantᴿ→` (WBisimInvariantR.agda:113) needs
--     `Realisableᴿ t₁` on the SOURCE side of `t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ`.  For
--     architecture A we conclude `breakableSystem ⊨ᵂ φ` (= t₂) from
--     `abstract ⊨ᵂ φ` (= t₁), so the obligation is `Realisableᴿ abstract`
--     — over the SMALL abstract system's reachable states only.  Gate opens.
--
--   Q1b (§1 below): `Realisableᴿ` is genuinely dischargeable WITHOUT any
--     model-wide quantifier and WITHOUT stepping a composite:
--       · `τfreeᴿ→Realisableᴿ` — reachability-restricted τ-freeness
--         suffices (the R-analogue of `τfree-Realisable`, but the ∀ is
--         over `t ↠ s`, not over all `s`);
--       · `deadlock-Realisableᴿ` — a concrete, fully-closed witness.
--
--   Q1c (§2 below): `BisimStable` holds for all four liveness atoms AND
--     for the whole `respondsAtoD` formula (built from the derived
--     `G`/`F`/`⇒`/`∨`).  Fully discharged, no holes.
--
--   §3: the ONE genuinely new obligation the Q1 lead did not mention —
--     the transfer theorem lives on `⊨ᵂ` (WTrace) but the spec target
--     `BlockLiveness⁺` lives on `⊨`/`Trace`; the needed bridge direction
--     (`⊨ᵂ ⇒ ⊨`, a Trace↪WTrace terminator-generalisation embedding) is
--     stated as the obligation to discharge in the real campaign.
------------------------------------------------------------------------

open import Level using (Level; 0ℓ) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Examples.Cardano_network.NetworkVerification.LivenessSpike where

open PTree

------------------------------------------------------------------------
-- The concrete alphabet — the SAME one `breakableSystem` and the four atoms
-- run over, so §2's `BisimStable` proofs consume the REAL atoms.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using (p; Block₃)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.Net p
  using (Net_Api; apiBF; break; sendBFBlock; recvBFBlock)

private
  E : Set 0ℓ → Set _
  E = Net_Api Payload

  I : Set 0ℓ → Set _
  I = ExtI (Net_Api Payload)

open import Semantics.LTS      {E = E} {I = I}
open import Semantics.Deadlock {E = E} {I = I} using (IsStuck)
open import Semantics.DRBisim  {E = E} {I = I} using (DRbisim; _≈DR_)
open import Semantics.LTL.Convergence      {E = E} {I = I}
open import Semantics.LTL.WBisimInvariantR {E = E} {I = I}
  using (Realisableᴿ; τprogᴿ; convᴿ)

------------------------------------------------------------------------
-- §1  Q1b — `Realisableᴿ` is dischargeable on the abstract side.
------------------------------------------------------------------------

-- `deadlock` (the empty-offer react node) rejects EVERY LTS label.
-- (Local copy of `Semantics.Deadlock`'s `deadlock-IsStuck`, kept private
-- so the spike does not depend on that lemma's export status.)
deadlock-stuck : ∀ {ℓr} {R : Set ℓr} → IsStuck (deadlock {E = E} {I = I} {R = R})
deadlock-stuck (sRet ())
deadlock-stuck (sSil ())
deadlock-stuck (sVis refl ())
deadlock-stuck (sTau refl ())

-- From a STUCK root, τ+visible reachability `↠` cannot leave the root.
-- This is the finite-reachability fact the abstract side relies on: for a
-- terminal state the reachable set is a singleton.
↠-from-stuck : ∀ {ℓr} {R : Set ℓr} {t s : PTree E I R}
             → IsStuck t → t ↠ s → s ≡ t
↠-from-stuck st ↠-refl      = refl
↠-from-stuck st (↠-τ  x _)  = ⊥-elim (st x)
↠-from-stuck st (↠-ev x _)  = ⊥-elim (st x)

-- KEY LEMMA (Q1b).  Reachability-restricted τ-freeness ⇒ `Realisableᴿ`.
--
-- The R-analogue of `RealisableInstances.τfree-Realisable`, but the
-- premise quantifies only over states REACHABLE from `t` (`t ↠ s`), NOT
-- over the whole model.  This is EXACTLY the abstract-side gate: if the
-- small abstract system's reachable fragment has no τ (or, more generally,
-- a finite decidable τ structure), the record is discharged — the composite
-- `breakableSystem` never enters the obligation.
τfreeᴿ→Realisableᴿ :
    ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
  → (∀ {s s′ : PTree E I R} → t ↠ s → s ─[ τ ]─► s′ → ⊥)
  → Realisableᴿ t
τprogᴿ (τfreeᴿ→Realisableᴿ tf) r     = inj₂ (λ st → tf r st)
convᴿ  (τfreeᴿ→Realisableᴿ tf) r _ _ = cvg (λ st → ⊥-elim (tf r st))

-- CONCRETE WITNESS (Q1b).  `deadlock` is `Realisableᴿ` — fully closed, no
-- holes, no postulates, no composite stepped.  (`deadlock` is the τ-free
-- fragment's degenerate case; a nontrivial abstract system built from the
-- prefix / external-choice fragment discharges the premise of
-- `τfreeᴿ→Realisableᴿ` the same way, by a finite `↠`-inversion.)
deadlock-Realisableᴿ : Realisableᴿ (deadlock {E = E} {I = I} {R = ⊤ {0ℓ}})
deadlock-Realisableᴿ =
  τfreeᴿ→Realisableᴿ
    (λ r st → deadlock-stuck (subst-step (↠-from-stuck deadlock-stuck r) st))
  where
    -- transport the τ-step back along `s ≡ deadlock`
    subst-step : ∀ {s s′ : PTree E I (⊤ {0ℓ})}
               → s ≡ deadlock → s ─[ τ ]─► s′ → deadlock ─[ τ ]─► s′
    subst-step refl st = st

------------------------------------------------------------------------
-- §2  Q1c — `BisimStable` for the four atoms and the whole formula.
------------------------------------------------------------------------

open import Semantics.LTL.Traces_Based {E = E} {I = I}
  using ( Frame; FramePred; LTLᵗ; atom; ⊤'; ¬_; _∧_; X_; _U_
        ; _∨_; _⇒_; F_; G_ )
open import Semantics.LTL.FrameSim {E = E} {I = I}
  using ( FrameSim; BisimStable; bs-⊤; bs-atom; bs-¬; bs-∧; bs-X; bs-U )

-- the real atoms + formula from the LTL spec module (unmodified).
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( producedA; arrivedD; brkG1; brkG2; confined; respondsAtoD )

-- A `step`-frame atom is bisim-stable: `FrameSim` on two `step` frames
-- forces the events equal (`e₁ ≡ e₂`), and every atom below inspects ONLY
-- the event, never the (state) slot — so `P fr₁ → P fr₂` is `refl`-transport.
-- The `bs-atom` witness pattern-matches the source frame into the atom's
-- matching shape; every non-matching source makes `P fr₁ = ⊥`, absurd.

producedA-BS : ∀ b → BisimStable (atom (producedA b))
producedA-BS b = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → producedA b fr₁ → producedA b fr₂
    stab {Frame.step _ (evl (evLabel _ (apiBF l d sendBFBlock) a))}
         {Frame.step _ _} (refl , _) q = q

arrivedD-BS : ∀ b → BisimStable (atom (arrivedD b))
arrivedD-BS b = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → arrivedD b fr₁ → arrivedD b fr₂
    stab {Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))}
         {Frame.step _ _} (refl , _) q = q

brkG1-BS : BisimStable (atom brkG1)
brkG1-BS = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → brkG1 fr₁ → brkG1 fr₂
    stab {Frame.step _ (evl (evLabel _ (break l) _))}
         {Frame.step _ _} (refl , _) q = q

brkG2-BS : BisimStable (atom brkG2)
brkG2-BS = bs-atom stab
  where
    stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → brkG2 fr₁ → brkG2 fr₂
    stab {Frame.step _ (evl (evLabel _ (break l) _))}
         {Frame.step _ _} (refl , _) q = q

-- BisimStable is closed under the DERIVED operators (definitional unfolds).
bs-F : ∀ {ℓa} {φ : LTLᵗ ℓa (⊤ {0ℓ})} → BisimStable φ → BisimStable (F φ)
bs-F bφ = bs-U bs-⊤ bφ

bs-G : ∀ {ℓa} {φ : LTLᵗ ℓa (⊤ {0ℓ})} → BisimStable φ → BisimStable (G φ)
bs-G bφ = bs-¬ (bs-U bs-⊤ (bs-¬ bφ))

bs-∨ : ∀ {ℓa} {φ ψ : LTLᵗ ℓa (⊤ {0ℓ})}
     → BisimStable φ → BisimStable ψ → BisimStable (φ ∨ ψ)
bs-∨ bφ bψ = bs-¬ (bs-∧ (bs-¬ bφ) (bs-¬ bψ))

bs-⇒ : ∀ {ℓa} {φ ψ : LTLᵗ ℓa (⊤ {0ℓ})}
     → BisimStable φ → BisimStable ψ → BisimStable (φ ⇒ ψ)
bs-⇒ bφ bψ = bs-∨ (bs-¬ bφ) bψ

-- Q1c CAPSTONE: the WHOLE liveness formula is bisim-stable.
-- confined = G(¬ brkG1) ∨ G(¬ brkG2)
confined-BS : BisimStable confined
confined-BS = bs-∨ (bs-G (bs-¬ brkG1-BS)) (bs-G (bs-¬ brkG2-BS))

-- respondsAtoD b = confined ⇒ G (atom (producedA b) ⇒ F (atom (arrivedD b)))
respondsAtoD-BS : ∀ b → BisimStable (respondsAtoD b)
respondsAtoD-BS b =
  bs-⇒ confined-BS
       (bs-G (bs-⇒ (producedA-BS b) (bs-F (arrivedD-BS b))))

------------------------------------------------------------------------
-- §3  The layer-bridge obligation (new finding — NOT in the Q1 lead).
--
-- `⊨-DRWB-invariantᴿ→` concludes `breakableSystem ⊨ᵂ φ` on the WTrace layer
-- (`Semantics.LTL.WTrace._⊨ᵂ_`), but `BlockLiveness`/`BlockLiveness⁺` are
-- stated on the coinductive-`Trace` layer (`Semantics.LTL.Traces_Based._⊨_`
-- / `◇ᵗ` / `□ᵗ`).  The two layers share the SAME `step` relation
-- (`═[ ev e ]═►`) and differ ONLY in terminators: a `Trace` `done`/`stuck`
-- is IMMEDIATE (`force ≡ ret` / `IsStuck`), a `WTrace` `done`/`stuck` allows
-- a `─[τ*]─►` prefix.  Hence every `Trace` embeds into a `WTrace` (take
-- `τ*-refl`), giving the needed direction `⊨ᵂ ⇒ ⊨` by specialisation.  The
-- obligation the campaign must discharge (stated, NOT proved here):
--
--   Trace↪WTrace : ∀ {R} {t} → Trace R t → WTrace R t         (embedding)
--   frame-agree  : frameOf (Trace↪WTrace tr) ≡ frameOfᵀ tr    (observations)
--   ⊨ᵂ⇒⊨        : t ⊨ᵂ φ → t ⊨ φ                             (corollary)
--
-- Modest (an embedding + a frame-observation-agreement lemma), NOT a gate.
------------------------------------------------------------------------
