{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Fairness transfer across the campaign seams (campaign milestone F2).
--
-- F1 (`Semantics.LTL.Fairness`) shipped the visible-class weak-fairness
-- notion on the coinductive `Trace` layer.  F2 ships the TRANSFER layer the
-- M5 endgame needs: a `Fair C` fact on a concrete `breakableSystem` trace must
-- become a `Fair`-fact on the abstract trace the ≈DR transport produces, so
-- the abstract liveness walk can consume it.
--
-- Direction (verified against `⊨-DRWB-invariantᴿ→`, WBisimInvariantR):
-- that theorem takes a t₂-trace (t₂ = the concrete `breakableSystem`), transports
-- it BACKWARD to a corresponding t₁-trace (t₁ = the abstract spec, on which
-- liveness is proved), producing `sim : WTraceSim (concrete) (abstract)`, runs
-- the t₁-side satisfaction, then transports the result forward.  The `Fair C`
-- hypothesis rides on the CONCRETE trace (per `BlockLiveness⁺ᶠ`, spike-report
-- §Q3), so the campaign transfers fairness FORWARD along that same
-- `WTraceSim` (concrete ↝ abstract).  Hence the primary shipped shape is
-- `Fairᵂ-transfer : WTraceSim tr₁ tr₂ → Fairᵂ C tr₁ → Fairᵂ C tr₂`, used with
-- tr₁ = concrete-embedded, tr₂ = abstract.  `WTraceSim`-symmetry gives the
-- reverse for free (`Fairᵂ-transfer←`).
--
-- Because the ≈DR transport lives on the WTrace layer (`⟦⟧ᵂ-transport`,
-- `WTraceSim`), fairness must be stated there too; `Fairᵂ` mirrors F1's `Fair`
-- with WTrace's `frameOf`/`drop`/`⟦_⟧ᵂ`.  The `WEnabled`/`Fires` vocabulary is
-- REUSED verbatim from F1 (both are stated on the shared `Frame`/`PTree`, not
-- on either trace layer), so the harvested `wenabled-invariant` and the
-- `Fires` correspondence carry over with no re-statement.  The M0-bridge
-- extension (`Fair→Fairᵂ`) lifts a Trace-level `Fair` onto its embedded
-- WTrace, using M0's `frame-agree` + `drop-sem-bwd`.
--
-- Harvest note (√-free `C`): the spike's `wenabled-invariant` typed `C` over
-- `Event√ R`; F1's review retyped the class to the √-FREE `Event`.  The proof
-- body is unchanged (one `dr-wev-sim`) — only the reused `WEnabled`'s domain
-- moved, which is transparent here.
--
-- Generic (model-agnostic): parametric in E, I, R, and the class `C`.  NO
-- postulate, NO new classical axiom (spike-report §"Any new classical-axiom
-- need": NONE) — every lemma is a constructive consequence of `dr-wev-sim`,
-- `FrameSim`, `⟦⟧ᵂ-transport`, and the M0 bridge.
------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Process_Trees using (PTree)

module Semantics.LTL.FairnessTransfer
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} using (Event; Event√; evl; √)
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}
  using (_≈DR_; DRbisim; dr-wev-sim; drbisim-sym)

-- The Trace-based LTL layer: qualified `T` for the pieces whose names clash
-- with the WTrace layer; the shared frame/formula vocabulary unqualified.
import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I} as T
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using ( Frame; step; done; stuck; div
        ; frameState; FramePred; LTLᵗ; atom; ⊤'; F_; ◇ᵗ; ◇ᵗ⇒F )

-- The WTrace layer: qualified `W`.
import Semantics.LTL.WTrace {ℓ} {ℓe} {ℓi} {E} {I} as W

open import Semantics.LTL.FrameSim {ℓ} {ℓe} {ℓi} {E} {I}
  using (FrameSim; BisimStable; bs-⊤; bs-atom; bs-U)
open import Semantics.LTL.WBisimInvariant {ℓ} {ℓe} {ℓi} {E} {I}
  using (WTraceSim; heads; tails; drop-WTraceSim; WTraceSim-sym; ⟦⟧ᵂ-transport)
-- F1's fairness vocabulary — reused verbatim (state/frame level, layer-agnostic).
open import Semantics.LTL.Fairness {ℓ} {ℓe} {ℓi} {E} {I}
  using (WEnabled; Fires; enabledAt; Fair)
-- M0's Trace↪WTrace bridge (frame agreement + per-drop semantic embedding).
open import Semantics.LTL.TraceBridge {ℓ} {ℓe} {ℓi} {E} {I}
  using (Trace↪WTrace; frame-agree; drop-sem-bwd)

------------------------------------------------------------
-- §1  The harvested crux: weak-enabledness is ≈DR-invariant.
--
-- Spike-report §Q2(a) / FairnessSpike §9, adapted to F1's √-free `C`: the
-- reused `WEnabled` already quantifies its weak visible step over `evl e`
-- (a √-free `Event`), so the one-line `dr-wev-sim` proof carries over.
------------------------------------------------------------

-- Weak-enabledness of a visible class transfers across ≈DR-corresponding states.
wenabled-invariant : ∀ {ℓr ℓc} {R : Set ℓr} {t₁ t₂ : PTree E I R} {C : Event → Set ℓc}
                   → t₁ ≈DR t₂ → WEnabled C t₁ → WEnabled C t₂
wenabled-invariant dr (e , t′ , w , ce) with dr-wev-sim w dr
... | t₂′ , w₂ , _ = e , t₂′ , w₂ , ce

------------------------------------------------------------
-- §2  Frame-level correspondence pieces.
--
-- `FrameSim` records that corresponding frames carry ≈DR-related states and
-- (at `step` frames) the SAME event.  From that: (a) their states are ≈DR
-- (so `WEnabled` transfers), and (b) `Fires` is preserved (same event).
------------------------------------------------------------

-- The states of two FrameSim-corresponding frames are ≈DR-related.
framestate-≈DR : ∀ {ℓr} {R : Set ℓr} {fr₁ fr₂ : Frame R}
               → FrameSim fr₁ fr₂ → frameState fr₁ ≈DR frameState fr₂
framestate-≈DR {fr₁ = step _ _}  {step _ _}  (_ , b) = b
framestate-≈DR {fr₁ = done _ _}  {done _ _}  (_ , b) = b
framestate-≈DR {fr₁ = stuck _}   {stuck _}   b       = b
framestate-≈DR {fr₁ = div _}     {div _}     b       = b
framestate-≈DR {fr₁ = step _ _}  {done _ _}  (lift ())
framestate-≈DR {fr₁ = step _ _}  {stuck _}   (lift ())
framestate-≈DR {fr₁ = step _ _}  {div _}     (lift ())
framestate-≈DR {fr₁ = done _ _}  {step _ _}  (lift ())
framestate-≈DR {fr₁ = done _ _}  {stuck _}   (lift ())
framestate-≈DR {fr₁ = done _ _}  {div _}     (lift ())
framestate-≈DR {fr₁ = stuck _}   {step _ _}  (lift ())
framestate-≈DR {fr₁ = stuck _}   {done _ _}  (lift ())
framestate-≈DR {fr₁ = stuck _}   {div _}     (lift ())
framestate-≈DR {fr₁ = div _}     {step _ _}  (lift ())
framestate-≈DR {fr₁ = div _}     {done _ _}  (lift ())
framestate-≈DR {fr₁ = div _}     {stuck _}   (lift ())

-- `Fires` is preserved across FrameSim-corresponding frames: only `step`/`evl`
-- frames fire, and there FrameSim pins the event equal, so the class-membership
-- witness carries over; every other source frame makes `Fires C` empty.
Fires-frameSim : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc} {fr₁ fr₂ : Frame R}
               → FrameSim fr₁ fr₂ → Fires C fr₁ → Fires C fr₂
Fires-frameSim {fr₁ = step _ (evl _)} {step _ _} (refl , _) f = f
Fires-frameSim {fr₁ = step _ (evl _)} {done _ _} (lift ())
Fires-frameSim {fr₁ = step _ (evl _)} {stuck _}  (lift ())
Fires-frameSim {fr₁ = step _ (evl _)} {div _}    (lift ())
Fires-frameSim {fr₁ = step _ (√ _)}   _ (lift ())
Fires-frameSim {fr₁ = done _ _}       _ (lift ())
Fires-frameSim {fr₁ = stuck _}        _ (lift ())
Fires-frameSim {fr₁ = div _}          _ (lift ())

-- `atom (Fires C)` is a bisim-stable atom (the `bs-atom` witness Fires' preservation gives).
fires-stable : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
             → BisimStable {R = R} (atom (Fires C))
fires-stable = bs-atom Fires-frameSim

-- Hence `F (atom (Fires C))` (= `⊤' U atom (Fires C)`) is bisim-stable too.
fair-F-stable : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
              → BisimStable {R = R} (F_ (atom (Fires C)))
fair-F-stable = bs-U bs-⊤ fires-stable

------------------------------------------------------------
-- §3  Fairness on the WTrace layer (mirror of F1's `Fair`).
--
-- The ≈DR transport lives on WTrace, so this is where the transferable
-- fairness fact is stated.  It reuses F1's `WEnabled`/`Fires` unchanged and
-- swaps only the trace-observation combinators for WTrace's.
------------------------------------------------------------

-- `C` is (weakly) enabled at the k-th suffix of a WTrace.
enabledAtᵂ : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
           → (Event → Set ℓc) → W.WTrace R t → ℕ
           → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓc)
enabledAtᵂ C tr k = WEnabled C (frameState (W.frameOf (W.drop k tr)))

-- Weak fairness on the WTrace layer: from every suffix, continuous weak
-- enabledness of `C` forces `C` to eventually fire (`⟦ F ... ⟧ᵂ`).
Fairᵂ : ∀ {ℓr ℓc} {R : Set ℓr} {t : PTree E I R}
      → (Event → Set ℓc) → W.WTrace R t
      → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓc)
Fairᵂ C tr = ∀ n → (∀ k → enabledAtᵂ C tr (n + k))
           → W.⟦ F_ (atom (Fires C)) ⟧ᵂ (W.drop n tr)

------------------------------------------------------------
-- §4  Transfer of fairness along a `WTraceSim` correspondence.
------------------------------------------------------------

-- Per-suffix weak-enabledness transfers backward along a `WTraceSim`
-- (frames correspond ⇒ states ≈DR ⇒ `wenabled-invariant`).  This is the
-- granular fact the `Fairᵂ` antecedent needs (M5-consumable on its own).
enabledAtᵂ-transfer : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
                        {t₁ t₂ : PTree E I R}
                        {tr₁ : W.WTrace R t₁} {tr₂ : W.WTrace R t₂}
                    → WTraceSim tr₁ tr₂ → (k : ℕ)
                    → enabledAtᵂ C tr₂ k → enabledAtᵂ C tr₁ k
enabledAtᵂ-transfer sim k e₂ =
  wenabled-invariant (drbisim-sym (framestate-≈DR (heads (drop-WTraceSim k sim)))) e₂

-- `Fairᵂ` transports forward along a `WTraceSim`: pull the enabledness
-- antecedent back to tr₁ (enabledAtᵂ-transfer), run `Fairᵂ` on tr₁, then push
-- the `F`-consequent forward with `⟦⟧ᵂ-transport` (F is bisim-stable).  This
-- is the campaign direction (tr₁ = concrete-embedded, tr₂ = abstract).
Fairᵂ-transfer : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
                   {t₁ t₂ : PTree E I R}
                   {tr₁ : W.WTrace R t₁} {tr₂ : W.WTrace R t₂}
               → WTraceSim tr₁ tr₂ → Fairᵂ C tr₁ → Fairᵂ C tr₂
Fairᵂ-transfer {C = C} sim fair₁ n cont₂ =
  ⟦⟧ᵂ-transport (fair-F-stable {C = C}) (drop-WTraceSim n sim)
    (fair₁ n (λ k → enabledAtᵂ-transfer sim (n + k) (cont₂ k)))

-- The reverse direction (via `WTraceSim`-symmetry), for completeness.
Fairᵂ-transfer← : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
                    {t₁ t₂ : PTree E I R}
                    {tr₁ : W.WTrace R t₁} {tr₂ : W.WTrace R t₂}
                → WTraceSim tr₁ tr₂ → Fairᵂ C tr₂ → Fairᵂ C tr₁
Fairᵂ-transfer← sim = Fairᵂ-transfer (WTraceSim-sym sim)

------------------------------------------------------------
-- §5  The M0-bridge extension: Trace-level `Fair` ↪ WTrace-level `Fairᵂ`.
--
-- `BlockLiveness⁺ᶠ` states `Fair C tr` on a coinductive `Trace`; the transport
-- consumes `Fairᵂ` on a `WTrace`.  M0's embedding preserves the observed frame
-- at every suffix (`frame-agree`, and `drop` commutes definitionally through
-- the embedding), so weak-enabledness matches suffix-wise, and `◇ᵗ`/`F` cross
-- via M0's `drop-sem-bwd` (spike-report §Q2(b): `frame-agree` + definitional
-- `drop`).
------------------------------------------------------------

-- The embedded WTrace exposes, at every drop index, the SAME frame as the
-- source Trace.  Recursion on `n` (base = M0's `frame-agree`); the `step`/
-- terminator tails commute definitionally through `Trace↪WTrace`, exactly as
-- in M0's `drop-sem-*`.
frame-drop-agree : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                     (n : ℕ) (tr : T.Trace R t)
                 → W.frameOf (W.drop n (Trace↪WTrace tr)) ≡ T.frameOf (T.drop n tr)
frame-drop-agree zero    tr             = frame-agree tr
frame-drop-agree (suc n) (T.step x tr)  = frame-drop-agree n (T.force tr)
frame-drop-agree (suc n) (T.done eq)    = frame-drop-agree n (T.done eq)
frame-drop-agree (suc n) (T.stuck st)   = frame-drop-agree n (T.stuck st)
frame-drop-agree (suc n) (T.div dv)     = frame-drop-agree n (T.div dv)

-- Weak-enabledness at suffix `k` agrees between a Trace and its embedding
-- (same suffix state, via `frame-drop-agree`) — carried across as a `subst`
-- on the `WEnabled` state argument (no corecursion here).
enabledAt⇐enabledAtᵂ : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
                         {t : PTree E I R} (k : ℕ) (tr : T.Trace R t)
                     → enabledAtᵂ C (Trace↪WTrace tr) k → enabledAt C tr k
enabledAt⇐enabledAtᵂ {C = C} k tr e =
  subst (WEnabled C) (cong frameState (frame-drop-agree k tr)) e

-- A Trace-level `Fair C` gives `Fairᵂ C` on its embedded WTrace: convert the
-- WTrace enabledness antecedent to the Trace one, run `Fair`, turn the
-- resulting `◇ᵗ` into `⟦ F ⟧` (`◇ᵗ⇒F`) and cross to `⟦ F ⟧ᵂ` via M0's
-- `drop-sem-bwd`.  This is the hypothesis direction the M5 endgame needs.
Fair→Fairᵂ : ∀ {ℓr ℓc} {R : Set ℓr} {C : Event → Set ℓc}
               {t : PTree E I R} (tr : T.Trace R t)
           → Fair C tr → Fairᵂ C (Trace↪WTrace tr)
Fair→Fairᵂ {C = C} tr fair n cont =
  drop-sem-bwd (F_ (atom (Fires C))) n tr
    (◇ᵗ⇒F {φ = atom (Fires C)}
      (fair n (λ k → enabledAt⇐enabledAtᵂ (n + k) tr (cont k))))
