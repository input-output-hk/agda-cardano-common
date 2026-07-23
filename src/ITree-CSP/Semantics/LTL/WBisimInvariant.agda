{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; lift) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym)

open import Process_Trees hiding (div)

module Semantics.LTL.WBisimInvariant
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; wτ; wev; WSimF)
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}
  using (DRbisim; _≈DR_; drbisim-refl; drbisim-sym; dr-τ*-sim; dr-wev-sim; Diverges)
open import Semantics.Deadlock  {ℓ} {ℓe} {ℓi} {E} {I} using (IsStuck)
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using (LTLᵗ)
open import Semantics.LTL.FrameSim     {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.LTL.Convergence  {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.LTL.WTrace       {ℓ} {ℓe} {ℓi} {E} {I} hiding (stuck)

√-inv : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} {r : R}
      → t ─[ ev (√ r) ]─► t′ → PTree.force t ≡ ret r
√-inv (sRet eq) = eq

stuck-τ*-refl : ∀ {ℓr} {R : Set ℓr} {u p : PTree E I R}
              → IsStuck u → u ─[τ*]─► p → p ≡ u
stuck-τ*-refl stuck τ*-refl        = refl
stuck-τ*-refl stuck (τ*-step uτ _) = ⊥-elim (stuck uτ)

mkStuck : ∀ {ℓr} {R : Set ℓr} {s : PTree E I R}
        → (∀ {t′} → s ─[ τ ]─► t′ → ⊥)
        → (∀ {l t′} → s ─[ ev l ]─► t′ → ⊥)
        → IsStuck s
mkStuck nτ nv {ev l} st = nv st
mkStuck nτ nv {τ}    st = nτ st

bisim-to-stuck-no-vis : ∀ {ℓr} {R : Set ℓr} {u s : PTree E I R}
  → DRbisim R u s → IsStuck u → ∀ {l t′} → s ─[ ev l ]─► t′ → ⊥
bisim-to-stuck-no-vis b stuck sev with b .DRbisim.bwd .WSimF.on-ev sev
... | _ , wev uτ* uev _ , _ =
      stuck (subst (λ z → z ─[ _ ]─► _) (stuck-τ*-refl stuck uτ*) uev)

ret-ret-bisim : ∀ {ℓr} {R : Set ℓr} {x y : PTree E I R} {r : R}
              → PTree.force x ≡ ret r → PTree.force y ≡ ret r → DRbisim R x y
ret-ret-bisim {R = R} {x = x} {y} {r} fx fy = go fx fy
  where
    -- a ret-node has no τ-step
    ret-no-τ : ∀ {z t′ : PTree E I R} {q : R} → PTree.force z ≡ ret q → z ─[ τ ]─► t′ → ⊥
    ret-no-τ fz (sSil eq)   with trans (sym fz) eq
    ... | ()
    ret-no-τ fz (sTau eq _) with trans (sym fz) eq
    ... | ()
    ret-no-div : ∀ {z : PTree E I R} {q : R} → PTree.force z ≡ ret q → Diverges z → ⊥
    ret-no-div fz d = ret-no-τ fz (d .Diverges.step)
    -- a ret-node has no visible (`evl`) step
    ret-no-evl : ∀ {z t′ : PTree E I R} {q : R} {e}
               → PTree.force z ≡ ret q → z ─[ ev (evl e) ]─► t′ → ⊥
    ret-no-evl fz (sVis eq _) with trans (sym fz) eq
    ... | ()
    go : ∀ {a b : PTree E I R} → PTree.force a ≡ ret r → PTree.force b ≡ ret r → DRbisim R a b
    go {a} {b} fa fb .DRbisim.fwd .WSimF.on-ev (sRet eq) with trans (sym fa) eq
    ... | refl =
      deadlock , wev τ*-refl (sRet fb) τ*-refl , drbisim-refl deadlock
    go {a} {b} fa fb .DRbisim.fwd .WSimF.on-ev {l = evl e} sev = ⊥-elim (ret-no-evl fa sev)
    go {a} {b} fa fb .DRbisim.fwd .WSimF.on-tau tτ = ⊥-elim (ret-no-τ fa tτ)
    go {a} {b} fa fb .DRbisim.bwd .WSimF.on-ev (sRet eq) with trans (sym fb) eq
    ... | refl =
      deadlock , wev τ*-refl (sRet fa) τ*-refl , drbisim-refl deadlock
    go {a} {b} fa fb .DRbisim.bwd .WSimF.on-ev {l = evl e} sev = ⊥-elim (ret-no-evl fb sev)
    go {a} {b} fa fb .DRbisim.bwd .WSimF.on-tau tτ = ⊥-elim (ret-no-τ fb tτ)
    go fa fb .DRbisim.div→ d = ⊥-elim (ret-no-div fa d)
    go fa fb .DRbisim.div← d = ⊥-elim (ret-no-div fb d)

ret-reach-preserved :
    ∀ {ℓr} {R : Set ℓr} {u s : PTree E I R} {r : R}
  → DRbisim R u s → PTree.force u ≡ ret r
  → Σ[ p ∈ PTree E I R ] Σ[ q ∈ PTree E I R ]
      ((s ─[τ*]─► p) × (p ─[ ev (√ r) ]─► q) × (PTree.force p ≡ ret r) × DRbisim R u p)
ret-reach-preserved b fu with b .DRbisim.fwd .WSimF.on-ev (sRet fu)
... | _ , wev sτ* pev _ , _ =
      _ , _ , sτ* , pev , √-inv pev , ret-ret-bisim fu (√-inv pev)

stuck-reach-preserved :
    ∀ {ℓr} {R : Set ℓr}
  → (τdec : ∀ (t : PTree E I R) → τ-progress t)
  → ∀ {u s : PTree E I R}
  → DRbisim R u s → IsStuck u → Converges s
  → Σ[ s′ ∈ PTree E I R ] ((s ─[τ*]─► s′) × IsStuck s′ × DRbisim R u s′)
stuck-reach-preserved τdec {u} {s} b stuck (cvg cvgf) with τdec s
... | inj₂ noτ = s , τ*-refl , mkStuck noτ (bisim-to-stuck-no-vis b stuck) , b
... | inj₁ (s′ , sτ) with b .DRbisim.bwd .WSimF.on-tau sτ
...   | _ , wτ uτ* , s′≈u′′
        with stuck-reach-preserved τdec
               (drbisim-sym (subst (DRbisim _ s′) (stuck-τ*-refl stuck uτ*) s′≈u′′))
               stuck (cvgf sτ)
...       | s′′ , s′↠s′′ , st′′ , u≈s′′ = s′′ , τ*-step sτ s′↠s′′ , st′′ , u≈s′′

record WTraceSim {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                 (tr₁ : WTrace R t₁) (tr₂ : WTrace R t₂)
               : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    heads : FrameSim (frameOf tr₁) (frameOf tr₂)
    tails : WTraceSim (tail tr₁) (tail tr₂)

open WTraceSim public

WTraceSim-sym : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                  {tr₁ : WTrace R t₁} {tr₂ : WTrace R t₂}
              → WTraceSim tr₁ tr₂ → WTraceSim tr₂ tr₁
heads (WTraceSim-sym sim) = FrameSim-sym (heads sim)
tails (WTraceSim-sym sim) = WTraceSim-sym (tails sim)

drop-WTraceSim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                   {tr₁ : WTrace R t₁} {tr₂ : WTrace R t₂}
                 → (n : ℕ) → WTraceSim tr₁ tr₂
                 → WTraceSim (drop n tr₁) (drop n tr₂)
drop-WTraceSim zero    sim = sim
drop-WTraceSim (suc n) sim = drop-WTraceSim n (tails sim)

⟦⟧ᵂ-transport : ∀ {ℓr ℓa} {R : Set ℓr} {t₁ t₂ : PTree E I R}
                  {tr₁ : WTrace R t₁} {tr₂ : WTrace R t₂} {φ : LTLᵗ ℓa R}
              → BisimStable φ → WTraceSim tr₁ tr₂ → ⟦ φ ⟧ᵂ tr₁ → ⟦ φ ⟧ᵂ tr₂
⟦⟧ᵂ-transport bs-⊤            sim _              = lift tt
⟦⟧ᵂ-transport (bs-atom stab)  sim h              = stab (heads sim) h
⟦⟧ᵂ-transport (bs-¬ bsφ)      sim h              = λ q₂ → h (⟦⟧ᵂ-transport bsφ (WTraceSim-sym sim) q₂)
⟦⟧ᵂ-transport (bs-∧ bsφ bsψ)  sim (hφ , hψ)      = ⟦⟧ᵂ-transport bsφ sim hφ , ⟦⟧ᵂ-transport bsψ sim hψ
⟦⟧ᵂ-transport (bs-X bsφ)      sim h              = ⟦⟧ᵂ-transport bsφ (tails sim) h
⟦⟧ᵂ-transport (bs-U bsφ bsψ)  sim (n , qψ , bef) =
  n , ⟦⟧ᵂ-transport bsψ (drop-WTraceSim n sim) qψ
    , λ m m<n → ⟦⟧ᵂ-transport bsφ (drop-WTraceSim m sim) (bef m m<n)

-- ─── transport: every weak trace of t₁ has a ≈DR-corresponding weak trace of t₂ ───

-- stuttering self-correspondence for a terminator WTrace paired with any
-- WTrace whose frame corresponds and which is itself a terminator.
term-sim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R}
             (tr₁ : WTrace R t₁) (tr₂ : WTrace R t₂)
           → IsTermᵂ tr₁ → IsTermᵂ tr₂
           → FrameSim (frameOf tr₁) (frameOf tr₂)
           → WTraceSim tr₁ tr₂
-- terminator/terminator pairs: `tail tr = tr` definitionally for both traces, so the
-- corecursive `tails` self-loop is guarded without any `rewrite`. The `step` cases are
-- impossible (`IsTermᵂ (step _ _) = ⊥`), discharged by the term witnesses.
heads (term-sim (done _ _)          (done _ _)          te₁ te₂ fs) = fs
heads (term-sim (done _ _)          (WTrace.stuck _ _)  te₁ te₂ fs) = fs
heads (term-sim (done _ _)          (div _)             te₁ te₂ fs) = fs
heads (term-sim (WTrace.stuck _ _)  (done _ _)          te₁ te₂ fs) = fs
heads (term-sim (WTrace.stuck _ _)  (WTrace.stuck _ _)  te₁ te₂ fs) = fs
heads (term-sim (WTrace.stuck _ _)  (div _)             te₁ te₂ fs) = fs
heads (term-sim (div _)             (done _ _)          te₁ te₂ fs) = fs
heads (term-sim (div _)             (WTrace.stuck _ _)  te₁ te₂ fs) = fs
heads (term-sim (div _)             (div _)             te₁ te₂ fs) = fs
heads (term-sim (step _ _)          _                   ()  te₂ fs)
heads (term-sim _                   (step _ _)          te₁ ()  fs)
tails (term-sim tr₁@(done _ _)         tr₂@(done _ _)         te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(done _ _)         tr₂@(WTrace.stuck _ _) te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(done _ _)         tr₂@(div _)            te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(WTrace.stuck _ _) tr₂@(done _ _)         te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(WTrace.stuck _ _) tr₂@(WTrace.stuck _ _) te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(WTrace.stuck _ _) tr₂@(div _)            te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(div _)            tr₂@(done _ _)         te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(div _)            tr₂@(WTrace.stuck _ _) te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim tr₁@(div _)            tr₂@(div _)            te₁ te₂ fs) = term-sim tr₁ tr₂ te₁ te₂ fs
tails (term-sim (step _ _)          _                   ()  te₂ fs)
tails (term-sim _                   (step _ _)          te₁ ()  fs)

-- Two mutually-corecursive producers, each guarded in its own coinductive type:
--   `wt`     builds the transported witness trace of t₂ (coinductive via `∞wt`),
--   `wt-sim` builds the WTraceSim between the original trace and that witness.
-- The `step` case corecurses under `WTrace.step`/`∞WTrace.force` (for `wt`) and under
-- `WTraceSim.tails` (for `wt-sim`); both perform the same `dr-wev-sim` `with`, so their
-- reducts agree definitionally and `wt-sim`'s `tails` typechecks against `wt`'s output.
wt     : ∀ {ℓr} {R : Set ℓr} → Realisable R
       → ∀ {t₁ t₂ : PTree E I R} → t₁ ≈DR t₂
       → WTrace R t₁ → WTrace R t₂
∞wt    : ∀ {ℓr} {R : Set ℓr} → Realisable R
       → ∀ {t₁ t₂ : PTree E I R} → t₁ ≈DR t₂
       → WTrace R t₁ → ∞WTrace R t₂
wt-sim : ∀ {ℓr} {R : Set ℓr} → (real : Realisable R)
       → ∀ {t₁ t₂ : PTree E I R} (b : t₁ ≈DR t₂)
       → (tr₁ : WTrace R t₁) → WTraceSim tr₁ (wt real b tr₁)

wt real b (div dv)          = div (b .DRbisim.div→ dv)
wt real b (done p eq) with dr-τ*-sim p b
... | S , t₂↠S , u≈S with ret-reach-preserved u≈S eq
...   | P , Q , S↠P , _ , fP , u≈P = done (τ*-trans t₂↠S S↠P) fP
wt real b (WTrace.stuck p st) with dr-τ*-sim p b
... | S , t₂↠S , u≈S
      with stuck-reach-preserved (τprog real) u≈S st (conv real u≈S st)
...   | S′ , S↠S′ , st′ , u≈S′ = WTrace.stuck (τ*-trans t₂↠S S↠S′) st′
wt real b (step {e = e} w rest) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = step w₂ (∞wt real b′ (force rest))

force (∞wt real b tr) = wt real b tr

wt-sim real b (div dv) =
  term-sim (div dv) (wt real b (div dv)) tt tt b
wt-sim real b (done p eq) with dr-τ*-sim p b
... | S , t₂↠S , u≈S with ret-reach-preserved u≈S eq
...   | P , Q , S↠P , _ , fP , u≈P =
        term-sim (done p eq) (done (τ*-trans t₂↠S S↠P) fP) tt tt (refl , u≈P)
wt-sim real b (WTrace.stuck p st) with dr-τ*-sim p b
... | S , t₂↠S , u≈S
      with stuck-reach-preserved (τprog real) u≈S st (conv real u≈S st)
...   | S′ , S↠S′ , st′ , u≈S′ =
        term-sim (WTrace.stuck p st) (WTrace.stuck (τ*-trans t₂↠S S↠S′) st′) tt tt u≈S′
heads (wt-sim real b (step {e = e} w rest)) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = refl , b
tails (wt-sim real b (step {e = e} w rest)) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = wt-sim real b′ (force rest)

transport : ∀ {ℓr} {R : Set ℓr} → Realisable R
          → ∀ {t₁ t₂ : PTree E I R} → t₁ ≈DR t₂
          → (tr₁ : WTrace R t₁) → Σ[ tr₂ ∈ WTrace R t₂ ] WTraceSim tr₁ tr₂
transport real b tr₁ = wt real b tr₁ , wt-sim real b tr₁

-- ─── ⊨-DRWB-invariant: headline theorem ───

⊨-DRWB-invariant→ : ∀ {ℓr ℓa} {R : Set ℓr} {t₁ t₂ : PTree E I R} {φ : LTLᵗ ℓa R}
                  → Realisable R → t₁ ≈DR t₂ → BisimStable φ → t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ
⊨-DRWB-invariant→ real b bs sat tr₂ with transport real (drbisim-sym b) tr₂
... | tr₁ , sim = ⟦⟧ᵂ-transport bs (WTraceSim-sym sim) (sat tr₁)

⊨-DRWB-invariant↔ : ∀ {ℓr ℓa} {R : Set ℓr} {t₁ t₂ : PTree E I R} {φ : LTLᵗ ℓa R}
                  → Realisable R → t₁ ≈DR t₂ → BisimStable φ
                  → (t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ) × (t₂ ⊨ᵂ φ → t₁ ⊨ᵂ φ)
⊨-DRWB-invariant↔ real b bs =
  (λ s₁ → ⊨-DRWB-invariant→ real b bs s₁) ,
  (λ s₂ → ⊨-DRWB-invariant→ real (drbisim-sym b) bs s₂)

-- ─── sanity: Stop = deadlock is stuck, has a canonical stuck-rooted WTrace, and
--            the invariance theorem holds trivially on the reflexive instance ───

private
  -- Stop = deadlock; its canonical weak trace is `stuck` reached in 0 τ-steps.
  Stop : ∀ {ℓr} {R : Set ℓr} → PTree E I R
  Stop = deadlock

  Stop-IsStuck : ∀ {ℓr} {R : Set ℓr} → IsStuck (Stop {R = R})
  Stop-IsStuck (sRet eq)      = case eq of λ ()
  Stop-IsStuck (sSil eq)      = case eq of λ ()
  Stop-IsStuck (sVis refl br) = case br of λ ()
  Stop-IsStuck (sTau refl br) = case br of λ ()

  StopWTrace : ∀ {ℓr} {R : Set ℓr} → WTrace R (Stop {R = R})
  StopWTrace = WTrace.stuck τ*-refl Stop-IsStuck

  -- Reflexivity instance of the theorem: any Realisable R and φ stable,
  -- Stop ⊨ᵂ φ ↔ Stop ⊨ᵂ φ (uses drbisim-refl).
  Stop-invariant : ∀ {ℓr ℓa} {R : Set ℓr} {φ : LTLᵗ ℓa R}
                 → Realisable R → BisimStable φ → Stop {R = R} ⊨ᵂ φ → Stop {R = R} ⊨ᵂ φ
  Stop-invariant real bs = ⊨-DRWB-invariant→ real (drbisim-refl Stop) bs
