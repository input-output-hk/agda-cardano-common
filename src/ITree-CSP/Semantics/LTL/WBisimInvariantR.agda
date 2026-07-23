{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees hiding (div)

module Semantics.LTL.WBisimInvariantR
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I}
  using (DRbisim; _≈DR_; drbisim-sym; dr-τ*-sim; dr-wev-sim)
open import Semantics.Deadlock  {ℓ} {ℓe} {ℓi} {E} {I} using (IsStuck)
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I} using (LTLᵗ)
open import Semantics.LTL.FrameSim     {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.LTL.Convergence  {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.LTL.WTrace       {ℓ} {ℓe} {ℓi} {E} {I} hiding (stuck)
open import Semantics.LTL.WBisimInvariant {ℓ} {ℓe} {ℓi} {E} {I}
  using ( mkStuck; bisim-to-stuck-no-vis; stuck-τ*-refl
        ; ret-reach-preserved; term-sim
        ; WTraceSim; heads; tails; WTraceSim-sym; drop-WTraceSim; ⟦⟧ᵂ-transport)

-- τ* and weak-visible runs embed into ↠ (τ+visible reachability).
τ*→↠ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} → t ─[τ*]─► t′ → t ↠ t′
τ*→↠ τ*-refl        = ↠-refl
τ*→↠ (τ*-step s rs) = ↠-τ s (τ*→↠ rs)

wev→↠ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} {l} → t ═[ ev l ]═► t′ → t ↠ t′
wev→↠ (wev a b c) = ↠-trans (τ*→↠ a) (↠-ev b (τ*→↠ c))

record Realisableᴿ {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  field
    τprogᴿ : ∀ {s : PTree E I R}   → t ↠ s → τ-progress s
    convᴿ  : ∀ {s u : PTree E I R} → t ↠ s → DRbisim R u s → IsStuck u → Converges s

open Realisableᴿ public

stuck-reach-preservedᴿ :
    ∀ {ℓr} {R : Set ℓr} {s : PTree E I R}
  → (τdec : ∀ {s′ : PTree E I R} → s ↠ s′ → τ-progress s′)
  → ∀ {u : PTree E I R}
  → DRbisim R u s → IsStuck u → Converges s
  → Σ[ s′ ∈ PTree E I R ] ((s ─[τ*]─► s′) × IsStuck s′ × DRbisim R u s′)
stuck-reach-preservedᴿ {s = s} τdec {u} b stuck (cvg cvgf) with τdec ↠-refl
... | inj₂ noτ = s , τ*-refl , mkStuck noτ (bisim-to-stuck-no-vis b stuck) , b
... | inj₁ (s′ , sτ) with b .DRbisim.bwd .WSimF.on-tau sτ
...   | _ , wτ uτ* , s′≈u′′
        with stuck-reach-preservedᴿ (λ s′↠ → τdec (↠-τ sτ s′↠))
               (drbisim-sym (subst (DRbisim _ s′) (stuck-τ*-refl stuck uτ*) s′≈u′′))
               stuck (cvgf sτ)
...       | s′′ , s′↠s′′ , st′′ , u≈s′′ = s′′ , τ*-step sτ s′↠s′′ , st′′ , u≈s′′

-- ─── reachability-threaded transport: faithful adaptation of `transport` from
--     Semantics.LTL.WBisimInvariant, threading a `root ↠ t₂` accumulator `r₂` ───

wtᴿ     : ∀ {ℓr} {R : Set ℓr} {root : PTree E I R} → Realisableᴿ root
        → ∀ {t₁ t₂ : PTree E I R} → root ↠ t₂ → t₁ ≈DR t₂ → WTrace R t₁ → WTrace R t₂
∞wtᴿ    : ∀ {ℓr} {R : Set ℓr} {root : PTree E I R} → Realisableᴿ root
        → ∀ {t₁ t₂ : PTree E I R} → root ↠ t₂ → t₁ ≈DR t₂ → WTrace R t₁ → ∞WTrace R t₂
wt-simᴿ : ∀ {ℓr} {R : Set ℓr} {root : PTree E I R} → (real : Realisableᴿ root)
        → ∀ {t₁ t₂ : PTree E I R} (r₂ : root ↠ t₂) (b : t₁ ≈DR t₂)
        → (tr₁ : WTrace R t₁) → WTraceSim tr₁ (wtᴿ real r₂ b tr₁)

wtᴿ real r₂ b (div dv)          = div (b .DRbisim.div→ dv)
wtᴿ real r₂ b (done p eq) with dr-τ*-sim p b
... | S , t₂↠S , u≈S with ret-reach-preserved u≈S eq
...   | P , Q , S↠P , _ , fP , u≈P = done (τ*-trans t₂↠S S↠P) fP
wtᴿ real r₂ b (WTrace.stuck p st) with dr-τ*-sim p b
... | S , t₂↠S , u≈S
      with stuck-reach-preservedᴿ (λ S↠s′ → τprogᴿ real (↠-trans (↠-trans r₂ (τ*→↠ t₂↠S)) S↠s′))
             u≈S st (convᴿ real (↠-trans r₂ (τ*→↠ t₂↠S)) u≈S st)
...   | S′ , S↠S′ , st′ , u≈S′ = WTrace.stuck (τ*-trans t₂↠S S↠S′) st′
wtᴿ real r₂ b (step {e = e} w rest) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = step w₂ (∞wtᴿ real (↠-trans r₂ (wev→↠ w₂)) b′ (force rest))

force (∞wtᴿ real r₂ b tr) = wtᴿ real r₂ b tr

wt-simᴿ real r₂ b (div dv) =
  term-sim (div dv) (wtᴿ real r₂ b (div dv)) tt tt b
wt-simᴿ real r₂ b (done p eq) with dr-τ*-sim p b
... | S , t₂↠S , u≈S with ret-reach-preserved u≈S eq
...   | P , Q , S↠P , _ , fP , u≈P =
        term-sim (done p eq) (done (τ*-trans t₂↠S S↠P) fP) tt tt (refl , u≈P)
wt-simᴿ real r₂ b (WTrace.stuck p st) with dr-τ*-sim p b
... | S , t₂↠S , u≈S
      with stuck-reach-preservedᴿ (λ S↠s′ → τprogᴿ real (↠-trans (↠-trans r₂ (τ*→↠ t₂↠S)) S↠s′))
             u≈S st (convᴿ real (↠-trans r₂ (τ*→↠ t₂↠S)) u≈S st)
...   | S′ , S↠S′ , st′ , u≈S′ =
        term-sim (WTrace.stuck p st) (WTrace.stuck (τ*-trans t₂↠S S↠S′) st′) tt tt u≈S′
heads (wt-simᴿ real r₂ b (step {e = e} w rest)) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = refl , b
tails (wt-simᴿ real r₂ b (step {e = e} w rest)) with dr-wev-sim w b
... | t₂′ , w₂ , b′ = wt-simᴿ real (↠-trans r₂ (wev→↠ w₂)) b′ (force rest)

transportᴿ : ∀ {ℓr} {R : Set ℓr} {root : PTree E I R} → Realisableᴿ root
           → ∀ {t₁ t₂ : PTree E I R} → root ↠ t₂ → t₁ ≈DR t₂
           → (tr₁ : WTrace R t₁) → Σ[ tr₂ ∈ WTrace R t₂ ] WTraceSim tr₁ tr₂
transportᴿ real r₂ b tr₁ = wtᴿ real r₂ b tr₁ , wt-simᴿ real r₂ b tr₁

-- ─── ⊨-DRWB-invariantᴿ: headline theorem (reachability-parametrised) ───

-- The transport back from a t₂-trace to a t₁-trace lands on the t₁-side, so it is
-- the reachability structure of `t₁` (the target of that transport) that is used;
-- hence the hypothesis is `Realisableᴿ t₁` (with the accumulator started at `↠-refl`).
⊨-DRWB-invariantᴿ→ : ∀ {ℓr ℓa} {R : Set ℓr} {t₁ t₂ : PTree E I R} {φ : LTLᵗ ℓa R}
                   → Realisableᴿ t₁ → t₁ ≈DR t₂ → BisimStable φ → t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ
⊨-DRWB-invariantᴿ→ real b bs sat tr₂ with transportᴿ real ↠-refl (drbisim-sym b) tr₂
... | tr₁ , sim = ⟦⟧ᵂ-transport bs (WTraceSim-sym sim) (sat tr₁)

⊨-DRWB-invariantᴿ↔ : ∀ {ℓr ℓa} {R : Set ℓr} {t₁ t₂ : PTree E I R} {φ : LTLᵗ ℓa R}
                   → Realisableᴿ t₁ → Realisableᴿ t₂ → t₁ ≈DR t₂ → BisimStable φ
                   → (t₁ ⊨ᵂ φ → t₂ ⊨ᵂ φ) × (t₂ ⊨ᵂ φ → t₁ ⊨ᵂ φ)
⊨-DRWB-invariantᴿ↔ real₁ real₂ b bs =
  (λ s₁ → ⊨-DRWB-invariantᴿ→ real₁ b bs s₁) ,
  (λ s₂ → ⊨-DRWB-invariantᴿ→ real₂ (drbisim-sym b) bs s₂)
