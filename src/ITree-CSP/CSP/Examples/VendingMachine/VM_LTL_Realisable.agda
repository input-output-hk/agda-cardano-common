{-# OPTIONS --guardedness #-}

-- Discharges `Realisableᴿ VM_body_impl` (from `Semantics.LTL.WBisimInvariantR`)
-- for the vending-machine body process, and derives the resulting
-- DR-weak-bisim LTL invariance corollary. `VM_body_impl` is τ-free at every
-- ↠-reachable state (VM_body_impl → body2 → Skip → deadlock), so the
-- Realisableᴿ record discharges directly from that τ-freeness.

module CSP.Examples.VendingMachine.VM_LTL_Realisable where

open import Level using () renaming (zero to lzero)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- The VM model: VM_body_impl and its component states.
open import CSP.Examples.VendingMachine.VendingMachine

import CSP.Operators {E = VM} as CSPOps
open CSPOps VM-AnyTypes-≟

open import Semantics.LTS {E = VM} {I = ExtI VM}
  using (_─[_]─►_; τ; ev; Event√)

-- The VM's existing τ-refutations and visible-step inversions (body2, Skip,
-- deadlock states + their pinned successors).
open import CSP.Examples.VendingMachine.VendingMachine_LTL_Sat
  using ( body2
        ; VM_body_impl-no-τ; body2-no-τ; Skip-no-τ; deadlock-no-τ
        ; VM_body_impl-ev-inv′; body2-ev-inv′; Skip-ev-inv′; deadlock-no-ev
        )

open import Semantics.LTL.Convergence {E = VM} {I = ExtI VM}
  using (_↠_; ↠-refl; ↠-τ; ↠-ev; cvg)
open import Semantics.LTL.WBisimInvariantR {E = VM} {I = ExtI VM}
  using (Realisableᴿ; τprogᴿ; convᴿ; ⊨-DRWB-invariantᴿ→)
open import Semantics.DRBisim {E = VM} {I = ExtI VM} using (_≈DR_)
open import Semantics.LTL.FrameSim {E = VM} {I = ExtI VM} using (BisimStable)
open import Semantics.LTL.WTrace   {E = VM} {I = ExtI VM} using (_⊨ᵂ_)
open import Semantics.LTL.Traces_Based {E = VM} {I = ExtI VM} using (LTLᵗ)

-- The finitely many states ↠-reachable from VM_body_impl: itself, the
-- post-coin external choice `body2`, the post-drink `Skip`, and the
-- post-√ `deadlock`.
BodyState : PTree VM (ExtI VM) (⊤ {lzero}) → Set₁
BodyState s = (s ≡ VM_body_impl) ⊎ (s ≡ body2) ⊎ (s ≡ Skip {lzero}) ⊎ (s ≡ deadlock {R = ⊤ {lzero}})

body-start : BodyState VM_body_impl
body-start = inj₁ refl

body-τfree : ∀ {s} → BodyState s → ∀ {t′} → s ─[ τ ]─► t′ → ⊥
body-τfree (inj₁ refl)                   sτ = VM_body_impl-no-τ sτ
body-τfree (inj₂ (inj₁ refl))            sτ = body2-no-τ sτ
body-τfree (inj₂ (inj₂ (inj₁ refl)))     sτ = Skip-no-τ sτ
body-τfree (inj₂ (inj₂ (inj₂ refl)))     sτ = deadlock-no-τ sτ

body-step-cl : ∀ {s s′} {l : Event√ (⊤ {lzero})} → BodyState s → s ─[ ev l ]─► s′ → BodyState s′
body-step-cl (inj₁ refl) st with VM_body_impl-ev-inv′ st
... | _ , refl = inj₂ (inj₁ refl)
body-step-cl (inj₂ (inj₁ refl)) st with body2-ev-inv′ st
... | _ , refl = inj₂ (inj₂ (inj₁ refl))
body-step-cl (inj₂ (inj₂ (inj₁ refl))) st with Skip-ev-inv′ st
... | _ , refl = inj₂ (inj₂ (inj₂ refl))
body-step-cl (inj₂ (inj₂ (inj₂ refl))) st = ⊥-elim (deadlock-no-ev st)

body-reach-τfree : ∀ {s} → VM_body_impl ↠ s → ∀ {t′} → s ─[ τ ]─► t′ → ⊥
body-reach-τfree reach = go body-start reach
  where
    go : ∀ {s} → BodyState s → ∀ {s′} → s ↠ s′ → ∀ {t′} → s′ ─[ τ ]─► t′ → ⊥
    go bs ↠-refl          sτ = body-τfree bs sτ
    go bs (↠-τ  st rest)  sτ = ⊥-elim (body-τfree bs st)
    go bs (↠-ev st rest)  sτ = go (body-step-cl bs st) rest sτ

VM_body_Realisableᴿ : Realisableᴿ VM_body_impl
τprogᴿ VM_body_Realisableᴿ reach     = inj₂ (body-reach-τfree reach)
convᴿ  VM_body_Realisableᴿ reach _ _ = cvg (λ sτ → ⊥-elim (body-reach-τfree reach sτ))

vm-body-⊨ᵂ-invariant→ :
    ∀ {ℓa} {t₂ : PTree VM (ExtI VM) ⊤} {φ : LTLᵗ ℓa ⊤}
  → VM_body_impl ≈DR t₂ → BisimStable φ → VM_body_impl ⊨ᵂ φ → t₂ ⊨ᵂ φ
vm-body-⊨ᵂ-invariant→ b bs sat = ⊨-DRWB-invariantᴿ→ VM_body_Realisableᴿ b bs sat
