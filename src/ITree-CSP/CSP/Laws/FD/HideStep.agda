{-# OPTIONS --guardedness #-}

-- Hide-step (T3.5 / U5.5 and the simple half of T3.6 / U5.6):  how hiding meets a prefix.
--
-- Two faces of  (?x:A → P) ∖ X, split on whether the offered events meet X:
--
--   • A ∩ X = ∅  (no offered event hidden):  (?x:A→P) ∖ X  ≈FD  ?x:A→(P x ∖ X).
--     Every event stays VISIBLE and the continuation hides on; a NON-recursive STRONG
--     bisimulation (matched targets coincide ⇒ sbisim-refl, like □-step / hide-dist).
--
--   • a ∈ X  (the single hidden event, T3.5):  (a→P) ∖ X  ≈FD  P ∖ X.
--     The hidden event becomes a τ — a τ-SLIDE.  This is the first §6 law that is
--     genuinely WEAK (τ-absorbing), so it is proved as a hand-built ≈DR witness:
--     the left's only move is one τ to `P ∖ X`, which the right matches by standing
--     still (τ̂ = τ*, zero steps); divergence transfers straight through that single τ.
--     We state it for the no-binding prefix `e ⟶₀ P` with `A` inhabited (a witness
--     `a₀`) and every event of (A,e) hidden — exactly TPC's single-event `a → P`.

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.HideStep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim {E = E} {I = ExtI E}
  using (DRbisim; _≈DR_; Diverges; drbisim-refl)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-keep; Hide-hidden; Hide-τ-elim; HideτR; hτP; hτH
        ; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLaws E-≟ using (Prefix-cont-just)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- shared prefix-step facts
-------------------------------------------------------------------------------------

-- a prefix is τ-free (its τ-branch is ∅t).
prefix-no-τ : {A : Set ℓ} {e : E A} {P : A → PTree E (ExtI E) R} {P′ : PTree E (ExtI E) R}
            → (Prefix e P) ─[ τ ]─► P′ → ⊥
prefix-no-τ (sSil ())
prefix-no-τ (sTau refl ())

-------------------------------------------------------------------------------------
-- T3.6 simple half:  A ∩ X = ∅  ⇒  (?x:A→P) ∖ X  ≈FD  ?x:A→(P x ∖ X)   (STRONG)
-------------------------------------------------------------------------------------

module _ {A : Set ℓ} (e : E A) (P : A → PTree E (ExtI E) R) (X : EventSet)
         (notmem : (x : A) → ¬ EventSet.mem X (A , e) x) where

  private
    LHS : PTree E (ExtI E) R
    LHS = (Prefix e P) ∖ X
    RHS : PTree E (ExtI E) R
    RHS = Prefix e (λ x → P x ∖ X)

  out-fwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
             → LHS ─[ ev l ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ] (RHS ─[ ev l ]─► M′) × (M ∼ M′)
  out-fwd-ev step with Hide-ev-elim X (Prefix e P) step
  ... | heV {B} {e′} {a} P′ ¬mem (sVis {at = at} refl br) with E-≟ (A , e) at
  ...   | no  _    = case br of λ ()
  ...   | yes refl with br
  ...                 | refl =
              (P a ∖ X)
            , sVis {at = A , e} {a = a} refl (Prefix-cont-just e (λ y → P y ∖ X) a)
            , sbisim-refl (P a ∖ X)
  out-fwd-ev step | he√ ()

  out-bwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
             → RHS ─[ ev l ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ] (LHS ─[ ev l ]─► M′) × (M ∼ M′)
  out-bwd-ev (sRet ())
  out-bwd-ev (sVis {at = at} {a = x} refl br) with E-≟ (A , e) at
  ... | no  _    = case br of λ ()
  ... | yes refl with br
  ...               | refl =
          (P x ∖ X)
        , Hide-keep X (Prefix e P) (notmem x)
            (sVis {at = A , e} {a = x} refl (Prefix-cont-just e P x))
        , sbisim-refl (P x ∖ X)

  out-fwd-tau : {M : PTree E (ExtI E) R}
              → LHS ─[ τ ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ] (RHS ─[ τ ]─► M′) × (M ∼ M′)
  out-fwd-tau step with Hide-τ-elim X (Prefix e P) step
  ... | hτP P′ pstep teq = ⊥-elim (prefix-no-τ pstep)
  ... | hτH {B} {e′} {a} P′ mem (sVis {at = at} refl br) teq with E-≟ (A , e) at
  ...   | no  _    = case br of λ ()
  ...   | yes refl = ⊥-elim (notmem a mem)

  out-bwd-tau : {M : PTree E (ExtI E) R}
              → RHS ─[ τ ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ] (LHS ─[ τ ]─► M′) × (M ∼ M′)
  out-bwd-tau step = ⊥-elim (prefix-no-τ step)

  hide-prefix-out-∼ : LHS ∼ RHS
  hide-prefix-out-∼ .Sbisim.fwd .SSimF.on-ev  = out-fwd-ev
  hide-prefix-out-∼ .Sbisim.fwd .SSimF.on-tau = out-fwd-tau
  hide-prefix-out-∼ .Sbisim.bwd .SSimF.on-ev  = out-bwd-ev
  hide-prefix-out-∼ .Sbisim.bwd .SSimF.on-tau = out-bwd-tau

  -- (?x:A→P) ∖ X  ≈FD  ?x:A→(P x ∖ X)      (when A ∩ X = ∅)
  hide-prefix-out-FD : LHS ≈FD RHS
  hide-prefix-out-FD = drbisim→≈FD (sbisim→drbisim hide-prefix-out-∼)

-------------------------------------------------------------------------------------
-- T3.5:  a ∈ X  ⇒  (a→P) ∖ X  ≈FD  P ∖ X        (WEAK / DR — a τ-slide)
-------------------------------------------------------------------------------------

module _ {A : Set ℓ} (e : E A) (P : PTree E (ExtI E) R) (X : EventSet)
         (a₀ : A) (allmem : (x : A) → EventSet.mem X (A , e) x) where

  private
    HID : PTree E (ExtI E) R
    HID = (Prefix₀ e P) ∖ X

    -- the prefix fires its own event at any value, landing in the (constant) P
    pfx-ev : (x : A) → (Prefix₀ e P) ─[ ev (evl (evLabel A e x)) ]─► P
    pfx-ev x = sVis {at = A , e} {a = x} refl (Prefix-cont-just e (λ _ → P) x)

    -- the τ-slide: the hidden event becomes a τ to P ∖ X
    slide : HID ─[ τ ]─► (P ∖ X)
    slide = Hide-hidden X (Prefix₀ e P) (allmem a₀) (pfx-ev a₀)

  hidden-fwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
                → HID ─[ ev l ]─► M
                → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ X) ═[ ev l ]═► M′) × DRbisim R M M′
  hidden-fwd-ev step with Hide-ev-elim X (Prefix₀ e P) step
  ... | heV {B} {e′} {a} P′ ¬mem (sVis {at = at} refl br) with E-≟ (A , e) at
  ...   | no  _    = case br of λ ()
  ...   | yes refl = ⊥-elim (¬mem (allmem a))
  hidden-fwd-ev step | he√ ()

  hidden-fwd-tau : {M : PTree E (ExtI E) R}
                 → HID ─[ τ ]─► M
                 → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ X) ═[ τ ]═► M′) × DRbisim R M M′
  hidden-fwd-tau step with Hide-τ-elim X (Prefix₀ e P) step
  ... | hτP P′ pstep teq = ⊥-elim (prefix-no-τ pstep)
  ... | hτH {B} {e′} {a} P′ mem (sVis {at = at} refl br) teq with E-≟ (A , e) at
  ...   | no  _    = case br of λ ()
  ...   | yes refl with br
  ...                 | refl =
          (P ∖ X) , wτ τ*-refl
          , subst (λ z → DRbisim R z (P ∖ X)) (sym teq) (drbisim-refl (P ∖ X))

  hidden-bwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
                → (P ∖ X) ─[ ev l ]─► M
                → Σ[ M′ ∈ PTree E (ExtI E) R ] (HID ═[ ev l ]═► M′) × DRbisim R M M′
  hidden-bwd-ev {M = M} step =
    M , wev (τ*-step slide τ*-refl) step τ*-refl , drbisim-refl M

  hidden-bwd-tau : {M : PTree E (ExtI E) R}
                 → (P ∖ X) ─[ τ ]─► M
                 → Σ[ M′ ∈ PTree E (ExtI E) R ] (HID ═[ τ ]═► M′) × DRbisim R M M′
  hidden-bwd-tau {M = M} step =
    M , wτ (τ*-step slide (τ*-step step τ*-refl)) , drbisim-refl M

  hidden-div→ : Diverges HID → Diverges (P ∖ X)
  hidden-div→ d with Hide-τ-elim X (Prefix₀ e P) (d .Diverges.step)
  ... | hτP P′ pstep teq = ⊥-elim (prefix-no-τ pstep)
  ... | hτH {B} {e′} {a} P′ mem (sVis {at = at} refl br) teq with E-≟ (A , e) at
  ...   | no  _    = case br of λ ()
  ...   | yes refl with br
  ...                 | refl = subst Diverges teq (d .Diverges.rest)

  hidden-div← : Diverges (P ∖ X) → Diverges HID
  hidden-div← dR = record { step = slide ; rest = dR }

  hide-prefix-hidden-DR : DRbisim R HID (P ∖ X)
  hide-prefix-hidden-DR .DRbisim.fwd .WSimF.on-ev  = hidden-fwd-ev
  hide-prefix-hidden-DR .DRbisim.fwd .WSimF.on-tau = hidden-fwd-tau
  hide-prefix-hidden-DR .DRbisim.bwd .WSimF.on-ev  = hidden-bwd-ev
  hide-prefix-hidden-DR .DRbisim.bwd .WSimF.on-tau = hidden-bwd-tau
  hide-prefix-hidden-DR .DRbisim.div→ = hidden-div→
  hide-prefix-hidden-DR .DRbisim.div← = hidden-div←

  -- (a→P) ∖ X  ≈FD  P ∖ X      (when the prefixed event a ∈ X)
  hide-prefix-hidden-FD : HID ≈FD (P ∖ X)
  hide-prefix-hidden-FD = drbisim→≈FD hide-prefix-hidden-DR
