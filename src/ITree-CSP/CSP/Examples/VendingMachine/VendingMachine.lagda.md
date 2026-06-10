# Vending machine: modelling and verification

A worked example modelling a simple vending machine in CSP and verifying
properties about it via both **refinement** (`_⊑ᵀ_`, `_⊑FD_`) and **LTL**
(`_⊨_` over `LTLᵗ` from `ITree_Relations.LTL.Traces_Based`).

The implementation uses **external choice** (`□`) between tea and coffee;
the specification uses **internal choice** (`⊓`). They are trace-equivalent
but FD-related strictly in one direction — the canonical "external choice
refines internal choice" lesson.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.VendingMachine.VendingMachine where
```

## §1. Imports

```agda
open import Level using (Level; _⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes

open ITree

-- DecEq for the polymorphic unit type (Lift lzero ⊤₀), needed by _□_
instance
  DecEq-⊤poly : DecEq (⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §2. The event type

`coin`, `tea`, `coffee` — three nullary visible events.

```agda
data VM : Set → Set where
  coin   : VM ⊤
  tea    : VM ⊤
  coffee : VM ⊤
```

## §3. Decidable equality

```agda
VM-AnyTypes-≟ : (x y : AnyTypes VM) → Dec (x ≡ y)
VM-AnyTypes-≟ (_ , coin)   (_ , coin)   = yes refl
VM-AnyTypes-≟ (_ , tea)    (_ , tea)    = yes refl
VM-AnyTypes-≟ (_ , coffee) (_ , coffee) = yes refl
VM-AnyTypes-≟ (_ , coin)   (_ , tea)    = no λ ()
VM-AnyTypes-≟ (_ , coin)   (_ , coffee) = no λ ()
VM-AnyTypes-≟ (_ , tea)    (_ , coin)   = no λ ()
VM-AnyTypes-≟ (_ , tea)    (_ , coffee) = no λ ()
VM-AnyTypes-≟ (_ , coffee) (_ , coin)   = no λ ()
VM-AnyTypes-≟ (_ , coffee) (_ , tea)    = no λ ()

import CSP.Definitions.Operators {E = VM} as CSPOps
open CSPOps VM-AnyTypes-≟
import CSP.Definitions.Iterate {E = VM} as CSPIte
open CSPIte VM-AnyTypes-≟
```

## §4. Process definitions

The body of each iteration: `coin`, then either tea or coffee, then loop back.

```agda
VM_body_impl : ITree VM (ExtI VM) (⊤ {lzero})
VM_body_impl = coin ⟶₀ ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))

VM_body_spec : ITree VM (ExtI VM) (⊤ {lzero})
VM_body_spec = coin ⟶₀ ((tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip))

VM_impl : ITree VM (ExtI VM) ⊥
VM_impl = loop0 VM_body_impl

VM_spec : ITree VM (ExtI VM) ⊥
VM_spec = loop0 VM_body_spec
```

## §5. Verification

We now develop the verification, working at the **body level**
(`VM_body_impl` / `VM_body_spec`) where the proofs stay finite. Lifting
through `loop0` would require monotonicity laws for `>>=` and `loop0`
under `_⊑ᵀ_` / `_⊑FD_` that are currently stubs in
`CSP.Laws.FailuresDivergences`; we record that as future work.

```agda
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using () renaming (tt to tt₀)

open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open Failures
open import CSP.Laws.Traces VM-AnyTypes-≟
  using ( Prefix₀-trace; ExternalChoice-trace; InternalChoice-trace
        ; Prefix₀-trace-intro; IntChoice-trace-introL; IntChoice-trace-introR
        ; ExtChoice-trace-introL; ExtChoice-trace-introR)

import CSP.Laws.InternalChoice_FD as ICFD
open ICFD VM-AnyTypes-≟
  using (⊓-failures⊥-introL; ⊓-failures⊥-introR; ⊓-step-L; ⊓-step-R
        ; ⊓-failures-introL; ⊓-failures-introR)

import CSP.Laws.ExternalChoice_FD VM-AnyTypes-≟ as ECFD
open ECFD using (asymm-walk-□)
```

### §5.1 Trace equivalence at the body level

The library `CSP.Laws.Traces` provides both elimination (`InternalChoice-trace`) and
introduction (`IntChoice-trace-introL/R`, `Prefix₀-trace-intro`) directions for the
choice combinators. We use them directly below.

```agda
open ITree_Relations.LTS.Traces using (traces; _⊑ᵀ_)
```

### §5.2 Trace equivalence: `VM_body_impl ⟺ VM_body_spec`

Both bodies are trace-equivalent. We prove both directions.

```agda
open import Function using (case_of_)
```

**Direction 1** — spec traces are contained in impl traces (the hard direction:
inject `⊓` traces into `□`).

```agda
VM_body_impl⊑ᵀVM_body_spec : VM_body_impl ⊑ᵀ VM_body_spec
VM_body_impl⊑ᵀVM_body_spec {s} tr
  with Prefix₀-trace coin _ tr
... | inj₁ refl = _ , bNil
... | inj₂ (a , s′ , refl , tr-inner)
  with InternalChoice-trace (tea ⟶₀ Skip) (coffee ⟶₀ Skip) tr-inner
... | inj₁ tr-tea    = Prefix₀-trace-intro coin _ a (ExtChoice-trace-introL tr-tea)
... | inj₂ tr-coffee = Prefix₀-trace-intro coin _ a (ExtChoice-trace-introR tr-coffee)
```

**Direction 2** — impl traces are contained in spec traces (the easy direction:
inject `□` traces into `⊓`).

```agda
VM_body_spec⊑ᵀVM_body_impl : VM_body_spec ⊑ᵀ VM_body_impl
VM_body_spec⊑ᵀVM_body_impl {s} tr
  with Prefix₀-trace coin _ tr
... | inj₁ refl = _ , bNil
... | inj₂ (a , s′ , refl , tr-inner)
  with ExternalChoice-trace (tea ⟶₀ Skip) (coffee ⟶₀ Skip) tr-inner
... | inj₁ tr-tea    = Prefix₀-trace-intro coin _ a (IntChoice-trace-introL tr-tea)
... | inj₂ tr-coffee = Prefix₀-trace-intro coin _ a (IntChoice-trace-introR tr-coffee)
```

### §5.3 The canonical failures-divergences lesson

External choice refines internal choice in the FD model, but not the
reverse — this is the canonical lesson the example illustrates.

We start with the divergence side. Neither body has any divergences,
because each is a finite `vis`-shape ending in `Skip`. We prove
`VM_body_impl` divergence-free directly; this discharges `⊑D` trivially.

```agda
private
  -- No τ from a node P with force P = ret tt, or from anything bigstep-reachable from it.
  -- Uses library no-τ-from-ret (single-step) and no-τ-from-deadlock-bigstep (bigstep from deadlock).
  no-τ-from-ret-node :
    ∀ {P : ITree VM (ExtI VM) (⊤ {lzero})}
    → ITree.force P ≡ ret tt
    → ∀ {s : List (Event√ VM (⊤ {lzero}))} {P′ Q : ITree VM (ExtI VM) (⊤ {lzero})}
    → P ═⟨ s ⟩═► P′
    → P′ ─[ τ ]─► Q → ⊥
  no-τ-from-ret-node force-ret bNil step'' =
    no-τ-from-ret force-ret step''
  no-τ-from-ret-node force-ret (bTau τ-step _) _ =
    no-τ-from-ret force-ret τ-step
  no-τ-from-ret-node force-ret (bStep (sVis force-vis _) _) _ =
    -- force P = ret tt (force-ret) but sVis says force P = vis _ — contradiction
    case trans (sym force-ret) force-vis of λ ()
  no-τ-from-ret-node force-ret (bStep (sMixVis force-mix _) _) _ =
    case trans (sym force-ret) force-mix of λ ()
  no-τ-from-ret-node force-ret (bStep (sRet _) rest3) step'' =
    -- After √-step we are at deadlock; use library bigstep lemma.
    no-τ-from-deadlock-bigstep rest3 step''

  -- The target of a vis-step from (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip) has force = ret tt.
  -- Proof: mergeVis fP fQ at a = just t′ implies t′ = Skip by case on which event fired.
  ext-choice-step-force :
    ∀ {at : AnyTypes VM} {a : proj₁ at} {t′ : ITree VM (ExtI VM) (⊤ {lzero})}
    → mergeVis (Prefix-cont tea (λ (_ : ⊤ {lzero}) → Skip {E = VM}) at)
               (Prefix-cont coffee (λ (_ : ⊤ {lzero}) → Skip {E = VM}) at) a
        ≡ just t′
    → ITree.force t′ ≡ ret tt
  ext-choice-step-force {at = at} {a = a} eq'
    with VM-AnyTypes-≟ (⊤ , tea) at
  ... | yes refl
    with VM-AnyTypes-≟ (⊤ , coffee) (⊤ , tea)
  ... | yes ()
  ... | no  _
    with eq'
  ... | refl = refl
  ext-choice-step-force {at = at} {a = a} eq'
    | no _
    with VM-AnyTypes-≟ (⊤ , coffee) at
  ... | yes refl
    with eq'
  ... | refl = refl
  ext-choice-step-force {at = at} {a = a} eq'
    | no _ | no _
    = case eq' of λ ()

  -- No τ reachable from (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip) via bigstep.
  no-τ-layer1 :
    ∀ {s : List (Event√ VM (⊤ {lzero}))}
      {P Q : ITree VM (ExtI VM) (⊤ {lzero})}
    → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ═⟨ s ⟩═► P
    → P ─[ τ ]─► Q → ⊥
  no-τ-layer1 bNil step' =
    τ-from-force-vis-impossible refl step'
  no-τ-layer1 (bTau τ-step _) _ =
    τ-from-force-vis-impossible refl τ-step
  no-τ-layer1 (bStep (sVis refl eq') rest2) step' =
    -- Target t′ has force = ret tt (proven by ext-choice-step-force).
    no-τ-from-ret-node (ext-choice-step-force eq') rest2 step'
  no-τ-layer1 (bStep (sMixVis eq-mix _) _) _ =
    -- force = vis _, not mix _ — impossible (via eq-mix : force _ ≡ mix _ _)
    case eq-mix of λ ()

  -- No τ reachable via bigstep from VM_body_impl.
  no-τ-from-reachable :
    ∀ {s : List (Event√ VM (⊤ {lzero}))}
      {P Q : ITree VM (ExtI VM) (⊤ {lzero})}
    → VM_body_impl ═⟨ s ⟩═► P
    → P ─[ τ ]─► Q → ⊥
  no-τ-from-reachable bNil step =
    τ-from-force-vis-impossible refl step
  no-τ-from-reachable (bTau τ-step _) _ =
    τ-from-force-vis-impossible refl τ-step
  no-τ-from-reachable (bStep (sVis {at = at} refl eq-j) rest) step
    with VM-AnyTypes-≟ (⊤ , coin) at
  ... | no  _ = case eq-j of λ ()
  ... | yes refl with eq-j
  ...   | refl = no-τ-layer1 rest step
  no-τ-from-reachable (bStep (sMixVis eq-mix _) _) _ =
    case eq-mix of λ ()

VM_body_impl-no-div : ∀ {s} → divergences VM_body_impl s → ⊥
VM_body_impl-no-div d =
  no-τ-from-reachable
    (d .IsDivergence.reach)
    (Divergent.step (d .IsDivergence.divwit))

VM_body_spec⊑D-VM_body_impl : VM_body_spec ⊑D VM_body_impl
VM_body_spec⊑D-VM_body_impl d = ⊥-elim (VM_body_impl-no-div d)

```

The failures side: every failure of the impl is a failure of the spec.

```agda
private
  -- Helper: refusal of (tea⟶₀Skip) when noev says B excludes (tea□coffee) events.
  -- Uses top-level with-abstraction to force Prefix-cont to reduce.
  tea-noev-from-□ :
    ∀ {B : Event√ VM (⊤ {lzero}) → Set (lsuc lzero)}
    → (noev : ∀ e → B e → ∀ {Q : ITree VM (ExtI VM) (⊤ {lzero})}
                         → ¬ (((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ─[ ev e ]─► Q))
    → ∀ (e : Event√ VM (⊤ {lzero})) → B e
    → ∀ {Q : ITree VM (ExtI VM) (⊤ {lzero})}
    → ¬ ((tea ⟶₀ Skip) ─[ ev e ]─► Q)
  tea-noev-from-□ noev (evl (evLabel _ e a)) Be (sVis {at = at} refl eq-j)
    with VM-AnyTypes-≟ (⊤ , tea) at
  ... | no _    = case eq-j of λ ()
  ... | yes refl =
    noev (evl (evLabel ⊤ tea a)) Be
         (sVis {at = ⊤ , tea} {a = a} refl
               (cong (λ x → mergeMaybe x nothing)
                     (Prefix-cont-just tea (λ _ → Skip {E = VM}) a)))
  tea-noev-from-□ noev (evl _) Be (sMixVis eq-mix _) = case eq-mix of λ ()
  tea-noev-from-□ noev (√ _) _ (sRet ())

  -- Helper: refusal of VM_body_spec when noev says B excludes VM_body_impl events.
  spec-noev-from-impl :
    ∀ {B : Event√ VM (⊤ {lzero}) → Set (lsuc lzero)}
    → (noev : ∀ e → B e → ∀ {Q : ITree VM (ExtI VM) (⊤ {lzero})}
                         → ¬ (VM_body_impl ─[ ev e ]─► Q))
    → ∀ (e : Event√ VM (⊤ {lzero})) → B e
    → ∀ {Q : ITree VM (ExtI VM) (⊤ {lzero})}
    → ¬ (VM_body_spec ─[ ev e ]─► Q)
  spec-noev-from-impl noev (evl (evLabel _ e a)) Be (sVis {at = at} refl eq-j)
    with VM-AnyTypes-≟ (⊤ , coin) at
  ... | no _    = case eq-j of λ ()
  ... | yes refl =
    noev (evl (evLabel ⊤ coin a)) Be
         (sVis {at = ⊤ , coin} {a = a} refl
               (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) a))
  spec-noev-from-impl noev (evl _) Be (sMixVis eq-mix _) = case eq-mix of λ ()
  spec-noev-from-impl noev (√ _) _ (sRet ())

VM_body_spec⊑F⊥-VM_body_impl : VM_body_spec ⊑F⊥ VM_body_impl
-- Divergence case: impl never diverges.
VM_body_spec⊑F⊥-VM_body_impl (inj₂ d) = ⊥-elim (VM_body_impl-no-div d)
-- Failure case: lift each failure of impl to a failure of spec.
-- The key step uses asymm-walk-□ (core of ⊓⊑F⊥□; every failure of P □ Q is a failure of P ⊓ Q)
-- and prepends the coin step on the spec side via sVis + Prefix-cont-just.
VM_body_spec⊑F⊥-VM_body_impl {B = B} (inj₁ (P′ , bigstep , refusal)) =
  inj₁ (go bigstep refusal)
  where
    go : ∀ {s′} {Q} → VM_body_impl ═⟨ s′ ⟩═► Q → Q ref B → failures VM_body_spec s′ B
    -- Impossible bTau cases (force VM_body_impl = vis):
    go (bTau (sSil ())      _) _
    go (bTau (sNdbr () _)   _) _
    go (bTau (sMixSlide ()) _) _
    -- Impossible bStep constructors:
    go (bStep (sMixVis eq-mix _) _) _ = case eq-mix of λ ()
    go (bStep (sRet ())          _) _
    -- bNil: P′ = VM_body_impl; ref-tick is absurd (force = vis not ret).
    go bNil (ref-tick (sRet ()) _)
    -- bNil, ref-stable: B excludes coin events; spec has same vis-coin shape.
    go bNil (ref-stable _ noev) =
      VM_body_spec , bNil ,
        ref-stable tt₀ (spec-noev-from-impl noev)
    -- bStep (sVis coin): fired coin a, arriving at (tea□coffee).
    -- Use asymm-walk-□ (the plain-failures direction of ⊓⊑F⊥□) to lift
    -- the failure of (tea□coffee) to (tea⊓coffee), then prepend the coin step.
    go (bStep (sVis {at = at} {a = a} refl eq-j) rest) refusal′
      with VM-AnyTypes-≟ (⊤ , coin) at
    ... | no _    = case eq-j of λ ()
    ... | yes refl with eq-j
    ... | refl =
      let (T-spec , bs-spec , ref-spec) =
            asymm-walk-□ (τ*-step (⊓-step-L _ _) τ*-zero)
                         (τ*-step (⊓-step-R _ _) τ*-zero)
                         (_ , rest , refusal′)
      in  T-spec
          , bStep (sVis {at = ⊤ , coin} {a = a} refl
                        (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip)) a))
                  bs-spec
          , ref-spec
```

Combining failures and divergences:

```agda
canonical-lesson-✓ : VM_body_spec ⊑FD VM_body_impl
canonical-lesson-✓ = VM_body_spec⊑F⊥-VM_body_impl
                   , VM_body_spec⊑D-VM_body_impl
```

The reverse direction fails. We exhibit a refusal that the spec admits but
the impl does not: after firing `coin`, the spec can resolve the inner `⊓`
into the coffee branch and thereby refuse the `tea` event; the impl
cannot refuse `tea` because its `□` still offers both events.

```agda
-- The refusal predicate: the impl is asked to refuse the tea event.
-- `_⊑F_` quantifies B at level `lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr` which evaluates
-- to `lsuc lzero` here, so the codomain must live there.
RefusesTea : Event√ VM (⊤ {lzero}) → Set (lsuc lzero)
RefusesTea (evl (evLabel A tea a)) = Lift (lsuc lzero) (⊤ {lzero})
RefusesTea _                       = Lift (lsuc lzero) ⊥

private
  -- coffee ⟶₀ Skip is stable (vis-shaped, isStable = tt), and any
  -- visible step from it carries the coffee event — not tea.
  -- Combined with RefusesTea selecting only tea-labelled events,
  -- no enabled firing is possible.
  coffee-refuses-tea : ∀ e → RefusesTea e
                     → ∀ {Q : ITree VM (ExtI VM) (⊤ {lzero})}
                     → (coffee ⟶₀ Skip) ─[ ev e ]─► Q → ⊥
  -- Only tea-labelled events have RefusesTea = Lift ⊤.
  -- A step from (coffee ⟶₀ Skip) via sVis requires eq-j : Prefix-cont coffee _ at a ≡ just Q.
  -- Since at = (A, tea) (from the label match), Prefix-cont coffee _ (A, tea) a
  -- checks E-≟ (A, coffee) (A, tea) = no _, returning nothing.  So eq-j : nothing ≡ just Q, absurd.
  coffee-refuses-tea (evl (evLabel A tea a)) _ (sVis {at = at} refl eq-j) = case eq-j of λ ()
  coffee-refuses-tea (evl (evLabel A tea a)) _ (sMixVis eq-mix _) = case eq-mix of λ ()
  coffee-refuses-tea (evl (evLabel A coffee a)) (lift ()) _
  coffee-refuses-tea (evl (evLabel A coin   a)) (lift ()) _
  coffee-refuses-tea (√ _)                      (lift ()) _

fail-coin-refuses-tea
  : failures⊥ VM_body_spec (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea
fail-coin-refuses-tea =
  -- Exhibit the failure: fire coin, then τ-step via ⊓-step-R to (coffee ⟶₀ Skip),
  -- which is stable and refuses RefusesTea.
  inj₁ ( coffee ⟶₀ Skip
       , bStep (sVis {at = ⊤ , coin} {a = tt} refl
                     (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip)) tt))
               (bTau (⊓-step-R _ _) bNil)
       , ref-stable tt₀ coffee-refuses-tea
       )

private
  -- Decompose a bigstep from (tea □ coffee) along the empty trace.
  -- force (tea □ coffee) = vis _, so τ is impossible, and only bNil remains.
  go-inner : ∀ {P′ : ITree VM (ExtI VM) (⊤ {lzero})}
           → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ═⟨ [] ⟩═► P′
           → _ref_ P′ RefusesTea → ⊥
  -- τ from (tea □ coffee) is impossible: force = vis
  go-inner (bTau (sSil ())      _) _
  go-inner (bTau (sNdbr () _)   _) _
  go-inner (bTau (sMixSlide ()) _) _
  -- bNil: P′ = (tea □ coffee); dispatch on the refusal.
  go-inner bNil (ref-tick (sRet ()) _)
  -- ref-stable: noev claims no RefusesTea-event is enabled.
  -- But (tea □ coffee) CAN fire tea: sVis refl (merged cont = just Skip).
  go-inner bNil (ref-stable _ noev) =
    noev (evl (evLabel ⊤ tea tt)) (lift tt)
         (sVis {at = ⊤ , tea} {a = tt} refl
               (cong (λ x → mergeMaybe x nothing)
                     (Prefix-cont-just tea (λ _ → Skip {E = VM}) tt)))

no-such-failure-impl
  : failures⊥ VM_body_impl (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea → ⊥
-- Divergence case: impl never diverges.
no-such-failure-impl (inj₂ d) = VM_body_impl-no-div d
-- Failure case: decompose the bigstep, reach (tea □ coffee), derive contradiction.
no-such-failure-impl (inj₁ (P′ , bigstep , ref)) = go bigstep ref
  where
    go : ∀ {P′ : ITree VM (ExtI VM) (⊤ {lzero})}
       → VM_body_impl ═⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩═► P′
       → _ref_ P′ RefusesTea → ⊥
    -- τ from VM_body_impl is impossible: force = vis
    go (bTau (sSil ())      _) _
    go (bTau (sNdbr () _)   _) _
    go (bTau (sMixSlide ()) _) _
    -- bStep: fire the coin event, reaching the inner □-state.
    go (bStep (sMixVis eq-mix _) _) _ = case eq-mix of λ ()
    go (bStep (sVis {at = at} refl eq-j) rest) ref′
      with VM-AnyTypes-≟ (⊤ , coin) at
    ... | no  neq = ⊥-elim (neq refl)
    ... | yes refl with eq-j
    ... | refl = go-inner rest ref′

canonical-lesson-✗ : VM_body_impl ⊑FD VM_body_spec → ⊥
canonical-lesson-✗ refines =
  no-such-failure-impl (proj₁ refines fail-coin-refuses-tea)
```

### §5.3b Loop-level refinement

The body-level results lift to the `loop0`-wrapped processes. The
**forward** direction is now a direct consequence of the iterate
monotonicity law `loop0-mono-⊑FD` (discharged in `CSP.Laws.Iterate_FD`
atop the generic iteration bisimulation), which was the stub §5.5
previously flagged.

```agda
import CSP.Laws.Iterate_FD {E = VM} as IterFD
open IterFD VM-AnyTypes-≟ using (loop0-mono-⊑FD)

-- VM_spec = loop0 VM_body_spec, VM_impl = loop0 VM_body_impl (both at R = ⊥).
VM_spec⊑FD-VM_impl : VM_spec ⊑FD VM_impl
VM_spec⊑FD-VM_impl = loop0-mono-⊑FD canonical-lesson-✓
```

### §5.3c Loop-level strictness (reverse)

The reverse refinement `VM_impl ⊑FD VM_spec` is **false**, mirroring the
body-level `canonical-lesson-✗` one iteration deep through `loop0`. We
reuse the body-level building blocks, threading them through the
`iter-bind` one-iteration prefix via the `loop0-failures⊥` characterisation
laws (already proved in `CSP.Laws.Iterate`).

```agda
import CSP.Laws.Iterate {E = VM} as IterL
open IterL VM-AnyTypes-≟
  using ( LoopSplit; in-body; in-loop
        ; LoopFailureSplit; loop-fail
        ; LoopDivergenceSplit; loop-div
        ; Loop0FailureSplit; Loop0DivergenceSplit
        ; loop0-failures⊥-elim; loop0-failures⊥-intro-failures
        ; iter-bind-force-vis; iter-bind-cont-vis-just )

import CSP.Laws.Bind {E = VM} as BindL
open BindL VM-AnyTypes-≟ using (lift-bind-bigstep; bind-force-vis)
```

The loop processes carry return type `⊥`, so the refusal predicate must
live over `Event√ VM ⊥`. We reuse the same "refuse the tea event" idea.

```agda
RefusesTea⊥ : Event√ VM ⊥ → Set (lsuc lzero)
RefusesTea⊥ (evl (evLabel A tea a)) = Lift (lsuc lzero) (⊤ {lzero})
RefusesTea⊥ _                       = Lift (lsuc lzero) ⊥
```

We name the one-iteration body bigstep of the spec: fire `coin`, then
τ-resolve the inner `⊓` to the coffee branch, landing at `coffee ⟶₀ Skip`.
This reuses the very shape from the body-level `fail-coin-refuses-tea`.

```agda
private
  -- VM_body_spec ═⟨ [coin] ⟩═► (coffee ⟶₀ Skip).
  spec-body-bigstep
    : VM_body_spec ═⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩═► (coffee ⟶₀ Skip)
  spec-body-bigstep =
    bStep (sVis {at = ⊤ , coin} {a = tt} refl
                (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip)) tt))
          (bTau (⊓-step-R _ _) bNil)

  -- The continuation that loopStep appends after the body.
  loop-k : ⊤ {lzero} → ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
  loop-k = λ a' → Ret (inj₁ a')

  -- P' : the body endpoint lifted through loopStep's bind.
  spec-P' : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
  spec-P' = (coffee ⟶₀ Skip) >>= loop-k

  -- loopStep specialised to the spec body (loopStep is private in Iterate,
  -- so we spell out its definition `body a >>= λ a' → Ret (inj₁ a')`).
  spec-loopStep : ⊤ {lzero} → ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
  spec-loopStep = λ a → VM_body_spec >>= loop-k

  -- Q : one-iteration reachable loop state, wrapped through iter-bind.
  spec-Q : ITree VM (ExtI VM) ⊥
  spec-Q = iter-bind spec-P' spec-loopStep
```

`spec-Q` is doubly vis-wrapped (`coffee ⟶₀ Skip` is vis-shaped, so both
the `>>= loop-k` bind layer and the outer `iter-bind` layer keep a `vis`
force). Hence `spec-Q` is stable, and the only event it can fire is
`coffee` — never `tea`. This is the two-continuation-layer analogue of the
body-level `coffee-refuses-tea`.

```agda
private
  spec-Q-refuses-tea : ∀ e → RefusesTea⊥ e
                     → ∀ {Q : ITree VM (ExtI VM) ⊥}
                     → spec-Q ─[ ev e ]─► Q → ⊥
  -- tea: the only event with RefusesTea ≠ ⊥. A sVis from spec-Q at (⊤,tea)
  -- needs eq-j : iter-bind-cont-vis _ (bind-cont-vis loop-k fcoffee) (⊤,tea) a ≡ just Q.
  -- That continuation chain returns nothing (coffee ≠ tea), so eq-j is absurd.
  spec-Q-refuses-tea (evl (evLabel A tea a)) _ (sVis {at = at} refl eq-j) = case eq-j of λ ()
  spec-Q-refuses-tea (evl (evLabel A tea a)) _ (sMixVis eq-mix _) = case eq-mix of λ ()
  spec-Q-refuses-tea (evl (evLabel A coffee a)) (lift ()) _
  spec-Q-refuses-tea (evl (evLabel A coin   a)) (lift ()) _
  spec-Q-refuses-tea (√ _)                      (lift ()) _
```

Assemble the loop-level failure: lift the body bigstep through
`loopStep`'s bind, package it as a `LoopSplit` (`in-body`), and attach the
stable refusal at `spec-Q`.

```agda
spec-loop-fail : failures⊥ VM_spec (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea⊥
spec-loop-fail =
  loop0-failures⊥-intro-failures VM_body_spec
    (loop-fail
      (in-body {P' = spec-P'} {s = evLabel ⊤ coin tt ∷ []}
               (lift-bind-bigstep VM_body_spec loop-k
                                  (evLabel ⊤ coin tt ∷ []) spec-body-bigstep)
               refl)
      (ref-stable tt₀ spec-Q-refuses-tea))
```

### (B) The impl loop cannot refuse `tea` after `coin`

After `coin`, the impl sits at `((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) >>= k`
inside `iter-bind`, which still OFFERS `tea`. We refute both arms of
`loop0-failures⊥-elim`.

```agda
private
  -- impl loopStep continuation (spelled out, loopStep is private).
  impl-loopStep : ⊤ {lzero} → ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
  impl-loopStep = λ a → VM_body_impl >>= loop-k

  -- The impl one-iteration state after firing coin (the □-state, bind- then
  -- iter-bind-wrapped).  It OFFERS tea, so it cannot refuse it.
  impl-P' : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
  impl-P' = ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) >>= loop-k

  impl-Q : ITree VM (ExtI VM) ⊥
  impl-Q = iter-bind impl-P' impl-loopStep

  -- The force-continuation of (tea □ coffee), fully annotated to avoid
  -- level/index ambiguity.
  f□ : (at : AnyTypes VM) → ContinueType at (Maybe (ITree VM (ExtI VM) (⊤ {lzero})))
  f□ = λ Ae → mergeVis (Prefix-cont tea    (λ (_ : ⊤ {lzero}) → Skip {E = VM} {I = ExtI VM}) Ae)
                       (Prefix-cont coffee (λ (_ : ⊤ {lzero}) → Skip {E = VM} {I = ExtI VM}) Ae)

  -- impl-Q fires tea: chase the merge / bind / iter-bind continuations.
  impl-Q-fires-tea : impl-Q ─[ ev (evl (evLabel ⊤ tea tt)) ]─►
                     iter-bind (Skip {E = VM} {I = ExtI VM} >>= loop-k) impl-loopStep
  impl-Q-fires-tea =
    sVis {at = ⊤ , tea} {a = tt} refl
      (iter-bind-cont-vis-just impl-loopStep (bind-cont-vis loop-k f□) (⊤ , tea) tt
        (bind-cont-vis-just loop-k f□ (⊤ , tea) tt
          (cong (λ x → mergeMaybe x nothing)
                (Prefix-cont-just tea (λ (_ : ⊤ {lzero}) → Skip {E = VM} {I = ExtI VM}) tt))))

  -- A bigstep of the impl loopStep along [coin] must end exactly at impl-P'.
  -- force (VM_body_impl >>= loop-k) = vis (bind-cont-vis loop-k fcoin), so the
  -- only viable first step is sVis firing coin; the empty tail leaves us at
  -- impl-P' = (tea□coffee) >>= loop-k (vis-shaped, so bNil is forced).
  loopStep-coin-inv : ∀ {P' : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
                    → (VM_body_impl >>= loop-k) ═⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩═► P'
                    → P' ≡ impl-P'
  -- τ from a vis-shaped node is impossible.
  loopStep-coin-inv (bTau (sSil ())      _)
  loopStep-coin-inv (bTau (sNdbr () _)   _)
  loopStep-coin-inv (bTau (sMixSlide ()) _)
  loopStep-coin-inv (bStep (sMixVis eq-mix _) _) = case eq-mix of λ ()
  -- The trace head `evl (evLabel ⊤ coin tt)` forces at = (⊤,coin); the coin
  -- continuation yields just impl-P', so eq-j pins t′ = impl-P'.
  loopStep-coin-inv (bStep (sVis refl eq-j) rest)
    with eq-j
  ... | refl = inv-tail rest
    where
      -- After firing coin we are at impl-P' (vis-shaped); the empty trace
      -- forces bNil, pinning the endpoint.
      inv-tail : ∀ {P' : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
               → impl-P' ═⟨ [] ⟩═► P' → P' ≡ impl-P'
      inv-tail bNil = refl
      inv-tail (bTau (sSil ())      _)
      inv-tail (bTau (sNdbr () _)   _)
      inv-tail (bTau (sMixSlide ()) _)

  -- A vis-shaped tree cannot perform a √-tick as its first action: the only
  -- step producing a √-label is sRet, which requires force ≡ ret.
  vis-no-immediate-tick
    : ∀ {a' : ⊤ {lzero}} {rest : List (Event√ VM (⊤ {lzero} ⊎ ⊥))}
        {P T : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
        {f}
    → ITree.force P ≡ vis f
    → P ═⟨ √ (inj₁ a') ∷ rest ⟩═► T → ⊥
  vis-no-immediate-tick fv (bTau step _) = τ-from-force-vis-impossible fv step
  vis-no-immediate-tick fv (bStep (sRet eq-r) _) = case trans (sym fv) eq-r of λ ()

  -- From a [coin]-split (over any R), the visible prefix s1 ∈ {[], [coin]}.
  s1-from-coin-split
    : ∀ {ℓr'} {R' : Set ℓr'} (s1 : List (Event VM)) {s2 : List (Event√ VM R')}
    → map (evl {R = R'}) s1 ++ s2 ≡ evl (evLabel ⊤ coin tt) ∷ []
    → (s1 ≡ []) ⊎ (s1 ≡ evLabel ⊤ coin tt ∷ [])
  s1-from-coin-split []                          _   = inj₁ refl
  s1-from-coin-split (.(evLabel ⊤ coin tt) ∷ []) refl = inj₂ refl
  s1-from-coin-split (e ∷ _ ∷ _)                 ()

  -- loopStep tt cannot tick √(inj₁ a') with s1 ∈ {[], [coin]}: it needs to
  -- fire coin AND a drink before completing one iteration.
  impl-tick-absurd
    : ∀ {a' : ⊤ {lzero}} (s1 : List (Event VM))
    → (s1 ≡ []) ⊎ (s1 ≡ evLabel ⊤ coin tt ∷ [])
    → (VM_body_impl >>= loop-k) ═⟨ map (evl {R = ⊤ {lzero} ⊎ ⊥}) s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
    → ⊥
  -- s1 = []: tick immediately from the (vis-shaped) coin offer — impossible.
  impl-tick-absurd .[]                      (inj₁ refl) bs = vis-no-immediate-tick refl bs
  -- s1 = [coin]: fire coin then tick from impl-P' (vis-shaped) — impossible.
  impl-tick-absurd .(evLabel ⊤ coin tt ∷ []) (inj₂ refl) bs = go-coin bs
    where
      go-coin : (VM_body_impl >>= loop-k)
                  ═⟨ evl (evLabel ⊤ coin tt) ∷ [ √ (inj₁ _) ] ⟩═► deadlock → ⊥
      go-coin (bTau (sSil ())      _)
      go-coin (bTau (sNdbr () _)   _)
      go-coin (bTau (sMixSlide ()) _)
      go-coin (bStep (sMixVis eq-mix _) _) = case eq-mix of λ ()
      go-coin (bStep (sVis refl eq-j) rest)
        with eq-j
      ... | refl = vis-no-immediate-tick refl rest

  -- After firing a prefix of [coin] through loopStep, the residual P' is
  -- always vis-shaped (force P' = vis): for s1 = [] it is loopStep tt, for
  -- s1 = [coin] it is impl-P'.  Hence iter-bind P' impl-loopStep is vis too.
  in-body-Q-no-τ
    : ∀ (s1 : List (Event VM)) {P' : ITree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
        {Q' : ITree VM (ExtI VM) ⊥}
    → (s1 ≡ []) ⊎ (s1 ≡ evLabel ⊤ coin tt ∷ [])
    → (VM_body_impl >>= loop-k) ═⟨ map (evl {R = ⊤ {lzero} ⊎ ⊥}) s1 ⟩═► P'
    → iter-bind P' impl-loopStep ─[ τ ]─► Q' → ⊥
  -- s1 = []: P' = loopStep tt (force vis); iter-bind force vis; no τ.
  in-body-Q-no-τ .[] (inj₁ refl) bNil                   step =
    τ-from-force-vis-impossible refl step
  in-body-Q-no-τ .[] (inj₁ refl) (bTau (sSil ())      _) _
  in-body-Q-no-τ .[] (inj₁ refl) (bTau (sNdbr () _)   _) _
  in-body-Q-no-τ .[] (inj₁ refl) (bTau (sMixSlide ()) _) _
  -- s1 = coin ∷ []: P' = impl-P' (force vis); iter-bind force vis; no τ.
  in-body-Q-no-τ .(evLabel ⊤ coin tt ∷ []) (inj₂ refl) bs step
    with loopStep-coin-inv bs
  ... | refl = τ-from-force-vis-impossible refl step

  -- A refusal at a vis-shaped Q is necessarily ref-stable (ref-tick needs ret).
  -- Its noev claims no RefusesTea⊥-event fires; we contradict it with the tea
  -- step.  Used in the failure arm after pinning Q = impl-Q.
  impl-Q-no-ref : impl-Q ref RefusesTea⊥ → ⊥
  impl-Q-no-ref (ref-tick (sRet ()) _)
  impl-Q-no-ref (ref-stable _ noev) =
    noev (evl (evLabel ⊤ tea tt)) (lift tt) impl-Q-fires-tea
```

Now refute both arms of `loop0-failures⊥-elim` and assemble the loop-level
analogue of `no-such-failure-impl`.

```agda
no-loop-fail-impl
  : failures⊥ VM_impl (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea⊥ → ⊥
no-loop-fail-impl f with loop0-failures⊥-elim VM_body_impl f
-- Divergence arm: VM_impl fires a visible coin every iteration, never diverges.
... | inj₂ (loop-div prefix suffix split (in-body {s = s1} bs refl) divwit) =
      in-body-Q-no-τ s1 (s1-from-coin-split s1 {s2 = suffix} (sym split)) bs
                     (divwit .Divergent.step)
... | inj₂ (loop-div prefix suffix split
              (in-loop {s1 = s1} {s2 = s2} eq-s tick-bs trk) divwit) =
      impl-tick-absurd s1
        (s1-from-coin-split s1 {s2 = s2 ++ suffix} (helper (sym split) eq-s)) tick-bs
  where
    open import Data.List.Properties using (++-assoc)
    -- prefix = map evl s1 ++ s2 and prefix ++ suffix = [coin], so
    -- map evl s1 ++ (s2 ++ suffix) = [coin].
    helper : prefix ++ suffix ≡ evl (evLabel ⊤ coin tt) ∷ []
           → prefix ≡ map (evl {R = ⊥}) s1 ++ s2
           → map (evl {R = ⊥}) s1 ++ (s2 ++ suffix) ≡ evl (evLabel ⊤ coin tt) ∷ []
    helper sp es rewrite sym (++-assoc (map (evl {R = ⊥}) s1) s2 suffix)
                       | sym es = sp
-- Failure arm: after coin the impl sits at the □-state, which OFFERS tea.
-- We abstract the LoopSplit's trace to a variable `s` (so the `in-body`
-- `map evl s'` index unifies without getting stuck), then use the
-- propositional `s ≡ [coin]` to pin the iteration shape.
... | inj₁ (loop-fail ls ref) = fail-absurd _ ls refl ref
  where
    fail-absurd : ∀ {Q : ITree VM (ExtI VM) ⊥} (s : List (Event√ VM ⊥))
                → LoopSplit (λ _ → VM_body_impl) tt Q s
                → s ≡ evl (evLabel ⊤ coin tt) ∷ []
                → _ref_ Q RefusesTea⊥ → ⊥
    -- in-body: the single coin event forces s' = [coin]; then loopStep-coin-inv
    -- pins P' = impl-P', so Q = impl-Q, which offers tea (impl-Q-no-ref).
    fail-absurd s (in-body {s = []}        bs refl) () _
    fail-absurd s (in-body {s = _ ∷ _ ∷ _} bs refl) () _
    fail-absurd s (in-body {s = _ ∷ []}    bs refl) refl ref'
      with loopStep-coin-inv bs
    ... | refl = impl-Q-no-ref ref'
    -- in-loop: loopStep cannot complete an iteration (√-tick) within [coin].
    fail-absurd s (in-loop {s1 = s1} {s2 = s2} eq-s tick-bs trk) s≡coin _ =
      impl-tick-absurd s1
        (s1-from-coin-split s1 {s2 = s2} (trans (sym eq-s) s≡coin)) tick-bs
```

Assemble the loop-level strictness: if the impl FD-refined the spec, the
spec's `[coin]`-then-refuse-`tea` failure would transfer to the impl —
but the impl cannot refuse `tea`.

```agda
canonical-lesson-loop-✗ : VM_impl ⊑FD VM_spec → ⊥
canonical-lesson-loop-✗ refines =
  no-loop-fail-impl (proj₁ refines spec-loop-fail)
```




### §5.4 LTL on a sample trace

We illustrate LTL safety and liveness on a finite witness trace of
`VM_body_impl`. Following the LTL module's v1 limits, we work at the
witness-trace level (`⟦ φ ⟧ tr`) rather than at the satisfaction level
(`t ⊨ φ`), which would need trace-uniqueness lemmas the LTL module
defers to v2.

```agda
open import ITree_Relations.LTL.Traces_Based
  using ( LTLᵗ; atom; ⟦_⟧; G_; F_; X_; _⇒_
        ; Frame; Trace; ∞Trace; step; done; stuck
        ; ⟦G⟧⁺; ⟦G⟧⁺⇒⟦G⟧; tail; drop; drop-stutter; frameOf)
open ∞Trace
```

The VM-specific atoms react only to event shape; they are polymorphic in
the trace's return type so the same atom set works for body-level
(`R = ⊤`) and (hypothetical) loop-level (`R = ⊥`) traces.

```agda
atCoin : ∀ {R : Set lzero} → LTLᵗ lzero VM (ExtI VM) R
atCoin = atom λ
  { (step _ (evl (evLabel _ coin _)))   → ⊤ {lzero}
  ; _                                    → ⊥ }

atTea : ∀ {R : Set lzero} → LTLᵗ lzero VM (ExtI VM) R
atTea = atom λ
  { (step _ (evl (evLabel _ tea _)))    → ⊤ {lzero}
  ; _                                    → ⊥ }

atCoffee : ∀ {R : Set lzero} → LTLᵗ lzero VM (ExtI VM) R
atCoffee = atom λ
  { (step _ (evl (evLabel _ coffee _))) → ⊤ {lzero}
  ; _                                    → ⊥ }

atDrink : ∀ {R : Set lzero} → LTLᵗ lzero VM (ExtI VM) R
atDrink = atom λ
  { (step _ (evl (evLabel _ tea _)))    → ⊤ {lzero}
  ; (step _ (evl (evLabel _ coffee _))) → ⊤ {lzero}
  ; _                                    → ⊥ }
```

A concrete finite trace of `VM_body_impl` exhibiting coin · coffee · √
(then `done tt`).  Both the safety and liveness witnesses below use this
single trace.

```agda
-- Fire coffee through (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip).
-- force (P □ Q) | vis fP | vis fQ = vis (mergeVis fP fQ).
-- mergeVis at (⊤,coffee) a = mergeMaybe nothing (just Skip) = just Skip,
-- since Prefix-cont tea _ (⊤,coffee) a = nothing definitionally (tea ≠ coffee).
private
  sampleTrace-□-coffee-step : ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))
                ─[ ev (evl (evLabel ⊤ coffee tt)) ]─► Skip {E = VM} {I = ExtI VM}
  sampleTrace-□-coffee-step =
    sVis {at = ⊤ , coffee} {a = tt} refl
         (cong (mergeMaybe nothing)
               (Prefix-cont-just coffee (λ _ → Skip {E = VM} {I = ExtI VM}) tt))

sampleTrace : Trace VM (ExtI VM) (⊤ {lzero})
sampleTrace =
  step (weak-ev {p = VM_body_impl} τ*-zero
                (sVis {at = ⊤ , coin} {a = tt} refl
                      (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) tt))
                τ*-zero)
       (record { force =
  step (weak-ev τ*-zero sampleTrace-□-coffee-step τ*-zero) (record { force =
  done {t = Skip} refl }) })
```

**Safety**: after every coin event, the very next observation is a drink.

```agda
safetyFormula : LTLᵗ lzero VM (ExtI VM) (⊤ {lzero})
safetyFormula = G (atCoin ⇒ X atDrink)

safety : ⟦ safetyFormula ⟧ sampleTrace
safety = ⟦G⟧⁺⇒⟦G⟧ {φ = atCoin ⇒ X atDrink} {tr = sampleTrace} safety⁺
  where
    safety⁺ : ⟦G⟧⁺ (atCoin ⇒ X atDrink) sampleTrace
    -- atCoin ⇒ X atDrink = (¬ atCoin) ∨ X atDrink = ¬ ((¬¬ atCoin) ∧ (¬ X atDrink))
    -- ⟦ … ⟧ tr = ((⟦ atCoin ⟧ tr → Lift lzero ⊥) → Lift lzero ⊥) × (⟦ X atDrink ⟧ tr → Lift lzero ⊥)
    --           → Lift lzero ⊥
    -- Strategy: use the second component (¬ X atDrink) or the first (¬¬ atCoin),
    -- whichever gives a contradiction.
    --
    -- pos 0: ⟦ X atDrink ⟧ sampleTrace = ⟦ atDrink ⟧ (tail sampleTrace)
    --      = atDrink at coffee step = ⊤ {lzero}
    -- Contradiction: notDrink : ⊤ {lzero} → Lift lzero ⊥, apply to tt
    safety⁺ zero (_ , notDrink) = notDrink tt
    -- pos 1: coffee step; ⟦ atCoin ⟧ (drop 1 sampleTrace) = ⊥ (coffee ≠ coin)
    -- ⟦¬¬ atCoin⟧ = (⊥ → Lift lzero ⊥) → Lift lzero ⊥
    -- notnotCoin : (⊥ → Lift lzero ⊥) → Lift lzero ⊥; apply to λ ()
    safety⁺ (suc zero) (notnotCoin , _) = notnotCoin (λ ())
    -- pos ≥ 2: drop (2+n) reaches the done frame which stutters.
    -- drop (suc (suc n)) sampleTrace = drop n (done refl) = done refl (by drop-stutter).
    -- At done frame: ⟦ atCoin ⟧ = ⊥, ⟦ X atDrink ⟧ = ⊥.
    -- notnotCoin : (⊥ → Lift lzero ⊥) → Lift lzero ⊥; apply to (λ x → ⊥-elim x).
    -- Transport the done-frame proof back along sym (drop-stutter n (done refl) tt₀).
    safety⁺ (suc (suc n)) =
      subst (⟦_⟧ {E = VM} {I = ExtI VM} {R = ⊤ {lzero}} (atCoin ⇒ X atDrink))
            (sym (drop-stutter n (done {t = Skip {E = VM} {I = ExtI VM}} refl) tt₀))
            (λ (notnotCoin , _) → notnotCoin (λ x → ⊥-elim x))
```

**Liveness**: a coffee event occurs.

```agda
livenessFormula : LTLᵗ lzero VM (ExtI VM) (⊤ {lzero})
livenessFormula = F atCoffee

liveness : ⟦ livenessFormula ⟧ sampleTrace
-- ⟦ F atCoffee ⟧ sampleTrace = Σ ℕ (λ n → ⟦ atCoffee ⟧ (drop n sampleTrace) × (∀ m < n → ⟦ ⊤' ⟧ ...))
-- n = 1: coffee is at pos 1 (second step); ⟦ atCoffee ⟧ (drop 1 ..) = ⊤ {lzero}, witness = tt (poly)
-- third component: ∀ m → m < 1 → Lift lzero Data.Unit.⊤; witness = λ _ _ → lift tt₀
liveness = 1 , tt , (λ _ _ → lift tt₀)
```

### §5.4b Further LTL properties on the witness trace

The same trace satisfies a spread of LTL connectives: conjunction with
`X` (next), `U` (until), nested `X` reaching the `done` terminator, and a
second `G`/`¬` safety property. (We rename the LTL negation to `¬ᵗ_` to
avoid the clash with `Relation.Nullary.¬_` already in scope.)

```agda
open import ITree_Relations.LTL.Traces_Based
  using (_U_; _∧_; atDone) renaming (¬_ to ¬ᵗ_)
open import Data.Nat using (_<_; s≤s)
```

**(a) Conjunction + next.** The run starts with `coin`, and the next
observation is `coffee`.

```agda
startThenCoffee : ⟦ atCoin ∧ X atCoffee ⟧ sampleTrace
startThenCoffee = tt , tt
```

**(b) Until.** `coin` holds until a drink is served — the drink lands at
position 1, and `coin` holds at the only earlier position 0.

```agda
coinUntilDrink : ⟦ atCoin U atDrink ⟧ sampleTrace
coinUntilDrink = 1 , tt , λ { zero _ → tt ; (suc _) (s≤s ()) }
```

**(c) Reaching termination.** After two steps the trace is `done`.
`⟦ X (X (atDone _)) ⟧` reduces to the `atDone` predicate at the `done tt`
frame, which we take to be trivially `⊤`.

```agda
reachesDone : ⟦ X (X (atDone (λ _ → ⊤ {lzero}))) ⟧ sampleTrace
reachesDone = tt
```

**(d) Safety: no tea.** This run never serves `tea` (the `□` resolved to
coffee). Proved via `⟦G⟧⁺` (the constructive global form), casing the
position into `0`, `1`, and `≥ 2`; from position 2 on the trace stutters
at the `done` frame (`drop-stutter`), where `atTea` is `⊥`.

```agda
neverTea : ⟦ G (¬ᵗ atTea) ⟧ sampleTrace
neverTea = ⟦G⟧⁺⇒⟦G⟧ {φ = ¬ᵗ atTea} {tr = sampleTrace} neverTea⁺
  where
    neverTea⁺ : ⟦G⟧⁺ (¬ᵗ atTea) sampleTrace
    neverTea⁺ zero       = λ ()
    neverTea⁺ (suc zero) = λ ()
    neverTea⁺ (suc (suc n)) =
      subst (⟦_⟧ {E = VM} {I = ExtI VM} {R = ⊤ {lzero}} (¬ᵗ atTea))
            (sym (drop-stutter n (done {t = Skip {E = VM} {I = ExtI VM}} refl) tt₀))
            (λ ())
```

**(e) Liveness culminating in termination.** Eventually a `coffee` is
served, immediately after which the machine is `done` — combining `F`,
`∧`, `X`, and the `done` terminator in a single formula.

```agda
coffeeThenDone : ⟦ F (atCoffee ∧ X (atDone (λ _ → ⊤ {lzero}))) ⟧ sampleTrace
coffeeThenDone = 1 , (tt , tt) , (λ _ _ → lift tt₀)
```

### §5.5 What is intentionally deferred

- **Loop-level refinement (forward).** ✅ Done — see §5.3b:
  `VM_spec ⊑FD VM_impl` follows from `loop0-mono-⊑FD`
  (`CSP.Laws.Iterate_FD`, built on the iteration-tag-generic
  bisimulation). The monotonicity laws that were stubs are now
  discharged.

- **Loop-level strictness (reverse).** ✅ Done — see §5.3b
  (`canonical-lesson-loop-✗`). Refuting `VM_impl ⊑FD VM_spec` at the
  loop level needed NO new law: it is assembled from the
  `loop0-failures⊥-elim` / `loop0-failures⊥-intro-failures`
  characterisation laws (already in `CSP.Laws.Iterate`) plus the
  body-level refusal arguments, threaded through the `iter-bind`
  one-iteration prefix.

- **`_⊨_`-shaped LTL claims.** `t ⊨ φ` quantifies over *every* trace
  rooted at `t`. Proving `VM_impl ⊨ G (atCoin ⇒ X atDrink)` requires
  trace-uniqueness / inversion lemmas the LTL module flags as v2 (see
  the footer of `ITree_Relations.LTL.Traces_Based`).

- **DR-weak bisimulation between `VM_impl` and `VM_spec`.** Plausible
  but out of scope here; the natural next step toward bisim-invariant
  LTL claims.
