# Vending machine: modelling and verification

A worked example modelling a simple vending machine in CSP and verifying
properties about it via **LTL** (`⟦_⟧` over `LTLᵗ` from
`Semantics.LTL.Traces_Based`).

The implementation uses **external choice** (`□`) between tea and coffee;
the specification uses **internal choice** (`⊓`). They are trace-equivalent
but FD-related strictly in one direction — the canonical "external choice
refines internal choice" lesson. (The FD development is done in both
directions at both the body level and the `loop0` level — see §5.)

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

open import Process_Trees

open PTree

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

import CSP.Operators {E = VM} as CSPOps
open CSPOps VM-AnyTypes-≟
```

## §4. Process definitions

The body of each iteration: `coin`, then either tea or coffee, then loop back.

```agda
VM_body_impl : PTree VM (ExtI VM) (⊤ {lzero})
VM_body_impl = coin ⟶₀ ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))

VM_body_spec : PTree VM (ExtI VM) (⊤ {lzero})
VM_body_spec = coin ⟶₀ ((tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip))

VM_impl : PTree VM (ExtI VM) ⊥
VM_impl = loop0 VM_body_impl

VM_spec : PTree VM (ExtI VM) ⊥
VM_spec = loop0 VM_body_spec
```

## §5. Verification

Shared law imports for the body-level trace and FD reasoning below.

```agda
open import CSP.Laws.Traces.TraceLawsExtChoiceMono VM-AnyTypes-≟ using (□≈T⊓)
open import CSP.Laws.Traces.TraceLaws              VM-AnyTypes-≟ using (⟶₀-mono-⊑ᵀ)
open import CSP.Laws.FD.ChoiceRefine               VM-AnyTypes-≟ using (⊓⊑FD□; ⟶₀-mono-⊑FD)
open import Semantics.Failures            {E = VM} {I = ExtI VM} using (_⊑T_)
open import Semantics.FailuresDivergences {E = VM} {I = ExtI VM} using (_⊑FD_)
```

### §5.1–§5.2 Body-level trace equivalence

The implementation (external choice) and specification (internal choice) of the
body agree on traces: external and internal choice have the same trace set, and
prefixing is trace-monotone, so the two bodies trace-refine each other in both
directions.

```agda
VM_body_impl⊑ᵀVM_body_spec : VM_body_impl ⊑T VM_body_spec
VM_body_impl⊑ᵀVM_body_spec =
  ⟶₀-mono-⊑ᵀ coin (proj₁ (□≈T⊓ (tea ⟶₀ Skip) (coffee ⟶₀ Skip)))

VM_body_spec⊑ᵀVM_body_impl : VM_body_spec ⊑T VM_body_impl
VM_body_spec⊑ᵀVM_body_impl =
  ⟶₀-mono-⊑ᵀ coin (proj₂ (□≈T⊓ (tea ⟶₀ Skip) (coffee ⟶₀ Skip)))
```

### §5.3 (forward) Body-level FD lesson — spec ⊑FD impl

The "external choice refines internal choice" lesson at the body level: the
specification (internal choice) FD-refines the implementation (external choice),
lifted under the `coin` prefix.

```agda
canonical-lesson-✓ : VM_body_spec ⊑FD VM_body_impl
canonical-lesson-✓ =
  ⟶₀-mono-⊑FD coin (⊓⊑FD□ (tea ⟶₀ Skip) (coffee ⟶₀ Skip))
```

### §5.3 (reverse) Body-level FD strictness — impl ⋢FD spec

The reverse direction fails. We exhibit a refusal that the spec admits but
the impl does not: after firing `coin`, the spec can resolve the inner `⊓`
into the coffee branch and thereby refuse the `tea` event; the impl
cannot refuse `tea` because its `□` still offers both events.

These imports bring the LTS step/event constructors, the (stable) refusals
and failures-divergences machinery, the `⊓` τ-step lemmas, and the
`Prefix-cont` reduction lemma into scope for the strictness proof.

```agda
open import Semantics.LTS {E = VM} {I = ExtI VM} hiding (Diverges)
  using (_─[_]─►_; sRet; sSil; sVis; sTau; ev; τ; Event√; evl; evLabel; √)
open import Semantics.Failures {E = VM} {I = ExtI VM}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Refusals {E = VM} {I = ExtI VM}
  using (Refuses; Offers)
open import Semantics.DRBisim {E = VM} {I = ExtI VM}
  using (Diverges)
open import Semantics.DRImpliesFD {E = VM} {I = ExtI VM}
  using (stable-no-τ)
open import Semantics.FailuresDivergences {E = VM} {I = ExtI VM}
  using (failures⊥; divergences; IsDivergence)
open import CSP.Laws.Bisim.Laws VM-AnyTypes-≟ using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.Traces.TraceLaws VM-AnyTypes-≟ using (Prefix-cont-just)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (case_of_)
```

We first record that the implementation never diverges: each reachable
state (`VM_body_impl`, then `tea □ coffee`, then `Skip`, then `deadlock`)
performs no τ-move, so the big-step witness of any alleged divergence
cannot in fact diverge.

```agda
private
  -- No τ from VM_body_impl = react (Prefix-cont coin _) ∅t (τc = ∅t).
  no-τ-impl : ∀ {Q} → VM_body_impl ─[ τ ]─► Q → ⊥
  no-τ-impl (sTau refl ())

  -- (tea □ coffee) is stable: its τc (□-mt of two ∅t nodes) is everywhere
  -- nothing.  We mirror □-mt's clause structure: split on the index head and
  -- (for `pair fin i`) the tag; in the fzero/fsuc-fzero cases □-mt does a
  -- `with viewT (react _ ∅t) … = with ∅t …`, which reduces to nothing.
  □-isStable : isStable ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))
  □-isStable (_ , base _)            _ = refl
  □-isStable (_ , fin)               _ = refl
  □-isStable (_ , pair (base _) _)   _ = refl
  □-isStable (_ , pair (pair _ _) _) _ = refl
  □-isStable (_ , pair fin i) (lift fzero , a)        = refl
  □-isStable (_ , pair fin i) (lift (fsuc fzero) , a) = refl
  □-isStable (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

  -- No τ from Skip = Ret tt (force = ret tt).  We pin the return type to
  -- ⊤ {lzero} (Skip and deadlock are level-polymorphic).
  no-τ-Skip : ∀ {Q} → Skip {lzero} ─[ τ ]─► Q → ⊥
  no-τ-Skip (sSil ())

  -- No τ from deadlock.
  no-τ-deadlock : ∀ {Q} → deadlock {R = ⊤ {lzero}} ─[ τ ]─► Q → ⊥
  no-τ-deadlock (sSil ())
  no-τ-deadlock (sTau refl ())

  -- Mutually-recursive no-τ helpers, one per reachable layer.  Forward
  -- declarations first (per the project's no-mutual-block convention).
  -- The big-step chain itself contains τ-steps (⟹-τ); each is refuted at
  -- the current node, so the chain can only advance by ev-steps.
  no-τ-from-reachable :
    ∀ {s} {P Q} → VM_body_impl ⟹⟨ s ⟩ P → P ─[ τ ]─► Q → ⊥
  no-τ-Skip-reach : ∀ {s} {P Q} → Skip {lzero} ⟹⟨ s ⟩ P → P ─[ τ ]─► Q → ⊥
  no-τ-dead-reach : ∀ {s} {P Q} → deadlock {R = ⊤ {lzero}} ⟹⟨ s ⟩ P → P ─[ τ ]─► Q → ⊥
  no-τ-layer1 :
    ∀ {s} {P Q} → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ⟹⟨ s ⟩ P → P ─[ τ ]─► Q → ⊥
  no-τ-after-□ :
    ∀ {s} {t′ P Q} (at : AnyTypes VM) {a : proj₁ at}
    → mergeVis (Prefix-cont tea (λ _ → Skip)) (Prefix-cont coffee (λ _ → Skip)) at a
        ≡ just t′
    → t′ ⟹⟨ s ⟩ P → P ─[ τ ]─► Q → ⊥

  -- Layer at Skip
  no-τ-Skip-reach ⟹-refl       step = no-τ-Skip step
  no-τ-Skip-reach (⟹-τ τs _)   _    = no-τ-Skip τs
  no-τ-Skip-reach (⟹-ev (sRet refl) rest) step = no-τ-dead-reach rest step
  -- Layer at deadlock (after a √-step)
  no-τ-dead-reach ⟹-refl     step = no-τ-deadlock step
  no-τ-dead-reach (⟹-τ τs _) _    = no-τ-deadlock τs
  no-τ-dead-reach (⟹-ev (sRet eq) _) _ = case eq of λ ()
  no-τ-dead-reach (⟹-ev (sVis refl br) _) _ = case br of λ ()
  -- Layer at (tea □ coffee): stable, so only ev-steps (tea/coffee → Skip) advance.
  no-τ-layer1 ⟹-refl     step = stable-no-τ □-isStable step
  no-τ-layer1 (⟹-τ τs _) _    = stable-no-τ □-isStable τs
  no-τ-layer1 (⟹-ev (sVis {at = at} refl eq-j) rest) step =
    no-τ-after-□ at eq-j rest step
  -- After an ev-step from (tea □ coffee): the target is Skip (whichever drink fired).
  no-τ-after-□ at eq-j rest step
    with VM-AnyTypes-≟ (⊤ , tea) at
  ... | yes refl with eq-j
  ...   | refl = no-τ-Skip-reach rest step
  no-τ-after-□ at eq-j rest step
    | no _ with VM-AnyTypes-≟ (⊤ , coffee) at
  ...   | yes refl with eq-j
  ...     | refl = no-τ-Skip-reach rest step
  no-τ-after-□ at eq-j rest step
    | no _ | no _ = case eq-j of λ ()
  -- Top layer at VM_body_impl: pure-vis coin, then descend into (tea □ coffee).
  no-τ-from-reachable ⟹-refl     step = no-τ-impl step
  no-τ-from-reachable (⟹-τ τs _) _    = no-τ-impl τs
  no-τ-from-reachable (⟹-ev (sVis {at = at} refl eq-j) rest) step
    with VM-AnyTypes-≟ (⊤ , coin) at
  ... | no _    = case eq-j of λ ()
  ... | yes refl with eq-j
  ...   | refl = no-τ-layer1 rest step

VM_body_impl-no-div : ∀ {s} → divergences VM_body_impl s → ⊥
VM_body_impl-no-div d =
  no-τ-from-reachable
    (d .IsDivergence.reach)
    (d .IsDivergence.divwit .Diverges.step)
```

The refusal predicate asks the process to refuse the `tea` event.

```agda
-- `failures⊥`/`_⊑F⊥_` quantify the refusal set `B` at the return-type level
-- `ℓr`, which is `lzero` here (R = ⊤ {lzero}), so the codomain lives in `Set`.
RefusesTea : Event√ (⊤ {lzero}) → Set lzero
RefusesTea (evl (evLabel A tea a)) = ⊤ {lzero}
RefusesTea _                       = ⊥

private
  -- coffee ⟶₀ Skip is stable, and any visible step from it carries the
  -- coffee event — not tea.  So it refuses every tea-labelled event.
  coffee-refuses-tea : ∀ e → RefusesTea e → ¬ Offers (coffee ⟶₀ Skip) e
  coffee-refuses-tea (evl (evLabel A tea a)) _ (_ , sVis {at = at} refl eq-j)
    with VM-AnyTypes-≟ (⊤ , coffee) at
  ... | yes ()
  ... | no  _  = case eq-j of λ ()
  coffee-refuses-tea (evl (evLabel A coffee a)) () _
  coffee-refuses-tea (evl (evLabel A coin   a)) () _
  coffee-refuses-tea (√ _)                      () _

  -- coffee ⟶₀ Skip is stable (vis-shaped, τc = ∅t).
  coffee-stable : isStable (coffee ⟶₀ Skip {lzero})
  coffee-stable _ _ = refl

fail-coin-refuses-tea
  : failures⊥ VM_body_spec (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea
fail-coin-refuses-tea =
  -- Fire coin, τ-resolve the ⊓ into the coffee branch (⊓-stepR), which is
  -- stable and refuses tea.
  inj₁ ( coffee ⟶₀ Skip
       , ⟹-ev (sVis {at = ⊤ , coin} {a = tt} refl
                     (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip)) tt))
              (⟹-τ (⊓-stepR _ _) ⟹-refl)
       , coffee-stable , coffee-refuses-tea
       )

private
  -- (tea □ coffee) CAN fire tea, so it cannot refuse RefusesTea.
  □-offers-tea : Offers ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) (evl (evLabel ⊤ tea tt))
  □-offers-tea =
    Skip , sVis {at = ⊤ , tea} {a = tt} refl
                (cong (λ x → mergeMaybe x nothing)
                      (Prefix-cont-just tea (λ _ → Skip) tt))

  -- Decompose a big-step from (tea □ coffee) along the empty trace: force is
  -- a stable react (vis), so τ is impossible and only ⟹-refl remains; then
  -- the stable refusal is contradicted by the available tea-offer.
  go-inner : ∀ {P′} → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ⟹⟨ [] ⟩ P′
           → Refuses P′ RefusesTea → ⊥
  go-inner ⟹-refl     (_ , noev) = noev (evl (evLabel ⊤ tea tt)) tt □-offers-tea
  go-inner (⟹-τ τs _) _          = stable-no-τ □-isStable τs

no-such-failure-impl
  : failures⊥ VM_body_impl (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea → ⊥
-- Divergence case: impl never diverges.
no-such-failure-impl (inj₂ d) = VM_body_impl-no-div d
-- Failure case: decompose the big-step, reach (tea □ coffee), derive contradiction.
no-such-failure-impl (inj₁ (P′ , bigstep , ref)) = go bigstep ref
  where
    go : ∀ {P′} → VM_body_impl ⟹⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩ P′
       → Refuses P′ RefusesTea → ⊥
    -- τ from VM_body_impl is impossible: pure-vis node.
    go (⟹-τ τs _) _ = no-τ-impl τs
    -- ev-step: fire coin, reach the inner □-state, then go-inner.
    go (⟹-ev (sVis {at = at} refl eq-j) rest) ref′
      with VM-AnyTypes-≟ (⊤ , coin) at
    ... | no  neq = ⊥-elim (neq refl)
    ... | yes refl with eq-j
    ...   | refl = go-inner rest ref′

canonical-lesson-✗ : VM_body_impl ⊑FD VM_body_spec → ⊥
canonical-lesson-✗ refines =
  no-such-failure-impl (proj₁ refines fail-coin-refuses-tea)
```

### §5.3b Loop-level FD refinement — `VM_spec ⊑FD VM_impl`

The body-level lesson `canonical-lesson-✓` lifts through `loop0` by
refinement-monotonicity of iteration (`loop0-mono-⊑FD`): wrapping both bodies
in the never-returning loop preserves the FD-refinement.

```agda
open import CSP.Laws.FD.IterateMonoFD VM-AnyTypes-≟ using (loop0-mono-⊑FD)

VM_spec⊑FD-VM_impl : VM_spec ⊑FD VM_impl
VM_spec⊑FD-VM_impl = loop0-mono-⊑FD VM_body_spec VM_body_impl canonical-lesson-✓
```

### §5.3c Loop-level FD strictness — `VM_impl ⋢FD VM_spec`

The reverse direction fails at the loop level too. We lift the body
counterexample (`canonical-lesson-✗`) through one `loop0` layer. The spec
loop admits a `coin`-then-refuse-`tea` failure (resolve the inner `⊓` to
coffee inside the first iteration); the impl loop never does, because its
external choice still offers `tea` after `coin`.

We reuse the `iter-bind`/`>>=` refusal- and run-transport helpers proved
generically inside `IterateMonoFD`/`IterateFD`/`BindFD`, and the loop0
failures-divergences characterisation.

```agda
open import CSP.Laws.FD.IterateFD VM-AnyTypes-≟
  using ( loop0-failures⊥-elim; loop0-failures⊥-intro-failures
        ; LoopFailureSplit; loop-fail; LoopSplit; loopStep; loop-k
        ; loop0-div-elim; LoopDivergenceSplit; loop-div )
open import CSP.Laws.FD.IterateMonoFD VM-AnyTypes-≟
  using ( banEvl
        ; refuses-iter-intro; refuses-bind-intro
        ; refuses-iter-elim; refuses-bind-elim
        ; body-terminates; bind-loopk-Diverges→
        ; ret-stuck; ⟹-then-τ* )
open import CSP.Laws.FD.BindFD VM-AnyTypes-≟
  using (BindSplit; bind-bigstep-inv; lift-bind-bigstep; evl-split)
open import Semantics.FailuresDivergences {E = VM} {I = ExtI VM}
  using (empty-div)
open import Semantics.WeakBisim {E = VM} {I = ExtI VM} using (_─[τ*]─►_; τ*-refl; τ*-step)
open import CSP.Laws.FD.IterateFD VM-AnyTypes-≟ using (loop-Diverges→; loop-back-sil)
open import CSP.Laws.FD.IterateMonoFD VM-AnyTypes-≟ using (map-evl-inj)
open import Data.List using (map; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Level using (lower)
open import Semantics.LTS {E = VM} {I = ExtI VM} using (τ-inv; ev-inv; Event)
open IsDivergence
```

The loop-level ban set bans the `tea` event; it is carrier-agnostic (events
are independent of the return type), so it mirrors the body-level `RefusesTea`.

```agda
RefusesTea⊥ : Event√ ⊥ → Set lzero
RefusesTea⊥ (evl (evLabel A tea a)) = ⊤ {lzero}
RefusesTea⊥ _                       = ⊥
```

**The spec loop's witness.** Inside the first iteration the spec fires
`coin`, τ-resolves the `⊓` into the (stable, tea-refusing) `coffee ⟶₀ Skip`
state, which is the body run already recorded in `fail-coin-refuses-tea`.
We lift that body run through `>>= loop-k` and re-wrap it as the `in-body`
arm of a `LoopSplit`, pushing the body refusal forward through the
`>>= loop-k` and `iter-bind` layers.

```agda
private
  -- The body run from `fail-coin-refuses-tea`, made explicit.
  spec-body-run :
    VM_body_spec ⟹⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩ (coffee ⟶₀ Skip)
  spec-body-run =
    ⟹-ev (sVis {at = ⊤ , coin} {a = tt} refl
                (Prefix-cont-just coin (λ _ → (tea ⟶₀ Skip) ⊓ (coffee ⟶₀ Skip)) tt))
         (⟹-τ (⊓-stepR _ _) ⟹-refl)

  -- The body refusal `Refuses (coffee ⟶₀ Skip) RefusesTea`, retagged to the
  -- nested `banEvl` shape demanded by `refuses-bind-intro`.  The nested ban
  -- set agrees with `RefusesTea⊥` on visible events (only `tea` banned) and
  -- bans no `√`.
  coffee-refuses-tea-ban :
    Refuses (coffee ⟶₀ Skip {lzero})
      (banEvl {X = ⊤ {lzero}} (λ e →
         banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e′ → RefusesTea⊥ (evl e′)) (evl e)))
  coffee-refuses-tea-ban = coffee-stable , no-off
    where
      no-off : ∀ e
        → banEvl {X = ⊤ {lzero}} (λ e →
            banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e′ → RefusesTea⊥ (evl e′)) (evl e)) e
        → ¬ Offers (coffee ⟶₀ Skip {lzero}) e
      no-off (evl (evLabel A tea a)) _ (_ , sVis {at = at} refl eq-j)
        with VM-AnyTypes-≟ (⊤ , coffee) at
      ... | yes ()
      ... | no  _  = case eq-j of λ ()
      no-off (evl (evLabel A coffee a)) () _
      no-off (evl (evLabel A coin   a)) () _

spec-loop-fail
  : failures⊥ VM_spec (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea⊥
spec-loop-fail =
  loop0-failures⊥-intro-failures VM_body_spec
    (loop-fail
      (LoopSplit.in-body {vs = evLabel ⊤ coin tt ∷ []}
        (lift-bind-bigstep VM_body_spec (coffee ⟶₀ Skip) loop-k
                           (evLabel ⊤ coin tt ∷ []) spec-body-run)
        refl)
      (refuses-iter-intro {k = loopStep VM_body_spec}
        {Q = (coffee ⟶₀ Skip) >>= loop-k} {B = RefusesTea⊥}
        (refuses-bind-intro {k = loop-k} {Q = coffee ⟶₀ Skip}
          {B = banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e′ → RefusesTea⊥ (evl e′))}
          coffee-refuses-tea-ban)))
```

**The impl loop has no such failure.** Decompose a hypothetical
`failures⊥ VM_impl [coin] RefusesTea⊥` with `loop0-failures⊥-elim`. The
divergence arm is impossible (the impl loop never diverges); the failure arm
peels back — through the `iter-bind`/`>>=` layers — to a body run reaching
`(tea □ coffee)`, which offers `tea` and so cannot refuse it.

First, the body never reaches a returning (`ret tt`) state on a visible
trace of length `≤ 1`: after `coin` it sits in the stable `(tea □ coffee)`
react, never a return. This is the obstruction to both a silent loop-back
and a divergence on the single-`coin` trace.

```agda
private
  -- `VM_body_impl` cannot reach `ret tt` on `[]` or on `[coin]`.  We descend
  -- through the (τ-free) reachable layers, mirroring `no-τ-from-reachable`.
  body-no-term-[] : ∀ {Bᵣ} → VM_body_impl ⟹⟨ [] ⟩ Bᵣ → force Bᵣ ≡ ret tt → ⊥
  body-no-term-[] ⟹-refl       ()
  body-no-term-[] (⟹-τ τs _) _ = no-τ-impl τs

  body-no-term-[coin] : ∀ {Bᵣ}
    → VM_body_impl ⟹⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩ Bᵣ → force Bᵣ ≡ ret tt → ⊥
  body-no-term-[coin] (⟹-τ τs _) _ = no-τ-impl τs
  body-no-term-[coin] (⟹-ev (sVis {at = at} refl eq-j) rest) fe
    with VM-AnyTypes-≟ (⊤ , coin) at
  ... | no  neq  = ⊥-elim (neq refl)
  ... | yes refl with eq-j
  ...   | refl = go-□ rest fe
    where
      -- after coin we are at (tea □ coffee); on the empty residual trace it
      -- stays a stable react (no τ, no ev), never a `ret tt`.
      go-□ : ∀ {Bᵣ} → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ⟹⟨ [] ⟩ Bᵣ
           → force Bᵣ ≡ ret tt → ⊥
      go-□ ⟹-refl       ()
      go-□ (⟹-τ τs _) _ = stable-no-τ □-isStable τs
```

The body-side obstruction to a loop-back / divergence on `≤ 1` visible
events: a complete iteration (`loopStep VM_body_impl tt` silently reaching a
`ret (inj₁ tt)` loop-back) would force the body to terminate on the same
trace, contradicting the above.

```agda
private
  loopback-absurd-short : ∀ {vs} {Pᵣ : PTree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
    → (vs ≡ [] ⊎ vs ≡ evLabel ⊤ coin tt ∷ [])
    → (loopStep VM_body_impl tt) ⟹⟨ map evl vs ⟩ Pᵣ → force Pᵣ ≡ ret (inj₁ tt) → ⊥
  loopback-absurd-short {vs} short run fe with body-terminates VM_body_impl run fe
  ... | (Bᵣ , bodyrun , feB) with short
  ...   | inj₁ refl = body-no-term-[]     bodyrun feB
  ...   | inj₂ refl = body-no-term-[coin] bodyrun feB
```

Now the divergence refutation.  A divergence of `loop0 VM_body_impl` at the
single-`coin` trace decomposes (via `loop0-div-elim`) into a `LoopSplit`-reached
diverging state; we case on the split and on `loop-Diverges→`.  Every branch
collapses: the body never diverges, and it never loops back on `≤ 1` events.

```agda
private
  -- a reachable body state `P″` with `Diverges P″` contradicts non-divergence.
  body-reach-no-div : ∀ {vs} {P″}
    → VM_body_impl ⟹⟨ map evl vs ⟩ P″ → Diverges P″ → ⊥
  body-reach-no-div {vs} run dv =
    VM_body_impl-no-div (record
      { prefix = map evl vs ; suffix = [] ; split = sym (++-identityʳ _)
      ; witness = _ ; reach = run ; divwit = dv })

  -- the bound: a `LoopSplit`/divergence prefix `vs` of `[coin]` is `[]` or `[coin]`.
  short-prefix : ∀ {ℓr} {R : Set ℓr} (vs : List Event) {s₂ : List (Event√ R)}
    → evl (evLabel ⊤ coin tt) ∷ [] ≡ map evl vs ++ s₂
    → (vs ≡ [] ⊎ vs ≡ evLabel ⊤ coin tt ∷ [])
  short-prefix []              eq = inj₁ refl
  short-prefix (v ∷ [])      {s₂} eq with hd-inj eq
    where hd-inj : evl (evLabel ⊤ coin tt) ∷ [] ≡ evl v ∷ s₂ → v ≡ evLabel ⊤ coin tt
          hd-inj refl = refl
  ... | refl = inj₂ refl
  short-prefix (v ∷ v₂ ∷ vs) ()

  -- divergence of one in-progress iteration, source reached on `vs ⊆ [coin]`.
  iter-div-absurd : ∀ {vs} {P′ : PTree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
    → (vs ≡ [] ⊎ vs ≡ evLabel ⊤ coin tt ∷ [])
    → (loopStep VM_body_impl tt) ⟹⟨ map evl vs ⟩ P′
    → Diverges (iter-bind P′ (loopStep VM_body_impl)) → ⊥
  iter-div-absurd {vs} {P′} short run dv
    with loop-Diverges→ VM_body_impl P′ dv
  ... | inj₁ dP′ = peel (map evl vs) refl dP′ (bind-bigstep-inv VM_body_impl loop-k run)
    where
      peel : ∀ {P′} (s : List (Event√ (⊤ {lzero} ⊎ ⊥))) → s ≡ map evl vs
           → Diverges P′ → BindSplit VM_body_impl loop-k P′ s → ⊥
      peel .(map evl vs₀) seq dP (BindSplit.in-P {P′ = P″} {vs = vs₀} runB refl)
        with map-evl-inj-local seq
        where map-evl-inj-local : ∀ {xs : List Event} → map evl xs ≡ map evl vs → xs ≡ vs
              map-evl-inj-local {xs} e = map-evl-inj e
      ... | refl = body-reach-no-div runB (bind-loopk-Diverges→ P″ dP)
      peel {P′} .(map evl s₁ ++ s₂) seq dP
           (BindSplit.in-k {r = tt} {s₁ = s₁} {s₂ = s₂} runB eqr kr)
        with evl-split (map evl s₁) vs s₂ (sym seq)
      ...   | vs₁ , vs₂ , _ , refl , _ =
              ret-div-absurd (ret-stuck {Q = loop-k tt} {x = inj₁ tt} vs₂ refl kr) dP
        where ret-div-absurd : ∀ {x} → force P′ ≡ ret x → Diverges P′ → ⊥
              ret-div-absurd ef dp with τ-inv (dp .Diverges.step)
              ... | inj₁ ef′                       with () ← trans (sym ef) ef′
              ... | inj₂ (_ , _ , _ , _ , ef′ , _) with () ← trans (sym ef) ef′
  ... | inj₂ (Qᵣ , silr , feQ , _) =
        loopback-absurd-short short (⟹-then-τ* run silr) feQ

  VM_impl-no-div : divergences VM_impl (evl (evLabel ⊤ coin tt) ∷ []) → ⊥
  VM_impl-no-div d with loop0-div-elim VM_body_impl d
  ... | loop-div {prefix = .(map evl vs)} eq (LoopSplit.in-body {P′ = P′} {vs = vs} bs refl) dvQ
        with short-prefix vs eq
  ...     | short = iter-div-absurd short bs dvQ
  VM_impl-no-div d
      | loop-div {prefix = .(map evl s₁ ++ s₂)} eq
          (LoopSplit.in-loop {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe cont) dvQ
        with short-prefix s₁ (trans eq (++-assoc (map evl s₁) s₂ _))
  ...     | short = loopback-absurd-short short bs fe
```

The failure arm.  Peel the loop failure split back to the body's
`(tea □ coffee)` state and reuse the body-level `go-inner`/`□-offers-tea`
contradiction (the impl offers `tea`, so it cannot refuse it).

```agda
private
  -- the in-body failure arm: a refusing state reached on `[coin]`.
  loop-fail-in-body-absurd
    : ∀ {P′ : PTree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)}
    → (loopStep VM_body_impl tt) ⟹⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩ P′
    → Refuses (iter-bind P′ (loopStep VM_body_impl)) RefusesTea⊥ → ⊥
  loop-fail-in-body-absurd {P′} run ref =
    peel (map evl (evLabel ⊤ coin tt ∷ [])) refl
         (refuses-iter-elim {Q = P′} ref)
         (bind-bigstep-inv VM_body_impl loop-k run)
    where
      peel : ∀ {P′} (s : List (Event√ (⊤ {lzero} ⊎ ⊥))) → s ≡ evl (evLabel ⊤ coin tt) ∷ []
           → Refuses P′ (banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e → RefusesTea⊥ (evl e)))
           → BindSplit VM_body_impl loop-k P′ s → ⊥
      -- in-P: body reaches `(tea □ coffee)` on [coin]; reuse go-inner.
      peel .(map evl vs₀) seq ref₁ (BindSplit.in-P {P′ = P″} {vs = vs₀} runB refl)
        with eq-coin vs₀ seq
        where eq-coin : ∀ (xs : List Event) → map evl xs ≡ evl (evLabel ⊤ coin tt) ∷ []
                      → xs ≡ evLabel ⊤ coin tt ∷ []
              eq-coin (x ∷ []) refl = refl
              eq-coin []           ()
              eq-coin (x ∷ _ ∷ _)  ()
      ... | refl = go-body runB
                     (refuses-bind-elim {k = loop-k} {Q = P″}
                       {B = banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e → RefusesTea⊥ (evl e))}
                       (bind-stable-from P″ (proj₁ ref₁)) ref₁)
        where
          -- a stable `P″ >>= loop-k` forces `P″` stable (inline of bind-stable-elim).
          bind-stable-from : ∀ (Q : PTree VM (ExtI VM) (⊤ {lzero}))
                           → isStable (Q >>= loop-k {R = ⊥}) → isStable Q
          bind-stable-from Q st with PTree.force Q in eqQ
          ... | ret r      = ⊥-elim (lower st)
          ... | sil c      = ⊥-elim (lower st)
          ... | react v τc = bindT-nil
            where
              st-react : ∀ i a → bindT loop-k (react v τc) i a ≡ nothing
              st-react = st
              bindT-nil : ∀ i a → τc i a ≡ nothing
              bindT-nil i a with τc i a in vt
              ... | nothing  = refl
              ... | just t″  = ⊥-elim (jn (trans (sym (bj i a vt)) (st-react i a)))
                where bj : ∀ i a → τc i a ≡ just t″
                         → bindT loop-k (react v τc) i a ≡ just (t″ >>= loop-k)
                      bj i a e with τc i a | e
                      ... | just _ | refl = refl
                      jn : ∀ {ℓx} {X : Set ℓx} {x : X} → just x ≡ nothing → ⊥
                      jn ()
          -- the body reaches `(tea □ coffee)` and refuses `RefusesTea⊥`'s retag:
          -- contradict via the available tea-offer (go-inner reasoning).
          go-body : ∀ {P″}
            → VM_body_impl ⟹⟨ evl (evLabel ⊤ coin tt) ∷ [] ⟩ P″
            → Refuses P″ (banEvl {X = ⊤ {lzero}}
                 (λ e → banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e′ → RefusesTea⊥ (evl e′)) (evl e)))
            → ⊥
          go-body (⟹-τ τs _) _ = no-τ-impl τs
          go-body (⟹-ev (sVis {at = at} refl eq-j) rest) ref′
            with VM-AnyTypes-≟ (⊤ , coin) at
          ... | no  neq = ⊥-elim (neq refl)
          ... | yes refl with eq-j
          ...   | refl = go-inner-□ rest ref′
            where
              -- (tea □ coffee) on empty residual: refl gives the stable refusal,
              -- contradicted by the tea-offer; τ is impossible (stable).
              go-inner-□ : ∀ {P‴}
                → ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)) ⟹⟨ [] ⟩ P‴
                → Refuses P‴ (banEvl {X = ⊤ {lzero}}
                    (λ e → banEvl {X = ⊤ {lzero} ⊎ ⊥} (λ e′ → RefusesTea⊥ (evl e′)) (evl e)))
                → ⊥
              go-inner-□ ⟹-refl     (_ , noev) =
                noev (evl (evLabel ⊤ tea tt)) tt □-offers-tea
              go-inner-□ (⟹-τ τs _) _ = stable-no-τ □-isStable τs
      -- in-k: body terminates on a prefix of [coin] then runs `loop-k`; the
      -- target P′ forces `ret (inj₁ tt)`, which is not stable — absurd refusal.
      peel {P′} .(map evl s₁ ++ s₂) seq ref₁
           (BindSplit.in-k {r = tt} {s₁ = s₁} {s₂ = s₂} runB eqr kr)
        with evl-split (map evl s₁) (evLabel ⊤ coin tt ∷ []) s₂ (sym seq)
      ...   | vs₁ , vs₂ , _ , refl , _ =
              ret-not-stable-local (ret-stuck {Q = loop-k tt} {x = inj₁ tt} vs₂ refl kr)
                                   (proj₁ ref₁)
        where ret-not-stable-local : ∀ {x} → force P′ ≡ ret x → isStable P′ → ⊥
              ret-not-stable-local ef st with force P′ | ef
              ... | ret r | refl = lower st

private
  -- `[coin] ≡ map evl vs` forces `vs ≡ [coin]`.
  coin≡map-evl : ∀ (vs : List Event)
               → evl {R = ⊥} (evLabel ⊤ coin tt) ∷ [] ≡ map evl vs
               → vs ≡ evLabel ⊤ coin tt ∷ []
  coin≡map-evl (v ∷ []) refl = refl
  coin≡map-evl []           ()
  coin≡map-evl (v ∷ _ ∷ _)  ()

  -- Worker on a `LoopSplit` carried at a GENERIC trace `s` (with `s ≡ [coin]`
  -- separate), so the `in-body`/`in-loop` trace index stays a free variable
  -- and unifies cleanly (mirrors `in-body-map′`/`peel-body`).
  loop-fail-absurd : ∀ {Q : PTree VM (ExtI VM) ⊥} (s : List (Event√ ⊥))
    → s ≡ evl (evLabel ⊤ coin tt) ∷ []
    → LoopSplit VM_body_impl Q s → Refuses Q RefusesTea⊥ → ⊥
  loop-fail-absurd .(map evl vs) seq (LoopSplit.in-body {P′ = P′} {vs = vs} bs refl) ref
    with coin≡map-evl vs (sym seq)
  ... | refl = loop-fail-in-body-absurd bs ref
  loop-fail-absurd .(map evl s₁ ++ s₂) seq
                   (LoopSplit.in-loop {s₁ = s₁} {s₂ = s₂} {Pᵣ = Pᵣ} bs fe cont) ref
    with short-prefix s₁ (sym seq)
  ... | short = loopback-absurd-short short bs fe

no-such-loop-failure-impl
  : failures⊥ VM_impl (evl (evLabel ⊤ coin tt) ∷ []) RefusesTea⊥ → ⊥
no-such-loop-failure-impl fl with loop0-failures⊥-elim VM_body_impl fl
... | inj₂ d = VM_impl-no-div d
... | inj₁ (loop-fail sp ref) = loop-fail-absurd _ refl sp ref

loop-lesson-✗ : VM_impl ⊑FD VM_spec → ⊥
loop-lesson-✗ refines =
  no-such-loop-failure-impl (proj₁ refines spec-loop-fail)
```



### §5.4 LTL on a sample trace

We illustrate LTL safety and liveness on a finite witness trace of
`VM_body_impl`. Following the LTL module's v1 limits, we work at the
witness-trace level (`⟦ φ ⟧ tr`) rather than at the satisfaction level
(`t ⊨ φ`), which would need trace-uniqueness lemmas the LTL module
defers to v2.

```agda
open import Data.List using (List; []; _∷_; _++_; [_]; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using () renaming (tt to tt₀)

open import Semantics.LTL.Traces_Based {E = VM} {I = ExtI VM}
  using ( LTLᵗ; atom; ⟦_⟧; G_; F_; X_; _⇒_; _U_; _∧_; atDone
        ; Frame; Trace; ∞Trace; step; done; stuck
        ; ⟦G⟧⁺; ⟦G⟧⁺⇒⟦G⟧; tail; drop; drop-stutter; dropIdx-stutter; frameOf )
  renaming (¬_ to ¬ᵗ_)
open ∞Trace

-- LTS step/event constructors (_─[_]─►_, sVis, ev, evl, evLabel) are already
-- in scope from the §5.3 imports above.
open import Semantics.WeakBisim {E = VM} {I = ExtI VM}   using (_═[_]═►_; wev)
```

The VM-specific atoms react only to event shape; they are polymorphic in
the trace's return type so the same atom set works for body-level
(`R = ⊤`) and (hypothetical) loop-level (`R = ⊥`) traces.

```agda
atCoin : ∀ {R : Set lzero} → LTLᵗ lzero R
atCoin = atom λ
  { (step _ (evl (evLabel _ coin _)))   → ⊤ {lzero}
  ; _                                    → ⊥ }

atTea : ∀ {R : Set lzero} → LTLᵗ lzero R
atTea = atom λ
  { (step _ (evl (evLabel _ tea _)))    → ⊤ {lzero}
  ; _                                    → ⊥ }

atCoffee : ∀ {R : Set lzero} → LTLᵗ lzero R
atCoffee = atom λ
  { (step _ (evl (evLabel _ coffee _))) → ⊤ {lzero}
  ; _                                    → ⊥ }

atDrink : ∀ {R : Set lzero} → LTLᵗ lzero R
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
-- force (P □ Q) | react vP _ | react vQ _ = react (mergeVis vP vQ) _.
-- mergeVis at (⊤,coffee) a = mergeMaybe nothing (just Skip) = just Skip,
-- since Prefix-cont tea _ (⊤,coffee) a = nothing definitionally (tea ≠ coffee).
private
  sampleTrace-□-coffee-step : ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))
                ─[ ev (evl (evLabel ⊤ coffee tt)) ]─► Skip
  sampleTrace-□-coffee-step =
    sVis {at = ⊤ , coffee} {a = tt} refl
         (cong (mergeMaybe nothing)
               (refl {x = just (Skip)}))

sampleTrace : Trace (⊤ {lzero}) VM_body_impl
sampleTrace =
  step (wev {p = VM_body_impl} τ*-refl
                (sVis {at = ⊤ , coin} {a = tt} refl
                      (refl {x = just ((tea ⟶₀ Skip) □ (coffee ⟶₀ Skip))}))
                τ*-refl)
       (record { force =
  step (wev τ*-refl sampleTrace-□-coffee-step τ*-refl) (record { force =
  done {t = Skip} refl }) })
```

**Safety**: after every coin event, the very next observation is a drink.

```agda
safetyFormula : LTLᵗ lzero (⊤ {lzero})
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
      subst (⟦_⟧ {R = ⊤ {lzero}} (atCoin ⇒ X atDrink))
            (sym (drop-stutter n (done {t = Skip} refl) tt₀))
            (doneφ n)
      where
        -- At the stuttering `done` frame, ⟦ atCoin ⟧ = ⊥ and ⟦ X atDrink ⟧ = ⊥.
        -- The proof inhabits ⟦ φ ⟧ at the subst-transported done trace, which
        -- is drop-stutter's RHS. dropIdx-stutter (suc n) (done refl) reduces to
        -- dropIdx-stutter n (done refl) definitionally, so the (suc n) goal is
        -- the (n) goal — discharge by induction on n.
        doneφ : (n : ℕ)
              → ⟦_⟧ {R = ⊤ {lzero}} (atCoin ⇒ X atDrink)
                    (subst (Trace (⊤ {lzero}))
                           (sym (dropIdx-stutter n (done {t = Skip} refl) tt₀))
                           (done {t = Skip} refl))
        doneφ zero    = λ (notnotCoin , _) → notnotCoin (λ x → ⊥-elim x)
        doneφ (suc n) = doneφ n
```

**Liveness**: a coffee event occurs.

```agda
livenessFormula : LTLᵗ lzero (⊤ {lzero})
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
avoid the clash with `Relation.Nullary.¬_` already in scope — done in the
§5.4 `open` above.)

```agda
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
      subst (⟦_⟧ {R = ⊤ {lzero}} (¬ᵗ atTea))
            (sym (drop-stutter n (done {t = Skip} refl) tt₀))
            (doneφ n)
      where
        doneφ : (n : ℕ)
              → ⟦_⟧ {R = ⊤ {lzero}} (¬ᵗ atTea)
                    (subst (Trace (⊤ {lzero}))
                           (sym (dropIdx-stutter n (done {t = Skip} refl) tt₀))
                           (done {t = Skip} refl))
        doneφ zero    = λ ()
        doneφ (suc n) = doneφ n
```

**(e) Liveness culminating in termination.** Eventually a `coffee` is
served, immediately after which the machine is `done` — combining `F`,
`∧`, `X`, and the `done` terminator in a single formula.

```agda
coffeeThenDone : ⟦ F (atCoffee ∧ X (atDone (λ _ → ⊤ {lzero}))) ⟧ sampleTrace
coffeeThenDone = 1 , (tt , tt) , (λ _ _ → lift tt₀)
```

### §5.5 What is intentionally deferred

The loop-level FD refinement (`VM_spec ⊑FD VM_impl`, §5.3b) and its
strictness counterpart (`VM_impl ⋢FD VM_spec`, §5.3c) are now **proved**
above, lifting the body-level lesson through `loop0` via the iteration law
infrastructure (`CSP.Laws.FD.IterateMonoFD` / `IterateFD` / `BindFD`).
What remains deferred:

- **`_⊨_`-shaped LTL claims (body *and* loop level).** These are now all
  **discharged** in the sibling module
  `CSP.Examples.VendingMachine.VendingMachine_LTL_Sat`, using a re-indexed
  `Trace` type that bakes in coherence (the root process is part of the
  type), giving trace inversion for free.  At the *body* level (`R = ⊤`) the
  proved theorems are:
  - `vm-safety   : VM_body_impl ⊨ G (atCoin ⇒ X atDrink)`
  - `vm-liveness : VM_body_impl ⊨ F atDrink`
  - `vm-until    : VM_body_impl ⊨ (atCoin U atDrink)`
  - `vm-terminates : VM_body_impl ⊨ F (atDone (λ _ → ⊤) ∨ atStuck)`

  The *loop* level (`R = ⊥`, `VM_impl = loop0 VM_body_impl`) is now **also**
  discharged in the same module, both theorems **fully constructive** (no
  postulate, no `NON_TERMINATING`):
  - `vm-loop-safety   : VM_impl ⊨ G (atCoin ⇒ X atDrink)` — after every coin
    the next observation is a drink, at every position of every loop run;
  - `vm-loop-liveness : VM_impl ⊨ G (F atDrink)` — a drink recurs forever
    (henceforth, eventually a drink).

  Both rest on a structural (non-coinductive) period-2 / re-rooting drop
  analysis: the three cycle roots `{VM_impl, P₁, P₂}` form the `LoopState`
  invariant, every position `dropIdx n tr` is again a loop state
  (`loop-state-drop`), and from any loop position a drink frame is reached
  within ≤ 1 step.  Because this recurses on the position index `n` (not
  coinductively), productivity is never at issue, so `--guardedness` is
  satisfied with no holes.

- **The body-level safety property does NOT transfer from `VM_impl` to
  `VM_spec` via trace refinement `⊑T`.** This is now a *certified negative
  result* (see `CSP.Examples.VendingMachine.VendingMachine_LTL_Sat`'s
  "Negative result" section, `vm-⊨ᵀ-safety-impossible`): the trace-based
  satisfaction relation `_⊨ᵀ_` of `Semantics.LTL.Refinement` is refuted for
  `G (atCoin ⇒ X atDrink)` by the one-letter CSP trace `[coin]`, which
  truncates the `X` ("next") obligation before any drink event is observed —
  even though the *same* formula is proved under the operational `_⊨_`
  (`vm-safety`). So although `⊑T-transfer-ᵀ` is itself a sound, monotone
  transfer lemma, it cannot be used to carry guarded-`X` safety from
  `VM_body_impl` to a trace-refined specification: next-time LTL needs a
  bisimulation-level refinement, not (prefix-closed) trace refinement.

- **DR-weak bisimulation between `VM_impl` and `VM_spec`.** This is the one
  remaining deferred item, and is now also the prerequisite for transferring
  next-time LTL claims (the point above): `VM_impl`/`VM_spec` are known to be
  trace-equivalent but not yet shown DR-bisimilar, and trace-equivalence alone
  is insufficient per the negative result above.  Plausible but out of scope
  here; the natural next step toward bisim-invariant LTL claims.
```
