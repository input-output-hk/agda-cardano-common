# TPC chapter 3: renaming `COPY`'s channels — `COPY⟦left↦aa, right↦bb⟧ ≈FD COPY'(aa,bb)`

Second chapter-3 example, porting the renaming illustrations of A.W.
Roscoe's *The Theory and Practice of Concurrency* (TPC §3.2).  Source:

- `fdr-examples/tpc/chapter03/section3-2.csp`

```csp
T = {0,1,2,3}

channel left,right,aa,bb:T

COPY = left?x -> right!x -> COPY

COPY'(a,b) = a?x -> b!x -> COPY'(a,b)

assert COPY[[left <- aa,right <- bb]] [FD= COPY'(aa,bb)
assert COPY'(aa,bb) [FD= COPY[[left <- aa,right <- bb]]
```

**Injective renaming** relabels a process's events one-for-one: applying
`[[left <- aa, right <- bb]]` to `COPY` yields a process that does `aa`
and `bb` exactly where `COPY` did `left` and `right` — which is precisely
the generic one-place buffer `COPY'` instantiated at the channel pair
`(aa, bb)`.  This module proves both FDR asserts at once as the single
failures-divergences **equivalence**

```text
copyRen≈FD-copy' : renameInv COPY inv ≈FD COPY'ab
```

**Modelling reductions:**

- **Payload.** `T = {0,1,2,3}` becomes `Bool`.  Nothing in the renaming
  argument depends on the payload's size — the relabel is
  payload-preserving on every channel — but a two-valued payload keeps the
  output guard's stuck payload decisions (`x ≟ v`, cf. `Ch1/Copy` §2.4)
  dischargeable by a finite case split.
- **The renaming operator.** FDR's `[[left <- aa, right <- bb]]` is the
  *inverse-based* injective wrapper `renameInv` of `CSP.Rename`,
  instantiated at the same-alphabet identity injection (as in
  `CSP.Examples.RenameSanity`): the relabel is given as a partial function
  `inv` from *target* concrete events back to their unique *source*
  preimage — `aa.x ↦ left.x`, `bb.x ↦ right.x`, and no target event maps
  back to `left`/`right` (the renamed process no longer performs them).

The non-injective half of TPC §3.2 (`SPLIT`/`RenSPLIT`, where a
comprehension-style renaming erases payloads and manufactures
nondeterminism, plus the two determinism checks) lives in §3 below; it
needs its own alphabet and therefore its own sub-module `Split`,
which is why the injective half already lives in the named sub-module
`Injective` (nothing alphabet-specific is opened at the top level,
following `Ch1/Copy.lagda.md`).

## §1. Shared imports

Alphabet-independent plumbing only: `Bool` (the payload), the polymorphic
unit return type `Poly.⊤ {lzero}`, `DecEq-Bool` (the output prefixes'
payload decisions), and the usual proof-side imports shared by the
verification sections.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch3.Renaming where

open import Level using (lift) renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)
open import Class.DecEq.Instances using (DecEq-Bool)

open import Process_Trees
```

## §2. The injective half: `COPY⟦left↦aa, right↦bb⟧` vs `COPY'(aa,bb)`

### §2.1 The alphabet

Four channels, all carrying a `Bool`: the pair `left`/`right` that `COPY`
uses, and the pair `aa`/`bb` that the renaming retargets them to.

```agda
module Injective where

  data RCh : Set → Set where
    left right aa bb : RCh Bool

  RCh-≟ : (x y : AnyTypes RCh) → Dec (x ≡ y)
  RCh-≟ (_ , left)  (_ , left)  = yes refl
  RCh-≟ (_ , right) (_ , right) = yes refl
  RCh-≟ (_ , aa)    (_ , aa)    = yes refl
  RCh-≟ (_ , bb)    (_ , bb)    = yes refl
  RCh-≟ (_ , left)  (_ , right) = no λ ()
  RCh-≟ (_ , left)  (_ , aa)    = no λ ()
  RCh-≟ (_ , left)  (_ , bb)    = no λ ()
  RCh-≟ (_ , right) (_ , left)  = no λ ()
  RCh-≟ (_ , right) (_ , aa)    = no λ ()
  RCh-≟ (_ , right) (_ , bb)    = no λ ()
  RCh-≟ (_ , aa)    (_ , left)  = no λ ()
  RCh-≟ (_ , aa)    (_ , right) = no λ ()
  RCh-≟ (_ , aa)    (_ , bb)    = no λ ()
  RCh-≟ (_ , bb)    (_ , left)  = no λ ()
  RCh-≟ (_ , bb)    (_ , right) = no λ ()
  RCh-≟ (_ , bb)    (_ , aa)    = no λ ()

  open import CSP.Operators RCh-≟

  RProc : Set₁
  RProc = PTree RCh (ExtI RCh) (Poly.⊤ {lzero})
```

### §2.2 `COPY` and the generic `COPY'(a,b)`

Both are the chapter-1 one-place buffer, `COPY` pinned at
`left`/`right` and `COPY'` generic in its channel pair (so
`COPY' left right` is `COPY` and `COPY' aa bb` is the renaming target).

```agda
  COPY : RProc
  COPY = loop0 (left ⟶ λ x → (right ! x ⟶ Skip))

  COPY' : RCh Bool → RCh Bool → RProc
  COPY' a b = loop0 (a ⟶ λ x → (b ! x ⟶ Skip))

  COPY'ab : RProc
  COPY'ab = COPY' aa bb
```

### §2.3 The renaming `COPY⟦left↦aa, right↦bb⟧`

`CSP.Rename` is instantiated at the same-alphabet identity injection
(exactly as `CSP.Examples.RenameSanity` does); the injective relabel is
then the inverse map `inv` sending each *target* concrete event to its
unique *source* preimage.  `aa` and `bb` pull back to `left` and `right`
at the same payload; `left` and `right` themselves have **no** preimage —
after the renaming they are gone from the alphabet of `RenCOPY`.

```agda
  open import CSP.Rename {E₁ = RCh} {E₂ = RCh} (λ e → e) (λ e → just e) (λ _ → refl)

  inv : (bt : AnyTypes RCh) → proj₁ bt → Maybe ConcEvent₁
  inv (_ , aa)    x = just ((Bool , left)  , x)
  inv (_ , bb)    x = just ((Bool , right) , x)
  inv (_ , left)  _ = nothing
  inv (_ , right) _ = nothing

  RenCOPY : RProc
  RenCOPY = renameInv COPY inv
```

### §2.4 Verification plan and the headline statement

`RenCOPY` and `COPY'ab` are *lockstep*: both read on `aa` (every
payload), write the read value back on `bb`, and re-enter their loop
through one silent step.  We exhibit the three-state binary relation
pairing the corresponding loop states, check it is a step-matching,
divergence-free (indeed *strong*, τ-for-τ) bisimulation, and run it
through the shared `DRFromRel` corecursion of `Semantics.BisimFromRel`
to get `RenCOPY ≈DR COPY'ab`; the `drbisim→≈FD` bridge then yields the
failures-divergences equivalence, whose two projections are the two FDR
`[FD=` asserts.

The `COPY'ab` side is a plain chapter-1-style loop, so its step
inversions are the channel-generic `loop-pfx-*`/`loop-out-*` lemmas of
`CSP.Laws.Traces.PrefixInversion`.  The renamed side needs *new*
inversions (§2.6): its nodes are the renamed offer/τ maps produced by
`_⟦_¿_⟧`, seen through `force (renameInv · inv)` exactly as in
`RenameSanity`.

```agda
  open import Semantics.LTS       {E = RCh} {I = ExtI RCh} hiding (Diverges)
  open import Semantics.WeakBisim {E = RCh} {I = ExtI RCh}
    using (_═[_]═►_; wev; wτ; τ*-refl; τ*-step)
  open import Semantics.DRBisim   {E = RCh} {I = ExtI RCh}
  open import Semantics.BisimFromRel {E = RCh} {I = ExtI RCh}
  open import Semantics.DRImpliesFD  {E = RCh} {I = ExtI RCh} using (drbisim→≈FD)
  open import Semantics.FailuresDivergences {E = RCh} {I = ExtI RCh} using (_≈FD_)
  open import CSP.Laws.Traces.PrefixInversion RCh-≟
    using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
           sil-no-ev; sil-τ-uniq; divergesSil)
```

The headline statement (both `[FD=` directions of the book's asserts):

```agda
  copyRen≈FD-copy' : renameInv COPY inv ≈FD COPY'ab
```

The two event labels of the renamed alphabet:

```agda
  lblA lblB : Bool → Event√ (Poly.⊤ {lzero})
  lblA x = evl (evLabel Bool aa x)
  lblB x = evl (evLabel Bool bb x)
```

### §2.5 Reachable states and named strong steps

The *source* (`COPY`) side passes through the post-`left` output state
`C₁ x` and the silent re-entry state `C₂`, exactly as in `Ch1/Copy` §2.6
— `iter-bind` terms that are definitional unfoldings of the loop's
successors.  The renamed process's states are their images under
`renameInv · inv`; the `COPY'ab` side has the mirror-image states
`D₁ x`/`D₂` over `aa`/`bb`.

```agda
  copyK copy'K : Poly.⊤ {lzero} → PTree RCh (ExtI RCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
  copyK  _ = (left ⟶ λ x → (right ! x ⟶ Skip)) >>= (λ a′ → Ret (inj₁ a′))
  copy'K _ = (aa   ⟶ λ x → (bb    ! x ⟶ Skip)) >>= (λ a′ → Ret (inj₁ a′))

  C₁ : Bool → RProc
  C₁ x = iter-bind ((right ! x ⟶ Skip) >>= (λ a′ → Ret (inj₁ a′))) copyK

  C₂ : RProc
  C₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) copyK

  Ren₁ : Bool → RProc
  Ren₁ x = renameInv (C₁ x) inv

  Ren₂ : RProc
  Ren₂ = renameInv C₂ inv

  D₁ : Bool → RProc
  D₁ x = iter-bind ((bb ! x ⟶ Skip) >>= (λ a′ → Ret (inj₁ a′))) copy'K

  D₂ : RProc
  D₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) copy'K
```

The named strong steps.  On the `COPY'ab` side these are the usual loop
steps (`Ch1/Copy` §2.6): the read fires definitionally at every payload,
the write's payload decision `x ≟ x` reduces once the `Bool` is closed,
and the re-entry is one `sil`.

```agda
  COPY'-aa : ∀ x → COPY'ab ─[ ev (lblA x) ]─► D₁ x
  COPY'-aa x = sVis {at = Bool , aa} {a = x} refl refl

  D₁-bb : ∀ x → D₁ x ─[ ev (lblB x) ]─► D₂
  D₁-bb true  = sVis {at = Bool , bb} {a = true}  refl refl
  D₁-bb false = sVis {at = Bool , bb} {a = false} refl refl

  D₂-τ : D₂ ─[ τ ]─► COPY'ab
  D₂-τ = sSil refl
```

On the renamed side the same three steps hold *definitionally through
the renaming*: `force RenCOPY` computes (via `_⟦_¿_⟧`'s match on
`force COPY`) to a `react` node whose offer at `(aa, x)` is
`rnFan (rnCollect vC (invPreimg inv (Bool , aa) x))`; `inv` yields the
singleton preimage `left.x`, `COPY`'s offer map answers `just (C₁ x)`,
and the singleton fan-in is the bare renamed source `just (Ren₁ x)` —
so `refl` proves the offer.  The write is the same computation through
`C₁ x`'s `Output-cont` guard (payload decision `x ≟ x`, hence the
closed-`Bool` split), and the re-entry is the renamed image of `C₂`'s
`sil` (rename maps `sil` to `sil`).

```agda
  Ren-aa : ∀ x → RenCOPY ─[ ev (lblA x) ]─► Ren₁ x
  Ren-aa x = sVis {at = Bool , aa} {a = x} refl refl

  Ren₁-bb : ∀ x → Ren₁ x ─[ ev (lblB x) ]─► Ren₂
  Ren₁-bb true  = sVis {at = Bool , bb} {a = true}  refl refl
  Ren₁-bb false = sVis {at = Bool , bb} {a = false} refl refl

  Ren₂-τ : Ren₂ ─[ τ ]─► RenCOPY
  Ren₂-τ = sSil refl
```

### §2.6 Step inversions for the renamed states

*Visible* inversion at the root: a visible step of `RenCOPY` case-splits
on the fired target event.  At `aa` the renamed offer computes to
`just (Ren₁ x)` as above, pinning label and successor.  At `bb` the
preimage is `right.x`, but `COPY`'s root offers nothing on `right`, so
the collected source list is empty and the fan-in is `nothing`.  At
`left`/`right` the preimage itself is empty (`inv` returns `nothing`).
Both refute the step by `case br of λ ()` — the offer pipeline reduces
to `nothing` even with the payload left open, since only *channel*
decisions are involved.

```agda
  RenCOPY-ev-inv : ∀ {l : Event√ (Poly.⊤ {lzero})} {t′ : RProc}
                 → RenCOPY ─[ ev l ]─► t′
                 → Σ[ x ∈ Bool ] ((l ≡ lblA x) × (t′ ≡ Ren₁ x))
  RenCOPY-ev-inv (sRet eq) = case eq of λ ()
  RenCOPY-ev-inv (sVis {at = _ , aa} {a = x} refl br) = x , refl , sym (just-injective br)
  RenCOPY-ev-inv (sVis {at = _ , bb}    refl br) = case br of λ ()
  RenCOPY-ev-inv (sVis {at = _ , left}  refl br) = case br of λ ()
  RenCOPY-ev-inv (sVis {at = _ , right} refl br) = case br of λ ()
```

*Silence* of the root: the renamed τ-branch is `extBranch`, which pulls
the target internal index back through `extBwd` and consults `COPY`'s
τ-map — which is everywhere-`nothing` (`∅t` under the prefix node, at
*any* index).  At a `base`/`fin` index `extBwd` computes (the identity
injection's `ι⁻¹` is total), so the branch reduces to `nothing`
outright; at a `pair` index `extBwd` is stuck on its sub-indices, so we
re-abstract the step over its value (the `with … | br` idiom of
`Ch1/Copy` §2.8) — in *both* branches the τ-map's answer is `nothing`.

```agda
  RenCOPY-no-τ : ∀ {t′ : RProc} → RenCOPY ─[ τ ]─► t′ → ⊥
  RenCOPY-no-τ (sSil eq) = case eq of λ ()
  RenCOPY-no-τ (sTau {i = _ , base _} refl br) = case br of λ ()
  RenCOPY-no-τ (sTau {i = _ , fin}    refl br) = case br of λ ()
  RenCOPY-no-τ (sTau {i = _ , pair p q} refl br) with extBwd (pair p q) | br
  ... | just _  | br′ = case br′ of λ ()
  ... | nothing | br′ = case br′ of λ ()
```

The post-read state `Ren₁ x` fires exactly `bb!x`: at `bb` the preimage
is `right.b`, and `C₁ x`'s `Output-cont` guard answers `just C₂` iff
`b ≟ x` fires — the stuck payload decision is discharged by splitting
both the state's value `x` and the fired payload `b` (`Ch1/Copy` §2.4's
closed-`Bool` trick), with the mismatched combinations refuted.  At
`aa` the preimage is `left.b`, refused by the output node's channel
guard; `left`/`right` have no preimage at all.

```agda
  Ren₁-ev-inv : ∀ x {l : Event√ (Poly.⊤ {lzero})} {t′ : RProc}
              → Ren₁ x ─[ ev l ]─► t′ → (l ≡ lblB x) × (t′ ≡ Ren₂)
  Ren₁-ev-inv x     (sRet eq) = case eq of λ ()
  Ren₁-ev-inv x     (sVis {at = _ , aa}    refl br) = case br of λ ()
  Ren₁-ev-inv x     (sVis {at = _ , left}  refl br) = case br of λ ()
  Ren₁-ev-inv x     (sVis {at = _ , right} refl br) = case br of λ ()
  Ren₁-ev-inv true  (sVis {at = _ , bb} {a = true}  refl br) = refl , sym (just-injective br)
  Ren₁-ev-inv true  (sVis {at = _ , bb} {a = false} refl br) = case br of λ ()
  Ren₁-ev-inv false (sVis {at = _ , bb} {a = true}  refl br) = case br of λ ()
  Ren₁-ev-inv false (sVis {at = _ , bb} {a = false} refl br) = refl , sym (just-injective br)

  Ren₁-no-τ : ∀ x {t′ : RProc} → Ren₁ x ─[ τ ]─► t′ → ⊥
  Ren₁-no-τ x (sSil eq) = case eq of λ ()
  Ren₁-no-τ x (sTau {i = _ , base _} refl br) = case br of λ ()
  Ren₁-no-τ x (sTau {i = _ , fin}    refl br) = case br of λ ()
  Ren₁-no-τ x (sTau {i = _ , pair p q} refl br) with extBwd (pair p q) | br
  ... | just _  | br′ = case br′ of λ ()
  ... | nothing | br′ = case br′ of λ ()
```

`Ren₂` needs no bespoke inversion: `force Ren₂` computes to
`sil RenCOPY` (rename maps `C₂`'s `sil COPY` to `sil` of the renamed
root), so the generic `sil-no-ev`/`sil-τ-uniq`/`divergesSil` helpers
apply with `refl`.

### §2.7 Divergence-freedom

Every state in the relation is stable or one `sil` away from a stable
state, on both sides.

```agda
  ¬div-RenCOPY : Diverges RenCOPY → ⊥
  ¬div-RenCOPY d = RenCOPY-no-τ (Diverges.step d)

  ¬div-Ren₁ : ∀ x → Diverges (Ren₁ x) → ⊥
  ¬div-Ren₁ x d = Ren₁-no-τ x (Diverges.step d)

  ¬div-Ren₂ : Diverges Ren₂ → ⊥
  ¬div-Ren₂ d = ¬div-RenCOPY (divergesSil refl d)

  ¬div-COPY' : Diverges COPY'ab → ⊥
  ¬div-COPY' d = loop-pfx-no-τ aa (λ x → (bb ! x ⟶ Skip)) copy'K (Diverges.step d)

  ¬div-D₁ : ∀ x → Diverges (D₁ x) → ⊥
  ¬div-D₁ x d = loop-out-no-τ bb x Skip copy'K (Diverges.step d)

  ¬div-D₂ : Diverges D₂ → ⊥
  ¬div-D₂ d = ¬div-COPY' (divergesSil refl d)
```

### §2.8 The bisimulation and the theorem

The relation pairs the three corresponding loop states.  Both sides
re-enter their loop through exactly one τ from the paired re-entry
states, so the matching is lockstep (every weak answer is a single
strong step, `τ*-refl` on both flanks).

```agda
  data RR : RProc → RProc → Set₁ where
    r₀ : RR RenCOPY COPY'ab
    r₁ : ∀ x → RR (Ren₁ x) (D₁ x)
    r₂ : RR Ren₂ D₂

  RR-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RR p q → p ─[ ev l ]─► p′
            → Σ[ q′ ∈ RProc ] ((q ═[ ev l ]═► q′) × RR p′ q′)
  RR-fwd-ev r₀ stp with RenCOPY-ev-inv stp
  ... | x , refl , refl = D₁ x , wev τ*-refl (COPY'-aa x) τ*-refl , r₁ x
  RR-fwd-ev (r₁ x) stp with Ren₁-ev-inv x stp
  ... | refl , refl = D₂ , wev τ*-refl (D₁-bb x) τ*-refl , r₂
  RR-fwd-ev r₂ stp = ⊥-elim (sil-no-ev refl stp)

  RR-fwd-τ : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
           → Σ[ q′ ∈ RProc ] ((q ═[ τ ]═► q′) × RR p′ q′)
  RR-fwd-τ r₀ stp = ⊥-elim (RenCOPY-no-τ stp)
  RR-fwd-τ (r₁ x) stp = ⊥-elim (Ren₁-no-τ x stp)
  RR-fwd-τ r₂ stp with sil-τ-uniq refl stp
  ... | refl = COPY'ab , wτ (τ*-step D₂-τ τ*-refl) , r₀

  RR-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → RR p q → q ─[ ev l ]─► q′
            → Σ[ p′ ∈ RProc ] ((p ═[ ev l ]═► p′) × RR p′ q′)
  RR-bwd-ev r₀ stp with loop-pfx-ev-inv aa (λ x → (bb ! x ⟶ Skip)) copy'K stp
  ... | x , refl , refl = Ren₁ x , wev τ*-refl (Ren-aa x) τ*-refl , r₁ x
  RR-bwd-ev (r₁ x) stp with loop-out-ev-inv bb x Skip copy'K stp
  ... | refl , refl = Ren₂ , wev τ*-refl (Ren₁-bb x) τ*-refl , r₂
  RR-bwd-ev r₂ stp = ⊥-elim (sil-no-ev refl stp)

  RR-bwd-τ : ∀ {p q q′} → RR p q → q ─[ τ ]─► q′
           → Σ[ p′ ∈ RProc ] ((p ═[ τ ]═► p′) × RR p′ q′)
  RR-bwd-τ r₀ stp = ⊥-elim (loop-pfx-no-τ aa (λ x → (bb ! x ⟶ Skip)) copy'K stp)
  RR-bwd-τ (r₁ x) stp = ⊥-elim (loop-out-no-τ bb x Skip copy'K stp)
  RR-bwd-τ r₂ stp with sil-τ-uniq refl stp
  ... | refl = RenCOPY , wτ (τ*-step Ren₂-τ τ*-refl) , r₀

  RR-¬divL : ∀ {p q} → RR p q → Diverges p → ⊥
  RR-¬divL r₀     = ¬div-RenCOPY
  RR-¬divL (r₁ x) = ¬div-Ren₁ x
  RR-¬divL r₂     = ¬div-Ren₂

  RR-¬divR : ∀ {p q} → RR p q → Diverges q → ⊥
  RR-¬divR r₀     = ¬div-COPY'
  RR-¬divR (r₁ x) = ¬div-D₁ x
  RR-¬divR r₂     = ¬div-D₂

  module MR = DRFromRel RR RR-fwd-ev RR-fwd-τ RR-bwd-ev RR-bwd-τ RR-¬divL RR-¬divR

  renCOPY≈DR-copy' : RenCOPY ≈DR COPY'ab
  renCOPY≈DR-copy' = MR.rel→dr r₀
```

The headline: `≈DR` weakens to the failures-divergences equivalence,
whose two halves are the book's `[FD=` asserts in both directions.

```agda
  copyRen≈FD-copy' = drbisim→≈FD renCOPY≈DR-copy'
```

## §3. The non-injective half: `SPLIT`, `RenSPLIT` and manufactured nondeterminism

TPC §3.2 continues with the non-injective example: a *deterministic
parity router*

```csp
SPLIT  = in?x -> (if odd(x) then out1!x -> SPLIT else out2!x -> SPLIT)
SPLIT' = in' -> ((out1' -> SPLIT') |~| (out2' -> SPLIT'))

assert SPLIT[[in.x <- in', out1.x <- out1', out2.x <- out2' | x <- T]] [FD= SPLIT'
assert SPLIT' [FD= SPLIT[[in.x <- in', out1.x <- out1', out2.x <- out2' | x <- T]]
```

whose routing decision is a *function of the payload*, renamed by a
comprehension-style relabel that **erases the payload** (every `in.x`
becomes the nullary `in'`, every `out1.x` becomes `out1'`, every `out2.x`
becomes `out2'`).  The renaming is **non-injective** — the preimage of
`in'` is the whole family `{in.x | x <- T}` — and, having forgotten the
datum that steered the router, the renamed process can no longer be told
apart from one that chooses its output channel *internally*: `RenSPLIT` is
failures-divergences **equivalent** to the nondeterministic `SPLIT'`.
Renaming does not preserve determinism; the two determinism checks of
§3.3 (`SPLIT` is deterministic, `SPLIT'` is not) make the manufacture of
nondeterminism a theorem rather than an impression.

**Modelling reductions** (on top of §2's): the payload `T` is again
`Bool`, and the parity test `odd(x)` becomes the `Bool` itself, routed by
the conditional `_◁_▷_` (`true ↦ out1`, `false ↦ out2`).  The nullary
target channels carry `Data.Unit.⊤`, as `ATM`'s `refuse` channel does.
The relabel is the **relational** `_⟦_¿_⟧` of `CSP.Rename` with a
hand-written relation and preimage enumerator (`renameInv` cannot express
it: `in'` has *two* source preimages), exactly the fan-in Check 2 of
`CSP.Examples.RenameSanity`.

### §3.1 The alphabet

One alphabet holds both halves — the `Bool`-carrying source channels and
the nullary (`⊤`-carrying) target channels — so the same-alphabet
identity instantiation of `CSP.Rename` (as in §2.3 and RenameSanity
Checks 1–3) applies; a two-alphabet split would need a
payload-*preserving* injection `ι` between the alphabets, which a
payload-erasing relabel does not have.  `in` is an Agda keyword, so the
source read channel is spelled `inn`.

```agda
module Split where

  open import Level using (Lift; lower) renaming (suc to lsuc)
  open import Data.Unit using (⊤; tt)
  open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
  open import Data.List using (List; []; _∷_; _∷ʳ_)
  open import Data.List.Properties using (∷-injectiveˡ; ∷-injectiveʳ)
  open import Data.Product using (proj₂)
  open import Data.Sum using (inj₂)
  open import Relation.Nullary using (¬_)

  data SCh : Set → Set where
    inn out1 out2   : SCh Bool
    in' out1' out2' : SCh ⊤

  SCh-≟ : (x y : AnyTypes SCh) → Dec (x ≡ y)
  SCh-≟ (_ , inn)   (_ , inn)   = yes refl
  SCh-≟ (_ , out1)  (_ , out1)  = yes refl
  SCh-≟ (_ , out2)  (_ , out2)  = yes refl
  SCh-≟ (_ , in')   (_ , in')   = yes refl
  SCh-≟ (_ , out1') (_ , out1') = yes refl
  SCh-≟ (_ , out2') (_ , out2') = yes refl

  SCh-≟ (_ , inn)   (_ , out1)  = no λ ()
  SCh-≟ (_ , inn)   (_ , out2)  = no λ ()
  SCh-≟ (_ , inn)   (_ , in')   = no λ ()
  SCh-≟ (_ , inn)   (_ , out1') = no λ ()
  SCh-≟ (_ , inn)   (_ , out2') = no λ ()

  SCh-≟ (_ , out1)  (_ , inn)   = no λ ()
  SCh-≟ (_ , out1)  (_ , out2)  = no λ ()
  SCh-≟ (_ , out1)  (_ , in')   = no λ ()
  SCh-≟ (_ , out1)  (_ , out1') = no λ ()
  SCh-≟ (_ , out1)  (_ , out2') = no λ ()

  SCh-≟ (_ , out2)  (_ , inn)   = no λ ()
  SCh-≟ (_ , out2)  (_ , out1)  = no λ ()
  SCh-≟ (_ , out2)  (_ , in')   = no λ ()
  SCh-≟ (_ , out2)  (_ , out1') = no λ ()
  SCh-≟ (_ , out2)  (_ , out2') = no λ ()

  SCh-≟ (_ , in')   (_ , inn)   = no λ ()
  SCh-≟ (_ , in')   (_ , out1)  = no λ ()
  SCh-≟ (_ , in')   (_ , out2)  = no λ ()
  SCh-≟ (_ , in')   (_ , out1') = no λ ()
  SCh-≟ (_ , in')   (_ , out2') = no λ ()

  SCh-≟ (_ , out1') (_ , inn)   = no λ ()
  SCh-≟ (_ , out1') (_ , out1)  = no λ ()
  SCh-≟ (_ , out1') (_ , out2)  = no λ ()
  SCh-≟ (_ , out1') (_ , in')   = no λ ()
  SCh-≟ (_ , out1') (_ , out2') = no λ ()

  SCh-≟ (_ , out2') (_ , inn)   = no λ ()
  SCh-≟ (_ , out2') (_ , out1)  = no λ ()
  SCh-≟ (_ , out2') (_ , out2)  = no λ ()
  SCh-≟ (_ , out2') (_ , in')   = no λ ()
  SCh-≟ (_ , out2') (_ , out1') = no λ ()

  open import CSP.Operators SCh-≟

  SProc : Set₁
  SProc = PTree SCh (ExtI SCh) (Poly.⊤ {lzero})
```

### §3.2 `SPLIT`, `SPLIT'` and their loop states

`SPLIT` reads a `Bool` on `inn` and writes it back on the
parity-selected output channel — `out1` for `true`, `out2` for `false` —
via `_◁_▷_`; every decision is driven by the visible datum, so the
process is deterministic.  `SPLIT'` reads the nullary `in'` and then
*internally* (`_⊓_`) chooses which nullary output to offer.

```agda
  sBody : Bool → SProc
  sBody x = (out1 ! x ⟶ Skip) ◁ x ▷ (out2 ! x ⟶ Skip)

  SPLIT : SProc
  SPLIT = loop0 (inn ⟶ sBody)

  choiceBody : SProc
  choiceBody = (out1' ⟶₀ Skip) ⊓ (out2' ⟶₀ Skip)

  SPLIT' : SProc
  SPLIT' = loop0 (in' ⟶₀ choiceBody)
```

The reachable loop states, as `iter-bind` unfoldings (`Ch1/Copy` §2.6,
§2.5 above).  On the `SPLIT` side: the post-read state `S₁ x` (for
closed `x` the conditional reduces to the single parity-selected output
node) and the silent re-entry state `S₂`.  On the `SPLIT'` side: the
post-read state `T₁` *sitting on the `⊓`* (unstable: two τs enabled, no
visible offer), the two resolved output states `T₂ x`, and the re-entry
state `T₃`.

```agda
  splitK split'K : Poly.⊤ {lzero} → PTree SCh (ExtI SCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
  splitK  _ = (inn ⟶ sBody)      >>= (λ a′ → Ret (inj₁ a′))
  split'K _ = (in' ⟶₀ choiceBody) >>= (λ a′ → Ret (inj₁ a′))

  S₁ : Bool → SProc
  S₁ x = iter-bind (sBody x >>= (λ a′ → Ret (inj₁ a′))) splitK

  S₂ : SProc
  S₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) splitK

  T₁ : SProc
  T₁ = iter-bind (choiceBody >>= (λ a′ → Ret (inj₁ a′))) split'K

  T₂ : Bool → SProc
  T₂ true  = iter-bind ((out1' ⟶₀ Skip) >>= (λ a′ → Ret (inj₁ a′))) split'K
  T₂ false = iter-bind ((out2' ⟶₀ Skip) >>= (λ a′ → Ret (inj₁ a′))) split'K

  T₃ : SProc
  T₃ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) split'K
```

The semantic layer at this alphabet, and the channel-generic loop
inversions.

```agda
  open import Semantics.LTS       {E = SCh} {I = ExtI SCh} hiding (Diverges)
  open import Semantics.WeakBisim {E = SCh} {I = ExtI SCh}
    using (_═[_]═►_; wev; wτ; τ*-refl; τ*-step)
  open import Semantics.DRBisim   {E = SCh} {I = ExtI SCh}
  open import Semantics.BisimFromRel {E = SCh} {I = ExtI SCh}
  open import Semantics.DRImpliesFD  {E = SCh} {I = ExtI SCh} using (drbisim→≈FD)
  open import Semantics.FailuresDivergences {E = SCh} {I = ExtI SCh} using (_≈FD_)
  open import Semantics.Failures  {E = SCh} {I = ExtI SCh}
    using (traces; failures; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
  open import Semantics.Refusals  {E = SCh} {I = ExtI SCh} using (Offers; Refuses)
  open import Semantics.Determinism {E = SCh} {I = ExtI SCh} using (Deterministic)
  open import CSP.Laws.Traces.PrefixInversion SCh-≟
    using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
           sil-no-ev; sil-τ-uniq; divergesSil)
```

The event labels: `Bool`-carrying on the source channels (the routed
output label is a function of the parity), `⊤`-carrying on the targets.

```agda
  lblSIn : Bool → Event√ (Poly.⊤ {lzero})
  lblSIn x = evl (evLabel Bool inn x)

  lblSOut : Bool → Event√ (Poly.⊤ {lzero})
  lblSOut true  = evl (evLabel Bool out1 true)
  lblSOut false = evl (evLabel Bool out2 false)

  lblIn' lblOut1' lblOut2' : Event√ (Poly.⊤ {lzero})
  lblIn'   = evl (evLabel ⊤ in' tt)
  lblOut1' = evl (evLabel ⊤ out1' tt)
  lblOut2' = evl (evLabel ⊤ out2' tt)

  lblOut' : Bool → Event√ (Poly.⊤ {lzero})
  lblOut' true  = lblOut1'
  lblOut' false = lblOut2'
```

`SPLIT`'s two non-root state shapes are the channel-generic loop-output
states (at closed `x` the conditional in `S₁ x` computes away), so their
step inversions come straight from `PrefixInversion`; the root is a
loop-prefix state handled inline by `loop-pfx-ev-inv`/`loop-pfx-no-τ`
below.

```agda
  S₁-ev-inv : ∀ x {l : Event√ (Poly.⊤ {lzero})} {t′ : SProc}
            → S₁ x ─[ ev l ]─► t′ → (l ≡ lblSOut x) × (t′ ≡ S₂)
  S₁-ev-inv true  = loop-out-ev-inv out1 true  Skip splitK
  S₁-ev-inv false = loop-out-ev-inv out2 false Skip splitK

  S₁-no-τ : ∀ x {t′ : SProc} → S₁ x ─[ τ ]─► t′ → ⊥
  S₁-no-τ true  = loop-out-no-τ out1 true  Skip splitK
  S₁-no-τ false = loop-out-no-τ out2 false Skip splitK
```

`SPLIT'`'s named strong steps.  The read fires definitionally; the two
τs resolving the `⊓` pick a `br2` branch at the closed `fin` index
(payload `lift fzero` / `lift (fsuc fzero)`), threaded through
`bindT`/`iterT` exactly as in `Ch1/ATM` §5.4; the resolved output states
fire their nullary prefix; the re-entry is one `sil`.

```agda
  SPLIT'-in : SPLIT' ─[ ev lblIn' ]─► T₁
  SPLIT'-in = sVis {at = ⊤ , in'} {a = tt} refl refl

  T₁-τ : ∀ x → T₁ ─[ τ ]─► T₂ x
  T₁-τ true  = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl
  T₁-τ false = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

  T₂-out : ∀ x → T₂ x ─[ ev (lblOut' x) ]─► T₃
  T₂-out true  = sVis {at = ⊤ , out1'} {a = tt} refl refl
  T₂-out false = sVis {at = ⊤ , out2'} {a = tt} refl refl

  T₃-τ : T₃ ─[ τ ]─► SPLIT'
  T₃-τ = sSil refl
```

Step inversions for the `⊓` state `T₁` — this is the shape `Ch1/ATM`
only ever *drove* and never inverted.  `T₁` offers nothing visibly (its
offer map is `∅v` threaded through `bindV`/`iterV`, definitionally
`nothing` at *every* event, so no channel split is needed), and its
τ-branches are exactly `br2 (out1'⟶₀…) (out2'⟶₀…)` threaded through
`bindT`/`iterT`: `nothing` at every `base`/`pair` index, and at a `fin`
index the payloads `lift fzero` / `lift (fsuc fzero)` select the two
arms (anything deeper is `nothing`).

```agda
  T₁-no-ev : ∀ {l : Event√ (Poly.⊤ {lzero})} {t′ : SProc} → T₁ ─[ ev l ]─► t′ → ⊥
  T₁-no-ev (sRet eq)      = case eq of λ ()
  T₁-no-ev (sVis refl br) = case br of λ ()

  T₁-τ-inv : ∀ {t′ : SProc} → T₁ ─[ τ ]─► t′ → (t′ ≡ T₂ true) ⊎ (t′ ≡ T₂ false)
  T₁-τ-inv (sSil eq) = case eq of λ ()
  T₁-τ-inv (sTau {i = _ , base _}   refl br) = case br of λ ()
  T₁-τ-inv (sTau {i = _ , pair _ _} refl br) = case br of λ ()
  T₁-τ-inv (sTau {i = _ , fin} {a = lift fzero} refl br) =
    inj₁ (sym (just-injective br))
  T₁-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl br) =
    inj₂ (sym (just-injective br))
  T₁-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) = case br of λ ()
```

The resolved states `T₂ x` are *stable* (their τ-part is `∅t` under the
prefix node, threaded through the same pipeline — `nothing` at every
index, definitionally).

```agda
  T₂-stable : ∀ x → isStable (T₂ x)
  T₂-stable true  _ _ = refl
  T₂-stable false _ _ = refl
```

### §3.3 The determinism checks

`Semantics.Determinism` (following Roscoe's failures characterisation):
`P` is deterministic iff no trace `s ⌢ ⟨a⟩` of `P` coexists with a
stable state reached by `s` that refuses `a`.

```agda
  split-det : Deterministic SPLIT

  split'-nondet : ¬ Deterministic SPLIT'
```

**`SPLIT'` is not deterministic** — the four-step witness: `SPLIT'` *can*
do `⟨in', out1'⟩` (resolve the `⊓` left, then fire `out1'`), yet after
the same trace `⟨in'⟩` it can also resolve the `⊓` right into the stable
state `T₂ false`, which offers only `out2'` and hence **refuses**
`out1'`.  The refusal's only step inversion is the loop-prefix one; the
fired label `out2'.x` can never equal `out1'` (channel constructors
clash).

```agda
  T₂false-refuses-out1' : ∀ (e : Event√ (Poly.⊤ {lzero}))
                        → e ≡ lblOut1' → ¬ Offers (T₂ false) e
  T₂false-refuses-out1' e refl (t′ , stp)
    with loop-pfx-ev-inv out2' (λ _ → Skip) split'K stp
  ... | x , eq , _ = case eq of λ ()

  split'-nondet det = det {s = lblIn' ∷ []} {a = lblOut1'}
    (T₃ , ⟹-ev SPLIT'-in (⟹-τ (T₁-τ true) (⟹-ev (T₂-out true) ⟹-refl)))
    (T₂ false , ⟹-ev SPLIT'-in (⟹-τ (T₁-τ false) ⟹-refl)
     , T₂-stable false , T₂false-refuses-out1')
```

**`SPLIT` is deterministic.**  Its reachable states are exactly
`SPLIT` (stable; offers `inn.x` for both `x`), `S₁ x` (stable; offers
*only* the parity-selected `lblSOut x`) and `S₂` (unstable; one τ back
to `SPLIT`) — every state reached by a given trace is unique up to the
silent re-entry, and each stable state refuses only what it never
offers.  The proof walks the *accepting* run (`t = s ⌢ ⟨a⟩`) and the
*refusing* run (`s`) in lockstep through the three state shapes; keeping
the accepting run's trace as an abstract `t` with the equation
`t ≡ s ∷ʳ a` on the side sidesteps the stuck `∷ʳ` when matching its
derivation.  When the refusing run halts (`⟹-refl`): at `SPLIT`/`S₁ x`
the accepting run's next step is an offer of `a` at that very state,
contradicting the refusal; at `S₂` there is no stable halt at all
(`force S₂` is a `sil`, so `isStable S₂` is `Lift ⊥`).

```agda
  []≢∷ʳ : ∀ {s : List (Event√ (Poly.⊤ {lzero}))} {a : Event√ (Poly.⊤ {lzero})}
        → [] ≡ s ∷ʳ a → ⊥
  []≢∷ʳ {s = []}    ()
  []≢∷ʳ {s = _ ∷ _} ()

  inn-lbl-inj : ∀ {x y : Bool} → lblSIn x ≡ lblSIn y → x ≡ y
  inn-lbl-inj refl = refl

  detS  : ∀ {t s : List (Event√ (Poly.⊤ {lzero}))} {a : Event√ (Poly.⊤ {lzero})}
            {w P′ : SProc}
        → t ≡ s ∷ʳ a → SPLIT ⟹⟨ t ⟩ w → SPLIT ⟹⟨ s ⟩ P′
        → Refuses P′ (λ e → e ≡ a) → ⊥
  detS₁ : ∀ x {t s : List (Event√ (Poly.⊤ {lzero}))} {a : Event√ (Poly.⊤ {lzero})}
            {w P′ : SProc}
        → t ≡ s ∷ʳ a → S₁ x ⟹⟨ t ⟩ w → S₁ x ⟹⟨ s ⟩ P′
        → Refuses P′ (λ e → e ≡ a) → ⊥
  detS₂ : ∀ {t s : List (Event√ (Poly.⊤ {lzero}))} {a : Event√ (Poly.⊤ {lzero})}
            {w P′ : SProc}
        → t ≡ s ∷ʳ a → S₂ ⟹⟨ t ⟩ w → S₂ ⟹⟨ s ⟩ P′
        → Refuses P′ (λ e → e ≡ a) → ⊥

  detS eq ⟹-refl        ⟹-refl          refu = case eq of λ ()
  detS eq ⟹-refl        (⟹-τ stp′ _)    refu = loop-pfx-no-τ inn sBody splitK stp′
  detS eq ⟹-refl        (⟹-ev stp′ _)   refu = case eq of λ ()
  detS eq (⟹-τ stp″ _)  _                refu = loop-pfx-no-τ inn sBody splitK stp″
  detS eq (⟹-ev stp″ _) ⟹-refl          refu =
    proj₂ refu _ (∷-injectiveˡ eq) (_ , stp″)
  detS eq (⟹-ev stp″ _) (⟹-τ stp′ _)    refu = loop-pfx-no-τ inn sBody splitK stp′
  detS eq (⟹-ev stp″ rest″) (⟹-ev stp′ rest′) refu
    with loop-pfx-ev-inv inn sBody splitK stp′ | loop-pfx-ev-inv inn sBody splitK stp″
  ... | x , refl , refl | y , refl , refl
    with inn-lbl-inj (∷-injectiveˡ eq)
  ...   | refl = detS₁ x (∷-injectiveʳ eq) rest″ rest′ refu

  detS₁ x eq ⟹-refl        ⟹-refl          refu = case eq of λ ()
  detS₁ x eq ⟹-refl        (⟹-τ stp′ _)    refu = S₁-no-τ x stp′
  detS₁ x eq ⟹-refl        (⟹-ev stp′ _)   refu = case eq of λ ()
  detS₁ x eq (⟹-τ stp″ _)  _                refu = S₁-no-τ x stp″
  detS₁ x eq (⟹-ev stp″ _) ⟹-refl          refu =
    proj₂ refu _ (∷-injectiveˡ eq) (_ , stp″)
  detS₁ x eq (⟹-ev stp″ _) (⟹-τ stp′ _)    refu = S₁-no-τ x stp′
  detS₁ x eq (⟹-ev stp″ rest″) (⟹-ev stp′ rest′) refu
    with S₁-ev-inv x stp′ | S₁-ev-inv x stp″
  ... | refl , refl | refl , refl = detS₂ (∷-injectiveʳ eq) rest″ rest′ refu

  detS₂ eq tr             ⟹-refl           refu = lower (proj₁ refu)
  detS₂ eq tr             (⟹-ev stp′ _)    refu = sil-no-ev refl stp′
  detS₂ eq ⟹-refl        (⟹-τ stp′ _)     refu = []≢∷ʳ eq
  detS₂ eq (⟹-ev stp″ _) (⟹-τ stp′ _)     refu = sil-no-ev refl stp″
  detS₂ eq (⟹-τ stp″ rest″) (⟹-τ stp′ rest′) refu
    with sil-τ-uniq refl stp″ | sil-τ-uniq refl stp′
  ... | refl | refl = detS eq rest″ rest′ refu

  split-det (_ , tr) (P′ , run , refu) = detS refl tr run refu
```

### §3.4 The non-injective renaming `RenSPLIT`

The same-alphabet identity instantiation of `CSP.Rename` (only the τ-index
re-tagging `extBwd` consults it; `SPLIT` is τ-free at every `react` node,
so it is inert), and the payload-erasing relation: every source event of a
`Bool` channel relates to the nullary event of its primed counterpart.
The preimage enumerator lists, per target event, **both** payloads of the
corresponding source channel — the fan-in that `renameInv`'s
`Maybe`-valued inverse cannot express.

```agda
  open import CSP.Rename {E₁ = SCh} {E₂ = SCh} (λ e → e) (λ e → just e) (λ _ → refl)

  ⊥₁ : Set₁
  ⊥₁ = Lift (lsuc lzero) ⊥

  Rre : ConcEvent₁ → ConcEvent₂ → Set₁
  Rre ce ((_ , in')   , _) = (ce ≡ ((Bool , inn)  , true)) ⊎ (ce ≡ ((Bool , inn)  , false))
  Rre ce ((_ , out1') , _) = (ce ≡ ((Bool , out1) , true)) ⊎ (ce ≡ ((Bool , out1) , false))
  Rre ce ((_ , out2') , _) = (ce ≡ ((Bool , out2) , true)) ⊎ (ce ≡ ((Bool , out2) , false))
  Rre _  ((_ , inn)   , _) = ⊥₁
  Rre _  ((_ , out1)  , _) = ⊥₁
  Rre _  ((_ , out2)  , _) = ⊥₁

  preimgS : (bt : AnyTypes SCh) (b : proj₁ bt)
          → List (Σ[ at ∈ AnyTypes SCh ] Σ[ a ∈ proj₁ at ] Rre (at , a) (bt , b))
  preimgS (_ , in')   _ = ((Bool , inn)  , true  , inj₁ refl)
                        ∷ ((Bool , inn)  , false , inj₂ refl) ∷ []
  preimgS (_ , out1') _ = ((Bool , out1) , true  , inj₁ refl)
                        ∷ ((Bool , out1) , false , inj₂ refl) ∷ []
  preimgS (_ , out2') _ = ((Bool , out2) , true  , inj₁ refl)
                        ∷ ((Bool , out2) , false , inj₂ refl) ∷ []
  preimgS (_ , inn)   _ = []
  preimgS (_ , out1)  _ = []
  preimgS (_ , out2)  _ = []

  RenSPLIT : SProc
  RenSPLIT = SPLIT ⟦ Rre ¿ preimgS ⟧
```

The headline statement — both FDR `[FD=` asserts at once:

```agda
  renSplit≈FD-split' : RenSPLIT ≈FD SPLIT'
```

**Where the nondeterminism appears.**  At the root, the renamed offer at
`in'` collects the source offers of *both* preimages `inn.true`/`inn.false`
— a two-element list — so `rnFan` builds the **fan-in node**: a `react`
with *no* visible offers and the two renamed sources as τ-branches
(`rnBranch`), i.e. a freshly manufactured *internal choice* between the
two (data-distinguished, hence at distinct renamed states!) source
continuations.  This is the exact τ-structure of `SPLIT'`'s post-`in'`
state `T₁` (`⊓` = `br2` under the loop), which is why a lockstep `≈DR`
relation closes.  At the post-read states the fan-in *degenerates*: `S₁ x`
offers only the single payload `x` on its output channel, so only one of
the two collected preimages is enabled and `rnFan`'s singleton case yields
a bare (τ-free) renamed continuation — determinism is preserved pointwise
there, manufactured only where the collected list has two entries.

```agda
  RenS₁ : Bool → SProc
  RenS₁ x = S₁ x ⟦ Rre ¿ preimgS ⟧

  Ren₂ : SProc
  Ren₂ = S₂ ⟦ Rre ¿ preimgS ⟧

  FanIn : SProc
  FanIn = ptree (react (λ _ _ → nothing)
                       (rnBranch Rre preimgS (S₁ true ∷ S₁ false ∷ [])))
```

The named renamed steps, all definitional through `_⟦_¿_⟧` (§2.5's
pattern; the fan-in τs mirror `T₁-τ` at the same `fin` index shape).

```agda
  Ren-in : RenSPLIT ─[ ev lblIn' ]─► FanIn
  Ren-in = sVis {at = ⊤ , in'} {a = tt} refl refl

  FanIn-τ : ∀ x → FanIn ─[ τ ]─► RenS₁ x
  FanIn-τ true  = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl
  FanIn-τ false = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

  RenS₁-out : ∀ x → RenS₁ x ─[ ev (lblOut' x) ]─► Ren₂
  RenS₁-out true  = sVis {at = ⊤ , out1'} {a = tt} refl refl
  RenS₁-out false = sVis {at = ⊤ , out2'} {a = tt} refl refl

  Ren₂-τ : Ren₂ ─[ τ ]─► RenSPLIT
  Ren₂-τ = sSil refl
```

### §3.5 Step inversions for the renamed states

The §2.6 pattern, adjusted for the fan-in.  At the root the only enabled
target is `in'` (dead targets reduce their whole offer pipeline to
`nothing`: primed outputs collect from source channels the root does not
offer; unprimed channels have an empty preimage), and its successor is
pinned to the fan-in node.  The root's τ-part is `extBranch` over
`SPLIT`'s everywhere-`nothing` τ-map (§2.6's `with extBwd (pair p q) | br`
re-abstraction for the stuck `pair` case).

```agda
  RenSPLIT-ev-inv : ∀ {l : Event√ (Poly.⊤ {lzero})} {t′ : SProc}
                  → RenSPLIT ─[ ev l ]─► t′ → (l ≡ lblIn') × (t′ ≡ FanIn)
  RenSPLIT-ev-inv (sRet eq) = case eq of λ ()
  RenSPLIT-ev-inv (sVis {at = _ , in'}   refl br) = refl , sym (just-injective br)
  RenSPLIT-ev-inv (sVis {at = _ , out1'} refl br) = case br of λ ()
  RenSPLIT-ev-inv (sVis {at = _ , out2'} refl br) = case br of λ ()
  RenSPLIT-ev-inv (sVis {at = _ , inn}   refl br) = case br of λ ()
  RenSPLIT-ev-inv (sVis {at = _ , out1}  refl br) = case br of λ ()
  RenSPLIT-ev-inv (sVis {at = _ , out2}  refl br) = case br of λ ()

  RenSPLIT-no-τ : ∀ {t′ : SProc} → RenSPLIT ─[ τ ]─► t′ → ⊥
  RenSPLIT-no-τ (sSil eq) = case eq of λ ()
  RenSPLIT-no-τ (sTau {i = _ , base _} refl br) = case br of λ ()
  RenSPLIT-no-τ (sTau {i = _ , fin}    refl br) = case br of λ ()
  RenSPLIT-no-τ (sTau {i = _ , pair p q} refl br) with extBwd (pair p q) | br
  ... | just _  | br′ = case br′ of λ ()
  ... | nothing | br′ = case br′ of λ ()
```

The fan-in node itself: no visible offers at all (its offer map is the
literal `λ _ _ → nothing`), and its τ-branches are exactly the two
renamed post-read states — `rnBranch` answers only at a `fin` index, with
`rnNth` selecting from the two-element list.

```agda
  FanIn-no-ev : ∀ {l : Event√ (Poly.⊤ {lzero})} {t′ : SProc} → FanIn ─[ ev l ]─► t′ → ⊥
  FanIn-no-ev (sRet eq)      = case eq of λ ()
  FanIn-no-ev (sVis refl br) = case br of λ ()

  FanIn-τ-inv : ∀ {t′ : SProc} → FanIn ─[ τ ]─► t′
              → (t′ ≡ RenS₁ true) ⊎ (t′ ≡ RenS₁ false)
  FanIn-τ-inv (sSil eq) = case eq of λ ()
  FanIn-τ-inv (sTau {i = _ , base _}   refl br) = case br of λ ()
  FanIn-τ-inv (sTau {i = _ , pair _ _} refl br) = case br of λ ()
  FanIn-τ-inv (sTau {i = _ , fin} {a = lift fzero} refl br) =
    inj₁ (sym (just-injective br))
  FanIn-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)} refl br) =
    inj₂ (sym (just-injective br))
  FanIn-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) = case br of λ ()
```

The renamed post-read state `RenS₁ x` fires exactly its parity-selected
*primed* output: at the enabled target the collected list is the
*singleton* enabled source (`x ≟ x` fires, the other payload's `x ≟ ¬x`
refuses — closed-`Bool` reductions), so `rnFan` yields the bare renamed
`S₂` with no fan-in τ; every other target's pipeline reduces to
`nothing`.  Its τ-part is again `extBranch` over an everywhere-`nothing`
source τ-map.

```agda
  RenS₁-ev-inv : ∀ x {l : Event√ (Poly.⊤ {lzero})} {t′ : SProc}
               → RenS₁ x ─[ ev l ]─► t′ → (l ≡ lblOut' x) × (t′ ≡ Ren₂)
  RenS₁-ev-inv true  (sRet eq) = case eq of λ ()
  RenS₁-ev-inv true  (sVis {at = _ , out1'} refl br) = refl , sym (just-injective br)
  RenS₁-ev-inv true  (sVis {at = _ , out2'} refl br) = case br of λ ()
  RenS₁-ev-inv true  (sVis {at = _ , in'}   refl br) = case br of λ ()
  RenS₁-ev-inv true  (sVis {at = _ , inn}   refl br) = case br of λ ()
  RenS₁-ev-inv true  (sVis {at = _ , out1}  refl br) = case br of λ ()
  RenS₁-ev-inv true  (sVis {at = _ , out2}  refl br) = case br of λ ()
  RenS₁-ev-inv false (sRet eq) = case eq of λ ()
  RenS₁-ev-inv false (sVis {at = _ , out2'} refl br) = refl , sym (just-injective br)
  RenS₁-ev-inv false (sVis {at = _ , out1'} refl br) = case br of λ ()
  RenS₁-ev-inv false (sVis {at = _ , in'}   refl br) = case br of λ ()
  RenS₁-ev-inv false (sVis {at = _ , inn}   refl br) = case br of λ ()
  RenS₁-ev-inv false (sVis {at = _ , out1}  refl br) = case br of λ ()
  RenS₁-ev-inv false (sVis {at = _ , out2}  refl br) = case br of λ ()

  RenS₁-no-τ : ∀ x {t′ : SProc} → RenS₁ x ─[ τ ]─► t′ → ⊥
  RenS₁-no-τ true  (sSil eq) = case eq of λ ()
  RenS₁-no-τ true  (sTau {i = _ , base _} refl br) = case br of λ ()
  RenS₁-no-τ true  (sTau {i = _ , fin}    refl br) = case br of λ ()
  RenS₁-no-τ true  (sTau {i = _ , pair p q} refl br) with extBwd (pair p q) | br
  ... | just _  | br′ = case br′ of λ ()
  ... | nothing | br′ = case br′ of λ ()
  RenS₁-no-τ false (sSil eq) = case eq of λ ()
  RenS₁-no-τ false (sTau {i = _ , base _} refl br) = case br of λ ()
  RenS₁-no-τ false (sTau {i = _ , fin}    refl br) = case br of λ ()
  RenS₁-no-τ false (sTau {i = _ , pair p q} refl br) with extBwd (pair p q) | br
  ... | just _  | br′ = case br′ of λ ()
  ... | nothing | br′ = case br′ of λ ()
```

`Ren₂` needs no bespoke inversion: `force Ren₂` computes to
`sil RenSPLIT`, so the generic `sil` helpers apply with `refl` (§2.6).

### §3.6 Divergence-freedom, the bisimulation, and the theorem

Every related state is stable or one `sil`/one resolved τ away from a
stable state: the only τ-sources are the fan-in / `⊓` states (whose
successors are τ-free) and the two re-entry `sil`s.

```agda
  ¬div-RenSPLIT : Diverges RenSPLIT → ⊥
  ¬div-RenSPLIT d = RenSPLIT-no-τ (Diverges.step d)

  ¬div-FanIn : Diverges FanIn → ⊥
  ¬div-FanIn d = halt (FanIn-τ-inv (Diverges.step d)) (Diverges.rest d)
    where
    halt : ∀ {nx} → (nx ≡ RenS₁ true) ⊎ (nx ≡ RenS₁ false) → Diverges nx → ⊥
    halt (inj₁ refl) rest = RenS₁-no-τ true  (Diverges.step rest)
    halt (inj₂ refl) rest = RenS₁-no-τ false (Diverges.step rest)

  ¬div-Ren₂ : Diverges Ren₂ → ⊥
  ¬div-Ren₂ d = ¬div-RenSPLIT (divergesSil refl d)

  ¬div-SPLIT' : Diverges SPLIT' → ⊥
  ¬div-SPLIT' d = loop-pfx-no-τ in' (λ _ → choiceBody) split'K (Diverges.step d)

  ¬div-T₂ : ∀ x → Diverges (T₂ x) → ⊥
  ¬div-T₂ true  d = loop-pfx-no-τ out1' (λ _ → Skip) split'K (Diverges.step d)
  ¬div-T₂ false d = loop-pfx-no-τ out2' (λ _ → Skip) split'K (Diverges.step d)

  ¬div-T₁ : Diverges T₁ → ⊥
  ¬div-T₁ d = halt (T₁-τ-inv (Diverges.step d)) (Diverges.rest d)
    where
    halt : ∀ {nx} → (nx ≡ T₂ true) ⊎ (nx ≡ T₂ false) → Diverges nx → ⊥
    halt (inj₁ refl) rest = ¬div-T₂ true  rest
    halt (inj₂ refl) rest = ¬div-T₂ false rest

  ¬div-T₃ : Diverges T₃ → ⊥
  ¬div-T₃ d = ¬div-SPLIT' (divergesSil refl d)
```

The relation pairs the four corresponding state shapes — crucially the
fan-in node against the `⊓` state, matching manufactured τ against
internal-choice τ *strongly* (every weak answer is a single step).

```agda
  data QQ : SProc → SProc → Set₁ where
    q₀ : QQ RenSPLIT SPLIT'
    q₁ : QQ FanIn T₁
    q₂ : ∀ x → QQ (RenS₁ x) (T₂ x)
    q₃ : QQ Ren₂ T₃

  QQ-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → QQ p q → p ─[ ev l ]─► p′
            → Σ[ q′ ∈ SProc ] ((q ═[ ev l ]═► q′) × QQ p′ q′)
  QQ-fwd-ev q₀ stp with RenSPLIT-ev-inv stp
  ... | refl , refl = T₁ , wev τ*-refl SPLIT'-in τ*-refl , q₁
  QQ-fwd-ev q₁ stp = ⊥-elim (FanIn-no-ev stp)
  QQ-fwd-ev (q₂ x) stp with RenS₁-ev-inv x stp
  ... | refl , refl = T₃ , wev τ*-refl (T₂-out x) τ*-refl , q₃
  QQ-fwd-ev q₃ stp = ⊥-elim (sil-no-ev refl stp)

  QQ-fwd-τ : ∀ {p q p′} → QQ p q → p ─[ τ ]─► p′
           → Σ[ q′ ∈ SProc ] ((q ═[ τ ]═► q′) × QQ p′ q′)
  QQ-fwd-τ q₀ stp = ⊥-elim (RenSPLIT-no-τ stp)
  QQ-fwd-τ q₁ stp with FanIn-τ-inv stp
  ... | inj₁ refl = T₂ true  , wτ (τ*-step (T₁-τ true)  τ*-refl) , q₂ true
  ... | inj₂ refl = T₂ false , wτ (τ*-step (T₁-τ false) τ*-refl) , q₂ false
  QQ-fwd-τ (q₂ x) stp = ⊥-elim (RenS₁-no-τ x stp)
  QQ-fwd-τ q₃ stp with sil-τ-uniq refl stp
  ... | refl = SPLIT' , wτ (τ*-step T₃-τ τ*-refl) , q₀

  QQ-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → QQ p q → q ─[ ev l ]─► q′
            → Σ[ p′ ∈ SProc ] ((p ═[ ev l ]═► p′) × QQ p′ q′)
  QQ-bwd-ev q₀ stp with loop-pfx-ev-inv in' (λ _ → choiceBody) split'K stp
  ... | x , refl , refl = FanIn , wev τ*-refl Ren-in τ*-refl , q₁
  QQ-bwd-ev q₁ stp = ⊥-elim (T₁-no-ev stp)
  QQ-bwd-ev (q₂ true) stp with loop-pfx-ev-inv out1' (λ _ → Skip) split'K stp
  ... | y , refl , refl = Ren₂ , wev τ*-refl (RenS₁-out true) τ*-refl , q₃
  QQ-bwd-ev (q₂ false) stp with loop-pfx-ev-inv out2' (λ _ → Skip) split'K stp
  ... | y , refl , refl = Ren₂ , wev τ*-refl (RenS₁-out false) τ*-refl , q₃
  QQ-bwd-ev q₃ stp = ⊥-elim (sil-no-ev refl stp)

  QQ-bwd-τ : ∀ {p q q′} → QQ p q → q ─[ τ ]─► q′
           → Σ[ p′ ∈ SProc ] ((p ═[ τ ]═► p′) × QQ p′ q′)
  QQ-bwd-τ q₀ stp = ⊥-elim (loop-pfx-no-τ in' (λ _ → choiceBody) split'K stp)
  QQ-bwd-τ q₁ stp with T₁-τ-inv stp
  ... | inj₁ refl = RenS₁ true  , wτ (τ*-step (FanIn-τ true)  τ*-refl) , q₂ true
  ... | inj₂ refl = RenS₁ false , wτ (τ*-step (FanIn-τ false) τ*-refl) , q₂ false
  QQ-bwd-τ (q₂ true)  stp = ⊥-elim (loop-pfx-no-τ out1' (λ _ → Skip) split'K stp)
  QQ-bwd-τ (q₂ false) stp = ⊥-elim (loop-pfx-no-τ out2' (λ _ → Skip) split'K stp)
  QQ-bwd-τ q₃ stp with sil-τ-uniq refl stp
  ... | refl = RenSPLIT , wτ (τ*-step Ren₂-τ τ*-refl) , q₀

  QQ-¬divL : ∀ {p q} → QQ p q → Diverges p → ⊥
  QQ-¬divL q₀     = ¬div-RenSPLIT
  QQ-¬divL q₁     = ¬div-FanIn
  QQ-¬divL (q₂ x) = λ d → RenS₁-no-τ x (Diverges.step d)
  QQ-¬divL q₃     = ¬div-Ren₂

  QQ-¬divR : ∀ {p q} → QQ p q → Diverges q → ⊥
  QQ-¬divR q₀     = ¬div-SPLIT'
  QQ-¬divR q₁     = ¬div-T₁
  QQ-¬divR (q₂ x) = ¬div-T₂ x
  QQ-¬divR q₃     = ¬div-T₃

  module MQ = DRFromRel QQ QQ-fwd-ev QQ-fwd-τ QQ-bwd-ev QQ-bwd-τ QQ-¬divL QQ-¬divR

  renSplit≈DR-split' : RenSPLIT ≈DR SPLIT'
  renSplit≈DR-split' = MQ.rel→dr q₀
```

The headline: `≈DR` weakens to the failures-divergences equivalence,
whose two halves are the book's `[FD=` asserts in both directions — a
*deterministic* process, non-injectively renamed, is FD-equal to a
*nondeterministic* one.

```agda
  renSplit≈FD-split' = drbisim→≈FD renSplit≈DR-split'
```
