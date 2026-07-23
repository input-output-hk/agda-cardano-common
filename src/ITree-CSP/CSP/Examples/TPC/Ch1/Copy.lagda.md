# TPC/UCS chapter 1: `COPY`, the bounded/unbounded buffers, and `Abs1`/`Abs2`

The fourth of five example modules porting chapter-1 processes from A.W.
Roscoe's two CSP books — *The Theory and Practice of Concurrency* (TPC) and
*Understanding Concurrent Systems* (UCS) — to this process-tree
formalisation. Sources:

- `fdr-examples/tpc/chapter01/chapter1.csp` (TPC §1.1: `COPY`, `Binf`, `BN`)
- `fdr-examples/ucs/chapter01/ucs1.csp` (UCS ch. 1: `COPY`, `Binf`, `BN`,
  `Abs1`, `Abs2`)

```csp
channel left, right : {0,1}

COPY = left?x -> right!x -> COPY

Binf(s) = if s==<> then left?x -> Binf(<x>)
                   else (left?x -> Binf(s^<x>)
                        [] right!head(s) -> Binf(tail(s)))

BN(s,N) = if s==<> then left?x -> BN(<x>,N)
          else if #s == N then right!head(s) -> BN(tail(s),N)
                   else (left?x -> BN(s^<x>,N)
                        [] right!head(s) -> BN(tail(s),N))

channel aleft, aright : Int

Abs1 = aleft?x -> aright!(if x <0 then -x else x) -> Abs1
Abs2 = aleft?x -> (if x < 0 then aright!(-x) -> Abs2
                           else aright!x -> Abs2)
```

`Binf`/`BN` grow their state at the *right* end (`s^<x>`, i.e. append) and
drain it from the *left* end (`head`/`tail`), the reverse of the usual
textbook picture — the `.csp` source calls this out explicitly, and we keep
the same convention below (`List Bool` with the oldest element at the head,
`_∷ʳ_` appending the newest at the tail).

The UCS book model-checks `Abs1`/`Abs2` over `Int = {-5..5}` so FDR's
state space stays finite; nothing in the process *definitions* needs that
restriction, so here we give `aleft`/`aright` the full (unbounded) `ℤ` and
only bound the alphabet if a later, model-checking-style example needs it.

This module carries both the definitions **and** their verification
(§§2.4–2.8 for the buffers, §3.3 for `Abs1`/`Abs2`), porting the proof
machinery of `UpDown.lagda.md` §§5–6 and `DayRoutine.lagda.md` §5 and
generalising it from nullary events to payload-carrying ones. Unlike its
siblings it needs **two** event
alphabets living side by side: `{left, right}` over `Bool` payloads for the
buffers, and `{aleft, aright}` over `ℤ` payloads for `Abs1`/`Abs2`. Each
alphabet gets its own `CSP.Operators` instantiation, and since both
instantiations export clashing operator names (`_⟶_`, `_□_`, `Skip`, `loop`,
…), each lives in its own named sub-module (`Buffers`, `Abs`) that is
**not** re-opened at the top level. Downstream users therefore refer to the
buffer processes as `CSP.Examples.TPC.Ch1.Copy.Buffers.COPY` etc., and the
`Abs` processes as `CSP.Examples.TPC.Ch1.Copy.Abs.Abs1` etc.

## §1. Shared imports

Both sub-modules need `Bool` (the buffers' payload type, and the type of
the `◁_▷_` guards) and the polymorphic-unit return type `Poly.⊤ {lzero}`
shared by every top-level process below. `DecEq-Bool`, `DecEq-List` and
`DecEq-ℤ` (`Class.DecEq.Instances`) are `open import`ed once here — as
plain `open`s rather than qualified `import`s — so that ordinary instance
resolution finds them inside *both* sub-modules below: `DecEq-Bool` for the
buffers' `Output`/`_□_` (return type `List Bool`, via `DecEq-List`), and
`DecEq-ℤ` for `Abs`'s `Output` (payload type `ℤ`). Neither sub-module needs
`_□_`/`⊓` at the `Poly.⊤`-typed top level, so — unlike `UpDown.lagda.md` and
`DayRoutine.lagda.md` — no `DecEq-⊤poly` instance is required here. The
remaining imports (`Maybe`, `Σ`, `case_of_`, `_≟_`, the `lift`/`Fin`
patterns, …) are alphabet-independent proof plumbing shared by the two
verification sections below (§§2.4–2.8, §3.3).

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch1.Copy where

open import Level using (lift) renaming (zero to lzero)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false; if_then_else_; not)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; length; _∷ʳ_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-Bool; DecEq-List; DecEq-ℤ)

open import Process_Trees
```

## §2. The buffer half: `COPY`, `Binf`, `BN`

`DATA = {0,1}` becomes `Bool`, and `left`/`right` are the two channels,
both carrying a single `Bool`.

```agda
module Buffers where

  data Ch : Set → Set where
    left right : Ch Bool

  Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
  Ch-≟ (_ , left)  (_ , left)  = yes refl
  Ch-≟ (_ , right) (_ , right) = yes refl
  Ch-≟ (_ , left)  (_ , right) = no λ ()
  Ch-≟ (_ , right) (_ , left)  = no λ ()

  open import CSP.Operators Ch-≟

  CProc : Set₁
  CProc = PTree Ch (ExtI Ch) (Poly.⊤ {lzero})
```

### §2.1 `COPY = left?x -> right!x -> COPY`

The simplest buffer: read on `left`, immediately write the same value on
`right`, loop.

```agda
  COPY : CProc
  COPY = loop0 (left ⟶ λ x → (right ! x ⟶ Skip))
```

### §2.2 `Binf` — the unbounded buffer

`Binf(s)`'s state `s` is a `List Bool`, oldest element at the head. When
empty, only `left?x` is offered (seeding the buffer with `⟨x⟩`); once
non-empty, `left?x` (append `x` at the tail, via `_∷ʳ_`) and
`right!head(s)` (drop the head, output it) are both offered via `_□_` —
which needs `DecEq (List Bool)`, resolved from `DecEq-List` + `DecEq-Bool`
(§1).

```agda
  binf-step : List Bool → PTree Ch (ExtI Ch) (List Bool)
  binf-step []      = left ⟶ λ x → Ret (x ∷ [])
  binf-step (y ∷ s) = (left ⟶ λ x → Ret ((y ∷ s) ∷ʳ x))
                    □ (right ! y ⟶ Ret s)

  Binf : List Bool → CProc
  Binf = loop binf-step
```

### §2.3 `BN` — the buffer bounded above by `N`

`BN(s,N)` is `Binf(s)` except that once `s` is full (`#s == N`) only the
output branch is offered — no more `left?x` until something has been
drained. The guarded alternative is `_◁_▷_` (`P ◁ b ▷ Q = if b then P else
Q`): the buffer being processed in this branch is `y ∷ s`, whose length is
`suc (length s)`, so the guard `suc (length s) ≡ᵇ N` tests whether the
buffer is *already* at capacity `N` — exactly the `.csp` source's
fullness check `#s == N`. When it holds we take the output-only branch (no
read happens here); otherwise both branches are offered exactly as in
`Binf`.

```agda
  bn-step : ℕ → List Bool → PTree Ch (ExtI Ch) (List Bool)
  bn-step N []      = left ⟶ λ x → Ret (x ∷ [])
  bn-step N (y ∷ s) = (right ! y ⟶ Ret s)
                    ◁ (suc (length s) ≡ᵇ N) ▷
                      ((left ⟶ λ x → Ret ((y ∷ s) ∷ʳ x)) □ (right ! y ⟶ Ret s))

  BN : ℕ → List Bool → CProc
  BN N = loop (bn-step N)
```

### §2.4 Verification: the buffer theorems

The `.csp` sources leave the buffer relationships implicit; the two
standard facts are

- **`COPY` is the one-place buffer**: `COPY ≈DR BN 1 []` —
  divergence-respecting weak bisimilarity, which subsumes the FDR asserts
  `[T=`/`[F=`/`[FD=` in both directions;
- **the bounded buffer trace-refines the unbounded one**:
  `Binf s [T= BN N s` for every bound `N` and shared start state `s` (the
  headline instance is `s = []`).

The machinery is ported from `UpDown.lagda.md` §§5–6 and
`DayRoutine.lagda.md` §5 (loop-node inversions, the factored-out
corecursions `DRFromRel`/`WSimFromRel`), re-instantiated at the `Ch`
alphabet. What is genuinely new here is the **payload**: the buffers'
states are `Output` nodes (`right ! y ⟶ ·`) and `□`s of a reader prefix
against an output. An output's offer map is stuck on the payload decision
`y ≟ y` (which does not reduce for an *open* `y : Bool`), so the
output-step lemmas below (`C₁-right`, `BN1-right`, `Binf∷-right`)
case-split the payload: at a closed `true`/`false` the decision reduces
definitionally and a bare `sVis refl refl` fires the step. (The
`ℤ`-payload `Abs` half cannot enumerate its payloads, so §3.3 discharges
the same stuck decision propositionally instead.)

```agda
  open import Semantics.LTS       {E = Ch} {I = ExtI Ch} hiding (Diverges)
  open import Semantics.WeakBisim {E = Ch} {I = ExtI Ch}
    using (WSimF; _═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
  open import Semantics.Failures  {E = Ch} {I = ExtI Ch} using (_⊑T_)
  open import Semantics.WeakSim   {E = Ch} {I = ExtI Ch}
  open import Semantics.DRBisim   {E = Ch} {I = ExtI Ch}
  open import CSP.Laws.Traces.PrefixInversion Ch-≟
    using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
           sil-no-ev; sil-τ-uniq; divergesSil)
  open import Semantics.BisimFromRel {E = Ch} {I = ExtI Ch}
  open WSimF

  lblL lblR : Bool → Event√ (Poly.⊤ {lzero})
  lblL x = evl (evLabel Bool left x)
  lblR y = evl (evLabel Bool right y)
```

The two headline statements:

```agda
  COPY≈DRBN1 : COPY ≈DR BN 1 []

  Binf⊑TBN : ∀ N s₀ → Binf s₀ ⊑T BN N s₀
```

### §2.5 Node-level scaffolding

Step inversions for the three stable loop-node shapes (reader prefix,
output, reader `□` output), following `UpDown` §6.4 but generalised to
payloads: a prefix state fires its event at *every* payload `x` (hence the
`Σ` in the conclusion), an output state fires only its carried value, and
the `□` state fires either summand. All three shapes are τ-free. The
prefix and output inversions are the channel-generic `loop-pfx-*`/
`loop-out-*` lemmas imported from `CSP.Laws.Traces.PrefixInversion` in the
§2.4 block above; only the `□` shape's inversion remains local (its
statement is pinned to this module's `left`-reader-vs-`right`-output
binary `□`).

```agda
  loop-□-ev-inv : ∀ {A : Set} ⦃ _ : DecEq A ⦄
                    (P₁ : Bool → PTree Ch (ExtI Ch) A) (y : Bool)
                    (P₂ : PTree Ch (ExtI Ch) A)
                    (K : A → PTree Ch (ExtI Ch) (A ⊎ Poly.⊤ {lzero}))
                    {l : Event√ (Poly.⊤ {lzero})} {t′ : CProc}
                → iter-bind (((left ⟶ P₁) □ (right ! y ⟶ P₂)) >>= (λ a′ → Ret (inj₁ a′))) K
                    ─[ ev l ]─► t′
                → (Σ[ x ∈ Bool ] ((l ≡ lblL x)
                       × (t′ ≡ iter-bind (P₁ x >>= (λ a′ → Ret (inj₁ a′))) K)))
                  ⊎ ((l ≡ lblR y) × (t′ ≡ iter-bind (P₂ >>= (λ a′ → Ret (inj₁ a′))) K))
  loop-□-ev-inv P₁ y P₂ K (sRet eq) = case eq of λ ()
  loop-□-ev-inv P₁ y P₂ K (sVis {at = _ , left}  {a = x} refl br) =
    inj₁ (x , refl , sym (just-injective br))
  loop-□-ev-inv P₁ y P₂ K (sVis {at = _ , right} {a = a} refl br) with a ≟ y
  ... | yes refl = inj₂ (refl , sym (just-injective br))
  ... | no _     = ⊥-elim (case br of λ ())

  loop-□-no-τ : ∀ {A : Set} ⦃ _ : DecEq A ⦄
                  (P₁ : Bool → PTree Ch (ExtI Ch) A) (y : Bool)
                  (P₂ : PTree Ch (ExtI Ch) A)
                  (K : A → PTree Ch (ExtI Ch) (A ⊎ Poly.⊤ {lzero})) {t′ : CProc}
              → iter-bind (((left ⟶ P₁) □ (right ! y ⟶ P₂)) >>= (λ a′ → Ret (inj₁ a′))) K
                  ─[ τ ]─► t′ → ⊥
  loop-□-no-τ P₁ y P₂ K (sSil eq) = case eq of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , base _}            refl br) = case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , fin}               refl br) = case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , pair fin _} {a = lift fzero , _}           refl br) =
    case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , _}    refl br) =
    case br of λ ()
  loop-□-no-τ P₁ y P₂ K (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl br) =
    case br of λ ()
```

The `sil`-headed states (the loop re-entries) offer no visible event and
take exactly one τ, to the named successor — `sil-no-ev`/`sil-τ-uniq`
(and, in §2.6, `divergesSil`), imported from
`CSP.Laws.Traces.PrefixInversion` in the §2.4 block above.

### §2.6 Reachable states and strong steps

`COPY = loop0 (left ⟶ λ x → right ! x ⟶ Skip)` passes through the
post-`left` output state `C₁ x`, the silent re-entry state `C₂`, and back.
As in `UpDown` §5.3 the states are `iter-bind` terms — definitional
unfoldings of the loop's successors, checked by the `refl`s (and
`≟`-firing lemmas) in the step proofs.

```agda
  copyK : Poly.⊤ {lzero} → PTree Ch (ExtI Ch) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
  copyK _ = (left ⟶ λ x → (right ! x ⟶ Skip)) >>= (λ a′ → Ret (inj₁ a′))

  C₁ : Bool → CProc
  C₁ x = iter-bind ((right ! x ⟶ Skip) >>= (λ a′ → Ret (inj₁ a′))) copyK

  C₂ : CProc
  C₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) copyK

  COPY-left : ∀ x → COPY ─[ ev (lblL x) ]─► C₁ x
  COPY-left x = sVis {at = Bool , left} {a = x} refl refl

  C₁-right : ∀ x → C₁ x ─[ ev (lblR x) ]─► C₂
  C₁-right true  = sVis {at = Bool , right} {a = true}  refl refl
  C₁-right false = sVis {at = Bool , right} {a = false} refl refl

  C₂-τ : C₂ ─[ τ ]─► COPY
  C₂-τ = sSil refl
```

`BN`/`Binf` are *stateful* loops: after every event the body returns the
next buffer state `s` and the loop silently re-enters at `s`. The states
after an event therefore all have the same shape, the pre-re-entry
`BNre N s` / `Binfre s` (one τ away from `BN N s` / `Binf s`).

```agda
  bnK : ℕ → List Bool → PTree Ch (ExtI Ch) (List Bool ⊎ Poly.⊤ {lzero})
  bnK N s = bn-step N s >>= (λ s′ → Ret (inj₁ s′))

  BNre : ℕ → List Bool → CProc
  BNre N s = iter-bind (Ret s >>= (λ s′ → Ret (inj₁ s′))) (bnK N)

  BNre-τ : ∀ N s → BNre N s ─[ τ ]─► BN N s
  BNre-τ N s = sSil refl

  BN[]-left : ∀ N x → BN N [] ─[ ev (lblL x) ]─► BNre N (x ∷ [])
  BN[]-left N x = sVis {at = Bool , left} {a = x} refl refl

  BN1-right : ∀ x → BN 1 (x ∷ []) ─[ ev (lblR x) ]─► BNre 1 []
  BN1-right true  = sVis {at = Bool , right} {a = true}  refl refl
  BN1-right false = sVis {at = Bool , right} {a = false} refl refl

  binfK : List Bool → PTree Ch (ExtI Ch) (List Bool ⊎ Poly.⊤ {lzero})
  binfK s = binf-step s >>= (λ s′ → Ret (inj₁ s′))

  Binfre : List Bool → CProc
  Binfre s = iter-bind (Ret s >>= (λ s′ → Ret (inj₁ s′))) binfK

  Binfre-τ : ∀ s → Binfre s ─[ τ ]─► Binf s
  Binfre-τ s = sSil refl

  Binf[]-left : ∀ x → Binf [] ─[ ev (lblL x) ]─► Binfre (x ∷ [])
  Binf[]-left x = sVis {at = Bool , left} {a = x} refl refl

  Binf∷-left : ∀ y s x → Binf (y ∷ s) ─[ ev (lblL x) ]─► Binfre ((y ∷ s) ∷ʳ x)
  Binf∷-left y s x = sVis {at = Bool , left} {a = x} refl refl

  Binf∷-right : ∀ y s → Binf (y ∷ s) ─[ ev (lblR y) ]─► Binfre s
  Binf∷-right true  s = sVis {at = Bool , right} {a = true}  refl refl
  Binf∷-right false s = sVis {at = Bool , right} {a = false} refl refl
```

None of the states reachable in the `COPY`-vs-`BN 1 []` bisimulation
diverges: each is stable (its first `Diverges.step` is refuted by the
`no-τ` inversion for its shape) or a `sil` state whose single τ lands on a
stable one.

```agda
  ¬div-COPY : Diverges COPY → ⊥
  ¬div-COPY d = loop-pfx-no-τ left (λ x → (right ! x ⟶ Skip)) copyK (Diverges.step d)

  ¬div-C₁ : ∀ x → Diverges (C₁ x) → ⊥
  ¬div-C₁ x d = loop-out-no-τ right x Skip copyK (Diverges.step d)

  ¬div-C₂ : Diverges C₂ → ⊥
  ¬div-C₂ d = ¬div-COPY (divergesSil refl d)

  ¬div-BN[] : Diverges (BN 1 []) → ⊥
  ¬div-BN[] d = loop-pfx-no-τ left (λ x → Ret (x ∷ [])) (bnK 1) (Diverges.step d)

  ¬div-BN1 : ∀ x → Diverges (BN 1 (x ∷ [])) → ⊥
  ¬div-BN1 x d = loop-out-no-τ right x (Ret []) (bnK 1) (Diverges.step d)

  ¬div-BNre1 : ∀ x → Diverges (BNre 1 (x ∷ [])) → ⊥
  ¬div-BNre1 x d = ¬div-BN1 x (divergesSil refl d)

  ¬div-BNre[] : Diverges (BNre 1 []) → ⊥
  ¬div-BNre[] d = ¬div-BN[] (divergesSil refl d)
```

### §2.7 `COPY ≈DR BN 1 []`

The coinductive machinery is the shared `DRFromRel` principle imported
from `Semantics.BisimFromRel` in the §2.4 block above: any step-matching,
divergence-free binary relation is contained in `≈DR`.

The relation. `COPY` re-enters its loop only after `right` (one `sil`);
`BN 1` re-enters after *every* event (its body returns the new buffer
state). So after `left?x` the pair is `(C₁ x , BNre 1 ⟨x⟩)` — `BN`'s
pending re-entry τ is answered by `C₁ x` standing still, giving the
τ-shifted pair `(C₁ x , BN 1 ⟨x⟩)` — and after `right!x` both sides sit
at their re-entry states `(C₂ , BNre 1 [])`, whose τs close the cycle.

```agda
  data RCB : CProc → CProc → Set₁ where
    k₀ : RCB COPY (BN 1 [])
    k₁ : ∀ x → RCB (C₁ x) (BNre 1 (x ∷ []))
    k₂ : ∀ x → RCB (C₁ x) (BN 1 (x ∷ []))
    k₃ : RCB C₂ (BNre 1 [])

  RCB-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RCB p q → p ─[ ev l ]─► p′
             → Σ[ q′ ∈ CProc ] ((q ═[ ev l ]═► q′) × RCB p′ q′)
  RCB-fwd-ev k₀ stp with loop-pfx-ev-inv left (λ x → (right ! x ⟶ Skip)) copyK stp
  ... | x , refl , refl = BNre 1 (x ∷ []) , wev τ*-refl (BN[]-left 1 x) τ*-refl , k₁ x
  RCB-fwd-ev (k₁ x) stp with loop-out-ev-inv right x Skip copyK stp
  ... | refl , refl =
        BNre 1 [] , wev (τ*-step (BNre-τ 1 (x ∷ [])) τ*-refl) (BN1-right x) τ*-refl , k₃
  RCB-fwd-ev (k₂ x) stp with loop-out-ev-inv right x Skip copyK stp
  ... | refl , refl = BNre 1 [] , wev τ*-refl (BN1-right x) τ*-refl , k₃
  RCB-fwd-ev k₃ stp = ⊥-elim (sil-no-ev refl stp)

  RCB-fwd-τ : ∀ {p q p′} → RCB p q → p ─[ τ ]─► p′
            → Σ[ q′ ∈ CProc ] ((q ═[ τ ]═► q′) × RCB p′ q′)
  RCB-fwd-τ k₀ stp = ⊥-elim (loop-pfx-no-τ left (λ x → (right ! x ⟶ Skip)) copyK stp)
  RCB-fwd-τ (k₁ x) stp = ⊥-elim (loop-out-no-τ right x Skip copyK stp)
  RCB-fwd-τ (k₂ x) stp = ⊥-elim (loop-out-no-τ right x Skip copyK stp)
  RCB-fwd-τ k₃ stp with sil-τ-uniq refl stp
  ... | refl = BN 1 [] , wτ (τ*-step (BNre-τ 1 []) τ*-refl) , k₀

  RCB-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → RCB p q → q ─[ ev l ]─► q′
             → Σ[ p′ ∈ CProc ] ((p ═[ ev l ]═► p′) × RCB p′ q′)
  RCB-bwd-ev k₀ stp with loop-pfx-ev-inv left (λ x → Ret (x ∷ [])) (bnK 1) stp
  ... | x , refl , refl = C₁ x , wev τ*-refl (COPY-left x) τ*-refl , k₁ x
  RCB-bwd-ev (k₁ x) stp = ⊥-elim (sil-no-ev refl stp)
  RCB-bwd-ev (k₂ x) stp with loop-out-ev-inv right x (Ret []) (bnK 1) stp
  ... | refl , refl = C₂ , wev τ*-refl (C₁-right x) τ*-refl , k₃
  RCB-bwd-ev k₃ stp = ⊥-elim (sil-no-ev refl stp)

  RCB-bwd-τ : ∀ {p q q′} → RCB p q → q ─[ τ ]─► q′
            → Σ[ p′ ∈ CProc ] ((p ═[ τ ]═► p′) × RCB p′ q′)
  RCB-bwd-τ k₀ stp = ⊥-elim (loop-pfx-no-τ left (λ x → Ret (x ∷ [])) (bnK 1) stp)
  RCB-bwd-τ (k₁ x) stp with sil-τ-uniq refl stp
  ... | refl = C₁ x , wτ τ*-refl , k₂ x
  RCB-bwd-τ (k₂ x) stp = ⊥-elim (loop-out-no-τ right x (Ret []) (bnK 1) stp)
  RCB-bwd-τ k₃ stp with sil-τ-uniq refl stp
  ... | refl = COPY , wτ (τ*-step C₂-τ τ*-refl) , k₀

  RCB-¬divL : ∀ {p q} → RCB p q → Diverges p → ⊥
  RCB-¬divL k₀     = ¬div-COPY
  RCB-¬divL (k₁ x) = ¬div-C₁ x
  RCB-¬divL (k₂ x) = ¬div-C₁ x
  RCB-¬divL k₃     = ¬div-C₂

  RCB-¬divR : ∀ {p q} → RCB p q → Diverges q → ⊥
  RCB-¬divR k₀     = ¬div-BN[]
  RCB-¬divR (k₁ x) = ¬div-BNre1 x
  RCB-¬divR (k₂ x) = ¬div-BN1 x
  RCB-¬divR k₃     = ¬div-BNre[]

  module MCB = DRFromRel RCB RCB-fwd-ev RCB-fwd-τ RCB-bwd-ev RCB-bwd-τ RCB-¬divL RCB-¬divR

  COPY≈DRBN1 = MCB.rel→dr k₀
```

### §2.8 `Binf s ⊑T BN N s`

`Binf s₀ ⊑T BN N s₀` unfolds to `∀ t → traces (BN N s₀) t → traces
(Binf s₀) t`, so `BN` is the *simulated* side: we exhibit a weak
simulation of `BN N s₀` inside `Binf s₀` and conclude with `wsim→⊑T`.
The simulation is cyclic over the whole (infinite) state space, so it is
corecursive; the corecursion is factored out once in the shared
`WSimFromRel` principle (the one-directional half of `DRFromRel`),
imported from `Semantics.BisimFromRel` in the §2.4 block above.

The relation is state-indexed: `(BN N s , Binf s)` for *every* buffer
state `s`, plus the matching pair of re-entry states. No reachability
invariant is needed — every offer of `BN N s` (`left` when not full,
`right` when non-empty) is also an offer of `Binf s` from the same `s`,
and the fullness guard `suc (length s) ≡ᵇ N` is dispatched by a `with`
that re-abstracts the step (`| stp`) so the `BN` node reduces to the
output-only or `□` shape.

```agda
  data RBB (N : ℕ) : CProc → CProc → Set₁ where
    rB : ∀ s → RBB N (BN N s) (Binf s)
    rM : ∀ s → RBB N (BNre N s) (Binfre s)

  RBB-fwd-ev : ∀ N {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RBB N p q → p ─[ ev l ]─► p′
             → Σ[ q′ ∈ CProc ] ((q ═[ ev l ]═► q′) × RBB N p′ q′)
  RBB-fwd-ev N (rB []) stp with loop-pfx-ev-inv left (λ x → Ret (x ∷ [])) (bnK N) stp
  ... | x , refl , refl = Binfre (x ∷ []) , wev τ*-refl (Binf[]-left x) τ*-refl , rM (x ∷ [])
  RBB-fwd-ev N (rB (y ∷ s)) stp with suc (length s) ≡ᵇ N | stp
  ... | true  | stp′ with loop-out-ev-inv right y (Ret s) (bnK N) stp′
  ...   | refl , refl = Binfre s , wev τ*-refl (Binf∷-right y s) τ*-refl , rM s
  RBB-fwd-ev N (rB (y ∷ s)) stp | false | stp′
    with loop-□-ev-inv (λ x → Ret ((y ∷ s) ∷ʳ x)) y (Ret s) (bnK N) stp′
  ...   | inj₁ (x , refl , refl) =
          Binfre ((y ∷ s) ∷ʳ x) , wev τ*-refl (Binf∷-left y s x) τ*-refl , rM ((y ∷ s) ∷ʳ x)
  ...   | inj₂ (refl , refl) = Binfre s , wev τ*-refl (Binf∷-right y s) τ*-refl , rM s
  RBB-fwd-ev N (rM s) stp = ⊥-elim (sil-no-ev refl stp)

  RBB-fwd-τ : ∀ N {p q p′} → RBB N p q → p ─[ τ ]─► p′
            → Σ[ q′ ∈ CProc ] ((q ═[ τ ]═► q′) × RBB N p′ q′)
  RBB-fwd-τ N (rB []) stp = ⊥-elim (loop-pfx-no-τ left (λ x → Ret (x ∷ [])) (bnK N) stp)
  RBB-fwd-τ N (rB (y ∷ s)) stp with suc (length s) ≡ᵇ N | stp
  ... | true  | stp′ = ⊥-elim (loop-out-no-τ right y (Ret s) (bnK N) stp′)
  ... | false | stp′ = ⊥-elim (loop-□-no-τ (λ x → Ret ((y ∷ s) ∷ʳ x)) y (Ret s) (bnK N) stp′)
  RBB-fwd-τ N (rM s) stp with sil-τ-uniq refl stp
  ... | refl = Binf s , wτ (τ*-step (Binfre-τ s) τ*-refl) , rB s

  module MBB (N : ℕ) = WSimFromRel (RBB N) (RBB-fwd-ev N) (RBB-fwd-τ N)

  Binf⊑TBN N s₀ = wsim→⊑T (MBB.rel→wsim N (rB s₀))
```

## §3. The `Abs` half: `Abs1`, `Abs2`

`aleft`/`aright` carry a `ℤ` payload. The standard library's `Data.Integer`
has no Boolean-valued `_<ᵇ_` (only `_≤ᵇ_`); we derive one locally as
`x <ᵇ y = not (y ≤ᵇ x)` (`ℤ` is totally ordered, so `x < y` iff `¬ (y ≤
x)`) rather than importing a name that does not exist.

```agda
module Abs where

  open import Data.Integer using (ℤ; -_; _≤ᵇ_) renaming (0ℤ to 0ᶻ)

  _<ᵇ_ : ℤ → ℤ → Bool
  x <ᵇ y = not (y ≤ᵇ x)

  data ACh : Set → Set where
    aleft aright : ACh ℤ

  ACh-≟ : (x y : AnyTypes ACh) → Dec (x ≡ y)
  ACh-≟ (_ , aleft)  (_ , aleft)  = yes refl
  ACh-≟ (_ , aright) (_ , aright) = yes refl
  ACh-≟ (_ , aleft)  (_ , aright) = no λ ()
  ACh-≟ (_ , aright) (_ , aleft)  = no λ ()

  open import CSP.Operators ACh-≟

  AProc : Set₁
  AProc = PTree ACh (ExtI ACh) (Poly.⊤ {lzero})
```

### §3.1 `Abs1` — absolute value, computed inline

`Abs1 = aleft?x -> aright!(if x<0 then -x else x) -> Abs1`: read `x`, write
`|x|`, loop.

```agda
  abs1-body : AProc
  abs1-body = aleft ⟶ λ x → (aright ! (if x <ᵇ 0ᶻ then - x else x) ⟶ Skip)

  Abs1 : AProc
  Abs1 = loop0 abs1-body
```

### §3.2 `Abs2` — absolute value, computed via a guarded choice on the output side

`Abs2` is the same specification with the `if` moved after the read, so
the branching happens on the *output* prefix rather than inside the value
expression: `aleft?x -> (if x<0 then aright!(-x) -> Abs2 else aright!x ->
Abs2)`.

```agda
  abs2-body : AProc
  abs2-body = aleft ⟶ λ x →
                ((aright ! (- x) ⟶ Skip) ◁ (x <ᵇ 0ᶻ) ▷ (aright ! x ⟶ Skip))

  Abs2 : AProc
  Abs2 = loop0 abs2-body
```

### §3.3 Verification: `Abs1 ≈DR Abs2` and both trace refinements

Chapter 1's asserts about this pair are

```csp
assert Abs1 [T= Abs2
assert Abs2 [T= Abs1
```

In fact `Abs1` and `Abs2` are the same process up to where the `if` sits
around the output prefix, so we prove the stronger `Abs1 ≈DR Abs2`
(divergence-respecting weak bisimilarity) and extract both trace
refinements from it. The machinery is the `Ch`-side §§2.5–2.7 re-ported
at the `ACh` alphabet, with one new wrinkle: the payload is `ℤ`, so the
`Bool`-payload trick of §2.6 (case-split the payload until the output
guard's `u ≟ u` reduces definitionally) is unavailable — `out-fire` below
discharges the stuck decision *propositionally* instead, with a single
`with u ≟ u` over the whole `bindV`/`iterV`-composed offer pipeline
(matched as `yes _`, not `yes refl`, so the stuck `Output-cont` branch
reduces). The *other* scrutinee, `Abs2`'s guard `x <ᵇ 0ᶻ`, is dispatched
by a `with (x <ᵇ 0ᶻ) | stp` re-abstraction exactly like `BN`'s fullness
guard in §2.8: in each branch both bodies output the *same* integer
(`- x` when negative, `x` otherwise), which is what makes the two loops
lockstep-bisimilar.

```agda
  open import Semantics.LTS       {E = ACh} {I = ExtI ACh} hiding (Diverges)
  open import Semantics.WeakBisim {E = ACh} {I = ExtI ACh}
    using (WSimF; _═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
  open import Semantics.Failures  {E = ACh} {I = ExtI ACh} using (_⊑T_; traces-respects-≈)
  open import Semantics.DRBisim   {E = ACh} {I = ExtI ACh}
  open import CSP.Laws.Traces.PrefixInversion ACh-≟
    using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ; out-fire;
           sil-no-ev; sil-τ-uniq; divergesSil)
  open import Semantics.BisimFromRel {E = ACh} {I = ExtI ACh}
  open WSimF

  alblL alblR : ℤ → Event√ (Poly.⊤ {lzero})
  alblL x = evl (evLabel ℤ aleft x)
  alblR u = evl (evLabel ℤ aright u)
```

The three headline statements:

```agda
  Abs1≈DRAbs2 : Abs1 ≈DR Abs2

  Abs1⊑TAbs2 : Abs1 ⊑T Abs2
  Abs2⊑TAbs1 : Abs2 ⊑T Abs1
```

The reachable states. Both processes are `loop0`s, so both re-enter their
loop only through the single post-`aright` `sil` state; the post-`aleft`
states carry the read value `x`. Naming the two post-read continuations
(`abs1-cont`/`abs2-cont`, definitionally the bodies' lambdas) lets the
inversion lemmas below be stated compactly.

```agda
  abs1-cont abs2-cont : ℤ → AProc
  abs1-cont x = aright ! (if x <ᵇ 0ᶻ then - x else x) ⟶ Skip
  abs2-cont x = (aright ! (- x) ⟶ Skip) ◁ (x <ᵇ 0ᶻ) ▷ (aright ! x ⟶ Skip)

  aK₁ aK₂ : Poly.⊤ {lzero} → PTree ACh (ExtI ACh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
  aK₁ _ = abs1-body >>= (λ a′ → Ret (inj₁ a′))
  aK₂ _ = abs2-body >>= (λ a′ → Ret (inj₁ a′))

  A1₁ A2₁ : ℤ → AProc
  A1₁ x = iter-bind (abs1-cont x >>= (λ a′ → Ret (inj₁ a′))) aK₁
  A2₁ x = iter-bind (abs2-cont x >>= (λ a′ → Ret (inj₁ a′))) aK₂

  A1₂ A2₂ : AProc
  A1₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) aK₁
  A2₂ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) aK₂
```

The propositional output-firing lemma: the offer map of a loop state
sitting on `aright ! u ⟶ P` is the `Output-cont` guard threaded through
`bindV` and `iterV`, all stuck on the one decision `u ≟ u`; the
channel-generic `out-fire` imported from
`CSP.Laws.Traces.PrefixInversion` in the §3.3 block above discharges it
and the whole pipeline computes.

Step inversions for the two stable loop-node shapes (reader prefix and
output) are the channel-generic `loop-pfx-*`/`loop-out-*` lemmas imported
from `CSP.Laws.Traces.PrefixInversion` in the §3.3 block above; `Abs` has
no `□` state, so no `□` inversion is needed.

The `sil` helpers are imported from `CSP.Laws.Traces.PrefixInversion` in
the §3.3 block above.

The named strong steps: the reads (definitional, the `Prefix-cont` guard
is a channel decision only), and the two re-entry τs.

```agda
  Abs1-left : ∀ x → Abs1 ─[ ev (alblL x) ]─► A1₁ x
  Abs1-left x = sVis {at = ℤ , aleft} {a = x} refl refl

  Abs2-left : ∀ x → Abs2 ─[ ev (alblL x) ]─► A2₁ x
  Abs2-left x = sVis {at = ℤ , aleft} {a = x} refl refl

  A1₂-τ : A1₂ ─[ τ ]─► Abs1
  A1₂-τ = sSil refl

  A2₂-τ : A2₂ ─[ τ ]─► Abs2
  A2₂-τ = sSil refl
```

No reachable state diverges. `A2₁ x` is stuck on the `x <ᵇ 0ᶻ` guard, so
its refutation case-splits the guard first (re-abstracting the τ step);
`A1₁ x`'s output *payload* may be stuck but its node shape is not, so
`loop-out-no-τ` applies directly with the open `if`-payload.

```agda
  ¬div-Abs1 : Diverges Abs1 → ⊥
  ¬div-Abs1 d = loop-pfx-no-τ aleft abs1-cont aK₁ (Diverges.step d)

  ¬div-Abs2 : Diverges Abs2 → ⊥
  ¬div-Abs2 d = loop-pfx-no-τ aleft abs2-cont aK₂ (Diverges.step d)

  ¬div-A1₁ : ∀ x → Diverges (A1₁ x) → ⊥
  ¬div-A1₁ x d = loop-out-no-τ aright (if x <ᵇ 0ᶻ then - x else x) Skip aK₁ (Diverges.step d)

  ¬div-A2₁ : ∀ x → Diverges (A2₁ x) → ⊥
  ¬div-A2₁ x d with x <ᵇ 0ᶻ | Diverges.step d
  ... | true  | stp = loop-out-no-τ aright (- x) Skip aK₂ stp
  ... | false | stp = loop-out-no-τ aright x Skip aK₂ stp

  ¬div-A1₂ : Diverges A1₂ → ⊥
  ¬div-A1₂ d = ¬div-Abs1 (divergesSil refl d)

  ¬div-A2₂ : Diverges A2₂ → ⊥
  ¬div-A2₂ d = ¬div-Abs2 (divergesSil refl d)
```

The coinductive machinery is the shared `DRFromRel` principle imported
from `Semantics.BisimFromRel` in the §3.3 block above.

The relation is lockstep — both sides are `loop0`s that re-enter only
after the write — so three constructors suffice: the roots, the
post-read pair at each `x`, and the shared pre-re-entry pair.

```agda
  data RA : AProc → AProc → Set₁ where
    a₀ : RA Abs1 Abs2
    a₁ : ∀ x → RA (A1₁ x) (A2₁ x)
    a₂ : RA A1₂ A2₂

  RA-fwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {p′} → RA p q → p ─[ ev l ]─► p′
            → Σ[ q′ ∈ AProc ] ((q ═[ ev l ]═► q′) × RA p′ q′)
  RA-fwd-ev a₀ stp with loop-pfx-ev-inv aleft abs1-cont aK₁ stp
  ... | x , refl , refl = A2₁ x , wev τ*-refl (Abs2-left x) τ*-refl , a₁ x
  RA-fwd-ev (a₁ x) stp with x <ᵇ 0ᶻ | stp
  ... | true  | stp′ with loop-out-ev-inv aright (- x) Skip aK₁ stp′
  ...   | refl , refl =
          A2₂ , wev τ*-refl (sVis {at = ℤ , aright} {a = - x} refl
                              (out-fire aright (- x) Skip aK₂)) τ*-refl , a₂
  RA-fwd-ev (a₁ x) stp | false | stp′
    with loop-out-ev-inv aright x Skip aK₁ stp′
  ...   | refl , refl =
          A2₂ , wev τ*-refl (sVis {at = ℤ , aright} {a = x} refl
                              (out-fire aright x Skip aK₂)) τ*-refl , a₂
  RA-fwd-ev a₂ stp = ⊥-elim (sil-no-ev refl stp)

  RA-fwd-τ : ∀ {p q p′} → RA p q → p ─[ τ ]─► p′
           → Σ[ q′ ∈ AProc ] ((q ═[ τ ]═► q′) × RA p′ q′)
  RA-fwd-τ a₀ stp = ⊥-elim (loop-pfx-no-τ aleft abs1-cont aK₁ stp)
  RA-fwd-τ (a₁ x) stp = ⊥-elim (loop-out-no-τ aright (if x <ᵇ 0ᶻ then - x else x) Skip aK₁ stp)
  RA-fwd-τ a₂ stp with sil-τ-uniq refl stp
  ... | refl = Abs2 , wτ (τ*-step A2₂-τ τ*-refl) , a₀

  RA-bwd-ev : ∀ {p q} {l : Event√ (Poly.⊤ {lzero})} {q′} → RA p q → q ─[ ev l ]─► q′
            → Σ[ p′ ∈ AProc ] ((p ═[ ev l ]═► p′) × RA p′ q′)
  RA-bwd-ev a₀ stp with loop-pfx-ev-inv aleft abs2-cont aK₂ stp
  ... | x , refl , refl = A1₁ x , wev τ*-refl (Abs1-left x) τ*-refl , a₁ x
  RA-bwd-ev (a₁ x) stp with x <ᵇ 0ᶻ | stp
  ... | true  | stp′ with loop-out-ev-inv aright (- x) Skip aK₂ stp′
  ...   | refl , refl =
          A1₂ , wev τ*-refl (sVis {at = ℤ , aright} {a = - x} refl
                              (out-fire aright (- x) Skip aK₁)) τ*-refl , a₂
  RA-bwd-ev (a₁ x) stp | false | stp′
    with loop-out-ev-inv aright x Skip aK₂ stp′
  ...   | refl , refl =
          A1₂ , wev τ*-refl (sVis {at = ℤ , aright} {a = x} refl
                              (out-fire aright x Skip aK₁)) τ*-refl , a₂
  RA-bwd-ev a₂ stp = ⊥-elim (sil-no-ev refl stp)

  RA-bwd-τ : ∀ {p q q′} → RA p q → q ─[ τ ]─► q′
           → Σ[ p′ ∈ AProc ] ((p ═[ τ ]═► p′) × RA p′ q′)
  RA-bwd-τ a₀ stp = ⊥-elim (loop-pfx-no-τ aleft abs2-cont aK₂ stp)
  RA-bwd-τ (a₁ x) stp with x <ᵇ 0ᶻ | stp
  ... | true  | stp′ = ⊥-elim (loop-out-no-τ aright (- x) Skip aK₂ stp′)
  ... | false | stp′ = ⊥-elim (loop-out-no-τ aright x Skip aK₂ stp′)
  RA-bwd-τ a₂ stp with sil-τ-uniq refl stp
  ... | refl = Abs1 , wτ (τ*-step A1₂-τ τ*-refl) , a₀

  RA-¬divL : ∀ {p q} → RA p q → Diverges p → ⊥
  RA-¬divL a₀     = ¬div-Abs1
  RA-¬divL (a₁ x) = ¬div-A1₁ x
  RA-¬divL a₂     = ¬div-A1₂

  RA-¬divR : ∀ {p q} → RA p q → Diverges q → ⊥
  RA-¬divR a₀     = ¬div-Abs2
  RA-¬divR (a₁ x) = ¬div-A2₁ x
  RA-¬divR a₂     = ¬div-A2₂

  module MA = DRFromRel RA RA-fwd-ev RA-fwd-τ RA-bwd-ev RA-bwd-τ RA-¬divL RA-¬divR

  Abs1≈DRAbs2 = MA.rel→dr a₀
```

Both FDR asserts follow by weakening `≈DR` to plain weak bisimilarity and
projecting the two trace inclusions (`traces-respects-≈`), exactly as in
`UpDown` §7.

```agda
  Abs1⊑TAbs2 s = proj₂ (traces-respects-≈ (drbisim→wbisim Abs1≈DRAbs2))
  Abs2⊑TAbs1 s = proj₁ (traces-respects-≈ (drbisim→wbisim Abs1≈DRAbs2))
```
