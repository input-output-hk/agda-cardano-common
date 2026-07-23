# TPC chapter 2: two chained one-place buffers = one two-place buffer

Fourth chapter-2 example (parallel operators), porting the chained-buffer
alphabetised parallel of A.W. Roscoe's *The Theory and Practice of
Concurrency* (TPC §2.2). Source:

- `fdr-examples/tpc/chapter02/section2-2.csp` (buffer block)

```csp
T = {0,1}
channel aa, bb, cc : T

COPY'(a,b) = a?x -> b!x -> COPY'(a,b)

CC0 = COPY'(aa,bb) [{|aa,bb|}||{|bb,cc|}] COPY'(bb,cc)

CC0'      = aa?x -> CC1'(x)
CC1'(x)   = bb!x -> CC2'(x)
CC2'(x)   = cc!x -> CC0' [] aa?y -> CC3'(x,y)
CC3'(x,y) = cc!x -> CC1'(y)

assert CC0 [T= CC0'
assert CC0' [T= CC0
```

Two one-place `COPY'` buffers are chained on the middle channel `bb`: the
first reads on `aa` and writes on `bb`, the second reads on `bb` and writes
on `cc`. Their alphabetised parallel behaves as a **two**-place buffer, and
`CC0'`–`CC3'` is exactly that buffer written out sequentially by hand: the
four control states track the buffer contents *empty* (`CC0'`), *one value
in the first cell, not yet transferred* (`CC1'(x)`), *one value transferred
to the second cell* (`CC2'(x)`), and *full* (`CC3'(x,y)`). This module
proves both TPC asserts as trace refinements.

**Modelling reductions:**

- **Payload.** `T = {0,1}` becomes `Bool`.
- **Alphabetised parallel as interface parallel.** `COPY'(aa,bb)` only ever
  communicates in `{|aa,bb|}` and `COPY'(bb,cc)` only in `{|bb,cc|}` — each
  component respects its alphabet — so the alphabetised parallel
  `[{|aa,bb|}‖{|bb,cc|}]` denotes the same process as the interface parallel
  on the *intersection*, `[| {|bb|} |]` (i.e. `{bb.0, bb.1}`). We model the
  composition with `_∥⇘_⇙_` at that shared synchronisation set: `bb`
  synchronises (its value agreed by both buffers), `aa` is a left-solo
  event, `cc` a right-solo one.
- **`CC0'` as a stateful loop.** The four mutually recursive equations
  become one `loop` over a four-constructor state type `BSt` carrying the
  buffered value(s).

This module proves both asserts, for every trace:

```text
cc0⊑cc0'  : CC0  ⊑T CC0'    -- every CC0' trace is realised by the chain
cc0'⊑cc0  : CC0' ⊑T CC0     -- every chain trace is a CC0' trace
```

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch2.ChainedBuffers where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; _≟_)
open import Class.DecEq.Instances using (DecEq-Bool)

open import Process_Trees
```

## §2. The event type and its decidable equality

Three channels, all carrying a `Bool` (`channel aa, bb, cc : T`). Three
constructors give `3 × 3 = 9` clauses on `AnyTypes BCh`: three diagonal
`yes refl` and six off-diagonal `no λ ()`, the hand-rolled idiom of the
chapter-1 `Copy.Buffers.Ch-≟`.

```agda
data BCh : Set → Set where
  aa bb cc : BCh Bool

BCh-≟ : (x y : AnyTypes BCh) → Dec (x ≡ y)
BCh-≟ (_ , aa) (_ , aa) = yes refl
BCh-≟ (_ , bb) (_ , bb) = yes refl
BCh-≟ (_ , cc) (_ , cc) = yes refl
BCh-≟ (_ , aa) (_ , bb) = no λ ()
BCh-≟ (_ , aa) (_ , cc) = no λ ()
BCh-≟ (_ , bb) (_ , aa) = no λ ()
BCh-≟ (_ , bb) (_ , cc) = no λ ()
BCh-≟ (_ , cc) (_ , aa) = no λ ()
BCh-≟ (_ , cc) (_ , bb) = no λ ()

open import CSP.Operators BCh-≟
```

## §3. Process definitions

```agda
BProc : Set₁
BProc = PTree BCh (ExtI BCh) (Poly.⊤ {lzero})
```

### §3.1 The two `COPY'` instances

`COPY'(a,b) = a?x → b!x → COPY'(a,b)`, specialised to the two used channel
pairs (exactly chapter 1's `COPY`, at the new alphabet).

```agda
abbody bcbody : BProc
abbody = aa ⟶ λ x → (bb ! x ⟶ Skip)
bcbody = bb ⟶ λ x → (cc ! x ⟶ Skip)

COPYab : BProc          -- COPY'(aa,bb)
COPYab = loop0 abbody

COPYbc : BProc          -- COPY'(bb,cc)
COPYbc = loop0 bcbody
```

### §3.2 The chain `CC0`

The shared alphabet `{|aa,bb|} ∩ {|bb,cc|} = {|bb|}` as a channel-level
`EventSet`, and the chained composition (see the header for why the
alphabetised parallel collapses to this interface parallel).

```agda
sharedbb : AnyTypes BCh → Set        -- {|bb|}
sharedbb (_ , aa) = ⊥
sharedbb (_ , bb) = ⊤
sharedbb (_ , cc) = ⊥

sharedbb-dec : (at : AnyTypes BCh) → Dec (sharedbb at)
sharedbb-dec (_ , aa) = no (λ z → z)
sharedbb-dec (_ , bb) = yes tt
sharedbb-dec (_ , cc) = no (λ z → z)

Shared : EventSet
Shared = chanSet sharedbb sharedbb-dec

-- CC0 = COPY'(aa,bb) [{|aa,bb|}||{|bb,cc|}] COPY'(bb,cc)  =  COPYab [|{|bb|}|] COPYbc
CC0 : BProc
CC0 = COPYab ∥⇘ Shared ⇙ COPYbc
```

### §3.3 The hand-unfolded two-place buffer `CC0'`

The four control points `CC0'`/`CC1'(x)`/`CC2'(x)`/`CC3'(x,y)` become the
state type `BSt`; `cc0'-step` transcribes the four `.csp` clauses, and
`CC0'` is the stateful loop started at the empty buffer. The `□` in the
`s2` clause chooses at return type `BSt`, so `BSt` gets a hand-written
`DecEq` instance (payload comparisons via `DecEq-Bool`).

```agda
data BSt : Set where
  s0 : BSt
  s1 s2 : Bool → BSt
  s3 : Bool → Bool → BSt

BSt-≟ : (x y : BSt) → Dec (x ≡ y)
BSt-≟ s0 s0 = yes refl
BSt-≟ (s1 x) (s1 y) with x ≟ y
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
BSt-≟ (s2 x) (s2 y) with x ≟ y
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
BSt-≟ (s3 x y) (s3 x′ y′) with x ≟ x′ | y ≟ y′
... | yes refl | yes refl = yes refl
... | yes _    | no ¬p    = no λ { refl → ¬p refl }
... | no ¬p    | _        = no λ { refl → ¬p refl }
BSt-≟ s0       (s1 _)   = no λ ()
BSt-≟ s0       (s2 _)   = no λ ()
BSt-≟ s0       (s3 _ _) = no λ ()
BSt-≟ (s1 _)   s0       = no λ ()
BSt-≟ (s1 _)   (s2 _)   = no λ ()
BSt-≟ (s1 _)   (s3 _ _) = no λ ()
BSt-≟ (s2 _)   s0       = no λ ()
BSt-≟ (s2 _)   (s1 _)   = no λ ()
BSt-≟ (s2 _)   (s3 _ _) = no λ ()
BSt-≟ (s3 _ _) s0       = no λ ()
BSt-≟ (s3 _ _) (s1 _)   = no λ ()
BSt-≟ (s3 _ _) (s2 _)   = no λ ()

instance
  DecEq-BSt : DecEq BSt
  DecEq-BSt = record { _≟_ = BSt-≟ }

cc0'-step : BSt → PTree BCh (ExtI BCh) BSt
cc0'-step s0       = aa ⟶ λ x → Ret (s1 x)                    -- CC0'      = aa?x -> CC1'(x)
cc0'-step (s1 x)   = bb ! x ⟶ Ret (s2 x)                      -- CC1'(x)   = bb!x -> CC2'(x)
cc0'-step (s2 x)   = (cc ! x ⟶ Ret s0)                        -- CC2'(x)   = cc!x -> CC0'
                   □ (aa ⟶ λ y → Ret (s3 x y))                --          [] aa?y -> CC3'(x,y)
cc0'-step (s3 x y) = cc ! x ⟶ Ret (s1 y)                      -- CC3'(x,y) = cc!x -> CC1'(y)

CC0' : BProc
CC0' = loop cc0'-step s0
```

## §4. Verification

The two TPC asserts, as trace refinements. The proof follows the
`ATMParallel` grammar-characterisation recipe, but where that example's
total synchronisation collapsed the interleaving witness to the diagonal,
here the witness is genuinely three-way: `aa` steps are left-solo
(`psoloL`), `cc` steps right-solo (`psoloR`), and `bb` steps synchronised
with the value agreed (`psync`). The crux (§4.8) is that shuffling a
`COPYab` trace against a `COPYbc` trace under exactly that discipline
*is* the four-state grammar of `CC0'`: the pair of per-side phases
(first buffer ready/pending, second buffer ready/pending) is in bijection
with `BSt`.

```agda
open import Semantics.LTS       {E = BCh} {I = ExtI BCh}
open import Semantics.Failures  {E = BCh} {I = ExtI BCh}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

open import CSP.Laws.Traces.PrefixInversion BCh-≟
  using (loop-pfx-ev-inv; loop-pfx-no-τ; loop-out-ev-inv; loop-out-no-τ;
         out-fire; sil-no-ev; sil-τ-uniq)
open import CSP.Laws.Traces.TraceLawsParallel BCh-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace BCh-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono BCh-≟
  using (Par-trace-intro)
```

### §4.1 The FDR asserts

```agda
-- assert CC0 [T= CC0'   (holds)
cc0⊑cc0' : CC0 ⊑T CC0'

-- assert CC0' [T= CC0   (holds)
cc0'⊑cc0 : CC0' ⊑T CC0
```

### §4.2 Event labels and the merge function

```agda
Ev : Set₁
Ev = Event√ (Poly.⊤ {lzero})

lblAA lblBB lblCC : Bool → Ev
lblAA x = evl (evLabel Bool aa x)
lblBB x = evl (evLabel Bool bb x)
lblCC x = evl (evLabel Bool cc x)

-- the merge function of the CSP parallel (η-equal to the one baked into _∥⇘_⇙_)
mg⊤ : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})
mg⊤ _ _ = Poly.tt
```

### §4.3 The three trace grammars

Each `COPY'` alternates strictly between its *ready* phase (about to read)
and its *pending* phase (holding a value about to be written), so its
trace language is the phase-indexed grammar of the two-letter cycle.
`CTr` is the four-state trace language of `CC0'`, one production per
prefix of the `.csp` clauses. No grammar produces `√` (the loops never
terminate).

```agda
data APh : Set where          -- COPYab: ready / holding x (pending bb!x)
  aR : APh
  aP : Bool → APh

data BPh : Set where          -- COPYbc: ready / holding x (pending cc!x)
  bR : BPh
  bP : Bool → BPh

data ATr : APh → List Ev → Set₁ where
  anil : ∀ {α} → ATr α []
  aIn  : ∀ {x tr} → ATr (aP x) tr → ATr aR     (lblAA x ∷ tr)
  aOut : ∀ {x tr} → ATr aR tr     → ATr (aP x) (lblBB x ∷ tr)

data BTr : BPh → List Ev → Set₁ where
  bnil : ∀ {β} → BTr β []
  bIn  : ∀ {x tr} → BTr (bP x) tr → BTr bR     (lblBB x ∷ tr)
  bOut : ∀ {x tr} → BTr bR tr     → BTr (bP x) (lblCC x ∷ tr)

data CTr : BSt → List Ev → Set₁ where
  cnil : ∀ {σ} → CTr σ []
  cIn0 : ∀ {x tr}   → CTr (s1 x) tr   → CTr s0       (lblAA x ∷ tr)
  cBB  : ∀ {x tr}   → CTr (s2 x) tr   → CTr (s1 x)   (lblBB x ∷ tr)
  cCC2 : ∀ {x tr}   → CTr s0 tr       → CTr (s2 x)   (lblCC x ∷ tr)
  cIn2 : ∀ {x y tr} → CTr (s3 x y) tr → CTr (s2 x)   (lblAA y ∷ tr)
  cCC3 : ∀ {x y tr} → CTr (s1 y) tr   → CTr (s3 x y) (lblCC x ∷ tr)
```

The phase bijection: a `BSt` control state *is* a pair of per-side phases.

```agda
comb : APh → BPh → BSt
comb aR     bR     = s0
comb (aP x) bR     = s1 x
comb aR     (bP x) = s2 x
comb (aP y) (bP x) = s3 x y

aph : BSt → APh
aph s0       = aR
aph (s1 x)   = aP x
aph (s2 _)   = aR
aph (s3 _ y) = aP y

bph : BSt → BPh
bph s0       = bR
bph (s1 _)   = bR
bph (s2 x)   = bP x
bph (s3 x _) = bP x
```

### §4.4 Reachable states and strong steps of the two `COPY'`s

Both are `loop0`s, so their states are `iter-bind` terms — definitional
unfoldings of the loops' successors. Each has a post-read output state
(holding the read value) and a silent loop re-entry state. Reader
prefixes fire definitionally (`refl refl`); the payload outputs go
through the channel-generic `out-fire`.

```agda
abK bcK : Poly.⊤ {lzero} → PTree BCh (ExtI BCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
abK _ = abbody >>= (λ a′ → Ret (inj₁ a′))
bcK _ = bcbody >>= (λ a′ → Ret (inj₁ a′))

A⋆ : Bool → BProc               -- COPYab holding x: bb!x pending
A⋆ x = iter-bind ((bb ! x ⟶ Skip) >>= (λ a′ → Ret (inj₁ a′))) abK

A↝ : BProc                      -- COPYab silent re-entry
A↝ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) abK

B⋆ : Bool → BProc               -- COPYbc holding x: cc!x pending
B⋆ x = iter-bind ((cc ! x ⟶ Skip) >>= (λ a′ → Ret (inj₁ a′))) bcK

B↝ : BProc                      -- COPYbc silent re-entry
B↝ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) bcK

COPYab-aa : ∀ x → COPYab ─[ ev (lblAA x) ]─► A⋆ x
COPYab-aa x = sVis {at = Bool , aa} {a = x} refl refl

A⋆-bb : ∀ x → A⋆ x ─[ ev (lblBB x) ]─► A↝
A⋆-bb x = sVis {at = Bool , bb} {a = x} refl (out-fire bb x Skip abK)

A↝-τ : A↝ ─[ τ ]─► COPYab
A↝-τ = sSil refl

COPYbc-bb : ∀ x → COPYbc ─[ ev (lblBB x) ]─► B⋆ x
COPYbc-bb x = sVis {at = Bool , bb} {a = x} refl refl

B⋆-cc : ∀ x → B⋆ x ─[ ev (lblCC x) ]─► B↝
B⋆-cc x = sVis {at = Bool , cc} {a = x} refl (out-fire cc x Skip bcK)

B↝-τ : B↝ ─[ τ ]─► COPYbc
B↝-τ = sSil refl
```

### §4.5 Reachable states and strong steps of `CC0'`

`CC0'` is a *stateful* loop: after every event the body returns the next
control state `σ` and the loop silently re-enters at `σ` (exactly the
chapter-1 `BN` pattern). `CCat σ` is the loop head at `σ`, `CCre σ` the
pre-re-entry state one τ before it.

```agda
ccK : BSt → PTree BCh (ExtI BCh) (BSt ⊎ Poly.⊤ {lzero})
ccK σ = cc0'-step σ >>= (λ σ′ → Ret (inj₁ σ′))

CCat : BSt → BProc
CCat σ = loop cc0'-step σ

CCre : BSt → BProc
CCre σ = iter-bind (Ret σ >>= (λ σ′ → Ret (inj₁ σ′))) ccK

CCre-τ : ∀ σ → CCre σ ─[ τ ]─► CCat σ
CCre-τ σ = sSil refl
```

The five event steps of the four control states. The `s2` state is a `□`
of an output against a reader: the reader summand (`aa?y`) fires
definitionally even at an *open* held value `x` (the output summand's
channel decision `cc ≟ aa` reduces on constructors, so the merged offer
falls through to the reader), while the output summand (`cc!x`) is stuck
on the payload decision `x ≟ x` and fires after a `Bool` case-split (the
chapter-1 `C₁-right` idiom). The plain output states use `out-fire`.

```agda
CC-aa0 : ∀ x → CCat s0 ─[ ev (lblAA x) ]─► CCre (s1 x)
CC-aa0 x = sVis {at = Bool , aa} {a = x} refl refl

CC-bb1 : ∀ x → CCat (s1 x) ─[ ev (lblBB x) ]─► CCre (s2 x)
CC-bb1 x = sVis {at = Bool , bb} {a = x} refl (out-fire bb x (Ret (s2 x)) ccK)

CC-cc2 : ∀ x → CCat (s2 x) ─[ ev (lblCC x) ]─► CCre s0
CC-cc2 true  = sVis {at = Bool , cc} {a = true}  refl refl
CC-cc2 false = sVis {at = Bool , cc} {a = false} refl refl

CC-aa2 : ∀ x y → CCat (s2 x) ─[ ev (lblAA y) ]─► CCre (s3 x y)
CC-aa2 x y = sVis {at = Bool , aa} {a = y} refl refl

CC-cc3 : ∀ x y → CCat (s3 x y) ─[ ev (lblCC x) ]─► CCre (s1 y)
CC-cc3 x y = sVis {at = Bool , cc} {a = x} refl (out-fire cc x (Ret (s1 y)) ccK)
```

### §4.6 Step inversion for the `s2`-shaped `□` loop state

The reader-prefix and output loop states are inverted by the imported
channel-generic `loop-pfx-*`/`loop-out-*`; only the `s2` shape's `□`
(output `cc!u` against reader `aa?y`) needs a local inversion, ported
from the chapter-1 `Copy.Buffers.loop-□-*` (there: reader `□` output;
here the summands are swapped). A visible step fires exactly one summand
— the third channel `bb` finds both offers `nothing` — and the node is
τ-free (`□-mt` of two `∅t`-parted prefixes is pointwise `nothing`, the
seven `ExtI`-index clauses).

```agda
loop-□-ev-inv : ∀ {A : Set} ⦃ _ : DecEq A ⦄
                  (u : Bool) (P₁ : PTree BCh (ExtI BCh) A)
                  (P₂ : Bool → PTree BCh (ExtI BCh) A)
                  (K : A → PTree BCh (ExtI BCh) (A ⊎ Poly.⊤ {lzero}))
                  {l : Ev} {t′ : BProc}
              → iter-bind (((cc ! u ⟶ P₁) □ (aa ⟶ P₂)) >>= (λ a′ → Ret (inj₁ a′))) K
                  ─[ ev l ]─► t′
              → ((l ≡ lblCC u) × (t′ ≡ iter-bind (P₁ >>= (λ a′ → Ret (inj₁ a′))) K))
                ⊎ (Σ[ y ∈ Bool ] ((l ≡ lblAA y)
                     × (t′ ≡ iter-bind (P₂ y >>= (λ a′ → Ret (inj₁ a′))) K)))
loop-□-ev-inv u P₁ P₂ K (sRet eq) = case eq of λ ()
loop-□-ev-inv u P₁ P₂ K (sVis {at = _ , aa} {a = y} refl br) =
  inj₂ (y , refl , sym (just-injective br))
loop-□-ev-inv u P₁ P₂ K (sVis {at = _ , bb} {a = _} refl br) = ⊥-elim (case br of λ ())
loop-□-ev-inv u P₁ P₂ K (sVis {at = _ , cc} {a = a} refl br) with a ≟ u
... | yes refl = inj₁ (refl , sym (just-injective br))
... | no _     = ⊥-elim (case br of λ ())

loop-□-no-τ : ∀ {A : Set} ⦃ _ : DecEq A ⦄
                (u : Bool) (P₁ : PTree BCh (ExtI BCh) A)
                (P₂ : Bool → PTree BCh (ExtI BCh) A)
                (K : A → PTree BCh (ExtI BCh) (A ⊎ Poly.⊤ {lzero})) {t′ : BProc}
            → iter-bind (((cc ! u ⟶ P₁) □ (aa ⟶ P₂)) >>= (λ a′ → Ret (inj₁ a′))) K
                ─[ τ ]─► t′ → ⊥
loop-□-no-τ u P₁ P₂ K (sSil eq) = case eq of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , base _}            refl br) = case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , fin}               refl br) = case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , pair fin _} {a = lift fzero , _}           refl br) =
  case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , _}    refl br) =
  case br of λ ()
loop-□-no-τ u P₁ P₂ K (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl br) =
  case br of λ ()
```

### §4.7 Big-step characterisations (the elim halves)

`AState`/`BState`/`CState` index the reachable states by their grammar
phase; reading a big-step off as a grammar derivation is structural
induction with the loop step-inversions, chasing the silent re-entries
with `sil-τ-uniq`/`sil-no-ev`.

```agda
data AState : APh → BProc → Set₁ where
  aSt0 : AState aR COPYab
  aSt1 : ∀ x → AState (aP x) (A⋆ x)
  aSt↝ : AState aR A↝

COPYab-char : ∀ {α p tr} {p′ : BProc} → AState α p → p ⟹⟨ tr ⟩ p′ → ATr α tr
COPYab-char _ ⟹-refl = anil
COPYab-char aSt0 (⟹-τ st _)     = ⊥-elim (loop-pfx-no-τ aa (λ x → (bb ! x ⟶ Skip)) abK st)
COPYab-char aSt0 (⟹-ev st rest) with loop-pfx-ev-inv aa (λ x → (bb ! x ⟶ Skip)) abK st
... | x , refl , refl = aIn (COPYab-char (aSt1 x) rest)
COPYab-char (aSt1 x) (⟹-τ st _)     = ⊥-elim (loop-out-no-τ bb x Skip abK st)
COPYab-char (aSt1 x) (⟹-ev st rest) with loop-out-ev-inv bb x Skip abK st
... | refl , refl = aOut (COPYab-char aSt↝ rest)
COPYab-char aSt↝ (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = COPYab-char aSt0 rest
COPYab-char aSt↝ (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

data BState : BPh → BProc → Set₁ where
  bSt0 : BState bR COPYbc
  bSt1 : ∀ x → BState (bP x) (B⋆ x)
  bSt↝ : BState bR B↝

COPYbc-char : ∀ {β p tr} {p′ : BProc} → BState β p → p ⟹⟨ tr ⟩ p′ → BTr β tr
COPYbc-char _ ⟹-refl = bnil
COPYbc-char bSt0 (⟹-τ st _)     = ⊥-elim (loop-pfx-no-τ bb (λ x → (cc ! x ⟶ Skip)) bcK st)
COPYbc-char bSt0 (⟹-ev st rest) with loop-pfx-ev-inv bb (λ x → (cc ! x ⟶ Skip)) bcK st
... | x , refl , refl = bIn (COPYbc-char (bSt1 x) rest)
COPYbc-char (bSt1 x) (⟹-τ st _)     = ⊥-elim (loop-out-no-τ cc x Skip bcK st)
COPYbc-char (bSt1 x) (⟹-ev st rest) with loop-out-ev-inv cc x Skip bcK st
... | refl , refl = bOut (COPYbc-char bSt↝ rest)
COPYbc-char bSt↝ (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = COPYbc-char bSt0 rest
COPYbc-char bSt↝ (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

data CState : BSt → BProc → Set₁ where
  cAt : ∀ σ → CState σ (CCat σ)
  cRe : ∀ σ → CState σ (CCre σ)

CC0'-char : ∀ {σ p tr} {p′ : BProc} → CState σ p → p ⟹⟨ tr ⟩ p′ → CTr σ tr
CC0'-char _ ⟹-refl = cnil
CC0'-char (cAt s0) (⟹-τ st _)     = ⊥-elim (loop-pfx-no-τ aa (λ x → Ret (s1 x)) ccK st)
CC0'-char (cAt s0) (⟹-ev st rest) with loop-pfx-ev-inv aa (λ x → Ret (s1 x)) ccK st
... | x , refl , refl = cIn0 (CC0'-char (cRe (s1 x)) rest)
CC0'-char (cAt (s1 x)) (⟹-τ st _)     = ⊥-elim (loop-out-no-τ bb x (Ret (s2 x)) ccK st)
CC0'-char (cAt (s1 x)) (⟹-ev st rest) with loop-out-ev-inv bb x (Ret (s2 x)) ccK st
... | refl , refl = cBB (CC0'-char (cRe (s2 x)) rest)
CC0'-char (cAt (s2 x)) (⟹-τ st _) =
  ⊥-elim (loop-□-no-τ x (Ret s0) (λ y → Ret (s3 x y)) ccK st)
CC0'-char (cAt (s2 x)) (⟹-ev st rest)
  with loop-□-ev-inv x (Ret s0) (λ y → Ret (s3 x y)) ccK st
... | inj₁ (refl , refl)     = cCC2 (CC0'-char (cRe s0) rest)
... | inj₂ (y , refl , refl) = cIn2 (CC0'-char (cRe (s3 x y)) rest)
CC0'-char (cAt (s3 x y)) (⟹-τ st _)     = ⊥-elim (loop-out-no-τ cc x (Ret (s1 y)) ccK st)
CC0'-char (cAt (s3 x y)) (⟹-ev st rest) with loop-out-ev-inv cc x (Ret (s1 y)) ccK st
... | refl , refl = cCC3 (CC0'-char (cRe (s1 y)) rest)
CC0'-char (cRe σ) (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = CC0'-char (cAt σ) rest
CC0'-char (cRe σ) (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)
```

### §4.8 The chaining shuffle

The crux of `cc0'⊑cc0`: a `Shared`-disciplined interleaving of a `COPYab`
trace and a `COPYbc` trace, read from phases `α`/`β`, is a `CTr` trace
from the combined control state `comb α β`. `aa` at the head of the left
share is a solo step (`psync` on it is refuted by its `⊥` membership);
`bb` must be joint (`psoloL`/`psoloR` on it are refuted by `¬ ⊤`), and
`psync`'s single shared label forces the two sides to agree on the
carried value — the pattern match unifies the `x` of `aOut` with the `x`
of `bIn`, which is exactly the hand-off of the buffered value; `cc` at
the head of the right share is a solo step; and the joint `√` (`p√`)
would need `√` at the head of the left share, which no `ATr` trace
contains.

```agda
shuffle : ∀ α β {sP sQ tr}
        → ParInter Shared mg⊤ sP sQ tr → ATr α sP → BTr β sQ
        → CTr (comb α β) tr
shuffle α β pnil _ _ = cnil
shuffle _ _      (psync m∈ PI) (aIn _)          _         = ⊥-elim m∈
shuffle _ _      (psync _  PI) (aOut {x = x} tl) (bIn tl′) =
  cBB (shuffle aR (bP x) PI tl tl′)
shuffle _ bR     (psoloL _ PI) (aIn {x = x} tl) btr =
  cIn0 (shuffle (aP x) bR PI tl btr)
shuffle _ (bP z) (psoloL _ PI) (aIn {x = x} tl) btr =
  cIn2 (shuffle (aP x) (bP z) PI tl btr)
shuffle _ _      (psoloL ¬m PI) (aOut _)        _         = ⊥-elim (¬m tt)
shuffle aR _     (psoloR _ PI) atr (bOut {x = x} tl) =
  cCC2 (shuffle aR bR PI atr tl)
shuffle (aP y) _ (psoloR _ PI) atr (bOut {x = x} tl) =
  cCC3 (shuffle (aP y) bR PI atr tl)
shuffle _ _      (psoloR ¬m PI) _  (bIn _)                = ⊥-elim (¬m tt)
shuffle _ _      p√ () _
```

### §4.9 `assert CC0' [T= CC0`

The intro half for `CC0'` (each `CTr` production is the matching §4.5
step, crossing the silent re-entry), then the assembly: de-interleave the
chain's trace with `Par-trace-elim`, characterise both `COPY'` shares,
and push them through the chaining shuffle.

```agda
CC0'-intro : ∀ {σ tr} → CTr σ tr → traces (CCat σ) tr
CC0'-intro {σ} cnil = CCat σ , ⟹-refl
CC0'-intro (cIn0 {x = x} tl) with CC0'-intro tl
... | p′ , bs = p′ , ⟹-ev (CC-aa0 x) (⟹-τ (CCre-τ (s1 x)) bs)
CC0'-intro (cBB {x = x} tl) with CC0'-intro tl
... | p′ , bs = p′ , ⟹-ev (CC-bb1 x) (⟹-τ (CCre-τ (s2 x)) bs)
CC0'-intro (cCC2 {x = x} tl) with CC0'-intro tl
... | p′ , bs = p′ , ⟹-ev (CC-cc2 x) (⟹-τ (CCre-τ s0) bs)
CC0'-intro (cIn2 {x = x} {y = y} tl) with CC0'-intro tl
... | p′ , bs = p′ , ⟹-ev (CC-aa2 x y) (⟹-τ (CCre-τ (s3 x y)) bs)
CC0'-intro (cCC3 {x = x} {y = y} tl) with CC0'-intro tl
... | p′ , bs = p′ , ⟹-ev (CC-cc3 x y) (⟹-τ (CCre-τ (s1 y)) bs)

cc0'⊑cc0 s (Rt , bs) with Par-trace-elim Shared mg⊤ COPYab COPYbc bs
... | sP , sQ , P′ , Q′ , rP , rQ , inter =
      CC0'-intro (shuffle aR bR inter (COPYab-char aSt0 rP) (COPYbc-char bSt0 rQ))
```

### §4.10 `assert CC0 [T= CC0'`

The converse: split a `CC0'` trace back into its two per-side shares plus
the `ParInter` witness (each production becomes the corresponding
solo/sync step: `aa` productions are left-solo, `cc` productions
right-solo, and the `bb` production contributes the same labelled event
to *both* shares with `psync tt`), realise each share on its `COPY'`
(the intro halves), and re-interleave with `Par-trace-intro`.

```agda
CTr-split : ∀ {σ tr} → CTr σ tr
          → Σ[ sP ∈ List Ev ] Σ[ sQ ∈ List Ev ]
              (ATr (aph σ) sP × BTr (bph σ) sQ × ParInter Shared mg⊤ sP sQ tr)
CTr-split cnil = [] , [] , anil , bnil , pnil
CTr-split (cIn0 {x = x} tl) with CTr-split tl
... | sP , sQ , atr , btr , PI =
      lblAA x ∷ sP , sQ , aIn atr , btr , psoloL (λ z → z) PI
CTr-split (cBB {x = x} tl) with CTr-split tl
... | sP , sQ , atr , btr , PI =
      lblBB x ∷ sP , lblBB x ∷ sQ , aOut atr , bIn btr , psync tt PI
CTr-split (cCC2 {x = x} tl) with CTr-split tl
... | sP , sQ , atr , btr , PI =
      sP , lblCC x ∷ sQ , atr , bOut btr , psoloR (λ z → z) PI
CTr-split (cIn2 {x = x} {y = y} tl) with CTr-split tl
... | sP , sQ , atr , btr , PI =
      lblAA y ∷ sP , sQ , aIn atr , btr , psoloL (λ z → z) PI
CTr-split (cCC3 {x = x} {y = y} tl) with CTr-split tl
... | sP , sQ , atr , btr , PI =
      sP , lblCC x ∷ sQ , atr , bOut btr , psoloR (λ z → z) PI

aStOf : APh → BProc
aStOf aR     = COPYab
aStOf (aP x) = A⋆ x

bStOf : BPh → BProc
bStOf bR     = COPYbc
bStOf (bP x) = B⋆ x

COPYab-intro : ∀ {α tr} → ATr α tr → traces (aStOf α) tr
COPYab-intro {α} anil = aStOf α , ⟹-refl
COPYab-intro (aIn {x = x} tl) with COPYab-intro tl
... | p′ , bs = p′ , ⟹-ev (COPYab-aa x) bs
COPYab-intro (aOut {x = x} tl) with COPYab-intro tl
... | p′ , bs = p′ , ⟹-ev (A⋆-bb x) (⟹-τ A↝-τ bs)

COPYbc-intro : ∀ {β tr} → BTr β tr → traces (bStOf β) tr
COPYbc-intro {β} bnil = bStOf β , ⟹-refl
COPYbc-intro (bIn {x = x} tl) with COPYbc-intro tl
... | p′ , bs = p′ , ⟹-ev (COPYbc-bb x) bs
COPYbc-intro (bOut {x = x} tl) with COPYbc-intro tl
... | p′ , bs = p′ , ⟹-ev (B⋆-cc x) (⟹-τ B↝-τ bs)

cc0⊑cc0' s (Rt , bs) with CTr-split (CC0'-char (cAt s0) bs)
... | sP , sQ , atr , btr , PI with COPYab-intro atr | COPYbc-intro btr
...   | P′ , rP | Q′ , rQ = Par-trace-intro Shared mg⊤ COPYab COPYbc rP rQ PI
```

## §5. Status

Both TPC §2.2 asserts about the chained buffers are discharged:
`cc0⊑cc0'` (§4.10) and `cc0'⊑cc0` (§4.9) together give the trace
equivalence `traces CC0 = traces CC0'` — two chained one-place `COPY'`
buffers synchronised on the middle channel `bb` are exactly the
hand-unfolded two-place sequential buffer. The value hand-off is proved,
not assumed: the `psync` case of the §4.8 shuffle (and the `psync tt`
of §4.10's split) forces both sides to carry the *same* payload on the
shared `bb`. No postulates, no `NON_TERMINATING`, no `mutual` blocks.
