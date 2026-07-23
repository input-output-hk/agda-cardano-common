# TPC/UCS chapter 2: interleaved up/down loops vs the bounded counter

First chapter-2 example (parallel operators), porting the interleaving
example of A.W. Roscoe's *The Theory and Practice of Concurrency*:

- `fdr-examples/tpc/chapter02/section2-3.csp` (TPC §2.3)

```csp
channel up, down

L(0) = SKIP
L(N) = L1 ||| L(N-1)      -- N interleaved copies of  L1 = up -> down -> L1

LCOUNT(N,n) =  (n<N & up -> LCOUNT(N,n+1))
            [] (n>0 & down -> LCOUNT(N,n-1))
```

Each `L1` loop alternates `up`/`down`, so at any moment the number of
`up`s minus the number of `down`s across `N` interleaved copies lies in
`[0, N]` — i.e. the interleaving stays within the `N`-bounded counter.
Conversely, every `N`-bounded up/down run can be *scheduled* onto `N`
loops.  This module proves **both directions** as trace refinements:

```text
count⊑interleave-safe : ∀ n → LCOUNT (suc n) 0 ⊑T nCopies (suc n)   -- safety (§9)
interleave⊑count      : ∀ n → nCopies (suc n) ⊑T LCOUNT (suc n) 0   -- completeness (§10)
```

(every trace of `suc n` interleaved loops is a trace of the bounded
counter started at `0`, and vice versa — so the two processes are
trace-equivalent).  The chapter-1 module
`CSP.Examples.TPC.Ch1.UpDown` already defines the alphabet `UD`, the
loop `P1` (= `L1`) and `LCOUNT`; we reuse them here.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch2.Interleaving where

open import Level using () renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _≤_; z≤n; s≤s; _<ᵇ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq.Instances using (DecEq-ℕ)

open import Process_Trees
open import CSP.Examples.TPC.Ch1.UpDown
  using (UD; up; down; UD-≟; P1; LCOUNT; lcount-step;
         P1↑; P1↑↓; loopK; loop-ev-inv; loop-no-τ;
         P1-up; P1↑-down; P1↑↓-τ)
open import CSP.Operators UD-≟
open import Semantics.LTS       {E = UD} {I = ExtI UD}
open import Semantics.Failures  {E = UD} {I = ExtI UD}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsParallel UD-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace UD-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim;
         deadlock-no-τ; deadlock-no-ev)
open import CSP.Laws.Traces.TraceLawsParallelMono UD-≟
  using (Par-trace-intro)
open import CSP.Laws.Traces.PrefixInversion UD-≟
  using (sil-no-ev; sil-τ-uniq; TEmpty; ∅t-empty; □-mt-empty)
```

## §2. Definitions

`nCopies n` is `L(N)` above: `n` interleaved copies of `L1`, with `Skip`
as the 0-ary interleaving unit.  For `n ≥ 1` the leftmost `L1` never
terminates, so `nCopies (suc n)` never emits `√`.

```agda
Proc : Set₁
Proc = PTree UD (ExtI UD) (Poly.⊤ {lzero})

-- L1 = up → down → L1 (this is exactly UpDown.P1)
L1 : Proc
L1 = P1

-- n interleaved copies of L1 (Skip is the 0-ary interleaving unit; for n ≥ 1
-- the leftmost L1 never terminates, so nCopies (suc n) has no √).
nCopies : ℕ → Proc
nCopies zero    = Skip
nCopies (suc n) = L1 ⦀ nCopies n
```

The theorem, stated up front (FDR: every `L'(N)` trace is a
`LCOUNT(N,0)` trace — the interleaving stays in bounds):

```agda
count⊑interleave-safe : ∀ n → LCOUNT (suc n) 0 ⊑T nCopies (suc n)
```

## §3. Event and arithmetic scaffolding

```agda
Ev : Set₁
Ev = Event√ (Poly.⊤ {lzero})

upE downE : Ev
upE   = evl (evLabel ⊤ up tt)
downE = evl (evLabel ⊤ down tt)

-- the interleaving merge (η-equal to the one baked into _⦀_)
mgI : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})
mgI _ _ = Poly.tt
```

Tiny self-contained conversions between the boolean guard `_<ᵇ_` used by
`lcount-step` and the ordering `_≤_`, plus two weakening lemmas.

```agda
<ᵇ-sound : ∀ m n → (m <ᵇ n) ≡ true → suc m ≤ n
<ᵇ-sound zero    (suc n) _  = s≤s z≤n
<ᵇ-sound (suc m) (suc n) eq = s≤s (<ᵇ-sound m n eq)

<ᵇ-complete : ∀ {m n} → suc m ≤ n → (m <ᵇ n) ≡ true
<ᵇ-complete {zero}  (s≤s _) = refl
<ᵇ-complete {suc m} (s≤s h) = <ᵇ-complete h

≤-suc : ∀ {m n} → m ≤ n → m ≤ suc n
≤-suc z≤n     = z≤n
≤-suc (s≤s h) = s≤s (≤-suc h)

pred-≤ : ∀ {m n} → suc m ≤ n → m ≤ n
pred-≤ (s≤s h) = ≤-suc h
```

## §4. The two trace grammars

`L1Tr b s`: `s` is a (finite) trace of the `L1` loop starting from parity
`b` (`false` = next event is `up`, `true` = next is `down`); i.e. `s` is a
prefix of the alternating `up·down` stream.  `bv b` is the loop's current
contribution to the running count (`1` iff it is "up").

`CTr L m s`: `s` is a trace of the `L`-bounded counter started at `m`
(`up` allowed while `m < L`, `down` while `m > 0`).

```agda
data L1Tr : Bool → List Ev → Set₁ where
  lnil : ∀ {b} → L1Tr b []
  lup  : ∀ {s} → L1Tr true  s → L1Tr false (upE ∷ s)
  ldn  : ∀ {s} → L1Tr false s → L1Tr true  (downE ∷ s)

bv : Bool → ℕ
bv false = 0
bv true  = 1

data CTr (L : ℕ) : ℕ → List Ev → Set₁ where
  cnil : ∀ {m} → CTr L m []
  cup  : ∀ {m s} → suc m ≤ L → CTr L (suc m) s → CTr L m (upE ∷ s)
  cdn  : ∀ {m s} → CTr L m s → CTr L (suc m) (downE ∷ s)
```

## §5. `L1`'s big-steps are alternating traces

`L1 = P1` cycles through three states: `P1` (stable, offers `up`), `P1↑`
(stable, offers `down`), and the silent re-entry state `P1↑↓` (one τ back
to `P1`) — all named in `UpDown` §5.3.  We index them by their parity and
read a big-step off as an `L1Tr` by structural induction, using the
chapter-1 step inversions `loop-ev-inv` / `loop-no-τ` / `sil-τ-uniq`.

```agda
data L1St : Bool → Proc → Set₁ where
  at0 : L1St false P1
  at1 : L1St true  P1↑
  at2 : L1St false P1↑↓

L1-char : ∀ {b p s P′} → L1St b p → p ⟹⟨ s ⟩ P′ → L1Tr b s
L1-char _   ⟹-refl        = lnil
L1-char at0 (⟹-τ st _)    = ⊥-elim (loop-no-τ up (down ⟶₀ Skip) loopK st)
L1-char at1 (⟹-τ st _)    = ⊥-elim (loop-no-τ down Skip loopK st)
L1-char at2 (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = L1-char at0 rest
L1-char at0 (⟹-ev st rest) with loop-ev-inv up (down ⟶₀ Skip) loopK st
... | refl , refl = lup (L1-char at1 rest)
L1-char at1 (⟹-ev st rest) with loop-ev-inv down Skip loopK st
... | refl , refl = ldn (L1-char at2 rest)
L1-char at2 (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)
```

## §6. `LCOUNT`'s big-steps are bounded-counter traces

`LCOUNT L m = loop (lcount-step L) m` unfolds to an `iter-bind` over the
guarded external choice

```text
((up ⟶₀ Ret (suc m)) ◁ m <ᵇ L ▷ Stop) □ ((down ⟶₀ Ret (pred m)) ◁ 0 <ᵇ m ▷ Stop)
```

whose `force` is stuck on the two boolean guards when `m`, `L` are
variables.  We therefore generalise the guards to pattern-matchable
booleans: `LCst L b₁ b₂ m` is the same loop state with the guards
replaced by `b₁`, `b₂`, so that `LCOUNT L m` is **definitionally**
`LCst L (m <ᵇ L) (0 <ᵇ m) m`, and all step lemmas are proved by cases on
`b₁`, `b₂` (where everything reduces).  `LC↝ L m′` is the one-τ
re-entry state reached after an event (its single `sil` lands back on
`LCOUNT L m′`).

```agda
inj₁K : ℕ → PTree UD (ExtI UD) (ℕ ⊎ Poly.⊤ {lzero})
inj₁K a′ = Ret (inj₁ a′)

lcK : ℕ → ℕ → PTree UD (ExtI UD) (ℕ ⊎ Poly.⊤ {lzero})
lcK L a = lcount-step L a >>= inj₁K

gstep : Bool → Bool → ℕ → PTree UD (ExtI UD) ℕ
gstep b₁ b₂ m = ((up   ⟶₀ Ret (suc m))  ◁ b₁ ▷ Stop)
              □ ((down ⟶₀ Ret (pred m)) ◁ b₂ ▷ Stop)

LCst : ℕ → Bool → Bool → ℕ → Proc
LCst L b₁ b₂ m = iter-bind (gstep b₁ b₂ m >>= inj₁K) (lcK L)

LC↝ : ℕ → ℕ → Proc
LC↝ L m = iter-bind (Ret m >>= inj₁K) (lcK L)
```

### §6.1 Step introductions

With the guards concrete, both `sVis` equations hold by `refl` (the □
offer map computes on the constructor-headed prefix/`Stop` nodes, and
`UD-≟` decides on the concrete channels).

```agda
LCst-up : ∀ L b₂ m → LCst L true b₂ m ─[ ev upE ]─► LC↝ L (suc m)
LCst-up L true  m = sVis {at = ⊤ , up} {a = tt} refl refl
LCst-up L false m = sVis {at = ⊤ , up} {a = tt} refl refl

LCst-dn : ∀ L b₁ m → LCst L b₁ true m ─[ ev downE ]─► LC↝ L (pred m)
LCst-dn L true  m = sVis {at = ⊤ , down} {a = tt} refl refl
LCst-dn L false m = sVis {at = ⊤ , down} {a = tt} refl refl
```

### §6.2 Step inversions

A visible step fires exactly one of the two guarded prefixes (and reports
its guard `≡ true`); the state is stable — its τ-part is the □'s
`□-mt`, pointwise `nothing` (both operands carry `∅t`), pushed through
the `bindT`/`iterT` wrappers by the two `TEmpty`-preservation lemmas.

```agda
LCst-ev-inv : ∀ L b₁ b₂ m {l : Ev} {t′ : Proc}
            → LCst L b₁ b₂ m ─[ ev l ]─► t′
            → (b₁ ≡ true × l ≡ upE   × t′ ≡ LC↝ L (suc m))
            ⊎ (b₂ ≡ true × l ≡ downE × t′ ≡ LC↝ L (pred m))
LCst-ev-inv L true true m (sRet ())
LCst-ev-inv L true true m (sVis {at = at} {a = a} refl br) with UD-≟ (⊤ , up) at
... | yes refl = inj₁ (refl , refl , sym (just-injective br))
... | no ¬up with UD-≟ (⊤ , down) at
...   | yes refl = inj₂ (refl , refl , sym (just-injective br))
...   | no ¬dn   = case br of λ ()
LCst-ev-inv L true false m (sRet ())
LCst-ev-inv L true false m (sVis {at = at} {a = a} refl br) with UD-≟ (⊤ , up) at
... | yes refl = inj₁ (refl , refl , sym (just-injective br))
... | no ¬up   = case br of λ ()
LCst-ev-inv L false true m (sRet ())
LCst-ev-inv L false true m (sVis {at = at} {a = a} refl br) with UD-≟ (⊤ , down) at
... | yes refl = inj₂ (refl , refl , sym (just-injective br))
... | no ¬dn   = case br of λ ()
LCst-ev-inv L false false m (sRet ())
LCst-ev-inv L false false m (sVis refl br) = case br of λ ()

bindT-empty : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
                (k : R → PTree UD (ExtI UD) S)
                {v  : (at : AnyTypes UD) → ContinueType at (Maybe (PTree UD (ExtI UD) R))}
                {τc : (i : AnyTypes (ExtI UD)) → ContinueType i (Maybe (PTree UD (ExtI UD) R))}
            → TEmpty τc → TEmpty (bindT k (react v τc))
bindT-empty k {τc = τc} emp i a with τc i a | emp i a
... | nothing | _ = refl

iterT-empty : ∀ {ℓr} {A : Set} {R : Set ℓr}
                (K : A → PTree UD (ExtI UD) (A ⊎ R))
                {v  : (at : AnyTypes UD) → ContinueType at (Maybe (PTree UD (ExtI UD) (A ⊎ R)))}
                {τc : (i : AnyTypes (ExtI UD)) → ContinueType i (Maybe (PTree UD (ExtI UD) (A ⊎ R)))}
            → TEmpty τc → TEmpty (iterT K (react v τc))
iterT-empty K {τc = τc} emp i a with τc i a | emp i a
... | nothing | _ = refl

-- the two guarded-prefix offer maps, named so all the implicits that sit
-- under the non-injective with-functions (□-mt / bindT / iterT) can be
-- supplied explicitly (unification cannot recover them)
upC dnC : ℕ → (at : AnyTypes UD) → ContinueType at (Maybe (PTree UD (ExtI UD) ℕ))
upC m = Prefix-cont up   (λ _ → Ret (suc m))
dnC m = Prefix-cont down (λ _ → Ret (pred m))

-- τ-refutation for a loop state whose body node (bv , bt) has empty τ-part
body-no-τ : ∀ L (bv : (at : AnyTypes UD) → ContinueType at (Maybe (PTree UD (ExtI UD) ℕ)))
              (bt : (i : AnyTypes (ExtI UD)) → ContinueType i (Maybe (PTree UD (ExtI UD) ℕ)))
          → TEmpty bt
          → ∀ (i : AnyTypes (ExtI UD)) (a : proj₁ i) {t′ : Proc}
          → iterT (lcK L) (react (bindV inj₁K (react bv bt))
                                 (bindT inj₁K (react bv bt))) i a ≡ just t′
          → ⊥
body-no-τ L bv bt emp i a br =
  case trans (sym (iterT-empty (lcK L) {v = bindV inj₁K (react bv bt)}
                               {τc = bindT inj₁K (react bv bt)}
                               (bindT-empty inj₁K {v = bv} {τc = bt} emp) i a)) br of λ ()

LCst-no-τ : ∀ L b₁ b₂ m {t′ : Proc} → LCst L b₁ b₂ m ─[ τ ]─► t′ → ⊥
LCst-no-τ L true true m (sSil ())
LCst-no-τ L true true m (sTau {i = i} {a = a} refl br) =
  body-no-τ L (mergeVis (upC m) (dnC m))
            (□-mt (react (upC m) ∅t) (react (dnC m) ∅t)
                  (up ⟶₀ Ret (suc m)) (down ⟶₀ Ret (pred m)))
            (□-mt-empty {vP = upC m} {vQ = dnC m}
                        {P = up ⟶₀ Ret (suc m)} {Q = down ⟶₀ Ret (pred m)}
                        ∅t-empty ∅t-empty)
            i a br
LCst-no-τ L true false m (sSil ())
LCst-no-τ L true false m (sTau {i = i} {a = a} refl br) =
  body-no-τ L (mergeVis (upC m) ∅v)
            (□-mt (react (upC m) ∅t) (react ∅v ∅t)
                  (up ⟶₀ Ret (suc m)) Stop)
            (□-mt-empty {vP = upC m} {vQ = ∅v}
                        {P = up ⟶₀ Ret (suc m)} {Q = Stop}
                        ∅t-empty ∅t-empty)
            i a br
LCst-no-τ L false true m (sSil ())
LCst-no-τ L false true m (sTau {i = i} {a = a} refl br) =
  body-no-τ L (mergeVis ∅v (dnC m))
            (□-mt (react ∅v ∅t) (react (dnC m) ∅t)
                  Stop (down ⟶₀ Ret (pred m)))
            (□-mt-empty {vP = ∅v} {vQ = dnC m}
                        {P = Stop} {Q = down ⟶₀ Ret (pred m)}
                        ∅t-empty ∅t-empty)
            i a br
LCst-no-τ L false false m (sSil ())
LCst-no-τ L false false m (sTau {i = i} {a = a} refl br) =
  body-no-τ L (mergeVis ∅v ∅v)
            (□-mt (react ∅v ∅t) (react ∅v ∅t) (Stop {R = ℕ}) Stop)
            (□-mt-empty {vP = ∅v} {vQ = ∅v}
                        {P = Stop {R = ℕ}} {Q = Stop}
                        ∅t-empty ∅t-empty)
            i a br
```

### §6.3 Big-step elimination and introduction

`LC-char` reads any big-step of `LCOUNT L m` as a `CTr L m` derivation
(`LC↝-char` chases the re-entry τ; `LC-dn-case` turns the `0 <ᵇ m`
guard into the `suc`-shape `cdn` needs); `LC-intro` rebuilds the
big-step from a `CTr` derivation.  Forward declarations replace a
`mutual` block, per the project conventions.

```agda
LC-char    : ∀ L m {s} {Q′ : Proc} → LCOUNT L m ⟹⟨ s ⟩ Q′ → CTr L m s
LC↝-char   : ∀ L m {s} {Q′ : Proc} → LC↝ L m ⟹⟨ s ⟩ Q′ → CTr L m s
LC-dn-case : ∀ L m {s} {Q′ : Proc} → (0 <ᵇ m) ≡ true
           → LC↝ L (pred m) ⟹⟨ s ⟩ Q′ → CTr L m (downE ∷ s)

LC-char L m ⟹-refl     = cnil
LC-char L m (⟹-τ st _) = ⊥-elim (LCst-no-τ L (m <ᵇ L) (0 <ᵇ m) m st)
LC-char L m (⟹-ev st rest) with LCst-ev-inv L (m <ᵇ L) (0 <ᵇ m) m st
... | inj₁ (g₁ , refl , refl) = cup (<ᵇ-sound m L g₁) (LC↝-char L (suc m) rest)
... | inj₂ (g₂ , refl , refl) = LC-dn-case L m g₂ rest

LC-dn-case L (suc m) _ rest = cdn (LC↝-char L m rest)

LC↝-char L m ⟹-refl        = cnil
LC↝-char L m (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = LC-char L m rest
LC↝-char L m (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

LC-intro : ∀ L m {s} → CTr L m s → traces (LCOUNT L m) s
LC-intro L m cnil = LCOUNT L m , ⟹-refl
LC-intro L m (cup lt tr) with LC-intro L (suc m) tr
... | Q′ , bs = Q′ , ⟹-ev up-step (⟹-τ (sSil refl) bs)
  where
    up-step : LCOUNT L m ─[ ev upE ]─► LC↝ L (suc m)
    up-step = subst (λ b → LCst L b (0 <ᵇ m) m ─[ ev upE ]─► LC↝ L (suc m))
                    (sym (<ᵇ-complete lt)) (LCst-up L (0 <ᵇ m) m)
LC-intro L _ (cdn {m = m} tr) with LC-intro L m tr
... | Q′ , bs = Q′ , ⟹-ev (LCst-dn L (suc m <ᵇ L) (suc m)) (⟹-τ (sSil refl) bs)
```

## §7. `Skip`'s traces

The right end of the `nCopies` chain: `Skip` contributes only `[]` or the
lone `√` (after which the residual is `deadlock`).

```agda
Skip-char : ∀ {s} {S′ : Proc} → Skip ⟹⟨ s ⟩ S′
          → (s ≡ []) ⊎ (s ≡ √ Poly.tt ∷ [])
Skip-char ⟹-refl                        = inj₁ refl
Skip-char (⟹-τ (sSil ()) _)
Skip-char (⟹-τ (sTau () _) _)
Skip-char (⟹-ev (sVis () _) _)
Skip-char (⟹-ev (sRet refl) ⟹-refl)     = inj₂ refl
Skip-char (⟹-ev (sRet refl) (⟹-τ st _)) = ⊥-elim (deadlock-no-τ st)
Skip-char (⟹-ev (sRet refl) (⟹-ev st _)) = ⊥-elim (deadlock-no-ev st)
```

## §8. The counting shuffle

The crux.  At the empty synchronisation set, `psync` is uninhabited
(`∅ES .mem` is `⊥`), so a `ParInter ∅ES` witness is a pure shuffle of
the two operand traces.  Shuffling an alternating `L1` trace (current
contribution `bv b`) into an `n`-bounded counter trace from `m` (with the
reachability invariant `m ≤ n`) yields an `(n+1)`-bounded counter trace
from `bv b + m` — the running count never escapes `[0, suc n]`:

- an `L1` `up` raises the count from `m` to `suc m`, legal since `m ≤ n < suc n`;
- an `L1` `down` (only from parity `true`) lowers `suc m` to `m`;
- a counter `up` (guard `suc m ≤ n`) keeps `bv b + suc m ≤ suc n`;
- a counter `down` steps `suc m₀` to `m₀`, preserving the invariant;
- `√` never happens: it would need `√` at the head of an `L1` trace (`p√`).

```agda
par-shuffle : ∀ {mg : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})}
                {n b m sP sQ s}
            → ParInter ∅ES mg sP sQ s → L1Tr b sP → CTr n m sQ → m ≤ n
            → CTr (suc n) (bv b + m) s
par-shuffle pnil          _        _   _   = cnil
par-shuffle (psync m∈ _)  _        _   _   = ⊥-elim m∈
par-shuffle (psoloL _ PI) (lup tl) ctr inv = cup (s≤s inv) (par-shuffle PI tl ctr inv)
par-shuffle (psoloL _ PI) (ldn tl) ctr inv = cdn (par-shuffle PI tl ctr inv)
par-shuffle {b = false} (psoloR _ PI) l1 (cup lt tl) inv =
  cup (≤-suc lt) (par-shuffle PI l1 tl lt)
par-shuffle {b = true}  (psoloR _ PI) l1 (cup lt tl) inv =
  cup (s≤s lt) (par-shuffle PI l1 tl lt)
par-shuffle {b = false} (psoloR _ PI) l1 (cdn tl) inv =
  cdn (par-shuffle PI l1 tl (pred-≤ inv))
par-shuffle {b = true}  (psoloR _ PI) l1 (cdn tl) inv =
  cdn (par-shuffle PI l1 tl (pred-≤ inv))
par-shuffle p√ () _ _

-- an L1 trace can never supply the √ that a joint termination would need,
-- so no shuffle absorbs a √-trace on the right
no-√-shuffle : ∀ {mg : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})}
                 {b sP s} {r : Poly.⊤ {lzero}}
             → ParInter ∅ES mg sP (√ r ∷ []) s → L1Tr b sP → ⊥
no-√-shuffle (psoloL _ PI) (lup tl) = no-√-shuffle PI tl
no-√-shuffle (psoloL _ PI) (ldn tl) = no-√-shuffle PI tl
no-√-shuffle p√ ()
```

## §9. Assembly

De-interleave a `nCopies (suc n)` trace with `Par-trace-elim ∅ES`,
characterise the left `L1` component (§5) and — recursively — the right
tail, and fold the shuffle through §8.  The `Skip` at the right end
contributes `[]` (fed to the shuffle as the empty counter trace
`CTr 0 0 []`) or its `√`, which §8 refutes.

```agda
nCopies-char : ∀ n {s} → traces (nCopies (suc n)) s → CTr (suc n) 0 s
nCopies-char zero (Rt , bs) with Par-trace-elim ∅ES mgI P1 Skip bs
... | sP , sQ , P′ , Q′ , rP , rQ , inter with Skip-char rQ
...   | inj₁ refl = par-shuffle inter (L1-char at0 rP) cnil z≤n
...   | inj₂ refl = ⊥-elim (no-√-shuffle inter (L1-char at0 rP))
nCopies-char (suc n) (Rt , bs) with Par-trace-elim ∅ES mgI P1 (nCopies (suc n)) bs
... | sP , sQ , P′ , Q′ , rP , rQ , inter =
      par-shuffle inter (L1-char at0 rP) (nCopies-char n (Q′ , rQ)) z≤n

count⊑interleave-safe n s tr = LC-intro (suc n) 0 (nCopies-char n tr)
```

## §10. Completeness: the interleaving realises every bounded run

The converse (liveness) direction: every trace of `LCOUNT (suc n) 0` is
a trace of `nCopies (suc n)`.

The engine is `unshuffle`, the inverse of §8's `par-shuffle`: it
*schedules* a `(suc n)`-bounded counter trace at count `bv b + m`
(reachability invariant `m ≤ n`) into an `L1` trace from parity `b` and
an `n`-bounded counter trace from `m`, with the `ParInter ∅ES` witness
recording who took each event.  The greedy policy:

- give an `up` to the loop whenever it is currently down (`b = false`) —
  the loop flips to `true` and the residual counter is untouched;
- otherwise (`b = true`) give the `up` to the residual counter — the
  head guard `suc (suc m) ≤ suc n` is exactly the residual guard
  `suc m ≤ n` plus the loop's contribution, so `cup` applies;
- dually, give a `down` to the loop whenever it is up (`b = true`),
  and to the residual counter otherwise (whose state `m` is then
  necessarily a `suc`, since the head `cdn` fired from count `m > 0`).

Both structural-recursive calls are on the tail of the `CTr`
derivation, so `unshuffle` terminates on the nose.  (At the empty
synchronisation set, `psync` never applies — its side condition is
`⊥` — so `psoloL`/`psoloR` with the trivial refutation `λ z → z` cover
every event.)

```agda
s≤s-inv : ∀ {m n} → suc m ≤ suc n → m ≤ n
s≤s-inv (s≤s h) = h

unshuffle : ∀ n b m {s}
          → CTr (suc n) (bv b + m) s → m ≤ n
          → Σ[ sP ∈ List Ev ] Σ[ sQ ∈ List Ev ]
            (L1Tr b sP × CTr n m sQ × ParInter ∅ES mgI sP sQ s)
unshuffle n false m        cnil        inv = [] , [] , lnil , cnil , pnil
unshuffle n false m        (cup lt tl) inv with unshuffle n true m tl inv
... | sP , sQ , l1 , ctr , PI =
      upE ∷ sP , sQ , lup l1 , ctr , psoloL (λ z → z) PI
unshuffle n false (suc m₀) (cdn tl)    inv with unshuffle n false m₀ tl (pred-≤ inv)
... | sP , sQ , l1 , ctr , PI =
      sP , downE ∷ sQ , l1 , cdn ctr , psoloR (λ z → z) PI
unshuffle n true  m        cnil        inv = [] , [] , lnil , cnil , pnil
unshuffle n true  m        (cup lt tl) inv with unshuffle n true (suc m) tl (s≤s-inv lt)
... | sP , sQ , l1 , ctr , PI =
      sP , upE ∷ sQ , l1 , cup (s≤s-inv lt) ctr , psoloR (λ z → z) PI
unshuffle n true  m        (cdn tl)    inv with unshuffle n false m tl inv
... | sP , sQ , l1 , ctr , PI =
      downE ∷ sP , sQ , ldn l1 , ctr , psoloL (λ z → z) PI
```

An `L1Tr` is read back as a big step of the loop, starting from the
parity's state (§5's `L1St` in the intro direction): each `lup` is the
strong step `P1-up`, each `ldn` is `P1↑-down` followed by the silent
re-entry `P1↑↓-τ` (all three are chapter-1 `refl`-steps).

```agda
L1st : Bool → Proc
L1st false = P1
L1st true  = P1↑

L1-intro : ∀ {b s} → L1Tr b s → Σ[ P′ ∈ Proc ] (L1st b ⟹⟨ s ⟩ P′)
L1-intro {b} lnil = L1st b , ⟹-refl
L1-intro (lup tl) with L1-intro tl
... | P′ , bs = P′ , ⟹-ev P1-up bs
L1-intro (ldn tl) with L1-intro tl
... | P′ , bs = P′ , ⟹-ev P1↑-down (⟹-τ P1↑↓-τ bs)
```

Assembly, mirroring §9 in the intro direction: peel one loop per level
of the `nCopies` chain with `unshuffle` (started at parity `false`,
count `0 = bv false + 0`, invariant `0 ≤ n`), realise the loop's share
with `L1-intro` and the residual share recursively, and re-interleave
with `Par-trace-intro ∅ES`.  At the bottom, a `0`-bounded counter
trace from `0` is necessarily empty (`cup` would need `1 ≤ 0`; `cdn`
starts from a positive count), and `Skip` realises it by standing
still.

```agda
count→copies : ∀ n {s} → CTr n 0 s → traces (nCopies n) s
count→copies zero    cnil       = Skip , ⟹-refl
count→copies zero    (cup () _)
count→copies (suc n) ctr with unshuffle n false 0 ctr z≤n
... | sP , sQ , l1 , ctr′ , PI with L1-intro l1 | count→copies n ctr′
...   | P′ , rP | Q′ , rQ = Par-trace-intro ∅ES mgI P1 (nCopies n) rP rQ PI
```

The theorem (FDR: every `LCOUNT(N,0)` trace is an `L'(N)` trace):

```agda
interleave⊑count : ∀ n → nCopies (suc n) ⊑T LCOUNT (suc n) 0
interleave⊑count n s (Q′ , bs) = count→copies (suc n) (LC-char (suc n) 0 bs)
```

## §11. The book's assertions

TPC §2.3 checks the equivalence at `N = 9` and `N = 10`; both are
instances of the two `∀ N ≥ 1` theorems (`nCopies 9 = nCopies (suc 8)`
is nine interleaved copies, `nCopies 10 = nCopies (suc 9)` ten):

```agda
-- assert L'(9) [T= LCOUNT(9,0)
L'9⊑count9 : nCopies 9 ⊑T LCOUNT 9 0
L'9⊑count9 = interleave⊑count 8

-- assert LCOUNT(10,0) [T= L(10)
count10⊑L10 : LCOUNT 10 0 ⊑T nCopies 10
count10⊑L10 = count⊑interleave-safe 9
```

## §12. Status

Both directions of TPC §2.3's interleaving example are discharged for
every `N ≥ 1`: `count⊑interleave-safe` (safety, §9) and
`interleave⊑count` (completeness, §10) together give the trace
equivalence `traces (LCOUNT N 0) = traces (L'(N))`, with the book's
`N = 9` / `N = 10` assertions as instances (§11).  No postulates, no
`NON_TERMINATING`, no `mutual` blocks.
