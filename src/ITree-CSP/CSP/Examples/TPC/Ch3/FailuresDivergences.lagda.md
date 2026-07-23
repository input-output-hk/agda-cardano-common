# TPC chapter 3: failures refinement, divergence, and the strictness of ⊓

Chapter-3 example porting the failures/divergences illustrations of A.W.
Roscoe's *The Theory and Practice of Concurrency* (TPC §3.3).  Source:

- `fdr-examples/tpc/chapter03/section3-3.csp`

The section's processes contrast external and internal choice in the
*failures* model, and exhibit divergence created by hiding:

```csp
channel a, b, c

Q1 = (a -> STOP) [] (b -> STOP)
Q2 = (a -> STOP) |~| (b -> STOP)
Q3 = STOP |~| Q1

AS  = a -> AS
DIV = AS \ {a}
```

- `Q1` deterministically *offers* both `a` and `b`; its only stable
  refusals before acting exclude both events.
- `Q2` may internally commit to either branch, so it can refuse `{a}` or
  `{b}` (but not `{a,b}`): strictly more failures than `Q1`.
- `Q3` can moreover deadlock outright via the `STOP` branch: strictly
  more failures again.  Hence the failures-refinement chain
  `Q3 ⊑F Q2 ⊑F Q1`.
- `DIV` hides the only event of the unguardedly recursive `AS`, turning
  its infinite `a`-stream into an infinite τ-stream: **livelock**.  In the
  divergence-strict FD model `DIV` is identified with `div` (immediate
  divergence, the FD-bottom `⊥`), and `⊓` is **divergence-strict**:
  `Q3 ⊓ DIV ≈FD DIV`.

This module proves exactly those four facts:

```text
Q3⊑F⊥Q2        : Q3 ⊑F⊥ Q2
Q2⊑F⊥Q1        : Q2 ⊑F⊥ Q1
DIV≈FDdiv      : DIV ≈FD div
Q3⊓DIV≈FD-DIV  : (Q3 ⊓ DIV) ≈FD DIV
```

§7 extends this with the section's `Q4 = (a -> STOP) |~| (b -> DIV)`
quartet — the asserts that *distinguish* the failures model from the
failures-divergences model (see §7 for the statements and for a
model-theoretic subtlety about which refinement renders FDR's `[F=`).

The two refinements are proved *constructively* by case analysis on the
`⟹`/`Refuses` witnesses (no classical postulate is on the proof path:
the divergence disjunct of `failures⊥` is refuted by hand for these
finite convergent processes, rather than routed through the certified
`□-Diverges→` projection).  `DIV≈FDdiv` is proved by exhibiting the τ-loop
divergence of `DIV`, making both sides FD-bottom (the same pattern as
`⊓-zero-FD` in `CSP.Laws.FD.FDLawsIChoiceZero`); the strictness law is
then a chain of already-validated ≈FD laws.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch3.FailuresDivergences where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
```

## §2. The event type and decidable equality

Three nullary visible events, mirroring `channel a, b, c` (`c` plays no
role in the processes; it exists so that refusal sets have something
strictly outside `{a, b}` to talk about, as in the book).

```agda
data FCh : Set → Set where
  a b c : FCh ⊤

FCh-≟ : (x y : AnyTypes FCh) → Dec (x ≡ y)
FCh-≟ (_ , a) (_ , a) = yes refl
FCh-≟ (_ , a) (_ , b) = no λ ()
FCh-≟ (_ , a) (_ , c) = no λ ()
FCh-≟ (_ , b) (_ , a) = no λ ()
FCh-≟ (_ , b) (_ , b) = yes refl
FCh-≟ (_ , b) (_ , c) = no λ ()
FCh-≟ (_ , c) (_ , a) = no λ ()
FCh-≟ (_ , c) (_ , b) = no λ ()
FCh-≟ (_ , c) (_ , c) = yes refl

open import CSP.Operators FCh-≟
```

`_□_` is parametrised by a `DecEq` instance on the return type; as in the
other `TPC` modules the only instance needed is the one for the
polymorphic unit type (the `Irrelevant⇒DecEq` idiom).

```agda
instance
  DecEq-⊤poly : DecEq (Poly.⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §3. Process definitions

```agda
FProc : Set₁
FProc = PTree FCh (ExtI FCh) (Poly.⊤ {lzero})

aSTOP bSTOP : FProc
aSTOP = a ⟶₀ Stop
bSTOP = b ⟶₀ Stop

Q1 : FProc                          -- (a -> STOP) [] (b -> STOP)
Q1 = aSTOP □ bSTOP

Q2 : FProc                          -- (a -> STOP) |~| (b -> STOP)
Q2 = aSTOP ⊓ bSTOP

Q3 : FProc                          -- STOP |~| Q1
Q3 = Stop ⊓ Q1
```

`AS = a -> AS` is a `loop0`, exactly like `P1` in the chapter-1 `UpDown`
module; `DIV` hides its single channel.  The hide-set is the channel-level
`EventSet` containing **only** `a`.

```agda
AS : FProc                          -- a -> AS
AS = loop0 (a ⟶₀ Skip)

hideA-cs : AnyTypes FCh → Set
hideA-cs (_ , a) = ⊤
hideA-cs (_ , b) = ⊥
hideA-cs (_ , c) = ⊥

hideA-dec : (at : AnyTypes FCh) → Dec (hideA-cs at)
hideA-dec (_ , a) = yes tt
hideA-dec (_ , b) = no λ ()
hideA-dec (_ , c) = no λ ()

hideA : EventSet
hideA = chanSet hideA-cs hideA-dec

DIV : FProc                         -- AS \ {a}
DIV = AS ∖ hideA
```

## §4. The failures refinements `Q3 ⊑F⊥ Q2 ⊑F⊥ Q1`

The FDR asserts `Q3 [F= Q2` and `Q2 [F= Q1`.  Here `_⊑F⊥_` is the
refinement of divergence-strict failures
(`failures⊥ P s B = failures P s B ⊎ divergences P s`), so each proof has
a failures part (rebuild the witness on the refining side) and a
divergence part (refute — none of `Q1`, `Q2`, `Q3` can diverge).

```agda
open import Semantics.LTS       {E = FCh} {I = ExtI FCh} hiding (Diverges)
open import Semantics.DRBisim   {E = FCh} {I = ExtI FCh} using (Diverges)
open import Semantics.Failures  {E = FCh} {I = ExtI FCh}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = FCh} {I = ExtI FCh}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _≈FD_;
         empty-div; div-extension-closed; ≈FD-refl; ≈FD-sym; ≈FD-trans)
open import CSP.Laws.Traces.TraceLaws FCh-≟ using (Stop-no-τ; Stop-no-ev)
open import CSP.Laws.Traces.PrefixInversion FCh-≟ using (⟶₀-no-τ; ⟶₀-ev-inv)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono FCh-≟
  using (□τR; cP; cQ; sPQ; sQP; chP; chQ; □-τ-elim;
         □evR; evP; evQ; evPQ; □-ev-elim)
open import CSP.Laws.FD.ExtChoiceComm FCh-≟ using (Stop-refuses; Stop-fail-nil)
open import CSP.Laws.FD.ExtChoiceFD FCh-≟ using (□-failures-elim-top)
open import CSP.Laws.FD.FDLawsIChoiceAssoc FCh-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)
```

### §4.1 The statements

```agda
-- assert Q3 [F= Q2   (holds)
Q3⊑F⊥Q2 : Q3 ⊑F⊥ Q2

-- assert Q2 [F= Q1   (holds)
Q2⊑F⊥Q1 : Q2 ⊑F⊥ Q1
```

### §4.2 Prefix/Stop scaffolding

Every behaviour of `e ⟶₀ Stop` is pinned down: it is stable, fires only
`e` (landing on `Stop`), and never diverges.  So its `failures⊥` traces
are exactly `[]` and `[e]` — the shape lemma that drives `Q3⊑F⊥Q2`.

```agda
Stop-⟹-empty : {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
             → Stop ⟹⟨ s ⟩ W → s ≡ []
Stop-⟹-empty ⟹-refl        = refl
Stop-⟹-empty (⟹-τ stp _)  = ⊥-elim (Stop-no-τ stp)
Stop-⟹-empty (⟹-ev stp _) = ⊥-elim (Stop-no-ev stp)

Stop-reach-¬div : {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
                → Stop ⟹⟨ s ⟩ W → Diverges W → ⊥
Stop-reach-¬div ⟹-refl        d = Stop-no-τ (d .Diverges.step)
Stop-reach-¬div (⟹-τ stp _)  _ = Stop-no-τ stp
Stop-reach-¬div (⟹-ev stp _) _ = Stop-no-ev stp

pfx-¬div : (e : FCh ⊤) → Diverges (e ⟶₀ Stop) → ⊥
pfx-¬div e d = ⟶₀-no-τ (d .Diverges.step)

pfx-reach-¬div : (e : FCh ⊤) {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
               → (e ⟶₀ Stop) ⟹⟨ s ⟩ W → Diverges W → ⊥
pfx-reach-¬div e ⟹-refl          d = pfx-¬div e d
pfx-reach-¬div e (⟹-τ stp _)    _ = ⟶₀-no-τ stp
pfx-reach-¬div e (⟹-ev stp rest) d with ⟶₀-ev-inv stp
... | _ , refl , refl = Stop-reach-¬div rest d

-- the failures⊥ of e ⟶₀ Stop live at exactly the traces [] and [e]
pfx-fail⊥-shape : (e : FCh ⊤) {s : List (Event√ (Poly.⊤ {lzero}))}
                  {B : Event√ (Poly.⊤ {lzero}) → Set lzero}
                → failures⊥ (e ⟶₀ Stop) s B
                → (s ≡ []) ⊎ (s ≡ evl (evLabel ⊤ e tt) ∷ [])
pfx-fail⊥-shape e (inj₁ (_ , ⟹-refl , _))       = inj₁ refl
pfx-fail⊥-shape e (inj₁ (_ , ⟹-τ stp _ , _))    = ⊥-elim (⟶₀-no-τ stp)
pfx-fail⊥-shape e (inj₁ (_ , ⟹-ev stp rest , _)) with ⟶₀-ev-inv stp
... | _ , refl , refl =
      inj₂ (cong (evl (evLabel ⊤ e tt) ∷_) (Stop-⟹-empty rest))
pfx-fail⊥-shape e (inj₂ d) =
  ⊥-elim (pfx-reach-¬div e (d .IsDivergence.reach) (d .IsDivergence.divwit))
```

### §4.3 `Q1`'s visible steps

`Q1` is a stable external choice of two prefix nodes offering *distinct*
events, so its offer map computes: both steps hold by `refl` (the `□` of
two `react` nodes merges the offers pointwise, and only one operand offers
each event).

```agda
Q1-a : Q1 ─[ ev (evl (evLabel ⊤ a tt)) ]─► Stop
Q1-a = sVis {at = ⊤ , a} {a = tt} refl refl

Q1-b : Q1 ─[ ev (evl (evLabel ⊤ b tt)) ]─► Stop
Q1-b = sVis {at = ⊤ , b} {a = tt} refl refl
```

### §4.4 `Q3 ⊑F⊥ Q2`

Split the `Q2` behaviour into an operand (`⊓-failures⊥→`), read off its
trace shape (§4.2), and rebuild inside `Q3 = Stop ⊓ Q1`:

- trace `[]`: whatever `B` the operand refused, `Q3`'s `Stop` branch
  refuses it too (`Stop` refuses *everything*), via the left τ;
- trace `[a]` (resp. `[b]`): `Q3` commits right to `Q1`, fires the event
  (§4.3) and lands on `Stop`, which again refuses everything.

Both rebuilds produce a *superset* refusal, so the given `B` is covered.

```agda
Q3⊑F⊥Q2 f with ⊓-failures⊥→ aSTOP bSTOP f
... | inj₁ fa with pfx-fail⊥-shape a fa
...   | inj₁ refl = ⊓-failures⊥←l Stop Q1 (inj₁ Stop-fail-nil)
...   | inj₂ refl =
        ⊓-failures⊥←r Stop Q1 (inj₁ (Stop , ⟹-ev Q1-a ⟹-refl , Stop-refuses))
Q3⊑F⊥Q2 f | inj₂ fb with pfx-fail⊥-shape b fb
...   | inj₁ refl = ⊓-failures⊥←l Stop Q1 (inj₁ Stop-fail-nil)
...   | inj₂ refl =
        ⊓-failures⊥←r Stop Q1 (inj₁ (Stop , ⟹-ev Q1-b ⟹-refl , Stop-refuses))
```

### §4.5 `Q1` never diverges

For `Q2⊑F⊥Q1`'s divergence disjunct we refute any divergence reached from
`Q1` — constructively, by chasing the big-step through the `□`
step-inversions.  A τ of `Q1` is impossible unless it commits/slides,
and every such shape carries an operand τ, refuted by `⟶₀-no-τ`; a
visible step lands in `Stop` (via §4.2); the both-fire case `evPQ` is
impossible since `aSTOP` and `bSTOP` offer distinct events.

```agda
Q1-¬div : Diverges Q1 → ⊥
Q1-¬div d with □-τ-elim aSTOP bSTOP (d .Diverges.step)
... | cP eq         = pfx-¬div a (subst Diverges eq (d .Diverges.rest))
... | cQ eq         = pfx-¬div b (subst Diverges eq (d .Diverges.rest))
... | sPQ _ Pτ _    = ⟶₀-no-τ Pτ
... | sQP _ Qτ _    = ⟶₀-no-τ Qτ
... | chP _ Pτ _    = ⟶₀-no-τ Pτ
... | chQ _ Qτ _    = ⟶₀-no-τ Qτ

Q1-reach-¬div : {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
              → Q1 ⟹⟨ s ⟩ W → Diverges W → ⊥
Q1-reach-¬div ⟹-refl d = Q1-¬div d
Q1-reach-¬div (⟹-τ stp rest) d with □-τ-elim aSTOP bSTOP stp
... | cP refl       = pfx-reach-¬div a rest d
... | cQ refl       = pfx-reach-¬div b rest d
... | sPQ _ Pτ _    = ⟶₀-no-τ Pτ
... | sQP _ Qτ _    = ⟶₀-no-τ Qτ
... | chP _ Pτ _    = ⟶₀-no-τ Pτ
... | chQ _ Qτ _    = ⟶₀-no-τ Qτ
Q1-reach-¬div (⟹-ev stp rest) d with □-ev-elim aSTOP bSTOP stp
... | evP Pev with ⟶₀-ev-inv Pev
...   | _ , refl , refl = Stop-reach-¬div rest d
Q1-reach-¬div (⟹-ev stp rest) d | evQ Qev with ⟶₀-ev-inv Qev
... | _ , refl , refl = Stop-reach-¬div rest d
Q1-reach-¬div (⟹-ev stp rest) d | evPQ Pev Qev
  with ⟶₀-ev-inv Pev | ⟶₀-ev-inv Qev
... | _ , refl , _ | _ , () , _
```

### §4.6 `Q2 ⊑F⊥ Q1`

A (stable) failure of the external choice is a failure of one operand
(`□-failures-elim-top`, the constructive general `□` failures law), and
each operand's failures embed into the internal choice `Q2` by committing
with the corresponding τ (`⊓-failures⊥←l/r`).  A divergence of `Q1` is
refuted by §4.5.

```agda
Q2⊑F⊥Q1 (inj₁ f) with □-failures-elim-top {P = aSTOP} {Q = bSTOP} f
... | inj₁ fa = ⊓-failures⊥←l aSTOP bSTOP (inj₁ fa)
... | inj₂ fb = ⊓-failures⊥←r aSTOP bSTOP (inj₁ fb)
Q2⊑F⊥Q1 (inj₂ d) =
  ⊥-elim (Q1-reach-¬div (d .IsDivergence.reach) (d .IsDivergence.divwit))
```

## §5. `DIV ≈FD div`: hiding-induced livelock is FD-bottom

`AS` fires `a` into its one-step loop body and silently re-enters; with
`a` hidden, *both* steps of the cycle are τs, so `DIV` runs an infinite
τ-loop through two states:

```text
DIV = AS ∖ {a}  ─τ(hidden a)─►  AS¹ ∖ {a}  ─τ(loop re-entry)─►  DIV  ─τ─► …
```

In the divergence-strict model a process divergent at `[]` is divergent at
*every* trace (extension-closure), i.e. it is the bottom element ⊥ =
chaos: every `failures⊥`/`divergences` obligation is discharged by
producing that divergence.  Both `DIV` and `div` are such processes, so
they are ≈FD without further step analysis — exactly the proof pattern of
`⊓-zero-FD`.

### §5.1 The τ-cycle of `DIV`

As in the chapter-1 `UpDown` module, the post-`a` loop state is an
`iter-bind` term (the definitional unfolding of `loop0`'s successor), and
the strong steps of `AS` hold by `refl`.

```agda
open import CSP.Laws.Traces.TraceLawsHide FCh-≟ using (Hide-hidden; Hide-τ)
open import CSP.Laws.FD.FDLawsIChoiceZero FCh-≟ using (⊓-zero-FD; div-all)
open import CSP.Laws.FD.FDLawsIChoice     FCh-≟ using (⊓-comm-FD)
open import CSP.Laws.FD.FDLawsIChoiceRep  FCh-≟ using (⊓-cong-FD≈)

loopKA : Poly.⊤ {lzero} → PTree FCh (ExtI FCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
loopKA _ = (a ⟶₀ Skip) >>= (λ x → Ret (inj₁ x))

AS¹ : FProc
AS¹ = iter-bind (Skip >>= (λ x → Ret (inj₁ x))) loopKA

AS-a : AS ─[ ev (evl (evLabel ⊤ a tt)) ]─► AS¹
AS-a = sVis {at = ⊤ , a} {a = tt} refl refl

AS¹-τ : AS¹ ─[ τ ]─► AS
AS¹-τ = sSil refl

-- the hidden a becomes a τ (Hide-hidden); the loop re-entry τ propagates (Hide-τ)
DIV-slide : DIV ─[ τ ]─► (AS¹ ∖ hideA)
DIV-slide = Hide-hidden hideA AS tt AS-a

DIV-back : (AS¹ ∖ hideA) ─[ τ ]─► DIV
DIV-back = Hide-τ hideA AS¹ AS¹-τ
```

### §5.2 `DIV` diverges

The two-state τ-cycle, as a corecursive pair (forward declarations, no
`mutual` block).

```agda
DIV-diverges  : Diverges DIV
DIV¹-diverges : Diverges (AS¹ ∖ hideA)

DIV-diverges .Diverges.next = AS¹ ∖ hideA
DIV-diverges .Diverges.step = DIV-slide
DIV-diverges .Diverges.rest = DIV¹-diverges

DIV¹-diverges .Diverges.next = DIV
DIV¹-diverges .Diverges.step = DIV-back
DIV¹-diverges .Diverges.rest = DIV-diverges

-- divergence-strictness: divergent at [], hence at EVERY trace
DIV-div-all : {s : List (Event√ (Poly.⊤ {lzero}))} → divergences DIV s
DIV-div-all = div-extension-closed (empty-div DIV-diverges)
```

### §5.3 The equivalence

```agda
DIV≈FDdiv : DIV ≈FD div
DIV≈FDdiv =
    ( (λ _ → inj₂ DIV-div-all) , (λ _ → DIV-div-all) )
  , ( (λ _ → inj₂ div-all)     , (λ _ → div-all) )
```

(`DIV` is in fact even divergence-respecting weakly bisimilar to `div` —
both are pure τ-loops — but the FD identification above is all the
chapter's asserts need, and it falls out of divergence-strictness
directly.)

## §6. Strictness of ⊓: `Q3 ⊓ DIV ≈FD DIV`

`Q3 ⊓ DIV` is *not* ≈DR-equal to `DIV` (it has a non-divergent τ-branch
to `Q3`), so this is genuinely an FD-model law: one divergent operand
poisons the whole choice.  It is a chain of already-validated ≈FD laws —
commutativity, the ≈FD-premised congruence, and the div-zero law
`⊓-zero-FD : (div ⊓ P) ≈FD div`:

```text
Q3 ⊓ DIV  ≈FD  DIV ⊓ Q3       (⊓-comm-FD)
          ≈FD  div ⊓ Q3       (⊓-cong-FD≈ DIV≈FDdiv (≈FD-refl Q3))
          ≈FD  div            (⊓-zero-FD Q3)
          ≈FD  DIV            (≈FD-sym DIV≈FDdiv)
```

```agda
Q3⊓DIV≈FD-DIV : (Q3 ⊓ DIV) ≈FD DIV
Q3⊓DIV≈FD-DIV =
  ≈FD-trans (⊓-comm-FD Q3 DIV)
 (≈FD-trans (⊓-cong-FD≈ DIV≈FDdiv (≈FD-refl Q3))
 (≈FD-trans (⊓-zero-FD Q3) (≈FD-sym DIV≈FDdiv)))
```

## §7. `Q4`: divergence distinguishes `[F=` from `[FD=`

The section's last four asserts contrast the failures model with the
failures-divergences model on

```csp
Q4 = (a -> STOP) |~| (b -> DIV)
```

```agda
bDIV : FProc
bDIV = b ⟶₀ DIV

Q4 : FProc                          -- (a -> STOP) |~| (b -> DIV)
Q4 = aSTOP ⊓ bDIV
```

FDR reports (TPC §3.3):

```text
assert Q2 [F=  Q4   -- holds : after b, Q4 has NO stable failures at all
assert Q4 [F=  Q2   -- FAILS : Q2 after b is STOP, which refuses everything
assert Q2 [FD= Q4   -- FAILS : Q4 diverges after b, Q2 does not
assert Q4 [FD= Q2   -- holds : the divergent Q4 is chaos after b (⊒ anything)
```

**Which formal refinement renders `[F=`?**  FDR's `[F=` is the *stable
failures* model — in this development `_⊑F_` (`Semantics.Failures`), *not*
the divergence-strict `_⊑F⊥_` (`failures⊥ P s B = failures P s B ⊎
divergences P s`).  For the divergence-free `Q1`–`Q3` of §4 the two
coincide, but on `Q4` they *differ*, and the F-pair **flips** under
`_⊑F⊥_`: divergences are extension-closed, so `failures⊥ Q4 ⟨b,b⟩ B`
holds (via `Q4 ⟹⟨b⟩ DIV` and `Diverges DIV`) while `failures⊥ Q2 ⟨b,b⟩ B`
is empty (`Q2` neither traces `⟨b,b⟩` nor diverges) — hence
`¬ (Q2 ⊑F⊥ Q4)`; and conversely `Q4 ⊑F⊥ Q2` *holds*, because `Q4`'s
divergence-chaos after `b` absorbs `Q2`'s post-`b` `STOP` failures.
This module therefore proves **six** facts — the book's quartet (with
`_⊑F_` carrying the two `[F=` asserts) *and* the two flipped `⊑F⊥` facts
that exhibit the divergence-strictness of `failures⊥`:

```text
Q2⊑FQ4    : Q2 ⊑F Q4          (assert 1, stable failures — holds)
¬Q4⊑FQ2   : ¬ (Q4 ⊑F Q2)      (assert 2 — fails)
¬Q2⊑FDQ4  : ¬ (Q2 ⊑FD Q4)     (assert 3 — fails)
Q4⊑FDQ2   : Q4 ⊑FD Q2         (assert 4 — holds)
¬Q2⊑F⊥Q4  : ¬ (Q2 ⊑F⊥ Q4)     (the F-pair flips divergence-strictly …)
Q4⊑F⊥Q2   : Q4 ⊑F⊥ Q2         (… in both directions)
```

### §7.1 Imports and statements

```agda
open import Semantics.Failures            {E = FCh} {I = ExtI FCh} using (_⊑F_)
open import Semantics.Refusals            {E = FCh} {I = ExtI FCh} using (Offers; Refuses)
open import Semantics.FailuresDivergences {E = FCh} {I = ExtI FCh} using (_⊑D_; _⊑FD_)
open import Semantics.DRImpliesFD         {E = FCh} {I = ExtI FCh} using (stable-no-τ)
open import CSP.Laws.Traces.PrefixInversion FCh-≟
  using (loop-pfx-no-τ; loop-pfx-ev-inv; sil-no-ev; sil-τ-uniq)
open import CSP.Laws.Traces.TraceLawsHide FCh-≟
  using (Hide-τ-elim; Hide-ev-elim; hτP; hτH; heV; he√)
open import CSP.Laws.FD.ExtChoiceFD FCh-≟ using (mk-stable)
open import CSP.Laws.FD.FDLawsIChoiceAssoc FCh-≟
  using (⊓-failures→; ⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←r; ⊓-⟹-inr)

evB : Event√ (Poly.⊤ {lzero})
evB = evl (evLabel ⊤ b tt)

Q2⊑FQ4   : Q2 ⊑F Q4
¬Q4⊑FQ2  : ¬ (Q4 ⊑F Q2)
¬Q2⊑FDQ4 : ¬ (Q2 ⊑FD Q4)
Q4⊑FDQ2  : Q4 ⊑FD Q2
¬Q2⊑F⊥Q4 : ¬ (Q2 ⊑F⊥ Q4)
Q4⊑F⊥Q2  : Q4 ⊑F⊥ Q2
```

### §7.2 `DIV` emits nothing and is never stable

The two states of `DIV`'s τ-cycle (§5.1) offer no visible events and each
has an enabled τ, so *no weakly reachable state of `DIV` is stable* —
that is why `Q4` has no stable failures after `b`.  The single-step
inversions come from the generic loop lemmas (`AS` *is* the `iter-bind`
form definitionally) and the `sil`-node helpers, pushed through the hide
inversions `Hide-τ-elim`/`Hide-ev-elim`.

```agda
DIV¹ : FProc
DIV¹ = AS¹ ∖ hideA

AS-no-τ : {W : FProc} → AS ─[ τ ]─► W → ⊥
AS-no-τ = loop-pfx-no-τ a (λ _ → Skip) loopKA

AS-ev-target : {l : Event√ (Poly.⊤ {lzero})} {W : FProc} → AS ─[ ev l ]─► W → W ≡ AS¹
AS-ev-target stp with loop-pfx-ev-inv a (λ _ → Skip) loopKA stp
... | _ , _ , eqW = eqW

-- DIV's τ is the hidden `a` (AS itself has no τ), landing on DIV¹ …
DIV-τ-next : {W : FProc} → DIV ─[ τ ]─► W → W ≡ DIV¹
DIV-τ-next stp with Hide-τ-elim hideA AS stp
... | hτP P′ ASτ _        = ⊥-elim (AS-no-τ ASτ)
... | hτH P′ _ ASev eqW with AS-ev-target ASev
...   | refl = eqW

-- … and DIV¹'s τ is the loop re-entry `sil`, landing back on DIV
DIV¹-τ-next : {W : FProc} → DIV¹ ─[ τ ]─► W → W ≡ DIV
DIV¹-τ-next stp with Hide-τ-elim hideA AS¹ stp
... | hτH P′ _ AS¹ev _    = ⊥-elim (sil-no-ev refl AS¹ev)
... | hτP P′ AS¹τ eqW with sil-τ-uniq refl AS¹τ
...   | refl = eqW

-- no visible event survives the hide: AS offers only `a`, and a ∈ hideA
DIV-no-ev : {l : Event√ (Poly.⊤ {lzero})} {W : FProc} → DIV ─[ ev l ]─► W → ⊥
DIV-no-ev stp with Hide-ev-elim hideA AS stp
... | he√ ()
... | heV P′ ¬mem ASev with loop-pfx-ev-inv a (λ _ → Skip) loopKA ASev
...   | _ , refl , _ = ¬mem tt

DIV¹-no-ev : {l : Event√ (Poly.⊤ {lzero})} {W : FProc} → DIV¹ ─[ ev l ]─► W → ⊥
DIV¹-no-ev stp with Hide-ev-elim hideA AS¹ stp
... | he√ ()
... | heV P′ _ AS¹ev = sil-no-ev refl AS¹ev

-- the τ-cycle: everything DIV weakly reaches is unstable (and emits nothing)
DIV-reach-unstable  : {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
                    → DIV  ⟹⟨ s ⟩ W → isStable W → ⊥
DIV¹-reach-unstable : {s : List (Event√ (Poly.⊤ {lzero}))} {W : FProc}
                    → DIV¹ ⟹⟨ s ⟩ W → isStable W → ⊥

DIV-reach-unstable ⟹-refl          st = stable-no-τ st DIV-slide
DIV-reach-unstable (⟹-τ stp rest)  st with DIV-τ-next stp
... | refl = DIV¹-reach-unstable rest st
DIV-reach-unstable (⟹-ev stp _)    _  = DIV-no-ev stp

DIV¹-reach-unstable ⟹-refl         st = stable-no-τ st DIV-back
DIV¹-reach-unstable (⟹-τ stp rest) st with DIV¹-τ-next stp
... | refl = DIV-reach-unstable rest st
DIV¹-reach-unstable (⟹-ev stp _)   _  = DIV¹-no-ev stp
```

### §7.3 Prefix scaffolding: refusal transfer and the `failures⊥` split

`b ⟶₀ P` and `b ⟶₀ Q` have the *same* offer map (only `b`) and the same
empty τ-part, so a refusal of one is a refusal of the other — this is
what lets `Q2`'s `b`-branch cover `Q4`'s and vice versa at the empty
trace.

```agda
pfx-stable : (e : FCh ⊤) (P : FProc) → isStable (e ⟶₀ P)
pfx-stable e P = mk-stable {t = e ⟶₀ P} refl (λ i x → refl)

b-offers-swap : (P Q : FProc) {l : Event√ (Poly.⊤ {lzero})}
              → Offers (b ⟶₀ P) l → Offers (b ⟶₀ Q) l
b-offers-swap P Q (W , stp) with ⟶₀-ev-inv stp
... | _ , refl , _ = Q , sVis {at = ⊤ , b} {a = tt} refl refl

b-refuses-swap : (P Q : FProc) {B : Event√ (Poly.⊤ {lzero}) → Set lzero}
               → Refuses (b ⟶₀ P) B → Refuses (b ⟶₀ Q) B
b-refuses-swap P Q (_ , nof) =
  pfx-stable b Q , λ e Be off → nof e Be (b-offers-swap Q P off)
```

A refinement of §4.2's shape lemma that also *returns* the refusal in the
empty-trace case (needed to rebuild it on the other `⊓`-operand):

```agda
pfx-fail⊥-split : (e : FCh ⊤) {s : List (Event√ (Poly.⊤ {lzero}))}
                  {B : Event√ (Poly.⊤ {lzero}) → Set lzero}
                → failures⊥ (e ⟶₀ Stop) s B
                → ((s ≡ []) × Refuses (e ⟶₀ Stop) B)
                  ⊎ (s ≡ evl (evLabel ⊤ e tt) ∷ [])
pfx-fail⊥-split e (inj₁ (_ , ⟹-refl , ref))        = inj₁ (refl , ref)
pfx-fail⊥-split e (inj₁ (_ , ⟹-τ stp _ , _))       = ⊥-elim (⟶₀-no-τ stp)
pfx-fail⊥-split e (inj₁ (_ , ⟹-ev stp rest , _)) with ⟶₀-ev-inv stp
... | _ , refl , refl =
      inj₂ (cong (evl (evLabel ⊤ e tt) ∷_) (Stop-⟹-empty rest))
pfx-fail⊥-split e (inj₂ d) =
  ⊥-elim (pfx-reach-¬div e (d .IsDivergence.reach) (d .IsDivergence.divwit))
```

The *stable failures* of `bDIV = b ⟶₀ DIV` live only at the empty trace:
firing `b` lands in `DIV`, none of whose reachable states is stable
(§7.2).

```agda
bDIV-fail-shape : {s : List (Event√ (Poly.⊤ {lzero}))}
                  {X : Event√ (Poly.⊤ {lzero}) → Set lzero}
                → failures bDIV s X → (s ≡ []) × Refuses bDIV X
bDIV-fail-shape (_ , ⟹-refl , ref)  = refl , ref
bDIV-fail-shape (_ , ⟹-τ stp _ , _) = ⊥-elim (⟶₀-no-τ stp)
bDIV-fail-shape (_ , ⟹-ev stp rest , (stW , _)) with ⟶₀-ev-inv stp
... | _ , refl , refl = ⊥-elim (DIV-reach-unstable rest stW)
```

### §7.4 The divergence witnesses

`Q4` commits right (`⊓-⟹-inr`), fires `b` and reaches the divergent
`DIV`, so `⟨b⟩ ∈ divergences Q4`; extension-closure then puts *every*
extension — e.g. `⟨b,b⟩`, which is not even a trace of `Q2` — in as well.
`Q2` never diverges (both operands are τ-free prefix processes).

```agda
bSTOP-b : bSTOP ─[ ev evB ]─► Stop
bSTOP-b = sVis {at = ⊤ , b} {a = tt} refl refl

bDIV-b : bDIV ─[ ev evB ]─► DIV
bDIV-b = sVis {at = ⊤ , b} {a = tt} refl refl

bDIV-div-b : divergences bDIV (evB ∷ [])
bDIV-div-b = record { prefix = evB ∷ [] ; suffix = [] ; split = refl
                    ; witness = DIV ; reach = ⟹-ev bDIV-b ⟹-refl
                    ; divwit = DIV-diverges }

Q4-div-b : divergences Q4 (evB ∷ [])
Q4-div-b = ⊓-div←r aSTOP bDIV bDIV-div-b

Q4-div-bb : divergences Q4 (evB ∷ evB ∷ [])
Q4-div-bb = div-extension-closed {t = evB ∷ []} Q4-div-b

Q2-¬div : {s : List (Event√ (Poly.⊤ {lzero}))} → divergences Q2 s → ⊥
Q2-¬div d with ⊓-div→ aSTOP bSTOP d
... | inj₁ da = pfx-reach-¬div a (da .IsDivergence.reach) (da .IsDivergence.divwit)
... | inj₂ db = pfx-reach-¬div b (db .IsDivergence.reach) (db .IsDivergence.divwit)
```

### §7.5 The stable-failures pair: `Q2 ⊑F Q4` holds, `Q4 ⊑F Q2` fails

*Holds:* a stable failure of `Q4` is one of an operand
(`⊓-failures→`).  The `aSTOP` operand is shared with `Q2`.  A `bDIV`
failure lives only at `[]` (§7.3), where its refusal transfers to
`Q2`'s `bSTOP` branch (`b-refuses-swap`).

```agda
Q2⊑FQ4 s X f with ⊓-failures→ aSTOP bDIV f
... | inj₁ fa = ⊓-failures←l aSTOP bSTOP fa
... | inj₂ fb with bDIV-fail-shape fb
...   | refl , ref =
        ⊓-failures←r aSTOP bSTOP (bSTOP , ⟹-refl , b-refuses-swap DIV Stop ref)
```

*Fails:* the distinguishing witness is the failure `(⟨b⟩ , Σ)` — after
`b`, `Q2` sits in the stable `STOP`, which refuses the whole alphabet;
`Q4` after `b` is in `DIV`'s τ-cycle and is *never* stable, so it has no
failure at `⟨b⟩` whatsoever.  Feeding the witness through an assumed
`Q4 ⊑F Q2` demands one, which §7.2/§7.3 refute (`aSTOP` cannot fire `b`;
`bDIV`'s failures sit at `[]`, not `⟨b⟩`).

```agda
Xall : Event√ (Poly.⊤ {lzero}) → Set
Xall _ = ⊤

Q2-fail-b : failures Q2 (evB ∷ []) Xall
Q2-fail-b = Stop , ⊓-⟹-inr aSTOP bSTOP (⟹-ev bSTOP-b ⟹-refl) , Stop-refuses

¬Q4⊑FQ2 h with ⊓-failures→ aSTOP bDIV (h (evB ∷ []) Xall Q2-fail-b)
... | inj₁ fa with pfx-fail⊥-split a (inj₁ fa)
...   | inj₁ (() , _)
...   | inj₂ ()
¬Q4⊑FQ2 h | inj₂ fb with bDIV-fail-shape fb
...   | () , _
```

### §7.6 The FD pair: `Q2 ⊑FD Q4` fails, `Q4 ⊑FD Q2` holds

*Fails:* `⊑FD`'s divergence component demands
`divergences Q4 ⊆ divergences Q2`; `⟨b⟩` is in the former (§7.4) and the
latter is empty.

```agda
¬Q2⊑FDQ4 (_ , hD) = Q2-¬div (hD Q4-div-b)
```

*Holds:* the failures⊥ component is `Q4⊑F⊥Q2` below (§7.7); the
divergence component is vacuous, `Q2` having no divergences.

```agda
Q4⊑FDQ2 = Q4⊑F⊥Q2 , (λ d → ⊥-elim (Q2-¬div d))
```

### §7.7 The divergence-strict flip

Under `failures⊥` the F-pair inverts.  *`Q4 ⊑F⊥ Q2` holds:* split a `Q2`
behaviour into an operand's (`⊓-failures⊥→`); the `aSTOP` side is shared;
a `bSTOP` behaviour at `[]` transfers its refusal onto `bDIV` (same offer
map), and at `⟨b⟩` is *absorbed by `Q4`'s divergence-chaos* — the
`inj₂ bDIV-div-b` disjunct, no refusal analysis needed.  This is exactly
Roscoe's "`⊥` refines to everything below it": `Q4` is chaos after `b`.

```agda
Q4⊑F⊥Q2 f with ⊓-failures⊥→ aSTOP bSTOP f
... | inj₁ fa = ⊓-failures⊥←l aSTOP bDIV fa
... | inj₂ fb with pfx-fail⊥-split b fb
...   | inj₁ (refl , ref) =
        ⊓-failures⊥←r aSTOP bDIV
          (inj₁ (bDIV , ⟹-refl , b-refuses-swap Stop DIV ref))
...   | inj₂ refl = ⊓-failures⊥←r aSTOP bDIV (inj₂ bDIV-div-b)
```

*`Q2 ⊑F⊥ Q4` fails:* divergences are extension-closed, so
`failures⊥ Q4 ⟨b,b⟩ B` holds for every `B` — but `⟨b,b⟩` is not even a
*trace* of `Q2` (and `Q2` never diverges), so `failures⊥ Q2 ⟨b,b⟩ B` is
empty.  This is the precise sense in which the divergence-strict
failures order already *sees* the divergence that the stable-failures
order ignores.

```agda
¬Q2⊑F⊥Q4 h with ⊓-failures⊥→ aSTOP bSTOP (h {B = Xall} (inj₂ Q4-div-bb))
... | inj₁ fa with pfx-fail⊥-split a fa
...   | inj₁ (() , _)
...   | inj₂ ()
¬Q2⊑F⊥Q4 h | inj₂ fb with pfx-fail⊥-split b fb
...   | inj₁ (() , _)
...   | inj₂ ()
```
