# TPC chapter 3: hiding the internal channel of a buffer chain

First chapter-3 example, porting the hiding example of A.W. Roscoe's *The
Theory and Practice of Concurrency* (TPC §3.1).  Source:

- `fdr-examples/tpc/chapter03/section3-1.csp`

```csp
T = {0,1}
N = 2
channel dd : {0..N}.T

COPY'(i) = dd.i?x -> dd.i+1!x -> COPY'(i)

BCHAIN = || i : {0..N-1} @ [{|dd.i, dd.i+1|}] COPY'(i)

HCHAIN = BCHAIN \ {| dd.i | i <- {1..N-1} |}

BN(s) =    #s < N & dd.0?x  -> BN(s ^ <x>)
        [] #s > 0 & dd.N!head(s) -> BN(tail(s))

assert BN(<>) [FD= HCHAIN
assert HCHAIN [FD= BN(<>)
```

A chain of `N` one-place `COPY'` cells passes values along the indexed
channel family `dd.0 … dd.N`: cell `i` reads on `dd.i` and writes on
`dd.i+1`, adjacent cells synchronising on the shared middle channel.
**Hiding** the internal channels `dd.1 … dd.N-1` leaves only the outer
interface `dd.0` (input) and `dd.N` (output); the result is
failures-divergences equal to the sequential `N`-place buffer `BN` — the
internal hand-off becomes a τ that no environment can see or block, and
since only finitely many τs ever happen between visible events, hiding
introduces **no divergence**.

**Modelling reductions:**

- **Payload.** `T = {0,1}` becomes `Bool`.
- **The channel family as one indexed channel.** `dd : {0..N}.T` becomes a
  single channel `dd : DCh (ℕ × Bool)` carrying *(position index, value)*.
  "Cell `i` reads on `dd.i`" is a **value-guarded** offer: accept exactly
  the events `dd (i , x)`.  Synchronisation sets and hide-sets then become
  *value-level* `EventSet`s (predicates on the index component), which is
  what makes the whole family ℕ-indexable for the ∀`N` generalisation.
- **Alphabetised parallel as interface parallel.** As in the chapter-2
  `ChainedBuffers`, each cell respects its alphabet, so the alphabetised
  parallel of adjacent cells collapses to the interface parallel `_∥⇘_⇙_`
  on the intersection — the shared index (`syncAt (i+1)`).
- **`BN` as a stateful loop** over a `List Bool` state (oldest value at
  the head), input guarded by `length < N`, output guarded by non-emptiness.

This module proves the two FDR asserts at `N = 2`, and *stronger*: a
divergence-respecting weak bisimulation, hence the full
failures-divergences **equivalence**

```text
hchain2≈FD-buffer2 : HCHAIN 2 ≈FD BN 2
```

(both `[FD=` asserts are its two halves), and then (§7) generalises the
equivalence to **every** chain length:

```text
hchain≈FD-buffer  : ∀ N → HCHAIN N ≈FD BN N
hchain5≈FD-buffer5 : HCHAIN 5 ≈FD BN 5
```

The ∀`N` proof replaces §5's nine named configurations by an *indexed
configuration family* — a length-`N` vector of per-cell phases — and proves
the step characterisations once, by recursion over the vector.

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch3.HidingBuffer where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (tt)
import Data.Unit.Polymorphic as Poly
open import Data.Bool using (Bool; true; false; _∧_; T; if_then_else_)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Nat.Properties using () renaming (_≟_ to _ℕ≟_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees
```

## §2. The event type and its decidable equality

One channel `dd` carrying *(index , value)*; the index selects the chain
position (`dd.i` of the `.csp` family is `dd (i , _)` here).  With a single
constructor the hand-rolled decider is one diagonal clause.

```agda
data DCh : Set → Set where
  dd : DCh (ℕ × Bool)

DCh-≟ : (x y : AnyTypes DCh) → Dec (x ≡ y)
DCh-≟ (_ , dd) (_ , dd) = yes refl

open import CSP.Operators DCh-≟
open EventSet
```

## §3. Value-guarded offer menus

Since `DCh` has exactly one channel, a stable (τ-free) process node is
determined by a function `(ℕ × Bool) → Maybe continuation`: the **menu** of
accepted *(index , value)* pairs.  All guarded reads (`dd.i?x`), writes
(`dd.i+1!x`), and the guarded-alternative body of `BN` are `menu`s, so one
set of step lemmas (§5.1) covers every stable state of every process here.

```agda
DTree : Set → Set₁
DTree A = PTree DCh (ExtI DCh) A

DProc : Set₁
DProc = DTree (Poly.⊤ {lzero})

Menu : Set → Set₁
Menu A = (ℕ × Bool) → Maybe (DTree A)

menuV : ∀ {A : Set} → Menu A
      → (at : AnyTypes DCh) → ContinueType at (Maybe (DTree A))
menuV f (_ , dd) = f

menu : ∀ {A : Set} → Menu A → DTree A
menu f = pchoice (menuV f)
```

## §4. Process definitions

### §4.1 The `COPY'` cells

`COPY'(i) = dd.i?x → dd.(i+1)!x → COPY'(i)`: a `loop0` whose body is the
guarded read (any value at index `i`) followed by the single-value write
at index `i+1`.

```agda
cellOut : ℕ → Bool → Menu (Poly.⊤ {lzero})   -- dd.(i+1)!x → …
cellOut i x (n , y) with n ℕ≟ suc i
... | no  _ = nothing
... | yes _ with y B≟ x
...   | yes _ = just Skip
...   | no  _ = nothing

cellIn : ℕ → Menu (Poly.⊤ {lzero})           -- dd.i?x → …
cellIn i (n , x) with n ℕ≟ i
... | yes _ = just (menu (cellOut i x))
... | no  _ = nothing

cellbody : ℕ → DTree (Poly.⊤ {lzero})
cellbody i = menu (cellIn i)

COPYcell : ℕ → DProc
COPYcell i = loop0 (cellbody i)
```

### §4.2 The chain, the sync sets, and the hide set

`syncAt k` is the shared channel between adjacent cells: membership is the
propositional index equation `n ≡ k` (value-level, decided by `ℕ≟`).
`hideInternal N` hides all internal indices `1 … N-1`, phrased as the
boolean condition `0 < n ∧ n < N` (so it is a single ℕ-indexed
definition, ready for the ∀`N` generalisation).

```agda
syncAt : ℕ → EventSet
syncAt k .mem (_ , dd) (n , x) = n ≡ k
syncAt k .dec (_ , dd) (n , x) = n ℕ≟ k

hideInternal : ℕ → EventSet
hideInternal N .mem (_ , dd) (n , x) = T ((0 <ᵇ n) ∧ (n <ᵇ N))
hideInternal N .dec (_ , dd) (n , x) with (0 <ᵇ n) ∧ (n <ᵇ N)
... | true  = yes tt
... | false = no (λ z → z)

-- cells k, k+1, …, k+n chained on their shared indices
chainFrom : ℕ → ℕ → DProc
chainFrom k zero    = COPYcell k
chainFrom k (suc n) = COPYcell k ∥⇘ syncAt (suc k) ⇙ chainFrom (suc k) n

BCHAIN : ℕ → DProc          -- N cells (indices 0 … N-1), N ≥ 1
BCHAIN zero    = Stop
BCHAIN (suc n) = chainFrom 0 n

HCHAIN : ℕ → DProc          -- the chain with the internal channels hidden
HCHAIN N = BCHAIN N ∖ hideInternal N
```

At `N = 2` this is `(COPYcell 0 ∥⇘ syncAt 1 ⇙ COPYcell 1) ∖ hideInternal 2`
definitionally — the two-cell chain synchronised on `dd.1`, with `dd.1`
hidden; visible alphabet `{dd.0, dd.2}`.

### §4.3 The buffer specification `BN`

The `N`-place buffer over a `List Bool` state: read `dd (0 , x)` when
`length < N` (append at the back), write `dd (N , head)` when non-empty
(drop the head).  Input is checked first; the two offers can never clash
(indices `0` vs `N`, and only `N ≥ 1` chains are used).

```agda
bn-vis : ℕ → List Bool → Menu (List Bool)
bn-vis N bs (n , x) with n ℕ≟ 0
bn-vis N bs         (n , x) | yes _ =
  if length bs <ᵇ N then just (Ret (bs ∷ʳ x)) else nothing
bn-vis N []         (n , x) | no _ = nothing
bn-vis N (y ∷ rest) (n , x) | no _ with n ℕ≟ N
... | no  _ = nothing
... | yes _ with x B≟ y
...   | yes _ = just (Ret rest)
...   | no  _ = nothing

bn-step : ℕ → List Bool → DTree (List Bool)
bn-step N bs = menu (bn-vis N bs)

BN : ℕ → DProc
BN N = loop (bn-step N) []
```

## §5. Verification

The plan: name the (finitely many) reachable states of both processes,
prove per-state step characterisations (**views**: what every strong step
of that state must be), pair the states up in a relation `Rel`, discharge
the four step-matching obligations and the two non-divergence obligations,
and let the generic `DRFromRel` coinduction principle produce the
divergence-respecting weak bisimulation; `drbisim→≈FD` then yields the
failures-divergences equivalence.

```agda
open import Semantics.LTS       {E = DCh} {I = ExtI DCh} hiding (Diverges)
open import Semantics.WeakBisim {E = DCh} {I = ExtI DCh}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.DRBisim             {E = DCh} {I = ExtI DCh}
  using (Diverges; _≈DR_)
open import Semantics.DRImpliesFD         {E = DCh} {I = ExtI DCh} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = DCh} {I = ExtI DCh} using (_≈FD_)
open import Semantics.BisimFromRel        {E = DCh} {I = ExtI DCh}

open import CSP.Laws.Traces.PrefixInversion DCh-≟
  using (sil-no-ev; sil-τ-uniq; divergesSil)
open import CSP.Laws.Traces.TraceLawsParallel DCh-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim DCh-≟
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR;
         evSync; evL; evR; evBoth; ev√; Par-force-ret-inv)
open import CSP.Laws.Traces.TraceLawsHide DCh-≟
  using (Hide-τ; Hide-keep; Hide-hidden; Hide-τ-elim; Hide-ev-elim;
         HideτR; hτP; hτH; HideevR; heV; he√)
```

### §5.1 Generic step lemmas for menu-shaped loop states

Every *stable* state of every process here is an `mnode f K` — a `menu f`
body remainder inside the loop's `iter-bind`/`>>=` wrappers.  Its offer
map at `dd (n , x)` computes (through `iterV`/`bindV`) to exactly `f (n ,
x)`, and its τ-part is everywhere `nothing`.  Four lemmas capture this
once: firing, non-offer, step inversion, τ-freeness.

```agda
Ev : Set₁
Ev = Event√ (Poly.⊤ {lzero})

lblD : ℕ × Bool → Ev
lblD p = evl (evLabel (ℕ × Bool) dd p)

mnode : ∀ {A : Set} → Menu A → (A → DTree (A ⊎ Poly.⊤ {lzero})) → DProc
mnode f K = iter-bind ((menu f) >>= (λ a′ → Ret (inj₁ a′))) K

menu-offer : ∀ {A : Set} (f : Menu A) (K : A → DTree (A ⊎ Poly.⊤ {lzero}))
               {p : ℕ × Bool} {t : DTree A}
           → f p ≡ just t
           → viewV (PTree.force (mnode f K)) ((ℕ × Bool) , dd) p
             ≡ just (iter-bind (t >>= (λ a′ → Ret (inj₁ a′))) K)
menu-offer f K {p} feq with f p
... | just _  = case feq of λ { refl → refl }
... | nothing = case feq of λ ()

menu-fire : ∀ {A : Set} (f : Menu A) (K : A → DTree (A ⊎ Poly.⊤ {lzero}))
              {p : ℕ × Bool} {t : DTree A}
          → f p ≡ just t
          → mnode f K ─[ ev (lblD p) ]─►
              iter-bind (t >>= (λ a′ → Ret (inj₁ a′))) K
menu-fire f K {p} feq = sVis {at = (ℕ × Bool) , dd} {a = p} refl (menu-offer f K feq)

menu-noffer : ∀ {A : Set} (f : Menu A) (K : A → DTree (A ⊎ Poly.⊤ {lzero}))
                {p : ℕ × Bool}
            → f p ≡ nothing
            → viewV (PTree.force (mnode f K)) ((ℕ × Bool) , dd) p ≡ nothing
menu-noffer f K {p} feq with f p
... | nothing = refl
... | just _  = case feq of λ ()

menu-ev-inv : ∀ {A : Set} (f : Menu A) (K : A → DTree (A ⊎ Poly.⊤ {lzero}))
                {l : Ev} {t′ : DProc}
            → mnode f K ─[ ev l ]─► t′
            → Σ[ p ∈ ℕ × Bool ] Σ[ t ∈ DTree A ]
                ((l ≡ lblD p) × (f p ≡ just t)
                 × (t′ ≡ iter-bind (t >>= (λ a′ → Ret (inj₁ a′))) K))
menu-ev-inv f K (sRet eq) = case eq of λ ()
menu-ev-inv f K (sVis {at = _ , dd} {a = p} refl br) with f p in feq
... | just t  = p , t , refl , feq , sym (just-injective br)
... | nothing = ⊥-elim (case br of λ ())

menu-no-τ : ∀ {A : Set} (f : Menu A) (K : A → DTree (A ⊎ Poly.⊤ {lzero}))
              {t′ : DProc}
          → mnode f K ─[ τ ]─► t′ → ⊥
menu-no-τ f K (sSil eq)      = case eq of λ ()
menu-no-τ f K (sTau refl br) = case br of λ ()
```

### §5.2 The reachable states

Each cell has three states: the loop head `C∘ i` (offering the read
`dd.i?x`), the pending write `C⋆ i x` (offering `dd.(i+1)!x`), and the
silent loop re-entry `C↝ i`.  All are definitional unfoldings of
`COPYcell i`'s successors.

```agda
cellK : ℕ → Poly.⊤ {lzero} → DTree (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
cellK i _ = cellbody i >>= (λ a′ → Ret (inj₁ a′))

C∘ : ℕ → DProc                -- loop head (= COPYcell i)
C∘ i = COPYcell i

C⋆ : ℕ → Bool → DProc         -- holding x: dd.(i+1)!x pending
C⋆ i x = mnode (cellOut i x) (cellK i)

C↝ : ℕ → DProc                -- silent loop re-entry
C↝ i = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) (cellK i)
```

The chain states are `∖`-wrapped parallels of the cell states.  Nine
configurations are reachable; `g1` **is** `HCHAIN 2` (definitionally).
The comments give the buffer contents each represents (oldest first).

```agda
sync1 hid2 : EventSet
sync1 = syncAt 1
hid2  = hideInternal 2

mg⊤ : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})
mg⊤ _ _ = Poly.tt

BPar : DProc → DProc → DProc
BPar l r = Par sync1 mg⊤ l r

HC : DProc → DProc → DProc
HC l r = BPar l r ∖ hid2

g1 g2 g3 g4 : DProc
g1 = HC (C∘ 0) (C∘ 1)                 -- ⟨⟩            (initial = HCHAIN 2)
g2 = HC (C↝ 0) (C∘ 1)                 -- ⟨⟩
g3 = HC (C∘ 0) (C↝ 1)                 -- ⟨⟩
g4 = HC (C↝ 0) (C↝ 1)                 -- ⟨⟩

g5 g6 g7 g8 : Bool → DProc
g5 x = HC (C⋆ 0 x) (C∘ 1)             -- ⟨x⟩  (in cell 0; hand-off pending)
g6 x = HC (C↝ 0) (C⋆ 1 x)             -- ⟨x⟩  (handed to cell 1)
g7 x = HC (C∘ 0) (C⋆ 1 x)             -- ⟨x⟩  (stable: in & out offered)
g8 x = HC (C⋆ 0 x) (C↝ 1)             -- ⟨x⟩

g9 : Bool → Bool → DProc
g9 x y = HC (C⋆ 0 y) (C⋆ 1 x)         -- ⟨x, y⟩ (full; only out offered)
```

The specification has the loop heads `Sat bs` and, one τ before each, the
pre-re-entry states `Sre bs`; `Sat [] = BN 2`.

```agda
bnK : List Bool → DTree (List Bool ⊎ Poly.⊤ {lzero})
bnK bs = bn-step 2 bs >>= (λ a′ → Ret (inj₁ a′))

Sat : List Bool → DProc
Sat bs = loop (bn-step 2) bs

Sre : List Bool → DProc
Sre bs = iter-bind (Ret bs >>= (λ a′ → Ret (inj₁ a′))) bnK
```

### §5.3 Menu equations and membership helpers

The concrete firing equations of the three menus (payload decisions on an
*open* `Bool` need the two-point case split), the guard-set helpers, and
the decode lemmas that read a `just` back off each menu.

```agda
cellIn-eq : ∀ i x → cellIn i (i , x) ≡ just (menu (cellOut i x))
cellIn-eq i x with i ℕ≟ i
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p refl)

cellOut-eq : ∀ i x → cellOut i x (suc i , x) ≡ just Skip
cellOut-eq i x with suc i ℕ≟ suc i
... | no ¬p = ⊥-elim (¬p refl)
... | yes _ with x B≟ x
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

bn-out-eq : ∀ x rest → bn-vis 2 (x ∷ rest) (2 , x) ≡ just (Ret rest)
bn-out-eq true  rest = refl
bn-out-eq false rest = refl

-- hide-set membership at N = 2 pins the index to 1
hid2→1 : ∀ n → T ((0 <ᵇ n) ∧ (n <ᵇ 2)) → n ≡ 1
hid2→1 (suc zero) _ = refl

cellIn-inv : ∀ i n x {t} → cellIn i (n , x) ≡ just t
           → (n ≡ i) × (t ≡ menu (cellOut i x))
cellIn-inv i n x feq with n ℕ≟ i
... | yes q = q , sym (just-injective feq)
... | no  _ = case feq of λ ()

cellOut-inv : ∀ i u n y {t} → cellOut i u (n , y) ≡ just t
            → (n ≡ suc i) × (y ≡ u) × (t ≡ Skip)
cellOut-inv i u n y feq with n ℕ≟ suc i
... | no  _ = case feq of λ ()
... | yes q with y B≟ u
...   | yes q′ = q , q′ , sym (just-injective feq)
...   | no  _  = case feq of λ ()

bn0-inv : ∀ n b {t} → bn-vis 2 [] (n , b) ≡ just t
        → (n ≡ 0) × (t ≡ Ret (b ∷ []))
bn0-inv n b feq with n ℕ≟ 0
... | yes q = q , sym (just-injective feq)
... | no  _ = case feq of λ ()

bn1-inv : ∀ y n b {t} → bn-vis 2 (y ∷ []) (n , b) ≡ just t
        → ((n ≡ 0) × (t ≡ Ret (y ∷ b ∷ [])))
          ⊎ ((n ≡ 2) × (b ≡ y) × (t ≡ Ret []))
bn1-inv y n b feq with n ℕ≟ 0
... | yes q = inj₁ (q , sym (just-injective feq))
... | no  _ with n ℕ≟ 2
...   | no  _ = case feq of λ ()
...   | yes q with b B≟ y
...     | yes q′ = inj₂ (q , q′ , sym (just-injective feq))
...     | no  _  = case feq of λ ()

bn2-inv : ∀ y z n b {t} → bn-vis 2 (y ∷ z ∷ []) (n , b) ≡ just t
        → (n ≡ 2) × (b ≡ y) × (t ≡ Ret (z ∷ []))
bn2-inv y z n b feq with n ℕ≟ 0
... | yes _ = case feq of λ ()
... | no  _ with n ℕ≟ 2
...   | no  _ = case feq of λ ()
...   | yes q with b B≟ y
...     | yes q′ = q , q′ , sym (just-injective feq)
...     | no  _  = case feq of λ ()
```

### §5.4 Concrete strong steps

The specification's steps (all `menu-fire` on computed menu entries plus
the `sil` re-entry) and the chain's steps (component steps lifted through
the parallel intro lemmas, then through hiding: a non-hidden solo event
survives via `Hide-keep`, the synchronised hand-off on `dd.1` becomes a τ
via `Hide-hidden`, component τs propagate via `Hide-τ`).

```agda
sp-in0 : ∀ b → Sat [] ─[ ev (lblD (0 , b)) ]─► Sre (b ∷ [])
sp-in0 b = menu-fire (bn-vis 2 []) bnK {p = 0 , b} refl

sp-in1 : ∀ x b → Sat (x ∷ []) ─[ ev (lblD (0 , b)) ]─► Sre (x ∷ b ∷ [])
sp-in1 x b = menu-fire (bn-vis 2 (x ∷ [])) bnK {p = 0 , b} refl

sp-out1 : ∀ x → Sat (x ∷ []) ─[ ev (lblD (2 , x)) ]─► Sre []
sp-out1 x = menu-fire (bn-vis 2 (x ∷ [])) bnK {p = 2 , x} (bn-out-eq x [])

sp-out2 : ∀ x y → Sat (x ∷ y ∷ []) ─[ ev (lblD (2 , x)) ]─► Sre (y ∷ [])
sp-out2 x y = menu-fire (bn-vis 2 (x ∷ y ∷ [])) bnK {p = 2 , x} (bn-out-eq x (y ∷ []))

sp-τ : ∀ bs → Sre bs ─[ τ ]─► Sat bs
sp-τ bs = sSil refl
```

The chain's visible steps: `dd.0` is left-solo (index `0` is neither
shared nor hidden), `dd.2` right-solo.  The idle operand's non-offer
hypotheses and the (non-)membership proofs all compute.

```agda
inL-g1 : ∀ b → g1 ─[ ev (lblD (0 , b)) ]─► g5 b
inL-g1 b = Hide-keep hid2 (BPar (C∘ 0) (C∘ 1)) (λ z → z)
             (Par-soloL sync1 mg⊤ (C∘ 0) (C∘ 1) (λ ())
               (menu-fire (cellIn 0) (cellK 0) {p = 0 , b} (cellIn-eq 0 b))
               (menu-noffer (cellIn 1) (cellK 1) {p = 0 , b} refl))

inL-g3 : ∀ b → g3 ─[ ev (lblD (0 , b)) ]─► g8 b
inL-g3 b = Hide-keep hid2 (BPar (C∘ 0) (C↝ 1)) (λ z → z)
             (Par-soloL sync1 mg⊤ (C∘ 0) (C↝ 1) (λ ())
               (menu-fire (cellIn 0) (cellK 0) {p = 0 , b} (cellIn-eq 0 b))
               refl)

inL-g7 : ∀ x b → g7 x ─[ ev (lblD (0 , b)) ]─► g9 x b
inL-g7 x b = Hide-keep hid2 (BPar (C∘ 0) (C⋆ 1 x)) (λ z → z)
               (Par-soloL sync1 mg⊤ (C∘ 0) (C⋆ 1 x) (λ ())
                 (menu-fire (cellIn 0) (cellK 0) {p = 0 , b} (cellIn-eq 0 b))
                 (menu-noffer (cellOut 1 x) (cellK 1) {p = 0 , b} refl))

outR-g6 : ∀ x → g6 x ─[ ev (lblD (2 , x)) ]─► g4
outR-g6 x = Hide-keep hid2 (BPar (C↝ 0) (C⋆ 1 x)) (λ z → z)
              (Par-soloR sync1 mg⊤ (C↝ 0) (C⋆ 1 x) (λ ())
                (menu-fire (cellOut 1 x) (cellK 1) {p = 2 , x} (cellOut-eq 1 x))
                refl)

outR-g7 : ∀ x → g7 x ─[ ev (lblD (2 , x)) ]─► g3
outR-g7 x = Hide-keep hid2 (BPar (C∘ 0) (C⋆ 1 x)) (λ z → z)
              (Par-soloR sync1 mg⊤ (C∘ 0) (C⋆ 1 x) (λ ())
                (menu-fire (cellOut 1 x) (cellK 1) {p = 2 , x} (cellOut-eq 1 x))
                (menu-noffer (cellIn 0) (cellK 0) {p = 2 , x} refl))

outR-g9 : ∀ x y → g9 x y ─[ ev (lblD (2 , x)) ]─► g8 y
outR-g9 x y = Hide-keep hid2 (BPar (C⋆ 0 y) (C⋆ 1 x)) (λ z → z)
                (Par-soloR sync1 mg⊤ (C⋆ 0 y) (C⋆ 1 x) (λ ())
                  (menu-fire (cellOut 1 x) (cellK 1) {p = 2 , x} (cellOut-eq 1 x))
                  (menu-noffer (cellOut 0 y) (cellK 0) {p = 2 , x} refl))
```

The chain's τ steps: the loop re-entries of the two cells, and — the crux
of the example — the **hidden hand-off**: the `dd (1 , x)` synchronisation
of the two cells (`Par-sync`, value agreed) is in the hide-set, so
`Hide-hidden` turns it into a τ of `HCHAIN`.

```agda
τ-g2 : g2 ─[ τ ]─► g1
τ-g2 = Hide-τ hid2 (BPar (C↝ 0) (C∘ 1))
         (Par-τ-L sync1 mg⊤ (C↝ 0) (C∘ 1) (sSil refl))

τ-g3 : g3 ─[ τ ]─► g1
τ-g3 = Hide-τ hid2 (BPar (C∘ 0) (C↝ 1))
         (Par-τ-R sync1 mg⊤ (C∘ 0) (C↝ 1) (sSil refl))

τ-g4 : g4 ─[ τ ]─► g3
τ-g4 = Hide-τ hid2 (BPar (C↝ 0) (C↝ 1))
         (Par-τ-L sync1 mg⊤ (C↝ 0) (C↝ 1) (sSil refl))

τ-g5 : ∀ x → g5 x ─[ τ ]─► g6 x               -- the hidden hand-off dd.1
τ-g5 x = Hide-hidden hid2 (BPar (C⋆ 0 x) (C∘ 1)) {a = 1 , x} tt
           (Par-sync sync1 mg⊤ (C⋆ 0 x) (C∘ 1) refl
             (menu-fire (cellOut 0 x) (cellK 0) {p = 1 , x} (cellOut-eq 0 x))
             (menu-fire (cellIn 1) (cellK 1) {p = 1 , x} (cellIn-eq 1 x)))

τ-g6 : ∀ x → g6 x ─[ τ ]─► g7 x
τ-g6 x = Hide-τ hid2 (BPar (C↝ 0) (C⋆ 1 x))
           (Par-τ-L sync1 mg⊤ (C↝ 0) (C⋆ 1 x) (sSil refl))

τ-g8 : ∀ x → g8 x ─[ τ ]─► g5 x
τ-g8 x = Hide-τ hid2 (BPar (C⋆ 0 x) (C↝ 1))
           (Par-τ-R sync1 mg⊤ (C⋆ 0 x) (C↝ 1) (sSil refl))
```

### §5.5 Step views: every strong step of every chain state

For each configuration, a complete characterisation of its strong steps,
obtained by peeling the hiding layer (`Hide-ev-elim`/`Hide-τ-elim`), then
the parallel layer (`Par-ev-elim`/`Par-τ-elim`), then the menu-shaped
component states (§5.1) — refuting the impossible branches by index
arithmetic (a `cellIn 0` step has index `0`, a `cellOut i` step index
`i+1`, the sync/hide sets demand index `1`) or by `sil` inversion.

First the visible views.

```agda
g1-ev : ∀ {l M} → g1 ─[ ev l ]─► M
      → Σ[ b ∈ Bool ] ((l ≡ lblD (0 , b)) × (M ≡ g5 b))
g1-ev stp with Hide-ev-elim hid2 (BPar (C∘ 0) (C∘ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C∘ 0) (C∘ 1) pstp
...   | evSync m _ _ = case m of λ { refl → ⊥-elim (¬c tt) }
...   | evL ¬m lstp with menu-ev-inv (cellIn 0) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl with cellIn-inv 0 n′ b′ feq
...       | refl , refl = b , refl , refl
g1-ev stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evR ¬m rstp with menu-ev-inv (cellIn 1) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl = ⊥-elim (¬m (proj₁ (cellIn-inv 1 n′ b′ feq)))
g1-ev stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evBoth ¬m _ rstp with menu-ev-inv (cellIn 1) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl = ⊥-elim (¬m (proj₁ (cellIn-inv 1 n′ b′ feq)))

g2-no-ev : ∀ {l M} → g2 ─[ ev l ]─► M → ⊥
g2-no-ev stp with Hide-ev-elim hid2 (BPar (C↝ 0) (C∘ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C↝ 0) (C∘ 1) pstp
...   | evSync _ lstp _  = sil-no-ev refl lstp
...   | evL _ lstp       = sil-no-ev refl lstp
...   | evBoth _ lstp _  = sil-no-ev refl lstp
...   | evR ¬m rstp with menu-ev-inv (cellIn 1) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl = ¬m (proj₁ (cellIn-inv 1 n′ b′ feq))

g3-ev : ∀ {l M} → g3 ─[ ev l ]─► M
      → Σ[ b ∈ Bool ] ((l ≡ lblD (0 , b)) × (M ≡ g8 b))
g3-ev stp with Hide-ev-elim hid2 (BPar (C∘ 0) (C↝ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C∘ 0) (C↝ 1) pstp
...   | evSync _ _ rstp = ⊥-elim (sil-no-ev refl rstp)
...   | evR _ rstp      = ⊥-elim (sil-no-ev refl rstp)
...   | evBoth _ _ rstp = ⊥-elim (sil-no-ev refl rstp)
...   | evL ¬m lstp with menu-ev-inv (cellIn 0) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl with cellIn-inv 0 n′ b′ feq
...       | refl , refl = b , refl , refl

g4-no-ev : ∀ {l M} → g4 ─[ ev l ]─► M → ⊥
g4-no-ev stp with Hide-ev-elim hid2 (BPar (C↝ 0) (C↝ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C↝ 0) (C↝ 1) pstp
...   | evSync _ lstp _  = sil-no-ev refl lstp
...   | evL _ lstp       = sil-no-ev refl lstp
...   | evBoth _ lstp _  = sil-no-ev refl lstp
...   | evR _ rstp       = sil-no-ev refl rstp

g5-no-ev : ∀ x {l M} → g5 x ─[ ev l ]─► M → ⊥
g5-no-ev x stp with Hide-ev-elim hid2 (BPar (C⋆ 0 x) (C∘ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C⋆ 0 x) (C∘ 1) pstp
...   | evSync m _ _ = case m of λ { refl → ¬c tt }
...   | evL ¬m lstp with menu-ev-inv (cellOut 0 x) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl = ¬m (proj₁ (cellOut-inv 0 x n′ b′ feq))
g5-no-ev x stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evR ¬m rstp with menu-ev-inv (cellIn 1) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl = ¬m (proj₁ (cellIn-inv 1 n′ b′ feq))
g5-no-ev x stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evBoth ¬m _ rstp with menu-ev-inv (cellIn 1) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl = ¬m (proj₁ (cellIn-inv 1 n′ b′ feq))

g6-ev : ∀ x {l M} → g6 x ─[ ev l ]─► M
      → (l ≡ lblD (2 , x)) × (M ≡ g4)
g6-ev x stp with Hide-ev-elim hid2 (BPar (C↝ 0) (C⋆ 1 x)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C↝ 0) (C⋆ 1 x) pstp
...   | evSync _ lstp _  = ⊥-elim (sil-no-ev refl lstp)
...   | evL _ lstp       = ⊥-elim (sil-no-ev refl lstp)
...   | evBoth _ lstp _  = ⊥-elim (sil-no-ev refl lstp)
...   | evR ¬m rstp with menu-ev-inv (cellOut 1 x) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl with cellOut-inv 1 x n′ b′ feq
...       | refl , refl , refl = refl , refl

g7-ev : ∀ x {l M} → g7 x ─[ ev l ]─► M
      → (Σ[ b ∈ Bool ] ((l ≡ lblD (0 , b)) × (M ≡ g9 x b)))
        ⊎ ((l ≡ lblD (2 , x)) × (M ≡ g3))
g7-ev x stp with Hide-ev-elim hid2 (BPar (C∘ 0) (C⋆ 1 x)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C∘ 0) (C⋆ 1 x) pstp
...   | evSync m _ _ = case m of λ { refl → ⊥-elim (¬c tt) }
...   | evL ¬m lstp with menu-ev-inv (cellIn 0) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl with cellIn-inv 0 n′ b′ feq
...       | refl , refl = inj₁ (b , refl , refl)
g7-ev x stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evR ¬m rstp with menu-ev-inv (cellOut 1 x) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl with cellOut-inv 1 x n′ b′ feq
...       | refl , refl , refl = inj₂ (refl , refl)
g7-ev x stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evBoth _ lstp rstp with menu-ev-inv (cellIn 0) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl with cellIn-inv 0 n′ b′ feq
...       | refl , refl with menu-ev-inv (cellOut 1 x) (cellK 1) rstp
...         | (n₂ , b₂) , t₂ , refl , feq₂ , _ =
              case proj₁ (cellOut-inv 1 x n₂ b₂ feq₂) of λ ()

g8-no-ev : ∀ x {l M} → g8 x ─[ ev l ]─► M → ⊥
g8-no-ev x stp with Hide-ev-elim hid2 (BPar (C⋆ 0 x) (C↝ 1)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C⋆ 0 x) (C↝ 1) pstp
...   | evSync _ _ rstp = sil-no-ev refl rstp
...   | evR _ rstp      = sil-no-ev refl rstp
...   | evBoth _ _ rstp = sil-no-ev refl rstp
...   | evL ¬m lstp with menu-ev-inv (cellOut 0 x) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl = ¬m (proj₁ (cellOut-inv 0 x n′ b′ feq))

g9-ev : ∀ x y {l M} → g9 x y ─[ ev l ]─► M
      → (l ≡ lblD (2 , x)) × (M ≡ g8 y)
g9-ev x y stp with Hide-ev-elim hid2 (BPar (C⋆ 0 y) (C⋆ 1 x)) stp
... | he√ fq = case fq of λ ()
... | heV {e = dd} {a = n , b} P′ ¬c pstp
      with Par-ev-elim sync1 mg⊤ (C⋆ 0 y) (C⋆ 1 x) pstp
...   | evSync m _ _ = case m of λ { refl → ⊥-elim (¬c tt) }
...   | evL ¬m lstp with menu-ev-inv (cellOut 0 y) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl = ⊥-elim (¬m (proj₁ (cellOut-inv 0 y n′ b′ feq)))
g9-ev x y stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evR ¬m rstp with menu-ev-inv (cellOut 1 x) (cellK 1) rstp
...     | (n′ , b′) , t , refl , feq , refl with cellOut-inv 1 x n′ b′ feq
...       | refl , refl , refl = refl , refl
g9-ev x y stp | heV {e = dd} {a = n , b} P′ ¬c pstp
      | evBoth ¬m lstp _ with menu-ev-inv (cellOut 0 y) (cellK 0) lstp
...     | (n′ , b′) , t , refl , feq , refl = ⊥-elim (¬m (proj₁ (cellOut-inv 0 y n′ b′ feq)))
```

Now the τ views.  The three configurations with no τ (`g1`, `g7 x`,
`g9 x y`) are **stable** — every branch of the hiding/parallel τ analysis
is refuted; in particular the hidden-event branch (`hτH`) needs *both*
cells to offer index `1`, which never happens at a stable configuration.
The others each have their τ successor(s) pinned.

```agda
g1-no-τ : ∀ {M} → g1 ─[ τ ]─► M → ⊥
g1-no-τ stp with Hide-τ-elim hid2 (BPar (C∘ 0) (C∘ 1)) stp
... | hτP P′ pstp _ with Par-τ-elim sync1 mg⊤ (C∘ 0) (C∘ 1) pstp
...   | τL _ lstp _ = menu-no-τ (cellIn 0) (cellK 0) lstp
...   | τR _ rstp _ = menu-no-τ (cellIn 1) (cellK 1) rstp
g1-no-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C∘ 0) (C∘ 1) pstp
...     | evSync _ lstp _ with menu-ev-inv (cellIn 0) (cellK 0) lstp
...       | (n′ , b′) , t , refl , feq , refl = case cellIn-inv 0 n′ b′ feq of λ { (() , _) }
g1-no-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evL ¬m _      = ¬m refl
g1-no-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evR ¬m _      = ¬m refl
g1-no-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evBoth ¬m _ _ = ¬m refl

g2-τ : ∀ {M} → g2 ─[ τ ]─► M → M ≡ g1
g2-τ stp with Hide-τ-elim hid2 (BPar (C↝ 0) (C∘ 1)) stp
... | hτP P′ pstp refl with Par-τ-elim sync1 mg⊤ (C↝ 0) (C∘ 1) pstp
...   | τL _ lstp refl with sil-τ-uniq refl lstp
...     | refl = refl
g2-τ stp | hτP P′ pstp refl | τR _ rstp _ =
  ⊥-elim (menu-no-τ (cellIn 1) (cellK 1) rstp)
g2-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C↝ 0) (C∘ 1) pstp
...     | evSync _ lstp _  = ⊥-elim (sil-no-ev refl lstp)
...     | evL ¬m _         = ⊥-elim (¬m refl)
...     | evR ¬m _         = ⊥-elim (¬m refl)
...     | evBoth ¬m _ _    = ⊥-elim (¬m refl)

g3-τ : ∀ {M} → g3 ─[ τ ]─► M → M ≡ g1
g3-τ stp with Hide-τ-elim hid2 (BPar (C∘ 0) (C↝ 1)) stp
... | hτP P′ pstp refl with Par-τ-elim sync1 mg⊤ (C∘ 0) (C↝ 1) pstp
...   | τR _ rstp refl with sil-τ-uniq refl rstp
...     | refl = refl
g3-τ stp | hτP P′ pstp refl | τL _ lstp _ =
  ⊥-elim (menu-no-τ (cellIn 0) (cellK 0) lstp)
g3-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C∘ 0) (C↝ 1) pstp
...     | evSync _ _ rstp  = ⊥-elim (sil-no-ev refl rstp)
...     | evL ¬m _         = ⊥-elim (¬m refl)
...     | evR ¬m _         = ⊥-elim (¬m refl)
...     | evBoth ¬m _ _    = ⊥-elim (¬m refl)

g4-τ : ∀ {M} → g4 ─[ τ ]─► M → (M ≡ g3) ⊎ (M ≡ g2)
g4-τ stp with Hide-τ-elim hid2 (BPar (C↝ 0) (C↝ 1)) stp
... | hτP P′ pstp refl with Par-τ-elim sync1 mg⊤ (C↝ 0) (C↝ 1) pstp
...   | τL _ lstp refl with sil-τ-uniq refl lstp
...     | refl = inj₁ refl
g4-τ stp | hτP P′ pstp refl | τR _ rstp refl with sil-τ-uniq refl rstp
...     | refl = inj₂ refl
g4-τ stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C↝ 0) (C↝ 1) pstp
...     | evSync _ lstp _  = ⊥-elim (sil-no-ev refl lstp)
...     | evL ¬m _         = ⊥-elim (¬m refl)
...     | evR ¬m _         = ⊥-elim (¬m refl)
...     | evBoth ¬m _ _    = ⊥-elim (¬m refl)

g5-τ : ∀ x {M} → g5 x ─[ τ ]─► M → M ≡ g6 x
g5-τ x stp with Hide-τ-elim hid2 (BPar (C⋆ 0 x) (C∘ 1)) stp
... | hτP P′ pstp _ with Par-τ-elim sync1 mg⊤ (C⋆ 0 x) (C∘ 1) pstp
...   | τL _ lstp _ = ⊥-elim (menu-no-τ (cellOut 0 x) (cellK 0) lstp)
...   | τR _ rstp _ = ⊥-elim (menu-no-τ (cellIn 1) (cellK 1) rstp)
g5-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp refl with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C⋆ 0 x) (C∘ 1) pstp
...     | evSync _ lstp rstp with menu-ev-inv (cellOut 0 x) (cellK 0) lstp
...       | (n′ , b′) , t , refl , feq , refl with cellOut-inv 0 x n′ b′ feq
...         | refl , refl , refl with menu-ev-inv (cellIn 1) (cellK 1) rstp
...           | (n₂ , b₂) , t₂ , refl , feq₂ , refl with cellIn-inv 1 n₂ b₂ feq₂
...             | refl , refl = refl
g5-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp refl | refl
      | evL ¬m _      = ⊥-elim (¬m refl)
g5-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp refl | refl
      | evR ¬m _      = ⊥-elim (¬m refl)
g5-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp refl | refl
      | evBoth ¬m _ _ = ⊥-elim (¬m refl)

g6-τ : ∀ x {M} → g6 x ─[ τ ]─► M → M ≡ g7 x
g6-τ x stp with Hide-τ-elim hid2 (BPar (C↝ 0) (C⋆ 1 x)) stp
... | hτP P′ pstp refl with Par-τ-elim sync1 mg⊤ (C↝ 0) (C⋆ 1 x) pstp
...   | τL _ lstp refl with sil-τ-uniq refl lstp
...     | refl = refl
g6-τ x stp | hτP P′ pstp refl | τR _ rstp _ =
  ⊥-elim (menu-no-τ (cellOut 1 x) (cellK 1) rstp)
g6-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C↝ 0) (C⋆ 1 x) pstp
...     | evSync _ lstp _  = ⊥-elim (sil-no-ev refl lstp)
...     | evL ¬m _         = ⊥-elim (¬m refl)
...     | evR ¬m _         = ⊥-elim (¬m refl)
...     | evBoth ¬m _ _    = ⊥-elim (¬m refl)

g7-no-τ : ∀ x {M} → g7 x ─[ τ ]─► M → ⊥
g7-no-τ x stp with Hide-τ-elim hid2 (BPar (C∘ 0) (C⋆ 1 x)) stp
... | hτP P′ pstp _ with Par-τ-elim sync1 mg⊤ (C∘ 0) (C⋆ 1 x) pstp
...   | τL _ lstp _ = menu-no-τ (cellIn 0) (cellK 0) lstp
...   | τR _ rstp _ = menu-no-τ (cellOut 1 x) (cellK 1) rstp
g7-no-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C∘ 0) (C⋆ 1 x) pstp
...     | evSync _ lstp _ with menu-ev-inv (cellIn 0) (cellK 0) lstp
...       | (n′ , b′) , t , refl , feq , refl = case cellIn-inv 0 n′ b′ feq of λ { (() , _) }
g7-no-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evL ¬m _      = ¬m refl
g7-no-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evR ¬m _      = ¬m refl
g7-no-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evBoth ¬m _ _ = ¬m refl

g8-τ : ∀ x {M} → g8 x ─[ τ ]─► M → M ≡ g5 x
g8-τ x stp with Hide-τ-elim hid2 (BPar (C⋆ 0 x) (C↝ 1)) stp
... | hτP P′ pstp refl with Par-τ-elim sync1 mg⊤ (C⋆ 0 x) (C↝ 1) pstp
...   | τR _ rstp refl with sil-τ-uniq refl rstp
...     | refl = refl
g8-τ x stp | hτP P′ pstp refl | τL _ lstp _ =
  ⊥-elim (menu-no-τ (cellOut 0 x) (cellK 0) lstp)
g8-τ x stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C⋆ 0 x) (C↝ 1) pstp
...     | evSync _ _ rstp  = ⊥-elim (sil-no-ev refl rstp)
...     | evL ¬m _         = ⊥-elim (¬m refl)
...     | evR ¬m _         = ⊥-elim (¬m refl)
...     | evBoth ¬m _ _    = ⊥-elim (¬m refl)

g9-no-τ : ∀ x y {M} → g9 x y ─[ τ ]─► M → ⊥
g9-no-τ x y stp with Hide-τ-elim hid2 (BPar (C⋆ 0 y) (C⋆ 1 x)) stp
... | hτP P′ pstp _ with Par-τ-elim sync1 mg⊤ (C⋆ 0 y) (C⋆ 1 x) pstp
...   | τL _ lstp _ = menu-no-τ (cellOut 0 y) (cellK 0) lstp
...   | τR _ rstp _ = menu-no-τ (cellOut 1 x) (cellK 1) rstp
g9-no-τ x y stp | hτH {e = dd} {a = n , b} P′ csat pstp _ with hid2→1 n csat
...   | refl with Par-ev-elim sync1 mg⊤ (C⋆ 0 y) (C⋆ 1 x) pstp
...     | evSync _ _ rstp with menu-ev-inv (cellOut 1 x) (cellK 1) rstp
...       | (n′ , b′) , t , refl , feq , refl =
            case cellOut-inv 1 x n′ b′ feq of λ { (() , _) }
g9-no-τ x y stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evL ¬m _      = ¬m refl
g9-no-τ x y stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evR ¬m _      = ¬m refl
g9-no-τ x y stp | hτH {e = dd} {a = n , b} P′ csat pstp _ | refl
      | evBoth ¬m _ _ = ¬m refl
```

### §5.6 No state diverges

Every chain configuration reaches a stable configuration in at most three
τs (the τ views above pin each successor), so no infinite τ-path exists.
Same for the specification (loop heads are stable, re-entries take one τ).

```agda
¬div-g1 : Diverges g1 → ⊥
¬div-g1 d = g1-no-τ (d .Diverges.step)

¬div-g2 : Diverges g2 → ⊥
¬div-g2 d = ¬div-g1 (subst Diverges (g2-τ (d .Diverges.step)) (d .Diverges.rest))

¬div-g3 : Diverges g3 → ⊥
¬div-g3 d = ¬div-g1 (subst Diverges (g3-τ (d .Diverges.step)) (d .Diverges.rest))

¬div-g4 : Diverges g4 → ⊥
¬div-g4 d with g4-τ (d .Diverges.step)
... | inj₁ eq = ¬div-g3 (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = ¬div-g2 (subst Diverges eq (d .Diverges.rest))

¬div-g7 : ∀ x → Diverges (g7 x) → ⊥
¬div-g7 x d = g7-no-τ x (d .Diverges.step)

¬div-g6 : ∀ x → Diverges (g6 x) → ⊥
¬div-g6 x d = ¬div-g7 x (subst Diverges (g6-τ x (d .Diverges.step)) (d .Diverges.rest))

¬div-g5 : ∀ x → Diverges (g5 x) → ⊥
¬div-g5 x d = ¬div-g6 x (subst Diverges (g5-τ x (d .Diverges.step)) (d .Diverges.rest))

¬div-g8 : ∀ x → Diverges (g8 x) → ⊥
¬div-g8 x d = ¬div-g5 x (subst Diverges (g8-τ x (d .Diverges.step)) (d .Diverges.rest))

¬div-g9 : ∀ x y → Diverges (g9 x y) → ⊥
¬div-g9 x y d = g9-no-τ x y (d .Diverges.step)

¬div-Sat : ∀ bs → Diverges (Sat bs) → ⊥
¬div-Sat bs d = menu-no-τ (bn-vis 2 bs) bnK (d .Diverges.step)

¬div-Sre : ∀ bs → Diverges (Sre bs) → ⊥
¬div-Sre bs d = ¬div-Sat bs (divergesSil refl d)
```

### §5.7 The relation

Each reachable chain configuration is paired with the buffer loop head
holding the same contents.  Three extra pairs (`r1′`, `r7′`, `r9′`) pair
the *stable* canonical configuration of each contents class with the
specification's pre-re-entry state — these are where the chain's weak
answers to the specification's strong steps land.

```agda
data Rel : DProc → DProc → Set₁ where
  r1  : Rel g1 (Sat [])
  r2  : Rel g2 (Sat [])
  r3  : Rel g3 (Sat [])
  r4  : Rel g4 (Sat [])
  r5  : ∀ x → Rel (g5 x) (Sat (x ∷ []))
  r6  : ∀ x → Rel (g6 x) (Sat (x ∷ []))
  r7  : ∀ x → Rel (g7 x) (Sat (x ∷ []))
  r8  : ∀ x → Rel (g8 x) (Sat (x ∷ []))
  r9  : ∀ x y → Rel (g9 x y) (Sat (x ∷ y ∷ []))
  r1′ : Rel g1 (Sre [])
  r7′ : ∀ x → Rel (g7 x) (Sre (x ∷ []))
  r9′ : ∀ x y → Rel (g9 x y) (Sre (x ∷ y ∷ []))
```

### §5.8 The four step-matching obligations

Forward on visibles: the chain's `dd.0`/`dd.2` steps are answered by the
buffer's input/output, folding the loop re-entry τ into the weak answer
(and, from the primed pairs, prepending the re-entry τ).

```agda
R-fwd-ev : ∀ {p q} {l : Ev} {p′} → Rel p q → p ─[ ev l ]─► p′
         → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × Rel p′ q′)
R-fwd-ev r1 stp with g1-ev stp
... | b , refl , refl =
      Sat (b ∷ []) ,
      wev τ*-refl (sp-in0 b) (τ*-step (sp-τ (b ∷ [])) τ*-refl) , r5 b
R-fwd-ev r2 stp = ⊥-elim (g2-no-ev stp)
R-fwd-ev r3 stp with g3-ev stp
... | b , refl , refl =
      Sat (b ∷ []) ,
      wev τ*-refl (sp-in0 b) (τ*-step (sp-τ (b ∷ [])) τ*-refl) , r8 b
R-fwd-ev r4 stp = ⊥-elim (g4-no-ev stp)
R-fwd-ev (r5 x) stp = ⊥-elim (g5-no-ev x stp)
R-fwd-ev (r6 x) stp with g6-ev x stp
... | refl , refl =
      Sat [] , wev τ*-refl (sp-out1 x) (τ*-step (sp-τ []) τ*-refl) , r4
R-fwd-ev (r7 x) stp with g7-ev x stp
... | inj₁ (b , refl , refl) =
      Sat (x ∷ b ∷ []) ,
      wev τ*-refl (sp-in1 x b) (τ*-step (sp-τ (x ∷ b ∷ [])) τ*-refl) , r9 x b
... | inj₂ (refl , refl) =
      Sat [] , wev τ*-refl (sp-out1 x) (τ*-step (sp-τ []) τ*-refl) , r3
R-fwd-ev (r8 x) stp = ⊥-elim (g8-no-ev x stp)
R-fwd-ev (r9 x y) stp with g9-ev x y stp
... | refl , refl =
      Sat (y ∷ []) ,
      wev τ*-refl (sp-out2 x y) (τ*-step (sp-τ (y ∷ [])) τ*-refl) , r8 y
R-fwd-ev r1′ stp with g1-ev stp
... | b , refl , refl =
      Sat (b ∷ []) ,
      wev (τ*-step (sp-τ []) τ*-refl) (sp-in0 b)
          (τ*-step (sp-τ (b ∷ [])) τ*-refl) , r5 b
R-fwd-ev (r7′ x) stp with g7-ev x stp
... | inj₁ (b , refl , refl) =
      Sat (x ∷ b ∷ []) ,
      wev (τ*-step (sp-τ (x ∷ [])) τ*-refl) (sp-in1 x b)
          (τ*-step (sp-τ (x ∷ b ∷ [])) τ*-refl) , r9 x b
... | inj₂ (refl , refl) =
      Sat [] ,
      wev (τ*-step (sp-τ (x ∷ [])) τ*-refl) (sp-out1 x)
          (τ*-step (sp-τ []) τ*-refl) , r3
R-fwd-ev (r9′ x y) stp with g9-ev x y stp
... | refl , refl =
      Sat (y ∷ []) ,
      wev (τ*-step (sp-τ (x ∷ y ∷ [])) τ*-refl) (sp-out2 x y)
          (τ*-step (sp-τ (y ∷ [])) τ*-refl) , r8 y
```

Forward on τ: the buffer answers every chain τ — including the hidden
`dd.1` hand-off (`g5 → g6`) — by **staying put** (`wτ τ*-refl`): the
sequential buffer transfers instantaneously, the weak-step slack absorbs
the chain's internal moves.

```agda
R-fwd-τ : ∀ {p q p′} → Rel p q → p ─[ τ ]─► p′
        → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × Rel p′ q′)
R-fwd-τ r1 stp = ⊥-elim (g1-no-τ stp)
R-fwd-τ r2 stp with g2-τ stp
... | refl = Sat [] , wτ τ*-refl , r1
R-fwd-τ r3 stp with g3-τ stp
... | refl = Sat [] , wτ τ*-refl , r1
R-fwd-τ r4 stp with g4-τ stp
... | inj₁ refl = Sat [] , wτ τ*-refl , r3
... | inj₂ refl = Sat [] , wτ τ*-refl , r2
R-fwd-τ (r5 x) stp with g5-τ x stp
... | refl = Sat (x ∷ []) , wτ τ*-refl , r6 x
R-fwd-τ (r6 x) stp with g6-τ x stp
... | refl = Sat (x ∷ []) , wτ τ*-refl , r7 x
R-fwd-τ (r7 x) stp = ⊥-elim (g7-no-τ x stp)
R-fwd-τ (r8 x) stp with g8-τ x stp
... | refl = Sat (x ∷ []) , wτ τ*-refl , r5 x
R-fwd-τ (r9 x y) stp = ⊥-elim (g9-no-τ x y stp)
R-fwd-τ r1′ stp = ⊥-elim (g1-no-τ stp)
R-fwd-τ (r7′ x) stp = ⊥-elim (g7-no-τ x stp)
R-fwd-τ (r9′ x y) stp = ⊥-elim (g9-no-τ x y stp)
```

Backward on visibles: a buffer input is answered by the chain reading on
`dd.0` and then *silently pumping the value along* (the hidden hand-off
plus re-entries) to the stable configuration `g7`/`g9`; a buffer output is
answered by the chain flushing on `dd.2` and silently re-entering both
loops back to `g1`/`g7`.  The answers land exactly on the primed pairs.

```agda
R-bwd-ev : ∀ {p q} {l : Ev} {q′} → Rel p q → q ─[ ev l ]─► q′
         → Σ[ p′ ∈ DProc ] ((p ═[ ev l ]═► p′) × Rel p′ q′)
R-bwd-ev r1 stp with menu-ev-inv (bn-vis 2 []) bnK stp
... | (n , b) , t , refl , feq , refl with bn0-inv n b feq
...   | refl , refl =
        g7 b ,
        wev τ*-refl (inL-g1 b)
            (τ*-step (τ-g5 b) (τ*-step (τ-g6 b) τ*-refl)) , r7′ b
R-bwd-ev r2 stp with menu-ev-inv (bn-vis 2 []) bnK stp
... | (n , b) , t , refl , feq , refl with bn0-inv n b feq
...   | refl , refl =
        g7 b ,
        wev (τ*-step τ-g2 τ*-refl) (inL-g1 b)
            (τ*-step (τ-g5 b) (τ*-step (τ-g6 b) τ*-refl)) , r7′ b
R-bwd-ev r3 stp with menu-ev-inv (bn-vis 2 []) bnK stp
... | (n , b) , t , refl , feq , refl with bn0-inv n b feq
...   | refl , refl =
        g7 b ,
        wev (τ*-step τ-g3 τ*-refl) (inL-g1 b)
            (τ*-step (τ-g5 b) (τ*-step (τ-g6 b) τ*-refl)) , r7′ b
R-bwd-ev r4 stp with menu-ev-inv (bn-vis 2 []) bnK stp
... | (n , b) , t , refl , feq , refl with bn0-inv n b feq
...   | refl , refl =
        g7 b ,
        wev (τ*-step τ-g4 (τ*-step τ-g3 τ*-refl)) (inL-g1 b)
            (τ*-step (τ-g5 b) (τ*-step (τ-g6 b) τ*-refl)) , r7′ b
R-bwd-ev (r5 x) stp with menu-ev-inv (bn-vis 2 (x ∷ [])) bnK stp
... | (n , b) , t , refl , feq , refl with bn1-inv x n b feq
...   | inj₁ (refl , refl) =
        g9 x b ,
        wev (τ*-step (τ-g5 x) (τ*-step (τ-g6 x) τ*-refl)) (inL-g7 x b)
            τ*-refl , r9′ x b
...   | inj₂ (refl , refl , refl) =
        g1 ,
        wev (τ*-step (τ-g5 x) τ*-refl) (outR-g6 x)
            (τ*-step τ-g4 (τ*-step τ-g3 τ*-refl)) , r1′
R-bwd-ev (r6 x) stp with menu-ev-inv (bn-vis 2 (x ∷ [])) bnK stp
... | (n , b) , t , refl , feq , refl with bn1-inv x n b feq
...   | inj₁ (refl , refl) =
        g9 x b ,
        wev (τ*-step (τ-g6 x) τ*-refl) (inL-g7 x b) τ*-refl , r9′ x b
...   | inj₂ (refl , refl , refl) =
        g1 ,
        wev τ*-refl (outR-g6 x)
            (τ*-step τ-g4 (τ*-step τ-g3 τ*-refl)) , r1′
R-bwd-ev (r7 x) stp with menu-ev-inv (bn-vis 2 (x ∷ [])) bnK stp
... | (n , b) , t , refl , feq , refl with bn1-inv x n b feq
...   | inj₁ (refl , refl) =
        g9 x b , wev τ*-refl (inL-g7 x b) τ*-refl , r9′ x b
...   | inj₂ (refl , refl , refl) =
        g1 , wev τ*-refl (outR-g7 x) (τ*-step τ-g3 τ*-refl) , r1′
R-bwd-ev (r8 x) stp with menu-ev-inv (bn-vis 2 (x ∷ [])) bnK stp
... | (n , b) , t , refl , feq , refl with bn1-inv x n b feq
...   | inj₁ (refl , refl) =
        g9 x b ,
        wev (τ*-step (τ-g8 x) (τ*-step (τ-g5 x) (τ*-step (τ-g6 x) τ*-refl)))
            (inL-g7 x b) τ*-refl , r9′ x b
...   | inj₂ (refl , refl , refl) =
        g1 ,
        wev (τ*-step (τ-g8 x) (τ*-step (τ-g5 x) τ*-refl)) (outR-g6 x)
            (τ*-step τ-g4 (τ*-step τ-g3 τ*-refl)) , r1′
R-bwd-ev (r9 x y) stp with menu-ev-inv (bn-vis 2 (x ∷ y ∷ [])) bnK stp
... | (n , b) , t , refl , feq , refl with bn2-inv x y n b feq
...   | refl , refl , refl =
        g7 y ,
        wev τ*-refl (outR-g9 x y)
            (τ*-step (τ-g8 y) (τ*-step (τ-g5 y) (τ*-step (τ-g6 y) τ*-refl))) ,
        r7′ y
R-bwd-ev r1′ stp = ⊥-elim (sil-no-ev refl stp)
R-bwd-ev (r7′ x) stp = ⊥-elim (sil-no-ev refl stp)
R-bwd-ev (r9′ x y) stp = ⊥-elim (sil-no-ev refl stp)
```

Backward on τ: the buffer's only τs are the loop re-entries (`Sre bs →
Sat bs`); the chain stays put.

```agda
R-bwd-τ : ∀ {p q q′} → Rel p q → q ─[ τ ]─► q′
        → Σ[ p′ ∈ DProc ] ((p ═[ τ ]═► p′) × Rel p′ q′)
R-bwd-τ r1 stp = ⊥-elim (menu-no-τ (bn-vis 2 []) bnK stp)
R-bwd-τ r2 stp = ⊥-elim (menu-no-τ (bn-vis 2 []) bnK stp)
R-bwd-τ r3 stp = ⊥-elim (menu-no-τ (bn-vis 2 []) bnK stp)
R-bwd-τ r4 stp = ⊥-elim (menu-no-τ (bn-vis 2 []) bnK stp)
R-bwd-τ (r5 x) stp = ⊥-elim (menu-no-τ (bn-vis 2 (x ∷ [])) bnK stp)
R-bwd-τ (r6 x) stp = ⊥-elim (menu-no-τ (bn-vis 2 (x ∷ [])) bnK stp)
R-bwd-τ (r7 x) stp = ⊥-elim (menu-no-τ (bn-vis 2 (x ∷ [])) bnK stp)
R-bwd-τ (r8 x) stp = ⊥-elim (menu-no-τ (bn-vis 2 (x ∷ [])) bnK stp)
R-bwd-τ (r9 x y) stp = ⊥-elim (menu-no-τ (bn-vis 2 (x ∷ y ∷ [])) bnK stp)
R-bwd-τ r1′ stp with sil-τ-uniq refl stp
... | refl = g1 , wτ τ*-refl , r1
R-bwd-τ (r7′ x) stp with sil-τ-uniq refl stp
... | refl = g7 x , wτ τ*-refl , r7 x
R-bwd-τ (r9′ x y) stp with sil-τ-uniq refl stp
... | refl = g9 x y , wτ τ*-refl , r9 x y
```

### §5.9 The non-divergence obligations

```agda
R-¬divL : ∀ {p q} → Rel p q → Diverges p → ⊥
R-¬divL r1        = ¬div-g1
R-¬divL r2        = ¬div-g2
R-¬divL r3        = ¬div-g3
R-¬divL r4        = ¬div-g4
R-¬divL (r5 x)    = ¬div-g5 x
R-¬divL (r6 x)    = ¬div-g6 x
R-¬divL (r7 x)    = ¬div-g7 x
R-¬divL (r8 x)    = ¬div-g8 x
R-¬divL (r9 x y)  = ¬div-g9 x y
R-¬divL r1′       = ¬div-g1
R-¬divL (r7′ x)   = ¬div-g7 x
R-¬divL (r9′ x y) = ¬div-g9 x y

R-¬divR : ∀ {p q} → Rel p q → Diverges q → ⊥
R-¬divR r1        = ¬div-Sat []
R-¬divR r2        = ¬div-Sat []
R-¬divR r3        = ¬div-Sat []
R-¬divR r4        = ¬div-Sat []
R-¬divR (r5 x)    = ¬div-Sat (x ∷ [])
R-¬divR (r6 x)    = ¬div-Sat (x ∷ [])
R-¬divR (r7 x)    = ¬div-Sat (x ∷ [])
R-¬divR (r8 x)    = ¬div-Sat (x ∷ [])
R-¬divR (r9 x y)  = ¬div-Sat (x ∷ y ∷ [])
R-¬divR r1′       = ¬div-Sre []
R-¬divR (r7′ x)   = ¬div-Sre (x ∷ [])
R-¬divR (r9′ x y) = ¬div-Sre (x ∷ y ∷ [])
```

### §5.10 The theorem

`DRFromRel` closes the relation into the divergence-respecting weak
bisimulation, and the `drbisim→≈FD` bridge yields the failures-divergences
equivalence — both FDR `[FD=` asserts of the `.csp` source at once.

```agda
module MHB = DRFromRel Rel R-fwd-ev R-fwd-τ R-bwd-ev R-bwd-τ R-¬divL R-¬divR

hchain2≈DR-buffer2 : HCHAIN 2 ≈DR BN 2
hchain2≈DR-buffer2 = MHB.rel→dr r1

hchain2≈FD-buffer2 : HCHAIN 2 ≈FD BN 2
hchain2≈FD-buffer2 = drbisim→≈FD hchain2≈DR-buffer2
```

## §6. Status

Both TPC §3.1 asserts (`BN(<>) [FD= HCHAIN` and `HCHAIN [FD= BN(<>)`) are
discharged at `N = 2`, strengthened to the single equivalence
`hchain2≈FD-buffer2 : HCHAIN 2 ≈FD BN 2` via a divergence-respecting weak
bisimulation.  The two claims specific to *hiding* are both proved, not
assumed: (i) the hidden `dd.1` hand-off is a τ of the chain that the
sequential buffer matches without moving (the `R-fwd-τ` clauses for
`r5`/`r6`), and (ii) hiding introduces **no divergence** — every chain
configuration reaches a stable one in at most three τs (§5.6).  All
definitions (`DCh`, `COPYcell`, `syncAt`, `hideInternal`, `chainFrom`,
`BCHAIN`, `HCHAIN`, `BN`) are ℕ-indexed, ready for the ∀`N`
generalisation.  No postulates, no `NON_TERMINATING`, no `mutual` blocks.

## §7. The ∀N generalisation

The named configurations `g1..g9` of §5 are the `N = 2` instance of a
`3^N`-state family: each cell is in one of three *phases* — the loop head
`p∘`, holding a value `p⋆ x`, or the silent re-entry `p↝` — and a chain
configuration is a length-`N` **vector of phases**.  The §5 proof pattern
(views by peeling Hide, then Par, then the menus) is re-done *once, by
recursion over the vector*; the buffer contents corresponding to a
configuration is computed by a `cts` function (the oldest value is the one
furthest along the chain), giving the coupling invariant

> `HConf ps` is related to the buffer holding `cts ps`.

The hard directions are (i) the **backward** matching — the buffer's
one-step input/output must be answered by the chain *pumping values through
the hidden middle channels* (`freeFront`/`fillBack` below construct those
τ*-sequences), and (ii) **non-divergence** — an explicit measure `msr`
strictly decreases along every chain τ, so hiding introduces no divergence
at any `N`.

### §7.1 Phases, configurations, contents, and the measure

```agda
open import Data.Nat using (_+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using
  (≤-refl; ≤-trans; ≤-antisym; ≤-pred; <⇒≤; <-trans; <-irrefl; <-asym;
   n<1+n; n≤1+n; m≤n⇒m≤1+n; ≮⇒≥; ≤∧≢⇒<; 1+n≢n; <ᵇ⇒<; <⇒<ᵇ; +-monoʳ-<;
   +-identityʳ; +-suc)
open import Data.Vec using (Vec; []; _∷_; replicate)
open import Data.List.Properties using (∷-injective)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; trans; subst₂)

data Ph : Set where
  p∘ : Ph                       -- loop head, offering the read
  p⋆ : Bool → Ph                -- holding a value, write pending
  p↝ : Ph                       -- silent loop re-entry

cst : ℕ → Ph → DProc
cst i p∘     = C∘ i
cst i (p⋆ x) = C⋆ i x
cst i p↝     = C↝ i

-- the sub-chain of cells k, k+1, … in the given phases (split on the
-- LENGTH index so the cons clause reduces with an abstract tail)
chainC : ℕ → ∀ {n} → Vec Ph (suc n) → DProc
chainC k {zero}  (p ∷ []) = cst k p
chainC k {suc m} (p ∷ ps) = Par (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps)

HConf : ∀ {n} → Vec Ph (suc n) → DProc
HConf {n} ps = chainC 0 ps ∖ hideInternal (suc n)

-- buffer contents of a configuration, oldest first (deepest cell = oldest)
cts : ∀ {n} → Vec Ph n → List Bool
cts []          = []
cts (p∘ ∷ ps)   = cts ps
cts (p↝ ∷ ps)   = cts ps
cts (p⋆ x ∷ ps) = cts ps ∷ʳ x

lst : ∀ {n} → Vec Ph (suc n) → Ph
lst {zero}  (p ∷ []) = p
lst {suc m} (p ∷ ps) = lst ps

outv : ∀ {n} → Vec Ph (suc n) → Vec Ph (suc n)   -- flush the last cell
outv {zero}  (p ∷ []) = p↝ ∷ []
outv {suc m} (p ∷ ps) = p ∷ outv ps

-- the τ-measure: a held value weighs more the further it is from the exit
-- (a hidden hand-off moves it one cell closer and pays for the p↝ it leaves
-- behind); a p↝ weighs 1; a p∘ weighs 0.  Every chain τ strictly decreases msr.
wt⋆ : ℕ → ℕ
wt⋆ zero    = 2
wt⋆ (suc r) = suc (suc (wt⋆ r))

wt : ℕ → Ph → ℕ
wt r p∘     = 0
wt r p↝     = 1
wt r (p⋆ _) = wt⋆ r

msr : ∀ {n} → Vec Ph n → ℕ
msr []             = 0
msr (_∷_ {n} p ps) = wt n p + msr ps
```

### §7.2 Arithmetic and boolean-guard helpers

`endIdx k m` is the output index of the sub-chain of cells `k … k+m`
(defined by recursion so the cons case is definitional), and the `hid*`
helpers convert between the boolean hide-set guard and `_<_`.

```agda
endIdx : ℕ → ℕ → ℕ
endIdx k zero    = suc k
endIdx k (suc m) = endIdx (suc k) m

k<endIdx : ∀ k m → k < endIdx k m
k<endIdx k zero    = n<1+n k
k<endIdx k (suc m) = <-trans (n<1+n k) (k<endIdx (suc k) m)

endIdx≡ : ∀ k m → endIdx k m ≡ suc (k + m)
endIdx≡ k zero    = cong suc (sym (+-identityʳ k))
endIdx≡ k (suc m) = trans (endIdx≡ (suc k) m) (cong suc (sym (+-suc k m)))

<⇒≢ʳ : ∀ {a b} → a < b → b ≢ a
<⇒≢ʳ lt eq = <-irrefl (sym eq) lt

<⇒≢ : ∀ {a b} → a < b → a ≢ b
<⇒≢ lt eq = <-irrefl eq lt

k≢1+k : ∀ k → k ≢ suc k
k≢1+k k eq = 1+n≢n (sym eq)

T∧ : ∀ x y → T x → T y → T (x ∧ y)
T∧ true  true  _  _  = tt
T∧ true  false _  ()
T∧ false _     () _

T∧₁ : ∀ x y → T (x ∧ y) → T x
T∧₁ true  _ _ = tt
T∧₁ false _ ()

T∧₂ : ∀ x y → T (x ∧ y) → T y
T∧₂ true  true  _ = tt
T∧₂ true  false ()
T∧₂ false _     ()

hidMem : ∀ N j → 0 < j → j < N → T ((0 <ᵇ j) ∧ (j <ᵇ N))
hidMem N j lo hi = T∧ (0 <ᵇ j) (j <ᵇ N) (<⇒<ᵇ lo) (<⇒<ᵇ hi)

hidLo : ∀ N j → T ((0 <ᵇ j) ∧ (j <ᵇ N)) → 0 < j
hidLo N j m = <ᵇ⇒< 0 j (T∧₁ (0 <ᵇ j) (j <ᵇ N) m)

hidHi : ∀ N j → T ((0 <ᵇ j) ∧ (j <ᵇ N)) → j < N
hidHi N j m = <ᵇ⇒< j N (T∧₂ (0 <ᵇ j) (j <ᵇ N) m)

len-∷ʳ : ∀ (xs : List Bool) (x : Bool) → length (xs ∷ʳ x) ≡ suc (length xs)
len-∷ʳ []       x = refl
len-∷ʳ (y ∷ xs) x = cong suc (len-∷ʳ xs x)

len-cts : ∀ {n} (ps : Vec Ph n) → length (cts ps) ≤ n
len-cts []          = z≤n
len-cts (p∘ ∷ ps)   = m≤n⇒m≤1+n (len-cts ps)
len-cts (p↝ ∷ ps)   = m≤n⇒m≤1+n (len-cts ps)
len-cts (p⋆ x ∷ ps) = subst (_≤ suc _) (sym (len-∷ʳ (cts ps) x)) (s≤s (len-cts ps))
```

### §7.3 Cell-level step lemmas at open indices

The §5.3 menu equations were used at concrete indices; here every index is
open, so the non-offer sides need the `≢`-guarded variants, and the cell's
complete step characterisations (`cst-ev-inv`/`cst-τ-inv`) are stated per
phase.

```agda
cellIn-nof : ∀ i j b → j ≢ i → cellIn i (j , b) ≡ nothing
cellIn-nof i j b ne with j ℕ≟ i
... | yes q = ⊥-elim (ne q)
... | no  _ = refl

cellOut-nof : ∀ i x j b → j ≢ suc i → cellOut i x (j , b) ≡ nothing
cellOut-nof i x j b ne with j ℕ≟ suc i
... | yes q = ⊥-elim (ne q)
... | no  _ = refl

cst-no-ret : ∀ i p {r} → PTree.force (cst i p) ≡ ret r → ⊥
cst-no-ret i p∘     eq = case eq of λ ()
cst-no-ret i (p⋆ x) eq = case eq of λ ()
cst-no-ret i p↝     eq = case eq of λ ()

cst-noffer : ∀ i p j b → j ≢ i → j ≢ suc i
           → viewV (PTree.force (cst i p)) ((ℕ × Bool) , dd) (j , b) ≡ nothing
cst-noffer i p∘     j b ne _  = menu-noffer (cellIn i)    (cellK i) {p = j , b} (cellIn-nof i j b ne)
cst-noffer i (p⋆ x) j b _  ne = menu-noffer (cellOut i x) (cellK i) {p = j , b} (cellOut-nof i x j b ne)
cst-noffer i p↝     j b _  _  = refl

cst-ev-inv : ∀ i p {l : Ev} {M} → cst i p ─[ ev l ]─► M
           → (Σ[ b ∈ Bool ] ((p ≡ p∘) × (l ≡ lblD (i , b)) × (M ≡ C⋆ i b)))
           ⊎ (Σ[ x ∈ Bool ] ((p ≡ p⋆ x) × (l ≡ lblD (suc i , x)) × (M ≡ C↝ i)))
cst-ev-inv i p∘ stp with menu-ev-inv (cellIn i) (cellK i) stp
... | (j , b) , t , refl , feq , refl with cellIn-inv i j b feq
...   | refl , refl = inj₁ (b , refl , refl , refl)
cst-ev-inv i (p⋆ x) stp with menu-ev-inv (cellOut i x) (cellK i) stp
... | (j , b) , t , refl , feq , refl with cellOut-inv i x j b feq
...   | refl , refl , refl = inj₂ (x , refl , refl , refl)
cst-ev-inv i p↝ stp = ⊥-elim (sil-no-ev refl stp)

cst-τ-inv : ∀ i p {M} → cst i p ─[ τ ]─► M → (p ≡ p↝) × (M ≡ C∘ i)
cst-τ-inv i p∘     stp = ⊥-elim (menu-no-τ (cellIn i)    (cellK i) stp)
cst-τ-inv i (p⋆ x) stp = ⊥-elim (menu-no-τ (cellOut i x) (cellK i) stp)
cst-τ-inv i p↝     stp = refl , sil-τ-uniq refl stp
```

### §7.4 The buffer specification at open `N`

`SatN`/`SreN` generalise §5.2's `Sat`/`Sre`; the firing equations now carry
the guards as hypotheses (`T (length bs <ᵇ N)` for input, a `suc`-shaped
`N` for output), and the inversion `bn-invN` decodes a step of `BN (suc n)`
into the input or output case.

```agda
bnKN : ℕ → List Bool → DTree (List Bool ⊎ Poly.⊤ {lzero})
bnKN N bs = bn-step N bs >>= (λ a′ → Ret (inj₁ a′))

SatN : ℕ → List Bool → DProc
SatN N bs = loop (bn-step N) bs

SreN : ℕ → List Bool → DProc
SreN N bs = iter-bind (Ret bs >>= (λ a′ → Ret (inj₁ a′))) (bnKN N)

bn-in-eq : ∀ N bs b → T (length bs <ᵇ N) → bn-vis N bs (0 , b) ≡ just (Ret (bs ∷ʳ b))
bn-in-eq N bs b g with length bs <ᵇ N
... | true  = refl
... | false = ⊥-elim g

bn-out-eq′ : ∀ N h rest → bn-vis (suc N) (h ∷ rest) (suc N , h) ≡ just (Ret rest)
bn-out-eq′ N h rest with suc N ℕ≟ suc N
... | no ¬p = ⊥-elim (¬p refl)
... | yes _ with h B≟ h
...   | yes _ = refl
...   | no ¬p = ⊥-elim (¬p refl)

bn-invN : ∀ N bs j b {t} → bn-vis (suc N) bs (j , b) ≡ just t
        → ((j ≡ 0) × T (length bs <ᵇ suc N) × (t ≡ Ret (bs ∷ʳ b)))
        ⊎ (Σ[ rest ∈ List Bool ] ((bs ≡ b ∷ rest) × (j ≡ suc N) × (t ≡ Ret rest)))
bn-invN N bs j b feq with j ℕ≟ 0
bn-invN N bs j b feq | yes q with length bs <ᵇ suc N
... | true  = inj₁ (q , tt , sym (just-injective feq))
... | false = case feq of λ ()
bn-invN N []         j b feq | no _ = case feq of λ ()
bn-invN N (y ∷ rest) j b feq | no _ with j ℕ≟ suc N
... | no _ = case feq of λ ()
... | yes q with b B≟ y
...   | yes q′ = inj₂ (rest , cong (_∷ rest) (sym q′) , q , sym (just-injective feq))
...   | no  _  = case feq of λ ()

bn-vis0-nof : ∀ j b {t} → bn-vis 0 [] (j , b) ≡ just t → ⊥
bn-vis0-nof j b feq with j ℕ≟ 0
... | yes _ = case feq of λ ()
... | no  _ = case feq of λ ()

sp-inN : ∀ N bs b → T (length bs <ᵇ N)
       → SatN N bs ─[ ev (lblD (0 , b)) ]─► SreN N (bs ∷ʳ b)
sp-inN N bs b g = menu-fire (bn-vis N bs) (bnKN N) {p = 0 , b} (bn-in-eq N bs b g)

sp-outN : ∀ N h rest → SatN (suc N) (h ∷ rest) ─[ ev (lblD (suc N , h)) ]─► SreN (suc N) rest
sp-outN N h rest = menu-fire (bn-vis (suc N) (h ∷ rest)) (bnKN (suc N)) {p = suc N , h}
                             (bn-out-eq′ N h rest)

sp-τN : ∀ N bs → SreN N bs ─[ τ ]─► SatN N bs
sp-τN N bs = sSil refl

¬div-SatN : ∀ N bs → Diverges (SatN N bs) → ⊥
¬div-SatN N bs d = menu-no-τ (bn-vis N bs) (bnKN N) (d .Diverges.step)

¬div-SreN : ∀ N bs → Diverges (SreN N bs) → ⊥
¬div-SreN N bs d = ¬div-SatN N bs (divergesSil refl d)
```

### §7.5 Non-offer propagation through the parallel

`Par-noffer` (generic): if neither operand offers an event, the composite
does not offer it; `cc-noffer-lo` instantiates it along the chain — a
sub-chain of cells `k, k+1, …` offers only indices `≥ k`, so any index
`< k` is refused.  This feeds `Par-soloL/R`'s idle-side hypotheses.

```agda
Par-noffer : (A : EventSet) (P Q : DProc) {at : AnyTypes DCh} {a : proj₁ at}
           → viewV (PTree.force P) at a ≡ nothing
           → viewV (PTree.force Q) at a ≡ nothing
           → viewV (PTree.force (Par A mg⊤ P Q)) at a ≡ nothing
Par-noffer A P Q {at} {a} nP nQ with PTree.force P | PTree.force Q
... | ret _ | ret _ = refl
... | ret _ | sil _ = refl
... | sil _ | ret _ = refl
... | ret _ | react vQ τcQ with A .dec at a
...   | yes _ = refl
...   | no _ with vQ at a | nQ
...     | nothing | _  = refl
...     | just _  | ()
Par-noffer A P Q {at} {a} nP nQ | react vP τcP | ret _ with A .dec at a
...   | yes _ = refl
...   | no _ with vP at a | nP
...     | nothing | _  = refl
...     | just _  | ()
Par-noffer A P Q {at} {a} nP nQ | sil _ | sil _ with A .dec at a
...   | yes _ = refl
...   | no  _ = refl
Par-noffer A P Q {at} {a} nP nQ | sil _ | react vQ τcQ
  with A .dec at a | vQ at a | nQ
...   | yes _ | nothing | _  = refl
...   | no  _ | nothing | _  = refl
...   | _     | just _  | ()
Par-noffer A P Q {at} {a} nP nQ | react vP τcP | sil _
  with A .dec at a | vP at a | nP
...   | yes _ | nothing | _  = refl
...   | no  _ | nothing | _  = refl
...   | _     | just _  | ()
Par-noffer A P Q {at} {a} nP nQ | react vP τcP | react vQ τcQ
  with A .dec at a | vP at a | vQ at a | nP | nQ
...   | yes _ | nothing | _       | _  | _  = refl
...   | no  _ | nothing | nothing | _  | _  = refl
...   | _     | just _  | _       | () | _
...   | no  _ | nothing | just _  | _  | ()

cc-noffer-lo : ∀ k {n} (ps : Vec Ph (suc n)) j b → j < k
             → viewV (PTree.force (chainC k ps)) ((ℕ × Bool) , dd) (j , b) ≡ nothing
cc-noffer-lo k {zero} (p ∷ []) j b lt =
  cst-noffer k p j b (<⇒≢ lt) (<⇒≢ (<-trans lt (n<1+n k)))
cc-noffer-lo k {suc m} (p ∷ ps) j b lt =
  Par-noffer (syncAt (suc k)) (cst k p) (chainC (suc k) ps)
    (cst-noffer k p j b (<⇒≢ lt) (<⇒≢ (<-trans lt (n<1+n k))))
    (cc-noffer-lo (suc k) ps j b (<-trans lt (n<1+n k)))
```

### §7.6 Chain step INTRO lemmas

The four ways a chain configuration moves: the front cell reads (`cc-in`,
solo left), a cell re-enters its loop (`cc-reτ`/`cc-tailτ`), adjacent cells
hand a value across their shared index (`cc-hand`, a `Par-sync` between the
head's write and the sub-chain's front read), and the last cell writes
(`cc-out`, solo right all the way down).

```agda
cc-in : ∀ k {n} (ps : Vec Ph n) b
      → chainC k (p∘ ∷ ps) ─[ ev (lblD (k , b)) ]─► chainC k (p⋆ b ∷ ps)
cc-in k []          b = menu-fire (cellIn k) (cellK k) {p = k , b} (cellIn-eq k b)
cc-in k {suc m} ps  b =
  Par-soloL (syncAt (suc k)) mg⊤ (C∘ k) (chainC (suc k) ps) (k≢1+k k)
    (menu-fire (cellIn k) (cellK k) {p = k , b} (cellIn-eq k b))
    (cc-noffer-lo (suc k) ps k b (n<1+n k))

cc-reτ : ∀ k {n} (ps : Vec Ph n)
       → chainC k (p↝ ∷ ps) ─[ τ ]─► chainC k (p∘ ∷ ps)
cc-reτ k []         = sSil refl
cc-reτ k {suc m} ps = Par-τ-L (syncAt (suc k)) mg⊤ (C↝ k) (chainC (suc k) ps) (sSil refl)

cc-tailτ : ∀ k p {n} (ps : Vec Ph (suc n)) {qs : Vec Ph (suc n)}
         → chainC (suc k) ps ─[ τ ]─► chainC (suc k) qs
         → chainC k (p ∷ ps) ─[ τ ]─► chainC k (p ∷ qs)
cc-tailτ k p ps stp = Par-τ-R (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps) stp

cc-hand : ∀ k {m} (ps : Vec Ph m) x
        → chainC k (p⋆ x ∷ p∘ ∷ ps) ─[ ev (lblD (suc k , x)) ]─► chainC k (p↝ ∷ p⋆ x ∷ ps)
cc-hand k ps x =
  Par-sync (syncAt (suc k)) mg⊤ (C⋆ k x) (chainC (suc k) (p∘ ∷ ps)) refl
    (menu-fire (cellOut k x) (cellK k) {p = suc k , x} (cellOut-eq k x))
    (cc-in (suc k) ps x)

cc-out : ∀ k {n} (ps : Vec Ph (suc n)) {x} → lst ps ≡ p⋆ x
       → chainC k ps ─[ ev (lblD (endIdx k n , x)) ]─► chainC k (outv ps)
cc-out k {zero} (p⋆ y ∷ []) refl =
  menu-fire (cellOut k y) (cellK k) {p = suc k , y} (cellOut-eq k y)
cc-out k {suc m} (p ∷ ps) {x} e =
  Par-soloR (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps)
    (<⇒≢ʳ (k<endIdx (suc k) m))
    (cc-out (suc k) ps e)
    (cst-noffer k p (endIdx (suc k) m) x
      (<⇒≢ʳ (<-trans (n<1+n k) (k<endIdx (suc k) m)))
      (<⇒≢ʳ (k<endIdx (suc k) m)))

cts-outv : ∀ {n} (ps : Vec Ph (suc n)) {x} → lst ps ≡ p⋆ x
         → cts ps ≡ x ∷ cts (outv ps)
cts-outv {zero}  (p⋆ y ∷ []) refl = refl
cts-outv {suc m} (p∘ ∷ ps)   e = cts-outv ps e
cts-outv {suc m} (p↝ ∷ ps)   e = cts-outv ps e
cts-outv {suc m} (p⋆ y ∷ ps) e = cong (_∷ʳ y) (cts-outv ps e)
```

### §7.7 Chain step ELIM: the `CCStep`/`CCτ` characterisations

Every strong step of `chainC k ps` is one of four vector rewrites, proved
by recursion over the vector through `Par-ev-elim`/`Par-τ-elim`; the
impossible branches die on index arithmetic (a sub-chain of cells `≥ k+1`
never touches index `≤ k`, sync forces index `k+1`, …).

```agda
data CCStep : ℕ → ∀ {n} → Vec Ph (suc n) → ℕ × Bool → Vec Ph (suc n) → Set where
  csIn   : ∀ {k n} {ps : Vec Ph n} b
         → CCStep k (p∘ ∷ ps) (k , b) (p⋆ b ∷ ps)
  csOut1 : ∀ {k} x
         → CCStep k (p⋆ x ∷ []) (suc k , x) (p↝ ∷ [])
  csHand : ∀ {k m} {ps : Vec Ph m} x
         → CCStep k (p⋆ x ∷ p∘ ∷ ps) (suc k , x) (p↝ ∷ p⋆ x ∷ ps)
  csTail : ∀ {k m} {ps qs : Vec Ph (suc m)} {j b p}
         → suc k < j → CCStep (suc k) ps (j , b) qs
         → CCStep k (p ∷ ps) (j , b) (p ∷ qs)

data CCτ : ℕ → ∀ {n} → Vec Ph (suc n) → Vec Ph (suc n) → Set where
  cτRe   : ∀ {k n} {ps : Vec Ph n} → CCτ k (p↝ ∷ ps) (p∘ ∷ ps)
  cτTail : ∀ {k m} {ps qs : Vec Ph (suc m)} {p}
         → CCτ (suc k) ps qs → CCτ k (p ∷ ps) (p ∷ qs)

ccstep-lb : ∀ {k n} {ps qs : Vec Ph (suc n)} {j b} → CCStep k ps (j , b) qs → k ≤ j
ccstep-lb (csIn b)      = ≤-refl
ccstep-lb (csOut1 x)    = n≤1+n _
ccstep-lb (csHand x)    = n≤1+n _
ccstep-lb (csTail lt c) = <⇒≤ (<-trans (n<1+n _) lt)

ccstep-ub : ∀ {k n} {ps qs : Vec Ph (suc n)} {j b} → CCStep k ps (j , b) qs → j ≤ endIdx k n
ccstep-ub {k} {n} (csIn b)   = <⇒≤ (k<endIdx k n)
ccstep-ub (csOut1 x)         = ≤-refl
ccstep-ub (csHand {k} {m} x) = <⇒≤ (k<endIdx (suc k) m)
ccstep-ub (csTail lt c)      = ccstep-ub c

-- an INTERNAL step (index strictly between the ends) is a hand-off:
-- contents preserved, measure strictly decreased
cts-int : ∀ {k n} {ps qs : Vec Ph (suc n)} {j b}
        → CCStep k ps (j , b) qs → k < j → j < endIdx k n → cts qs ≡ cts ps
cts-int (csIn b)   lo hi = ⊥-elim (<-irrefl refl lo)
cts-int (csOut1 x) lo hi = ⊥-elim (<-irrefl refl hi)
cts-int (csHand x) lo hi = refl
cts-int (csTail {p = p∘}   lt c) lo hi = cts-int c lt hi
cts-int (csTail {p = p↝}   lt c) lo hi = cts-int c lt hi
cts-int (csTail {p = p⋆ y} lt c) lo hi = cong (_∷ʳ y) (cts-int c lt hi)

msr-int : ∀ {k n} {ps qs : Vec Ph (suc n)} {j b}
        → CCStep k ps (j , b) qs → k < j → j < endIdx k n → msr qs < msr ps
msr-int (csIn b)   lo hi = ⊥-elim (<-irrefl refl lo)
msr-int (csOut1 x) lo hi = ⊥-elim (<-irrefl refl hi)
msr-int (csHand x) lo hi = ≤-refl
msr-int (csTail {p = p} lt c) lo hi = +-monoʳ-< (wt _ p) (msr-int c lt hi)

-- an END step (index = the chain's output index) flushes the OLDEST value
cts-end : ∀ {k n} {ps qs : Vec Ph (suc n)} {j b}
        → CCStep k ps (j , b) qs → j ≡ endIdx k n → cts ps ≡ b ∷ cts qs
cts-end {k} {n} (csIn b) eq = ⊥-elim (<-irrefl eq (k<endIdx k n))
cts-end (csOut1 x)       eq = refl
cts-end (csHand {k} {m} x) eq = ⊥-elim (<-irrefl eq (k<endIdx (suc k) m))
cts-end (csTail {p = p∘}   lt c) eq = cts-end c eq
cts-end (csTail {p = p↝}   lt c) eq = cts-end c eq
cts-end (csTail {p = p⋆ y} lt c) eq = cong (_∷ʳ y) (cts-end c eq)

-- τ preserves contents and strictly decreases the measure
cts-ccτ : ∀ {k n} {ps qs : Vec Ph (suc n)} → CCτ k ps qs → cts qs ≡ cts ps
cts-ccτ cτRe                 = refl
cts-ccτ (cτTail {p = p∘}   c) = cts-ccτ c
cts-ccτ (cτTail {p = p↝}   c) = cts-ccτ c
cts-ccτ (cτTail {p = p⋆ y} c) = cong (_∷ʳ y) (cts-ccτ c)

msr-ccτ : ∀ {k n} {ps qs : Vec Ph (suc n)} → CCτ k ps qs → msr qs < msr ps
msr-ccτ (cτRe {ps = ps})   = n<1+n (msr ps)
msr-ccτ (cτTail {p = p} c) = +-monoʳ-< (wt _ p) (msr-ccτ c)

cc-no-ret : ∀ k {n} (ps : Vec Ph (suc n)) {r} → PTree.force (chainC k ps) ≡ ret r → ⊥
cc-no-ret k {zero}  (p ∷ []) eq = cst-no-ret k p eq
cc-no-ret k {suc m} (p ∷ ps) eq with Par-force-ret-inv (syncAt (suc k)) mg⊤ eq
... | r₁ , r₂ , eqP , _ , _ = cst-no-ret k p eqP

cc-ev-inv : ∀ k {n} (ps : Vec Ph (suc n)) {l : Ev} {M} → chainC k ps ─[ ev l ]─► M
          → Σ[ jb ∈ ℕ × Bool ] Σ[ qs ∈ Vec Ph (suc n) ]
              ((l ≡ lblD jb) × (M ≡ chainC k qs) × CCStep k ps jb qs)
cc-ev-inv k {zero} (p ∷ []) stp with cst-ev-inv k p stp
... | inj₁ (b , refl , refl , refl) = (k , b) , (p⋆ b ∷ []) , refl , refl , csIn b
... | inj₂ (x , refl , refl , refl) = (suc k , x) , (p↝ ∷ []) , refl , refl , csOut1 x
cc-ev-inv k {suc m} (p ∷ ps) stp
  with Par-ev-elim (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps) stp
... | ev√ fpP _ = ⊥-elim (cst-no-ret k p fpP)
... | evSync {e = dd} {a = j , b} mm lstp rstp with cst-ev-inv k p lstp
...   | inj₁ (b′ , refl , refl , refl) = ⊥-elim (k≢1+k k mm)
...   | inj₂ (x , refl , refl , refl) with cc-ev-inv (suc k) ps rstp
...     | (j₂ , b₂) , qs′ , refl , refl , csIn {ps = ps₁} b₃ =
          (suc k , x) , (p↝ ∷ p⋆ x ∷ ps₁) , refl , refl , csHand x
...     | (j₂ , b₂) , qs′ , refl , refl , csTail lt c₃ =
          ⊥-elim (<-asym lt (n<1+n (suc k)))
cc-ev-inv k {suc m} (p ∷ ps) stp
    | evL {e = dd} {a = j , b} ¬mm lstp with cst-ev-inv k p lstp
...   | inj₁ (b′ , refl , refl , refl) =
        (k , b′) , (p⋆ b′ ∷ ps) , refl , refl , csIn b′
...   | inj₂ (x , refl , refl , refl) = ⊥-elim (¬mm refl)
cc-ev-inv k {suc m} (p ∷ ps) stp
    | evR {e = dd} {a = j , b} ¬mm rstp with cc-ev-inv (suc k) ps rstp
...   | (j₂ , b₂) , qs′ , refl , refl , c₂ =
        (j₂ , b₂) , (p ∷ qs′) , refl , refl ,
        csTail (≤∧≢⇒< (ccstep-lb c₂) (λ eq → ¬mm (sym eq))) c₂
cc-ev-inv k {suc m} (p ∷ ps) stp
    | evBoth {e = dd} {a = j , b} ¬mm lstp rstp with cst-ev-inv k p lstp
...   | inj₂ (x , refl , refl , refl) = ⊥-elim (¬mm refl)
...   | inj₁ (b′ , refl , refl , refl) with cc-ev-inv (suc k) ps rstp
...     | (j₂ , b₂) , qs′ , refl , _ , c₂ = ⊥-elim (<-irrefl refl (ccstep-lb c₂))

cc-τ-inv : ∀ k {n} (ps : Vec Ph (suc n)) {M} → chainC k ps ─[ τ ]─► M
         → Σ[ qs ∈ Vec Ph (suc n) ] ((M ≡ chainC k qs) × CCτ k ps qs)
cc-τ-inv k {zero} (p ∷ []) stp with cst-τ-inv k p stp
... | refl , refl = (p∘ ∷ []) , refl , cτRe
cc-τ-inv k {suc m} (p ∷ ps) stp
  with Par-τ-elim (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps) stp
... | τL P′ lstp meq with cst-τ-inv k p lstp
...   | refl , refl = (p∘ ∷ ps) , meq , cτRe
cc-τ-inv k {suc m} (p ∷ ps) stp
    | τR Q′ rstp meq with cc-τ-inv (suc k) ps rstp
...   | qs′ , refl , c′ = (p ∷ qs′) , meq , cτTail c′
```

### §7.8 Internal step sequences and the pumping lemmas

An `ISeq` is a sequence of chain steps that are all invisible after hiding:
τs, or events whose index lies strictly between the sub-chain's ends (so at
the top level they are in `hideInternal`).  `iseq-lift` embeds a sub-chain's
sequence into a longer chain (τ via `Par-τ-R`, internal events via
`Par-soloR` — the head cell never offers indices `> k+1`), and `iseq-τ*`
converts a top-level sequence into a `τ*` of `HConf` (`Hide-τ`/`Hide-hidden`).

```agda
data ISeq (k : ℕ) {n : ℕ} : Vec Ph (suc n) → Vec Ph (suc n) → Set₁ where
  inil : ∀ {ps} → ISeq k ps ps
  iτ   : ∀ {ps rs} (qs : Vec Ph (suc n))
       → chainC k ps ─[ τ ]─► chainC k qs
       → ISeq k qs rs → ISeq k ps rs
  iev  : ∀ {ps rs} (qs : Vec Ph (suc n)) j b → k < j → j < endIdx k n
       → chainC k ps ─[ ev (lblD (j , b)) ]─► chainC k qs
       → ISeq k qs rs → ISeq k ps rs

iseq-++ : ∀ {k n} {ps qs rs : Vec Ph (suc n)}
        → ISeq k ps qs → ISeq k qs rs → ISeq k ps rs
iseq-++ inil                    s₂ = s₂
iseq-++ (iτ qs st s)            s₂ = iτ qs st (iseq-++ s s₂)
iseq-++ (iev qs j b lo hi st s) s₂ = iev qs j b lo hi st (iseq-++ s s₂)

iseq-lift : ∀ {k n} (p : Ph) {ps qs : Vec Ph (suc n)}
          → ISeq (suc k) ps qs → ISeq k (p ∷ ps) (p ∷ qs)
iseq-lift     p inil = inil
iseq-lift {k} p (iτ {ps = ps₀} qs st s) =
  iτ (p ∷ qs) (cc-tailτ k p ps₀ st) (iseq-lift p s)
iseq-lift {k} p (iev {ps = ps₀} qs j b lo hi st s) =
  iev (p ∷ qs) j b (<-trans (n<1+n k) lo) hi
      (Par-soloR (syncAt (suc k)) mg⊤ (cst k p) (chainC (suc k) ps₀)
        (<⇒≢ʳ lo) st
        (cst-noffer k p j b (<⇒≢ʳ (<-trans (n<1+n k) lo)) (<⇒≢ʳ lo)))
      (iseq-lift p s)

iseq-τ* : ∀ {n} {ps qs : Vec Ph (suc n)} → ISeq 0 ps qs
        → (chainC 0 ps ∖ hideInternal (suc n)) ─[τ*]─► (chainC 0 qs ∖ hideInternal (suc n))
iseq-τ* inil = τ*-refl
iseq-τ* {n} (iτ {ps = ps} qs st s) =
  τ*-step (Hide-τ (hideInternal (suc n)) (chainC 0 ps) st) (iseq-τ* s)
iseq-τ* {n} (iev {ps = ps} qs j b lo hi st s) =
  τ*-step (Hide-hidden (hideInternal (suc n)) (chainC 0 ps) {a = j , b}
            (hidMem (suc n) j lo (subst (j <_) (endIdx≡ 0 n) hi)) st)
          (iseq-τ* s)
```

**Front-freeing**: a non-full chain silently reaches a configuration whose
front cell is at its loop head, ready to read — a held value at the front is
handed one cell down (the sub-chain first frees *its* front, recursively).

```agda
freeFront : ∀ k {n} (ps : Vec Ph (suc n)) → length (cts ps) ≤ n
          → Σ[ qs ∈ Vec Ph n ] (ISeq k ps (p∘ ∷ qs) × (cts qs ≡ cts ps))
freeFront k (p∘ ∷ ps) bnd = ps , inil , refl
freeFront k (p↝ ∷ ps) bnd = ps , iτ (p∘ ∷ ps) (cc-reτ k ps) inil , refl
freeFront k {zero} (p⋆ x ∷ []) ()
freeFront k {suc m} (p⋆ x ∷ ps) bnd
  with freeFront (suc k) ps
         (≤-pred (subst (_≤ suc m) (len-∷ʳ (cts ps) x) bnd))
... | qs′ , s′ , ceq =
      (p⋆ x ∷ qs′) ,
      iseq-++ (iseq-lift (p⋆ x) s′)
        (iev (p↝ ∷ p⋆ x ∷ qs′) (suc k) x (n<1+n k) (k<endIdx (suc k) m)
             (cc-hand k qs′ x)
             (iτ (p∘ ∷ p⋆ x ∷ qs′) (cc-reτ k (p⋆ x ∷ qs′)) inil)) ,
      cong (_∷ʳ x) ceq
```

**Back-filling**: a non-empty chain silently reaches a configuration whose
*last* cell holds the *oldest* value, ready to write it out.  If the tail
sub-chain is empty, the head's value is handed down and pumped onwards.

```agda
fillBack : ∀ k {n} (ps : Vec Ph (suc n)) {h rest} → cts ps ≡ h ∷ rest
         → Σ[ qs ∈ Vec Ph (suc n) ]
             (ISeq k ps qs × (cts qs ≡ cts ps) × (lst qs ≡ p⋆ h))
fillBack k {zero} (p∘ ∷ []) ()
fillBack k {zero} (p↝ ∷ []) ()
fillBack k {zero} (p⋆ x ∷ []) refl = (p⋆ x ∷ []) , inil , refl , refl
fillBack k {suc m} (p∘ ∷ ps) eq with fillBack (suc k) ps eq
... | qs′ , s′ , ceq , leq = (p∘ ∷ qs′) , iseq-lift p∘ s′ , ceq , leq
fillBack k {suc m} (p↝ ∷ ps) eq with fillBack (suc k) ps eq
... | qs′ , s′ , ceq , leq = (p↝ ∷ qs′) , iseq-lift p↝ s′ , ceq , leq
fillBack k {suc m} (p⋆ x ∷ ps) eq with cts ps in ceq₀
fillBack k {suc m} (p⋆ x ∷ ps) refl | c ∷ cs with fillBack (suc k) ps ceq₀
... | qs′ , s′ , ceq , leq =
      (p⋆ x ∷ qs′) , iseq-lift (p⋆ x) s′ , cong (_∷ʳ x) (trans ceq ceq₀) , leq
fillBack k {suc m} (p⋆ x ∷ ps) refl | []
  with freeFront (suc k) ps (subst (_≤ m) (cong length (sym ceq₀)) z≤n)
... | qs″ , sA , ceqA
  with fillBack (suc k) (p⋆ x ∷ qs″) (cong (_∷ʳ x) (trans ceqA ceq₀))
...   | rs′ , sB , ceqB , leqB =
        (p↝ ∷ rs′) ,
        iseq-++ (iseq-lift (p⋆ x) sA)
          (iseq-++ (iev (p↝ ∷ p⋆ x ∷ qs″) (suc k) x (n<1+n k) (k<endIdx (suc k) m)
                        (cc-hand k qs″ x) inil)
                   (iseq-lift p↝ sB)) ,
        trans ceqB (cong (_∷ʳ x) (trans ceqA ceq₀)) ,
        leqB
```

### §7.9 The top-level views of `HConf`

Every strong step of `HConf ps`, classified by peeling the hiding layer and
feeding the chain inversion: a τ is a re-entry or a hidden hand-off
(contents preserved, measure decreased); a visible step is the front input
`dd.0?b` or the back output `dd.(suc n)!b` (which flushes the head of the
contents).

```agda
hconf-τ-view : ∀ {n} (ps : Vec Ph (suc n)) {M} → HConf ps ─[ τ ]─► M
             → Σ[ qs ∈ Vec Ph (suc n) ]
                 ((M ≡ HConf qs) × (cts qs ≡ cts ps) × (msr qs < msr ps))
hconf-τ-view {n} ps stp with Hide-τ-elim (hideInternal (suc n)) (chainC 0 ps) stp
... | hτP P′ pstp meq with cc-τ-inv 0 ps pstp
...   | qs , refl , c = qs , meq , cts-ccτ c , msr-ccτ c
hconf-τ-view {n} ps stp
    | hτH {e = dd} {a = j , b} P′ csat pstp meq with cc-ev-inv 0 ps pstp
...   | (j₂ , b₂) , qs , refl , refl , c =
        qs , meq ,
        cts-int c (hidLo (suc n) j₂ csat)
                  (subst (j₂ <_) (sym (endIdx≡ 0 n)) (hidHi (suc n) j₂ csat)) ,
        msr-int c (hidLo (suc n) j₂ csat)
                  (subst (j₂ <_) (sym (endIdx≡ 0 n)) (hidHi (suc n) j₂ csat))

notHid⇒end : ∀ n j → 0 < j → j ≤ endIdx 0 n
           → ¬ T ((0 <ᵇ j) ∧ (j <ᵇ suc n)) → j ≡ suc n
notHid⇒end n j lo ub ¬c =
  ≤-antisym (subst (j ≤_) (endIdx≡ 0 n) ub)
            (≮⇒≥ (λ hi → ¬c (hidMem (suc n) j lo hi)))

hconf-ev-view : ∀ {n} (ps : Vec Ph (suc n)) {l : Ev} {M} → HConf ps ─[ ev l ]─► M
  → (Σ[ b ∈ Bool ] Σ[ ps′ ∈ Vec Ph n ]
       ((ps ≡ p∘ ∷ ps′) × (l ≡ lblD (0 , b)) × (M ≡ HConf (p⋆ b ∷ ps′))))
  ⊎ (Σ[ b ∈ Bool ] Σ[ qs ∈ Vec Ph (suc n) ]
       ((l ≡ lblD (suc n , b)) × (M ≡ HConf qs) × (cts ps ≡ b ∷ cts qs)))
hconf-ev-view {n} ps stp with Hide-ev-elim (hideInternal (suc n)) (chainC 0 ps) stp
... | he√ fq = ⊥-elim (cc-no-ret 0 ps fq)
... | heV {e = dd} {a = j , b} P′ ¬c pstp with cc-ev-inv 0 ps pstp
...   | (j₂ , b₂) , qs , refl , refl , csIn b₃ =
        inj₁ (b₃ , _ , refl , refl , refl)
...   | (j₂ , b₂) , qs , refl , refl , csOut1 x =
        inj₂ (x , (p↝ ∷ []) , refl , refl , refl)
...   | (j₂ , b₂) , qs , refl , refl , csHand x = ⊥-elim (¬c tt)
...   | (j₂ , b₂) , qs , refl , refl , csTail {p = p} lt c′
        with notHid⇒end n j₂ (<-trans (n<1+n 0) lt)
                        (ccstep-ub (csTail {p = p} lt c′)) ¬c
...     | refl =
          inj₂ (b₂ , qs , refl , refl ,
                cts-end (csTail {p = p} lt c′) (sym (endIdx≡ 0 n)))
```

### §7.10 No configuration diverges, at any `N`

Fuel recursion on the measure: every τ strictly decreases `msr`, so an
infinite τ-chain is impossible — hiding introduces **no divergence**.

```agda
¬div-HConf′ : ∀ {n} (m : ℕ) (ps : Vec Ph (suc n)) → msr ps ≤ m
            → Diverges (HConf ps) → ⊥
¬div-HConf′ zero ps bnd d with hconf-τ-view ps (d .Diverges.step)
... | qs , meq , _ , lt = case ≤-trans lt bnd of λ ()
¬div-HConf′ (suc m) ps bnd d with hconf-τ-view ps (d .Diverges.step)
... | qs , meq , _ , lt =
      ¬div-HConf′ m qs (≤-pred (≤-trans lt bnd))
                  (subst Diverges meq (d .Diverges.rest))

¬div-HConf : ∀ {n} (ps : Vec Ph (suc n)) → Diverges (HConf ps) → ⊥
¬div-HConf ps = ¬div-HConf′ (msr ps) ps ≤-refl
```

### §7.11 The degenerate `N = 0` case

`HCHAIN 0 = Stop ∖ hideInternal 0` and `BN 0` (a buffer with no places)
both deadlock immediately.

```agda
stop-no-ev : ∀ {l : Ev} {M} → (Stop {R = Poly.⊤ {lzero}}) ─[ ev l ]─► M → ⊥
stop-no-ev (sRet eq)    = case eq of λ ()
stop-no-ev (sVis refl br) = case br of λ ()

stop-no-τ : ∀ {M} → (Stop {R = Poly.⊤ {lzero}}) ─[ τ ]─► M → ⊥
stop-no-τ (sSil eq)      = case eq of λ ()
stop-no-τ (sTau refl br) = case br of λ ()

hchain0-no-ev : ∀ {l : Ev} {M} → HCHAIN 0 ─[ ev l ]─► M → ⊥
hchain0-no-ev stp with Hide-ev-elim (hideInternal 0) Stop stp
... | he√ fq = case fq of λ ()
... | heV P′ ¬c pstp = stop-no-ev pstp

hchain0-no-τ : ∀ {M} → HCHAIN 0 ─[ τ ]─► M → ⊥
hchain0-no-τ stp with Hide-τ-elim (hideInternal 0) Stop stp
... | hτP P′ pstp _      = stop-no-τ pstp
... | hτH P′ csat pstp _ = stop-no-ev pstp

bn0-no-ev : ∀ {l : Ev} {M} → BN 0 ─[ ev l ]─► M → ⊥
bn0-no-ev stp with menu-ev-inv (bn-vis 0 []) (bnKN 0) stp
... | (j , b) , t , refl , feq , refl = bn-vis0-nof j b feq
```

### §7.12 The relation and the theorem

Two constructor families cover every reachable pair at every `N ≥ 1`:
a configuration against the buffer loop head holding the same contents
(`rS`), and against the pre-re-entry state (`rR`) — where the buffer lands
after answering, absorbing its re-entry τ.  `rZ` is the `N = 0` deadlock.

```agda
data RelN : DProc → DProc → Set₁ where
  rS : ∀ {n} (ps : Vec Ph (suc n)) → RelN (HConf ps) (SatN (suc n) (cts ps))
  rR : ∀ {n} (ps : Vec Ph (suc n)) → RelN (HConf ps) (SreN (suc n) (cts ps))
  rZ : RelN (HCHAIN 0) (BN 0)

RN-fwd-ev : ∀ {p q} {l : Ev} {p′} → RelN p q → p ─[ ev l ]─► p′
          → Σ[ q′ ∈ DProc ] ((q ═[ ev l ]═► q′) × RelN p′ q′)
RN-fwd-ev (rS {n} ps) stp with hconf-ev-view ps stp
... | inj₁ (b , ps′ , refl , refl , refl) =
      SreN (suc n) (cts ps′ ∷ʳ b) ,
      wev τ*-refl (sp-inN (suc n) (cts ps′) b (<⇒<ᵇ (s≤s (len-cts ps′)))) τ*-refl ,
      rR (p⋆ b ∷ ps′)
... | inj₂ (b , qs , refl , refl , ceq) =
      SreN (suc n) (cts qs) ,
      wev τ*-refl
          (subst (λ bs → SatN (suc n) bs ─[ ev (lblD (suc n , b)) ]─► SreN (suc n) (cts qs))
                 (sym ceq) (sp-outN n b (cts qs)))
          τ*-refl ,
      rR qs
RN-fwd-ev (rR {n} ps) stp with hconf-ev-view ps stp
... | inj₁ (b , ps′ , refl , refl , refl) =
      SreN (suc n) (cts ps′ ∷ʳ b) ,
      wev (τ*-step (sp-τN (suc n) (cts ps′)) τ*-refl)
          (sp-inN (suc n) (cts ps′) b (<⇒<ᵇ (s≤s (len-cts ps′)))) τ*-refl ,
      rR (p⋆ b ∷ ps′)
... | inj₂ (b , qs , refl , refl , ceq) =
      SreN (suc n) (cts qs) ,
      wev (τ*-step (sp-τN (suc n) (cts ps)) τ*-refl)
          (subst (λ bs → SatN (suc n) bs ─[ ev (lblD (suc n , b)) ]─► SreN (suc n) (cts qs))
                 (sym ceq) (sp-outN n b (cts qs)))
          τ*-refl ,
      rR qs
RN-fwd-ev rZ stp = ⊥-elim (hchain0-no-ev stp)

RN-fwd-τ : ∀ {p q p′} → RelN p q → p ─[ τ ]─► p′
         → Σ[ q′ ∈ DProc ] ((q ═[ τ ]═► q′) × RelN p′ q′)
RN-fwd-τ (rS {n} ps) stp with hconf-τ-view ps stp
... | qs , refl , ceq , _ =
      SatN (suc n) (cts ps) , wτ τ*-refl ,
      subst (λ bs → RelN (HConf qs) (SatN (suc n) bs)) ceq (rS qs)
RN-fwd-τ (rR {n} ps) stp with hconf-τ-view ps stp
... | qs , refl , ceq , _ =
      SreN (suc n) (cts ps) , wτ τ*-refl ,
      subst (λ bs → RelN (HConf qs) (SreN (suc n) bs)) ceq (rR qs)
RN-fwd-τ rZ stp = ⊥-elim (hchain0-no-τ stp)

RN-bwd-ev : ∀ {p q} {l : Ev} {q′} → RelN p q → q ─[ ev l ]─► q′
          → Σ[ p′ ∈ DProc ] ((p ═[ ev l ]═► p′) × RelN p′ q′)
RN-bwd-ev (rS {n} ps) stp
  with menu-ev-inv (bn-vis (suc n) (cts ps)) (bnKN (suc n)) stp
... | (j , b) , t , refl , feq , refl with bn-invN n (cts ps) j b feq
...   | inj₁ (refl , g , refl)
        with freeFront 0 ps (≤-pred (<ᵇ⇒< _ _ g))
...     | qs′ , sA , ceqA =
          HConf (p⋆ b ∷ qs′) ,
          wev (iseq-τ* sA)
              (Hide-keep (hideInternal (suc n)) (chainC 0 (p∘ ∷ qs′)) (λ z → z)
                         (cc-in 0 qs′ b))
              τ*-refl ,
          subst (λ bs → RelN (HConf (p⋆ b ∷ qs′)) (SreN (suc n) bs))
                (cong (_∷ʳ b) ceqA) (rR (p⋆ b ∷ qs′))
RN-bwd-ev (rS {n} ps) stp
    | (j , b) , t , refl , feq , refl
      | inj₂ (rest , beq , refl , refl)
        with fillBack 0 ps beq
...     | qs , sB , ceqB , leqB =
          HConf (outv qs) ,
          wev (iseq-τ* sB)
              (Hide-keep (hideInternal (suc n)) (chainC 0 qs)
                 (λ t′ → <-irrefl refl (<ᵇ⇒< (suc n) (suc n) t′))
                 (subst (λ j′ → chainC 0 qs ─[ ev (lblD (j′ , b)) ]─► chainC 0 (outv qs))
                        (endIdx≡ 0 n) (cc-out 0 qs leqB)))
              τ*-refl ,
          subst (λ bs → RelN (HConf (outv qs)) (SreN (suc n) bs))
                (proj₂ (∷-injective
                  (trans (sym (cts-outv qs leqB)) (trans ceqB beq))))
                (rR (outv qs))
RN-bwd-ev (rR ps) stp = ⊥-elim (sil-no-ev refl stp)
RN-bwd-ev rZ stp = ⊥-elim (bn0-no-ev stp)

RN-bwd-τ : ∀ {p q q′} → RelN p q → q ─[ τ ]─► q′
         → Σ[ p′ ∈ DProc ] ((p ═[ τ ]═► p′) × RelN p′ q′)
RN-bwd-τ (rS {n} ps) stp = ⊥-elim (menu-no-τ (bn-vis (suc n) (cts ps)) (bnKN (suc n)) stp)
RN-bwd-τ (rR {n} ps) stp with sil-τ-uniq refl stp
... | refl = HConf ps , wτ τ*-refl , rS ps
RN-bwd-τ rZ stp = ⊥-elim (menu-no-τ (bn-vis 0 []) (bnKN 0) stp)

RN-¬divL : ∀ {p q} → RelN p q → Diverges p → ⊥
RN-¬divL (rS ps) = ¬div-HConf ps
RN-¬divL (rR ps) = ¬div-HConf ps
RN-¬divL rZ      = λ d → hchain0-no-τ (d .Diverges.step)

RN-¬divR : ∀ {p q} → RelN p q → Diverges q → ⊥
RN-¬divR (rS {n} ps) = ¬div-SatN (suc n) (cts ps)
RN-¬divR (rR {n} ps) = ¬div-SreN (suc n) (cts ps)
RN-¬divR rZ          = ¬div-SatN 0 []
```

`DRFromRel` closes `RelN` into the divergence-respecting weak bisimulation;
the initial all-`p∘` configuration *is* `HCHAIN N` (up to the fold/replicate
correspondence) with empty contents, and `drbisim→≈FD` delivers the ∀`N`
failures-divergences equivalence — both FDR asserts of the `.csp` source at
every chain length, with `N = 5` as the named corollary.

```agda
module MHBN = DRFromRel RelN RN-fwd-ev RN-fwd-τ RN-bwd-ev RN-bwd-τ RN-¬divL RN-¬divR

chainC-rep : ∀ k n → chainFrom k n ≡ chainC k (replicate (suc n) p∘)
chainC-rep k zero    = refl
chainC-rep k (suc n) =
  cong (λ Q → COPYcell k ∥⇘ syncAt (suc k) ⇙ Q) (chainC-rep (suc k) n)

cts-rep : ∀ m → cts (replicate m p∘) ≡ []
cts-rep zero    = refl
cts-rep (suc m) = cts-rep m

hchain≈DR-buffer : ∀ N → HCHAIN N ≈DR BN N
hchain≈DR-buffer zero    = MHBN.rel→dr rZ
hchain≈DR-buffer (suc n) =
  subst₂ _≈DR_
    (cong (_∖ hideInternal (suc n)) (sym (chainC-rep 0 n)))
    (cong (loop (bn-step (suc n))) (cts-rep (suc n)))
    (MHBN.rel→dr (rS (replicate (suc n) p∘)))

hchain≈FD-buffer : ∀ N → HCHAIN N ≈FD BN N
hchain≈FD-buffer N = drbisim→≈FD (hchain≈DR-buffer N)

hchain5≈FD-buffer5 : HCHAIN 5 ≈FD BN 5
hchain5≈FD-buffer5 = hchain≈FD-buffer 5
```

## §8. Status (∀N)

Both TPC §3.1 asserts are discharged **for every chain length**:
`hchain≈FD-buffer : ∀ N → HCHAIN N ≈FD BN N` (with `hchain≈DR-buffer` the
underlying divergence-respecting weak bisimulation, and the `N = 5`
corollary `hchain5≈FD-buffer5`).  The §5 proof at `N = 2` is kept intact as
the worked finite instance.  The ∀`N` argument is a single relation over an
indexed configuration family (`Vec Ph N`), with: one vector-recursive step
characterisation (`cc-ev-inv`/`cc-τ-inv` through `Par-ev-elim`/`Par-τ-elim`
and `Hide-ev-elim`/`Hide-τ-elim`), τ*-pumping constructions
(`freeFront`/`fillBack`) answering the buffer's strong steps, and an
explicit strictly-decreasing τ-measure (`msr`) refuting divergence.  No
postulates, no `NON_TERMINATING`, no `mutual` blocks.
