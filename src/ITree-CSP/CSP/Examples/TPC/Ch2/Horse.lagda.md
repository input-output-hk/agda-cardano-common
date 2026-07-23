# TPC chapter 2: the pantomime horse

Third chapter-2 example (parallel operators), porting the pantomime-horse
alphabetised parallel of A.W. Roscoe's *The Theory and Practice of
Concurrency* (TPC §2.2). Source:

- `fdr-examples/tpc/chapter02/section2-2.csp` (horse block)

```csp
channel forward, backward, nod, neigh, wag, kick

Front = forward -> Front' [] nod -> Front
Back  = backward -> Back' [] wag -> Back

F = {forward, backward, nod, neigh}
B = {forward, backward, wag, kick}

Front' = RUN(F)
Back'  = RUN(B)

Horse = Front [F||B] Back

assert RUN({nod,wag}) [T= Horse
assert Horse [T= RUN({nod,wag})
```

The front and back halves of the horse can each *propose* moving (`forward`
resp. `backward`), but the two movement events are shared between the
alphabets `F` and `B`, and each is only ever *offered* by one half: `Front`
never offers `backward`, `Back` never offers `forward`. So both movement
events are **permanently blocked** — the poor horse can only stand still,
nodding and wagging (`nod` and `wag` are unshared, so they interleave
freely). That is exactly the book's pair of asserts: `Horse` is
trace-equivalent to `RUN({nod,wag})`.

**Modelling reductions:**

- **Alphabetised parallel as interface parallel.** `Front` only ever
  communicates in `{forward, nod} ⊆ F` and `Back` in `{backward, wag} ⊆ B`
  — each component respects its alphabet — so `Front [F||B] Back` denotes
  the same process as the interface parallel on the *shared* alphabet,
  `Front [| F ∩ B |] Back` with `F ∩ B = {forward, backward}`. We model
  the composition with `_∥⇘_⇙_` at that shared synchronisation set.
- **`Front'`/`Back'` are unreachable.** They sit behind the permanently
  blocked `forward`/`backward`, so no behaviour of `Horse` ever depends on
  them; we model both as `Stop`. (The proofs below *do* handle the
  `forward`/`backward` offers of the components — the blocking is proved,
  not assumed.)
- **`neigh`/`kick` are omitted** from the event type: they occur only
  inside the unreachable `RUN(F)`/`RUN(B)` and in no assert.

This module proves both asserts, for every trace:

```text
run⊑horse : RUNnw ⊑T Horse     -- every Horse trace is a RUN({nod,wag}) trace
horse⊑run : Horse ⊑T RUNnw     -- every RUN({nod,wag}) trace is realised by Horse
```

## §1. Imports

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.TPC.Ch2.Horse where

open import Level using (lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
```

## §2. The event type and its decidable equality

Four nullary visible events (`neigh`/`kick` omitted, see the header).

```agda
data HCh : Set → Set where
  forward backward nod wag : HCh ⊤

HCh-≟ : (x y : AnyTypes HCh) → Dec (x ≡ y)
HCh-≟ (_ , forward)  (_ , forward)  = yes refl
HCh-≟ (_ , backward) (_ , backward) = yes refl
HCh-≟ (_ , nod)      (_ , nod)      = yes refl
HCh-≟ (_ , wag)      (_ , wag)      = yes refl
HCh-≟ (_ , forward)  (_ , backward) = no λ ()
HCh-≟ (_ , forward)  (_ , nod)      = no λ ()
HCh-≟ (_ , forward)  (_ , wag)      = no λ ()
HCh-≟ (_ , backward) (_ , forward)  = no λ ()
HCh-≟ (_ , backward) (_ , nod)      = no λ ()
HCh-≟ (_ , backward) (_ , wag)      = no λ ()
HCh-≟ (_ , nod)      (_ , forward)  = no λ ()
HCh-≟ (_ , nod)      (_ , backward) = no λ ()
HCh-≟ (_ , nod)      (_ , wag)      = no λ ()
HCh-≟ (_ , wag)      (_ , forward)  = no λ ()
HCh-≟ (_ , wag)      (_ , backward) = no λ ()
HCh-≟ (_ , wag)      (_ , nod)      = no λ ()

open import CSP.Operators HCh-≟
```

`_□_` is parametrised by a `DecEq` instance on the return type; both loop
bodies below choose at the polymorphic unit `Poly.⊤ {lzero}`, so we supply
the same `Irrelevant⇒DecEq` instance as the chapter-1 modules.

```agda
instance
  DecEq-⊤poly : DecEq (Poly.⊤ {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })
```

## §3. Process definitions

`Front' = Back' = Stop` (unreachable, see the header); each half is a
`loop0` over the binary external choice of its `.csp` body.

```agda
HProc : Set₁
HProc = PTree HCh (ExtI HCh) (Poly.⊤ {lzero})

fbody bbody rbody : PTree HCh (ExtI HCh) (Poly.⊤ {lzero})
fbody = (forward  ⟶₀ Stop) □ (nod ⟶₀ Skip)
bbody = (backward ⟶₀ Stop) □ (wag ⟶₀ Skip)
rbody = (nod ⟶₀ Skip) □ (wag ⟶₀ Skip)

-- Front = forward -> Front' [] nod -> Front   (Front' = Stop)
Front : HProc
Front = loop0 fbody

-- Back  = backward -> Back' [] wag -> Back    (Back' = Stop)
Back : HProc
Back = loop0 bbody

-- RUN({nod,wag})
RUNnw : HProc
RUNnw = loop0 rbody
```

The shared alphabet `F ∩ B = {forward, backward}` as a channel-level
`EventSet`, and the horse itself.

```agda
shared : AnyTypes HCh → Set
shared (_ , forward)  = ⊤
shared (_ , backward) = ⊤
shared (_ , nod)      = ⊥
shared (_ , wag)      = ⊥

shared-dec : (at : AnyTypes HCh) → Dec (shared at)
shared-dec (_ , forward)  = yes tt
shared-dec (_ , backward) = yes tt
shared-dec (_ , nod)      = no (λ z → z)
shared-dec (_ , wag)      = no (λ z → z)

Shared : EventSet
Shared = chanSet shared shared-dec

-- Horse = Front [F||B] Back  =  Front [|F∩B|] Back  (alphabets respected)
Horse : HProc
Horse = Front ∥⇘ Shared ⇙ Back
```

## §4. Verification

```agda
open import Semantics.LTS       {E = HCh} {I = ExtI HCh}
open import Semantics.Failures  {E = HCh} {I = ExtI HCh}
  using (_⊑T_; traces; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

open import CSP.Laws.Traces.PrefixInversion HCh-≟
  using (sil-no-ev; sil-τ-uniq; TEmpty; ∅t-empty; □-mt-empty)
open import CSP.Laws.Traces.TraceLawsParallel HCh-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace HCh-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono HCh-≟
  using (Par-trace-intro)
```

### §4.1 The FDR asserts

```agda
-- assert RUN({nod,wag}) [T= Horse   (holds)
run⊑horse : RUNnw ⊑T Horse

-- assert Horse [T= RUN({nod,wag})   (holds)
horse⊑run : Horse ⊑T RUNnw
```

### §4.2 Event labels and reachable states

All three processes are `loop0`s over a `□` of two prefixes, so their
states are `iter-bind` terms — definitional unfoldings of the loops'
successors, checked by the `refl`s in §4.3. Each of `Front`/`Back` has a
dead post-movement state (`F↓`/`B↓`: the `Stop` continuation under the loop
wrappers — offerless and stable) and a silent loop re-entry state
(`F↝`/`B↝`); `RUNnw` re-enters silently after either event (`R↝`).

```agda
Ev : Set₁
Ev = Event√ (Poly.⊤ {lzero})

fwdE bwdE nodE wagE : Ev
fwdE = evl (evLabel ⊤ forward  tt)
bwdE = evl (evLabel ⊤ backward tt)
nodE = evl (evLabel ⊤ nod      tt)
wagE = evl (evLabel ⊤ wag      tt)

-- the merge function of the CSP parallel (η-equal to the one baked into _∥⇘_⇙_)
mg⊤ : Mg (Poly.⊤ {lzero}) (Poly.⊤ {lzero}) (Poly.⊤ {lzero})
mg⊤ _ _ = Poly.tt

frontK backK runK : Poly.⊤ {lzero}
                  → PTree HCh (ExtI HCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero})
frontK _ = fbody >>= (λ a′ → Ret (inj₁ a′))
backK  _ = bbody >>= (λ a′ → Ret (inj₁ a′))
runK   _ = rbody >>= (λ a′ → Ret (inj₁ a′))

F↓ F↝ B↓ B↝ R↝ : HProc
F↓ = iter-bind (Stop >>= (λ a′ → Ret (inj₁ a′))) frontK
F↝ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) frontK
B↓ = iter-bind (Stop >>= (λ a′ → Ret (inj₁ a′))) backK
B↝ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) backK
R↝ = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) runK
```

### §4.3 Strong steps

All hold by `refl`: the `□` offer maps compute on the constructor-headed
prefix nodes (`HCh-≟` decides on concrete channels), and the re-entry
`sil`s land definitionally back on the loop heads.

```agda
Front-fwd : Front ─[ ev fwdE ]─► F↓
Front-fwd = sVis {at = ⊤ , forward} {a = tt} refl refl

Front-nod : Front ─[ ev nodE ]─► F↝
Front-nod = sVis {at = ⊤ , nod} {a = tt} refl refl

F↝-τ : F↝ ─[ τ ]─► Front
F↝-τ = sSil refl

Back-bwd : Back ─[ ev bwdE ]─► B↓
Back-bwd = sVis {at = ⊤ , backward} {a = tt} refl refl

Back-wag : Back ─[ ev wagE ]─► B↝
Back-wag = sVis {at = ⊤ , wag} {a = tt} refl refl

B↝-τ : B↝ ─[ τ ]─► Back
B↝-τ = sSil refl

RUN-nod : RUNnw ─[ ev nodE ]─► R↝
RUN-nod = sVis {at = ⊤ , nod} {a = tt} refl refl

RUN-wag : RUNnw ─[ ev wagE ]─► R↝
RUN-wag = sVis {at = ⊤ , wag} {a = tt} refl refl

R↝-τ : R↝ ─[ τ ]─► RUNnw
R↝-τ = sSil refl
```

### §4.4 Stability: the loop heads take no τ

A loop head `iter-bind (((c ⟶₀ X) □ (d ⟶₀ Y)) >>= …) K` is stable: the
`□`'s τ-part is `□-mt` of two `∅t`s — pointwise `nothing` by the imported
`□-mt-empty` — pushed through the `bindT`/`iterT` wrappers by the two
`TEmpty`-preservation lemmas (the same idiom as the `Interleaving` module's
guarded-counter states).

```agda
bindT-empty : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
                (k : R → PTree HCh (ExtI HCh) S)
                {v  : (at : AnyTypes HCh) → ContinueType at (Maybe (PTree HCh (ExtI HCh) R))}
                {τc : (i : AnyTypes (ExtI HCh)) → ContinueType i (Maybe (PTree HCh (ExtI HCh) R))}
            → TEmpty τc → TEmpty (bindT k (react v τc))
bindT-empty k {τc = τc} emp i a with τc i a | emp i a
... | nothing | _ = refl

iterT-empty : ∀ {ℓr} {A : Set} {R : Set ℓr}
                (K : A → PTree HCh (ExtI HCh) (A ⊎ R))
                {v  : (at : AnyTypes HCh) → ContinueType at (Maybe (PTree HCh (ExtI HCh) (A ⊎ R)))}
                {τc : (i : AnyTypes (ExtI HCh)) → ContinueType i (Maybe (PTree HCh (ExtI HCh) (A ⊎ R)))}
            → TEmpty τc → TEmpty (iterT K (react v τc))
iterT-empty K {τc = τc} emp i a with τc i a | emp i a
... | nothing | _ = refl

-- τ-refutation for a loop head whose body node (bv , bt) has empty τ-part
□body-no-τ : ∀ (bv : (at : AnyTypes HCh) → ContinueType at (Maybe (PTree HCh (ExtI HCh) (Poly.⊤ {lzero}))))
               (bt : (i : AnyTypes (ExtI HCh)) → ContinueType i (Maybe (PTree HCh (ExtI HCh) (Poly.⊤ {lzero}))))
               (K : Poly.⊤ {lzero} → PTree HCh (ExtI HCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero}))
           → TEmpty bt
           → ∀ (i : AnyTypes (ExtI HCh)) (a : proj₁ i) {t′ : HProc}
           → iterT K (react (bindV (λ a′ → Ret (inj₁ a′)) (react bv bt))
                            (bindT (λ a′ → Ret (inj₁ a′)) (react bv bt))) i a ≡ just t′
           → ⊥
□body-no-τ bv bt K emp i a br =
  case trans (sym (iterT-empty K {v = bindV (λ a′ → Ret (inj₁ a′)) (react bv bt)}
                               {τc = bindT (λ a′ → Ret (inj₁ a′)) (react bv bt)}
                               (bindT-empty (λ a′ → Ret (inj₁ a′)) {v = bv} {τc = bt} emp)
                               i a)) br of λ ()

□loop-no-τ : ∀ (c d : HCh ⊤) (X Y : PTree HCh (ExtI HCh) (Poly.⊤ {lzero}))
               (K : Poly.⊤ {lzero} → PTree HCh (ExtI HCh) (Poly.⊤ {lzero} ⊎ Poly.⊤ {lzero}))
               {t′ : HProc}
           → iter-bind (((c ⟶₀ X) □ (d ⟶₀ Y)) >>= (λ a′ → Ret (inj₁ a′))) K ─[ τ ]─► t′
           → ⊥
□loop-no-τ c d X Y K (sSil ())
□loop-no-τ c d X Y K (sTau {i = i} {a = a} refl br) =
  □body-no-τ (mergeVis (Prefix-cont c (λ _ → X)) (Prefix-cont d (λ _ → Y)))
             (□-mt (react (Prefix-cont c (λ _ → X)) ∅t)
                   (react (Prefix-cont d (λ _ → Y)) ∅t)
                   (c ⟶₀ X) (d ⟶₀ Y))
             K
             (□-mt-empty {vP = Prefix-cont c (λ _ → X)} {vQ = Prefix-cont d (λ _ → Y)}
                         {P = c ⟶₀ X} {Q = d ⟶₀ Y} ∅t-empty ∅t-empty)
             i a br
```

### §4.5 Visible-step inversions of the loop heads

A visible step of a loop head fires exactly one of the two prefixes.
The channels are concrete constructors, so the `mergeVis` offer map
unblocks after the two `HCh-≟` decisions (cf. the `Interleaving` module's
`LCst-ev-inv`).

```agda
Front-ev-inv : ∀ {l : Ev} {t′ : HProc}
             → Front ─[ ev l ]─► t′
             → ((l ≡ fwdE) × (t′ ≡ F↓)) ⊎ ((l ≡ nodE) × (t′ ≡ F↝))
Front-ev-inv (sRet ())
Front-ev-inv (sVis {at = at} {a = x} refl br) with HCh-≟ (⊤ , forward) at
... | yes refl = inj₁ (refl , sym (just-injective br))
... | no _ with HCh-≟ (⊤ , nod) at
...   | yes refl = inj₂ (refl , sym (just-injective br))
...   | no _     = case br of λ ()

Back-ev-inv : ∀ {l : Ev} {t′ : HProc}
            → Back ─[ ev l ]─► t′
            → ((l ≡ bwdE) × (t′ ≡ B↓)) ⊎ ((l ≡ wagE) × (t′ ≡ B↝))
Back-ev-inv (sRet ())
Back-ev-inv (sVis {at = at} {a = x} refl br) with HCh-≟ (⊤ , backward) at
... | yes refl = inj₁ (refl , sym (just-injective br))
... | no _ with HCh-≟ (⊤ , wag) at
...   | yes refl = inj₂ (refl , sym (just-injective br))
...   | no _     = case br of λ ()

RUNnw-ev-inv : ∀ {l : Ev} {t′ : HProc}
             → RUNnw ─[ ev l ]─► t′
             → ((l ≡ nodE) × (t′ ≡ R↝)) ⊎ ((l ≡ wagE) × (t′ ≡ R↝))
RUNnw-ev-inv (sRet ())
RUNnw-ev-inv (sVis {at = at} {a = x} refl br) with HCh-≟ (⊤ , nod) at
... | yes refl = inj₁ (refl , sym (just-injective br))
... | no _ with HCh-≟ (⊤ , wag) at
...   | yes refl = inj₂ (refl , sym (just-injective br))
...   | no _     = case br of λ ()
```

### §4.6 The dead post-movement states

`F↓`/`B↓` wrap `Stop`, whose `∅v`/`∅t` continuations pass through the
`bind`/`iter` wrappers definitionally — no offers, no τ, so their only
big-step trace is `[]`.

```agda
F↓-no-ev : ∀ {l : Ev} {t′ : HProc} → F↓ ─[ ev l ]─► t′ → ⊥
F↓-no-ev (sRet ())
F↓-no-ev (sVis refl br) = case br of λ ()

F↓-no-τ : ∀ {t′ : HProc} → F↓ ─[ τ ]─► t′ → ⊥
F↓-no-τ (sSil ())
F↓-no-τ (sTau refl br) = case br of λ ()

F↓-end : ∀ {s} {p′ : HProc} → F↓ ⟹⟨ s ⟩ p′ → s ≡ []
F↓-end ⟹-refl       = refl
F↓-end (⟹-τ st _)  = ⊥-elim (F↓-no-τ st)
F↓-end (⟹-ev st _) = ⊥-elim (F↓-no-ev st)

B↓-no-ev : ∀ {l : Ev} {t′ : HProc} → B↓ ─[ ev l ]─► t′ → ⊥
B↓-no-ev (sRet ())
B↓-no-ev (sVis refl br) = case br of λ ()

B↓-no-τ : ∀ {t′ : HProc} → B↓ ─[ τ ]─► t′ → ⊥
B↓-no-τ (sSil ())
B↓-no-τ (sTau refl br) = case br of λ ()

B↓-end : ∀ {s} {p′ : HProc} → B↓ ⟹⟨ s ⟩ p′ → s ≡ []
B↓-end ⟹-refl       = refl
B↓-end (⟹-τ st _)  = ⊥-elim (B↓-no-τ st)
B↓-end (⟹-ev st _) = ⊥-elim (B↓-no-ev st)
```

### §4.7 The three trace grammars

`FTr`: traces of `Front` — any number of `nod`s, optionally closed by one
`forward` (after which `F↓` is dead). `BTr` mirrors it with
`wag`/`backward`. `RTr`: traces of `RUNnw` — any word over `{nod, wag}`.

```agda
data FTr : List Ev → Set₁ where
  fnil : FTr []
  ffwd : FTr (fwdE ∷ [])
  fnod : ∀ {s} → FTr s → FTr (nodE ∷ s)

data BTr : List Ev → Set₁ where
  bnil : BTr []
  bbwd : BTr (bwdE ∷ [])
  bwag : ∀ {s} → BTr s → BTr (wagE ∷ s)

data RTr : List Ev → Set₁ where
  rnil : RTr []
  rnod : ∀ {s} → RTr s → RTr (nodE ∷ s)
  rwag : ∀ {s} → RTr s → RTr (wagE ∷ s)
```

### §4.8 Big-step characterisations (the elim halves)

Structural induction over the big-step derivations with §4.4–§4.6, chasing
the silent re-entries with the imported `sil-τ-uniq`/`sil-no-ev`.

```agda
data FSt : HProc → Set₁ where
  f0 : FSt Front
  f↝ : FSt F↝

ffwd-end : ∀ {s} {p′ : HProc} → F↓ ⟹⟨ s ⟩ p′ → FTr (fwdE ∷ s)
ffwd-end bs with F↓-end bs
... | refl = ffwd

Front-char : ∀ {p s} {p′ : HProc} → FSt p → p ⟹⟨ s ⟩ p′ → FTr s
Front-char _  ⟹-refl        = fnil
Front-char f0 (⟹-τ st _)    = ⊥-elim (□loop-no-τ forward nod Stop Skip frontK st)
Front-char f0 (⟹-ev st rest) with Front-ev-inv st
... | inj₁ (refl , refl) = ffwd-end rest
... | inj₂ (refl , refl) = fnod (Front-char f↝ rest)
Front-char f↝ (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = Front-char f0 rest
Front-char f↝ (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

data BSt : HProc → Set₁ where
  b0 : BSt Back
  b↝ : BSt B↝

bbwd-end : ∀ {s} {p′ : HProc} → B↓ ⟹⟨ s ⟩ p′ → BTr (bwdE ∷ s)
bbwd-end bs with B↓-end bs
... | refl = bbwd

Back-char : ∀ {p s} {p′ : HProc} → BSt p → p ⟹⟨ s ⟩ p′ → BTr s
Back-char _  ⟹-refl        = bnil
Back-char b0 (⟹-τ st _)    = ⊥-elim (□loop-no-τ backward wag Stop Skip backK st)
Back-char b0 (⟹-ev st rest) with Back-ev-inv st
... | inj₁ (refl , refl) = bbwd-end rest
... | inj₂ (refl , refl) = bwag (Back-char b↝ rest)
Back-char b↝ (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = Back-char b0 rest
Back-char b↝ (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)

data RSt : HProc → Set₁ where
  r0 : RSt RUNnw
  r↝ : RSt R↝

RUNnw-char : ∀ {p s} {p′ : HProc} → RSt p → p ⟹⟨ s ⟩ p′ → RTr s
RUNnw-char _  ⟹-refl        = rnil
RUNnw-char r0 (⟹-τ st _)    = ⊥-elim (□loop-no-τ nod wag Skip Skip runK st)
RUNnw-char r0 (⟹-ev st rest) with RUNnw-ev-inv st
... | inj₁ (refl , refl) = rnod (RUNnw-char r↝ rest)
... | inj₂ (refl , refl) = rwag (RUNnw-char r↝ rest)
RUNnw-char r↝ (⟹-τ st rest) with sil-τ-uniq refl st
... | refl = RUNnw-char r0 rest
RUNnw-char r↝ (⟹-ev st _)   = ⊥-elim (sil-no-ev refl st)
```

### §4.9 The blocking shuffle

The crux: `forward`/`backward` are in the synchronisation set but each is
offered by only one side, so the `psync` case is **uninhabited** — a joint
`nod`/`wag` has `mem ≡ ⊥`, a joint `forward` would need `forward` at the
head of a `Back` trace (no `BTr` constructor produces it), and symmetrically
a joint `backward` never heads a `Front` trace. So every event of a `Horse`
trace is a solo `nod` (`psoloL`) or a solo `wag` (`psoloR`); the
post-movement suffixes are cut off by `ffwd`/`bbwd` (which would need the
blocked movement to have fired), and the joint √ (`p√`) would need `√` at
the head of a `Front` trace.

```agda
horse-shuffle : ∀ {sP sQ s}
              → ParInter Shared mg⊤ sP sQ s → FTr sP → BTr sQ → RTr s
horse-shuffle pnil           _         _         = rnil
horse-shuffle (psync m∈ PI)  (fnod _)  _         = ⊥-elim m∈
horse-shuffle (psync m∈ PI)  ffwd      ()
horse-shuffle (psoloL ¬m PI) (fnod tl) btr       = rnod (horse-shuffle PI tl btr)
horse-shuffle (psoloL ¬m PI) ffwd      _         = ⊥-elim (¬m tt)
horse-shuffle (psoloR ¬m PI) ftr       (bwag tl) = rwag (horse-shuffle PI ftr tl)
horse-shuffle (psoloR ¬m PI) ftr       bbwd      = ⊥-elim (¬m tt)
horse-shuffle p√ () _
```

### §4.10 `assert RUN({nod,wag}) [T= Horse`

The intro half for `RUNnw` (each production is the matching §4.3 step,
crossing the silent re-entry), then the assembly: de-interleave the `Horse`
trace with `Par-trace-elim`, characterise both shares, and push them
through the blocking shuffle.

```agda
RUNnw-intro : ∀ {s} → RTr s → traces RUNnw s
RUNnw-intro rnil = RUNnw , ⟹-refl
RUNnw-intro (rnod tl) with RUNnw-intro tl
... | p′ , bs = p′ , ⟹-ev RUN-nod (⟹-τ R↝-τ bs)
RUNnw-intro (rwag tl) with RUNnw-intro tl
... | p′ , bs = p′ , ⟹-ev RUN-wag (⟹-τ R↝-τ bs)

run⊑horse s (Rt , bs) with Par-trace-elim Shared mg⊤ Front Back bs
... | sP , sQ , P′ , Q′ , rP , rQ , inter =
      RUNnw-intro (horse-shuffle inter (Front-char f0 rP) (Back-char b0 rQ))
```

### §4.11 `assert Horse [T= RUN({nod,wag})`

The converse: every `{nod, wag}` word is realised by the horse — `Front`
supplies each `nod` and `Back` each `wag` as solo steps (`nod`/`wag` are
outside the synchronisation set, refuted by the identity `λ z → z` on `⊥`),
re-interleaved with `Par-trace-intro`.

```agda
run→horse : ∀ {s} → RTr s
          → Σ[ sP ∈ List Ev ] Σ[ sQ ∈ List Ev ]
            Σ[ P′ ∈ HProc ] Σ[ Q′ ∈ HProc ]
              (Front ⟹⟨ sP ⟩ P′) × (Back ⟹⟨ sQ ⟩ Q′)
              × ParInter Shared mg⊤ sP sQ s
run→horse rnil = [] , [] , Front , Back , ⟹-refl , ⟹-refl , pnil
run→horse (rnod tl) with run→horse tl
... | sP , sQ , P′ , Q′ , rP , rQ , PI =
      nodE ∷ sP , sQ , P′ , Q′ ,
      ⟹-ev Front-nod (⟹-τ F↝-τ rP) , rQ , psoloL (λ z → z) PI
run→horse (rwag tl) with run→horse tl
... | sP , sQ , P′ , Q′ , rP , rQ , PI =
      sP , wagE ∷ sQ , P′ , Q′ ,
      rP , ⟹-ev Back-wag (⟹-τ B↝-τ rQ) , psoloR (λ z → z) PI

horse⊑run s (Rt , bs) with run→horse (RUNnw-char r0 bs)
... | sP , sQ , P′ , Q′ , rP , rQ , PI =
      Par-trace-intro Shared mg⊤ Front Back rP rQ PI
```

## §5. Status

Both TPC §2.2 asserts about the pantomime horse are discharged:
`run⊑horse` (§4.10) and `horse⊑run` (§4.11) together give the trace
equivalence `traces Horse = traces RUN({nod,wag})` — the shared
`forward`/`backward` are permanently blocked (each offered by only one
half, proved uninhabited in §4.9), so the horse can only nod and wag. No
postulates, no `NON_TERMINATING`, no `mutual` blocks.
