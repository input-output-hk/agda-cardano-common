# Vending machine: process-level LTL satisfaction (`_⊨_`)

Discharges the first deferred item of `VendingMachine.lagda.md` §5.5: LTL
satisfaction quantified over *every* trace rooted at a VM process, via trace
inversion. Body level is proved unconditionally; loop level follows.

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.VendingMachine.VendingMachine_LTL_Sat where

open import Level using (Level; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Process_Trees
open PTree

-- The VM model, its atoms (atCoin/atDrink/atTea/atCoffee), and process defs.
open import CSP.Examples.VendingMachine.VendingMachine

-- CSP operators: _⟶₀_, _□_, Skip, deadlock, ∅t, loop0, etc.
import CSP.Operators {E = VM} as CSPOps
open CSPOps VM-AnyTypes-≟

open import Semantics.LTS       {E = VM} {I = ExtI VM}
open import Semantics.WeakBisim {E = VM} {I = ExtI VM} using (_═[_]═►_; wev; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.DRBisim   {E = VM} {I = ExtI VM} using (Diverges)
open import Semantics.Deadlock  {E = VM} {I = ExtI VM} using (IsStuck)
open import Semantics.LTL.Traces_Based {E = VM} {I = ExtI VM}
  using ( LTLᵗ; atom; ⟦_⟧; _⊨_; G_; F_; X_; _U_; _∧_; _∨_; _⇒_; atDone; atStuck
        ; Frame; Trace; ∞Trace; step; done; stuck; div
        ; frameOf; frameState; tail; tailIdx; drop; dropIdx; drop-stutter; dropIdx-stutter; tail-stutter
        ; IsTerminator; ⟦G⟧⁺; ⟦G⟧⁺⇒⟦G⟧ )
  renaming (¬_ to ¬ᵗ_)
open ∞Trace

-- The post-coin external choice, named for reuse.
body2 : PTree VM (ExtI VM) (⊤ {lzero})
body2 = (tea ⟶₀ Skip) □ (coffee ⟶₀ Skip)
```

```agda
open import Function.Base using (case_of_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

-- VM_body_impl and body2 have empty internal (∅t) react nodes ⇒ no τ-step.
-- Mirror Semantics.Deadlock.deadlock-IsStuck's sRet/sSil/sTau refutation.
VM_body_impl-no-τ : ∀ {t′} → VM_body_impl ─[ τ ]─► t′ → ⊥
VM_body_impl-no-τ (sSil eq)      = case eq of λ ()
VM_body_impl-no-τ (sTau refl br) = case br of λ ()

body2-no-τ : ∀ {t′} → body2 ─[ τ ]─► t′ → ⊥
body2-no-τ (sSil eq)      = case eq of λ ()
body2-no-τ (sTau {i = i} {a = a} refl br)
  with i   | a
... | _ , base _            | _               = case br of λ ()
... | _ , fin               | _               = case br of λ ()
... | _ , pair (base _) _   | _               = case br of λ ()
... | _ , pair (pair _ _) _ | _               = case br of λ ()
... | _ , pair fin _        | lift fzero              , _ = case br of λ ()
... | _ , pair fin _        | lift (fsuc fzero)       , _ = case br of λ ()
... | _ , pair fin _        | lift (fsuc (fsuc _))    , _ = case br of λ ()

Skip-no-τ : ∀ {t′} → Skip {lzero} ─[ τ ]─► t′ → ⊥
Skip-no-τ (sSil eq)      = case eq of λ ()
Skip-no-τ (sTau eq br)   = case eq of λ ()

deadlock-no-τ : ∀ {t′} → deadlock {E = VM} {I = ExtI VM} {R = ⊤ {lzero}} ─[ τ ]─► t′ → ⊥
deadlock-no-τ (sSil eq)      = case eq of λ ()
deadlock-no-τ (sTau refl br) = case br of λ ()

noτ⇒τ*≡ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree VM (ExtI VM) R}
         → (∀ {u} → t ─[ τ ]─► u → ⊥) → t ─[τ*]─► t′ → t ≡ t′
noτ⇒τ*≡ noτ τ*-refl         = refl
noτ⇒τ*≡ noτ (τ*-step t→u _) = ⊥-elim (noτ t→u)
```

Single visible-step inversion lemmas.

```agda
open import Relation.Nullary using (Dec; yes; no)
open import Data.Maybe.Properties using (just-injective)
open import CSP.Laws.Traces.TraceLaws VM-AnyTypes-≟ using (Prefix-cont-just)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono VM-AnyTypes-≟ using (□-vis-inv; □evR; evP; evQ; evPQ)

-- A `Prefix-cont ce P` offer map fires only on its own channel: if it returns
-- `just t′` for event (A , e), then (⊤ , ce) ≡ (A , e) and t′ ≡ P a.  Splitting
-- on `E-≟ (⊤ , ce) (A , e)` here reduces `Prefix-cont`'s own `with`.
Prefix-cont-fires : ∀ {A : Set lzero} {e : VM A} {a : A}
                      {ce : VM (⊤ {lzero})} {P : ⊤ {lzero} → PTree VM (ExtI VM) (⊤ {lzero})}
                      {t′ : PTree VM (ExtI VM) (⊤ {lzero})}
                  → Prefix-cont ce P (A , e) a ≡ just t′
                  → ((⊤ {lzero} , ce) ≡ (A , e)) × Σ[ x ∈ ⊤ {lzero} ] (t′ ≡ P x)
Prefix-cont-fires {A = A} {e = e} {a = a} {ce = ce} br with VM-AnyTypes-≟ (⊤ {lzero} , ce) (A , e)
... | yes refl = refl , a , sym (just-injective br)
... | no ¬eq   = ⊥-elim (case br of λ ())

VM_body_impl-ev-inv : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
                    → VM_body_impl ─[ ev (evl (evLabel A e a)) ]─► t′
                    → (A ≡ ⊤ {lzero}) × (t′ ≡ body2)
VM_body_impl-ev-inv st with ev-inv st
... | v , τc , refl , br with Prefix-cont-fires br
...   | refl , _ , t′≡ = refl , t′≡

body2-ev-inv : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
             → body2 ─[ ev (evl (evLabel A e a)) ]─► t′
             → (t′ ≡ Skip)
prefix-Skip : ∀ {A : Set lzero} {e : VM A} {a : A} {ce : VM (⊤ {lzero})} {t′}
            → (ce ⟶₀ Skip) ─[ ev (evl (evLabel A e a)) ]─► t′ → t′ ≡ Skip
prefix-Skip stp with ev-inv stp
... | v , τc , refl , br with Prefix-cont-fires br
...   | _ , _ , t′≡ = t′≡

-- tea and coffee are distinct channels, so the two prefix sub-steps of body2
-- cannot fire on a common event: that rules out the evPQ case.
tea≢coffee-step : ∀ {A : Set lzero} {e : VM A} {a : A} {P₁ Q₁}
                → (tea ⟶₀ Skip)    ─[ ev (evl (evLabel A e a)) ]─► P₁
                → (coffee ⟶₀ Skip) ─[ ev (evl (evLabel A e a)) ]─► Q₁
                → ⊥
tea≢coffee-step stT stC with ev-inv stT | ev-inv stC
... | _ , _ , refl , brT | _ , _ , refl , brC
      with Prefix-cont-fires brT | Prefix-cont-fires brC
...     | refl , _ , _ | () , _ , _

body2-ev-inv {A = A} {e = e} st with ev-inv st
... | v , τc , eqf , br with □-vis-inv (tea ⟶₀ Skip) (coffee ⟶₀ Skip) eqf br
... | evP stP = prefix-Skip stP
... | evQ stQ = prefix-Skip stQ
... | evPQ stP stQ = ⊥-elim (tea≢coffee-step stP stQ)
```

## Task 3: Weak-step collapse

`VM_body_impl`, `body2`, and `Skip` have no τ-steps, so the leading and
trailing `─[τ*]─►` closures in a weak visible step both collapse to
reflexivity. The weak successor therefore equals the strong successor, and we
reuse the Task 2 strong-step inversions.

```agda
VM_body_impl-wev-inv : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
                     → VM_body_impl ═[ ev (evl (evLabel A e a)) ]═► t′
                     → t′ ≡ body2
VM_body_impl-wev-inv (wev pre vis post)
  with noτ⇒τ*≡ VM_body_impl-no-τ pre
... | refl with VM_body_impl-ev-inv vis
...   | _ , refl = sym (noτ⇒τ*≡ body2-no-τ post)

body2-wev-inv : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
              → body2 ═[ ev (evl (evLabel A e a)) ]═► t′
              → t′ ≡ Skip
body2-wev-inv (wev pre vis post)
  with noτ⇒τ*≡ body2-no-τ pre
... | refl with body2-ev-inv vis
...   | refl = sym (noτ⇒τ*≡ Skip-no-τ post)
```

## Task 4: Terminator refutations

`VM_body_impl` and `body2` are `react` nodes, never `ret`; they offer visible
events; and they have no τ-steps. All three terminator shapes (`done`/`stuck`/
`div`) are therefore impossible.

```agda
-- Not done: force is `react …`, never `ret r`.
VM_body_impl-not-done : ∀ {r} → PTree.force VM_body_impl ≡ ret r → ⊥
VM_body_impl-not-done ()

body2-not-done : ∀ {r} → PTree.force body2 ≡ ret r → ⊥
body2-not-done ()

-- Not stuck: feed the IsStuck proof a real visible step.
-- VM_body_impl offers coin; body2 offers coffee.
VM_body_impl-not-stuck : IsStuck VM_body_impl → ⊥
VM_body_impl-not-stuck stk =
  stk (sVis {at = ⊤ , coin} {a = tt} refl
            (Prefix-cont-just coin (λ _ → body2) tt))

body2-not-stuck : IsStuck body2 → ⊥
body2-not-stuck stk =
  stk (sVis {at = ⊤ , coffee} {a = tt} refl
            (cong (mergeMaybe nothing) (refl {x = just Skip})))

-- Not divergent: a Diverges record exposes a τ-step, refuted by the no-τ lemmas.
VM_body_impl-not-div : Diverges VM_body_impl → ⊥
VM_body_impl-not-div d = VM_body_impl-no-τ (d .Diverges.step)

body2-not-div : Diverges body2 → ⊥
body2-not-div d = body2-no-τ (d .Diverges.step)
```

## Task 4 (body level): event-pinning step inversions

When a `Trace ⊤ t` is `step {e} st rest`, the carried `e : Event√ ⊤` is a
free variable; to read it off the frame we must invert the weak step and pin
`e`.  A weak step from a stable (τ-free) state collapses to a single strong
step, which is either `sRet` (event `√`) — impossible because the state is a
`react`, never a `ret` — or `sVis`, whose event is `evl (evLabel …)` with the
channel forced by the offer map.  These strengthened inversions expose the
event constructor *and* the successor index together.

```agda
-- A stable state offers no √ (sRet) step: sRet requires force ≡ ret _.
VM_body_impl-no-√ : ∀ {x : ⊤ {lzero}} {t′}
                  → VM_body_impl ─[ ev (√ x) ]─► t′ → ⊥
VM_body_impl-no-√ (sRet eq) = case eq of λ ()

body2-no-√ : ∀ {x : ⊤ {lzero}} {t′}
           → body2 ─[ ev (√ x) ]─► t′ → ⊥
body2-no-√ (sRet eq) = case eq of λ ()

-- Strong-step inversion pinning the event constructor for VM_body_impl.
-- For an arbitrary `e : Event√ ⊤`, a step `VM_body_impl ─[ ev e ]─► t′`
-- forces `e ≡ evl (evLabel ⊤ coin tt)` and `t′ ≡ body2`.
VM_body_impl-ev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
                     → VM_body_impl ─[ ev e ]─► t′
                     → (e ≡ evl (evLabel (⊤ {lzero}) coin tt)) × (t′ ≡ body2)
VM_body_impl-ev-inv′ (sRet eq) = case eq of λ ()
VM_body_impl-ev-inv′ (sVis {at = at} {a = a} refl br) with Prefix-cont-fires br
... | refl , _ , t′≡ = refl , t′≡

-- Strong-step inversion pinning the event for body2: an `e`-step forces
-- `e ≡ evl (evLabel ⊤ tea tt)` OR `e ≡ evl (evLabel ⊤ coffee tt)`, with the
-- successor `Skip` in both cases.
body2-ev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
              → body2 ─[ ev e ]─► t′
              → ((e ≡ evl (evLabel (⊤ {lzero}) tea tt))
                 ⊎ (e ≡ evl (evLabel (⊤ {lzero}) coffee tt)))
                × (t′ ≡ Skip)
body2-ev-inv′ (sRet eq) = case eq of λ ()
body2-ev-inv′ (sVis {at = at} {a = a} eq br)
  with □-vis-inv (tea ⟶₀ Skip) (coffee ⟶₀ Skip) eq br
... | evP stP with ev-inv stP
...   | _ , _ , refl , brP with Prefix-cont-fires brP
...     | refl , _ , t′≡ = inj₁ refl , t′≡
body2-ev-inv′ (sVis {at = at} {a = a} eq br)
  | evQ stQ with ev-inv stQ
...   | _ , _ , refl , brQ with Prefix-cont-fires brQ
...     | refl , _ , t′≡ = inj₂ refl , t′≡
body2-ev-inv′ (sVis {at = at} {a = a} eq br)
  | evPQ stP stQ = ⊥-elim (tea≢coffee-step stP stQ)
```

Lifting to the weak step: the surrounding `─[τ*]─►` closures collapse by the
no-τ lemmas, so the weak event/successor equal the strong ones.

```agda
VM_body_impl-wev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
                      → VM_body_impl ═[ ev e ]═► t′
                      → (e ≡ evl (evLabel (⊤ {lzero}) coin tt)) × (t′ ≡ body2)
VM_body_impl-wev-inv′ (wev pre vis post)
  with noτ⇒τ*≡ VM_body_impl-no-τ pre
... | refl with VM_body_impl-ev-inv′ vis
...   | e≡ , refl = e≡ , sym (noτ⇒τ*≡ body2-no-τ post)

body2-wev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
               → body2 ═[ ev e ]═► t′
               → ((e ≡ evl (evLabel (⊤ {lzero}) tea tt))
                  ⊎ (e ≡ evl (evLabel (⊤ {lzero}) coffee tt)))
                 × (t′ ≡ Skip)
body2-wev-inv′ (wev pre vis post)
  with noτ⇒τ*≡ body2-no-τ pre
... | refl with body2-ev-inv′ vis
...   | e≡ , refl = e≡ , sym (noτ⇒τ*≡ Skip-no-τ post)
```

## Task 4 (body level): trace-shape characterization

With the event pinned and the successor index known, each rooted trace's
frame is fully determined and its tail lives at the named successor state.
The tail `force rest : ∞Trace.force … : Trace ⊤ t′` is transported along
`t′ ≡ body2` / `t′ ≡ Skip` to the index the formula tasks expect.

```agda
-- A trace rooted at VM_body_impl fires `coin`, and its tail is rooted at body2.
rooted-VM⇒coin : (tr : Trace (⊤ {lzero}) VM_body_impl)
               → (frameOf tr ≡ step VM_body_impl (evl (evLabel (⊤ {lzero}) coin tt)))
                 × Trace (⊤ {lzero}) body2
rooted-VM⇒coin (step {e = e} st rest) with VM_body_impl-wev-inv′ st
... | refl , t′≡body2 =
  refl , subst (Trace (⊤ {lzero})) t′≡body2 (force rest)
rooted-VM⇒coin (done eq)  = ⊥-elim (VM_body_impl-not-done eq)
rooted-VM⇒coin (stuck st) = ⊥-elim (VM_body_impl-not-stuck st)
rooted-VM⇒coin (div d)    = ⊥-elim (VM_body_impl-not-div d)

-- A trace rooted at body2 fires tea OR coffee, and its tail is rooted at Skip.
rooted-body2⇒drink : (tr : Trace (⊤ {lzero}) body2)
                   → ((frameOf tr ≡ step body2 (evl (evLabel (⊤ {lzero}) tea tt)))
                      ⊎ (frameOf tr ≡ step body2 (evl (evLabel (⊤ {lzero}) coffee tt))))
                     × Trace (⊤ {lzero}) Skip
rooted-body2⇒drink (step {e = e} st rest) with body2-wev-inv′ st
... | inj₁ refl , t′≡Skip = inj₁ refl , subst (Trace (⊤ {lzero})) t′≡Skip (force rest)
... | inj₂ refl , t′≡Skip = inj₂ refl , subst (Trace (⊤ {lzero})) t′≡Skip (force rest)
rooted-body2⇒drink (done eq)  = ⊥-elim (body2-not-done eq)
rooted-body2⇒drink (stuck st) = ⊥-elim (body2-not-stuck st)
rooted-body2⇒drink (div d)    = ⊥-elim (body2-not-div d)
```

For `Skip = Ret tt`, a rooted trace either is `done` (`force Skip ≡ ret tt`)
or fires `√` (via `sRet`), landing in `deadlock`.  `Skip-no-τ` refutes `div`;
the `stuck` constructor is refuted by exhibiting the `√` step.  We strengthen
the inversion of a weak step from `Skip` to pin the event to `√ tt` and the
successor to `deadlock`.

```agda
-- A step from Skip can only be the √ termination step into deadlock.
Skip-ev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
             → Skip {lzero} ─[ ev e ]─► t′
             → (e ≡ √ tt) × (t′ ≡ deadlock)
Skip-ev-inv′ (sRet refl) = refl , refl
Skip-ev-inv′ (sVis eq _) = case eq of λ ()

Skip-wev-inv′ : ∀ {e : Event√ (⊤ {lzero})} {t′}
              → Skip {lzero} ═[ ev e ]═► t′
              → (e ≡ √ tt) × (t′ ≡ deadlock)
Skip-wev-inv′ (wev pre vis post)
  with noτ⇒τ*≡ Skip-no-τ pre
... | refl with Skip-ev-inv′ vis
...   | e≡ , refl = e≡ , sym (noτ⇒τ*≡ deadlock-no-τ post)

-- Skip is not stuck: it offers the √ step.
Skip-not-stuck : IsStuck (Skip {lzero}) → ⊥
Skip-not-stuck stk = stk (sRet {x = tt} refl)

-- Skip does not diverge: no τ-step.
Skip-not-div : Diverges (Skip {lzero}) → ⊥
Skip-not-div d = Skip-no-τ (d .Diverges.step)

data SkipShape (tr : Trace (⊤ {lzero}) Skip) : Set₁ where
  isDone : frameOf tr ≡ done Skip tt → SkipShape tr
  isTick : frameOf tr ≡ step Skip (√ tt) → Trace (⊤ {lzero}) deadlock → SkipShape tr

rooted-Skip⇒term : (tr : Trace (⊤ {lzero}) Skip) → SkipShape tr
rooted-Skip⇒term (step {e = e} st rest) with Skip-wev-inv′ st
... | refl , t′≡deadlock =
  isTick refl (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
rooted-Skip⇒term (done refl) = isDone refl
rooted-Skip⇒term (stuck st)  = ⊥-elim (Skip-not-stuck st)
rooted-Skip⇒term (div d)     = ⊥-elim (Skip-not-div d)
```

## Task 5: body-level LTL safety `VM_body_impl ⊨ G (atCoin ⇒ X atDrink)`

The atoms only inspect the *frame*, and `⟦ X φ ⟧ tr = ⟦ φ ⟧ (tail tr)`
inspects the frame of the tail.  The Task-4 characterizations return the
tail transported along the successor-index equality, so to turn a frame
fact about the *transported* tail into one about the *actual* `tail tr`
we use that `frameOf` ignores the index `subst`.

```agda
-- frameOf is invariant under the trace's index transport.
frameOf-subst : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree VM (ExtI VM) R}
                  (eq : t ≡ t′) (tr : Trace R t)
              → frameOf (subst (Trace R) eq tr) ≡ frameOf tr
frameOf-subst refl tr = refl

-- A *named* frame predicate matching atCoin's anonymous lambda, so it can be
-- used as a `subst` motive (anonymous extended lambdas have opaque identities
-- and never definitionally agree with a second copy).  We bridge `⟦ atCoin ⟧`
-- into it by *casing on the frame* (where atCoin's lambda reduces concretely).
IsCoinFrame : Frame (⊤ {lzero}) → Set
IsCoinFrame (step _ (evl (evLabel _ coin _)))   = ⊤ {lzero}
IsCoinFrame (step _ (evl (evLabel _ tea _)))    = ⊥
IsCoinFrame (step _ (evl (evLabel _ coffee _))) = ⊥
IsCoinFrame (step _ (√ _))                       = ⊥
IsCoinFrame (done _ _)                           = ⊥
IsCoinFrame (stuck _)                            = ⊥
IsCoinFrame (div _)                              = ⊥

atCoin⇒coinFrame : ∀ {t} (x : Trace (⊤ {lzero}) t)
                 → ⟦ atCoin ⟧ x → IsCoinFrame (frameOf x)
atCoin⇒coinFrame x c with frameOf x
... | step _ (evl (evLabel _ coin _))   = c
... | step _ (evl (evLabel _ tea _))    = c
... | step _ (evl (evLabel _ coffee _)) = c
... | step _ (√ _)                       = c
... | done _ _                           = c
... | stuck _                            = c
... | div _                              = c
```

The canonical implication exported by `Semantics.LTL.Traces_Based`.  Unfolds to
`φ ⇒ ψ = (¬ φ) ∨ ψ = ¬ ((¬¬ φ) ∧ (¬ ψ))`, so
`⟦ φ ⇒ ψ ⟧ tr = (((⟦ φ ⟧ tr → Lift ⊥) → Lift ⊥) × (⟦ ψ ⟧ tr → Lift ⊥)) → Lift ⊥`.
This matches §5.4's `safetyFormula`, and is strictly stronger than the previous
local `_⇒ᵗ_`.

```agda
safetyφᵇ : LTLᵗ lzero (⊤ {lzero})
safetyφᵇ = G (atCoin ⇒ X atDrink)
```

Per-position frame facts about an arbitrary `tr : Trace ⊤ VM_body_impl`.
Each is obtained by casing on `tr`, inverting the leading weak step, and
bridging the Task-4 characterization's transported tail back to the real
tail via `frameOf-subst`.

```agda
-- Position 1: `tail tr` is rooted at body2 and shows a tea-or-coffee frame.
tail-drink-frame : (tr : Trace (⊤ {lzero}) VM_body_impl)
                 → (frameOf (tail tr) ≡ step body2 (evl (evLabel (⊤ {lzero}) tea tt)))
                   ⊎ (frameOf (tail tr) ≡ step body2 (evl (evLabel (⊤ {lzero}) coffee tt)))
tail-drink-frame (step {e = e} st rest) with VM_body_impl-wev-inv′ st
... | refl , t′≡body2
      with rooted-body2⇒drink (subst (Trace (⊤ {lzero})) t′≡body2 (force rest))
        | frameOf-subst t′≡body2 (force rest)
...   | inj₁ fr , _ | fs = inj₁ (trans (sym fs) fr)
...   | inj₂ fr , _ | fs = inj₂ (trans (sym fs) fr)
tail-drink-frame (done eq)  = ⊥-elim (VM_body_impl-not-done eq)
tail-drink-frame (stuck st) = ⊥-elim (VM_body_impl-not-stuck st)
tail-drink-frame (div d)    = ⊥-elim (VM_body_impl-not-div d)
```

At a drink frame the atom `atDrink` is `⊤`, so `⟦ X atDrink ⟧ tr` holds.

```agda
X-atDrink : (tr : Trace (⊤ {lzero}) VM_body_impl) → ⟦ X atDrink ⟧ tr
X-atDrink tr with tail-drink-frame tr
... | inj₁ fr rewrite fr = tt
... | inj₂ fr rewrite fr = tt
```

For positions `≥ 2` the relevant frame is that of `drop n` applied to
some `Trace ⊤ Skip` tail.  A `Skip`-rooted trace never shows a `coin`
frame at any position: it is either `done` (a terminator that stutters,
non-coin) or fires `√` into `deadlock` (the `√` frame is non-coin, and
`deadlock` is `stuck` — again a terminator that stutters).  We need a
`Trace ⊤ deadlock` shape lemma first.

```agda
-- A trace rooted at deadlock (CSP Stop) is `stuck`: it offers no event,
-- never terminates, never diverges.  So every position stutters at the
-- `stuck deadlock` frame.
deadlock-not-done : ∀ {r} → PTree.force (deadlock {E = VM} {I = ExtI VM} {R = ⊤ {lzero}}) ≡ ret r → ⊥
deadlock-not-done ()

deadlock-not-div : Diverges (deadlock {E = VM} {I = ExtI VM} {R = ⊤ {lzero}}) → ⊥
deadlock-not-div d = deadlock-no-τ (d .Diverges.step)

-- deadlock offers no visible step: its react offer map is ∅v (always
-- nothing), so an sVis/sRet step is impossible (mirrors deadlock-no-τ).
deadlock-no-ev : ∀ {e : Event√ (⊤ {lzero})} {t′}
               → deadlock {E = VM} {I = ExtI VM} {R = ⊤ {lzero}} ─[ ev e ]─► t′ → ⊥
deadlock-no-ev (sRet eq)      = case eq of λ ()
deadlock-no-ev (sVis refl br) = case br of λ ()

deadlock-no-wev : ∀ {e : Event√ (⊤ {lzero})} {t′}
                → deadlock {E = VM} {I = ExtI VM} {R = ⊤ {lzero}} ═[ ev e ]═► t′ → ⊥
deadlock-no-wev (wev pre vis post) with noτ⇒τ*≡ deadlock-no-τ pre
... | refl = deadlock-no-ev vis

-- Every Trace ⊤ deadlock is `stuck`, with frame exactly `stuck deadlock`.
deadlock-frame : (s : Trace (⊤ {lzero}) deadlock)
               → frameOf s ≡ stuck deadlock
deadlock-frame (step st _) = ⊥-elim (deadlock-no-wev st)
deadlock-frame (done eq)   = ⊥-elim (deadlock-not-done eq)
deadlock-frame (stuck _)   = refl
deadlock-frame (div d)     = ⊥-elim (deadlock-not-div d)

deadlock-stuck-term : (s : Trace (⊤ {lzero}) deadlock)
                    → IsTerminator (frameOf s)
deadlock-stuck-term s = subst IsTerminator (sym (deadlock-frame s)) tt₀
```

The frame produced by `drop` is invariant under the trace's index
transport (a `drop`-level companion to `frameOf-subst`).

```agda
frameOf-drop-subst : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree VM (ExtI VM) R}
                       (eq : t ≡ t′) (s : Trace R t) (n : ℕ)
                   → frameOf (drop n (subst (Trace R) eq s)) ≡ frameOf (drop n s)
frameOf-drop-subst refl s n = refl
```

A `Skip`-rooted trace never exposes a `coin` frame at any position.  At
`m = 0` the frame is `done` or the `√` step (both non-coin).  For `m ≥ 1`
under `done` the trace stutters at the terminator; under the `√` step the
tail is rooted at `deadlock`, which is `stuck` (a terminator), so the
remaining drop stutters there.

```agda
Skip-noCoin : (m : ℕ) (s : Trace (⊤ {lzero}) Skip)
            → IsCoinFrame (frameOf (drop m s)) → ⊥
-- step from Skip: only the √ termination step into deadlock.
Skip-noCoin zero (step {e = e} st rest) with Skip-wev-inv′ st
... | refl , _ = λ ()
Skip-noCoin (suc m) (step {e = e} st rest) with Skip-wev-inv′ st
... | refl , t′≡deadlock
      -- drop (suc m) (step …) = drop m (force rest); transport force rest to
      -- deadlock, where it stutters (deadlock is stuck) at the `stuck deadlock`
      -- frame (non-coin), then bridge frames.
      rewrite sym (frameOf-drop-subst t′≡deadlock (force rest) m)
      | drop-stutter m (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
                       (deadlock-stuck-term (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest)))
      | frameOf-subst (sym (dropIdx-stutter m (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
                              (deadlock-stuck-term (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest)))))
                      (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
      | deadlock-frame (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
      = λ ()
-- done Skip: `tail (done refl) = done refl`, so `drop m (done refl)` reduces
-- to `done refl` by induction on m; at the `done` frame atCoin is ⊥.
Skip-noCoin zero    (done refl) = λ ()
Skip-noCoin (suc m) (done refl) = Skip-noCoin m (done refl)
Skip-noCoin m (stuck st)  = ⊥-elim (Skip-not-stuck st)
Skip-noCoin m (div d)     = ⊥-elim (Skip-not-div d)
```

For positions `≥ 2` we need a genuine `Trace ⊤ Skip` whose `drop n` frame
matches `frameOf (drop (suc (suc n)) tr) = frameOf (drop n (tail (tail tr)))`.
`tail (tail tr)` is rooted at `tailIdx (tail tr)`; casing `tr` then `tail tr`
and inverting both leading weak steps pins that index to `Skip`, and
`frameOf-drop-subst` bridges the index transport.

```agda
-- Helper: given a body2-rooted trace `b` and its `frameOf (drop n b)` linked
-- to the outer trace, produce the Skip bridge.  We split `b` (which is the
-- index-transported tail) so the body2-not-* refutations apply directly.
tail²-from-body2 : (b : Trace (⊤ {lzero}) body2) (n : ℕ)
                 → Σ[ s ∈ Trace (⊤ {lzero}) Skip ]
                     (frameOf (drop n s) ≡ frameOf (drop (suc n) b))
tail²-from-body2 (step {e = e2} st2 rest2) n with body2-wev-inv′ st2
... | _ , t′≡Skip =
        subst (Trace (⊤ {lzero})) t′≡Skip (force rest2)
        , frameOf-drop-subst t′≡Skip (force rest2) n
tail²-from-body2 (done eq)  n = ⊥-elim (body2-not-done eq)
tail²-from-body2 (stuck st) n = ⊥-elim (body2-not-stuck st)
tail²-from-body2 (div d)    n = ⊥-elim (body2-not-div d)

tail²-bridge : (tr : Trace (⊤ {lzero}) VM_body_impl) (n : ℕ)
             → Σ[ s ∈ Trace (⊤ {lzero}) Skip ]
                 (frameOf (drop n s) ≡ frameOf (drop (suc (suc n)) tr))
tail²-bridge (step {e = e} st rest) n with VM_body_impl-wev-inv′ st
... | refl , t′≡body2
      -- drop (suc (suc n)) (step st rest) = drop (suc n) (force rest).
      -- Transport force rest to body2, recurse, bridge the frame back.
      with tail²-from-body2 (subst (Trace (⊤ {lzero})) t′≡body2 (force rest)) n
...     | s , fr =
          s , trans fr (frameOf-drop-subst t′≡body2 (force rest) (suc n))
tail²-bridge (done eq)  n = ⊥-elim (VM_body_impl-not-done eq)
tail²-bridge (stuck st) n = ⊥-elim (VM_body_impl-not-stuck st)
tail²-bridge (div d)    n = ⊥-elim (VM_body_impl-not-div d)
```

The safety theorem.  Structure mirrors the §5.4 witness `safety`, but
each position's frame comes from the characterization rather than a
concrete trace, and the `≥ 2` case routes through the `Skip` tail's
`noCoin` lemma.

```agda
vm-safety : VM_body_impl ⊨ (G (atCoin ⇒ X atDrink))
vm-safety tr = ⟦G⟧⁺⇒⟦G⟧ {φ = atCoin ⇒ X atDrink} {tr = tr} (go tr)
  where
    go : (tr : Trace (⊤ {lzero}) VM_body_impl)
       → ⟦G⟧⁺ (atCoin ⇒ X atDrink) tr
    -- The canonical antecedent unfolds (mirrors §5.4 safety⁺) to
    -- ⟦ atCoin ⇒ X atDrink ⟧ tr
    --   = (((⟦ atCoin ⟧ tr → Lift ⊥) → Lift ⊥) × (⟦ X atDrink ⟧ tr → Lift ⊥)) → Lift ⊥
    -- so the antecedent is (notnotCoin , notDrink).
    -- pos 0: discharge via the X atDrink component.
    go tr zero (_ , notDrink) = notDrink (X-atDrink tr)
    -- pos 1: drop 1 tr = tail tr, whose frame is a drink frame, so
    -- ⟦ atCoin ⟧ there reduces to ⊥ (via IsCoinFrame); feed that to ¬¬ atCoin.
    -- (mirrors §5.4 safety⁺ (suc zero), where the concrete coffee frame makes
    -- the same atCoin = ⊥ obvious.)
    go tr (suc zero) (notnotCoin , _) =
      notnotCoin
        (λ coinp → ⊥-elim
          (case tail-drink-frame tr of λ
            { (inj₁ fr) → subst IsCoinFrame fr (atCoin⇒coinFrame (tail tr) coinp)
            ; (inj₂ fr) → subst IsCoinFrame fr (atCoin⇒coinFrame (tail tr) coinp)
            }))
    -- pos ≥ 2: drop (2+n) tr = drop n (tail (tail tr)); the doubly-tailed
    -- trace is Skip-rooted (Task 4) and never shows a coin frame, so the
    -- composite (⟦ atCoin ⟧ → ⊥) feeds ¬¬ atCoin (mirrors §5.4 safety⁺ (suc (suc n))).
    go tr (suc (suc n)) (notnotCoin , _) with tail²-bridge tr n
    ... | s , fr =
            notnotCoin
              (λ coinp → ⊥-elim
                (Skip-noCoin n s
                  (subst IsCoinFrame (sym fr)
                    (atCoin⇒coinFrame (drop (suc (suc n)) tr) coinp))))
```

## Task 6: body-level liveness `F atDrink` and until `atCoin U atDrink`

Both formulas pin the witness at `n = 1` (drink fires one step after coin).
`drop 1 tr = tail tr` definitionally, so `⟦ atDrink ⟧ (drop 1 tr)` is exactly
the safety helper `X-atDrink tr : ⟦ X atDrink ⟧ tr = ⟦ atDrink ⟧ (tail tr)`.

```agda
-- `⟦ atDrink ⟧ (drop 1 tr)` reuses the safety helper `X-atDrink`.
atDrink-pos1 : (tr : Trace (⊤ {lzero}) VM_body_impl)
             → ⟦ atDrink ⟧ (drop 1 tr)
atDrink-pos1 = X-atDrink

-- `⟦ atCoin ⟧ tr`: the rooted-trace characterization pins the frame to the
-- coin step, where `atCoin`'s atom predicate reduces to `⊤ {lzero}`.
atCoin-pos0 : (tr : Trace (⊤ {lzero}) VM_body_impl)
            → ⟦ atCoin ⟧ tr
atCoin-pos0 tr rewrite proj₁ (rooted-VM⇒coin tr) = tt
```

Liveness `F atDrink = ⊤' U atDrink`: witness `n = 1`, drink there, and the
single earlier position (`m < 1` ⇒ `m = 0`) trivially satisfies `⊤'`.

```agda
vm-liveness : VM_body_impl ⊨ (F atDrink)
vm-liveness tr = 1 , atDrink-pos1 tr , λ _ _ → lift tt₀
```

Until `atCoin U atDrink`: same witness `n = 1`; the only earlier position
is `m = 0`, where `atCoin` holds (`atCoin-pos0`); `m ≥ 1` is absurd.

```agda
vm-until : VM_body_impl ⊨ (atCoin U atDrink)
vm-until tr = 1 , atDrink-pos1 tr
            , λ { zero _ → atCoin-pos0 tr ; (suc _) (s≤s ()) }
```

## Task 7: body-level termination-reaching `F (atDone _ ∨ atStuck)`

The post-drink `Skip` terminates one of two ways: a `done Skip tt` frame, or a
`√`-step into `deadlock` (which is `stuck`).  So the branch-independent
"reaches a terminated state" formula is `F (atDone _ ∨ atStuck)`: the `done`
tail satisfies the left disjunct at position 2, the `√`-then-`deadlock` tail
the right disjunct at position 3.  (`F atDone` alone would be false for the
`√`-tail.)

We need the `atDone`/`atStuck` atoms in scope; add them to the import list.

```agda
-- Pull atDone/atStuck into scope (already imported above via the `using`).
termφᵇ : LTLᵗ lzero (⊤ {lzero})
termφᵇ = F (atDone (λ _ → ⊤ {lzero}) ∨ atStuck)
```

First a `∀ k`-strength variant of the doubly-tailed Skip bridge: every `drop k`
frame of the Skip tail matches the `drop (2 + k)` frame of `tr`.  The proof
mirrors `tail²-from-body2` / `tail²-bridge` but keeps `n` universally
quantified (each step is `frameOf-drop-subst`, which holds for every index).

```agda
tail²-from-body2-∀ : (b : Trace (⊤ {lzero}) body2)
                   → Σ[ s ∈ Trace (⊤ {lzero}) Skip ]
                       (∀ k → frameOf (drop k s) ≡ frameOf (drop (suc k) b))
tail²-from-body2-∀ (step {e = e2} st2 rest2) with body2-wev-inv′ st2
... | _ , t′≡Skip =
        subst (Trace (⊤ {lzero})) t′≡Skip (force rest2)
        , λ k → frameOf-drop-subst t′≡Skip (force rest2) k
tail²-from-body2-∀ (done eq)  = ⊥-elim (body2-not-done eq)
tail²-from-body2-∀ (stuck st) = ⊥-elim (body2-not-stuck st)
tail²-from-body2-∀ (div d)    = ⊥-elim (body2-not-div d)

tail²-bridge-∀ : (tr : Trace (⊤ {lzero}) VM_body_impl)
               → Σ[ s ∈ Trace (⊤ {lzero}) Skip ]
                   (∀ k → frameOf (drop k s) ≡ frameOf (drop (suc (suc k)) tr))
tail²-bridge-∀ (step {e = e} st rest) with VM_body_impl-wev-inv′ st
... | refl , t′≡body2
      with tail²-from-body2-∀ (subst (Trace (⊤ {lzero})) t′≡body2 (force rest))
...     | s , fr =
          s , λ k → trans (fr k) (frameOf-drop-subst t′≡body2 (force rest) (suc k))
tail²-bridge-∀ (done eq)  = ⊥-elim (VM_body_impl-not-done eq)
tail²-bridge-∀ (stuck st) = ⊥-elim (VM_body_impl-not-stuck st)
tail²-bridge-∀ (div d)    = ⊥-elim (VM_body_impl-not-div d)
```

Named frame predicates matching the anonymous lambdas inside `atDone (λ _ → ⊤)`
and `atStuck`, so we can transport an atom witness along a frame equality with
`subst` (the extended lambdas have opaque identities; we bridge by casing on
the frame, exactly as `atCoin⇒coinFrame` does).

```agda
-- ⟦ atDone (λ _ → ⊤) ⟧ x reduces to this on the frame.
IsDoneFrame⊤ : Frame (⊤ {lzero}) → Set lzero
IsDoneFrame⊤ (step _ _) = Lift lzero ⊥
IsDoneFrame⊤ (done _ _) = ⊤ {lzero}
IsDoneFrame⊤ (stuck _)  = Lift lzero ⊥
IsDoneFrame⊤ (div _)    = Lift lzero ⊥

doneFrame⇒atDone : ∀ {t} (x : Trace (⊤ {lzero}) t)
                 → IsDoneFrame⊤ (frameOf x) → ⟦ atDone (λ _ → ⊤ {lzero}) ⟧ x
doneFrame⇒atDone x p with frameOf x
... | step _ _ = p
... | done _ _ = p
... | stuck _  = p
... | div _    = p

-- ⟦ atStuck ⟧ x reduces to this on the frame.
IsStuckFrame : Frame (⊤ {lzero}) → Set lzero
IsStuckFrame (step _ _) = ⊥
IsStuckFrame (done _ _) = ⊥
IsStuckFrame (stuck _)  = ⊤₀
IsStuckFrame (div _)    = ⊥

stuckFrame⇒atStuck : ∀ {t} (x : Trace (⊤ {lzero}) t)
                   → IsStuckFrame (frameOf x) → ⟦ atStuck ⟧ x
stuckFrame⇒atStuck x p with frameOf x
... | step _ _ = p
... | done _ _ = p
... | stuck _  = p
... | div _    = p
```

Two small lemmas the theorem's `√`-branch needs: `frameOf (drop 1 s) ≡
frameOf (tail s)` (definitional, `drop 1 s = tail s`), and that at a `√`-step
Skip trace the tail is `deadlock`-rooted so its frame is `stuck deadlock`.

```agda
frameOf-drop1-tail : (s : Trace (⊤ {lzero}) Skip)
                   → frameOf (drop 1 s) ≡ frameOf (tail s)
frameOf-drop1-tail s = refl

-- At a `√`-step Skip trace, the tail (= drop 1 s) is the deadlock-rooted `d`
-- carried by isTick; its frame is `stuck deadlock`.
deadlock-frame-of-tick : (s : Trace (⊤ {lzero}) Skip)
                       → frameOf s ≡ step Skip (√ tt)
                       → (d : Trace (⊤ {lzero}) deadlock)
                       → frameOf (tail s) ≡ stuck deadlock
deadlock-frame-of-tick (step {e = e} st rest) _ _ with Skip-wev-inv′ st
... | refl , t′≡deadlock
      rewrite sym (frameOf-subst t′≡deadlock (force rest)) =
        deadlock-frame (subst (Trace (⊤ {lzero})) t′≡deadlock (force rest))
deadlock-frame-of-tick (done refl) () _
deadlock-frame-of-tick (stuck st)  _  _ = ⊥-elim (Skip-not-stuck st)
deadlock-frame-of-tick (div d)     _  _ = ⊥-elim (Skip-not-div d)
```

The termination-reaching theorem.  Reach the post-drink Skip tail `s` at
position 2 via `tail²-bridge-∀`, and case on `rooted-Skip⇒term s`.

- `isDone`: `frameOf (drop 2 tr) ≡ frameOf s ≡ done Skip tt`, so the left
  disjunct `atDone` holds at position `n = 2`.
- `isTick d`: `frameOf (drop 3 tr) ≡ frameOf (drop 1 s) ≡ frameOf (tail s)`,
  and the `√`-step's tail is the `deadlock`-rooted `d`, whose frame is
  `stuck deadlock` (`deadlock-frame`), so the right disjunct `atStuck` holds at
  position `n = 3`.  Here `drop 1 s = tail s`, and casing `s = step …` makes
  `tail s` definitionally the transported tail; the `isTick` constructor's
  carried `d` is exactly that tail (see `rooted-Skip⇒term`'s `step` clause).

The `_∨_` witness has shape
`((⟦L⟧ x → Lift ⊥) × (⟦R⟧ x → Lift ⊥)) → Lift ⊥`; we feed the relevant
disjunct's proof to the matching negation.

```agda
vm-terminates : VM_body_impl ⊨ (F (atDone (λ _ → ⊤ {lzero}) ∨ atStuck))
vm-terminates tr with tail²-bridge-∀ tr
... | s , brk with rooted-Skip⇒term s
...   | isDone frₛ =
          2
        , (λ { (notDone , _) →
                 notDone (doneFrame⇒atDone (drop 2 tr)
                            (subst IsDoneFrame⊤
                               (trans (sym frₛ) (brk 0)) tt)) })
        , (λ _ _ → lift tt₀)
...   | isTick frₛ d =
          3
        , (λ { (_ , notStuck) →
                 notStuck (stuckFrame⇒atStuck (drop 3 tr)
                            (subst IsStuckFrame
                               (trans (sym frₛ-tail) (brk 1)) tt₀)) })
        , (λ _ _ → lift tt₀)
  where
    -- `drop 1 s = tail s`; `s` fired `√`, so `tail s` is the deadlock tail,
    -- whose frame is `stuck deadlock`.  `rooted-Skip⇒term`'s isTick carries
    -- that very tail as `d`, and `deadlock-frame d` gives its frame.
    frₛ-tail : frameOf (drop 1 s) ≡ stuck deadlock
    frₛ-tail = trans (frameOf-drop1-tail s) (deadlock-frame-of-tick s frₛ d)
```

## Branch-independence: which §5.4 witness properties do NOT lift to ⊨

The four theorems above (`vm-safety`, `vm-liveness`, `vm-until`,
`vm-terminates`) are **branch-independent**: they hold for every coherent trace
rooted at `VM_body_impl`, regardless of whether the `□` external choice
resolves to the tea branch or the coffee branch.  In contrast, several §5.4
witness-trace properties from `VendingMachine.lagda.md` are deliberately NOT
lifted to `⊨` claims, because they depend on the specific choice made in
`sampleTrace` (the coffee run) and are **false** as process-level claims.

**Properties that are false as `⊨` claims:**

- `neverTea` (`G (¬ atTea)`): false at the process level.  The tea branch
  serves tea: a tea-run trace has a `tea` frame at position 1, so
  `⟦ G (¬ atTea) ⟧` fails there.  The `⊨` quantifier forces the formula to
  hold for *every* coherent trace, including the tea branch.

- `F atCoffee`: false at the process level.  A tea-run trace (coin → tea → √)
  never visits a `coffee` frame at any position; the `F` existential therefore
  fails.

- `startThenCoffee` (`atCoin ∧ X atCoffee`): false at the process level.  On
  a tea-run trace, position 1 shows a `tea` frame, not `coffee`, so
  `X atCoffee` fails.

- `coffeeThenDone` (`F (atCoffee ∧ X (atDone _))`): false at the process
  level for the same reason — the tea branch never exhibits a `coffee` frame.

These four are witness properties of a specific trace and are not invariants of
the process.  Lifting them to `⊨` would require the process to always choose
coffee, but `VM_body_impl` uses `□` (external choice), so either drink may be
served.

**Properties that DO lift (the four proved above):**

- Safety `G (atCoin ⇒ X atDrink)`: after every coin, the next observation is
  a drink — tea or coffee both satisfy `atDrink`.
- Liveness `F atDrink`: a drink is always served, regardless of which branch.
- Until `atCoin U atDrink`: coin holds until the drink fires, in every run.
- Termination-reaching `F (atDone _ ∨ atStuck)`: every run reaches a
  terminated state — via `done` (the `Skip` terminates normally) or via
  `atStuck` (the `√`-then-deadlock tail).  Note that `F atDone` alone does NOT
  lift: the `√`-into-`deadlock` tail terminates via `atStuck` (the deadlock
  frame), not `atDone`, so the disjunction is necessary.

**Remark on `¬ (VM_body_impl ⊨ F atCoffee)`.** A formal counter-witness would
construct a coherent tea-branch `Trace ⊤ VM_body_impl` (coin → tea → √ →
deadlock) and show that `F atCoffee` fails on it — since no position ever
shows a `coffee` frame.  Deriving `⊥` from a hypothetical `VM_body_impl ⊨ F
atCoffee` applied to that trace is straightforward in principle (the `F`
witness position must be 0, 1, 2, or 3, and each is refuted by casing the
frame), but is omitted here as the branch-independence point is fully made by
the prose argument above.  The optional counter-witness proof is left as an
exercise.

## Task 9: Loop-level force-shape and terminator refutations (stretch)

`VM_impl = loop0 VM_body_impl = iter (loop's step) tt = iter-bind (VM_body_impl
>>= loop-k) (loop's step)`.  Since `force VM_body_impl = react (Prefix-cont coin
…) ∅t`, the `>>=` layer maps the empty τ-part to empty and the `iter-bind` layer
likewise: `force VM_impl` is a `react` whose τ-part is `nothing` everywhere (NO
leading τ-step) and whose vis-part still OFFERS `coin` at `(⊤ , coin)`.  These
refutations are fully constructive — no coinduction needed.

```agda
-- Not done: force VM_impl is `react …`, never `ret r` (and R = ⊥ anyway).
VM_impl-not-done : ∀ {r} → PTree.force VM_impl ≡ ret r → ⊥
VM_impl-not-done ()

-- No τ-step: the head react's τ-part is `nothing` everywhere (the body's empty
-- ∅t survives both the >>= and iter-bind layers), so refute sSil/sTau.
VM_impl-no-τ : ∀ {t′} → VM_impl ─[ τ ]─► t′ → ⊥
VM_impl-no-τ (sSil eq)      = case eq of λ ()
VM_impl-no-τ (sTau refl br) = case br of λ ()

-- Not divergent: a Diverges record exposes a τ-step, refuted by VM_impl-no-τ.
VM_impl-not-div : Diverges VM_impl → ⊥
VM_impl-not-div d = VM_impl-no-τ (d .Diverges.step)

-- Not stuck: feed the real coin step.  The head react offers `coin` at
-- (⊤ , coin): the vis-part is `iterV step (react (bindV loop-k …) …)`, which on
-- (⊤ , coin) tt computes through `bindV loop-k (react (Prefix-cont coin …) ∅t)`
-- and `Prefix-cont coin … (⊤ , coin) tt = just (body2)` (VM-AnyTypes-≟ reflexive)
-- to `just (iter-bind (body2 >>= loop-k) step)`.  So `refl` discharges the offer.
VM_impl-not-stuck : IsStuck VM_impl → ⊥
VM_impl-not-stuck stk = stk (sVis {at = ⊤ , coin} {a = tt} refl refl)
```

## Task 10: Loop-level visible-step inversion (coin/drink cycle, stretch)

`VM_impl = loop0 VM_body_impl` unfolds *definitionally* (`loop0-unfold`) to
`iter-bind (loopStep VM_body_impl tt) (loopStep VM_body_impl)`.  We name the
loop's iteration body `step = loopStep VM_body_impl` (top-level copies from
`CSP.Laws.FD.IterateFD`, which are eta-equal to `loop0`'s private `where` step),
and `P₁` the post-coin state.

```agda
open import CSP.Laws.FD.IterateFD VM-AnyTypes-≟ using (loop-k; loopStep; loop-back-sil; loop0-unfold)

-- The loop's iteration step (R = ⊥, matching VM_impl : PTree VM (ExtI VM) ⊥).
vmStep : ⊤ {lzero} → PTree VM (ExtI VM) (⊤ {lzero} ⊎ ⊥)
vmStep = loopStep VM_body_impl

-- The post-coin loop state: after firing `coin` from `VM_impl`, the body's
-- continuation `body2` is spliced under the `>>= loop-k` / `iter-bind step`
-- layers.  This is the index that `VM_impl`'s coin offer computes to.
P₁ : PTree VM (ExtI VM) ⊥
P₁ = iter-bind (body2 >>= loop-k) vmStep
```

`VM_impl` is a `react` (never `ret`), so it offers no `√`/`sRet` step.  A
visible step inverts through `ev-inv`: the head react's vis-part, on the offered
event, fires only on `(⊤ , coin)` (the body's `Prefix-cont coin` survives the
`>>=`/`iter-bind` layers), with successor exactly `P₁`.

```agda
VM_impl-no-√ : ∀ {x : ⊥} {t′}
             → VM_impl ─[ ev (√ x) ]─► t′ → ⊥
VM_impl-no-√ (sRet eq) = case eq of λ ()

-- The vis-offer map of `force VM_impl`, applied to event (A , e), fires only on
-- `(⊤ , coin)` and returns `just P₁`.  Splitting on `VM-AnyTypes-≟ (⊤ , coin)
-- (A , e)` reduces the nested `iterV step (bindV loop-k (Prefix-cont coin …))`
-- offer (whose innermost `with` is exactly that `E-≟`).
VM_impl-offer-fires : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
                    → iterV vmStep (react (bindV loop-k (react (Prefix-cont coin (λ _ → body2)) ∅t)) (bindT loop-k (react (Prefix-cont coin (λ _ → body2)) ∅t))) (A , e) a ≡ just t′
                    → ((⊤ {lzero} , coin) ≡ (A , e)) × (t′ ≡ P₁)
VM_impl-offer-fires {A = A} {e = e} {a = a} br with VM-AnyTypes-≟ (⊤ {lzero} , coin) (A , e)
... | yes refl = refl , sym (just-injective br)
... | no ¬eq   = ⊥-elim (case br of λ ())
```

```agda
-- Strong-step inversion pinning the event for VM_impl: a step `VM_impl ─[ ev e ]─► t′`
-- forces `e ≡ evl (evLabel ⊤ coin tt)` and `t′ ≡ P₁`.
VM_impl-ev-inv′ : ∀ {e : Event√ ⊥} {t′}
                → VM_impl ─[ ev e ]─► t′
                → (e ≡ evl (evLabel (⊤ {lzero}) coin tt)) × (t′ ≡ P₁)
VM_impl-ev-inv′ (sRet eq) = case eq of λ ()
VM_impl-ev-inv′ (sVis {at = at} {a = a} refl br) with VM_impl-offer-fires br
... | refl , t′≡ = refl , t′≡
```

The post-coin state `P₁` is itself stable: `body2`'s empty internal part
survives the `>>= loop-k` and `iter-bind vmStep` layers, so the head react's
τ-part is `nothing` everywhere (no leading/trailing τ at `P₁`).

```agda
-- The τ-part is `iterT vmStep (… bindT loop-k (… □-mt …))`, which threads
-- body2's `□-mt` τ-part through.  As in `body2-no-τ`, splitting the index head
-- and (for `pair fin i`) the tag reduces `□-mt` to `nothing`, then `bindT`/`iterT`
-- map `nothing` to `nothing`.
P₁-no-τ : ∀ {t′} → P₁ ─[ τ ]─► t′ → ⊥
P₁-no-τ (sSil eq)      = case eq of λ ()
P₁-no-τ (sTau {i = i} {a = a} refl br)
  with i   | a
... | _ , base _            | _               = case br of λ ()
... | _ , fin               | _               = case br of λ ()
... | _ , pair (base _) _   | _               = case br of λ ()
... | _ , pair (pair _ _) _ | _               = case br of λ ()
... | _ , pair fin _        | lift fzero              , _ = case br of λ ()
... | _ , pair fin _        | lift (fsuc fzero)       , _ = case br of λ ()
... | _ , pair fin _        | lift (fsuc (fsuc _))    , _ = case br of λ ()
```

Lifting to the weak step: `VM_impl` has no τ (leading τ* collapses) and `P₁`
has no τ (trailing τ* collapses), so the weak event/successor equal the strong
ones.  This is the loop-level analogue of `VM_body_impl-wev-inv′`.

```agda
VM_impl-wev-inv : ∀ {e : Event√ ⊥} {t′}
                → VM_impl ═[ ev e ]═► t′
                → (e ≡ evl (evLabel (⊤ {lzero}) coin tt)) × (t′ ≡ P₁)
VM_impl-wev-inv (wev pre vis post)
  with noτ⇒τ*≡ VM_impl-no-τ pre
... | refl with VM_impl-ev-inv′ vis
...   | e≡ , refl = e≡ , sym (noτ⇒τ*≡ P₁-no-τ post)
```

### The drink step from `P₁` loops back to `VM_impl`

From `P₁` a visible `tea`/`coffee` step lands at the post-drink state `P₂`,
where `force (Skip >>= loop-k) ≡ ret (inj₁ tt)` makes the `iter-bind` node
do a single `sil` τ back to `loop0 VM_body_impl = VM_impl` (the period-2
loop-back).  No `√` appears in the loop.

```agda
-- The post-drink loop state.  `force (Skip >>= loop-k) = ret (inj₁ tt)`, so by
-- `loop-back-sil` this iter-bind node forces to `sil (loop0 VM_body_impl)`.
P₂ : PTree VM (ExtI VM) ⊥
P₂ = iter-bind (Skip >>= loop-k) vmStep

-- `P₁`'s vis-offer map fires only on `(⊤ , tea)` or `(⊤ , coffee)`, each with
-- successor `P₂`.  The offer threads `body2`'s `mergeVis` (which fires Skip on
-- either drink) through the `bindV loop-k` / `iterV vmStep` layers.
P₁-offer-fires : ∀ {A : Set lzero} {e : VM A} {a : A} {t′}
               → iterV vmStep
                   (react (bindV loop-k (react (mergeVis (viewV (react (Prefix-cont tea (λ _ → Skip)) ∅t))
                                                          (viewV (react (Prefix-cont coffee (λ _ → Skip)) ∅t)))
                                               (□-mt (react (Prefix-cont tea (λ _ → Skip)) ∅t)
                                                     (react (Prefix-cont coffee (λ _ → Skip)) ∅t)
                                                     (tea ⟶₀ Skip) (coffee ⟶₀ Skip))))
                          (bindT loop-k (react (mergeVis (viewV (react (Prefix-cont tea (λ _ → Skip)) ∅t))
                                                         (viewV (react (Prefix-cont coffee (λ _ → Skip)) ∅t)))
                                              (□-mt (react (Prefix-cont tea (λ _ → Skip)) ∅t)
                                                    (react (Prefix-cont coffee (λ _ → Skip)) ∅t)
                                                    (tea ⟶₀ Skip) (coffee ⟶₀ Skip)))))
                   (A , e) a ≡ just t′
               → (((⊤ {lzero} , tea) ≡ (A , e)) ⊎ ((⊤ {lzero} , coffee) ≡ (A , e))) × (t′ ≡ P₂)
P₁-offer-fires {A = A} {e = e} {a = a} br
  with VM-AnyTypes-≟ (⊤ {lzero} , tea) (A , e)
... | yes refl = inj₁ refl , sym (just-injective br)
... | no _ with VM-AnyTypes-≟ (⊤ {lzero} , coffee) (A , e)
...   | yes refl = inj₂ refl , sym (just-injective br)
...   | no _     = ⊥-elim (case br of λ ())
```

```agda
-- Strong-step inversion at P₁: a step `P₁ ─[ ev e ]─► t′` forces the event to
-- tea-or-coffee and the successor to `P₂`.  `P₁` is a react (never ret), so no √.
P₁-no-√ : ∀ {x : ⊥} {t′} → P₁ ─[ ev (√ x) ]─► t′ → ⊥
P₁-no-√ (sRet eq) = case eq of λ ()

P₁-ev-inv′ : ∀ {e : Event√ ⊥} {t′}
           → P₁ ─[ ev e ]─► t′
           → ((e ≡ evl (evLabel (⊤ {lzero}) tea tt)) ⊎ (e ≡ evl (evLabel (⊤ {lzero}) coffee tt)))
             × (t′ ≡ P₂)
P₁-ev-inv′ (sRet eq) = case eq of λ ()
P₁-ev-inv′ (sVis {at = at} {a = a} refl br) with P₁-offer-fires br
... | inj₁ refl , t′≡ = inj₁ refl , t′≡
... | inj₂ refl , t′≡ = inj₂ refl , t′≡
```

`P₂` forces to `sil VM_impl` (the loop-back), so it has *exactly one* step — a
`sSil` τ to `VM_impl` — and no visible / √ step.  `loop-back-sil` packages
`force (Skip >>= loop-k) ≡ ret (inj₁ tt)` into `force P₂ ≡ sil (loop0 …)`.

```agda
-- `force (Skip >>= loop-k) = force (Ret tt >>= loop-k) = force (loop-k tt)
--  = force (Ret (inj₁ tt)) = ret (inj₁ tt)`, by computation.
Skip>>=loop-k-ret : PTree.force (Skip >>= loop-k {R = ⊥}) ≡ ret (inj₁ tt)
Skip>>=loop-k-ret = refl

-- Hence force P₂ ≡ sil (loop0 VM_body_impl) ≡ sil VM_impl.
P₂-force : PTree.force P₂ ≡ sil VM_impl
P₂-force = loop-back-sil VM_body_impl (Skip >>= loop-k) Skip>>=loop-k-ret

-- The single τ-step of P₂ goes to VM_impl; no other step.
P₂-τ-inv : ∀ {t′} → P₂ ─[ τ ]─► t′ → t′ ≡ VM_impl
P₂-τ-inv (sSil eq)      with trans (sym eq) P₂-force
... | refl = refl
P₂-τ-inv (sTau eq _)    with trans (sym eq) P₂-force
... | ()

P₂-no-√ : ∀ {x : ⊥} {t′} → P₂ ─[ ev (√ x) ]─► t′ → ⊥
P₂-no-√ (sRet eq) with trans (sym eq) P₂-force
... | ()

P₂-no-ev : ∀ {e : Event√ ⊥} {t′} → P₂ ─[ ev e ]─► t′ → ⊥
P₂-no-ev (sRet eq)   with trans (sym eq) P₂-force
... | ()
P₂-no-ev (sVis eq _) with trans (sym eq) P₂-force
... | ()
```

A τ*-run from `P₂` reaches either `P₂` (empty) or `VM_impl` (one loop-back τ,
after which `VM_impl` is stable so the run stops): the τ* from `P₂` collapses to
at most the single loop-back.

```agda
τ*-from-P₂ : ∀ {t′} → P₂ ─[τ*]─► t′ → (t′ ≡ P₂) ⊎ (t′ ≡ VM_impl)
τ*-from-P₂ τ*-refl              = inj₁ refl
τ*-from-P₂ (τ*-step P₂→u rest) with P₂-τ-inv P₂→u
... | refl = inj₂ (sym (noτ⇒τ*≡ VM_impl-no-τ rest))
```

### Weak drink inversion `P₁ ═[ev e]═► t′`

`P₁` has no τ (leading τ* collapses) and the visible step lands at `P₂`; the
trailing τ* from `P₂` (by `τ*-from-P₂`) is either empty (`t′ ≡ P₂`) or the
single loop-back (`t′ ≡ VM_impl`).  Both successors are weakly equivalent (a
single internal step apart); the period-2 cycle is the `t′ ≡ VM_impl` arm.

Because `═[_]═►` keeps the trailing τ* arbitrary, the *honest* inversion is the
disjunction below — a weak drink step may stop at `P₂` or take the loop-back to
`VM_impl`.  `P₂` is internally `sil VM_impl` (`P₂-force`), so the two are one τ
apart.

```agda
P₁-wev-inv : ∀ {e : Event√ ⊥} {t′}
           → P₁ ═[ ev e ]═► t′
           → ((e ≡ evl (evLabel (⊤ {lzero}) tea tt)) ⊎ (e ≡ evl (evLabel (⊤ {lzero}) coffee tt)))
             × ((t′ ≡ P₂) ⊎ (t′ ≡ VM_impl))
P₁-wev-inv (wev pre vis post)
  with noτ⇒τ*≡ P₁-no-τ pre
... | refl with P₁-ev-inv′ vis
...   | e≡ , refl = e≡ , τ*-from-P₂ post
```

### Canonical period-2 witnesses

The two canonical weak steps closing the `(coin · drink)^ω` cycle: `VM_impl`
fires `coin` to `P₁`, and `P₁` fires `tea` (resp. `coffee`) and takes the
loop-back τ to `VM_impl`.  Task 11 uses these to build the period-2 trace.

```agda
-- coin: VM_impl ═[coin]═► P₁ (no leading/trailing τ).
VM_impl-coin-step : VM_impl ═[ ev (evl (evLabel (⊤ {lzero}) coin tt)) ]═► P₁
VM_impl-coin-step =
  wev τ*-refl (sVis {at = ⊤ , coin} {a = tt} refl refl) τ*-refl

-- The strong drink steps P₁ ─[tea/coffee]→ P₂ (offer fires to P₂ by refl).
P₁-tea-strong : P₁ ─[ ev (evl (evLabel (⊤ {lzero}) tea tt)) ]─► P₂
P₁-tea-strong = sVis {at = ⊤ , tea} {a = tt} refl refl

P₁-coffee-strong : P₁ ─[ ev (evl (evLabel (⊤ {lzero}) coffee tt)) ]─► P₂
P₁-coffee-strong = sVis {at = ⊤ , coffee} {a = tt} refl refl

-- The loop-back τ* from P₂ to VM_impl (the single sil from P₂-force).
P₂-loopback-τ* : P₂ ─[τ*]─► VM_impl
P₂-loopback-τ* = τ*-step (sSil P₂-force) τ*-refl

-- drink + loop-back: P₁ ═[tea/coffee]═► VM_impl (trailing τ* = the loop-back).
P₁-tea-loopback : P₁ ═[ ev (evl (evLabel (⊤ {lzero}) tea tt)) ]═► VM_impl
P₁-tea-loopback = wev τ*-refl P₁-tea-strong P₂-loopback-τ*

P₁-coffee-loopback : P₁ ═[ ev (evl (evLabel (⊤ {lzero}) coffee tt)) ]═► VM_impl
P₁-coffee-loopback = wev τ*-refl P₁-coffee-strong P₂-loopback-τ*
```

## Task 11: Loop-level coinductive characterization + safety (stretch)

Because `R = ⊥` the loop never terminates: every `Trace ⊥ t` for a loop state
`t ∈ {VM_impl, P₁, P₂}` is a `step` (the three terminator constructors are
all refuted).  The roots cycle `VM_impl →coin P₁ →drink {P₂,VM_impl}`, and
`P₂` is internally `sil VM_impl`, so a weak step from `P₂` absorbs that sil and
exposes the same `coin` step as `VM_impl`.  So at a `VM_impl`- or `P₂`-root the
frame is a coin step; at a `P₁`-root it is a drink step.

### Terminator refutations for `P₁` and `P₂`

```agda
-- P₁ is a react (never ret), offers a visible step (tea), and has no τ.
P₁-not-done : ∀ {r} → PTree.force P₁ ≡ ret r → ⊥
P₁-not-done ()

P₁-not-stuck : IsStuck P₁ → ⊥
P₁-not-stuck stk = stk (sVis {at = ⊤ , tea} {a = tt} refl refl)

P₁-not-div : Diverges P₁ → ⊥
P₁-not-div d = P₁-no-τ (d .Diverges.step)

-- P₂ forces to `sil VM_impl`, so it is never `ret`, it is not stuck (it offers
-- the loop-back τ), and it does not diverge (its single sil leads to the stable
-- VM_impl, refuting an infinite τ-run at the second step).
P₂-not-done : ∀ {r} → PTree.force P₂ ≡ ret r → ⊥
P₂-not-done eq with trans (sym eq) P₂-force
... | ()

P₂-not-stuck : IsStuck P₂ → ⊥
P₂-not-stuck stk = stk (sSil P₂-force)

-- A Diverges P₂ record steps P₂ → next via a τ; that τ must be the loop-back
-- (P₂-τ-inv) landing at VM_impl, whose `rest` field is another Diverges at
-- VM_impl — but VM_impl has no τ, refuted by VM_impl-no-τ.
P₂-not-div : Diverges P₂ → ⊥
P₂-not-div d =
  VM_impl-no-τ {t′ = d .Diverges.rest .Diverges.next}
    (subst (λ u → u ─[ τ ]─► d .Diverges.rest .Diverges.next)
           (P₂-τ-inv (d .Diverges.step))
           (d .Diverges.rest .Diverges.step))
```

### `P₂`'s weak step is a `coin` step to `P₁`

`P₂` has exactly one τ (the loop-back to `VM_impl`), then `VM_impl` offers
`coin`.  A weak step `P₂ ═[ev e]═► t′` therefore absorbs the leading sil and
fires `coin`: the leading τ* is either empty (impossible to fire from `P₂`,
which has no visible step) — so it must take the loop-back — and then becomes a
`VM_impl` weak step.  We invert by casing the leading τ*: it is either
reflexive (then the visible step is from `P₂`, refuted by `P₂-no-ev`) or starts
with the loop-back sil (then the rest is a `VM_impl` weak step inverted by
`VM_impl-ev-inv′`, with empty trailing τ*).

```agda
-- The canonical weak coin step P₂ ═[coin]═► P₁ (loop-back sil, then coin).
P₂-coin-step : P₂ ═[ ev (evl (evLabel (⊤ {lzero}) coin tt)) ]═► P₁
P₂-coin-step =
  wev (τ*-step (sSil P₂-force) τ*-refl)
      (sVis {at = ⊤ , coin} {a = tt} refl refl)
      τ*-refl

P₂-wev-inv : ∀ {e : Event√ ⊥} {t′}
           → P₂ ═[ ev e ]═► t′
           → (e ≡ evl (evLabel (⊤ {lzero}) coin tt)) × (t′ ≡ P₁)
-- Leading τ* reflexive: the visible step is directly from P₂ — impossible.
P₂-wev-inv (wev τ*-refl vis post) = ⊥-elim (P₂-no-ev vis)
-- Leading τ* nonempty: first τ is the loop-back to VM_impl (P₂-τ-inv); after
-- transporting `u ≡ VM_impl`, the residual (rest , vis , post) is a `VM_impl`
-- weak step, inverted by `VM_impl-wev-inv` to coin/P₁.
P₂-wev-inv {e = e} {t′ = t′} (wev (τ*-step P₂→u rest) vis post) =
  VM_impl-wev-inv
    (subst (λ u → u ═[ ev e ]═► t′) (P₂-τ-inv P₂→u) (wev rest vis post))
```

### Loop-state membership and frame classes (over `Frame ⊥`)

A *loop state* is one of the three cycle roots.  We classify frames as a coin
step or a drink step.  The atoms `atCoin`/`atDrink` reduce to these on the
frame (bridged below, exactly as the body-level `IsCoinFrame`).

```agda
-- The three cycle roots.
LoopState : PTree VM (ExtI VM) ⊥ → Set₁
LoopState t = (t ≡ VM_impl) ⊎ (t ≡ P₁) ⊎ (t ≡ P₂)

-- A frame is a coin step.
IsCoinFrame⊥ : Frame ⊥ → Set
IsCoinFrame⊥ (step _ (evl (evLabel _ coin _)))   = ⊤ {lzero}
IsCoinFrame⊥ (step _ (evl (evLabel _ tea _)))    = ⊥
IsCoinFrame⊥ (step _ (evl (evLabel _ coffee _))) = ⊥
IsCoinFrame⊥ (step _ (√ _))                       = ⊥
IsCoinFrame⊥ (done _ _)                           = ⊥
IsCoinFrame⊥ (stuck _)                            = ⊥
IsCoinFrame⊥ (div _)                              = ⊥

-- A frame is a drink (tea or coffee) step.
IsDrinkFrame⊥ : Frame ⊥ → Set
IsDrinkFrame⊥ (step _ (evl (evLabel _ coin _)))   = ⊥
IsDrinkFrame⊥ (step _ (evl (evLabel _ tea _)))    = ⊤ {lzero}
IsDrinkFrame⊥ (step _ (evl (evLabel _ coffee _))) = ⊤ {lzero}
IsDrinkFrame⊥ (step _ (√ _))                       = ⊥
IsDrinkFrame⊥ (done _ _)                           = ⊥
IsDrinkFrame⊥ (stuck _)                            = ⊥
IsDrinkFrame⊥ (div _)                              = ⊥

-- Bridges from the atoms to the frame classes.
atCoin⇒coinFrame⊥ : ∀ {t} (x : Trace ⊥ t)
                  → ⟦ atCoin ⟧ x → IsCoinFrame⊥ (frameOf x)
atCoin⇒coinFrame⊥ x c with frameOf x
... | step _ (evl (evLabel _ coin _))   = c
... | step _ (evl (evLabel _ tea _))    = c
... | step _ (evl (evLabel _ coffee _)) = c
... | step _ (√ _)                       = c
... | done _ _                           = c
... | stuck _                            = c
... | div _                              = c

drinkFrame⊥⇒atDrink : ∀ {t} (x : Trace ⊥ t)
                    → IsDrinkFrame⊥ (frameOf x) → ⟦ atDrink ⟧ x
drinkFrame⊥⇒atDrink x p with frameOf x
... | step _ (evl (evLabel _ coin _))   = p
... | step _ (evl (evLabel _ tea _))    = p
... | step _ (evl (evLabel _ coffee _)) = p
... | step _ (√ _)                       = p
... | done _ _                           = p
... | stuck _                            = p
... | div _                              = p
```

### Per-root trace characterizations

Each root determines its trace's frame class and the loop-state membership of
the tail's index.  Terminators are refuted (`R = ⊥`, so the loop never
terminates; all three states offer a visible weak step and never `ret`).

```agda
-- VM_impl-rooted: coin frame, tail rooted at P₁.
rooted-VMimpl : (s : Trace ⊥ VM_impl)
              → IsCoinFrame⊥ (frameOf s) × (tailIdx s ≡ P₁)
rooted-VMimpl (step {e = e} st rest) with VM_impl-wev-inv st
... | refl , refl = tt , refl
rooted-VMimpl (done eq)  = ⊥-elim (VM_impl-not-done eq)
rooted-VMimpl (stuck st) = ⊥-elim (VM_impl-not-stuck st)
rooted-VMimpl (div d)    = ⊥-elim (VM_impl-not-div d)

-- P₁-rooted: drink frame, tail rooted at P₂ OR VM_impl (both loop states).
rooted-P₁ : (s : Trace ⊥ P₁)
          → IsDrinkFrame⊥ (frameOf s) × ((tailIdx s ≡ P₂) ⊎ (tailIdx s ≡ VM_impl))
rooted-P₁ (step {e = e} st rest) with P₁-wev-inv st
... | inj₁ refl , t′ = tt , t′
... | inj₂ refl , t′ = tt , t′
rooted-P₁ (done eq)  = ⊥-elim (P₁-not-done eq)
rooted-P₁ (stuck st) = ⊥-elim (P₁-not-stuck st)
rooted-P₁ (div d)    = ⊥-elim (P₁-not-div d)

-- P₂-rooted: coin frame (absorbs the loop-back sil), tail rooted at P₁.
rooted-P₂ : (s : Trace ⊥ P₂)
          → IsCoinFrame⊥ (frameOf s) × (tailIdx s ≡ P₁)
rooted-P₂ (step {e = e} st rest) with P₂-wev-inv st
... | refl , refl = tt , refl
rooted-P₂ (done eq)  = ⊥-elim (P₂-not-done eq)
rooted-P₂ (stuck st) = ⊥-elim (P₂-not-stuck st)
rooted-P₂ (div d)    = ⊥-elim (P₂-not-div d)
```

### Loop-state invariant along `drop`

`dropIdx (suc n) tr ≡ tailIdx (drop n tr)` (a `drop`/`tailIdx` commutation),
and the tail of any loop-rooted trace is again a loop state, so every
`dropIdx n tr` is a loop state.

```agda
-- drop/tailIdx commutation. Inducting on n; `dropIdx`/`drop` both recurse via
-- `tail`, so the IH applies to `tail tr` at `n`.
dropIdx-suc : ∀ {ℓr} {R : Set ℓr} {t : PTree VM (ExtI VM) R}
                (n : ℕ) (tr : Trace R t)
              → dropIdx (suc n) tr ≡ tailIdx (drop n tr)
dropIdx-suc zero    tr = refl
dropIdx-suc (suc n) tr = dropIdx-suc n (tail tr)

-- The tail index of a loop-rooted trace is again a loop state.
loop-tail : (t : PTree VM (ExtI VM) ⊥) → LoopState t → (s : Trace ⊥ t)
          → LoopState (tailIdx s)
loop-tail .VM_impl (inj₁ refl)       s = inj₂ (inj₁ (proj₂ (rooted-VMimpl s)))
loop-tail .P₁      (inj₂ (inj₁ refl)) s with proj₂ (rooted-P₁ s)
... | inj₁ t′≡P₂      = inj₂ (inj₂ t′≡P₂)
... | inj₂ t′≡VM_impl = inj₁ t′≡VM_impl
loop-tail .P₂      (inj₂ (inj₂ refl)) s = inj₂ (inj₁ (proj₂ (rooted-P₂ s)))

-- Every position's root is a loop state.
loop-state-drop : (tr : Trace ⊥ VM_impl) (n : ℕ) → LoopState (dropIdx n tr)
loop-state-drop tr zero    = inj₁ refl
loop-state-drop tr (suc n) =
  subst LoopState (sym (dropIdx-suc n tr))
        (loop-tail (dropIdx n tr) (loop-state-drop tr n) (drop n tr))
```

### Frame facts at a position

If a trace's tail is rooted at `P₁`, its tail frame is a drink frame
(`rooted-P₁`), bridged through the index transport by `frameOf-subst`.

```agda
-- The tail of a coin-rooted trace (tailIdx ≡ P₁) shows a drink frame.
tail-is-drink : ∀ {t} (s : Trace ⊥ t)
              → tailIdx s ≡ P₁ → IsDrinkFrame⊥ (frameOf (tail s))
tail-is-drink s eq =
  subst IsDrinkFrame⊥
        (frameOf-subst eq (tail s))
        (proj₁ (rooted-P₁ (subst (Trace ⊥) eq (tail s))))

-- tailIdx and frameOf are invariant under the trace's index transport.
tailIdx-subst : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree VM (ExtI VM) R}
                  (eq : t ≡ t′) (s : Trace R t)
              → tailIdx (subst (Trace R) eq s) ≡ tailIdx s
tailIdx-subst refl s = refl

-- A coin-rooted trace `s` (root ≡ VM_impl or ≡ P₂) has `tailIdx s ≡ P₁`.
coinRoot-tailP₁ : ∀ {t} (s : Trace ⊥ t)
                → (t ≡ VM_impl) ⊎ (t ≡ P₂) → tailIdx s ≡ P₁
coinRoot-tailP₁ s (inj₁ eq) =
  trans (sym (tailIdx-subst eq s)) (proj₂ (rooted-VMimpl (subst (Trace ⊥) eq s)))
coinRoot-tailP₁ s (inj₂ eq) =
  trans (sym (tailIdx-subst eq s)) (proj₂ (rooted-P₂ (subst (Trace ⊥) eq s)))

-- A P₁-rooted trace `s` shows a drink frame, so `atCoin` there is ⊥.
P₁Root-noCoin : ∀ {t} (s : Trace ⊥ t)
              → t ≡ P₁ → IsCoinFrame⊥ (frameOf s) → ⊥
P₁Root-noCoin s eq coinp =
  drink-not-coin (proj₁ (rooted-P₁ (subst (Trace ⊥) eq s)))
                 (subst IsCoinFrame⊥ (sym (frameOf-subst eq s)) coinp)
  where
    -- no frame is both a coin step and a drink step.
    drink-not-coin : ∀ {fr} → IsDrinkFrame⊥ fr → IsCoinFrame⊥ fr → ⊥
    drink-not-coin {step _ (evl (evLabel _ coin _))}   () _
    drink-not-coin {step _ (evl (evLabel _ tea _))}    _  ()
    drink-not-coin {step _ (evl (evLabel _ coffee _))} _  ()
    drink-not-coin {step _ (√ _)}                       () _
    drink-not-coin {done _ _}                           () _
    drink-not-coin {stuck _}                            () _
    drink-not-coin {div _}                              () _
```

### The loop-level safety theorem

`VM_impl ⊨ G (atCoin ⇒ X atDrink)`, with the canonical `_⇒_` exported by
`Semantics.LTL.Traces_Based` (`φ ⇒ ψ = (¬φ) ∨ ψ`), matching the body-level
`vm-safety` exactly.  We prove `⟦G⟧⁺` (a position predicate `∀ n → …`) and lift
via `⟦G⟧⁺⇒⟦G⟧`.  At each position the antecedent unfolds to `(notnotCoin ,
notDrink)`:

- coin root (`VM_impl`/`P₂`): the next position is `P₁`-rooted, a drink frame,
  so `⟦ X atDrink ⟧` holds — discharge via `notDrink`;
- drink root (`P₁`): the current frame is a drink frame, so `atCoin` is ⊥ —
  discharge via `notnotCoin`.

This is **fully constructive** — no postulate.  The period-2 / re-rooting drop
analysis closes under `--guardedness` because `loop-state-drop` recurses
structurally on the position index `n` (via `dropIdx-suc`'s `tail` commutation),
not coinductively, so productivity is never at issue.

```agda
vm-loop-safety : VM_impl ⊨ (G (atCoin ⇒ X atDrink))
vm-loop-safety tr = ⟦G⟧⁺⇒⟦G⟧ {φ = atCoin ⇒ X atDrink} {tr = tr} (go tr)
  where
    go : (tr : Trace ⊥ VM_impl) → ⟦G⟧⁺ (atCoin ⇒ X atDrink) tr
    go tr n with loop-state-drop tr n
    -- coin root (VM_impl): drop (suc n) is P₁-rooted ⇒ drink ⇒ X atDrink.
    ... | inj₁ eq        = λ { (_ , notDrink) →
            notDrink (drinkFrame⊥⇒atDrink (tail (drop n tr))
                        (tail-is-drink (drop n tr)
                          (coinRoot-tailP₁ (drop n tr) (inj₁ eq)))) }
    -- coin root (P₂): same as VM_impl.
    ... | inj₂ (inj₂ eq) = λ { (_ , notDrink) →
            notDrink (drinkFrame⊥⇒atDrink (tail (drop n tr))
                        (tail-is-drink (drop n tr)
                          (coinRoot-tailP₁ (drop n tr) (inj₂ eq)))) }
    -- drink root (P₁): the current frame is a drink frame ⇒ atCoin is ⊥.
    ... | inj₂ (inj₁ eq) = λ { (notnotCoin , _) →
            notnotCoin (λ coinp →
              ⊥-elim (P₁Root-noCoin (drop n tr) eq
                        (atCoin⇒coinFrame⊥ (drop n tr) coinp))) }
```

## Task 12: Loop-level liveness `VM_impl ⊨ G (F atDrink)` (stretch)

A drink recurs forever: at *every* position of *every* loop-rooted trace, a
drink frame is reached within at most one further step.  This is the strongest
loop-level liveness — `G (F atDrink)`, "henceforth, eventually a drink" — with
the canonical `G_`/`F_`/`atDrink` exported by `Semantics.LTL.Traces_Based`.

The key local lemma `loop-F-atDrink` says any loop-rooted trace satisfies
`F atDrink`, with the witness depending on the `LoopState` class:

- `P₁`-root (drink frame *now*): witness `k = 0`; `drop 0 s = s` is the
  drink-framed trace itself (`rooted-P₁`), so `⟦ atDrink ⟧ s` holds and the
  earlier-positions obligation (`∀ m → m < 0`) is vacuous.
- `VM_impl`/`P₂`-root (coin frame now, drink *next*): witness `k = 1`;
  `drop 1 s = tail s` is `P₁`-rooted (`coinRoot-tailP₁`), hence a drink frame
  (`tail-is-drink`), so `⟦ atDrink ⟧ (tail s)` holds; the single earlier
  position `m = 0 < 1` trivially satisfies `⊤'`.

Then `G (F atDrink)` follows by `⟦G⟧⁺⇒⟦G⟧ {φ = F atDrink}`: at each position
`n` the root `dropIdx n tr` is a loop state (`loop-state-drop`), so
`loop-F-atDrink` gives `⟦ F atDrink ⟧ (drop n tr)`.  Everything is structural
in `n` (the position-index drop analysis of `vm-loop-safety`), reusing the
Task-11 re-rooting lemmas, so productivity is never at issue.

```agda
-- A loop-rooted trace satisfies `F atDrink`: a drink frame within ≤ 1 step.
loop-F-atDrink : ∀ {t} (s : Trace ⊥ t) → LoopState t → ⟦ F atDrink ⟧ s
-- P₁-root: drink frame now (k = 0).  `drop 0 s = s` definitionally.
loop-F-atDrink {t} s (inj₂ (inj₁ eq)) =
  0
  , drinkFrame⊥⇒atDrink s
      (subst IsDrinkFrame⊥ (frameOf-subst eq s)
        (proj₁ (rooted-P₁ (subst (Trace ⊥) eq s))))
  , λ m ()
-- VM_impl-root: coin now, drink next (k = 1).  `drop 1 s = tail s`.
loop-F-atDrink {t} s (inj₁ eq) =
  1
  , drinkFrame⊥⇒atDrink (tail s)
      (tail-is-drink s (coinRoot-tailP₁ s (inj₁ eq)))
  , λ { zero _ → lift tt₀ ; (suc _) (s≤s ()) }
-- P₂-root: coin now, drink next (k = 1), same witness as VM_impl-root.
loop-F-atDrink {t} s (inj₂ (inj₂ eq)) =
  1
  , drinkFrame⊥⇒atDrink (tail s)
      (tail-is-drink s (coinRoot-tailP₁ s (inj₂ eq)))
  , λ { zero _ → lift tt₀ ; (suc _) (s≤s ()) }
```

The loop-level liveness theorem.  **Fully constructive** — no postulate; the
period-2 / re-rooting drop analysis closes under `--guardedness` because the
position predicate recurses structurally on `n` (`loop-state-drop`), not
coinductively.

```agda
vm-loop-liveness : VM_impl ⊨ (G (F atDrink))
vm-loop-liveness tr = ⟦G⟧⁺⇒⟦G⟧ {φ = F atDrink} {tr = tr} (go tr)
  where
    go : (tr : Trace ⊥ VM_impl) → ⟦G⟧⁺ (F atDrink) tr
    go tr n = loop-F-atDrink (drop n tr) (loop-state-drop tr n)
```

## Negative result: trace-based safety does NOT capture next-time LTL

The four `⊨` theorems above (`vm-safety`, `vm-liveness`, `vm-until`,
`vm-terminates`, plus the loop-level `vm-loop-safety`/`vm-loop-liveness`)
quantify over the **operational, coinductive** `Trace` — at every position the
*tail always exists* (terminators stutter), so a `X φ` ("next") obligation
always has a genuine next frame to read.

`Semantics.LTL.Refinement` additionally provides a *trace-based* satisfaction
relation `_⊨ᵀ_`, quantified over the **prefix-closed** CSP trace words
`traces t s = Σ[ t′ ] (t ⟹⟨ s ⟩ t′)` instead of the coinductive `Trace`. This
relation is the natural target of a `⊑T`-refinement transfer
(`⊑T-transfer-ᵀ : P ⊑T Q → P ⊨ᵀ φ → Q ⊨ᵀ φ`), since CSP traces — unlike the
coinductive `Trace` — compose directly with trace refinement. The result
below shows that this convenience comes at a cost for "next"-time formulas:
**`_⊨ᵀ_` is unsound for guarded-`X` safety**, even though the *same* formula
is provable under `_⊨_` (`vm-safety` above).

The reason is prefix-closure. `VM_body_impl = coin ⟶₀ body2` has, among its
CSP traces, the *partial* word `coinEv ∷ []` — fire `coin`, then stop *before*
any drink event is observed. The finite-word evaluator `⟦_⟧ᵀ` reads `X φ` at a
nonempty word `e ∷ s` as `⟦ φ ⟧ᵀ s` (no end-of-word vacuous truth applies,
since the word is not literally `[]`); on the one-letter word `coinEv ∷ []`
this makes `⟦ X atDrink ⟧ᵀ (coinEv ∷ [])` reduce to `⟦ atDrink ⟧ᵀ [] = Lift ⊥`
— false — while `⟦ atCoin ⟧ᵀ (coinEv ∷ [])` is `⊤` (the head event is `coin`).
So the guard fires with no successor letter to discharge the "next is a
drink" obligation, and `G (atCoin ⇒ X atDrink)` fails at this one-letter
prefix. `_⊨ᵀ_` is consequently sound only for **X-free** (state-invariant)
safety; "next"-time LTL is fundamentally a branching-time / bisimulation
notion that prefix-closed trace semantics does not preserve. This complements
the separately-recorded finding that `VM_impl`/`VM_spec` are trace-equivalent
but not DR-bisimilar: bisimulation, not trace refinement, is the right tool
for transferring next-time LTL between implementation and specification.

The CSP-trace inversion below enumerates the shape of every
`VM_body_impl ⟹⟨ s ⟩ t′` run: either `s` is empty (`⟹-refl`), or the leading
event is pinned to `coin` by the existing `VM_body_impl-ev-inv′`, with the
remaining run rooted at `body2` (the τ-arm is impossible since
`VM_body_impl-no-τ` shows there is no τ-step to take). The named witness
`coinEv` realises the `coin`-event label needed by both the inversion and the
counterexample below.

```agda
open import Semantics.LTL.Refinement {E = VM} {I = ExtI VM}
  using (_⊨ᵀ_; ⟦_⟧ᵀ; ⊑T-transfer-ᵀ)
open import Semantics.Failures {E = VM} {I = ExtI VM}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)

-- The `coin` event label, used both by the inversion and the counterexample.
coinEv : Event√ (⊤ {lzero})
coinEv = evl (evLabel (⊤ {lzero}) coin tt)

-- CSP-trace inversion: every run from `VM_body_impl` is either the empty
-- run, or fires `coinEv` first and continues as a run from `body2`.
VM_body_impl-⟹-inv :
    ∀ {s t′} → VM_body_impl ⟹⟨ s ⟩ t′
  → (s ≡ []) ⊎ (Σ[ s′ ∈ List (Event√ (⊤ {lzero})) ] ((s ≡ coinEv ∷ s′) × (body2 ⟹⟨ s′ ⟩ t′)))
VM_body_impl-⟹-inv ⟹-refl        = inj₁ refl
VM_body_impl-⟹-inv (⟹-τ tτ _)    = ⊥-elim (VM_body_impl-no-τ tτ)
VM_body_impl-⟹-inv (⟹-ev st rest) with VM_body_impl-ev-inv′ st
... | refl , refl = inj₂ (_ , refl , rest)

-- The witness CSP trace: fire `coin`, then stop — `body2` is reached without
-- ever observing a drink event.  This one-letter word is a genuine member of
-- `traces VM_body_impl`, since CSP traces are prefix-closed.
trace-coin : traces VM_body_impl (coinEv ∷ [])
trace-coin = body2
           , ⟹-ev (sVis {at = ⊤ , coin} {a = tt} refl
                      (Prefix-cont-just coin (λ _ → body2) tt)) ⟹-refl

-- The certified negative result: `_⊨ᵀ_` does NOT validate the guarded-`X`
-- safety formula that `vm-safety` proves under the operational `_⊨_`.  At the
-- witness prefix `coinEv ∷ []`, `atCoin` holds (head event is `coin`) while
-- `X atDrink` reads past the end of the word (`⟦ atDrink ⟧ᵀ [] = Lift ⊥`), so
-- the antecedent `¬¬ atCoin × ¬ (X atDrink)` is inhabited and the `G`-bad
-- prefix at position 0 refutes the assumed satisfaction.
vm-⊨ᵀ-safety-impossible : VM_body_impl ⊨ᵀ (G (atCoin ⇒ X atDrink)) → Lift lzero ⊥
vm-⊨ᵀ-safety-impossible sat =
  sat {coinEv ∷ []} trace-coin
      ( 0
      , (λ psi → psi ((λ k → k tt) , (λ x → x)))
      , (λ m ()) )
```



