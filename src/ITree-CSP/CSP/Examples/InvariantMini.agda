{-# OPTIONS --guardedness #-}

-------------------------------------------------------------------------------------
-- INVARIANT-MINI: the smallest self-contained example of the
-- "step-inversion + progress invariant" technique for a STABLE-FAILURES liveness
-- refinement  `Spec ⊑F (System ∖ Hidden)`, together with the two variants that show
-- where the technique and the `⊑F` order break.
--
-- The technique.  Monotonicity/congruence laws cannot discharge such a goal (they
-- only replace components), and a full bisimulation is too expensive at scale.  The
-- alternative used here is:
--
--   (i)  INVERT the hide and the parallel one step at a time (`Hide-τ-elim`,
--        `Hide-ev-elim`, `Par-τ-elim`, `Par-ev-elim`), which pushes every obligation
--        down onto the LEAVES (`⟶₀-no-τ`, `⟶₀-ev-inv`);
--   (ii) carry a REACHABILITY INVARIANT — here literally a token position:
--        `atProducer` / `inTransit` / `atConsumer` / `atFinish` / `atEnd` — which
--        pairs each reachable implementation state with the spec state it must match;
--   (iii) discharge the liveness obligation with exactly two facts about that
--        invariant:
--          * PROGRESS  (`inTransit-τ`): the mid-flight position has the HIDDEN handoff
--            enabled, hence a τ, hence it is NOT stable and carries NO failure at all;
--          * OFFER     (`atConsumer-offers-b`): the position that IS stable after the
--            handoff really does offer the consumer's visible event.
--
-- Part 1 proves `Spec ⊑F Sys` this way.
-- Part 2 replaces the handoff by MISMATCHED hidden events: the mid-flight state is now
--        stable and refuses `b`, and `Spec ⊑F Sys′` is machine-checked FALSE.  This is
--        what shows the technique has real content — the progress lemma is exactly the
--        hypothesis Part 2 removes.
-- Part 3 replaces the producer's tail by a τ-loop: after `⟨a⟩` the implementation never
--        becomes stable, so it has NO failures there and `Spec ⊑F Sys″` holds VACUOUSLY
--        even though `b` never occurs.  Moral: a `⊑F` liveness statement carries content
--        only alongside divergence-freedom.  NOTE this vacuity survives the repair of
--        `_⊑F_` into Roscoe's (traces, failures) PAIR: `Sys″`'s traces are a SUBSET of
--        the spec's, so its trace obligation is discharged honestly (`invV-trace`) and
--        it is the FAILURES component alone that goes vacuous.
--
-- Nothing here is postulated and nothing is left as a hole; the whole dependency
-- closure used below (`Semantics.*` minus `DRImpliesFD`, `CSP.Operators`,
-- `CSP.Laws.Traces.*`) is postulate-free.
-------------------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Examples.InvariantMini where

-------------------------------------------------------------------------------------
-- §0  The alphabet: `a` (kept, produced), `m` (hidden handoff), `b` (kept, consumed),
--     plus `m′` — a FOURTH hidden event used only by the Part-2 deadlock variant.
-------------------------------------------------------------------------------------

-- four ⊤-carried channels
data Ev : Set → Set where
  a  : Ev ⊤
  m  : Ev ⊤
  b  : Ev ⊤
  m′ : Ev ⊤

-- decidable equality on the existential event index (what `CSP.Operators` needs)
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , a)  (_ , a)  = yes refl
Ev-≟ (_ , m)  (_ , m)  = yes refl
Ev-≟ (_ , b)  (_ , b)  = yes refl
Ev-≟ (_ , m′) (_ , m′) = yes refl
Ev-≟ (_ , a)  (_ , m)  = no λ ()
Ev-≟ (_ , a)  (_ , b)  = no λ ()
Ev-≟ (_ , a)  (_ , m′) = no λ ()
Ev-≟ (_ , m)  (_ , a)  = no λ ()
Ev-≟ (_ , m)  (_ , b)  = no λ ()
Ev-≟ (_ , m)  (_ , m′) = no λ ()
Ev-≟ (_ , b)  (_ , a)  = no λ ()
Ev-≟ (_ , b)  (_ , m)  = no λ ()
Ev-≟ (_ , b)  (_ , m′) = no λ ()
Ev-≟ (_ , m′) (_ , a)  = no λ ()
Ev-≟ (_ , m′) (_ , m)  = no λ ()
Ev-≟ (_ , m′) (_ , b)  = no λ ()

open import Semantics.LTS        {E = Ev} {I = ExtI Ev}
open import Semantics.Refusals   {E = Ev} {I = ExtI Ev}
open import Semantics.Failures   {E = Ev} {I = ExtI Ev}
open import Semantics.Stability  {E = Ev} {I = ExtI Ev}
  using (stable-no-τ; stable-not-ret; react-no-τ→stable)
open import CSP.Operators Ev-≟
open import CSP.Laws.Traces.PrefixInversion Ev-≟
  using (⟶₀-no-τ; ⟶₀-ev-inv; sil-τ-uniq; sil-no-ev)
open import CSP.Laws.Traces.TraceLawsHide Ev-≟
  using (HideτR; hτP; hτH; HideevR; heV; he√;
         Hide-τ-elim; Hide-ev-elim; Hide-τ; Hide-keep; Hide-hidden)
open import CSP.Laws.Traces.TraceLawsParallel Ev-≟
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L)
open import CSP.Laws.Traces.TraceLawsParallelElim Ev-≟
  using (ParτR; τL; τR; Par-τ-elim; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim)
open EventSet

-- the return type of every process below (CSP processes only ever return `tt`)
U : Set
U = ⊤ {0ℓ}

-- the one process type used throughout
Proc : Set₁
Proc = PTree Ev (ExtI Ev) U

-------------------------------------------------------------------------------------
-- §1  Event sets and the three visible labels.
-------------------------------------------------------------------------------------

-- the Part-1/Part-3 hidden alphabet: just the handoff `m`
csM : AnyTypes Ev → Set
csM (_ , a)  = ⊥
csM (_ , m)  = ⊤ {0ℓ}
csM (_ , b)  = ⊥
csM (_ , m′) = ⊥

-- …decided
decM : (at : AnyTypes Ev) → Dec (csM at)
decM (_ , a)  = no (λ z → z)
decM (_ , m)  = yes tt
decM (_ , b)  = no (λ z → z)
decM (_ , m′) = no (λ z → z)

-- `{m}` as an `EventSet` (channel-level: membership ignores the carried value)
mES : EventSet
mES = chanSet csM decM

-- the Part-2 hidden alphabet: BOTH handoff candidates `m` and `m′`
csMM : AnyTypes Ev → Set
csMM (_ , a)  = ⊥
csMM (_ , m)  = ⊤ {0ℓ}
csMM (_ , b)  = ⊥
csMM (_ , m′) = ⊤ {0ℓ}

-- …decided
decMM : (at : AnyTypes Ev) → Dec (csMM at)
decMM (_ , a)  = no (λ z → z)
decMM (_ , m)  = yes tt
decMM (_ , b)  = no (λ z → z)
decMM (_ , m′) = yes tt

-- `{m, m′}` as an `EventSet`
mm′ES : EventSet
mm′ES = chanSet csMM decMM

-- the three visible labels as trace letters
evA evM evB : Event√ U
evA = evl (evLabel U a tt)
evM = evl (evLabel U m tt)
evB = evl (evLabel U b tt)

-------------------------------------------------------------------------------------
-- §2  Leaf lemmas: how the two kinds of leaf (a prefix, and `Skip = Ret tt`) step.
--     These are the bottom of the inversion tower — every obligation below lands here.
-------------------------------------------------------------------------------------

-- a prefix on `a` fires on `evA` (and similarly for `m`, `m′`, `b`); the `E-≟`
-- comparison inside `Prefix-cont` reduces because the channel is concrete
fireA : {Q : Proc} → (a ⟶₀ Q) ─[ ev evA ]─► Q
fireA = sVis {at = U , a} {a = tt} refl refl

fireM : {Q : Proc} → (m ⟶₀ Q) ─[ ev evM ]─► Q
fireM = sVis {at = U , m} {a = tt} refl refl

fireB : {Q : Proc} → (b ⟶₀ Q) ─[ ev evB ]─► Q
fireB = sVis {at = U , b} {a = tt} refl refl

-- a prefix is a pure-visible `react`, hence STABLE (its τ-map is `∅t`).  Stated on the
-- two concrete spec states rather than generically: `isStable` is defined by a `with`
-- on `force`, so it only reduces once the tree is concrete.
Spec-stable : isStable (a ⟶₀ (b ⟶₀ Skip {0ℓ}))
Spec-stable _ _ = refl

Spec₁-stable : isStable (b ⟶₀ Skip {0ℓ})
Spec₁-stable _ _ = refl

-- `Skip = Ret tt` forces to `ret`, so it performs no τ …
Skip-no-τ : {W : Proc} → Skip {0ℓ} ─[ τ ]─► W → ⊥
Skip-no-τ (sSil eq)   = case eq of λ ()
Skip-no-τ (sTau eq _) = case eq of λ ()

-- … and no NON-√ visible event either (its only step is the `√`)
Skip-no-evl : {B : Set} {e : Ev B} {x : B} {W : Proc}
            → Skip {0ℓ} ─[ ev (evl (evLabel B e x)) ]─► W → ⊥
Skip-no-evl (sVis eq _) = case eq of λ ()

-- `deadlock` performs no τ (its τ-map is everywhere `nothing`)
dl-no-τ : {W : Proc} → deadlock {E = Ev} {I = ExtI Ev} {R = U} ─[ τ ]─► W → ⊥
dl-no-τ (sSil eq)      = case eq of λ ()
dl-no-τ (sTau refl br) = case br of λ ()

-------------------------------------------------------------------------------------
-- §3  PART 1 — the good case: the token flows producer → (hidden m) → consumer.
-------------------------------------------------------------------------------------

-- the producer: the kept event `a`, then the hidden handoff `m`
Prod : Proc
Prod = a ⟶₀ (m ⟶₀ Skip)

-- the producer's residual after `a` — the handoff is now pending
Prod₁ : Proc
Prod₁ = m ⟶₀ Skip

-- the consumer: the hidden handoff `m`, then the kept event `b`
Cons : Proc
Cons = m ⟶₀ (b ⟶₀ Skip)

-- the consumer's residual after the handoff — it now offers `b`
Cons₁ : Proc
Cons₁ = b ⟶₀ Skip

-- the implementation: producer ∥ consumer synchronising on `m`, with `m` HIDDEN
Sys : Proc
Sys = (Prod ∥⇘ mES ⇙ Cons) ∖ mES

-- the specification: `a` then `b`
Spec : Proc
Spec = a ⟶₀ (b ⟶₀ Skip)

-- the spec's residual after `a`
Spec₁ : Proc
Spec₁ = b ⟶₀ Skip

-- token IN TRANSIT: producer past `a`, handoff not yet taken (the hidden `m` is enabled)
S₁ : Proc
S₁ = (Prod₁ ∥⇘ mES ⇙ Cons) ∖ mES

-- token AT CONSUMER: handoff taken, `b` offered
S₂ : Proc
S₂ = (Skip ∥⇘ mES ⇙ Cons₁) ∖ mES

-- both components finished: the composite is about to `√`
S₃ : Proc
S₃ = (Skip ∥⇘ mES ⇙ Skip) ∖ mES

-------------------------------------------------------------------------------------
-- §3.1  Which of a leaf's events are hidden.  These four tiny lemmas are what make
--       every `Par-ev-elim` case below a one-liner: the `evL`/`evR`/`evBoth` branches
--       all carry `¬ mES .mem …`, and a leaf's event is either in `mES` or not.
-------------------------------------------------------------------------------------

-- the producer's first event is `a`, which is NOT hidden
prod-ev-open : {B : Set} {e : Ev B} {x : B} {W : Proc}
             → Prod ─[ ev (evl (evLabel B e x)) ]─► W → ¬ mES .mem (B , e) x
prod-ev-open st with ⟶₀-ev-inv st
... | _ , refl , _ = λ z → z

-- the producer's SECOND event is the hidden handoff `m`
prod₁-ev-hidden : {B : Set} {e : Ev B} {x : B} {W : Proc}
                → Prod₁ ─[ ev (evl (evLabel B e x)) ]─► W → mES .mem (B , e) x
prod₁-ev-hidden st with ⟶₀-ev-inv st
... | _ , refl , _ = tt

-- the consumer's first event is the hidden handoff `m`
cons-ev-hidden : {B : Set} {e : Ev B} {x : B} {W : Proc}
               → Cons ─[ ev (evl (evLabel B e x)) ]─► W → mES .mem (B , e) x
cons-ev-hidden st with ⟶₀-ev-inv st
... | _ , refl , _ = tt

-- the consumer's second event is `b`, which is NOT hidden
cons₁-ev-open : {B : Set} {e : Ev B} {x : B} {W : Proc}
              → Cons₁ ─[ ev (evl (evLabel B e x)) ]─► W → ¬ mES .mem (B , e) x
cons₁-ev-open st with ⟶₀-ev-inv st
... | _ , refl , _ = λ z → z

-------------------------------------------------------------------------------------
-- §3.2  THE TWO INVARIANT LEMMAS.  Everything the liveness argument needs about the
--       token positions is here; §3.3 below is pure inversion bookkeeping.
-------------------------------------------------------------------------------------

-- PROGRESS.  At the `inTransit` position the producer offers `m` and the consumer
-- accepts it, so the composite performs the synchronised `m`; hiding turns that into
-- a τ.  Hence `S₁` is NOT stable, and therefore contributes NO failure — this is the
-- one fact that makes the whole refinement go through, and it is exactly the fact
-- Part 2 destroys.
inTransit-τ : S₁ ─[ τ ]─► S₂
inTransit-τ = Hide-hidden mES (Prod₁ ∥⇘ mES ⇙ Cons) tt
                (Par-sync mES (λ _ _ → tt) Prod₁ Cons tt fireM fireM)

-- OFFER.  At the `atConsumer` position — the unique STABLE position after `⟨a⟩` — the
-- consumer's kept event `b` really is offered (the terminated producer cannot block it,
-- and `b ∉ mES` so hiding keeps it visible).
atConsumer-offers-b : Offers S₂ evB
atConsumer-offers-b =
  S₃ , Hide-keep mES (Skip ∥⇘ mES ⇙ Cons₁) (λ z → z)
         (Par-soloR mES (λ _ _ → tt) Skip Cons₁ (λ z → z) fireB refl)

-- the companion fact at the initial position: the kept event `a` is offered there
Sys-offers-a : Offers Sys evA
Sys-offers-a =
  S₁ , Hide-keep mES (Prod ∥⇘ mES ⇙ Cons) (λ z → z)
         (Par-soloL mES (λ _ _ → tt) Prod Cons (λ z → z) fireA refl)

-------------------------------------------------------------------------------------
-- §3.3  INVERSION PLUMBING.  For each token position: which τ-steps and which visible
--       steps exist.  Each proof is `Hide-*-elim` followed by `Par-*-elim` followed by
--       a leaf lemma from §2/§3.1 — the mechanical part that would grow with the size
--       of the composite.
-------------------------------------------------------------------------------------

-- the initial composite (before hiding) has no τ: both operands are prefixes
par-PC-no-τ : {W : Proc} → (Prod ∥⇘ mES ⇙ Cons) ─[ τ ]─► W → ⊥
par-PC-no-τ st with Par-τ-elim mES (λ _ _ → tt) Prod Cons st
... | τL _ Pτ _ = ⟶₀-no-τ Pτ
... | τR _ Qτ _ = ⟶₀-no-τ Qτ

-- …and no hidden event enabled: `mES`-membership forces `m`, but the producer offers `a`
par-PC-no-hidden : {B : Set} {e : Ev B} {x : B} {W : Proc}
                 → mES .mem (B , e) x
                 → (Prod ∥⇘ mES ⇙ Cons) ─[ ev (evl (evLabel B e x)) ]─► W → ⊥
par-PC-no-hidden csat st with Par-ev-elim mES (λ _ _ → tt) Prod Cons st
... | evSync _ Pev _ = prod-ev-open Pev csat
... | evL ¬cs _      = ¬cs csat
... | evR ¬cs _      = ¬cs csat
... | evBoth ¬cs _ _ = ¬cs csat

-- hence the initial state is τ-free
Sys-no-τ : {W : Proc} → Sys ─[ τ ]─► W → ⊥
Sys-no-τ st with Hide-τ-elim mES (Prod ∥⇘ mES ⇙ Cons) st
... | hτP _ Pτ _        = par-PC-no-τ Pτ
... | hτH _ csat Pev _  = par-PC-no-hidden csat Pev

-- the ONLY visible step out of the initial state is `a`, landing `inTransit`
Sys-ev-uniq : {e : Event√ U} {W : Proc} → Sys ─[ ev e ]─► W → (e ≡ evA) × (W ≡ S₁)
Sys-ev-uniq st with Hide-ev-elim mES (Prod ∥⇘ mES ⇙ Cons) st
... | he√ eqf      = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mES (λ _ _ → tt) Prod Cons Pev
...   | evSync csat _ _   = ⊥-elim (¬cs csat)
...   | evR _ Qev         = ⊥-elim (¬cs (cons-ev-hidden Qev))
...   | evBoth _ Pev′ Qev = ⊥-elim (prod-ev-open Pev′ (cons-ev-hidden Qev))
...   | evL _ Pev′ with ⟶₀-ev-inv Pev′
...     | _ , refl , refl = refl , refl

-- the in-transit composite (before hiding) has no τ: both operands are prefixes
par-P₁C-no-τ : {W : Proc} → (Prod₁ ∥⇘ mES ⇙ Cons) ─[ τ ]─► W → ⊥
par-P₁C-no-τ st with Par-τ-elim mES (λ _ _ → tt) Prod₁ Cons st
... | τL _ Pτ _ = ⟶₀-no-τ Pτ
... | τR _ Qτ _ = ⟶₀-no-τ Qτ

-- the in-transit state's ONLY τ is the hidden handoff, landing `atConsumer`
S₁-τ-uniq : {W : Proc} → S₁ ─[ τ ]─► W → W ≡ S₂
S₁-τ-uniq st with Hide-τ-elim mES (Prod₁ ∥⇘ mES ⇙ Cons) st
... | hτP _ Pτ _       = ⊥-elim (par-P₁C-no-τ Pτ)
... | hτH _ csat Pev refl with Par-ev-elim mES (λ _ _ → tt) Prod₁ Cons Pev
...   | evL ¬cs _      = ⊥-elim (¬cs csat)
...   | evR ¬cs _      = ⊥-elim (¬cs csat)
...   | evBoth ¬cs _ _ = ⊥-elim (¬cs csat)
...   | evSync _ Pev′ Qev′ with ⟶₀-ev-inv Pev′
...     | _ , refl , refl with ⟶₀-ev-inv Qev′
...       | _ , refl , refl = refl

-- the in-transit state has NO visible step: its only event, `m`, is hidden
S₁-no-ev : {e : Event√ U} {W : Proc} → S₁ ─[ ev e ]─► W → ⊥
S₁-no-ev st with Hide-ev-elim mES (Prod₁ ∥⇘ mES ⇙ Cons) st
... | he√ eqf       = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mES (λ _ _ → tt) Prod₁ Cons Pev
...   | evSync csat _ _  = ¬cs csat
...   | evL _ Pev′       = ¬cs (prod₁-ev-hidden Pev′)
...   | evR _ Qev′       = ¬cs (cons-ev-hidden Qev′)
...   | evBoth _ Pev′ _  = ¬cs (prod₁-ev-hidden Pev′)

-- the at-consumer composite (before hiding) has no τ: `Skip` is a `ret`, `Cons₁` a prefix
par-SC₁-no-τ : {W : Proc} → (Skip ∥⇘ mES ⇙ Cons₁) ─[ τ ]─► W → ⊥
par-SC₁-no-τ st with Par-τ-elim mES (λ _ _ → tt) Skip Cons₁ st
... | τL _ Pτ _ = Skip-no-τ Pτ
... | τR _ Qτ _ = ⟶₀-no-τ Qτ

-- the at-consumer state is τ-free: its only event, `b`, is NOT hidden
S₂-no-τ : {W : Proc} → S₂ ─[ τ ]─► W → ⊥
S₂-no-τ st with Hide-τ-elim mES (Skip ∥⇘ mES ⇙ Cons₁) st
... | hτP _ Pτ _       = par-SC₁-no-τ Pτ
... | hτH _ csat Pev _ with Par-ev-elim mES (λ _ _ → tt) Skip Cons₁ Pev
...   | evSync _ Pev′ _ = Skip-no-evl Pev′
...   | evL _ Pev′      = Skip-no-evl Pev′
...   | evR _ Qev′      = cons₁-ev-open Qev′ csat
...   | evBoth _ Pev′ _ = Skip-no-evl Pev′

-- the ONLY visible step out of the at-consumer state is `b`, landing at `atFinish`
S₂-ev-uniq : {e : Event√ U} {W : Proc} → S₂ ─[ ev e ]─► W → (e ≡ evB) × (W ≡ S₃)
S₂-ev-uniq st with Hide-ev-elim mES (Skip ∥⇘ mES ⇙ Cons₁) st
... | he√ eqf       = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mES (λ _ _ → tt) Skip Cons₁ Pev
...   | evSync _ Pev′ _ = ⊥-elim (Skip-no-evl Pev′)
...   | evL _ Pev′      = ⊥-elim (Skip-no-evl Pev′)
...   | evBoth _ Pev′ _ = ⊥-elim (Skip-no-evl Pev′)
...   | evR _ Qev′ with ⟶₀-ev-inv Qev′
...     | _ , refl , refl = refl , refl

-- the finished composite forces to `ret tt`, so it has no τ …
S₃-no-τ : {W : Proc} → S₃ ─[ τ ]─► W → ⊥
S₃-no-τ (sSil eq)   = case eq of λ ()
S₃-no-τ (sTau eq _) = case eq of λ ()

-- … and no non-√ visible step …
par-SS-no-evl : {B : Set} {e : Ev B} {x : B} {W : Proc}
              → (Skip ∥⇘ mES ⇙ Skip) ─[ ev (evl (evLabel B e x)) ]─► W → ⊥
par-SS-no-evl (sVis eq _) = case eq of λ ()

-- … its only step is the `√`, landing at `deadlock`
S₃-ev-uniq : {e : Event√ U} {W : Proc} → S₃ ─[ ev e ]─► W → (e ≡ √ tt) × (W ≡ deadlock)
S₃-ev-uniq st with Hide-ev-elim mES (Skip ∥⇘ mES ⇙ Skip) st
... | heV _ _ Pev = ⊥-elim (par-SS-no-evl Pev)
... | he√ _       = refl , refl

-- the spec's residuals offer exactly one event each, which is all the refusal
-- transfer below needs from the spec side
Spec-offer-inv : {e : Event√ U} → Offers Spec e → e ≡ evA
Spec-offer-inv (_ , st) with ⟶₀-ev-inv st
... | _ , refl , _ = refl

Spec₁-offer-inv : {e : Event√ U} → Offers Spec₁ e → e ≡ evB
Spec₁-offer-inv (_ , st) with ⟶₀-ev-inv st
... | _ , refl , _ = refl

-------------------------------------------------------------------------------------
-- §3.4  THE INVARIANT, and the refinement proof it drives.
-------------------------------------------------------------------------------------

-- The reachable-state invariant of `Sys`, indexed by the implementation state AND the
-- spec state that still has to be matched.  The five constructors ARE the token
-- positions: at the producer, in flight (hidden), at the consumer, both finished, ended.
data Inv : Proc → Proc → Set where
  atProducer : Inv Sys        Spec
  inTransit  : Inv S₁         Spec₁
  atConsumer : Inv S₂         Spec₁
  atFinish   : Inv S₃         (Skip {0ℓ})
  atEnd      : Inv deadlock   deadlock

-- CLOSURE UNDER τ.  A τ of the implementation is invisible to the spec, so the spec
-- stands still.  Only the `inTransit` position has a τ at all — that is the handoff.
inv-τ : {W V W′ : Proc} → Inv W V → W ─[ τ ]─► W′ → Inv W′ V
inv-τ atProducer st = ⊥-elim (Sys-no-τ st)
inv-τ inTransit  st with S₁-τ-uniq st
... | refl = atConsumer
inv-τ atConsumer st = ⊥-elim (S₂-no-τ st)
inv-τ atFinish   st = ⊥-elim (S₃-no-τ st)
inv-τ atEnd      st = ⊥-elim (dl-no-τ st)

-- CLOSURE UNDER A VISIBLE EVENT.  Each visible step of the implementation is matched
-- by the same event on the spec side, preserving the invariant.
inv-ev : {W V W′ : Proc} {e : Event√ U} → Inv W V → W ─[ ev e ]─► W′
       → Σ[ V′ ∈ Proc ] ((V ─[ ev e ]─► V′) × Inv W′ V′)
inv-ev atProducer st with Sys-ev-uniq st
... | refl , refl = Spec₁ , fireA , inTransit
inv-ev inTransit  st = ⊥-elim (S₁-no-ev st)
inv-ev atConsumer st with S₂-ev-uniq st
... | refl , refl = Skip , fireB , atFinish
inv-ev atFinish   st with S₃-ev-uniq st
... | refl , refl = deadlock , sRet refl , atEnd
inv-ev atEnd      st = ⊥-elim (deadlock-no-offer st)

-- REFUSAL TRANSFER at a state where the implementation has stopped.  This is where the
-- two invariant lemmas of §3.2 are consumed:
--   * `inTransit` is refuted by PROGRESS  — a mid-flight state is never stable, so it
--     never contributes a failure at all (the handoff is hidden, so a τ is enabled);
--   * `atConsumer` is discharged by OFFER — `b` is offered there, so no refusal of the
--     implementation at `⟨a⟩` can ban `b`, which is exactly what the spec demands;
--   * `atFinish` is refuted because a `ret` state is not stable either.
inv-refuses : {W V : Proc} {X : Event√ U → Set} → Inv W V → Refuses W X → Refuses V X
inv-refuses atProducer (_ , noff) =
  Spec-stable , λ e Xe off → case Spec-offer-inv off of λ { refl → noff evA Xe Sys-offers-a }
inv-refuses inTransit  (st , _) = ⊥-elim (stable-no-τ st inTransit-τ)
inv-refuses atConsumer (_ , noff) =
  Spec₁-stable , λ e Xe off → case Spec₁-offer-inv off of λ { refl → noff evB Xe atConsumer-offers-b }
inv-refuses atFinish   (st , _) = ⊥-elim (stable-not-ret {t = S₃} st refl)
inv-refuses atEnd      ref      = ref

-- a visible step prepends to a failure (`failures` is a plain Σ)
fail-ev : {V V′ : Proc} {e : Event√ U} {s : List (Event√ U)} {X : Event√ U → Set}
        → V ─[ ev e ]─► V′ → failures V′ s X → failures V (e ∷ s) X
fail-ev st (W , r , ref) = W , ⟹-ev st r , ref

-- the induction: walk the implementation's weak run, keeping the invariant, and
-- assemble the matching spec failure
inv-fail : {W V W′ : Proc} {s : List (Event√ U)} {X : Event√ U → Set}
         → Inv W V → W ⟹⟨ s ⟩ W′ → Refuses W′ X → failures V s X
inv-fail {V = V} inv ⟹-refl        ref = V , ⟹-refl , inv-refuses inv ref
inv-fail         inv (⟹-τ  st rest) ref = inv-fail (inv-τ inv st) rest ref
inv-fail         inv (⟹-ev st rest) ref with inv-ev inv st
... | _ , Vst , inv′ = fail-ev Vst (inv-fail inv′ rest ref)

-- the same induction with the refusal dropped: walk the run keeping the invariant and
-- read off the matching spec TRACE.  This is the trace component `_⊑F_` demands.
inv-trace : {W V W′ : Proc} {s : List (Event√ U)}
          → Inv W V → W ⟹⟨ s ⟩ W′ → traces V s
inv-trace {V = V} inv ⟹-refl         = V , ⟹-refl
inv-trace         inv (⟹-τ  st rest) = inv-trace (inv-τ inv st) rest
inv-trace         inv (⟹-ev st rest) with inv-ev inv st
... | _ , Vst , inv′ with inv-trace inv′ rest
...   | W , r = W , ⟹-ev Vst r

-- PART 1, the TRACE half: every trace of `Sys` is a trace of `Spec`
Spec⊑T-Sys : Spec ⊑T Sys
Spec⊑T-Sys s (_ , reach) = inv-trace atProducer reach

-- kept private: `_⊇F_` is the weaker half of `_⊑F_` and must not be reachable
-- as ordinary API (see `Semantics.Failures`); this feeds `Spec⊑F-Sys` below.
private
  -- PART 1, the FAILURES half
  Spec⊇F-Sys : Spec ⊇F Sys
  Spec⊇F-Sys s X (_ , reach , ref) = inv-fail atProducer reach ref

-- PART 1, THE THEOREM: the hidden handoff refines away — `Spec ⊑F Sys`, at Roscoe's
-- stable-failures order (traces AND failures; both halves come from the one invariant).
Spec⊑F-Sys : Spec ⊑F Sys
Spec⊑F-Sys = Spec⊑T-Sys , Spec⊇F-Sys

-------------------------------------------------------------------------------------
-- §4  PART 2 — the DEADLOCK variant: the producer offers `m′`, the consumer wants `m`,
--     both hidden.  After `⟨a⟩` the composite is stable, mid-flight, and refuses `b`,
--     so the refinement FAILS.  This is what shows the Part-1 progress lemma is the
--     real content of the argument, not a formality.
-------------------------------------------------------------------------------------

-- the mismatched producer: `a`, then the hidden `m′` (which nobody accepts)
ProdD : Proc
ProdD = a ⟶₀ (m′ ⟶₀ Skip)

-- its residual after `a`
ProdD₁ : Proc
ProdD₁ = m′ ⟶₀ Skip

-- the mismatched implementation: sync + hide on BOTH `m` and `m′`
SysD : Proc
SysD = (ProdD ∥⇘ mm′ES ⇙ Cons) ∖ mm′ES

-- the state after `⟨a⟩`: producer offers `m′`, consumer offers `m`, neither can move
D₁ : Proc
D₁ = (ProdD₁ ∥⇘ mm′ES ⇙ Cons) ∖ mm′ES

-- `ProdD`'s first event `a` is not hidden …
prodD-ev-open : {B : Set} {e : Ev B} {x : B} {W : Proc}
              → ProdD ─[ ev (evl (evLabel B e x)) ]─► W → ¬ mm′ES .mem (B , e) x
prodD-ev-open st with ⟶₀-ev-inv st
... | _ , refl , _ = λ z → z

-- … `ProdD₁`'s event `m′` IS hidden …
prodD₁-ev-hidden : {B : Set} {e : Ev B} {x : B} {W : Proc}
                 → ProdD₁ ─[ ev (evl (evLabel B e x)) ]─► W → mm′ES .mem (B , e) x
prodD₁-ev-hidden st with ⟶₀-ev-inv st
... | _ , refl , _ = tt

-- … and so is `Cons`'s event `m`
consD-ev-hidden : {B : Set} {e : Ev B} {x : B} {W : Proc}
                → Cons ─[ ev (evl (evLabel B e x)) ]─► W → mm′ES .mem (B , e) x
consD-ev-hidden st with ⟶₀-ev-inv st
... | _ , refl , _ = tt

-- THE MISMATCH: `ProdD₁` offers only `m′` and `Cons` only `m`, so they can never
-- synchronise — no handoff, hence (below) no τ, hence a STABLE mid-flight state.
mismatch : {B : Set} {e : Ev B} {x : B} {W₁ W₂ : Proc}
         → ProdD₁ ─[ ev (evl (evLabel B e x)) ]─► W₁
         → Cons   ─[ ev (evl (evLabel B e x)) ]─► W₂ → ⊥
mismatch p q with ⟶₀-ev-inv p
... | _ , refl , _ with ⟶₀-ev-inv q
...   | _ , eq , _ = case eq of λ ()

-- the mismatched composite (before hiding) has no τ
par-D-no-τ : {W : Proc} → (ProdD₁ ∥⇘ mm′ES ⇙ Cons) ─[ τ ]─► W → ⊥
par-D-no-τ st with Par-τ-elim mm′ES (λ _ _ → tt) ProdD₁ Cons st
... | τL _ Pτ _ = ⟶₀-no-τ Pτ
... | τR _ Qτ _ = ⟶₀-no-τ Qτ

-- FAILURE OF PROGRESS: `D₁` has NO τ at all.  The hidden events are individually
-- offered by the two operands, but never JOINTLY, so nothing is hidden into a τ.
D₁-no-τ : {W : Proc} → D₁ ─[ τ ]─► W → ⊥
D₁-no-τ st with Hide-τ-elim mm′ES (ProdD₁ ∥⇘ mm′ES ⇙ Cons) st
... | hτP _ Pτ _       = par-D-no-τ Pτ
... | hτH _ csat Pev _ with Par-ev-elim mm′ES (λ _ _ → tt) ProdD₁ Cons Pev
...   | evSync _ Pev′ Qev′ = mismatch Pev′ Qev′
...   | evL ¬cs _          = ¬cs csat
...   | evR ¬cs _          = ¬cs csat
...   | evBoth ¬cs _ _     = ¬cs csat

-- …hence `D₁` IS stable (it forces to a `react` node and performs no τ)
D₁-stable : isStable D₁
D₁-stable = react-no-τ→stable {t = D₁} refl D₁-no-τ

-- …and it offers no visible event either: both pending events are hidden
D₁-no-ev : {e : Event√ U} {W : Proc} → D₁ ─[ ev e ]─► W → ⊥
D₁-no-ev st with Hide-ev-elim mm′ES (ProdD₁ ∥⇘ mm′ES ⇙ Cons) st
... | he√ eqf       = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mm′ES (λ _ _ → tt) ProdD₁ Cons Pev
...   | evSync csat _ _ = ¬cs csat
...   | evL _ Pev′      = ¬cs (prodD₁-ev-hidden Pev′)
...   | evR _ Qev′      = ¬cs (consD-ev-hidden Qev′)
...   | evBoth _ Pev′ _ = ¬cs (prodD₁-ev-hidden Pev′)

-- the singleton refusal set `{b}` (a `Set₀`-valued predicate, as `_⊑F_` demands —
-- `_≡_` on `Event√ U` would land in `Set₁`)
Xb : Event√ U → Set
Xb (evl (evLabel _ b  _)) = ⊤ {0ℓ}
Xb (evl (evLabel _ a  _)) = ⊥
Xb (evl (evLabel _ m  _)) = ⊥
Xb (evl (evLabel _ m′ _)) = ⊥
Xb (√ _)                  = ⊥

-- `D₁` is a stable, mid-flight state refusing `{b}` — a genuine DEADLOCK failure
D₁-refuses-b : Refuses D₁ Xb
D₁-refuses-b = D₁-stable , λ _ _ off → D₁-no-ev (proj₂ off)

-- `SysD` reaches `D₁` on `⟨a⟩` (the kept event `a` is unaffected by the mismatch)
SysD-a : SysD ─[ ev evA ]─► D₁
SysD-a = Hide-keep mm′ES (ProdD ∥⇘ mm′ES ⇙ Cons) (λ z → z)
           (Par-soloL mm′ES (λ _ _ → tt) ProdD Cons (λ z → z) fireA refl)

-- (1) the offending failure: `SysD` refuses `b` after `⟨a⟩`
SysD-bad-failure : failures SysD (evA ∷ []) Xb
SysD-bad-failure = D₁ , ⟹-ev SysD-a ⟹-refl , D₁-refuses-b

-- the spec's only state after `⟨a⟩` is `b ⟶₀ Skip` …
spec-nil : {W : Proc} → Spec₁ ⟹⟨ [] ⟩ W → W ≡ Spec₁
spec-nil ⟹-refl       = refl
spec-nil (⟹-τ st _)   = ⊥-elim (⟶₀-no-τ st)

spec-after-a : {W : Proc} → Spec ⟹⟨ evA ∷ [] ⟩ W → W ≡ Spec₁
spec-after-a (⟹-τ st _)     = ⊥-elim (⟶₀-no-τ st)
spec-after-a (⟹-ev st rest) with ⟶₀-ev-inv st
... | _ , _ , refl = spec-nil rest

-- (2) …and it OFFERS `b`, so the spec has no such failure
Spec-no-bad-failure : ¬ failures Spec (evA ∷ []) Xb
Spec-no-bad-failure (_ , reach , (_ , noff)) with spec-after-a reach
... | refl = noff evB tt (Skip , fireB)

-- kept private: `_⊇F_` is the weaker half of `_⊑F_` and must not be reachable
-- as ordinary API (see `Semantics.Failures`); this feeds `Spec⋢F-SysD` below.
private
  -- (3) PART 2, THE REFUTATION: the mismatched implementation does not even contain the
  -- spec's FAILURES — the sharp form, since `_⊇F_` is the weaker of the two orders.
  Spec⊉F-SysD : ¬ (Spec ⊇F SysD)
  Spec⊉F-SysD ref = Spec-no-bad-failure (ref (evA ∷ []) Xb SysD-bad-failure)

-- …hence it is not a `⊑F` refinement either (`_⊑F_` is the stronger, paired order)
Spec⋢F-SysD : ¬ (Spec ⊑F SysD)
Spec⋢F-SysD ref = Spec⊉F-SysD (proj₂ ref)

-------------------------------------------------------------------------------------
-- §5  PART 3 — the VACUITY variant: the producer diverges instead of handing over.
--
--     MORAL.  In the stable-failures model a failure only exists at a STABLE state, so
--     a divergent implementation has NO failures at all past the divergence — and
--     therefore satisfies any must-offer obligation there VACUOUSLY.  `Spec ⊑F Sys″`
--     below is proved even though `b` NEVER occurs in `Sys″`.  The progress argument of
--     Part 1 exploits exactly this hole: "mid-flight ⇒ a τ is enabled ⇒ not stable ⇒ no
--     failure" is sound, but it cannot distinguish "a τ that makes progress" from "a τ
--     that spins forever".  A `⊑F` liveness statement therefore carries content only
--     when it is paired with divergence-freedom of the implementation (e.g. `⊑FD`, or a
--     separate `τ`-well-foundedness certificate); on its own it is satisfiable by
--     divergence.
-------------------------------------------------------------------------------------

-- the divergent producer: `a`, then the library's τ-loop `div` (force div = sil div)
ProdV : Proc
ProdV = a ⟶₀ div

-- the divergent implementation
SysV : Proc
SysV = (ProdV ∥⇘ mES ⇙ Cons) ∖ mES

-- the state after `⟨a⟩`: the producer spins on hidden τ's forever
V₁ : Proc
V₁ = (div ∥⇘ mES ⇙ Cons) ∖ mES

-- `ProdV`'s first event `a` is not hidden
prodV-ev-open : {B : Set} {e : Ev B} {x : B} {W : Proc}
              → ProdV ─[ ev (evl (evLabel B e x)) ]─► W → ¬ mES .mem (B , e) x
prodV-ev-open st with ⟶₀-ev-inv st
... | _ , refl , _ = λ z → z

-- the composite before hiding has no τ (both operands are prefixes)
par-VC-no-τ : {W : Proc} → (ProdV ∥⇘ mES ⇙ Cons) ─[ τ ]─► W → ⊥
par-VC-no-τ st with Par-τ-elim mES (λ _ _ → tt) ProdV Cons st
... | τL _ Pτ _ = ⟶₀-no-τ Pτ
... | τR _ Qτ _ = ⟶₀-no-τ Qτ

-- the initial state of the divergent system is τ-free (same shape as `Sys-no-τ`)
SysV-no-τ : {W : Proc} → SysV ─[ τ ]─► W → ⊥
SysV-no-τ st with Hide-τ-elim mES (ProdV ∥⇘ mES ⇙ Cons) st
... | hτP _ Pτ _       = par-VC-no-τ Pτ
... | hτH _ csat Pev _ with Par-ev-elim mES (λ _ _ → tt) ProdV Cons Pev
...   | evSync _ Pev′ _ = prodV-ev-open Pev′ csat
...   | evL ¬cs _       = ¬cs csat
...   | evR ¬cs _       = ¬cs csat
...   | evBoth ¬cs _ _  = ¬cs csat

-- the only visible step of the divergent system is `a`, landing in the spin state
SysV-ev-uniq : {e : Event√ U} {W : Proc} → SysV ─[ ev e ]─► W → (e ≡ evA) × (W ≡ V₁)
SysV-ev-uniq st with Hide-ev-elim mES (ProdV ∥⇘ mES ⇙ Cons) st
... | he√ eqf      = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mES (λ _ _ → tt) ProdV Cons Pev
...   | evSync csat _ _   = ⊥-elim (¬cs csat)
...   | evR _ Qev         = ⊥-elim (¬cs (cons-ev-hidden Qev))
...   | evBoth _ Pev′ Qev = ⊥-elim (prodV-ev-open Pev′ (cons-ev-hidden Qev))
...   | evL _ Pev′ with ⟶₀-ev-inv Pev′
...     | _ , refl , refl = refl , refl

-- THE SPIN: the producer's `sil` becomes a composite τ, which hiding propagates.
-- `V₁` steps to ITSELF, so it is never stable — and never will be.
V₁-τ : V₁ ─[ τ ]─► V₁
V₁-τ = Hide-τ mES (div ∥⇘ mES ⇙ Cons)
         (Par-τ-L mES (λ _ _ → tt) div Cons (sSil refl))

-- …and that is the ONLY τ of `V₁`: the hidden `m` still needs the (silent) producer
V₁-τ-uniq : {W : Proc} → V₁ ─[ τ ]─► W → W ≡ V₁
V₁-τ-uniq st with Hide-τ-elim mES (div ∥⇘ mES ⇙ Cons) st
... | hτP _ Pτ refl with Par-τ-elim mES (λ _ _ → tt) div Cons Pτ
...   | τL _ dτ refl with sil-τ-uniq {S = div} refl dτ
...     | refl = refl
V₁-τ-uniq st | hτP _ Pτ refl | τR _ Qτ _ = ⊥-elim (⟶₀-no-τ Qτ)
V₁-τ-uniq st | hτH _ csat Pev _ with Par-ev-elim mES (λ _ _ → tt) div Cons Pev
... | evSync _ Pev′ _ = ⊥-elim (sil-no-ev {S = div} refl Pev′)
... | evL _ Pev′      = ⊥-elim (sil-no-ev {S = div} refl Pev′)
... | evBoth _ Pev′ _ = ⊥-elim (sil-no-ev {S = div} refl Pev′)
... | evR ¬cs Qev′    = ⊥-elim (¬cs csat)

-- `V₁` offers nothing visible: the producer is silent and the consumer's `m` is hidden
V₁-no-ev : {e : Event√ U} {W : Proc} → V₁ ─[ ev e ]─► W → ⊥
V₁-no-ev st with Hide-ev-elim mES (div ∥⇘ mES ⇙ Cons) st
... | he√ eqf       = case eqf of λ ()
... | heV _ ¬cs Pev with Par-ev-elim mES (λ _ _ → tt) div Cons Pev
...   | evSync csat _ _ = ¬cs csat
...   | evL _ Pev′      = sil-no-ev {S = div} refl Pev′
...   | evR _ Qev′      = ¬cs (cons-ev-hidden Qev′)
...   | evBoth _ Pev′ _ = sil-no-ev {S = div} refl Pev′

-- `V₁` DIVERGES (the τ-self-loop, taken coinductively)
V₁-diverges : Diverges V₁
V₁-diverges .Diverges.next = V₁
V₁-diverges .Diverges.step = V₁-τ
V₁-diverges .Diverges.rest = V₁-diverges

-- THE VACUITY: `V₁` has NO failure at ANY trace.  Every run out of it is a sequence of
-- self-τ's (there is no visible step), and the endpoint is never stable.
-- The `W ≡ V₁` premise (rather than a `with` on `V₁-τ-uniq`) keeps the recursion on the
-- weak-run derivation structural, so no termination pragma is needed.
spin-no-fail : {W W′ : Proc} {s : List (Event√ U)} {X : Event√ U → Set}
             → W ≡ V₁ → W ⟹⟨ s ⟩ W′ → Refuses W′ X → ⊥
spin-no-fail refl ⟹-refl         (st , _) = stable-no-τ st V₁-τ
spin-no-fail refl (⟹-τ  st rest) ref      = spin-no-fail (V₁-τ-uniq st) rest ref
spin-no-fail refl (⟹-ev st _)    _        = V₁-no-ev st

V₁-no-failures : {s : List (Event√ U)} {X : Event√ U → Set} → ¬ failures V₁ s X
V₁-no-failures (_ , reach , ref) = spin-no-fail refl reach ref

-- hence `SysV` has NO failure at any trace extending `⟨a⟩` — in particular none that
-- would witness a refusal of `b`, which is why the refinement below is vacuous
SysV-no-failure-after-a : {s : List (Event√ U)} {X : Event√ U → Set}
                        → ¬ failures SysV (evA ∷ s) X
SysV-no-failure-after-a (_ , ⟹-τ st _ , _) = SysV-no-τ st
SysV-no-failure-after-a (W , ⟹-ev st rest , ref) with SysV-ev-uniq st
... | refl , refl = V₁-no-failures (W , rest , ref)

-- the divergent system offers `a` initially, exactly like `Sys`
SysV-offers-a : Offers SysV evA
SysV-offers-a =
  V₁ , Hide-keep mES (ProdV ∥⇘ mES ⇙ Cons) (λ z → z)
         (Par-soloL mES (λ _ _ → tt) ProdV Cons (λ z → z) fireA refl)

-- the divergent system's own (two-position) invariant: either at the producer, or
-- spinning.  `spinning` carries no failure, so the whole refinement collapses to the
-- initial refusal transfer.
data InvV : Proc → Proc → Set where
  atProducerV : InvV SysV Spec
  spinning    : InvV V₁   Spec₁

-- τ-closure (only the spin position has a τ, and it stays there)
invV-τ : {W V W′ : Proc} → InvV W V → W ─[ τ ]─► W′ → InvV W′ V
invV-τ atProducerV st = ⊥-elim (SysV-no-τ st)
invV-τ spinning    st with V₁-τ-uniq st
... | refl = spinning

-- visible-closure (only `a`, out of the initial position)
invV-ev : {W V W′ : Proc} {e : Event√ U} → InvV W V → W ─[ ev e ]─► W′
        → Σ[ V′ ∈ Proc ] ((V ─[ ev e ]─► V′) × InvV W′ V′)
invV-ev atProducerV st with SysV-ev-uniq st
... | refl , refl = Spec₁ , fireA , spinning
invV-ev spinning   st = ⊥-elim (V₁-no-ev st)

-- refusal transfer: the initial position as in Part 1; the spin position is REFUTED,
-- not discharged — that is precisely the vacuity
invV-refuses : {W V : Proc} {X : Event√ U → Set} → InvV W V → Refuses W X → Refuses V X
invV-refuses atProducerV (_ , noff) =
  Spec-stable , λ e Xe off → case Spec-offer-inv off of λ { refl → noff evA Xe SysV-offers-a }
invV-refuses spinning (st , _) = ⊥-elim (stable-no-τ st V₁-τ)

invV-fail : {W V W′ : Proc} {s : List (Event√ U)} {X : Event√ U → Set}
          → InvV W V → W ⟹⟨ s ⟩ W′ → Refuses W′ X → failures V s X
invV-fail {V = V} inv ⟹-refl         ref = V , ⟹-refl , invV-refuses inv ref
invV-fail         inv (⟹-τ  st rest) ref = invV-fail (invV-τ inv st) rest ref
invV-fail         inv (⟹-ev st rest) ref with invV-ev inv st
... | _ , Vst , inv′ = fail-ev Vst (invV-fail inv′ rest ref)

-- the trace half, as in Part 1: `SysV`'s only traces are `[]` and `⟨a⟩`, both of them
-- traces of `Spec`.  Divergence costs nothing here — it removes failures, not traces.
invV-trace : {W V W′ : Proc} {s : List (Event√ U)}
           → InvV W V → W ⟹⟨ s ⟩ W′ → traces V s
invV-trace {V = V} inv ⟹-refl         = V , ⟹-refl
invV-trace         inv (⟹-τ  st rest) = invV-trace (invV-τ inv st) rest
invV-trace         inv (⟹-ev st rest) with invV-ev inv st
... | _ , Vst , inv′ with invV-trace inv′ rest
...   | W , r = W , ⟹-ev Vst r

-- PART 3, THE THEOREM: `Spec ⊑F SysV` holds — VACUOUSLY IN ITS FAILURES COMPONENT.
-- `SysV` never performs `b` (see `SysV-no-failure-after-a` / `V₁-no-failures`), yet it
-- refines `Spec` in the stable-failures order, because a divergent state has no stable
-- failure to violate.  Note the trace component is NOT vacuous — it is discharged
-- honestly by `invV-trace` — and it is exactly what stops the WORSE vacuity of
-- `CSP.Examples.RefinementOrderCounterexamples` (`Stop ⊇F (a ⟶ div)`, where the
-- implementation performs a trace the spec cannot).  The liveness hole survives the
-- `_⊑F_` repair: `b` is offered by `Spec` and never by `SysV`, and no trace obligation
-- notices, because `SysV`'s traces are a SUBSET of the spec's.
Spec⊑F-SysV : Spec ⊑F SysV
Spec⊑F-SysV = (λ s (_ , reach) → invV-trace atProducerV reach)
            , (λ s X (_ , reach , ref) → invV-fail atProducerV reach ref)
