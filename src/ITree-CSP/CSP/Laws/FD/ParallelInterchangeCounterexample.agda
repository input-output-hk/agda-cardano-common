{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- NEGATIVE RESULT: the interface-parallel / interleaving INTERCHANGE law
--
--     (P₁ ⦀ P₂) ∥⇘ A ⇙ (Q₁ ⦀ Q₂)   ~   (P₁ ∥⇘ A ⇙ Q₁) ⦀ (P₂ ∥⇘ A ⇙ Q₂)
--
-- is FALSE without a side condition separating the two component alphabets.
--
-- WHY.  On the LEFT, an `A`-event offered by `P₁` may synchronise with the SAME
-- `A`-event offered by `Q₂` — the two operands of `∥⇘ A ⇙` are the whole
-- interleavings, so any pairing across components is available.  On the RIGHT
-- that pairing does not exist: `P₁` is only ever paired with `Q₁`, and `P₂` only
-- with `Q₂`.  A cross-component synchronisation is therefore a LEFT behaviour
-- with no RIGHT counterpart.
--
-- THE WITNESS (`P₁`/`Q₂` offer `h`, their partners are `Stop`, and `A = {h}`):
--
--     P₁ = h ⟶ Stop      P₂ = Stop
--     Q₁ = Stop           Q₂ = h ⟶ Stop
--
--   • LEFT   `(P₁ ⦀ Stop) ∥⇘{h}⇙ (Stop ⦀ Q₂)`  DOES fire `h`: the left operand
--     offers it through `P₁`, the right through `Q₂`, and `h ∈ A`, so they
--     synchronise                                            (`lhs-h`)
--   • RIGHT  `(P₁ ∥⇘{h}⇙ Stop) ⦀ (Stop ∥⇘{h}⇙ Q₂)`  CANNOT fire `h` at all:
--     each `∥⇘{h}⇙` demands its own partner's `h`, and both partners are `Stop`
--                                                            (`rhs-no-h`)
--
-- so the two sides are not bisimilar (`interchange-no-Disj`), and indeed differ
-- already on the length-one trace ⟨h⟩ — the refutation is not an artefact of the
-- relation chosen.
--
-- THE CONDITION THIS ISOLATES.  Every other candidate side condition holds of
-- this witness — `Sep Ah P₁ Q₁` and `Sep Ah P₂ Q₂` are machine-checked below
-- (`sepP`, `sepQ`) — and what fails is exactly alphabet DISJOINTNESS: `h` is
-- offered by `P₁` (a component-1 process) and by `Q₂` (a component-2 process),
-- so no `α₁`, `α₂` confining them can be `Disj` (`disj-would-fail`).  That is
-- precisely the hypothesis `CSP.Laws.FD.ParallelInterchange` assumes.
--
-- ZERO postulates, no NON_TERMINATING, no sized types, no holes.
------------------------------------------------------------------------

open import Level using (Level) renaming (zero to lzero)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.ParallelInterchangeCounterexample where
open PTree

open import CSP.Laws.FSim.HideCounterexample using (Ev; h; c; Ev-≟)
open import CSP.Operators Ev-≟
open EventSet
open import Semantics.LTS   {E = Ev} {I = ExtI Ev}
open import Semantics.Bisim {E = Ev} {I = ExtI Ev} using (_∼_; Sbisim; SSimF)
open import CSP.Laws.Traces.TraceLawsParallel Ev-≟
  using (Par-sync; Par-soloL; Par-soloR)
open import CSP.Laws.Traces.TraceLawsParallelElim Ev-≟
  using (Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Bisim.DRCongruence    Ev-≟ using (Sep)
open import CSP.Laws.Bisim.DRCongruenceRep Ev-≟ using (Alpha; Disj; OffersOnly)

-- the return type of every process here: nothing ever terminates
R0 : Set
R0 = ⊤ {lzero}

-- the ⊤-merge carried by `Par⊤` / `∥⇘_⇙` / `⦀`
tm : R0 → R0 → R0
tm _ _ = tt

------------------------------------------------------------------------
-- The synchronisation set A = {h}
------------------------------------------------------------------------

-- channel-level membership: `h` is in the sync set, `c` is not
isH : AnyTypes Ev → Set
isH (_ , h) = ⊤₀
isH (_ , c) = ⊥

-- ... and its decision
isH? : (at : AnyTypes Ev) → Dec (isH at)
isH? (_ , h) = yes tt₀
isH? (_ , c) = no (λ z → z)

-- the sync set itself
Ah : EventSet
Ah = chanSet isH isH?

------------------------------------------------------------------------
-- The four component processes and the two sides of the law
------------------------------------------------------------------------

-- `Stop` at the fixed return type (avoids repeating the implicit arguments)
stop : PTree Ev (ExtI Ev) R0
stop = Stop

-- component 1 of the LEFT-hand family offers the shared event `h`
P₁ : PTree Ev (ExtI Ev) R0
P₁ = h ⟶₀ stop

-- component 2 of the LEFT-hand family is inert
P₂ : PTree Ev (ExtI Ev) R0
P₂ = stop

-- component 1 of the RIGHT-hand family is inert
Q₁ : PTree Ev (ExtI Ev) R0
Q₁ = stop

-- component 2 of the RIGHT-hand family offers the shared event `h` — the
-- CROSS-component partner of `P₁`, which is what the law cannot reproduce
Q₂ : PTree Ev (ExtI Ev) R0
Q₂ = h ⟶₀ stop

-- the un-regrouped side: one `∥⇘Ah⇙` over the two whole interleavings
lhs : PTree Ev (ExtI Ev) R0
lhs = (P₁ ⦀ P₂) ∥⇘ Ah ⇙ (Q₁ ⦀ Q₂)

-- the regrouped side: component-wise `∥⇘Ah⇙`, then interleaved
rhs : PTree Ev (ExtI Ev) R0
rhs = (P₁ ∥⇘ Ah ⇙ Q₁) ⦀ (P₂ ∥⇘ Ah ⇙ Q₂)

------------------------------------------------------------------------
-- Basic step facts about `Stop` and the prefix
------------------------------------------------------------------------

-- `Stop` is `react ∅v ∅t`: it takes no step whatsoever
stop-no-step : ∀ {l} {M : PTree Ev (ExtI Ev) R0} → stop ─[ l ]─► M → ⊥
stop-no-step (sRet ())
stop-no-step (sSil ())
stop-no-step (sVis refl ())
stop-no-step (sTau refl ())

-- in particular `Stop` offers no visible event
stop-no-vis : ∀ {X} {e : Ev X} {a : X} {M : PTree Ev (ExtI Ev) R0}
            → stop ─[ ev (evl (evLabel X e a)) ]─► M → ⊥
stop-no-vis = stop-no-step

-- the prefix fires its own event (the vis map reduces through `E-≟ (⊤₀,h) (⊤₀,h)`)
h-fires : (h ⟶₀ stop) ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► stop
h-fires = sVis refl refl

------------------------------------------------------------------------
-- The LEFT side fires `h` (cross-component synchronisation)
------------------------------------------------------------------------

-- `P₁ ⦀ P₂` offers `h` solo (the partner `P₂ = Stop` does not offer it)
lhsL-h : (P₁ ⦀ P₂) ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► (stop ⦀ P₂)
lhsL-h = Par-soloL ∅ES tm P₁ P₂ (λ z → z) h-fires refl

-- `Q₁ ⦀ Q₂` offers `h` solo from its SECOND component
lhsR-h : (Q₁ ⦀ Q₂) ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► (Q₁ ⦀ stop)
lhsR-h = Par-soloR ∅ES tm Q₁ Q₂ (λ z → z) h-fires refl

-- ... and since `h ∈ Ah`, the outer `∥⇘Ah⇙` synchronises them: the LEFT side
-- performs `h` by pairing component 1 of one family with component 2 of the other
lhs-h : lhs ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► ((stop ⦀ P₂) ∥⇘ Ah ⇙ (Q₁ ⦀ stop))
lhs-h = Par-sync Ah tm (P₁ ⦀ P₂) (Q₁ ⦀ Q₂) tt₀ lhsL-h lhsR-h

------------------------------------------------------------------------
-- The RIGHT side cannot fire `h` at all
------------------------------------------------------------------------

-- `P₁ ∥⇘Ah⇙ Q₁` is blocked: `h ∈ Ah` needs BOTH operands, and `Q₁ = Stop`
rhsL-no-h : ∀ {M : PTree Ev (ExtI Ev) R0}
          → (P₁ ∥⇘ Ah ⇙ Q₁) ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► M → ⊥
rhsL-no-h st with Par-ev-elim Ah tm P₁ Q₁ st
... | evSync _   _ q = stop-no-vis q
... | evL    ¬cs _   = ¬cs tt₀
... | evR    _   q   = stop-no-vis q
... | evBoth _   _ q = stop-no-vis q

-- `P₂ ∥⇘Ah⇙ Q₂` is blocked for the mirror reason: `P₂ = Stop`
rhsR-no-h : ∀ {M : PTree Ev (ExtI Ev) R0}
          → (P₂ ∥⇘ Ah ⇙ Q₂) ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► M → ⊥
rhsR-no-h st with Par-ev-elim Ah tm P₂ Q₂ st
... | evSync _   p _ = stop-no-vis p
... | evL    _   p   = stop-no-vis p
... | evR    ¬cs _   = ¬cs tt₀
... | evBoth _   p _ = stop-no-vis p

-- hence the interleaving of the two blocked composites cannot fire `h` either
rhs-no-h : ∀ {M : PTree Ev (ExtI Ev) R0}
         → rhs ─[ ev (evl (evLabel ⊤₀ h tt₀)) ]─► M → ⊥
rhs-no-h st with Par-ev-elim ∅ES tm (P₁ ∥⇘ Ah ⇙ Q₁) (P₂ ∥⇘ Ah ⇙ Q₂) st
... | evSync () _ _
... | evL    _  l   = rhsL-no-h l
... | evR    _  r   = rhsR-no-h r
... | evBoth _  l _ = rhsL-no-h l

------------------------------------------------------------------------
-- The refutation
------------------------------------------------------------------------

-- LEFT can do `h`, RIGHT cannot: no bisimulation can relate them.  (The same
-- two facts refute every relation that preserves the length-one trace ⟨h⟩,
-- including ≈DR, ≈FD and `lhs ⊑FD rhs`.)
interchange-no-Disj : ¬ (lhs ∼ rhs)
interchange-no-Disj bis with SSimF.on-ev (Sbisim.fwd bis) lhs-h
... | _ , rstep , _ = rhs-no-h rstep

------------------------------------------------------------------------
-- What exactly fails: DISJOINTNESS, and nothing else
------------------------------------------------------------------------

-- `Sep Ah P Stop` holds for any P — `Stop` never steps, so the two operands can
-- never BOTH offer an outside-`Ah` event.
sep-stopR : ∀ {P : PTree Ev (ExtI Ev) R0} → Sep Ah P stop
sep-stopR .Sep.now _ _ q = ⊥-elim (stop-no-step q)
sep-stopR .Sep.stepL _   = sep-stopR
sep-stopR .Sep.stepR q   = ⊥-elim (stop-no-step q)

-- mirror
sep-stopL : ∀ {Q : PTree Ev (ExtI Ev) R0} → Sep Ah stop Q
sep-stopL .Sep.now _ p _ = ⊥-elim (stop-no-step p)
sep-stopL .Sep.stepL p   = ⊥-elim (stop-no-step p)
sep-stopL .Sep.stepR _   = sep-stopL

-- the per-pair `Sep` hypotheses of the law DO hold of this witness
sepP : Sep Ah P₁ Q₁
sepP = sep-stopR

sepQ : Sep Ah P₂ Q₂
sepQ = sep-stopL

-- ... whereas DISJOINTNESS cannot: `h` is offered by the component-1 process
-- `P₁` and by the component-2 process `Q₂`, so it belongs to BOTH alphabets.
-- This is the single hypothesis whose absence the counterexample exploits.
disj-would-fail : ∀ {α₁ α₂ : Alpha}
                → OffersOnly α₁ P₁ → OffersOnly α₂ Q₂ → Disj α₁ α₂ → ⊥
disj-would-fail oo₁ oo₂ dj =
  dj (⊤₀ , h) tt₀ (OffersOnly.now oo₁ h-fires) (OffersOnly.now oo₂ h-fires)
