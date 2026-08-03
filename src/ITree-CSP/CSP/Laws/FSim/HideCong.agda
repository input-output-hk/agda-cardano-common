{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for HIDING.
--
--   Hide-fsim : FSim R P₁ P₂ → FSim R (P₁ ∖ A) (P₂ ∖ A)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the SECOND
-- the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so this says: if the spec
-- failure-simulates the impl, the hidden spec failure-simulates the hidden impl.  Composed
-- with `fsim→⊑FD` it is a coinductive route to `(P₂ ∖ A) ⊑FD (P₁ ∖ A)`.
--
-- ⚠ NO SIDE CONDITION — and that is a genuinely stronger result than the FD layer's
-- `CSP.Laws.FD.HideMonoFD`, where the unconditional `P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)` is
-- FALSE (`Hide-mono-fail`'s header carries the counterexample: `Q = μX. h → X` versus an
-- infinitely-branching `P = ⊓ₙ (hⁿ ; STOP)`; `Q ∖ {h}` diverges, `P ∖ {h}` does not, and
-- infinite branching defeats König).  That counterexample does NOT refute `Hide-fsim`,
-- and this is now FORMALISED rather than argued in prose:
--
--     CSP.Laws.FSim.HideCounterexample.¬fsim-Pinf-Qh : ¬ (FSim Rt Qh Pinf)
--
-- builds exactly that pair over a concrete alphabet (`Qh = μX. h → X` the impl, `Pinf =
-- ⊓ₙ (hⁿ ; STOP)` the spec) and shows it is not a failure simulation, so it can never be
-- supplied to `Hide-fsim` in the first place.
--
-- NOTE the refutation is STATE-INDEXED, and a TRACE-LEVEL argument would NOT suffice:
-- `μX. h → X` and `⊓ₙ (hⁿ ; STOP)` have exactly the SAME traces (every `hᵏ`; both
-- inclusions are proved there as `Qh-trace` / `Pinf-trace`), so `fsim→⊑T` yields no
-- contradiction whatsoever.  What fails is the per-state obligation `WSimF.on-ev`: a weak
-- `h`-match by the spec must first COMMIT, by a τ, to ONE branch, and then lands in
-- `h^(n-1) ; STOP`, at which the simulation is still required to hold against an impl
-- that is back at `μX. h → X` — refuted by induction on `n` (`¬fsim-chain`).  Conversely
-- the same module proves `fsim-chain-Pinf`: the spec DOES failure-simulate every FINITE
-- `hⁿ ; STOP`, so the obstruction is precisely the impl's unbounded behaviour and not
-- some structural mismatch.  The per-state witness is exactly what the denotational
-- statement lacked.  (The FD half — that `P ⊑FD Q` genuinely holds denotationally — is
-- deliberately NOT formalised; it is not needed, since refuting `Hide-fsim` would require
-- exhibiting an `FSim`, and that is what is shown impossible.)
--
-- The three fields.
--
--   fwd  : the `bwd`-free half of `CSP.Laws.Bisim.DRCongruence`'s `dr-sim-∖`, verbatim up
--          to swapping `DRbisim.fwd` for `FSim.fwd` and the residual `cong-∖` for
--          `Hide-fsim`.  A step of the IMPL `P₁ ∖ A` is inverted with the reused
--          `Hide-ev-elim` / `Hide-τ-elim` into one of four shapes — a surviving non-hidden
--          event, a √ from a `ret`, a τ of `P₁`, or a HIDDEN event turned into a τ — each
--          matched through `FSim.fwd` and re-hidden by the reused `Hide-wev-keep` /
--          `Hide-wev-√` / `Hide-wτ` / `Hide-wev-hidden`.  Fully constructive.
--
--   stab : the field the task brief expected to force a side condition, and it does NOT.
--          `isStable (P₁ ∖ A)` says more than `isStable P₁`: it also says `P₁` offers NO
--          hidden event (`hide-stable-noOffA` — an `A`-offer of `P₁` would be a τ of
--          `P₁ ∖ A` by `Hide-hidden`), which is where maximal progress enters.  Both halves
--          then transfer to the settled spec state:
--            • `hide-stable-elim` (reused) gives `isStable P₁`, which `FSim.stab` turns
--              into a stable `P₂′` with `P₂ ─[τ*]─► P₂′` and `Offers P₂′ ⊆ Offers P₁`;
--            • that INCLUSION DIRECTION is the one we need — it carries "offers nothing
--              hidden" from `P₁` to `P₂′` (had `FSim.stab` given the reverse inclusion the
--              field would be unprovable and a divergence-freedom-style hypothesis would
--              have been forced).
--          `hide-stable-intro` (reused) then makes `P₂′ ∖ A` stable, `Hide-τ*` (reused)
--          lifts the settling run through the hide, and the new `hide-offer-mono` carries
--          the offer inclusion across `∖` (the √ case is impossible — a √-offer needs a
--          `ret` force and `P₂′` is stable).  Fully constructive.
--
--   div→ : the ONLY classical ingredient, exactly as at the ≈DR level.  `Diverges (P₁ ∖ A)`
--          is not `Diverges P₁`: it projects (reused constructive `div∖→modA`) to an
--          infinite path of `P₁` mixing τ's and hidden events, `DivModA A P₁`, and re-hides
--          (reused constructive `modA→div∖`).  The transfer in between is the König step —
--          a hidden impl event is matched by a WEAK spec event, which always contributes
--          ≥ 1 spec step, but an impl τ may be matched by an EMPTY spec run, so a path with
--          only finitely many hidden events can stall the spec.  Rather than introduce a new
--          postulate (`CSP.Laws.Bisim.DRCongruence.modA-transfer` cannot be reused: it
--          consumes a full `DRbisim`, which an `FSim` cannot supply) the transfer is DERIVED
--          from TWO PRE-EXISTING repo postulates, both certified from the single `dne` of
--          `CSP.Laws.ClassicalFromLEM`:
--            • `Diverges-LEM` (`CSP.Laws.FD.FDTransfer`, Derivation 10) decides, at each
--              round, whether the impl τ-diverges HERE.  If it does, `FSim.div→` hands over
--              the whole spec divergence at once (`diverges→modA`).
--            • `¬DivModA→MAcc` (`CSP.Laws.FD.HideDivergence`, Derivation 9) instantiated at
--              the EMPTY hidden set turns the other branch's `¬ Diverges P₁` into τ-ACCESS-
--              IBILITY `MAcc ∅ES P₁` (at `∅ES` a `ModAStep` is just a τ, `modA∅→diverges`),
--              the positive/inductive form that lets `hide-fsim-round` SEARCH forward along
--              the impl path for the next hidden event by well-founded recursion.
--          Each round therefore emits ≥ 1 spec `ModAStep`, so `hide-fsim-modA` is productive
--          (`hide-fsim-tail` walks the round's run under the `maRest` copattern and only
--          then re-enters `hide-fsim-modA`).  This is the same reliance on the same certified
--          König family that `CSP.Laws.FSim.ParCong.Par-fsim-div→` has on `Par-Diverges→`
--          and `DRCongruence.cong-∖` has on `modA-transfer`.
--
-- This module declares NO postulate, no NON_TERMINATING, no sized type and no hole.
-- `fwd` and `stab` are classical-ingredient-free; `div→` uses the two named pre-existing
-- certified postulates and nothing else.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FSim.HideCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability  {E = E} {I = ExtI E} using (stable-no-τ; stable-not-ret)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E} using (FSim; fsim-refl)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using ( Hide-τ; Hide-keep; Hide-hidden; Hide-√
        ; Hide-τ-elim; Hide-ev-elim; HideτR; hτP; hτH; HideevR; heV; he√)
open import CSP.Laws.Bisim.DRCongruence E-≟
  using ( Hide-τ*; Hide-wτ; Hide-wev-keep; Hide-wev-hidden; Hide-wev-√
        ; ModAStep; maτ; maE; DivModA; div∖→modA; modA→div∖)
open import CSP.Laws.FD.HideDivergence E-≟ using (MAcc; macc; ¬DivModA→MAcc)
open import CSP.Laws.FD.HideMonoFD E-≟ using (hide-stable-elim; hide-stable-intro)
open import CSP.Laws.FD.FDTransfer E-≟ using (Diverges-LEM)
open DivModA

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- STABILITY / OFFERS across the hide — the ingredients of `stab`.
-------------------------------------------------------------------------------------

-- MAXIMAL PROGRESS, elimination form: a stable `P ∖ A` forces `P` to offer NO hidden
-- event, since such an offer would be a τ of `P ∖ A` (`Hide-hidden`).
hide-stable-noOffA : (A : EventSet) (P : PTree E (ExtI E) R) → isStable (P ∖ A)
                   → ∀ {B : Set ℓ} {e : E B} {a : B}
                   → A .mem (B , e) a → ¬ Offers P (evl (evLabel B e a))
hide-stable-noOffA A P st mem (P′ , step) = stable-no-τ st (Hide-hidden A P mem step)

-- OFFER MONOTONICITY through the hide: an offer of `Pₛ ∖ A` is a surviving (non-hidden)
-- offer of `Pₛ`, included in `P`'s offers by hypothesis, and re-hides by `Hide-keep`.
-- The √ case cannot arise — a √-offer needs a `ret` force and `Pₛ` is stable.
hide-offer-mono : (A : EventSet) (P Pₛ : PTree E (ExtI E) R) → isStable Pₛ
                → (∀ e → Offers Pₛ e → Offers P e)
                → ∀ e → Offers (Pₛ ∖ A) e → Offers (P ∖ A) e
hide-offer-mono A P Pₛ st incl e (M , step) with Hide-ev-elim A Pₛ step
... | heV {B} {e = e′} {a = a} P′ ¬mem Pev
      with incl (evl (evLabel B e′ a)) (P′ , Pev)
...   | P″ , P″ev = (P″ ∖ A) , Hide-keep A P ¬mem P″ev
hide-offer-mono A P Pₛ st incl e (M , step) | he√ fpP =
  ⊥-elim (stable-not-ret {t = Pₛ} st fpP)

-- THE `stab` FIELD.  No side condition: `hide-stable-elim` + `hide-stable-noOffA` split the
-- composite's stability into "P₁ stable" and "P₁ offers nothing hidden", the operand's own
-- `FSim.stab` settles the spec, and the offer inclusion it returns carries BOTH halves over.
hide-fsim-stab : (A : EventSet) {P₁ P₂ : PTree E (ExtI E) R}
               → FSim R P₁ P₂ → isStable (P₁ ∖ A)
               → Σ[ M ∈ PTree E (ExtI E) R ]
                   ( (P₂ ∖ A) ─[τ*]─► M × isStable M
                   × (∀ e → Offers M e → Offers (P₁ ∖ A) e) )
hide-fsim-stab A {P₁} {P₂} sim st with sim .FSim.stab (hide-stable-elim A P₁ st)
... | P₂′ , run , st′ , incl =
      (P₂′ ∖ A)
    , Hide-τ* A P₂ run
    , hide-stable-intro A P₂′ st′
        (λ mem off → hide-stable-noOffA A P₁ st mem (incl (evl (evLabel _ _ _)) off))
    , hide-offer-mono A P₁ P₂′ st′ incl

-------------------------------------------------------------------------------------
-- DIVERGENCE under hiding — the `div→` field.
--
-- `A`-modulo RUNS (the reflexive-transitive closure of `ModAStep`), so that a finite
-- stretch of spec progress can be handed around as data.
-------------------------------------------------------------------------------------

-- a finite `A`-modulo run: each step a τ or a hidden `A`-event (i.e. a τ-run of `t ∖ A`)
data ModA* {ℓr} {R : Set ℓr} (A : EventSet)
     : PTree E (ExtI E) R → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  ma-refl : {t : PTree E (ExtI E) R} → ModA* A t t
  ma-cons : {t t′ t″ : PTree E (ExtI E) R}
          → ModAStep A t t′ → ModA* A t′ t″ → ModA* A t t″

-- a plain τ*-run is in particular an `A`-modulo run
τ*→ModA* : (A : EventSet) {t t′ : PTree E (ExtI E) R}
         → t ─[τ*]─► t′ → ModA* A t t′
τ*→ModA* A τ*-refl          = ma-refl
τ*→ModA* A (τ*-step s rest) = ma-cons (maτ s) (τ*→ModA* A rest)

-- `A`-modulo runs compose
ModA*-trans : (A : EventSet) {t t′ t″ : PTree E (ExtI E) R}
            → ModA* A t t′ → ModA* A t′ t″ → ModA* A t t″
ModA*-trans A ma-refl        r₂ = r₂
ModA*-trans A (ma-cons s r₁) r₂ = ma-cons s (ModA*-trans A r₁ r₂)

-- a τ-divergence is an `A`-modulo divergence (every τ is a `ModAStep`)
diverges→modA : (A : EventSet) {t : PTree E (ExtI E) R} → Diverges t → DivModA A t
diverges→modA A d .maNext = d .Diverges.next
diverges→modA A d .maStep = maτ (d .Diverges.step)
diverges→modA A d .maRest = diverges→modA A (d .Diverges.rest)

-- at the EMPTY hidden set a `ModAStep` can only be a τ (nothing is a member of `∅ES`)
modA∅-step : {t t′ : PTree E (ExtI E) R} → ModAStep ∅ES t t′ → t ─[ τ ]─► t′
modA∅-step (maτ s)     = s
modA∅-step (maE mem _) = ⊥-elim mem

-- …hence an `∅ES`-modulo divergence is a plain τ-divergence.  This is what lets the
-- `MAcc` König postulate be instantiated at `∅ES` to obtain τ-ACCESSIBILITY.
modA∅→diverges : {t : PTree E (ExtI E) R} → DivModA ∅ES t → Diverges t
modA∅→diverges dm .Diverges.next = dm .maNext
modA∅→diverges dm .Diverges.step = modA∅-step (dm .maStep)
modA∅→diverges dm .Diverges.rest = modA∅→diverges (dm .maRest)

-- ONE PRODUCTIVE ROUND of the spec's `A`-modulo divergence: a NONEMPTY spec run (its first
-- step held separately, which is what makes the round productive), ending in a spec state
-- that still failure-simulates an `A`-modulo-diverging impl state.
record Round {ℓr} {R : Set ℓr} (A : EventSet) (Q : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  field
    {rMid}  : PTree E (ExtI E) R          -- spec state after the round's FIRST step
    {rEnd}  : PTree E (ExtI E) R          -- spec state after the whole round
    {rImpl} : PTree E (ExtI E) R          -- impl state reached in step with it
    rStep   : ModAStep A Q rMid
    rRun    : ModA* A rMid rEnd
    rSim    : FSim R rImpl rEnd
    rDiv    : DivModA A rImpl
open Round

-- a spec run taken BEFORE a round is absorbed into it (the round stays nonempty)
Round-prepend : (A : EventSet) {Q Q′ : PTree E (ExtI E) R}
              → ModA* A Q Q′ → Round A Q′ → Round A Q
Round-prepend A ma-refl        rd = rd
Round-prepend A (ma-cons s r) rd = record
  { rStep = s
  ; rRun  = ModA*-trans A r (ma-cons (rd .rStep) (rd .rRun))
  ; rSim  = rd .rSim
  ; rDiv  = rd .rDiv
  }

-- THE SEARCH.  Walk the impl's `A`-modulo divergence, matching each step on the spec side,
-- until a HIDDEN impl event is met: that step is matched by a WEAK spec event whose middle
-- transition is a real (hidden) step, so the accumulated spec run is nonempty.  An impl τ,
-- whose spec match may be EMPTY, consumes one τ-accessibility step instead — so the walk is
-- a well-founded recursion on `MAcc ∅ES` and must end at a hidden event.
hide-fsim-round : (A : EventSet) {P Q : PTree E (ExtI E) R}
                → MAcc ∅ES P → DivModA A P → FSim R P Q → Round A Q
hide-fsim-round A {P} {Q} (macc rs) dm sim with dm .maStep
-- an impl τ: match it weakly (possibly by nothing at all) and keep searching
... | maτ step with sim .FSim.fwd .WSimF.on-tau step
...   | Q′ , wτ run , sim′ =
        Round-prepend A (τ*→ModA* A run)
          (hide-fsim-round A (rs (maτ step)) (dm .maRest) sim′)
-- a HIDDEN impl event: the spec's weak match contains a real hidden step ⇒ round complete
hide-fsim-round A {P} {Q} (macc rs) dm sim | maE mem hev
  with sim .FSim.fwd .WSimF.on-ev hev
...   | Q′ , wev q→q₁ q₁ev q₂→q′ , sim′ =
        Round-prepend A (τ*→ModA* A q→q₁)
          (record { rStep = maE mem q₁ev
                  ; rRun  = τ*→ModA* A q₂→q′
                  ; rSim  = sim′
                  ; rDiv  = dm .maRest })

-- THE TRANSFER.  Forward declarations (no old-style mutual block): `hide-fsim-modA` emits a
-- round, `hide-fsim-out` puts the round's FIRST step under the `maStep` copattern, and
-- `hide-fsim-tail` walks the round's remaining run under the `maRest` copattern before
-- re-entering `hide-fsim-modA` — so every cycle passes through a coinductive copattern and
-- the corecursion is productive.
hide-fsim-modA : (A : EventSet) {P Q : PTree E (ExtI E) R}
               → DivModA A P → FSim R P Q → DivModA A Q
hide-fsim-out  : (A : EventSet) {Q : PTree E (ExtI E) R} → Round A Q → DivModA A Q
hide-fsim-tail : (A : EventSet) {P Q Q′ : PTree E (ExtI E) R}
               → ModA* A Q Q′ → DivModA A P → FSim R P Q′ → DivModA A Q

hide-fsim-out A rd .maNext = rd .rMid
hide-fsim-out A rd .maStep = rd .rStep
hide-fsim-out A rd .maRest = hide-fsim-tail A (rd .rRun) (rd .rDiv) (rd .rSim)

hide-fsim-tail A ma-refl        dm sim = hide-fsim-modA A dm sim
hide-fsim-tail A (ma-cons {t′ = mid} s r) dm sim .maNext = mid
hide-fsim-tail A (ma-cons s r) dm sim .maStep = s
hide-fsim-tail A (ma-cons s r) dm sim .maRest = hide-fsim-tail A r dm sim

-- the round-by-round transfer: either the impl τ-diverges HERE — and `FSim.div→` hands the
-- whole spec divergence over at once — or it does not, and the search finds the next hidden
-- event after finitely many τ-accessibility steps.
hide-fsim-modA A {P} {Q} dm sim with Diverges-LEM P
... | inj₁ d  = diverges→modA A (sim .FSim.div→ d)
... | inj₂ nd = hide-fsim-out A
                  (hide-fsim-round A
                    (¬DivModA→MAcc ∅ES (λ dm∅ → nd (modA∅→diverges dm∅))) dm sim)

-- THE `div→` FIELD: project the composite divergence to an `A`-modulo divergence of the
-- impl (reused `div∖→modA`), transfer it, re-hide it (reused `modA→div∖`).
hide-fsim-div→ : (A : EventSet) {P₁ P₂ : PTree E (ExtI E) R}
               → FSim R P₁ P₂ → Diverges (P₁ ∖ A) → Diverges (P₂ ∖ A)
hide-fsim-div→ A {P₁} {P₂} sim d =
  modA→div∖ A P₂ (hide-fsim-modA A (div∖→modA A P₁ d) sim)

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations again: the corecursive `Hide-fsim` residuals sit
-- under the `WSimF` Σ-results of `f-sim-∖`, the discipline `DRCongruence.dr-sim-∖` uses.
-- The operands are passed as ARGUMENTS to every lift lemma and never `with`-forced at the
-- call site, so no `P ∖ A` is ever driven to weak head normal form here.
-------------------------------------------------------------------------------------

-- HEADLINE: hiding is an FSim congruence, with NO side condition
Hide-fsim : (A : EventSet) {P₁ P₂ : PTree E (ExtI E) R}
          → FSim R P₁ P₂ → FSim R (P₁ ∖ A) (P₂ ∖ A)

-- the forward-simulation half: invert an impl step of `P₁ ∖ A`, match the underlying
-- `P₁`-step, re-hide the spec's weak match
f-sim-∖ : (A : EventSet) {P₁ P₂ : PTree E (ExtI E) R}
        → FSim R P₁ P₂ → WSimF (FSim R) (P₁ ∖ A) (P₂ ∖ A)
-- a surviving (non-hidden) visible event
f-sim-∖ A {P₁} {P₂} sim .WSimF.on-ev step with Hide-ev-elim A P₁ step
... | heV {B} {e} {a} P′ ¬mem Pev with sim .FSim.fwd .WSimF.on-ev Pev
...   | P₂′ , wP , rel = (P₂′ ∖ A) , Hide-wev-keep A P₂ ¬mem wP , Hide-fsim A rel
-- termination: √ passes through the hide and lands in `deadlock`
f-sim-∖ A {P₁} {P₂} sim .WSimF.on-ev step | he√ {r} fpP
  with sim .FSim.fwd .WSimF.on-ev (sRet fpP)
...   | _ , wP , _ = deadlock , Hide-wev-√ A P₂ wP , fsim-refl deadlock
-- a τ of the operand stays a τ
f-sim-∖ A {P₁} {P₂} sim .WSimF.on-tau step with Hide-τ-elim A P₁ step
... | hτP P′ Pτ refl with sim .FSim.fwd .WSimF.on-tau Pτ
...   | P₂′ , wτ run , rel = (P₂′ ∖ A) , Hide-wτ A P₂ (wτ run) , Hide-fsim A rel
-- a HIDDEN event of the operand becomes a τ, matched by the spec's weak event re-hidden
f-sim-∖ A {P₁} {P₂} sim .WSimF.on-tau step | hτH {B} {e} {a} P′ mem Pev refl
  with sim .FSim.fwd .WSimF.on-ev Pev
...   | P₂′ , wP , rel = (P₂′ ∖ A) , Hide-wev-hidden A P₂ mem wP , Hide-fsim A rel

Hide-fsim A sim .FSim.fwd     = f-sim-∖ A sim
Hide-fsim A sim .FSim.stab st = hide-fsim-stab A sim st
Hide-fsim A sim .FSim.div→ d  = hide-fsim-div→ A sim d
