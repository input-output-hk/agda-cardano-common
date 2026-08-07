{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for THROW (Roscoe's `P [|A|> Q`, here `_⟦_▷_`).
--
--   Θ-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ⟦ A ▷ Q₁) (P₂ ⟦ A ▷ Q₂)
--
-- TWO-SIDED and UNCONDITIONAL — no divergence-freedom hypothesis, no `Sep`-style
-- separation condition, no side condition of any kind.  ORIENTATION: in `FSim R t₁ t₂`
-- the FIRST argument is the IMPLEMENTATION and the SECOND the SPECIFICATION
-- (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so the reading is: if the spec failure-simulates
-- the impl in BOTH the body and the handler, the composed spec failure-simulates the
-- composed impl.  For the REFINEMENT form, write `fsim→⊑FD (Θ-fsim A … …)`: the
-- `-mono-⊑FD` name now belongs to the FACT-SHAPED (`⊑FD → ⊑FD`) precongruence in
-- `CSP.Laws.FD.ThrowMonoFD`, which is strictly stronger — the shape-3 cash-out wrapper
-- that used to sit at the bottom of this module was retired in its favour (see
-- `CSP.Laws.FD.Congruences`'s POLICY note for the three-shape taxonomy).
--
-- ⭐ `--safe` CLEAN.  `agda --safe CSP/Laws/FSim/ThrowCong.agda` succeeds: the entire
-- import closure is postulate-free — no `dne`, no König family, no `Diverges-LEM`, no
-- `offer-LEM`, nothing classical anywhere.  Of the FSim congruences only
-- `CSP.Laws.FSim.IChoiceCong` (`⊓-fsim`, `prefix-fsim`) was `--safe` before this one, and
-- those two operators never inspect an operand's `force` at all — their composite is a
-- FIXED `react` node.  So this is the first `--safe` FSim congruence for an operator that
-- DECONSTRUCTS a live operand (`□`/`▷`/`Par`/`⦀`/`∖`/`>>=`/`loop`/αpar all fail `--safe`,
-- on `□-Diverges→`, `Par-Diverges→`, `αpar-Diverges→` or `offer-LEM`).  Two facts make
-- that possible:
--   • `Θ-Diverges→` is STRUCTURAL (unlike `△-Diverges→` / `Par-Diverges→` / the hide's
--     `modA` transfer): the composite's ONLY τ-moves are the body's τ-moves, so an
--     infinite τ-path of `P ⟦ A ▷ Q` projects to an infinite τ-path of `P` step by step
--     with no search and no bar induction.  `div→` is therefore literally
--     `Θ-Diverges-L ∘ FSim.div→ ∘ Θ-Diverges→`.
--   • the six Throw step/divergence lemmas it needs were HOISTED (commit before this one)
--     from `CSP.Laws.FD.ThrowFD` — which drags in the classical `Semantics.DRImpliesFD` —
--     into `CSP.Laws.Traces.TraceLawsThrowInterrupt`, which is itself `--safe` clean.
--
-- WHY THROW IS THE EASY OPERATOR.  `force (P ⟦ A ▷ Q)` inspects ONLY `P`, and the whole
-- composite LTS is a function of the body's LTS:
--   • the τ-space of the composite IS the body's τ-space — there is no extra τ (contrast
--     `▷`, whose slide-τ commits to `Q`), hence no `sil`-masking (the αpar killer) and a
--     structural divergence projection in BOTH directions;
--   • the visible offers of the composite are exactly the body's offers: `Θ-vis` returns
--     `just` for *every* body offer, only the TARGET depends on `A .dec at a` (fire → `Q`,
--     pass → `P′ ⟦ A ▷ Q`).  So no both-offer overlap can arise and no `Sep` hypothesis
--     is needed — `A`-membership is decisive;
--   • the handler is DORMANT until a visible `A`-event fires the throw, so `Q` can never
--     act before the trigger, and the trigger is CONSUMED, so the handler starts at once.
--
-- The `Θthrow` arm of `on-ev` is where the two-sidedness comes for free, and it is worth
-- spelling out: the impl fires on the visible label `ℓ = evl (evLabel _ _ a)`.  The spec
-- BODY weakly matches the SAME `ℓ` (that is what `WSimF.on-ev` gives), hence the same
-- `at`/`a`, hence the SAME `A .dec at a` branch — so the spec composite fires too, and
-- lands on `Q₂` while the impl lands on `Q₁`.  The residual obligation is exactly
-- `FSim R Q₁ Q₂`, discharged by the hypothesis with NO invariant extension and NO
-- corecursion.  (This is why the handler needs no relation between `Q₁`/`Q₂` and the
-- bodies: the fire discards both bodies simultaneously.)
--
-- The three fields.
--
--   fwd  : `Θ-τ-elim` / `Θ-ev-elim` (reused from the trace layer) invert an impl step into
--          one of four shapes — a body τ, a passing (non-`A`) body event, a firing (`A`)
--          body event, or the body's √ from a `ret` — each matched through `FSim.fwd` and
--          re-lifted by the new `Θ-wτ` / `Θ-wev-pass` / `Θ-wev-fire` / `Θ-wev-√`.  The
--          corecursive residual is `Θ-fsim` itself for the τ and pass arms, the handler
--          hypothesis for the fire arm, and `fsim-refl deadlock` for the √ arm.
--
--   stab : `isStable (P₁ ⟦ A ▷ Q₁)` ⟺ `isStable P₁` — the composite's τ-map is the body's,
--          so stability transfers BOTH ways with no maximal-progress side condition (this
--          is strictly simpler than hiding, where `hide-stable-noOffA` was needed).  The
--          body's own `FSim.stab` settles the spec body at a stable `P₂′`, `Θ-τ*-L` lifts
--          the settling run through the throw, `Θ-stable-intro` re-stabilises, and
--          `Θ-offer-mono` carries the offer inclusion across `⟦ A ▷ ·` by re-firing /
--          re-passing the transported body offer (the √ case is impossible — a √-offer
--          needs a `ret` force and `P₂′` is stable).  Fully constructive.
--
--   div→ : two lines, as described above.  Fully constructive.
--
-- This module declares NO postulate, no NON_TERMINATING, no sized type and no hole.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FSim.ThrowCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS        {E = E} {I = ExtI E}
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability  {E = E} {I = ExtI E}
  using (stable-not-ret; stable-no-τ; stable→react; mk-stable; react-no-τ→stable)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_⊑FD_)
open import Semantics.FailureSim {E = E} {I = ExtI E} using (FSim; fsim-refl; fsim→⊑FD)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using ( force-Θ-ret; force-Θ-react; force-Θ-sil
        ; Θ-τ-elim; Θ-ev-elim; ΘevR; Θthrow; Θpass; Θdone
        ; Θ-τ-lift-P; Θ-throw-step; Θ-pass-step; Θ-Diverges→; Θ-Diverges-L )

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- WEAK LIFTS.  The composite's moves are the body's moves, so every weak run of the
-- body re-lifts through `⟦ A ▷ Q` — the handler `Q` is passed as an ARGUMENT to each
-- lemma and is never `with`-forced, so no `P ⟦ A ▷ Q` is driven to whnf here.
-------------------------------------------------------------------------------------

-- a τ*-run of the body lifts through the throw (iterated `Θ-τ-lift-P`)
Θ-τ*-L : (A : EventSet) (Q : PTree E (ExtI E) R) {P P′ : PTree E (ExtI E) R}
       → P ─[τ*]─► P′ → (P ⟦ A ▷ Q) ─[τ*]─► (P′ ⟦ A ▷ Q)
Θ-τ*-L A Q τ*-refl              = τ*-refl
Θ-τ*-L A Q (τ*-step {t′ = P″} s rest) =
  τ*-step (Θ-τ-lift-P {P′ = P″} {Q = Q} {A = A} s) (Θ-τ*-L A Q rest)

-- a WEAK τ of the body lifts through the throw (its whole τ*-run is lifted)
Θ-wτ : (A : EventSet) (Q : PTree E (ExtI E) R) {P P′ : PTree E (ExtI E) R}
     → P ═[ τ ]═► P′ → (P ⟦ A ▷ Q) ═[ τ ]═► (P′ ⟦ A ▷ Q)
Θ-wτ A Q (wτ run) = wτ (Θ-τ*-L A Q run)

-- a weak NON-`A` visible run of the body lifts through the throw unchanged: the leading
-- and trailing τ*-runs lift, and the middle step passes by `Θ-pass-step`.
Θ-wev-pass : (A : EventSet) (Q : PTree E (ExtI E) R) {P P′ : PTree E (ExtI E) R}
               {at : AnyTypes E} {a : proj₁ at}
           → P ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► P′ → ¬ (A .mem at a)
           → (P ⟦ A ▷ Q) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► (P′ ⟦ A ▷ Q)
Θ-wev-pass A Q (wev pre stp post) ¬m =
  wev (Θ-τ*-L A Q pre) (Θ-pass-step {X = Q} stp ¬m) (Θ-τ*-L A Q post)

-- a weak `A`-visible run of the body FIRES the throw: the leading τ*-run lifts, the
-- middle step transfers control to `Q`, and the body's TRAILING τ*-run is DISCARDED
-- (the body is thrown away at the fire, so it can contribute nothing afterwards).
Θ-wev-fire : (A : EventSet) (Q : PTree E (ExtI E) R) {P P′ : PTree E (ExtI E) R}
               {at : AnyTypes E} {a : proj₁ at}
           → P ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► P′ → A .mem at a
           → (P ⟦ A ▷ Q) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► Q
Θ-wev-fire A Q (wev pre stp post) m =
  wev (Θ-τ*-L A Q pre) (Θ-throw-step {X = Q} stp m) τ*-refl

-- a weak √ of the body lifts: `force (P ⟦ A ▷ Q)` IS `force P` at a `ret`, so the
-- composite performs the same √ and lands in `deadlock` (trailing τ*-run discarded).
-- The middle step can only be `sRet` — `sVis` produces an `evl` label, not a `√`.
Θ-wev-√ : (A : EventSet) (Q : PTree E (ExtI E) R) {P P′ : PTree E (ExtI E) R} {r : R}
        → P ═[ ev (√ r) ]═► P′ → (P ⟦ A ▷ Q) ═[ ev (√ r) ]═► deadlock
-- (the run's midpoint `P₁` is named: `_⟦_▷_` is a defined function, so the unifier
-- cannot recover it from `force (P₁ ⟦ A ▷ Q)` and `force-Θ-ret`'s `P` must be given)
Θ-wev-√ A Q (wev {p′ = P₁} pre (sRet eqf) post) =
  wev (Θ-τ*-L A Q pre) (sRet (force-Θ-ret {P = P₁} {Q = Q} {A = A} eqf)) τ*-refl

-------------------------------------------------------------------------------------
-- STABILITY / OFFERS across the throw — the ingredients of `stab`.
--
-- `Θ-τ A nP Q i a` is `just _` exactly when `viewT nP i a` is, so the composite's
-- τ-branching IS the body's: stability transfers in BOTH directions, unconditionally.
-------------------------------------------------------------------------------------

-- the composite's τ-map is `nothing` wherever the body's `viewT` is (re-doing the
-- `with viewT nP i a` of `Θ-τ`'s definition is what lets the clause reduce)
Θ-τ-nothing : (nP : NodeKind E (ExtI E) R) (A : EventSet) (Q : PTree E (ExtI E) R)
                {i : AnyTypes (ExtI E)} {a : proj₁ i}
            → viewT nP i a ≡ nothing → Θ-τ A nP Q i a ≡ nothing
Θ-τ-nothing nP A Q {i = i} {a = a} eq with viewT nP i a
... | just _  = case eq of λ ()
... | nothing = refl

-- STABILITY, elimination form, keyed on a PROPOSITIONAL force-equation for the body (so
-- no `with PTree.force P` is needed at the call site, which would reduce the composite's
-- `isStable` hypothesis).  `ret` is refuted because the composite then forces to `ret`
-- too; `sil` is refuted because the body's `sil`-τ lifts to a τ of the composite.
Θ-stable-elim-at : (A : EventSet) (Q P : PTree E (ExtI E) R)
                     (nP : NodeKind E (ExtI E) R)
                 → PTree.force P ≡ nP → isStable (P ⟦ A ▷ Q) → isStable P
Θ-stable-elim-at A Q P (ret r) eqP st =
  ⊥-elim (stable-not-ret {t = P ⟦ A ▷ Q} st (force-Θ-ret {P = P} {Q = Q} {A = A} eqP))
Θ-stable-elim-at A Q P (sil P₁) eqP st =
  ⊥-elim (stable-no-τ {t = P ⟦ A ▷ Q} st
            (Θ-τ-lift-P {P = P} {P′ = P₁} {Q = Q} {A = A} (sSil eqP)))
Θ-stable-elim-at A Q P (react v τc) eqP st =
  react-no-τ→stable {t = P} eqP
    (λ pτ → stable-no-τ {t = P ⟦ A ▷ Q} st (Θ-τ-lift-P {P = P} {Q = Q} {A = A} pτ))

-- STABILITY, elimination form: a stable composite has a stable body.  (Instantiating the
-- `-at` version at `PTree.force P` / `refl` is what performs the force case-split.)
Θ-stable-elim : (A : EventSet) (Q : PTree E (ExtI E) R) {P : PTree E (ExtI E) R}
              → isStable (P ⟦ A ▷ Q) → isStable P
Θ-stable-elim A Q {P = P} st = Θ-stable-elim-at A Q P (PTree.force P) refl st

-- STABILITY, introduction form: a stable body makes the composite stable.  No maximal
-- progress condition: the composite offers no τ that the body did not already offer.
Θ-stable-intro : (A : EventSet) (Q : PTree E (ExtI E) R) {P : PTree E (ExtI E) R}
               → isStable P → isStable (P ⟦ A ▷ Q)
Θ-stable-intro A Q {P = P} st with stable→react {t = P} st
... | v , τc , eqP , h =
      mk-stable {t = P ⟦ A ▷ Q} (force-Θ-react {P = P} {Q = Q} {A = A} eqP)
                (λ i a → Θ-τ-nothing (react v τc) A Q {i = i} {a = a} (h i a))

-- OFFER MONOTONICITY through the throw.  An offer of `P₂ ⟦ A ▷ Q₂` inverts (`Θ-ev-elim`)
-- to a body offer of `P₂` at the same event, which the hypothesis transports to an offer
-- of `P₁`; the SAME `A`-decision then re-fires (`Θ-throw-step`, target `Q₁`) or re-passes
-- (`Θ-pass-step`) it on the impl side.  The √ arm cannot arise — a √-offer needs a `ret`
-- force and `P₂` is stable.
Θ-offer-mono : (A : EventSet) (Q₁ Q₂ : PTree E (ExtI E) R) {P₁ P₂ : PTree E (ExtI E) R}
             → isStable P₂ → (∀ l → Offers P₂ l → Offers P₁ l)
             → ∀ l → Offers (P₂ ⟦ A ▷ Q₂) l → Offers (P₁ ⟦ A ▷ Q₁) l
Θ-offer-mono A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂} st incl l (M , step)
  with Θ-ev-elim P₂ Q₂ step
... | Θthrow {at = at} {a = a} {P₁ = P′} pev m
      with incl (evl (evLabel (proj₁ at) (proj₂ at) a)) (P′ , pev)
...   | (P″ , P″ev) =
        Q₁ , Θ-throw-step {P = P₁} {P′ = P″} {X = Q₁} {A = A} {at = at} {a = a} P″ev m
Θ-offer-mono A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂} st incl l (M , step)
    | Θpass {at = at} {a = a} {P₁ = P′} pev ¬m
      with incl (evl (evLabel (proj₁ at) (proj₂ at) a)) (P′ , pev)
...   | (P″ , P″ev) =
        (P″ ⟦ A ▷ Q₁)
      , Θ-pass-step {P = P₁} {P′ = P″} {X = Q₁} {A = A} {at = at} {a = a} P″ev ¬m
Θ-offer-mono A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂} st incl l (M , step) | Θdone fpP =
  ⊥-elim (stable-not-ret {t = P₂} st fpP)

-- THE `stab` FIELD.  Split the composite's stability into the body's (`Θ-stable-elim`),
-- settle the spec body with its own `FSim.stab`, lift the settling run (`Θ-τ*-L`),
-- re-stabilise (`Θ-stable-intro`) and transport the offers (`Θ-offer-mono`).
Θ-fsim-stab : (A : EventSet) (Q₁ Q₂ : PTree E (ExtI E) R) {P₁ P₂ : PTree E (ExtI E) R}
            → FSim R P₁ P₂ → isStable (P₁ ⟦ A ▷ Q₁)
            → Σ[ M ∈ PTree E (ExtI E) R ]
                ( (P₂ ⟦ A ▷ Q₂) ─[τ*]─► M × isStable M
                × (∀ l → Offers M l → Offers (P₁ ⟦ A ▷ Q₁) l) )
Θ-fsim-stab A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂} sim st
  with sim .FSim.stab (Θ-stable-elim A Q₁ {P = P₁} st)
... | P₂′ , run , st′ , incl =
      (P₂′ ⟦ A ▷ Q₂)
    , Θ-τ*-L A Q₂ run
    , Θ-stable-intro A Q₂ {P = P₂′} st′
    , Θ-offer-mono A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂′} st′ incl

-------------------------------------------------------------------------------------
-- DIVERGENCE across the throw — the `div→` field.  STRUCTURAL in both directions
-- (`Θ-Diverges→` projects the composite's infinite τ-path onto the body's, `Θ-Diverges-L`
-- re-lifts it), so no König step and no classical principle are involved.
-------------------------------------------------------------------------------------

-- THE `div→` FIELD: project to the body, transfer with the body's own `div→`, re-lift.
Θ-fsim-div→ : (A : EventSet) (Q₁ Q₂ : PTree E (ExtI E) R) {P₁ P₂ : PTree E (ExtI E) R}
            → FSim R P₁ P₂ → Diverges (P₁ ⟦ A ▷ Q₁) → Diverges (P₂ ⟦ A ▷ Q₂)
Θ-fsim-div→ A Q₁ Q₂ {P₁ = P₁} {P₂ = P₂} sim d =
  Θ-Diverges-L {P = P₂} {Q = Q₂} {A = A}
    (sim .FSim.div→ (Θ-Diverges→ {P = P₁} {Q = Q₁} {A = A} d))

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations (no old-style `mutual`): the corecursive
-- `Θ-fsim` residuals sit under the `WSimF` Σ-results of `f-sim-Θ`, the discipline
-- `HideCong.f-sim-∖` uses.  Both operands are passed as ARGUMENTS to every lift lemma.
-------------------------------------------------------------------------------------

-- HEADLINE: throw is an FSim congruence in BOTH operands, with NO side condition
Θ-fsim : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
       → FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ⟦ A ▷ Q₁) (P₂ ⟦ A ▷ Q₂)

-- the forward-simulation half: invert an impl step of `P₁ ⟦ A ▷ Q₁`, match the underlying
-- `P₁`-step, re-lift the spec body's weak match through `⟦ A ▷ Q₂`
f-sim-Θ : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
        → FSim R P₁ P₂ → FSim R Q₁ Q₂ → WSimF (FSim R) (P₁ ⟦ A ▷ Q₁) (P₂ ⟦ A ▷ Q₂)
-- a τ of the body stays a τ; the handler is untouched, so the residual is corecursive
f-sim-Θ A {P₁} {P₂} {Q₁} {Q₂} simP simQ .WSimF.on-tau step with Θ-τ-elim P₁ Q₁ step
... | (P′ , Pτ , refl) with simP .FSim.fwd .WSimF.on-tau Pτ
...   | P₂′ , w , rel = (P₂′ ⟦ A ▷ Q₂) , Θ-wτ A Q₂ w , Θ-fsim A rel simQ
-- a visible step: fire, pass, or the body's √
f-sim-Θ A {P₁} {P₂} {Q₁} {Q₂} simP simQ .WSimF.on-ev step with Θ-ev-elim P₁ Q₁ step
-- FIRE (the event is in `A`): the spec body weakly matches the SAME label, hence the same
-- `at`/`a`, hence the same `A .dec` branch — so the spec composite fires too and lands on
-- `Q₂`.  The body residual `rel` is DISCARDED; the obligation is exactly `simQ`.
... | Θthrow {at = at} {a = a} Pev m with simP .FSim.fwd .WSimF.on-ev Pev
...   | P₂′ , w , rel = Q₂ , Θ-wev-fire A Q₂ w m , simQ
-- PASS (the event is not in `A`): both sides stay under the throw; residual corecursive
f-sim-Θ A {P₁} {P₂} {Q₁} {Q₂} simP simQ .WSimF.on-ev step
    | Θpass {at = at} {a = a} Pev ¬m with simP .FSim.fwd .WSimF.on-ev Pev
...   | P₂′ , w , rel = (P₂′ ⟦ A ▷ Q₂) , Θ-wev-pass A Q₂ w ¬m , Θ-fsim A rel simQ
-- TERMINATION: the body's √ passes straight through the throw and lands in `deadlock`
f-sim-Θ A {P₁} {P₂} {Q₁} {Q₂} simP simQ .WSimF.on-ev step | Θdone {r = r} fpP
  with simP .FSim.fwd .WSimF.on-ev (sRet fpP)
...   | _ , w , _ = deadlock , Θ-wev-√ A Q₂ w , fsim-refl deadlock

Θ-fsim A {P₁} {P₂} {Q₁} {Q₂} simP simQ .FSim.fwd     = f-sim-Θ A simP simQ
Θ-fsim A {P₁} {P₂} {Q₁} {Q₂} simP simQ .FSim.stab st = Θ-fsim-stab A Q₁ Q₂ simP st
Θ-fsim A {P₁} {P₂} {Q₁} {Q₂} simP simQ .FSim.div→ d  = Θ-fsim-div→ A Q₁ Q₂ simP d

-- RETIRED: the shape-3 `FSim → ⊑FD` cash-out `Θ-mono-⊑FD` used to live here.  It was a
-- one-liner (`fsim→⊑FD (Θ-fsim A simP simQ)`) that could never consume a `⊑FD` fact, and
-- the canonical `-mono-⊑FD` name now belongs to the fact-shaped precongruence in
-- `CSP.Laws.FD.ThrowMonoFD`.  Please do not re-add it — write the one-liner at the call
-- site, or feed it to the fact-shaped law.
