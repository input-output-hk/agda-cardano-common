{-# OPTIONS --guardedness #-}

-- Divergence-respecting weak-bisimulation congruences of the CSP operators.
--
-- Contents (each section has its own banner):
--   1. HIDING     `cong-∖`                                       — unconditional
--   2. PARALLEL   `cong-Par⊤-L/-R`, `cong-Par⊤`, `cong-⦀`        — conditioned on `Sep`
--   3. INTERRUPT  `cong-△-L/-R`, `cong-△`                        — conditioned on `Sep△`
--   4. RENAMING   `cong-renameInv`, `cong-renameMap`             — unconditional
-- Sections 2 and 3 carry, in their banners, the counterexamples that make the
-- UNCONDITIONAL laws false and hence force the `Sep` / `Sep△` side conditions.
--
-- ===================================================================================
-- 1. HIDING.
--
--   cong-∖ : P ≈DR Q → (P ∖ A) ≈DR (Q ∖ A)
--
-- Hiding is a τ-introducing context: a step of `P ∖ A` comes from a step of P
-- (a non-A visible event passes through; an A-event becomes a τ-slide; a τ stays a
-- τ).  We invert via the hide single-step ELIM lemmas (`Hide-τ-elim` / `Hide-ev-elim`
-- in TraceLawsHide), match the underlying P-step through `P ≈DR Q`'s simulation to a
-- WEAK step of Q, then re-hide that weak step (`hide-rehide-weak`) to a weak step of
-- `Q ∖ A`; residuals are related by `cong-∖` corecursively.
--
-- Divergence: `Diverges (P ∖ A)` is an infinite τ-path of `P ∖ A`; every such τ is
-- either a τ of P or a hidden A-event of P, so it projects to an infinite path of P
-- mixing τ's and A-events.  That path keeps P from being weakly stable, which under
-- the DR-simulation forces Q to also have such an infinite path, hence
-- `Diverges (Q ∖ A)`.  This last part (divergence under hiding) is the subtle one.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
import Data.Unit as U0 using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Bisim.DRCongruence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS       {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim   {E = E} {I = ExtI E}
  using ( DRbisim; _≈DR_; Diverges; drbisim-sym; drbisim-refl; drbisim-trans
        ; dr-τ*-sim; dr-wev-sim)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using ( Hide-τ; Hide-keep; Hide-hidden; Hide-√
        ; Hide-τ-elim; Hide-ev-elim; HideτR; hτP; hτH; HideevR; heV; he√)
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using ( Mg; Par-τ-L; Par-τ-R; Par-sync
        ; fPar-er; fPar-re; fPar-nn )
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟
  using ( Par-soloL-reach; Par-soloR-reach
        ; brBoth-commitL; brBoth-commitR
        ; par-hVisL-eq; par-hVisR-eq
        ; par-pVis-soloL-eq; par-pVis-soloR-eq; par-pVis-both-eq )
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using ( ParτR; τL; τR; Par-τ-elim
        ; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim
        ; fPar-rr )
open EventSet
open import CSP.Laws.FD.ParallelDivergence E-≟
  using (Par-Diverges→; Par-Diverges-L; Par-Diverges-R)
-- section 3 (interrupt)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using ( force-△-Pret; force-△-LR; force-△-mt; ret-no-τ
        ; △τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim
        ; △evR; △evP; △evQ; △evPQ; △-ev-elim )
open import CSP.Laws.FD.InterruptFD E-≟
  using ( △-τ-lift-P; △-τ-lift-Q; △-Diverges-L; △-Diverges-R
        ; △-toQ-Qret; △-merge-noP )
open import CSP.Laws.FD.InterruptDivergence E-≟ using (△-Diverges→)
-- section 4 (renaming): the target alphabet is supplied by the inner module further
-- down, so these stay UN-APPLIED (aliases only, nothing brought into scope here)
import CSP.Rename                     as Rnm
import CSP.Laws.Traces.RenameDeadlock  as RDm
import Semantics.LTS                   as LTSm
import Semantics.WeakBisim             as WBm
import Semantics.DRBisim               as DRBm

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- re-hiding weak steps:  a weak step of P re-hides to a weak step of P ∖ A.
-- (A τ* run of P re-hides to a τ* run of P ∖ A — every τ of P is a τ of P ∖ A.)
-------------------------------------------------------------------------------------

Hide-τ* : (A : EventSet) (P : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
        → P ─[τ*]─► P′ → (P ∖ A) ─[τ*]─► (P′ ∖ A)
Hide-τ* A P τ*-refl            = τ*-refl
Hide-τ* A P (τ*-step Pτ rest)  = τ*-step (Hide-τ A P Pτ) (Hide-τ* A _ rest)

-- a weak τ̂ step re-hides
Hide-wτ : (A : EventSet) (P : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
        → P ═[ τ ]═► P′ → (P ∖ A) ═[ τ ]═► (P′ ∖ A)
Hide-wτ A P (wτ run) = wτ (Hide-τ* A P run)

-- a weak visible (non-√, non-A) step re-hides keeping the event visible
Hide-wev-keep : (A : EventSet) (P : PTree E (ExtI E) R)
                  {B : Set ℓ} {e : E B} {a : B} {P′ : PTree E (ExtI E) R}
              → ¬ A .EventSet.mem (B , e) a
              → P ═[ ev (evl (evLabel B e a)) ]═► P′
              → (P ∖ A) ═[ ev (evl (evLabel B e a)) ]═► (P′ ∖ A)
Hide-wev-keep A P ¬mem (wev p→p₁ p₁ev p₂→p′) =
  wev (Hide-τ* A P p→p₁) (Hide-keep A _ ¬mem p₁ev) (Hide-τ* A _ p₂→p′)

-- a weak visible A-event re-hides to a weak τ (the event is hidden ⇒ becomes a τ-slide,
-- which fuses with the surrounding τ* runs into one τ* run of P ∖ A).
Hide-wev-hidden : (A : EventSet) (P : PTree E (ExtI E) R)
                    {B : Set ℓ} {e : E B} {a : B} {P′ : PTree E (ExtI E) R}
                → A .EventSet.mem (B , e) a
                → P ═[ ev (evl (evLabel B e a)) ]═► P′
                → (P ∖ A) ═[ τ ]═► (P′ ∖ A)
Hide-wev-hidden A P mem (wev p→p₁ p₁ev p₂→p′) =
  wτ (τ*-trans (Hide-τ* A P p→p₁)
       (τ*-step (Hide-hidden A _ mem p₁ev) (Hide-τ* A _ p₂→p′)))

-- a √ step always lands in deadlock and comes from a `ret`
√-source : ∀ {p t : PTree E (ExtI E) R} {r : R}
         → p ─[ ev (√ r) ]─► t → PTree.force p ≡ ret r
√-source (sRet eq) = eq

-- a weak √ step re-hides (√ propagates through hiding; the trailing τ* is discarded
-- because the visible √ already lands in `deadlock`).
Hide-wev-√ : (A : EventSet) (P : PTree E (ExtI E) R) {r : R} {P′ : PTree E (ExtI E) R}
           → P ═[ ev (√ r) ]═► P′
           → (P ∖ A) ═[ ev (√ r) ]═► deadlock
Hide-wev-√ A P (wev p→p₁ p₁ev p₂→q) =
  wev (Hide-τ* A P p→p₁) (Hide-√ A _ (√-source p₁ev)) τ*-refl

-------------------------------------------------------------------------------------
-- The simulation half (fwd + bwd) of the FULL ≈DR congruence: `dr-sim-∖` turns the
-- DR-simulation of P/Q into a DR-simulation of (P∖A)/(Q∖A), carrying the FULL DRbisim
-- residual `cong-∖ A P′≈Q′` corecursively (this is productive: each residual sits
-- under the `WSimF` constructor of the on-ev/on-tau Σ-result; the divergence transfer
-- lives in the separate, non-corecursive `div→`/`div←` fields below via `modA-transfer`).
-- A step of (P ∖ A) inverts (Hide-ev-elim / Hide-τ-elim) to:
--   • a non-A visible event of P  (stays visible)            — Hide-wev-keep
--   • √ from a ret of P                                      — Hide-wev-√
--   • a τ of P                                               — Hide-wτ
--   • a hidden A-event of P  (becomes a τ)                   — Hide-wev-hidden
-- each matched through `P ≈DR Q`'s simulation then re-hidden.
-------------------------------------------------------------------------------------

-- forward declaration of the FULL ≈DR congruence (needed for the DRbisim residuals
-- carried by the simulation below).  Its `div→`/`div←` fields are defined further
-- down, once Bridges 1 & 3 and the König-step `modA-transfer` are in scope; the
-- `fwd`/`bwd` (simulation) fields are defined here via `dr-sim-∖`.
cong-∖ : (A : EventSet) {P Q : PTree E (ExtI E) R}
       → DRbisim R P Q → DRbisim R (P ∖ A) (Q ∖ A)

-- the simulation half, now carrying FULL DRbisim residuals (`cong-∖ A P′≈Q′`).
dr-sim-∖ : (A : EventSet) {P Q : PTree E (ExtI E) R}
         → DRbisim R P Q → WSimF (DRbisim R) (P ∖ A) (Q ∖ A)
dr-sim-∖ A {P} {Q} pq .WSimF.on-ev step with Hide-ev-elim A P step
... | heV {B} {e} {a} P′ ¬mem Pev with pq .DRbisim.fwd .WSimF.on-ev Pev
...   | Q′ , Qweak , P′≈Q′ =
        (Q′ ∖ A) , Hide-wev-keep A Q ¬mem Qweak , cong-∖ A P′≈Q′
dr-sim-∖ A {P} {Q} pq .WSimF.on-ev step | he√ {r} fpP
  with pq .DRbisim.fwd .WSimF.on-ev (sRet fpP)
...   | Q′ , Qweak , _ = deadlock , Hide-wev-√ A Q Qweak , drbisim-refl deadlock
dr-sim-∖ A {P} {Q} pq .WSimF.on-tau step with Hide-τ-elim A P step
... | hτP P′ Pτ refl with pq .DRbisim.fwd .WSimF.on-tau Pτ
...   | Q′ , wτ Q→Q′ , P′≈Q′ =
        (Q′ ∖ A) , Hide-wτ A Q (wτ Q→Q′) , cong-∖ A P′≈Q′
dr-sim-∖ A {P} {Q} pq .WSimF.on-tau step | hτH {B} {e} {a} P′ mem Pev refl
  with pq .DRbisim.fwd .WSimF.on-ev Pev
...   | Q′ , Qweak , P′≈Q′ =
        (Q′ ∖ A) , Hide-wev-hidden A Q mem Qweak , cong-∖ A P′≈Q′

-------------------------------------------------------------------------------------
-- Divergence under hiding.
--
-- `Diverges (P ∖ A)` is NOT `Diverges P`: each τ of `P ∖ A` is either a τ of P or a
-- HIDDEN A-event of P, so it projects to an infinite P-path mixing τ's and A-events
-- (`DivModA A P` below).  Transferring such a path through `P ≈DR Q` to a
-- `Diverges (Q ∖ A)` is the genuinely subtle half: an A-event of P is matched by a
-- WEAK visible A-step of Q (τ*·a·τ*), which re-hides to a nonempty τ*-run of `Q ∖ A`;
-- a τ of P is matched by a WEAK τ of Q, which may be EMPTY.  An infinite P-path with
-- only finitely many A-events therefore eventually becomes a pure τ-tail of P, whose
-- image in Q can be empty — so producing a Q-step each round requires knowing the
-- P-path has either an A-event or a *productive* τ ahead.  See note at the bottom.
-------------------------------------------------------------------------------------

-- an "A-modulo" step of t: a τ, or a hidden A-event
data ModAStep {ℓr} {R : Set ℓr} (A : EventSet)
              (t : PTree E (ExtI E) R) (t′ : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  maτ : t ─[ τ ]─► t′ → ModAStep A t t′
  maE : {B : Set ℓ} {e : E B} {a : B} → A .EventSet.mem (B , e) a
      → t ─[ ev (evl (evLabel B e a)) ]─► t′ → ModAStep A t t′

-- an infinite A-modulo path
record DivModA {ℓr} {R : Set ℓr} (A : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    {maNext} : PTree E (ExtI E) R
    maStep   : ModAStep A t maNext
    maRest   : DivModA A maNext
open DivModA

-- single-step inversion packaged as a Σ so the copattern definition of `div∖→modA`
-- can use pure PROJECTIONS (no `with`, no `subst` on the corecursive argument) — the
-- `sbisim-div→` idiom that the guardedness checker accepts.
hide-τ-step-Σ : ∀ {ℓr} {R : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R)
                  {M : PTree E (ExtI E) R}
              → (P ∖ A) ─[ τ ]─► M
              → Σ[ P′ ∈ PTree E (ExtI E) R ] (ModAStep A P P′ × (P′ ∖ A ≡ M))
hide-τ-step-Σ A P step with Hide-τ-elim A P step
... | hτP P′ Pτ teq          = P′ , maτ Pτ , sym teq
... | hτH {B} {e} {a} P′ mem Pev teq = P′ , maE mem Pev , sym teq

-- Bridge 1: divergence of `P ∖ A` projects to an A-modulo divergence of P.
div∖→modA : ∀ {ℓr} {R : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R)
          → Diverges (P ∖ A) → DivModA A P
div∖→modA A P d .maNext = proj₁ (hide-τ-step-Σ A P (d .Diverges.step))
div∖→modA A P d .maStep = proj₁ (proj₂ (hide-τ-step-Σ A P (d .Diverges.step)))
div∖→modA A P d .maRest =
  div∖→modA A _
    (subst Diverges (sym (proj₂ (proj₂ (hide-τ-step-Σ A P (d .Diverges.step)))))
           (d .Diverges.rest))

-- a ModAStep, re-hidden, is a single τ-step of (t ∖ A) to (t′ ∖ A)
modA-hide-τ : (A : EventSet) {t t′ : PTree E (ExtI E) R}
            → ModAStep A t t′ → (t ∖ A) ─[ τ ]─► (t′ ∖ A)
modA-hide-τ A {t} (maτ Pτ)        = Hide-τ A t Pτ
modA-hide-τ A {t} (maE mem Pev)   = Hide-hidden A t mem Pev

-- Bridge 3: an A-modulo divergence of t re-hides to a genuine divergence of (t ∖ A),
-- because EVERY A-modulo step (τ OR hidden A-event) is a τ of (t ∖ A).
modA→div∖ : (A : EventSet) (t : PTree E (ExtI E) R) → DivModA A t → Diverges (t ∖ A)
modA→div∖ A t dm .Diverges.next = dm .maNext ∖ A
modA→div∖ A t dm .Diverges.step = modA-hide-τ A (dm .maStep)
modA→div∖ A t dm .Diverges.rest = modA→div∖ A _ (dm .maRest)

-------------------------------------------------------------------------------------
-- Bridge 2 — the divergence transfer for the FULL ≈DR hiding congruence.
--
-- To upgrade `cong-∖-w` (Wbisim) to a full `cong-∖ : P ≈DR Q → (P∖A) ≈DR (Q∖A)` we
-- need `div→ : Diverges (P∖A) → Diverges (Q∖A)`.  Via Bridge 1 (`div∖→modA`) and
-- Bridge 3 (`modA→div∖`) (both proven, postulate-free above) this reduces EXACTLY to
-- the transfer
--
--     modA-transfer : DivModA A P → P ≈DR Q → DivModA A Q
--
-- which is a genuine CLASSICAL KÖNIG STEP: divergence-modulo-A transfers across ≈DR.
-- It is GENUINELY NON-CONSTRUCTIVE here:
--   • An A-event step of P is matched by a WEAK visible A-step of Q (τ*·a·τ*) whose
--     middle `a` is a real step ⇒ that round produces ≥1 Q-step (productive).
--   • A τ-step of P is matched by a WEAK τ of Q (`wτ : Q ─[τ*]─► Q′`) that may be
--     EMPTY (`τ*-refl`, zero steps) ⇒ that round may emit NO Q-step.
-- An infinite P-path with only finitely many A-events eventually becomes a pure-τ
-- tail of P whose Q-image can stall, so producing a Q-step each round requires
-- DECIDING "is there an A-event or a productive τ ahead" — a Σ⁰₂ / König-type
-- statement.  It is exactly the class the repo isolates in CSP.Laws.ClassicalFromLEM
-- (derivable from one `dne`); cf. the FD layer's `Par-Diverges→` / `loop-Diverges→`.
--
-- We therefore take `modA-transfer` as the SINGLE König-step postulate of this module
-- (matching the repo's postulate-in-laws + certify-from-dne pattern).  It is derivable
-- from one `dne`, certified standalone in CSP.Laws.ClassicalFromLEM (see
-- `modA-transfer-cert` there); nothing else in this module is postulated.
-------------------------------------------------------------------------------------

postulate
  -- classical König step — divergence-modulo-A transfers across ≈DR; derivable from
  -- one `dne`, certified in CSP.Laws.ClassicalFromLEM; cf. the FD layer's Par-Diverges→.
  modA-transfer : (A : EventSet) {P Q : PTree E (ExtI E) R}
                → DivModA A P → DRbisim R P Q → DivModA A Q

-------------------------------------------------------------------------------------
-- The FULL divergence-respecting hiding congruence.
--   fwd / bwd  : the weak simulation, reused verbatim from `cong-∖-w`.
--   div→ / div← : Diverges (P∖A) ↔ Diverges (Q∖A), via Bridge 1 (`div∖→modA`),
--                 the König step (`modA-transfer`), and Bridge 3 (`modA→div∖`).
-------------------------------------------------------------------------------------

cong-∖ A {P} {Q} pq .DRbisim.fwd  = dr-sim-∖ A pq
cong-∖ A {P} {Q} pq .DRbisim.bwd  = dr-sim-∖ A (drbisim-sym pq)
cong-∖ A {P} {Q} pq .DRbisim.div→ d =
  modA→div∖ A Q (modA-transfer A (div∖→modA A P d) pq)
cong-∖ A {P} {Q} pq .DRbisim.div← d =
  modA→div∖ A P (modA-transfer A (div∖→modA A Q d) (drbisim-sym pq))

-------------------------------------------------------------------------------------
-- 2. PARALLEL CONGRUENCE for divergence-respecting weak bisimulation.
--
--   cong-Par⊤-L : P ≈DR P′ → Par⊤ A P Q ≈DR Par⊤ A P′ Q
--   cong-Par⊤-R, cong-Par⊤, cong-⦀  derived from it.
--
-- This section first builds the reusable, postulate-free PLUMBING:
--   • τ*-lifting   : an operand τ* run lifts to a Par τ* run (Par-τ*-L / Par-τ*-R);
--   • weak-τ lift  : a weak τ̂ of an operand lifts to a weak τ̂ of the composite;
--   • divergence transfer (cong-Par⊤-div→ / div←) via the certified Par-Diverges→
--     (König) + the constructive Par-Diverges-L / -R.
-- The DIVERGENCE half of the congruence is therefore complete and postulate-free.
--
-- The SIMULATION half (fwd/bwd) is documented below as a genuine BLOCKER intrinsic
-- to the both-offer overlap encoding of `Par` under WEAK bisimulation: see the note
-- preceding the (intentionally absent) `cong-Par⊤-L` definition.
-------------------------------------------------------------------------------------

-- the ⊤-merge used by Par⊤ / ⦀
⊤merge : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
⊤merge _ _ = tt

-------------------------------------------------------------------------------------
-- τ*-lifting: an operand's τ* run lifts to a Par τ* run (map Par-τ-L / Par-τ-R).
-- These are the parallel analogues of Hide-τ* above and are fully constructive.
-------------------------------------------------------------------------------------

Par-τ*-L : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr})) {P′ : PTree E (ExtI E) (⊤ {ℓr})}
         → P ─[τ*]─► P′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P′ ∥⇘ A ⇙ Q)
Par-τ*-L A P Q τ*-refl           = τ*-refl
Par-τ*-L A P Q (τ*-step Pτ rest) =
  τ*-step (Par-τ-L A ⊤merge P Q Pτ) (Par-τ*-L A _ Q rest)

Par-τ*-R : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr})) {Q′ : PTree E (ExtI E) (⊤ {ℓr})}
         → Q ─[τ*]─► Q′ → (P ∥⇘ A ⇙ Q) ─[τ*]─► (P ∥⇘ A ⇙ Q′)
Par-τ*-R A P Q τ*-refl           = τ*-refl
Par-τ*-R A P Q (τ*-step Qτ rest) =
  τ*-step (Par-τ-R A ⊤merge P Q Qτ) (Par-τ*-R A P _ rest)

-- a weak τ̂ of one operand lifts to a weak τ̂ of the composite (left/right).
Par-wτ-L : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr})) {P′ : PTree E (ExtI E) (⊤ {ℓr})}
         → P ═[ τ ]═► P′ → (P ∥⇘ A ⇙ Q) ═[ τ ]═► (P′ ∥⇘ A ⇙ Q)
Par-wτ-L A P Q (wτ run) = wτ (Par-τ*-L A P Q run)

Par-wτ-R : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr})) {Q′ : PTree E (ExtI E) (⊤ {ℓr})}
         → Q ═[ τ ]═► Q′ → (P ∥⇘ A ⇙ Q) ═[ τ ]═► (P ∥⇘ A ⇙ Q′)
Par-wτ-R A P Q (wτ run) = wτ (Par-τ*-R A P Q run)

-------------------------------------------------------------------------------------
-- Divergence transfer for the parallel congruence (FULLY PROVEN, postulate-free).
--
-- `Diverges (Par⊤ A P Q)` decomposes (via the certified König step `Par-Diverges→`)
-- into `Diverges P ⊎ Diverges Q`; the P-summand transfers across `P ≈DR P′` (its
-- `div→` field) and re-lifts via `Par-Diverges-L`; the Q-summand is unchanged on the
-- left operand and re-lifts via `Par-Diverges-R`.  div← is symmetric (drbisim-sym).
-- This is exactly the `cong-∖` divergence pattern, but with Par's König step.
-------------------------------------------------------------------------------------

cong-Par⊤-div→ : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})}
               → DRbisim (⊤ {ℓr}) P P′
               → Diverges (P ∥⇘ A ⇙ Q) → Diverges (P′ ∥⇘ A ⇙ Q)
cong-Par⊤-div→ A {P} {P′} {Q} pp′ d with Par-Diverges→ A ⊤merge d
... | inj₁ dP = Par-Diverges-L A ⊤merge Q (pp′ .DRbisim.div→ dP)
... | inj₂ dQ = Par-Diverges-R A ⊤merge P′ dQ

cong-Par⊤-div← : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})}
               → DRbisim (⊤ {ℓr}) P P′
               → Diverges (P′ ∥⇘ A ⇙ Q) → Diverges (P ∥⇘ A ⇙ Q)
cong-Par⊤-div← A {P} {P′} {Q} pp′ d with Par-Diverges→ A ⊤merge d
... | inj₁ dP′ = Par-Diverges-L A ⊤merge Q (pp′ .DRbisim.div← dP′)
... | inj₂ dQ  = Par-Diverges-R A ⊤merge P dQ

-- RIGHT-operand divergence transfer (mirror, transferring the Q-summand across Q ≈DR Q′).
cong-Par⊤-div→-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
                 → DRbisim (⊤ {ℓr}) Q Q′
                 → Diverges (P ∥⇘ A ⇙ Q) → Diverges (P ∥⇘ A ⇙ Q′)
cong-Par⊤-div→-R A {P} {Q} {Q′} qq′ d with Par-Diverges→ A ⊤merge d
... | inj₁ dP = Par-Diverges-L A ⊤merge Q′ dP
... | inj₂ dQ = Par-Diverges-R A ⊤merge P (qq′ .DRbisim.div→ dQ)

cong-Par⊤-div←-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
                 → DRbisim (⊤ {ℓr}) Q Q′
                 → Diverges (P ∥⇘ A ⇙ Q′) → Diverges (P ∥⇘ A ⇙ Q)
cong-Par⊤-div←-R A {P} {Q} {Q′} qq′ d with Par-Diverges→ A ⊤merge d
... | inj₁ dP  = Par-Diverges-L A ⊤merge Q dP
... | inj₂ dQ′ = Par-Diverges-R A ⊤merge P (qq′ .DRbisim.div← dQ′)

-------------------------------------------------------------------------------------
-- SEPARATION INVARIANT and the RESTRICTED simulation half.
--
-- The blocker on the fwd/bwd simulation half was exactly the `evBoth` case of
-- `Par-ev-elim` — both operands offer the same non-sync visible event, producing the
-- inline ⊓-overlap node, which has no single ≈DR-matching right state under WEAK
-- bisimulation.  We CLEAR the blocker WITHOUT up-to-expansion by restricting the
-- congruence to operand pairs that NEVER both-offer a non-sync event, and stay so
-- under stepping.  This is the `Sep` invariant below.  The `EvBothProbe` spike
-- confirms the Cardano `Network`'s parallel/interleaving nodes satisfy it (disjoint
-- non-sync offered alphabets), so a `Sep`-restricted `cong-Par⊤`/`cong-⦀` suffices.
--
--   Sep .now    : refutes the both-offer of a non-sync event at the CURRENT heads —
--                 its hypotheses are EXACTLY the payload of `evBoth`, so `evBoth` is
--                 discharged by `⊥-elim (sep .now ¬cs Pstep Qstep)`.
--   Sep .stepL  : Sep is preserved when P does ANY step  (closure under P stepping).
--   Sep .stepR  : Sep is preserved when Q does ANY step  (closure under Q stepping).
-- The closure fields make `Sep` available for the residual operands of every
-- non-evBoth case, threaded corecursively through `cong-Par⊤-L`.
-------------------------------------------------------------------------------------

record Sep (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
     : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  coinductive
  field
    now   : ∀ {X} {e : E X} {a : X} {P′ Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → ¬ A .mem (X , e) a
          → P ─[ ev (evl (evLabel X e a)) ]─► P′
          → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
          → ⊥
    stepL : ∀ {l} {P′ : PTree E (ExtI E) (⊤ {ℓr})}
          → P ─[ l ]─► P′ → Sep A P′ Q
    stepR : ∀ {l} {Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → Q ─[ l ]─► Q′ → Sep A P Q′
open Sep

-- `Sep` preservation along a τ* run of the LEFT / RIGHT operand.
sep-τ*-L : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})}
         → P ─[τ*]─► P′ → Sep A P Q → Sep A P′ Q
sep-τ*-L A τ*-refl          s = s
sep-τ*-L A (τ*-step Pτ rs)  s = sep-τ*-L A rs (s .stepL Pτ)

sep-τ*-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
         → Q ─[τ*]─► Q′ → Sep A P Q → Sep A P Q′
sep-τ*-R A τ*-refl          s = s
sep-τ*-R A (τ*-step Qτ rs)  s = sep-τ*-R A rs (s .stepR Qτ)

-- `Sep` preservation along a WEAK visible run of the LEFT / RIGHT operand.
sep-wev-L : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})} {l : Event√ (⊤ {ℓr})}
          → P ═[ ev l ]═► P′ → Sep A P Q → Sep A P′ Q
sep-wev-L A (wev p→p₁ p₁ev p₂→p′) s =
  sep-τ*-L A p₂→p′ ((sep-τ*-L A p→p₁ s) .stepL p₁ev)

sep-wev-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})} {l : Event√ (⊤ {ℓr})}
          → Q ═[ ev l ]═► Q′ → Sep A P Q → Sep A P Q′
sep-wev-R A (wev q→q₁ q₁ev q₂→q′) s =
  sep-τ*-R A q₂→q′ ((sep-τ*-R A q→q₁ s) .stepR q₁ev)

-------------------------------------------------------------------------------------
-- WEAK-STEP LIFTING for the simulation: a weak step of one operand lifts to a weak
-- step of the composite.  τ* and weak-τ̂ are already done (Par-τ*-L/R, Par-wτ-L/R).
-- For a weak VISIBLE solo event we additionally need a SINGLE solo-step lemma that
-- returns the composite step + the (possibly overlap-commit) τ* tail.  We reuse the
-- `Par-soloL-reach`/`Par-soloR-reach` machinery but expose the single-step shape.
-------------------------------------------------------------------------------------

-- a single non-sync solo step of P lifts to: a composite visible step then a τ* run
-- (the τ* is empty unless the step went via the both-offer overlap node, in which case
-- it is the single commit-L τ).
Par-soloL-step : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
                   {X : Set ℓ} {e : E X} {a : X} {P₁ : PTree E (ExtI E) (⊤ {ℓr})}
               → ¬ A .mem (X , e) a
               → P ─[ ev (evl (evLabel X e a)) ]─► P₁
               → Σ[ M ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
                   (((P ∥⇘ A ⇙ Q) ─[ ev (evl (evLabel X e a)) ]─► M)
                    × (M ─[τ*]─► (P₁ ∥⇘ A ⇙ Q)))
Par-soloL-step A P Q {X} {e} {a} {P₁} ¬cs (sVis {v = vP} {τc = τcP} eqP veqP)
  with PTree.force Q in eqQ
... | ret r₂ = (P₁ ∥⇘ A ⇙ Q)
             , sVis (fPar-er A ⊤merge eqP eqQ)
                    (par-hVisL-eq A ⊤merge {vP = vP} Q {at = X , e} {a = a} ¬cs veqP)
             , τ*-refl
... | sil Q' = (P₁ ∥⇘ A ⇙ Q)
             , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                    (par-pVis-soloL-eq A ⊤merge (react vP τcP) (sil Q') P Q
                                       {at = X , e} {a = a} ¬cs veqP refl)
             , τ*-refl
... | react vQ τcQ with vQ (X , e) a in vqeq
...   | nothing = (P₁ ∥⇘ A ⇙ Q)
                , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                       (par-pVis-soloL-eq A ⊤merge (react vP τcP) (react vQ τcQ) P Q
                                          {at = X , e} {a = a} ¬cs veqP vqeq)
                , τ*-refl
...   | just Q₁ = ptree (react (λ _ _ → nothing) (par-brBoth A ⊤merge P Q P₁ Q₁))
                , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                       (par-pVis-both-eq A ⊤merge (react vP τcP) (react vQ τcQ) P Q
                                         {at = X , e} {a = a} ¬cs veqP vqeq)
                , τ*-step (brBoth-commitL A ⊤merge P Q P₁ Q₁) τ*-refl

Par-soloR-step : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
                   {X : Set ℓ} {e : E X} {a : X} {Q₁ : PTree E (ExtI E) (⊤ {ℓr})}
               → ¬ A .mem (X , e) a
               → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
               → Σ[ M ∈ PTree E (ExtI E) (⊤ {ℓr}) ]
                   (((P ∥⇘ A ⇙ Q) ─[ ev (evl (evLabel X e a)) ]─► M)
                    × (M ─[τ*]─► (P ∥⇘ A ⇙ Q₁)))
Par-soloR-step A P Q {X} {e} {a} {Q₁} ¬cs (sVis {v = vQ} {τc = τcQ} eqQ veqQ)
  with PTree.force P in eqP
... | ret r₁ = (P ∥⇘ A ⇙ Q₁)
             , sVis (fPar-re A ⊤merge eqP eqQ)
                    (par-hVisR-eq A ⊤merge P {vQ = vQ} {at = X , e} {a = a} ¬cs veqQ)
             , τ*-refl
... | sil P' = (P ∥⇘ A ⇙ Q₁)
             , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                    (par-pVis-soloR-eq A ⊤merge (sil P') (react vQ τcQ) P Q
                                       {at = X , e} {a = a} ¬cs refl veqQ)
             , τ*-refl
... | react vP τcP with vP (X , e) a in vpeq
...   | nothing = (P ∥⇘ A ⇙ Q₁)
                , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                       (par-pVis-soloR-eq A ⊤merge (react vP τcP) (react vQ τcQ) P Q
                                          {at = X , e} {a = a} ¬cs vpeq veqQ)
                , τ*-refl
...   | just P₁ = ptree (react (λ _ _ → nothing) (par-brBoth A ⊤merge P Q P₁ Q₁))
                , sVis (fPar-nn A ⊤merge eqP eqQ U0.tt U0.tt)
                       (par-pVis-both-eq A ⊤merge (react vP τcP) (react vQ τcQ) P Q
                                         {at = X , e} {a = a} ¬cs vpeq veqQ)
                , τ*-step (brBoth-commitR A ⊤merge P Q P₁ Q₁) τ*-refl

-- a weak visible solo (non-sync) event of P lifts to a weak visible step of the composite.
Par-wsoloL : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
               {X : Set ℓ} {e : E X} {a : X} {P′ : PTree E (ExtI E) (⊤ {ℓr})}
           → ¬ A .mem (X , e) a
           → P ═[ ev (evl (evLabel X e a)) ]═► P′
           → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P′ ∥⇘ A ⇙ Q)
Par-wsoloL A P Q ¬cs (wev p→pₛ pₛev pₘ→p′)
  with Par-soloL-step A _ Q ¬cs pₛev
... | M , Pstep , M→Par =
      wev (Par-τ*-L A P Q p→pₛ) Pstep (τ*-trans M→Par (Par-τ*-L A _ Q pₘ→p′))

Par-wsoloR : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
               {X : Set ℓ} {e : E X} {a : X} {Q′ : PTree E (ExtI E) (⊤ {ℓr})}
           → ¬ A .mem (X , e) a
           → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
           → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P ∥⇘ A ⇙ Q′)
Par-wsoloR A P Q ¬cs (wev q→qₛ qₛev qₘ→q′)
  with Par-soloR-step A P _ ¬cs qₛev
... | M , Qstep , M→Par =
      wev (Par-τ*-R A P Q q→qₛ) Qstep (τ*-trans M→Par (Par-τ*-R A P _ qₘ→q′))

-- a weak SYNC event of P (matched event of P, the SAME event fires in Q which steps to
-- a fixed Q₂) lifts: P′ ═e═► P₃ fused with Q's single sync step.
-- LEFT variant: P is the side weakly matched, Q makes a single sync step to Q₂.
Par-wsync : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
              {X : Set ℓ} {e : E X} {a : X}
              {P′ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
          → A .mem (X , e) a
          → P ═[ ev (evl (evLabel X e a)) ]═► P′
          → Q ─[ ev (evl (evLabel X e a)) ]─► Q₂
          → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P′ ∥⇘ A ⇙ Q₂)
Par-wsync A P Q {Q₂ = Q₂} cs (wev p→pₛ pₛev pₘ→p′) Qev =
  wev (Par-τ*-L A P Q p→pₛ)
      (Par-sync A ⊤merge _ Q cs pₛev Qev)
      (Par-τ*-L A _ Q₂ pₘ→p′)

-- RIGHT variant: P makes a single sync step to P₂, Q is the side weakly matched.
Par-wsync-R : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
                {X : Set ℓ} {e : E X} {a : X}
                {P₂ Q′ : PTree E (ExtI E) (⊤ {ℓr})}
            → A .mem (X , e) a
            → P ─[ ev (evl (evLabel X e a)) ]─► P₂
            → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
            → (P ∥⇘ A ⇙ Q) ═[ ev (evl (evLabel X e a)) ]═► (P₂ ∥⇘ A ⇙ Q′)
Par-wsync-R A P Q {P₂ = P₂} cs Pev (wev q→qₛ qₛev qₘ→q′) =
  wev (Par-τ*-R A P Q q→qₛ)
      (Par-sync A ⊤merge P _ cs Pev qₛev)
      (Par-τ*-R A P₂ _ qₘ→q′)

-- joint √: P weakly reaches a ret; Q already at ret ⇒ composite weak √ to deadlock.
-- (reuses the general `√-source` defined above for the hide section)
Par-w√-L : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
             {r₂ : ⊤ {ℓr}} {P′ : PTree E (ExtI E) (⊤ {ℓr})}
         → PTree.force Q ≡ ret r₂
         → P ═[ ev (√ tt) ]═► P′
         → (P ∥⇘ A ⇙ Q) ═[ ev (√ tt) ]═► deadlock
Par-w√-L A P Q {r₂} eqQ (wev p→pₛ pₛev _) =
  wev (Par-τ*-L A P Q p→pₛ)
      (sRet (fPar-rr A ⊤merge (√-source pₛev) eqQ))
      τ*-refl

Par-w√-R : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
             {r₁ : ⊤ {ℓr}} {Q′ : PTree E (ExtI E) (⊤ {ℓr})}
         → PTree.force P ≡ ret r₁
         → Q ═[ ev (√ tt) ]═► Q′
         → (P ∥⇘ A ⇙ Q) ═[ ev (√ tt) ]═► deadlock
Par-w√-R A P Q {r₁} eqP (wev q→qₛ qₛev _) =
  wev (Par-τ*-R A P Q q→qₛ)
      (sRet (fPar-rr A ⊤merge eqP (√-source qₛev)))
      τ*-refl

-------------------------------------------------------------------------------------
-- THE RESTRICTED LEFT CONGRUENCE.
--
--   cong-Par⊤-L : Sep A P Q → Sep A P′ Q → P ≈DR P′ → Par⊤ A P Q ≈DR Par⊤ A P′ Q
--
-- fwd/bwd: invert a step of `Par⊤ A P Q` by Par-τ-elim / Par-ev-elim and match it
-- through P ≈DR P′; the `evBoth` case is impossible (⊥-elim of the `Sep .now` field).
-- Every residual is related by cong-Par⊤-L corecursively, THREADING the preserved
-- `Sep` (via the closure fields and the sep-τ*/sep-wev lifts).  div→/div← reuse the
-- already-proven cong-Par⊤-div→/cong-Par⊤-div←.
-------------------------------------------------------------------------------------

cong-Par⊤-L : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})}
            → Sep A P Q → Sep A P′ Q → P ≈DR P′
            → (P ∥⇘ A ⇙ Q) ≈DR (P′ ∥⇘ A ⇙ Q)

dr-sim-Par⊤-L : (A : EventSet) {P P′ Q : PTree E (ExtI E) (⊤ {ℓr})}
              → Sep A P Q → Sep A P′ Q → P ≈DR P′
              → WSimF (DRbisim (⊤ {ℓr})) (P ∥⇘ A ⇙ Q) (P′ ∥⇘ A ⇙ Q)

-- on-ev: invert the visible step
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-ev step
  with Par-ev-elim A ⊤merge P Q step
-- sync: P fires e∈A; matched weakly by P′; Q makes its single sync step.
... | evSync {X} {e} {a} {P₂} {Q₂} cs Pev Qev
      with pp′ .DRbisim.fwd .WSimF.on-ev Pev
...     | P₃ , P′weak , P₂≈P₃ =
          (P₃ ∥⇘ A ⇙ Q₂)
        , Par-wsync A P′ Q cs P′weak Qev
        , cong-Par⊤-L A ((sPQ .stepL Pev) .stepR Qev)
                        ((sep-wev-L A P′weak sP′Q) .stepR Qev)
                        P₂≈P₃
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-ev step | evL {X} {e} {a} {P₂} ¬cs Pev
      with pp′ .DRbisim.fwd .WSimF.on-ev Pev
...     | P₃ , P′weak , P₂≈P₃ =
          (P₃ ∥⇘ A ⇙ Q)
        , Par-wsoloL A P′ Q ¬cs P′weak
        , cong-Par⊤-L A (sPQ .stepL Pev) (sep-wev-L A P′weak sP′Q) P₂≈P₃
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-ev step | evR {X} {e} {a} {Q₂} ¬cs Qev =
          (P′ ∥⇘ A ⇙ Q₂)
        , Par-wsoloR A P′ Q ¬cs (wev τ*-refl Qev τ*-refl)
        , cong-Par⊤-L A (sPQ .stepR Qev) (sP′Q .stepR Qev) pp′
-- evBoth: impossible — both operands offered a non-sync event (Sep .now).
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-ev step | evBoth ¬cs Pev Qev =
          ⊥-elim (sPQ .now ¬cs Pev Qev)
-- √: both at ret ⇒ deadlock; matched by P′ weakly reaching its ret while Q stays at ret.
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-ev step | ev√ {r₁} fpP fpQ
      with pp′ .DRbisim.fwd .WSimF.on-ev (sRet fpP)
...     | P₃ , P′weak , _ =
          deadlock , Par-w√-L A P′ Q fpQ P′weak , drbisim-refl deadlock

-- on-tau: invert the τ-step
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-tau step
  with Par-τ-elim A ⊤merge P Q step
... | τL P₂ Pτ refl
      with pp′ .DRbisim.fwd .WSimF.on-tau Pτ
...     | P₃ , wτ P′→P₃ , P₂≈P₃ =
          (P₃ ∥⇘ A ⇙ Q)
        , Par-wτ-L A P′ Q (wτ P′→P₃)
        , cong-Par⊤-L A (sPQ .stepL Pτ) (sep-τ*-L A P′→P₃ sP′Q) P₂≈P₃
dr-sim-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .WSimF.on-tau step | τR Q₂ Qτ refl =
          (P′ ∥⇘ A ⇙ Q₂)
        , Par-wτ-R A P′ Q (wτ (τ*-step Qτ τ*-refl))
        , cong-Par⊤-L A (sPQ .stepR Qτ) (sP′Q .stepR Qτ) pp′

cong-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .DRbisim.fwd =
  dr-sim-Par⊤-L A sPQ sP′Q pp′
cong-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .DRbisim.bwd =
  dr-sim-Par⊤-L A sP′Q sPQ (drbisim-sym pp′)
cong-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .DRbisim.div→ d = cong-Par⊤-div→ A pp′ d
cong-Par⊤-L A {P} {P′} {Q} sPQ sP′Q pp′ .DRbisim.div← d = cong-Par⊤-div← A pp′ d

-------------------------------------------------------------------------------------
-- THE RESTRICTED RIGHT CONGRUENCE — symmetric construction (Q on the right side).
-------------------------------------------------------------------------------------

cong-Par⊤-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
            → Sep A P Q → Sep A P Q′ → Q ≈DR Q′
            → (P ∥⇘ A ⇙ Q) ≈DR (P ∥⇘ A ⇙ Q′)

dr-sim-Par⊤-R : (A : EventSet) {P Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
              → Sep A P Q → Sep A P Q′ → Q ≈DR Q′
              → WSimF (DRbisim (⊤ {ℓr})) (P ∥⇘ A ⇙ Q) (P ∥⇘ A ⇙ Q′)

dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-ev step
  with Par-ev-elim A ⊤merge P Q step
... | evSync {X} {e} {a} {P₂} {Q₂} cs Pev Qev
      with qq′ .DRbisim.fwd .WSimF.on-ev Qev
...     | Q₃ , Q′weak , Q₂≈Q₃ =
          (P₂ ∥⇘ A ⇙ Q₃)
        , Par-wsync-R A P Q′ cs Pev Q′weak
        , cong-Par⊤-R A ((sPQ .stepR Qev) .stepL Pev)
                        ((sep-wev-R A Q′weak sPQ′) .stepL Pev)
                        Q₂≈Q₃
dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | evL {X} {e} {a} {P₂} ¬cs Pev =
          (P₂ ∥⇘ A ⇙ Q′)
        , Par-wsoloL A P Q′ ¬cs (wev τ*-refl Pev τ*-refl)
        , cong-Par⊤-R A (sPQ .stepL Pev) (sPQ′ .stepL Pev) qq′
dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | evR {X} {e} {a} {Q₂} ¬cs Qev
      with qq′ .DRbisim.fwd .WSimF.on-ev Qev
...     | Q₃ , Q′weak , Q₂≈Q₃ =
          (P ∥⇘ A ⇙ Q₃)
        , Par-wsoloR A P Q′ ¬cs Q′weak
        , cong-Par⊤-R A (sPQ .stepR Qev) (sep-wev-R A Q′weak sPQ′) Q₂≈Q₃
dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | evBoth ¬cs Pev Qev =
          ⊥-elim (sPQ .now ¬cs Pev Qev)
dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | ev√ {r₁} {r₂} fpP fpQ
      with qq′ .DRbisim.fwd .WSimF.on-ev (sRet fpQ)
...     | Q₃ , Q′weak , _ =
          deadlock , Par-w√-R A P Q′ fpP Q′weak , drbisim-refl deadlock

dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-tau step
  with Par-τ-elim A ⊤merge P Q step
... | τL P₂ Pτ refl =
          (P₂ ∥⇘ A ⇙ Q′)
        , Par-wτ-L A P Q′ (wτ (τ*-step Pτ τ*-refl))
        , cong-Par⊤-R A (sPQ .stepL Pτ) (sPQ′ .stepL Pτ) qq′
dr-sim-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .WSimF.on-tau step | τR Q₂ Qτ refl
      with qq′ .DRbisim.fwd .WSimF.on-tau Qτ
...     | Q₃ , wτ Q′→Q₃ , Q₂≈Q₃ =
          (P ∥⇘ A ⇙ Q₃)
        , Par-wτ-R A P Q′ (wτ Q′→Q₃)
        , cong-Par⊤-R A (sPQ .stepR Qτ) (sep-τ*-R A Q′→Q₃ sPQ′) Q₂≈Q₃

cong-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .DRbisim.fwd =
  dr-sim-Par⊤-R A sPQ sPQ′ qq′
cong-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .DRbisim.bwd =
  dr-sim-Par⊤-R A sPQ′ sPQ (drbisim-sym qq′)
cong-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .DRbisim.div→ d = cong-Par⊤-div→-R A qq′ d
cong-Par⊤-R A {P} {Q} {Q′} sPQ sPQ′ qq′ .DRbisim.div← d = cong-Par⊤-div←-R A qq′ d

-------------------------------------------------------------------------------------
-- The two-operand restricted congruence and the `⦀` instance (A = ∅ES, where every
-- event is non-sync, so `Sep ∅ES P Q` = "P,Q never share ANY offered event").
-------------------------------------------------------------------------------------

cong-Par⊤ : (A : EventSet) {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → Sep A P Q → Sep A P′ Q → Sep A P′ Q′
          → P ≈DR P′ → Q ≈DR Q′
          → (P ∥⇘ A ⇙ Q) ≈DR (P′ ∥⇘ A ⇙ Q′)
cong-Par⊤ A {P} {P′} {Q} {Q′} sPQ sP′Q sP′Q′ pp′ qq′ =
  drbisim-trans (cong-Par⊤-L A sPQ sP′Q pp′)
                (cong-Par⊤-R A sP′Q sP′Q′ qq′)

cong-⦀ : {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
       → Sep ∅ES P Q → Sep ∅ES P′ Q → Sep ∅ES P′ Q′
       → P ≈DR P′ → Q ≈DR Q′
       → (P ⦀ Q) ≈DR (P′ ⦀ Q′)
cong-⦀ {P} {P′} {Q} {Q′} sPQ sP′Q sP′Q′ pp′ qq′ =
  cong-Par⊤ ∅ES sPQ sP′Q sP′Q′ pp′ qq′

-------------------------------------------------------------------------------------
-- HOW THE RESTRICTION CLEARS THE OLD `evBoth` BLOCKER (no up-to-expansion).
--
-- For the UNRESTRICTED weak-bisim parallel congruence, the only case that did not
-- close was the BOTH-OFFER OVERLAP:
--
--   • evBoth (¬cs : e∉A, P─e→P₂, Q─e→Q₂):  the LEFT residual is the inline overlap node
--         Lo = ptree (react ∅ (par-brBoth A ⊤merge P Q P₂ Q₂))
--            ≅ (Par⊤ A P₂ Q) ⊓ (Par⊤ A P Q₂)
--     which under WEAK bisim has no single right state matching it (the commit-R branch
--     needs `P ≈DR P′ₛ` for an INTERMEDIATE stable τ-descendant, which ≈DR does not give).
--
-- The `Sep` invariant restricts the congruence to operand pairs whose non-sync offered
-- alphabets are DISJOINT (and stay so under stepping), so the `evBoth` case can never
-- arise: its very payload (P and Q both firing the SAME non-sync event) is refuted by
-- `Sep .now`, and the case is closed by `⊥-elim (sPQ .now ¬cs Pev Qev)`.  Every other
-- case (evSync / evL / evR / ev√ / τL / τR) closes with the constructive weak-step lifts
-- above (Par-wsync / Par-wsolo{L,R} / Par-w√ / Par-wτ-{L,R}), threading the preserved
-- `Sep` to the residual operands via `Sep`'s closure fields and the sep-τ*/sep-wev lifts.
-- `cong-Par⊤` is the two-operand composite (drbisim-trans of -L then -R), and `cong-⦀`
-- the `A = ∅ES` instance (where EVERY event is non-sync, so `Sep ∅ES P Q` = "P,Q share
-- no offered event" — satisfied by the Network's disjoint-alphabet `⦀` components).
--
-- The divergence half (cong-Par⊤-div→/← and the -R variants) is fully proven via the
-- certified König step Par-Diverges→ + the constructive Par-Diverges-L/-R, and is reused
-- verbatim for the `div→`/`div←` fields.  No new postulate, no NON_TERMINATING, no hole.
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- 3. INTERRUPT CONGRUENCE for divergence-respecting weak bisimulation.
--
--   cong-△-L : Sep△ P Q → Sep△ P′ Q → P ≈DR P′ → (P △ Q) ≈DR (P′ △ Q)
--   cong-△-R : Sep△ P Q → Sep△ P Q′ → Q ≈DR Q′ → (P △ Q) ≈DR (P △ Q′)
--   cong-△   : the two-sided composite (drbisim-trans of -L then -R).
--
-- ===================================================================================
-- WHY THE LAW IS CONDITIONAL: the UNCONDITIONAL congruence is FALSE, on TWO independent
-- counts.  We therefore ship the CONDITIONED law, guarded by the `Sep△` invariant below,
-- whose two substantive fields (`liveL`, `now△`) are each forced by one of the two
-- witnesses recorded here.
--
-- ⚠ (A) WHY `P ≈DR P′ → (P △ Q) ≈DR (P′ △ Q)` IS FALSE — the `ret`-collapse clause.
-- `_△_`'s FIRST clause is  `force P ≡ ret r  ⇒  force (P △ Q) ≡ react ∅v (br2 P Q)`,
-- i.e. `P △ Q` COLLAPSES to the internal choice `P ⊓ Q` as soon as P can terminate.
-- Collapsing DISCARDS Q's ability to keep running beside P, so the τ that takes a
-- `sil`-headed P to a `ret`-headed P *resolves a choice* — exactly the classical reason
-- weak bisimulation fails to be a congruence for CCS `+`.  Concretely, with two distinct
-- events `b , c` (all offers on `⊤`):
--     P  = sil Skip            P′ = Skip            Q = (b ⟶₀ Stop) ⊓ (c ⟶₀ Stop)
-- • `P ≈DR P′` : P's only step is `─τ→ Skip`, matched by the EMPTY weak τ; P′'s only
--   step is its `√`, matched by `P ─τ→ Skip ─√→ deadlock`; neither diverges.
-- • `P △ Q` (both operands live ⇒ third clause) offers NOTHING visible and has exactly
--   three τ's:  `Skip △ Q`,  `P △ (b ⟶₀ Stop)`,  `P △ (c ⟶₀ Stop)`.
-- • `P′ △ Q` = `Skip ⊓ Q` (first clause) has exactly two τ's: `Skip` and `Q`.
-- Take the LHS step `P △ Q ─τ→ T` with `T = sil Skip △ (b ⟶₀ Stop)`.  `T` offers `b`
-- (the interrupt firing) and τ's to `Skip ⊓ (b ⟶₀ Stop)`; so `T` has the traces ⟨b⟩ and
-- ⟨√⟩ but NOT ⟨c⟩.  The τ*-closure of `P′ △ Q` is exactly
--     { Skip ⊓ Q , Skip , Q , b ⟶₀ Stop , c ⟶₀ Stop }
-- and every member is refuted at the TRACE level (≈DR ⇒ ≈FD ⇒ equal traces):
--     Skip ⊓ Q   has ⟨c⟩, T has not        Skip        has no ⟨b⟩
--     Q          has no ⟨√⟩                b ⟶₀ Stop   has no ⟨√⟩
--     c ⟶₀ Stop  has no ⟨b⟩
-- So no weak τ-match exists and `(P △ Q) ≉DR (P′ △ Q)`.  NOTE: here P and Q never
-- both-offer ANY event (P's τ-closure {sil Skip, Skip} offers no `evl` event at all), so
-- a `Sep`-style disjointness condition ALONE does NOT rescue the law.  This is what the
-- `liveL` field (the left operand has not terminated) is for: it puts the `ret`-collapse
-- clause out of reach, which is exactly what discharges `△-τ-elim`'s `△τ⊓P` / `△τ⊓Q`
-- arms and what licenses `△-τ-lift-Q` on the right-hand side.
--
-- ⚠ (B) WHY IT IS ALSO FALSE FOR THE BOTH-OFFER OVERLAP — the `△-merge` ⊓-node.
-- When P and Q offer the SAME event, `△-merge` produces the inline overlap node
--     Ov(P₁) = ptree (react ∅v (△-br2 P₁ Q Q₁))   ≅   (P₁ △ Q) ⊓ Q₁
-- which FREEZES the state reached immediately after the shared event: its only τ's are
-- the two commits, so a trailing τ-run of the matching side cannot be absorbed.  This is
-- structurally the same blocker as `Par`'s `evBoth` (see the blocker note closing
-- section 2 just above).  It is not merely a proof obstruction — it is false.  With
-- `Pₘ = Stop ⊓ (b ⟶₀ Stop)`:
--     Pᵃ = (a ⟶₀ Stop) ▷ (a ⟶₀ Pₘ)      Pᵇ = a ⟶₀ Pₘ      Q = a ⟶₀ (c ⟶₀ Stop)
-- • `Pᵃ ≈DR Pᵇ` : `Pᵃ ─a→ Stop` is matched by `Pᵇ ─a→ Pₘ ─τ→ Stop`; `Pᵃ ─τ→ Pᵇ` by the
--   empty weak τ; `Pᵇ ─a→ Pₘ` by `Pᵃ ─τ→ Pᵇ ─a→ Pₘ`; neither diverges.
-- • `Pᵃ △ Q ─a→ Ov(Stop)` (both offer `a`).  `Pᵇ △ Q` is STABLE, so its only weak
--   `a`-runs start `Pᵇ △ Q ─a→ Ov(Pₘ)`, and the τ*-closure of `Ov(Pₘ)` is exactly
--     { Ov(Pₘ) , Pₘ △ Q , Q₁ , Stop △ Q , (b ⟶₀ Stop) △ Q }   (Q₁ = c ⟶₀ Stop)
--   Each is again refuted at the TRACE level against `Ov(Stop)` (whose τ's are
--   `Stop △ Q` and `Q₁`, giving traces ⟨a⟩,⟨c⟩ but never ⟨b⟩):
--     Ov(Pₘ) , Pₘ △ Q , (b ⟶₀ Stop) △ Q  all have ⟨b⟩, Ov(Stop) has not
--     Q₁ has no ⟨a⟩                       Stop △ Q has no ⟨c⟩
-- So `(Pᵃ △ Q) ≉DR (Pᵇ △ Q)` although `Pᵃ ≈DR Pᵇ`.  Note both operands are `ret`-free
-- here, so `liveL` alone does not rescue it either — hence the `now△` field.
-- (Both witnesses were verified by hand, not machine-checked; each refutation is purely
-- trace-level, so it needs only `≈DR ⇒ ≈FD` and the finite τ*-closures listed above.)
-- ===================================================================================
--
-- THE CONDITIONED LAW.  `Sep△ P Q` (coinductive, closed under stepping) says
--   liveL  : the LEFT operand has not terminated (`NonRet (force P)`)  — kills (A);
--   now△   : P and Q never both-offer the same visible event           — kills (B).
-- Under it the three laws above are proved exactly along the `cong-∖` / `cong-Par⊤-L`
-- template: fwd/bwd invert a composite step with `△-τ-elim` / `△-ev-elim`, match the
-- operand step through the DR-simulation, and re-lift with the interrupt step lifts
-- (`△-τ-lift-P`, `△-τ-lift-Q`, `△-toQ-Qret` from `CSP.Laws.FD.InterruptFD`, plus the two
-- visible-step lifts built here).  `△evPQ` is discharged by `⊥-elim (… .now△ …)` and
-- `△τ⊓P`/`△τ⊓Q` by `⊥-elim (subst NonRet … (… .liveL))`.  div→/div← reuse the
-- ALREADY-CERTIFIED König step `△-Diverges→` (CSP.Laws.FD.InterruptDivergence, certified
-- from one `dne` in CSP.Laws.ClassicalFromLEM) together with the constructive
-- `△-Diverges-L` / `△-Diverges-R`.  NO NEW POSTULATE, no hole, no NON_TERMINATING.
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- τ-lifting through the interrupt: an operand's τ* run lifts to a composite τ* run.
-- LEFT is unconditional (`△-τ-lift-P`); RIGHT needs the left operand live, since a
-- `ret`-headed P collapses `P △ Q` to `P ⊓ Q` (whose τ's commit instead of sliding).
-------------------------------------------------------------------------------------

-- P's τ* run lifts:  P ─τ*→ P′  ⇒  (P △ Q) ─τ*→ (P′ △ Q)
△-τ*-L : (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
       → P ─[τ*]─► P′ → (P △ Q) ─[τ*]─► (P′ △ Q)
△-τ*-L P Q τ*-refl           = τ*-refl
△-τ*-L P Q (τ*-step Pτ rest) = τ*-step (△-τ-lift-P Pτ) (△-τ*-L _ Q rest)

-- Q's τ* run lifts, P live and FIXED throughout:  Q ─τ*→ Q′ ⇒ (P △ Q) ─τ*→ (P △ Q′)
△-τ*-R : (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P) → {Q′ : PTree E (ExtI E) R}
       → Q ─[τ*]─► Q′ → (P △ Q) ─[τ*]─► (P △ Q′)
△-τ*-R P Q ntP τ*-refl           = τ*-refl
△-τ*-R P Q ntP (τ*-step Qτ rest) = τ*-step (△-τ-lift-Q ntP Qτ) (△-τ*-R P _ ntP rest)

-- a weak τ̂ step of the LEFT operand lifts
△-wτ-L : (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
       → P ═[ τ ]═► P′ → (P △ Q) ═[ τ ]═► (P′ △ Q)
△-wτ-L P Q (wτ run) = wτ (△-τ*-L P Q run)

-- a weak τ̂ step of the RIGHT operand lifts (P live)
△-wτ-R : (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
       → {Q′ : PTree E (ExtI E) R}
       → Q ═[ τ ]═► Q′ → (P △ Q) ═[ τ ]═► (P △ Q′)
△-wτ-R P Q ntP (wτ run) = wτ (△-τ*-R P Q ntP run)

-------------------------------------------------------------------------------------
-- Two offer equations for `△-merge` (mirroring `△-merge-noP` / `△-merge-bothP` in
-- InterruptFD, which cover the Q-only and both-offer cells): the P-ONLY cell, and the
-- Q-terminated cell.  Both match `△-merge`'s own `with viewV nP at a | viewV nQ at a`.
-------------------------------------------------------------------------------------

-- P offers, Q does not ⇒ the interrupt keeps running as (P′ △ Q)
△-merge-onlyP : {Q P′ : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                {nP nQ : NodeKind E (ExtI E) R}
              → viewV nP at a ≡ just P′ → viewV nQ at a ≡ nothing
              → △-merge nP nQ Q at a ≡ just (P′ △ Q)
△-merge-onlyP {at = at} {a = a} {nP = nP} {nQ = nQ} vp vq
  with viewV nP at a | viewV nQ at a
... | just _  | nothing = case vp of λ { refl → refl }
... | just _  | just _  = case vq of λ ()
... | nothing | _       = case vp of λ ()

-- Q has terminated ⇒ every P-offer passes through wrapped as (P′ △ Q)
△-merge-Qret-eq : {Q P′ : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                  {nP : NodeKind E (ExtI E) R}
                → viewV nP at a ≡ just P′
                → △-merge-Qret nP Q at a ≡ just (P′ △ Q)
△-merge-Qret-eq {at = at} {a = a} {nP = nP} vp with viewV nP at a
... | just _  = case vp of λ { refl → refl }
... | nothing = case vp of λ ()

-------------------------------------------------------------------------------------
-- The two VISIBLE single-step lifts.  Each needs the OTHER operand not to offer the
-- same event — otherwise `△-merge` routes the step into the overlap ⊓-node (case (B)).
-------------------------------------------------------------------------------------

-- P's visible step lifts, keeping the interrupt armed:  (P △ Q) ─e→ (P₁ △ Q)
△-ev-lift-P : (P Q : PTree E (ExtI E) R) {X : Set ℓ} {e : E X} {a : X}
                {P₁ : PTree E (ExtI E) R}
            → P ─[ ev (evl (evLabel X e a)) ]─► P₁
            → (∀ {Q₁ : PTree E (ExtI E) R} → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁ → ⊥)
            → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► (P₁ △ Q)
△-ev-lift-P P Q {X} {e} {a} (sVis {v = vP} {τc = τcP} eqP br) ¬Qoff
  with PTree.force Q in eqQ
... | ret r′ = sVis (force-△-LR {P = P} {Q = Q} eqP eqQ U0.tt)
                    (△-merge-Qret-eq {Q = Q} {at = X , e} {a = a} {nP = react vP τcP} br)
... | sil Q′ = sVis (force-△-mt {P = P} {Q = Q} eqP eqQ U0.tt U0.tt)
                    (△-merge-onlyP {Q = Q} {at = X , e} {a = a}
                                   {nP = react vP τcP} {nQ = sil Q′} br refl)
... | react vQ τcQ with vQ (X , e) a in vqeq
...   | just Q₁  = ⊥-elim (¬Qoff (sVis eqQ vqeq))
...   | nothing  = sVis (force-△-mt {P = P} {Q = Q} eqP eqQ U0.tt U0.tt)
                        (△-merge-onlyP {Q = Q} {at = X , e} {a = a}
                                       {nP = react vP τcP} {nQ = react vQ τcQ} br vqeq)

-- Q's visible step FIRES the interrupt: the composite commits to the handler Q₁.
△-ev-lift-Q : (P Q : PTree E (ExtI E) R) {X : Set ℓ} {e : E X} {a : X}
                {Q₁ : PTree E (ExtI E) R}
            → NonRet (PTree.force P)
            → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
            → (∀ {P₁ : PTree E (ExtI E) R} → P ─[ ev (evl (evLabel X e a)) ]─► P₁ → ⊥)
            → (P △ Q) ─[ ev (evl (evLabel X e a)) ]─► Q₁
△-ev-lift-Q P Q {X} {e} {a} ntP (sVis {v = vQ} {τc = τcQ} eqQ brQ) ¬Poff
  with PTree.force P in eqP
-- (`with PTree.force P in eqP` has already rewritten `ntP` to `NonRet (ret r)` = ⊥)
... | ret r    = ⊥-elim ntP
... | sil P′   = sVis (force-△-mt {P = P} {Q = Q} eqP eqQ U0.tt U0.tt)
                      (△-merge-noP {Q = Q} {at = X , e} {a = a}
                                   {vQ = vQ} {τcQ = τcQ} {nP = sil P′} refl brQ)
... | react vP τcP with vP (X , e) a in vpeq
...   | just P₁ = ⊥-elim (¬Poff (sVis eqP vpeq))
...   | nothing = sVis (force-△-mt {P = P} {Q = Q} eqP eqQ U0.tt U0.tt)
                       (△-merge-noP {Q = Q} {at = X , e} {a = a}
                                    {vQ = vQ} {τcQ = τcQ} {nP = react vP τcP} vpeq brQ)

-------------------------------------------------------------------------------------
-- A `ret`-headed process forces its ≈DR partner to τ-reach a `ret`-headed state that is
-- STILL ≈DR-related to it.  Used for the `△τQret` arm of the RIGHT congruence, where
-- the LHS commits to the terminated handler and the RHS must τ-walk to its own `ret`.
-------------------------------------------------------------------------------------

-- a `ret`-headed tree has no τ, so any τ* run out of it is empty
ret-τ*-refl : {P P″ : PTree E (ExtI E) R} {r : R}
            → PTree.force P ≡ ret r → P ─[τ*]─► P″ → P″ ≡ P
ret-τ*-refl eqP τ*-refl        = refl
ret-τ*-refl eqP (τ*-step Pτ _) = ⊥-elim (ret-no-τ eqP Pτ)

-- the ret-partner extraction itself
△-ret-partner : {P P′ : PTree E (ExtI E) R} {r : R}
              → PTree.force P ≡ ret r → P ≈DR P′
              → Σ[ Pₛ ∈ PTree E (ExtI E) R ]
                  ((P′ ─[τ*]─► Pₛ)
                   × (Σ[ r′ ∈ R ] PTree.force Pₛ ≡ ret r′)
                   × (P ≈DR Pₛ))
△-ret-partner {P = P} {P′ = P′} {r = r} eqP pp′
  with pp′ .DRbisim.fwd .WSimF.on-ev (sRet eqP)
-- `ev (√ r)` admits only the `sRet` constructor, so the partner's `ret` is read off it
... | _ , wev p′→pₛ (sRet eqPₛ) _ , _
      with dr-τ*-sim p′→pₛ (drbisim-sym pp′)
...     | P″ , P→P″ , pₛ≈p″ =
          _ , p′→pₛ , (r , eqPₛ)
            , drbisim-sym (subst (DRbisim _ _) (ret-τ*-refl eqP P→P″) pₛ≈p″)

-------------------------------------------------------------------------------------
-- THE `Sep△` INVARIANT.  Coinductive, closed under stepping of either operand.
--   liveL : the LEFT operand has not terminated — puts the `ret`-collapse clause
--           (counterexample (A)) out of reach, and licenses `△-τ-lift-Q`.
--   now△  : the two operands never both-offer the same visible event — its hypotheses
--           are EXACTLY the payload of `△evPQ`, so the overlap case (counterexample
--           (B)) is discharged by `⊥-elim (sep .now△ Pev Qev)`.
--   stepL△/stepR△ : closure, making `Sep△` available for the residual operands.
-------------------------------------------------------------------------------------

record Sep△ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    liveL  : NonRet (PTree.force P)
    now△   : ∀ {X : Set ℓ} {e : E X} {a : X} {P′ Q′ : PTree E (ExtI E) R}
           → P ─[ ev (evl (evLabel X e a)) ]─► P′
           → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
           → ⊥
    stepL△ : ∀ {l} {P′ : PTree E (ExtI E) R} → P ─[ l ]─► P′ → Sep△ P′ Q
    stepR△ : ∀ {l} {Q′ : PTree E (ExtI E) R} → Q ─[ l ]─► Q′ → Sep△ P Q′
open Sep△

-- `Sep△` preservation along a τ* run of the LEFT / RIGHT operand
sep△-τ*-L : {P P′ Q : PTree E (ExtI E) R} → P ─[τ*]─► P′ → Sep△ P Q → Sep△ P′ Q
sep△-τ*-L τ*-refl         s = s
sep△-τ*-L (τ*-step Pτ rs) s = sep△-τ*-L rs (s .stepL△ Pτ)

sep△-τ*-R : {P Q Q′ : PTree E (ExtI E) R} → Q ─[τ*]─► Q′ → Sep△ P Q → Sep△ P Q′
sep△-τ*-R τ*-refl         s = s
sep△-τ*-R (τ*-step Qτ rs) s = sep△-τ*-R rs (s .stepR△ Qτ)

-- `Sep△` preservation along a WEAK visible run of the LEFT / RIGHT operand
sep△-wev-L : {P P′ Q : PTree E (ExtI E) R} {l : Event√ R}
           → P ═[ ev l ]═► P′ → Sep△ P Q → Sep△ P′ Q
sep△-wev-L (wev p→p₁ p₁ev p₂→p′) s =
  sep△-τ*-L p₂→p′ ((sep△-τ*-L p→p₁ s) .stepL△ p₁ev)

sep△-wev-R : {P Q Q′ : PTree E (ExtI E) R} {l : Event√ R}
           → Q ═[ ev l ]═► Q′ → Sep△ P Q → Sep△ P Q′
sep△-wev-R (wev q→q₁ q₁ev q₂→q′) s =
  sep△-τ*-R q₂→q′ ((sep△-τ*-R q→q₁ s) .stepR△ q₁ev)

-------------------------------------------------------------------------------------
-- WEAK visible lifts, built from the single-step lifts + the τ*-lifts.  For the LEFT
-- operand the interrupt stays armed, so the whole weak run re-lifts; for the RIGHT
-- operand the middle step COMMITS to the handler, so the trailing τ* run of Q is
-- already a τ* run of the (now bare) composite.
-------------------------------------------------------------------------------------

-- a weak visible step of P lifts to a weak visible step of P △ Q
△-wsoloL : (P Q : PTree E (ExtI E) R) {X : Set ℓ} {e : E X} {a : X}
             {P′ : PTree E (ExtI E) R}
         → Sep△ P Q
         → P ═[ ev (evl (evLabel X e a)) ]═► P′
         → (P △ Q) ═[ ev (evl (evLabel X e a)) ]═► (P′ △ Q)
△-wsoloL P Q sep (wev p→pₛ pₛev pₘ→p′) =
  wev (△-τ*-L P Q p→pₛ)
      (△-ev-lift-P _ Q pₛev (λ Qev → (sep△-τ*-L p→pₛ sep) .now△ pₛev Qev))
      (△-τ*-L _ Q pₘ→p′)

-- a weak visible step of Q lifts to a weak visible step of P △ Q FIRING the interrupt
△-wsoloR : (P Q : PTree E (ExtI E) R) {X : Set ℓ} {e : E X} {a : X}
             {Q′ : PTree E (ExtI E) R}
         → Sep△ P Q
         → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
         → (P △ Q) ═[ ev (evl (evLabel X e a)) ]═► Q′
△-wsoloR P Q sep (wev q→qₛ qₛev qₘ→q′) =
  wev (△-τ*-R P Q (sep .liveL) q→qₛ)
      (△-ev-lift-Q P _ (sep .liveL) qₛev
                   (λ Pev → (sep△-τ*-R q→qₛ sep) .now△ Pev qₛev))
      qₘ→q′

-------------------------------------------------------------------------------------
-- DIVERGENCE TRANSFER (both operands).  `Diverges (P △ Q)` decomposes via the
-- ALREADY-CERTIFIED König step `△-Diverges→` into `Diverges P ⊎ Diverges Q`; the
-- relevant summand transfers across the ≈DR hypothesis and re-lifts via the
-- constructive `△-Diverges-L` / `△-Diverges-R`.  Exactly the `cong-Par⊤-div→` pattern.
-------------------------------------------------------------------------------------

-- LEFT-operand divergence transfer, forwards
cong-△-div→ : {P P′ Q : PTree E (ExtI E) R}
            → P ≈DR P′ → Diverges (P △ Q) → Diverges (P′ △ Q)
cong-△-div→ {Q = Q} pp′ d with △-Diverges→ d
... | inj₁ dP = △-Diverges-L {Q = Q} (pp′ .DRbisim.div→ dP)
... | inj₂ dQ = △-Diverges-R dQ

-- LEFT-operand divergence transfer, backwards
cong-△-div← : {P P′ Q : PTree E (ExtI E) R}
            → P ≈DR P′ → Diverges (P′ △ Q) → Diverges (P △ Q)
cong-△-div← {Q = Q} pp′ d with △-Diverges→ d
... | inj₁ dP′ = △-Diverges-L {Q = Q} (pp′ .DRbisim.div← dP′)
... | inj₂ dQ  = △-Diverges-R dQ

-- RIGHT-operand divergence transfer, forwards
cong-△-div→-R : {P Q Q′ : PTree E (ExtI E) R}
              → Q ≈DR Q′ → Diverges (P △ Q) → Diverges (P △ Q′)
cong-△-div→-R {Q′ = Q′} qq′ d with △-Diverges→ d
... | inj₁ dP = △-Diverges-L {Q = Q′} dP
... | inj₂ dQ = △-Diverges-R (qq′ .DRbisim.div→ dQ)

-- RIGHT-operand divergence transfer, backwards
cong-△-div←-R : {P Q Q′ : PTree E (ExtI E) R}
              → Q ≈DR Q′ → Diverges (P △ Q′) → Diverges (P △ Q)
cong-△-div←-R {Q = Q} qq′ d with △-Diverges→ d
... | inj₁ dP  = △-Diverges-L {Q = Q} dP
... | inj₂ dQ′ = △-Diverges-R (qq′ .DRbisim.div← dQ′)

-------------------------------------------------------------------------------------
-- THE LEFT INTERRUPT CONGRUENCE.  Invert a step of `P △ Q`, match the P-step through
-- P ≈DR P′, re-lift, and thread the preserved `Sep△` to the residual operands.
-------------------------------------------------------------------------------------

-- forward declaration of the LEFT congruence (needed for the residuals below)
cong-△-L : {P P′ Q : PTree E (ExtI E) R}
         → Sep△ P Q → Sep△ P′ Q → P ≈DR P′ → (P △ Q) ≈DR (P′ △ Q)

-- the simulation half, carrying FULL DRbisim residuals
dr-sim-△-L : {P P′ Q : PTree E (ExtI E) R}
           → Sep△ P Q → Sep△ P′ Q → P ≈DR P′
           → WSimF (DRbisim R) (P △ Q) (P′ △ Q)

-- on-ev: P's event keeps the interrupt armed; Q's event fires it; both-offer is refuted
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-ev step
  with △-ev-elim P Q step
... | △evP Pev with pp′ .DRbisim.fwd .WSimF.on-ev Pev
...   | P₃ , P′weak , P₁≈P₃ =
        (P₃ △ Q)
      , △-wsoloL P′ Q sP′Q P′weak
      , cong-△-L (sPQ .stepL△ Pev) (sep△-wev-L P′weak sP′Q) P₁≈P₃
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-ev step | △evQ Qev =
        _
      , wev τ*-refl
            (△-ev-lift-Q P′ Q (sP′Q .liveL) Qev (λ P′ev → sP′Q .now△ P′ev Qev))
            τ*-refl
      , drbisim-refl _
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-ev step | △evPQ Pev Qev =
        ⊥-elim (sPQ .now△ Pev Qev)

-- on-tau: P's τ slides; Q's τ slides (P′ live); Q's √-interrupt commits; the two
-- `ret`-collapse arms are impossible under `liveL`
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-tau step
  with △-τ-elim P Q step
... | △τP Pτ with pp′ .DRbisim.fwd .WSimF.on-tau Pτ
...   | P₃ , wτ P′→P₃ , P₂≈P₃ =
        (P₃ △ Q)
      , △-wτ-L P′ Q (wτ P′→P₃)
      , cong-△-L (sPQ .stepL△ Pτ) (sep△-τ*-L P′→P₃ sP′Q) P₂≈P₃
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-tau step | △τQ {Q′ = Q₂} Qτ =
        (P′ △ Q₂)
      , wτ (τ*-step (△-τ-lift-Q (sP′Q .liveL) Qτ) τ*-refl)
      , cong-△-L (sPQ .stepR△ Qτ) (sP′Q .stepR△ Qτ) pp′
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-tau step | △τQret eqQ =
        Q
      , wτ (τ*-step (△-toQ-Qret P′ Q eqQ) τ*-refl)
      , drbisim-refl Q
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-tau step | △τ⊓P eqP =
        ⊥-elim (subst NonRet eqP (sPQ .liveL))
dr-sim-△-L {P = P} {P′ = P′} {Q = Q} sPQ sP′Q pp′ .WSimF.on-tau step | △τ⊓Q eqP =
        ⊥-elim (subst NonRet eqP (sPQ .liveL))

cong-△-L sPQ sP′Q pp′ .DRbisim.fwd    = dr-sim-△-L sPQ sP′Q pp′
cong-△-L sPQ sP′Q pp′ .DRbisim.bwd    = dr-sim-△-L sP′Q sPQ (drbisim-sym pp′)
cong-△-L sPQ sP′Q pp′ .DRbisim.div→ d = cong-△-div→ pp′ d
cong-△-L sPQ sP′Q pp′ .DRbisim.div← d = cong-△-div← pp′ d

-------------------------------------------------------------------------------------
-- THE RIGHT INTERRUPT CONGRUENCE — the handler side.  The interesting arms are `△evQ`
-- (the interrupt fires, so the composite COLLAPSES to the handler and the residual is
-- the bare `Q₁ ≈DR Q₃` with no congruence wrapper) and `△τQret` (the LHS commits to the
-- terminated handler, matched by τ-walking Q′ to its own `ret` via `△-ret-partner`).
-------------------------------------------------------------------------------------

-- forward declaration of the RIGHT congruence (needed for the residuals below)
cong-△-R : {P Q Q′ : PTree E (ExtI E) R}
         → Sep△ P Q → Sep△ P Q′ → Q ≈DR Q′ → (P △ Q) ≈DR (P △ Q′)

-- the simulation half, carrying FULL DRbisim residuals
dr-sim-△-R : {P Q Q′ : PTree E (ExtI E) R}
           → Sep△ P Q → Sep△ P Q′ → Q ≈DR Q′
           → WSimF (DRbisim R) (P △ Q) (P △ Q′)

dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-ev step
  with △-ev-elim P Q step
... | △evP {P₁ = P₁} Pev =
        (P₁ △ Q′)
      , wev τ*-refl
            (△-ev-lift-P P Q′ Pev (λ Q′ev → sPQ′ .now△ Pev Q′ev))
            τ*-refl
      , cong-△-R (sPQ .stepL△ Pev) (sPQ′ .stepL△ Pev) qq′
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | △evQ Qev
      with qq′ .DRbisim.fwd .WSimF.on-ev Qev
...     | Q₃ , Q′weak , Q₁≈Q₃ = Q₃ , △-wsoloR P Q′ sPQ′ Q′weak , Q₁≈Q₃
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-ev step | △evPQ Pev Qev =
        ⊥-elim (sPQ .now△ Pev Qev)

dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-tau step
  with △-τ-elim P Q step
... | △τP {P′ = P₂} Pτ =
        (P₂ △ Q′)
      , wτ (τ*-step (△-τ-lift-P Pτ) τ*-refl)
      , cong-△-R (sPQ .stepL△ Pτ) (sPQ′ .stepL△ Pτ) qq′
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-tau step | △τQ Qτ
      with qq′ .DRbisim.fwd .WSimF.on-tau Qτ
...     | Q₃ , wτ Q′→Q₃ , Q₂≈Q₃ =
          (P △ Q₃)
        , △-wτ-R P Q′ (sPQ′ .liveL) (wτ Q′→Q₃)
        , cong-△-R (sPQ .stepR△ Qτ) (sep△-τ*-R Q′→Q₃ sPQ′) Q₂≈Q₃
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-tau step | △τQret eqQ
      with △-ret-partner eqQ qq′
...     | Q′ₛ , Q′→Q′ₛ , (_ , eqQ′ₛ) , Q≈Q′ₛ =
          Q′ₛ
        , wτ (τ*-trans (△-τ*-R P Q′ (sPQ′ .liveL) Q′→Q′ₛ)
                       (τ*-step (△-toQ-Qret P Q′ₛ eqQ′ₛ) τ*-refl))
        , Q≈Q′ₛ
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-tau step | △τ⊓P eqP =
        ⊥-elim (subst NonRet eqP (sPQ .liveL))
dr-sim-△-R {P = P} {Q = Q} {Q′ = Q′} sPQ sPQ′ qq′ .WSimF.on-tau step | △τ⊓Q eqP =
        ⊥-elim (subst NonRet eqP (sPQ .liveL))

cong-△-R sPQ sPQ′ qq′ .DRbisim.fwd    = dr-sim-△-R sPQ sPQ′ qq′
cong-△-R sPQ sPQ′ qq′ .DRbisim.bwd    = dr-sim-△-R sPQ′ sPQ (drbisim-sym qq′)
cong-△-R sPQ sPQ′ qq′ .DRbisim.div→ d = cong-△-div→-R qq′ d
cong-△-R sPQ sPQ′ qq′ .DRbisim.div← d = cong-△-div←-R qq′ d

-------------------------------------------------------------------------------------
-- The two-sided interrupt congruence (drbisim-trans of -L then -R, as `cong-Par⊤`).
-------------------------------------------------------------------------------------

cong-△ : {P P′ Q Q′ : PTree E (ExtI E) R}
       → Sep△ P Q → Sep△ P′ Q → Sep△ P′ Q′
       → P ≈DR P′ → Q ≈DR Q′
       → (P △ Q) ≈DR (P′ △ Q′)
cong-△ sPQ sP′Q sP′Q′ pp′ qq′ =
  drbisim-trans (cong-△-L sPQ sP′Q pp′) (cong-△-R sP′Q sP′Q′ qq′)

-------------------------------------------------------------------------------------
-- 4. RENAMING CONGRUENCE for divergence-respecting weak bisimulation.
--
--   cong-renameInv : P ≈DR Q → (P ⟦ inv ⟧ⁱ) ≈DR (Q ⟦ inv ⟧ⁱ)
--   cong-renameMap : P ≈DR Q →  renameMap P  ≈DR  renameMap Q
--
-- ===================================================================================
-- UNCONDITIONAL — no side condition, no injectivity requirement (contrast sections 2
-- and 3, where the unconditional law is outright false).
--
-- `renameInv P inv` (and hence `renameMap = renameInv · ι-vis-inv`) is the wrapper whose
-- per-target preimage list `invPreimg inv bt b` has length ≤ 1, so `rnFan` NEVER builds a
-- fan-in node: the operator is a step-for-step STRUCTURAL relabelling —
--   ret r        ↦ ret r
--   sil P′       ↦ sil (renamed P′)
--   react vP τcP ↦ react (b ↦ renamed (vP (inv b)))  (extBranch … τcP)
-- Every target step therefore has exactly one source step behind it (`ren-τ-inv` /
-- `ren-ev-inv`) and every source step pushes forward (`ren-τ-fwd` / `ren-ev-fwd` /
-- `ren-√-fwd`), all in `CSP.Laws.Traces.RenameDeadlock`'s cross-alphabet Part 1.  Note in
-- particular that `inv` need NOT be injective: it may send several target events to the
-- same source event (fan-OUT), which merely duplicates offers — each duplicate still has
-- a single continuation, so the step correspondence survives.  And it may be partial:
-- targets outside the image simply offer nothing.
--
-- Consequently the divergence halves need NO classical/König step either: the τ-spaces
-- correspond one-for-one, so `Diverges (P ⟦inv⟧ⁱ) ↔ Diverges P` is a CONSTRUCTIVE
-- corecursive projection (`ren-Diverges→` / `ren-Diverges←` below).  This is what makes
-- rename the cheap congruence and hiding/parallel/interrupt the expensive ones.
-- ZERO postulates are used or introduced by this section's own reasoning (the module's
-- one postulate, `modA-transfer`, belongs to section 1 and is not touched here).
--
-- ⚠ SCOPE.  This is the `renameInv` (functional / at-most-one-preimage) wrapper.  The
-- GENERAL relational operator `_⟦ R ¿ preimg ⟧` is NOT covered and is NOT a ≈DR
-- congruence: with ≥ 2 enabled preimages `rnFan` emits the fan-in node
-- `ptree (react ∅ (rnBranch … ts))`, an internal choice over the sources ENABLED AT THAT
-- HEAD.  That node freezes the post-event state exactly like `Par`'s `evBoth` overlap
-- (the blocker note closing section 2) and the interrupt's `△-merge` both-offer node
-- (counterexample (B) of section 3), so a matching side whose weak run has a nonempty
-- trailing τ has no state to be matched against.  A conditioned relational version would
-- need a `Sep`-style invariant pinning the enabled-preimage lists of the two sides
-- together; not attempted here.
-- ===================================================================================

-------------------------------------------------------------------------------------
-- The target alphabet `E₂` and the event injection inducing the rename, exactly as in
-- `CSP.Rename` / `CSP.Laws.Traces.RenameDeadlock`.  Everything below is parametric in
-- them; the SAME-alphabet instance is `E₂ = E`, `ι = id`, `ι⁻¹ = just`.
-------------------------------------------------------------------------------------

module _ {ℓe₂} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E A))
  (ι-linv : ∀ {A} (e : E A) → ι⁻¹ (ι e) ≡ just e)
  where

  -- the rename operator and its cross-alphabet single-step lemmas
  module Rn  = Rnm  {E₁ = E} {E₂ = E₂} ι ι⁻¹ ι-linv
  module RD  = RDm  {E₁ = E} {E₂ = E₂} ι ι⁻¹ ι-linv
  -- the TARGET-alphabet semantics (the source-alphabet ones are in scope unqualified)
  module L2  = LTSm  {E = E₂} {I = ExtI E₂}
  module W2  = WBm   {E = E₂} {I = ExtI E₂}
  module DR2 = DRBm  {E = E₂} {I = ExtI E₂}

  open Rn using (ConcEvent₁; renameInv; renameMap; ι-vis-inv)
  open RD using (_⟦_⟧ⁱ; ren-τ-fwd; ren-ev-fwd; ren-√-fwd; ren-τ-inv; ren-ev-inv)
  -- target-side names get a ₂ suffix so they never shadow the source-side ones
  open L2 using () renaming
    ( _─[_]─►_ to _─[_]─►₂_ ; Event√ to Event√₂ ; τ to τ₂ ; ev to ev₂
    ; evl to evl₂ ; √ to √₂ ; evLabel to evLabel₂ ; sRet to sRet₂ ; Diverges to Diverges₂ )
  open W2 using () renaming
    ( _─[τ*]─►_ to _─[τ*]─►₂_ ; τ*-refl to τ*-refl₂ ; τ*-step to τ*-step₂
    ; _═[_]═►_ to _═[_]═►₂_ ; wτ to wτ₂ ; wev to wev₂ ; WSimF to WSimF₂ )
  open DR2 using () renaming
    ( DRbisim to DRbisim₂ ; _≈DR_ to _≈DR₂_ ; drbisim-refl to drbisim-refl₂ )

  -- the per-target partial inverse that drives `renameInv`
  RenInv : Set (lsuc ℓ ⊔ ℓe ⊔ ℓe₂)
  RenInv = (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁

  -----------------------------------------------------------------------------------
  -- Re-renaming WEAK steps: a weak step of P renames to a weak step of P ⟦inv⟧ⁱ.
  -- (Each source τ is a target τ, so a τ* run renames to a τ* run of the same length.)
  -----------------------------------------------------------------------------------

  -- a source τ* run renames to a target τ* run
  ren-τ* : {inv : RenInv} (P : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
         → P ─[τ*]─► P′ → (P ⟦ inv ⟧ⁱ) ─[τ*]─►₂ (P′ ⟦ inv ⟧ⁱ)
  ren-τ* P τ*-refl           = τ*-refl₂
  ren-τ* P (τ*-step Pτ rest) = τ*-step₂ (ren-τ-fwd Pτ) (ren-τ* _ rest)

  -- a weak τ̂ step renames
  ren-wτ : {inv : RenInv} (P : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
         → P ═[ τ ]═► P′ → (P ⟦ inv ⟧ⁱ) ═[ τ₂ ]═►₂ (P′ ⟦ inv ⟧ⁱ)
  ren-wτ P (wτ run) = wτ₂ (ren-τ* P run)

  -- a weak visible step renames, RELABELLED at the target event that `inv` maps back
  ren-wev : {inv : RenInv} (P : PTree E (ExtI E) R)
              {at : AnyTypes E} {a : proj₁ at} {bt : AnyTypes E₂} {b : proj₁ bt}
              {P′ : PTree E (ExtI E) R}
          → inv bt b ≡ just (at , a)
          → P ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► P′
          → (P ⟦ inv ⟧ⁱ) ═[ ev₂ (evl₂ (evLabel₂ (proj₁ bt) (proj₂ bt) b)) ]═►₂ (P′ ⟦ inv ⟧ⁱ)
  ren-wev P eqinv (wev p→p₁ p₁ev p₂→p′) =
    wev₂ (ren-τ* P p→p₁) (ren-ev-fwd p₁ev eqinv) (ren-τ* _ p₂→p′)

  -- a weak √ step renames (√ passes through unchanged and lands in `deadlock`)
  ren-w√ : {inv : RenInv} (P : PTree E (ExtI E) R) {r : R} {P′ : PTree E (ExtI E) R}
         → P ═[ ev (√ r) ]═► P′
         → (P ⟦ inv ⟧ⁱ) ═[ ev₂ (√₂ r) ]═►₂ deadlock
  -- `ev (√ r)` admits only the `sRet` constructor, so the source `ret` is read off it
  -- (`√-source` from section 1 would do just as well; destructing inline keeps this
  --  section independent of the hide plumbing).
  ren-w√ P (wev p→p₁ (sRet eqP) _) =
    wev₂ (ren-τ* P p→p₁) (ren-√-fwd eqP) τ*-refl₂

  -----------------------------------------------------------------------------------
  -- DIVERGENCE, both ways, CONSTRUCTIVELY (no König step): the τ-spaces correspond
  -- one-for-one, so an infinite τ-run on either side projects to one on the other.
  -- `ren-Diverges→` uses the `div∖→modA` idiom — the single-step inversion is already
  -- packaged as a Σ (`ren-τ-inv`), so the copattern definition uses pure PROJECTIONS.
  -----------------------------------------------------------------------------------

  -- an infinite τ-run of the RENAMED tree reflects to one of the source
  ren-Diverges→ : {inv : RenInv} (P : PTree E (ExtI E) R)
                → Diverges₂ (P ⟦ inv ⟧ⁱ) → Diverges P
  ren-Diverges→ {inv = inv} P d .Diverges.next =
    proj₁ (ren-τ-inv {inv = inv} {P = P} (d .Diverges₂.step))
  ren-Diverges→ {inv = inv} P d .Diverges.step =
    proj₁ (proj₂ (ren-τ-inv {inv = inv} {P = P} (d .Diverges₂.step)))
  ren-Diverges→ {inv = inv} P d .Diverges.rest =
    ren-Diverges→ _
      (subst Diverges₂ (proj₂ (proj₂ (ren-τ-inv {inv = inv} {P = P} (d .Diverges₂.step))))
             (d .Diverges₂.rest))

  -- an infinite τ-run of the source renames to one of the renamed tree
  ren-Diverges← : {inv : RenInv} (P : PTree E (ExtI E) R)
                → Diverges P → Diverges₂ (P ⟦ inv ⟧ⁱ)
  ren-Diverges← {inv = inv} P d .Diverges₂.next = (d .Diverges.next) ⟦ inv ⟧ⁱ
  ren-Diverges← {inv = inv} P d .Diverges₂.step = ren-τ-fwd (d .Diverges.step)
  ren-Diverges← {inv = inv} P d .Diverges₂.rest = ren-Diverges← _ (d .Diverges.rest)

  -----------------------------------------------------------------------------------
  -- THE CONGRUENCE.  Built as `fwd`/`bwd` from a single `dr-sim-renameInv` helper plus
  -- the divergence transfer above — the `cong-∖` shape.  A step of `P ⟦inv⟧ⁱ` inverts
  -- (`ren-ev-inv` / `ren-τ-inv`) to a source step of P, is matched through `P ≈DR Q`,
  -- and the resulting WEAK Q-step is re-renamed (`ren-wev` / `ren-w√` / `ren-τ*`).
  -- Residuals are related by `cong-renameInv` corecursively (productive: each residual
  -- sits under the `WSimF` constructor of the on-ev / on-tau Σ-result).
  -----------------------------------------------------------------------------------

  -- forward declaration of the congruence (needed for the residuals below)
  cong-renameInv : {inv : RenInv} {P Q : PTree E (ExtI E) R}
                 → DRbisim R P Q → DRbisim₂ R (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)

  -- the simulation half, carrying FULL DRbisim residuals
  dr-sim-renameInv : {inv : RenInv} {P Q : PTree E (ExtI E) R}
                   → DRbisim R P Q → WSimF₂ (DRbisim₂ R) (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
  dr-sim-renameInv {inv = inv} {P = P} {Q = Q} pq .WSimF₂.on-ev step
    with ren-ev-inv {inv = inv} {P = P} step
  ... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl)
        with pq .DRbisim.fwd .WSimF.on-ev Pev
  ...     | Q′ , Qweak , P₁≈Q′ =
            (Q′ ⟦ inv ⟧ⁱ) , ren-wev Q eqinv Qweak , cong-renameInv P₁≈Q′
  dr-sim-renameInv {inv = inv} {P = P} {Q = Q} pq .WSimF₂.on-ev step
      | inj₂ (r , refl , eqP , refl)
        with pq .DRbisim.fwd .WSimF.on-ev (sRet eqP)
  ...     | _ , Qweak , _ = deadlock , ren-w√ Q Qweak , drbisim-refl₂ deadlock
  dr-sim-renameInv {inv = inv} {P = P} {Q = Q} pq .WSimF₂.on-tau step
    with ren-τ-inv {inv = inv} {P = P} step
  ... | P₁ , Pτ , refl with pq .DRbisim.fwd .WSimF.on-tau Pτ
  ...   | Q′ , wτ Q→Q′ , P₁≈Q′ =
          (Q′ ⟦ inv ⟧ⁱ) , wτ₂ (ren-τ* Q Q→Q′) , cong-renameInv P₁≈Q′

  cong-renameInv pq .DRbisim₂.fwd = dr-sim-renameInv pq
  cong-renameInv pq .DRbisim₂.bwd = dr-sim-renameInv (drbisim-sym pq)
  cong-renameInv {P = P} {Q = Q} pq .DRbisim₂.div→ d =
    ren-Diverges← Q (pq .DRbisim.div→ (ren-Diverges→ P d))
  cong-renameInv {P = P} {Q = Q} pq .DRbisim₂.div← d =
    ren-Diverges← P (pq .DRbisim.div← (ren-Diverges→ Q d))

  -- the headline instance: the injective ALPHABET renaming induced by ι
  cong-renameMap : {P Q : PTree E (ExtI E) R}
                 → DRbisim R P Q → DRbisim₂ R (renameMap P) (renameMap Q)
  cong-renameMap = cong-renameInv {inv = ι-vis-inv}
