{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for PARALLEL composition.
--
--   Par-fsim : Sep A P₁ Q₁ → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
--            → FSim R (Par A merge P₁ Q₁) (Par A merge P₂ Q₂)
--
-- with the CSP corollaries `∥-fsim` (alphabetised parallel `_∥⇘_⇙_`) and `⦀-fsim`
-- (interleaving).  ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the
-- IMPLEMENTATION and the SECOND the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`),
-- so `Par-fsim` says: if the spec operands failure-simulate the impl operands, the spec
-- composite failure-simulates the impl composite.  Composed with `fsim→⊑FD` this is a
-- COINDUCTIVE route to `(Par A merge P₂ Q₂) ⊑FD (Par A merge P₁ Q₁)` — the same
-- conclusion as the trace-level `Par-mono-⊑FD`, but reached by one-state-at-a-time
-- reasoning instead of by decomposing whole traces.
--
-- The three fields.
--
--   fwd  : the `bwd`-free half of `CSP.Laws.Bisim.DRCongruence`'s `dr-sim-Par⊤-L/R`.
--          A step of the IMPL composite is inverted with `Par-τ-elim` / `Par-ev-elim`
--          and matched by a WEAK step of the spec composite, re-lifted by the
--          `Par-wsync-both` / `Par-wsolo{L,R}` / `Par-w√-both` / `Par-τ*-{L,R}` lifts.
--          Because only the IMPL composite is ever inverted, the `evBoth` overlap
--          obstruction has to be excluded on the IMPL PAIR ONLY — one `Sep A P₁ Q₁`
--          hypothesis, HALF of what the ≈DR congruence needs (which, being two-way,
--          needs `Sep` on both operand pairs).  See the SIDE CONDITION note below.
--
--   stab : the real work, and it needs NO side condition at all.  A stable
--          `Par A merge P₁ Q₁` is classified by the reused, constructive
--          `Par-stable-normal` (from `CSP.Laws.FD.ParallelMonoFD`) into
--          stable|stable, ret|stable or stable|ret — never ret|ret, never a `sil`.
--          Each operand is then settled on the spec side:
--            • a STABLE operand by that operand's own `FSim.stab`;
--            • a TERMINATED (`ret r`) operand by its `FSim.fwd`, whose match of the
--              impl's `√ r` step exhibits a τ*-run of the spec operand to a state
--              forcing to `ret r` (`√-source`) — this is the FSim analogue of
--              `ParallelMonoFD`'s `op-transfer-ret` √-extension trick, and it is what
--              lets `stab` cover the half-terminated leaves even though `FSim.stab`
--              itself says nothing about terminated states.
--          The two independent operand τ*-runs are concatenated into one composite run
--          by `Par-τ*-L` then `Par-τ*-R` (each operand settles without disturbing the
--          other), composite stability comes from the reused `Par-stable` /
--          `Par-stable-termL` / `Par-stable-termR`, and the offer inclusion composes by
--          the new `Par-offer-mono` (built from the reused constructive offer
--          elim/intro lemmas `Par-offer-elim` / `-sync` / `-soloL` / `-soloR`).
--
--   div→ : `Diverges (Par A merge P₁ Q₁)` splits into an operand divergence by the
--          pre-existing certified König step `Par-Diverges→`, transfers through that
--          operand's `FSim.div→`, and re-lifts by the constructive `Par-Diverges-L/-R`
--          — exactly the `DRCongruence.cong-Par⊤-div→` pattern.
--
-- SIDE CONDITION (unavoidable, and strictly weaker than the ≈DR one).  `Sep A P₁ Q₁`
-- says the impl operands never both offer the SAME non-synchronised event, and stay so
-- under stepping.  Without it the `evBoth` case of `Par-ev-elim` puts the impl composite
-- into the inline overlap node `(Par P′ Q₁) ⊓ (Par P₁ Q′)`, whose two commit branches
-- need the spec to still be able to fire `e` on the OTHER side after having already
-- consumed it on one side: matching the overlap by a solo spec step leaves the second
-- commit needing `FSim P₁ P₂′` (the pre-`e` impl operand against the post-`e` spec
-- operand), and matching it by a spec overlap leaves the commits needing the operand
-- relations at the spec's INTERMEDIATE (pre-trailing-τ) states.  Neither is derivable
-- from the operand `FSim`s, so the restriction is intrinsic to the overlap encoding of
-- `Par`, not an artefact of the one-way formulation.  `Sep` is `DRCongruence`'s
-- invariant generalised to two carriers; only the `now` + closure fields are needed here
-- (no τ*/weak-run closure, since only impl-side single-step residuals occur).
--
-- This module declares NO postulate, no NON_TERMINATING, no sized type and no hole.  The
-- only classical ingredient anywhere in the proof is the pre-existing, repo-fixed
-- `Par-Diverges→` König interface (certified from one `dne` in
-- `CSP.Laws.ClassicalFromLEM`), used for `div→` exactly as `DRCongruence` uses it;
-- `fwd` and `stab` are fully constructive.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt₀)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FSim.ParCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.Refusals   {E = E} {I = ExtI E} using (Offers)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E} using (FSim; fsim-refl)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync; fPar-er; fPar-re; fPar-nn)
open import CSP.Laws.Traces.TraceLawsParallelMono  E-≟
  using ( brBoth-commitL; brBoth-commitR
        ; par-hVisL-eq; par-hVisR-eq
        ; par-pVis-soloL-eq; par-pVis-soloR-eq; par-pVis-both-eq )
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟
  using ( ParτR; τL; τR; Par-τ-elim
        ; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim; fPar-rr )
open import CSP.Laws.FD.ParallelRefusals E-≟
  using ( Par-offer-elim; Par-offer-sync; Par-offer-soloL; Par-offer-soloR
        ; Par-stable; Par-stable-termL; Par-stable-termR
        ; stable-no-√-offer )
open import CSP.Laws.FD.ParallelDivergence E-≟
  using (Par-Diverges→; Par-Diverges-L; Par-Diverges-R)
open import CSP.Laws.FD.ParallelMonoFD E-≟ using (ParNormal; Par-stable-normal)

-- NOTE on levels: `Par-stable-normal` (reused from ParallelMonoFD) pins its three
-- carriers to ONE level, so every signature below quantifies `R₁ R₂ R : Set ℓr`
-- explicitly (generalizable `variable`s would hand each carrier a private level copy).
-- This costs nothing: the CSP instances all have R₁ = R₂ = R = ⊤.

-------------------------------------------------------------------------------------
-- τ*-LIFTING: an operand's silent run lifts to a silent run of the composite, on each
-- side INDEPENDENTLY, so two operand runs concatenate into one composite run.
-------------------------------------------------------------------------------------

-- a LEFT operand's τ* run lifts to a τ* run of the composite (map Par-τ-L)
Par-τ*-L : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           {P′ : PTree E (ExtI E) R₁}
         → P ─[τ*]─► P′ → (Par A merge P Q) ─[τ*]─► (Par A merge P′ Q)
Par-τ*-L A merge P Q τ*-refl           = τ*-refl
Par-τ*-L A merge P Q (τ*-step Pτ rest) =
  τ*-step (Par-τ-L A merge P Q Pτ) (Par-τ*-L A merge _ Q rest)

-- a RIGHT operand's τ* run lifts to a τ* run of the composite (map Par-τ-R)
Par-τ*-R : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           {Q′ : PTree E (ExtI E) R₂}
         → Q ─[τ*]─► Q′ → (Par A merge P Q) ─[τ*]─► (Par A merge P Q′)
Par-τ*-R A merge P Q τ*-refl           = τ*-refl
Par-τ*-R A merge P Q (τ*-step Qτ rest) =
  τ*-step (Par-τ-R A merge P Q Qτ) (Par-τ*-R A merge P _ rest)

-------------------------------------------------------------------------------------
-- SINGLE-STEP solo lifting.  A non-sync solo event of one operand lifts to a composite
-- visible step FOLLOWED BY a τ* tail: the tail is empty unless the other operand also
-- offered the event, in which case the composite went through the overlap node and the
-- single commit-τ finishes the job.  (Port of DRCongruence's Par-soloL/R-step to
-- arbitrary carriers + `merge`.)
-------------------------------------------------------------------------------------

-- a LEFT solo step lifts to: composite step, then a τ* run into `Par P₁ Q`
Par-soloL-step : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {e : E X} {a : X} {P₁ : PTree E (ExtI E) R₁}
               → ¬ A .mem (X , e) a
               → P ─[ ev (evl (evLabel X e a)) ]─► P₁
               → Σ[ M ∈ PTree E (ExtI E) R ]
                   (((Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► M)
                    × (M ─[τ*]─► (Par A merge P₁ Q)))
Par-soloL-step A merge P Q {X} {e} {a} {P₁} ¬cs (sVis {v = vP} {τc = τcP} eqP veqP)
  with PTree.force Q in eqQ
... | ret r₂ = (Par A merge P₁ Q)
             , sVis (fPar-er A merge eqP eqQ)
                    (par-hVisL-eq A merge {vP = vP} Q {at = X , e} {a = a} ¬cs veqP)
             , τ*-refl
... | sil Q' = (Par A merge P₁ Q)
             , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                    (par-pVis-soloL-eq A merge (react vP τcP) (sil Q') P Q
                                       {at = X , e} {a = a} ¬cs veqP refl)
             , τ*-refl
... | react vQ τcQ with vQ (X , e) a in vqeq
...   | nothing = (Par A merge P₁ Q)
                , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                       (par-pVis-soloL-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                          {at = X , e} {a = a} ¬cs veqP vqeq)
                , τ*-refl
...   | just Q₁ = ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁))
                , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                       (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                         {at = X , e} {a = a} ¬cs veqP vqeq)
                , τ*-step (brBoth-commitL A merge P Q P₁ Q₁) τ*-refl

-- a RIGHT solo step lifts to: composite step, then a τ* run into `Par P Q₁`
Par-soloR-step : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {e : E X} {a : X} {Q₁ : PTree E (ExtI E) R₂}
               → ¬ A .mem (X , e) a
               → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
               → Σ[ M ∈ PTree E (ExtI E) R ]
                   (((Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─► M)
                    × (M ─[τ*]─► (Par A merge P Q₁)))
Par-soloR-step A merge P Q {X} {e} {a} {Q₁} ¬cs (sVis {v = vQ} {τc = τcQ} eqQ veqQ)
  with PTree.force P in eqP
... | ret r₁ = (Par A merge P Q₁)
             , sVis (fPar-re A merge eqP eqQ)
                    (par-hVisR-eq A merge P {vQ = vQ} {at = X , e} {a = a} ¬cs veqQ)
             , τ*-refl
... | sil P' = (Par A merge P Q₁)
             , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                    (par-pVis-soloR-eq A merge (sil P') (react vQ τcQ) P Q
                                       {at = X , e} {a = a} ¬cs refl veqQ)
             , τ*-refl
... | react vP τcP with vP (X , e) a in vpeq
...   | nothing = (Par A merge P Q₁)
                , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                       (par-pVis-soloR-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                          {at = X , e} {a = a} ¬cs vpeq veqQ)
                , τ*-refl
...   | just P₁ = ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁))
                , sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                       (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                         {at = X , e} {a = a} ¬cs vpeq veqQ)
                , τ*-step (brBoth-commitR A merge P Q P₁ Q₁) τ*-refl

-------------------------------------------------------------------------------------
-- WEAK-STEP lifting: the three shapes the forward simulation has to produce.
-------------------------------------------------------------------------------------

-- a weak non-sync solo event of the LEFT operand lifts to a weak step of the composite
Par-wsoloL : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
             (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
             {X : Set ℓ} {e : E X} {a : X} {P′ : PTree E (ExtI E) R₁}
           → ¬ A .mem (X , e) a
           → P ═[ ev (evl (evLabel X e a)) ]═► P′
           → (Par A merge P Q) ═[ ev (evl (evLabel X e a)) ]═► (Par A merge P′ Q)
Par-wsoloL A merge P Q ¬cs (wev p→pₛ pₛev pₘ→p′)
  with Par-soloL-step A merge _ Q ¬cs pₛev
... | M , step , M→Par =
      wev (Par-τ*-L A merge P Q p→pₛ) step
          (τ*-trans M→Par (Par-τ*-L A merge _ Q pₘ→p′))

-- a weak non-sync solo event of the RIGHT operand lifts to a weak step of the composite
Par-wsoloR : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
             (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
             {X : Set ℓ} {e : E X} {a : X} {Q′ : PTree E (ExtI E) R₂}
           → ¬ A .mem (X , e) a
           → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
           → (Par A merge P Q) ═[ ev (evl (evLabel X e a)) ]═► (Par A merge P Q′)
Par-wsoloR A merge P Q ¬cs (wev q→qₛ qₛev qₘ→q′)
  with Par-soloR-step A merge P _ ¬cs qₛev
... | M , step , M→Par =
      wev (Par-τ*-R A merge P Q q→qₛ) step
          (τ*-trans M→Par (Par-τ*-R A merge P _ qₘ→q′))

-- BOTH operands weakly perform the same shared event ⇒ the composite weakly synchronises
-- on it (the two operands' leading τ*-runs are concatenated, then `Par-sync` fires, then
-- the two trailing τ*-runs are concatenated).
Par-wsync-both : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {e : E X} {a : X}
                 {P′ : PTree E (ExtI E) R₁} {Q′ : PTree E (ExtI E) R₂}
               → A .mem (X , e) a
               → P ═[ ev (evl (evLabel X e a)) ]═► P′
               → Q ═[ ev (evl (evLabel X e a)) ]═► Q′
               → (Par A merge P Q) ═[ ev (evl (evLabel X e a)) ]═► (Par A merge P′ Q′)
Par-wsync-both A merge P Q cs (wev p→pₛ pₛev pₘ→p′) (wev q→qₛ qₛev qₘ→q′) =
  wev (τ*-trans (Par-τ*-L A merge P Q p→pₛ) (Par-τ*-R A merge _ Q q→qₛ))
      (Par-sync A merge _ _ cs pₛev qₛev)
      (τ*-trans (Par-τ*-L A merge _ _ pₘ→p′) (Par-τ*-R A merge _ _ qₘ→q′))

-- a √ step comes from a `ret` node carrying exactly the ticked value
√-source : ∀ {ℓr} {R : Set ℓr} {p t : PTree E (ExtI E) R} {r : R}
         → p ─[ ev (√ r) ]─► t → PTree.force p ≡ ret r
√-source (sRet eq) = eq

-- BOTH operands weakly terminate ⇒ the composite weakly performs the joint √ into
-- deadlock (the two silent runs to the operands' `ret`s are concatenated).
Par-w√-both : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
              (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
              {r₁ : R₁} {r₂ : R₂} {P′ : PTree E (ExtI E) R₁} {Q′ : PTree E (ExtI E) R₂}
            → P ═[ ev (√ r₁) ]═► P′ → Q ═[ ev (√ r₂) ]═► Q′
            → (Par A merge P Q) ═[ ev (√ (merge r₁ r₂)) ]═► deadlock
Par-w√-both A merge P Q (wev p→pₛ pₛev _) (wev q→qₛ qₛev _) =
  wev (τ*-trans (Par-τ*-L A merge P Q p→pₛ) (Par-τ*-R A merge _ Q q→qₛ))
      (sRet (fPar-rr A merge (√-source pₛev) (√-source qₛev)))
      τ*-refl

-------------------------------------------------------------------------------------
-- THE SEPARATION INVARIANT (DRCongruence's `Sep`, generalised to two carriers).
-- `now` refutes the payload of `Par-ev-elim`'s `evBoth` at the CURRENT heads; the two
-- closure fields make the invariant available at every single-step residual pair.
-- Only the IMPL operand pair needs it here, because only the impl composite is inverted.
-------------------------------------------------------------------------------------

record Sep {ℓr} {R₁ R₂ : Set ℓr} (A : EventSet)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    -- the two operands never both offer the same NON-synchronised event
    now   : ∀ {X : Set ℓ} {e : E X} {a : X}
              {P′ : PTree E (ExtI E) R₁} {Q′ : PTree E (ExtI E) R₂}
          → ¬ A .mem (X , e) a
          → P ─[ ev (evl (evLabel X e a)) ]─► P′
          → Q ─[ ev (evl (evLabel X e a)) ]─► Q′
          → ⊥
    -- …and that stays true after ANY step of the left operand…
    stepL : ∀ {l : Label R₁} {P′ : PTree E (ExtI E) R₁} → P ─[ l ]─► P′ → Sep A P′ Q
    -- …or of the right operand
    stepR : ∀ {l : Label R₂} {Q′ : PTree E (ExtI E) R₂} → Q ─[ l ]─► Q′ → Sep A P Q′
open Sep

-- `deadlock` (= Stop) offers nothing and cannot step, so it is separated from every Q
-- (a ready-made, non-vacuous `Sep` witness).
Sep-deadlock-L : ∀ {ℓr} {R₁ R₂ : Set ℓr} (A : EventSet) (Q : PTree E (ExtI E) R₂)
               → Sep A (deadlock {E = E} {I = ExtI E} {R = R₁}) Q
Sep-deadlock-L A Q .now   _ (sVis refl ()) _
Sep-deadlock-L A Q .stepL (sSil ())
Sep-deadlock-L A Q .stepL (sVis refl ())
Sep-deadlock-L A Q .stepL (sTau refl ())
Sep-deadlock-L A Q .stepR Qstep = Sep-deadlock-L A _

-- mirror: `deadlock` on the right is separated from every P
Sep-deadlock-R : ∀ {ℓr} {R₁ R₂ : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R₁)
               → Sep A P (deadlock {E = E} {I = ExtI E} {R = R₂})
Sep-deadlock-R A P .now   _ _ (sVis refl ())
Sep-deadlock-R A P .stepL Pstep = Sep-deadlock-R A _
Sep-deadlock-R A P .stepR (sSil ())
Sep-deadlock-R A P .stepR (sVis refl ())
Sep-deadlock-R A P .stepR (sTau refl ())

-------------------------------------------------------------------------------------
-- OFFER DECOMPOSITION / COMPOSITION for `stab`.
-------------------------------------------------------------------------------------

-- OFFER MONOTONICITY: operand-wise offer inclusion composes to composite offer
-- inclusion.  The `evl` cases route through the reused constructive offer elim/intro
-- (a shared event needs BOTH operands, a non-shared one EITHER); the √ case cannot
-- arise because the including composite is stable and a √-offer needs a `ret` force.
Par-offer-mono : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P₁ P₂ : PTree E (ExtI E) R₁) (Q₁ Q₂ : PTree E (ExtI E) R₂)
               → isStable (Par A merge P₂ Q₂)
               → (∀ e → Offers P₂ e → Offers P₁ e)
               → (∀ e → Offers Q₂ e → Offers Q₁ e)
               → ∀ e → Offers (Par A merge P₂ Q₂) e → Offers (Par A merge P₁ Q₁) e
Par-offer-mono A merge P₁ P₂ Q₁ Q₂ st inclP inclQ (evl (evLabel X f a)) off
  with Par-offer-elim A merge P₂ Q₂ off
... | inj₁ (cs  , oP , oQ)  = Par-offer-sync  A merge P₁ Q₁ cs  (inclP _ oP) (inclQ _ oQ)
... | inj₂ (¬cs , inj₁ oP)  = Par-offer-soloL A merge P₁ Q₁ ¬cs (inclP _ oP)
... | inj₂ (¬cs , inj₂ oQ)  = Par-offer-soloR A merge P₁ Q₁ ¬cs (inclQ _ oQ)
Par-offer-mono A merge P₁ P₂ Q₁ Q₂ st inclP inclQ (√ r) off =
  ⊥-elim (stable-no-√-offer {t = Par A merge P₂ Q₂} st off)

-- a terminated state's ONLY offer is its own √, which an equally-terminated state also
-- offers — the offer inclusion for a `ret` operand (where `FSim.stab` says nothing).
ret-offer-incl : ∀ {ℓr} {R₁ : Set ℓr} {S T : PTree E (ExtI E) R₁} {r : R₁}
               → PTree.force S ≡ ret r → PTree.force T ≡ ret r
               → ∀ e → Offers S e → Offers T e
ret-offer-incl {S = S} eqS eqT (evl _) (_ , sVis eqf _) =
  ⊥-elim (case trans (sym eqS) eqf of λ ())
ret-offer-incl {S = S} eqS eqT (√ x)   (_ , sRet eqf) with trans (sym eqS) eqf
... | refl = deadlock , sRet eqT

-------------------------------------------------------------------------------------
-- THE `stab` FIELD, one named lemma per `ParNormal` leaf.  In all three the spec
-- composite settles by running the LEFT operand's silent run first (Par-τ*-L) and the
-- RIGHT operand's afterwards (Par-τ*-R) — legitimate because each lift leaves the other
-- operand untouched.
-------------------------------------------------------------------------------------

-- BOTH impl operands stable: settle both spec operands with their own `FSim.stab`
Par-fsim-stab-both : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                     {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
                   → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
                   → isStable P₁ → isStable Q₁
                   → Σ[ M ∈ PTree E (ExtI E) R ]
                       ( (Par A merge P₂ Q₂) ─[τ*]─► M × isStable M
                       × (∀ e → Offers M e → Offers (Par A merge P₁ Q₁) e) )
Par-fsim-stab-both A merge {P₁} {P₂} {Q₁} {Q₂} pp qq stP stQ
  with pp .FSim.stab stP | qq .FSim.stab stQ
... | P₂* , rP , stP* , inclP | Q₂* , rQ , stQ* , inclQ =
      Par A merge P₂* Q₂*
    , τ*-trans (Par-τ*-L A merge P₂ Q₂ rP) (Par-τ*-R A merge P₂* Q₂ rQ)
    , Par-stable A merge P₂* Q₂* stP* stQ*
    , Par-offer-mono A merge P₁ P₂* Q₁ Q₂*
        (Par-stable A merge P₂* Q₂* stP* stQ*) inclP inclQ

-- LEFT impl operand terminated, RIGHT stable: the spec's left operand is settled by
-- matching the impl's √ step (its weak match exhibits a τ*-run into a `ret r₁` state),
-- the spec's right operand by its own `FSim.stab`.
Par-fsim-stab-termL : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                      {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
                      {r₁ : R₁}
                    → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
                    → PTree.force P₁ ≡ ret r₁ → isStable Q₁
                    → Σ[ M ∈ PTree E (ExtI E) R ]
                        ( (Par A merge P₂ Q₂) ─[τ*]─► M × isStable M
                        × (∀ e → Offers M e → Offers (Par A merge P₁ Q₁) e) )
Par-fsim-stab-termL A merge {P₁} {P₂} {Q₁} {Q₂} pp qq eqP stQ
  with pp .FSim.fwd .WSimF.on-ev (sRet eqP) | qq .FSim.stab stQ
... | _ , wev {p′ = P₂ₛ} p→pₛ pₛev _ , _ | Q₂* , rQ , stQ* , inclQ =
      Par A merge P₂ₛ Q₂*
    , τ*-trans (Par-τ*-L A merge P₂ Q₂ p→pₛ) (Par-τ*-R A merge P₂ₛ Q₂ rQ)
    , Par-stable-termL A merge P₂ₛ Q₂* (√-source pₛev) stQ*
    , Par-offer-mono A merge P₁ P₂ₛ Q₁ Q₂*
        (Par-stable-termL A merge P₂ₛ Q₂* (√-source pₛev) stQ*)
        (ret-offer-incl (√-source pₛev) eqP) inclQ

-- LEFT impl operand stable, RIGHT terminated (mirror of Par-fsim-stab-termL)
Par-fsim-stab-termR : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                      {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
                      {r₂ : R₂}
                    → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
                    → isStable P₁ → PTree.force Q₁ ≡ ret r₂
                    → Σ[ M ∈ PTree E (ExtI E) R ]
                        ( (Par A merge P₂ Q₂) ─[τ*]─► M × isStable M
                        × (∀ e → Offers M e → Offers (Par A merge P₁ Q₁) e) )
Par-fsim-stab-termR A merge {P₁} {P₂} {Q₁} {Q₂} pp qq stP eqQ
  with pp .FSim.stab stP | qq .FSim.fwd .WSimF.on-ev (sRet eqQ)
... | P₂* , rP , stP* , inclP | _ , wev {p′ = Q₂ₛ} q→qₛ qₛev _ , _ =
      Par A merge P₂* Q₂ₛ
    , τ*-trans (Par-τ*-L A merge P₂ Q₂ rP) (Par-τ*-R A merge P₂* Q₂ q→qₛ)
    , Par-stable-termR A merge P₂* Q₂ₛ stP* (√-source qₛev)
    , Par-offer-mono A merge P₁ P₂* Q₁ Q₂ₛ
        (Par-stable-termR A merge P₂* Q₂ₛ stP* (√-source qₛev))
        inclP (ret-offer-incl (√-source qₛev) eqQ)

-- the `stab` field itself: classify the stable impl composite (reused, constructive
-- `Par-stable-normal`) and apply the matching leaf lemma.  NO side condition.
Par-fsim-stab : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
              → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
              → isStable (Par A merge P₁ Q₁)
              → Σ[ M ∈ PTree E (ExtI E) R ]
                  ( (Par A merge P₂ Q₂) ─[τ*]─► M × isStable M
                  × (∀ e → Offers M e → Offers (Par A merge P₁ Q₁) e) )
Par-fsim-stab A merge {P₁} {P₂} {Q₁} {Q₂} pp qq st
  with Par-stable-normal A merge P₁ Q₁ st
... | inj₁ (stP , stQ)             = Par-fsim-stab-both  A merge pp qq stP stQ
... | inj₂ (inj₁ (r₁ , eqP , stQ)) = Par-fsim-stab-termL A merge pp qq eqP stQ
... | inj₂ (inj₂ (stP , r₂ , eqQ)) = Par-fsim-stab-termR A merge pp qq stP eqQ

-------------------------------------------------------------------------------------
-- THE `div→` FIELD: split the composite livelock with the certified König step, push
-- the guilty operand through its own `div→`, re-lift constructively.
-------------------------------------------------------------------------------------

-- divergence transfer for the parallel congruence
Par-fsim-div→ : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
                {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
              → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
              → Diverges (Par A merge P₁ Q₁) → Diverges (Par A merge P₂ Q₂)
Par-fsim-div→ A merge {P₂ = P₂} {Q₂ = Q₂} pp qq d with Par-Diverges→ A merge d
... | inj₁ dP = Par-Diverges-L A merge Q₂ (pp .FSim.div→ dP)
... | inj₂ dQ = Par-Diverges-R A merge P₂ (qq .FSim.div→ dQ)

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations (no old-style mutual block): the corecursive
-- `Par-fsim` residuals sit under the `WSimF` Σ-results of `f-sim-Par`, which is exactly
-- the guardedness discipline `DRCongruence.dr-sim-Par⊤-L` uses.  Operands are passed as
-- ARGUMENTS to every lift lemma and are never `with`-forced at the call site, so no
-- composite is ever driven to weak head normal form here.
-------------------------------------------------------------------------------------

-- HEADLINE: `Par` is an FSim congruence (spec operands failure-simulate impl operands)
Par-fsim : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
           {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
         → Sep A P₁ Q₁ → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
         → FSim R (Par A merge P₁ Q₁) (Par A merge P₂ Q₂)

-- the forward-simulation half: invert an impl composite step, match it operand-wise,
-- re-lift the operand's WEAK match to the composite
f-sim-Par : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (A : EventSet) (merge : Mg R₁ R₂ R)
            {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
          → Sep A P₁ Q₁ → FSim R₁ P₁ P₂ → FSim R₂ Q₁ Q₂
          → WSimF (FSim R) (Par A merge P₁ Q₁) (Par A merge P₂ Q₂)

-- visible steps
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-ev step
  with Par-ev-elim A merge P₁ Q₁ step
-- a shared event: BOTH impl operands fired it, so both spec operands match it weakly
... | evSync {X} {e} {a} {P′} {Q′} cs Pev Qev
      with pp .FSim.fwd .WSimF.on-ev Pev | qq .FSim.fwd .WSimF.on-ev Qev
...     | P₂′ , wP , relP | Q₂′ , wQ , relQ =
          Par A merge P₂′ Q₂′
        , Par-wsync-both A merge P₂ Q₂ cs wP wQ
        , Par-fsim A merge ((sep .stepL Pev) .stepR Qev) relP relQ
-- a non-shared solo event of the LEFT impl operand
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-ev step
    | evL {X} {e} {a} {P′} ¬cs Pev with pp .FSim.fwd .WSimF.on-ev Pev
...   | P₂′ , wP , relP =
        Par A merge P₂′ Q₂
      , Par-wsoloL A merge P₂ Q₂ ¬cs wP
      , Par-fsim A merge (sep .stepL Pev) relP qq
-- a non-shared solo event of the RIGHT impl operand
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-ev step
    | evR {X} {e} {a} {Q′} ¬cs Qev with qq .FSim.fwd .WSimF.on-ev Qev
...   | Q₂′ , wQ , relQ =
        Par A merge P₂ Q₂′
      , Par-wsoloR A merge P₂ Q₂ ¬cs wQ
      , Par-fsim A merge (sep .stepR Qev) pp relQ
-- the both-offer overlap: impossible under `Sep` (this is the ONE case needing it)
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-ev step
    | evBoth ¬cs Pev Qev = ⊥-elim (sep .now ¬cs Pev Qev)
-- the joint √: both impl operands are at `ret`, so both spec operands weakly terminate
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-ev step
    | ev√ {r₁} {r₂} eqP eqQ
      with pp .FSim.fwd .WSimF.on-ev (sRet eqP) | qq .FSim.fwd .WSimF.on-ev (sRet eqQ)
...     | _ , wP , _ | _ , wQ , _ =
          deadlock , Par-w√-both A merge P₂ Q₂ wP wQ , fsim-refl deadlock

-- τ steps
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-tau step
  with Par-τ-elim A merge P₁ Q₁ step
... | τL P′ Pτ refl with pp .FSim.fwd .WSimF.on-tau Pτ
...   | P₂′ , wτ run , relP =
        Par A merge P₂′ Q₂
      , wτ (Par-τ*-L A merge P₂ Q₂ run)
      , Par-fsim A merge (sep .stepL Pτ) relP qq
f-sim-Par A merge {P₁} {P₂} {Q₁} {Q₂} sep pp qq .WSimF.on-tau step
    | τR Q′ Qτ refl with qq .FSim.fwd .WSimF.on-tau Qτ
...   | Q₂′ , wτ run , relQ =
        Par A merge P₂ Q₂′
      , wτ (Par-τ*-R A merge P₂ Q₂ run)
      , Par-fsim A merge (sep .stepR Qτ) pp relQ

Par-fsim A merge sep pp qq .FSim.fwd       = f-sim-Par     A merge sep pp qq
Par-fsim A merge sep pp qq .FSim.stab st   = Par-fsim-stab A merge pp qq st
Par-fsim A merge sep pp qq .FSim.div→  d   = Par-fsim-div→ A merge pp qq d

-------------------------------------------------------------------------------------
-- CSP corollaries: the ⊤-merge instances.
-------------------------------------------------------------------------------------

-- alphabetised parallel is an FSim congruence
∥-fsim : ∀ {ℓr} (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
       → Sep A P₁ Q₁ → FSim (⊤ {ℓr}) P₁ P₂ → FSim (⊤ {ℓr}) Q₁ Q₂
       → FSim (⊤ {ℓr}) (P₁ ∥⇘ A ⇙ Q₁) (P₂ ∥⇘ A ⇙ Q₂)
∥-fsim A = Par-fsim A (λ _ _ → tt)

-- interleaving (the A = ∅ES instance, where EVERY event is non-shared, so `Sep ∅ES P Q`
-- says P and Q share no offered event at all) is an FSim congruence
⦀-fsim : ∀ {ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
       → Sep ∅ES P₁ Q₁ → FSim (⊤ {ℓr}) P₁ P₂ → FSim (⊤ {ℓr}) Q₁ Q₂
       → FSim (⊤ {ℓr}) (P₁ ⦀ Q₁) (P₂ ⦀ Q₂)
⦀-fsim = Par-fsim ∅ES (λ _ _ → tt)
