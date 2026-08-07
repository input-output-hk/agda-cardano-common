{-# OPTIONS --guardedness #-}

-- WEAK LIFTING machinery for EXTERNAL CHOICE `_□_`, in the currency the `FSim` layer
-- speaks: single-step τ*-runs (`_─[τ*]─►_`), weak steps (`_═[_]═►_`) and `Offers`
-- inclusions.  Everything here is a statement about the LTS only — no `FSim`, no
-- refinement — so it is equally usable by the DR / trace layers.
--
-- ⚠ THE NAIVE τ*-LIFT IS FALSE.  `force (P □ Q)` resolves the composite EAGERLY when
-- an operand terminates: with `force Q ≡ ret r` a τ of `P` fires `□-τ-toslide` and
-- lands in `P′ ▷ Q` (Roscoe's R3 — the terminated operand becomes a TIMEOUT), NOT in
-- `P′ □ Q` (`□-τ-tochoice`, which needs `NonRet (force Q)`).  Two forms are therefore
-- provided, and BOTH are used downstream:
--
--   * `□-τ*-L-live` / `□-τ*-R-live` — the other operand is FIXED and `NonRet`, so the
--     composite stays a `□` throughout.  This is the form the `stab` field wants: the
--     settle target is STABLE, hence never a `ret`, which (via `τ*-stable-live`) is
--     exactly what supplies the `NonRet` premise for free.
--   * `□-τ*-L` / `□-τ*-R` — UNCONDITIONAL, with the conclusion a DISJUNCTION: the run
--     lands in `P′ □ Q` or in `P′ ▷ Q`.  Chosen over a `NonRet`-indexed statement
--     because the consumers that cannot supply `NonRet` (the weak-step lifts) go on to
--     perform a VISIBLE step, and a visible step DISSOLVES both shapes onto the same
--     successor (`□-ev-weak-L` for the choice, the reused `▷-ev-L` for the slide) — so
--     the disjunction is absorbed immediately and never propagates into a residual.
--
-- Contents:
--   □-τ*-L-live / -R-live, □-τ*-L / -R   silent-run lifting (above)
--   □-τ*-settle                          the two-operand settle run used by `stab`
--   □-ev-weak-L / -R                     ONE visible-or-√ step, as a τ*·ev·τ* triple:
--                                        the τ-prefix is the √-commit that a terminated
--                                        operand forces (cf. `□-ev-toL`'s `sRet` cases),
--                                        the τ-suffix resolves the `P₁ ⊓ Q₁` that an
--                                        offer overlap creates
--   □-wev-L / -R, □-w√-L / -R            WEAK visible / √ lifting
--   □-ev-LR, □-wev-LR                    the BOTH-OFFER case (lands in `P₁ ⊓ Q₁`)
--   □-offer-mono                         `Par-offer-mono`'s analogue, for `stab`
--
-- POSTULATES: none, local or inherited-and-used — neither `□-Diverges→` nor
-- `▷-Diverges→` (`CSP.Laws.FD.ExtChoiceDivergence`) appears as a term anywhere below.
-- The closure is nevertheless NOT `--safe`-clean: `agda --safe
-- CSP/Laws/FSim/ExtChoiceLift.agda` fails with two `SafeFlagPostulate` errors, one per
-- name, because `ExtChoiceDivergence` is reachable — TWICE over, in fact: directly via
-- `CSP.Laws.FD.ExtChoiceFD` (imported below for `□-offers-L`) and again via
-- `CSP.Laws.FSim.SlideCong` (imported for `▷-τ*-L`).  So the postulates are not
-- reachable "from nothing below" — they are reachable from two places — merely UNUSED
-- by this module's own proofs.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FSim.ExtChoiceLift {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev)
open import Semantics.Refusals  {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable→react)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq;
         □-τ-tochoice; □-τ-toslide; □-τ-tochoice-R; □-τ-toslide-R)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.FD.ExtChoiceFD  E-≟ using (□-offers-L)
open import CSP.Laws.FD.ExtChoiceAssoc E-≟ using (□-offers-R; offers-□-elim)
open import CSP.Laws.FSim.SlideCong E-≟ using (▷-τ*-L)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- LIVENESS WITNESSES.  `NonRet` is stated against a NAMED node shape (`force t ≡ n`
-- plus `NonRet n`) throughout the `□` machinery, so each witness is produced in that
-- packaged form; the source of a step / of a run into a stable state is never a `ret`.
-------------------------------------------------------------------------------------

-- a state performing a τ is not terminated
τ-live : {t u : PTree E (ExtI E) R} → t ─[ τ ]─► u
       → Σ[ n ∈ NodeKind E (ExtI E) R ] (PTree.force t ≡ n × NonRet n)
τ-live (sSil {t = u} eq)              = sil u      , eq , tt
τ-live (sTau {v = v} {τc = τc} eq _)  = react v τc , eq , tt

-- a state offering a VISIBLE (non-√) event forces to a `react` node, so it is not
-- terminated.  (A √-offer says the opposite — hence the `evl` restriction.)
ev-live : {t u : PTree E (ExtI E) R} {A : Set ℓ} {e : E A} {a : A}
        → t ─[ ev (evl (evLabel A e a)) ]─► u
        → Σ[ n ∈ NodeKind E (ExtI E) R ] (PTree.force t ≡ n × NonRet n)
ev-live (sVis {v = v} {τc = τc} eq _) = react v τc , eq , tt

-- a stable state forces to a `react` node, so it is not terminated.  (The tree is an
-- EXPLICIT argument: `isStable t` reads `t` only under `force`, so it never determines
-- `t` by unification.)
stable-live : (t : PTree E (ExtI E) R) → isStable t
            → Σ[ n ∈ NodeKind E (ExtI E) R ] (PTree.force t ≡ n × NonRet n)
stable-live t st with stable→react {t = t} st
... | v , τc , eq , _ = react v τc , eq , tt

-- the SOURCE of a silent run ending in a visible offer is not terminated (either the
-- run has a first τ, or the source itself is the offering `react` node)
τ*-ev-live : {t u u′ : PTree E (ExtI E) R} {A : Set ℓ} {e : E A} {a : A}
           → t ─[τ*]─► u → u ─[ ev (evl (evLabel A e a)) ]─► u′
           → Σ[ n ∈ NodeKind E (ExtI E) R ] (PTree.force t ≡ n × NonRet n)
τ*-ev-live τ*-refl           step = ev-live step
τ*-ev-live (τ*-step first _) _    = τ-live first

-- the SOURCE of a silent run ending in a STABLE state is not terminated (a `ret` has
-- no τ, so it would have to BE the stable state — and a `ret` is never stable)
τ*-stable-live : (t : PTree E (ExtI E) R) {u : PTree E (ExtI E) R}
               → t ─[τ*]─► u → isStable u
               → Σ[ n ∈ NodeKind E (ExtI E) R ] (PTree.force t ≡ n × NonRet n)
τ*-stable-live t τ*-refl           st = stable-live t st
τ*-stable-live t (τ*-step first _) _  = τ-live first

-------------------------------------------------------------------------------------
-- SILENT-RUN LIFTING, `NonRet`-indexed form.  The other operand is FIXED, so its
-- liveness witness is supplied once and reused at every step of the run: the merged
-- τ-branch fires throughout and the composite remains a `□`.
-------------------------------------------------------------------------------------

-- a silent run of the LEFT operand lifts to one of the choice, keeping a live `Q`
□-τ*-L-live : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {nQ : NodeKind E (ExtI E) R} {P′ : PTree E (ExtI E) R}
            → PTree.force Q ≡ nQ → NonRet nQ
            → P ─[τ*]─► P′ → (P □ Q) ─[τ*]─► (P′ □ Q)
□-τ*-L-live P Q eqQ ntQ τ*-refl           = τ*-refl
□-τ*-L-live P Q eqQ ntQ (τ*-step Pτ rest) =
  τ*-step (□-τ-tochoice P Q Pτ eqQ ntQ) (□-τ*-L-live _ Q eqQ ntQ rest)

-- mirror: a silent run of the RIGHT operand, keeping a live `P`
□-τ*-R-live : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {nP : NodeKind E (ExtI E) R} {Q′ : PTree E (ExtI E) R}
            → PTree.force P ≡ nP → NonRet nP
            → Q ─[τ*]─► Q′ → (P □ Q) ─[τ*]─► (P □ Q′)
□-τ*-R-live P Q eqP ntP τ*-refl           = τ*-refl
□-τ*-R-live P Q eqP ntP (τ*-step Qτ rest) =
  τ*-step (□-τ-tochoice-R P Q Qτ eqP ntP) (□-τ*-R-live P _ eqP ntP rest)

-------------------------------------------------------------------------------------
-- SILENT-RUN LIFTING, unconditional (DISJUNCTIVE) form.  A terminated other operand
-- turns the FIRST τ into a slide (`□-τ-toslide`) and every later τ stays inside that
-- slide (the reused `▷-τ*-L`), so the whole run lands in `P′ ▷ Q`.
-------------------------------------------------------------------------------------

-- a silent run of the LEFT operand lifts to the choice (`Q` live or the run empty) or
-- to the slide over a terminated `Q`
□-τ*-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
       → P ─[τ*]─► P′
       → ((P □ Q) ─[τ*]─► (P′ □ Q)) ⊎ ((P □ Q) ─[τ*]─► (P′ ▷ Q))
□-τ*-L P Q τ*-refl = inj₁ τ*-refl
□-τ*-L P Q (τ*-step {t′ = P₁} Pτ rest) with PTree.force Q in eqQ
... | ret _     = inj₂ (τ*-step (□-τ-toslide  P Q Pτ eqQ)    (▷-τ*-L P₁ Q rest))
... | sil _     = inj₁ (τ*-step (□-τ-tochoice P Q Pτ eqQ tt) (□-τ*-L-live P₁ Q eqQ tt rest))
... | react _ _ = inj₁ (τ*-step (□-τ-tochoice P Q Pτ eqQ tt) (□-τ*-L-live P₁ Q eqQ tt rest))

-- mirror: a silent run of the RIGHT operand.  Note the slide is `Q′ ▷ P` — the
-- terminated operand becomes the TIMEOUT, so the operands swap places
□-τ*-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q′ : PTree E (ExtI E) R}
       → Q ─[τ*]─► Q′
       → ((P □ Q) ─[τ*]─► (P □ Q′)) ⊎ ((P □ Q) ─[τ*]─► (Q′ ▷ P))
□-τ*-R P Q τ*-refl = inj₁ τ*-refl
□-τ*-R P Q (τ*-step {t′ = Q₁} Qτ rest) with PTree.force P in eqP
... | ret _     = inj₂ (τ*-step (□-τ-toslide-R  P Q Qτ eqP)    (▷-τ*-L Q₁ P rest))
... | sil _     = inj₁ (τ*-step (□-τ-tochoice-R P Q Qτ eqP tt) (□-τ*-R-live P Q₁ eqP tt rest))
... | react _ _ = inj₁ (τ*-step (□-τ-tochoice-R P Q Qτ eqP tt) (□-τ*-R-live P Q₁ eqP tt rest))

-- BOTH operands settle: run the left operand's silent path first (`Q` is live because
-- it silently reaches a STABLE state, which is never a `ret`), then the right one's
-- (the settled left operand is stable, hence live).  This is the `stab` settle run.
□-τ*-settle : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P* Q* : PTree E (ExtI E) R}
            → P ─[τ*]─► P* → isStable P* → Q ─[τ*]─► Q* → isStable Q*
            → (P □ Q) ─[τ*]─► (P* □ Q*)
□-τ*-settle P Q {P*} runP stP runQ stQ
  with τ*-stable-live Q runQ stQ | stable-live P* stP
... | nQ , eqQ , ntQ | nP* , eqP* , ntP* =
      τ*-trans (□-τ*-L-live P Q eqQ ntQ runP) (□-τ*-R-live P* Q eqP* ntP* runQ)

-------------------------------------------------------------------------------------
-- ONE visible-or-√ STEP, lifted as a τ*·ev·τ* triple.  Two padding runs are needed
-- and neither can be dropped:
--   * the τ-PREFIX is the √-commit.  With `force P ≡ ret x` the composite is NOT ready
--     to √ unless the other operand terminated on the SAME value; otherwise it must
--     first τ-commit to `P` (the `sRet` cases of `□-ev-toL`, which insert exactly this).
--   * the τ-SUFFIX resolves an OFFER OVERLAP.  If both operands offer the event the
--     merged branch lands in `P₁ ⊓ Q₁`, and one `⊓-stepL` reaches `P₁`.
-------------------------------------------------------------------------------------

-- a LEFT visible-or-√ step lifts to a weak step of the choice reaching the SAME
-- successor.  Mirrors `□-ev-toL`, but exposing the run/step/run decomposition
□-ev-weak-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {P₁ : PTree E (ExtI E) R} {e : Event√ R}
            → P ─[ ev e ]─► P₁
            → Σ[ A ∈ PTree E (ExtI E) R ] Σ[ Z ∈ PTree E (ExtI E) R ]
                ((P □ Q) ─[τ*]─► A × A ─[ ev e ]─► Z × Z ─[τ*]─► P₁)
□-ev-weak-L P Q {P₁} (sVis {v = vP} {at = at} {a = a} eqP brP) with PTree.force Q in eqQ
... | ret _ = (P □ Q) , P₁ , τ*-refl , sVis (fL-F {P = P} {Q = Q} eqP eqQ) brP , τ*-refl
... | sil _ = (P □ Q) , P₁ , τ*-refl
            , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                   (mergeVis-L-eq {vP = vP} {vQ = ∅v} brP refl) , τ*-refl
... | react vQ τcQ with vQ at a in eqVQ
...   | nothing = (P □ Q) , P₁ , τ*-refl
                , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                       (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqVQ) , τ*-refl
...   | just Q₁ = (P □ Q) , (P₁ ⊓ Q₁) , τ*-refl
                , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                       (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqVQ)
                , τ*-step (⊓-stepL P₁ Q₁) τ*-refl
□-ev-weak-L P Q (sRet {x = x} eqP) with PTree.force Q in eqQ
... | ret r′ with x ≟ r′
...   | yes refl = (P □ Q) , deadlock , τ*-refl
                 , sRet (fL-A {P = P} {Q = Q} eqP eqQ) , τ*-refl
...   | no ¬eq   = P , deadlock
                 , τ*-step (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                                 (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl) τ*-refl
                 , sRet eqP , τ*-refl
□-ev-weak-L P Q (sRet {x = x} eqP) | sil _ =
      P , deadlock
    , τ*-step (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                    {a = lift fzero , lift fzero}
                    (fL-C {P = P} {Q = Q} eqP eqQ) refl) τ*-refl
    , sRet eqP , τ*-refl
□-ev-weak-L P Q (sRet {x = x} eqP) | react _ _ =
      P , deadlock
    , τ*-step (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                    {a = lift fzero , lift fzero}
                    (fL-D {P = P} {Q = Q} eqP eqQ) refl) τ*-refl
    , sRet eqP , τ*-refl

-- mirror: a RIGHT visible-or-√ step (the overlap resolves with `⊓-stepR`)
□-ev-weak-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {Q₁ : PTree E (ExtI E) R} {e : Event√ R}
            → Q ─[ ev e ]─► Q₁
            → Σ[ A ∈ PTree E (ExtI E) R ] Σ[ Z ∈ PTree E (ExtI E) R ]
                ((P □ Q) ─[τ*]─► A × A ─[ ev e ]─► Z × Z ─[τ*]─► Q₁)
□-ev-weak-R P Q {Q₁} (sVis {v = vQ} {at = at} {a = a} eqQ brQ) with PTree.force P in eqP
... | ret _ = (P □ Q) , Q₁ , τ*-refl , sVis (fL-D {P = P} {Q = Q} eqP eqQ) brQ , τ*-refl
... | sil _ = (P □ Q) , Q₁ , τ*-refl
            , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                   (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl brQ) , τ*-refl
... | react vP τcP with vP at a in eqVP
...   | nothing = (P □ Q) , Q₁ , τ*-refl
                , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                       (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ) , τ*-refl
...   | just P₁ = (P □ Q) , (P₁ ⊓ Q₁) , τ*-refl
                , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                       (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ)
                , τ*-step (⊓-stepR P₁ Q₁) τ*-refl
□-ev-weak-R P Q (sRet {x = x} eqQ) with PTree.force P in eqP
... | ret r′ with r′ ≟ x
...   | yes refl = (P □ Q) , deadlock , τ*-refl
                 , sRet (fL-A {P = P} {Q = Q} eqP eqQ) , τ*-refl
...   | no ¬eq   = Q , deadlock
                 , τ*-step (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                                 (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl) τ*-refl
                 , sRet eqQ , τ*-refl
□-ev-weak-R P Q (sRet {x = x} eqQ) | sil _ =
      Q , deadlock
    , τ*-step (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                    {a = lift fzero , lift fzero}
                    (fL-E {P = P} {Q = Q} eqP eqQ) refl) τ*-refl
    , sRet eqQ , τ*-refl
□-ev-weak-R P Q (sRet {x = x} eqQ) | react _ _ =
      Q , deadlock
    , τ*-step (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                    {a = lift fzero , lift fzero}
                    (fL-F {P = P} {Q = Q} eqP eqQ) refl) τ*-refl
    , sRet eqQ , τ*-refl

-------------------------------------------------------------------------------------
-- WEAK visible / √ LIFTING.  This is where the disjunction of `□-τ*-L` is absorbed:
-- whichever shape the silent prefix lands in, the visible step DISSOLVES it onto the
-- same successor — `□-ev-weak-L` for the choice, the reused `▷-ev-L` for the slide —
-- so the residual is the operand's own, and no mixed shape survives.
-------------------------------------------------------------------------------------

-- a weak visible-or-√ step of the LEFT operand lifts to one of the choice, reaching
-- exactly the operand's own successor
□-wev-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
          {P′ : PTree E (ExtI E) R} {e : Event√ R}
        → P ═[ ev e ]═► P′ → (P □ Q) ═[ ev e ]═► P′
□-wev-L P Q (wev {p′ = M} pre step post) with □-τ*-L P Q pre
... | inj₁ run with □-ev-weak-L M Q step
...   | A , Z , pre′ , step′ , post′ =
        wev (τ*-trans run pre′) step′ (τ*-trans post′ post)
□-wev-L P Q (wev {p′ = M} pre step post) | inj₂ run =
        wev run (▷-ev-L {Q = Q} step) post

-- mirror: a weak visible-or-√ step of the RIGHT operand
□-wev-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
          {Q′ : PTree E (ExtI E) R} {e : Event√ R}
        → Q ═[ ev e ]═► Q′ → (P □ Q) ═[ ev e ]═► Q′
□-wev-R P Q (wev {p′ = M} pre step post) with □-τ*-R P Q pre
... | inj₁ run with □-ev-weak-R P M step
...   | A , Z , pre′ , step′ , post′ =
        wev (τ*-trans run pre′) step′ (τ*-trans post′ post)
□-wev-R P Q (wev {p′ = M} pre step post) | inj₂ run =
        wev run (▷-ev-L {Q = P} step) post

-- the √ INSTANCE of the left lift, named for the callers that terminate an operand.
-- ⚠ It is NOT the naive "√ of `P` is a √ of `P □ Q`": the composite generally has to
-- τ-COMMIT first (`□-ev-weak-L`'s `sRet` cases supply that τ), which is why the
-- statement is a WEAK step and not a single transition
□-w√-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
         {X : PTree E (ExtI E) R} {r : R}
       → P ═[ ev (√ r) ]═► X → (P □ Q) ═[ ev (√ r) ]═► X
□-w√-L P Q w = □-wev-L P Q w

-- mirror: the √ instance of the right lift
□-w√-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
         {X : PTree E (ExtI E) R} {r : R}
       → Q ═[ ev (√ r) ]═► X → (P □ Q) ═[ ev (√ r) ]═► X
□-w√-R P Q w = □-wev-R P Q w

-------------------------------------------------------------------------------------
-- THE BOTH-OFFER CASE.  When both operands offer the SAME visible event the merged
-- offer map fires `mergeVis-LQ-eq` and the composite lands in the INTERNAL CHOICE
-- `P₁ ⊓ Q₁` of the two successors — the point at which `□` becomes nondeterministic.
-- Restricted to `evl` events: a √ is NOT of this shape (two terminated operands with
-- the same value produce a single `ret`, i.e. `fL-A`, not a `⊓`), and `□-wev-L` /
-- `□-w√-L` already cover that.
-------------------------------------------------------------------------------------

-- both operands offer the event ⇒ the choice offers it, landing in the internal
-- choice of the two successors
□-ev-LR : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {A : Set ℓ} {e : E A} {a : A}
          {P₁ Q₁ : PTree E (ExtI E) R}
        → P ─[ ev (evl (evLabel A e a)) ]─► P₁
        → Q ─[ ev (evl (evLabel A e a)) ]─► Q₁
        → (P □ Q) ─[ ev (evl (evLabel A e a)) ]─► (P₁ ⊓ Q₁)
□-ev-LR P Q pev qev with ev-inv pev | ev-inv qev
... | vP , τcP , eqP , brP | vQ , τcQ , eqQ , brQ =
      sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
           (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP brQ)

-- WEAK form: both operands silently reach offering states.  No disjunction arises —
-- an offering state is a `react` node, so neither operand can be terminated where the
-- other's silent run is lifted, and the composite stays a `□` the whole way
□-wev-LR : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {A : Set ℓ} {e : E A} {a : A}
           {PA PB QA QB : PTree E (ExtI E) R}
         → P ─[τ*]─► PA → PA ─[ ev (evl (evLabel A e a)) ]─► PB
         → Q ─[τ*]─► QA → QA ─[ ev (evl (evLabel A e a)) ]─► QB
         → (P □ Q) ═[ ev (evl (evLabel A e a)) ]═► (PB ⊓ QB)
□-wev-LR P Q {PA = PA} {QA = QA} preP stepP preQ stepQ
  with τ*-ev-live preQ stepQ | ev-live stepP
... | nQ , eqQ , ntQ | nPA , eqPA , ntPA =
      wev (τ*-trans (□-τ*-L-live P Q eqQ ntQ preP)
                    (□-τ*-R-live PA Q eqPA ntPA preQ))
          (□-ev-LR PA QA stepP stepQ)
          τ*-refl

-------------------------------------------------------------------------------------
-- OFFER MONOTONICITY, the `Par-offer-mono` analogue that `FSim.stab` consumes.  Much
-- cheaper than `Par`'s: `□`'s offers are the plain UNION of the operands', so an offer
-- of the composite projects to ONE operand (`offers-□-elim`) and re-lifts through the
-- corresponding intro.  No √ side case is needed — `□-offers-L/R` refute a `sRet`
-- against the `react` shape that stability already provides.
-------------------------------------------------------------------------------------

-- operand-wise offer inclusion composes to composite offer inclusion, given that the
-- INCLUDING (impl) operands are stable
□-offer-mono : ⦃ _ : DecEq R ⦄ (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R)
             → isStable P₁ → isStable Q₁
             → (∀ e → Offers P₂ e → Offers P₁ e)
             → (∀ e → Offers Q₂ e → Offers Q₁ e)
             → ∀ e → Offers (P₂ □ Q₂) e → Offers (P₁ □ Q₁) e
□-offer-mono P₁ P₂ Q₁ Q₂ stP stQ inclP inclQ e off
  with stable→react {t = P₁} stP | stable→react {t = Q₁} stQ
... | vP , τcP , eqP , _ | vQ , τcQ , eqQ , _
      with offers-□-elim {P = P₂} {Q = Q₂} off
...     | inj₁ oP = □-offers-L P₁ Q₁ eqP eqQ (proj₂ (inclP e oP))
...     | inj₂ oQ = □-offers-R P₁ Q₁ eqP eqQ (proj₂ (inclQ e oQ))
