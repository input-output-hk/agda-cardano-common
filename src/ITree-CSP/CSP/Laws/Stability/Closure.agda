{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- STABILITY, gathered: one import for "is this state τ-free?".
--
-- WHY THIS MODULE.  The measured outcome of the divergence-freedom experiment
-- (`CSP.Laws.DivFree.Closure`) was that `τ-Acc` did not pay off at the existing
-- proof sites, because every `ndivL`/`ndivR` obligation already needs strict
-- τ-FREENESS (`isStable`) for its `fwdT`/`bwdT` neighbour, and once you have that
-- non-divergence is `stable→¬div`, a one-liner.  So STABILITY, not
-- divergence-freedom, is the load-bearing notion — and it was scattered over a
-- dozen FD modules with four copies of `mk-stable` alone.
--
-- This module is the single place to look.  It RE-EXPORTS the per-operator
-- stability lemmas that already existed (nothing below is re-proved) and adds the
-- gaps found while gathering them (§9).  The GENERIC facts — those that mention no
-- CSP operator — deliberately live one layer down, in `Semantics.Stability`, and
-- are re-exported from here too.
--
-- CONTENTS
--   §1  generic core (from `Semantics.Stability`)
--   §2  leaves          `Stop`, `deadlock`, `deadlock ∖ Z`
--   §3  prefixes/menus  `pchoice v`, `e ⟶ P`, `e ⟶₀ P`, `menuOf`
--   §4  the UNSTABLE operators  `P ⊓ Q`, `P ▷ Q`, and the `□` shapes that slide
--   §5  external choice `P □ Q`
--   §6  parallel        `Par A merge P Q` (intro, elim, classify, reassociate)
--   §7  hide            `P ∖ A`
--   §8  bind / seq / iterate
--   §9  NEW: the gaps — `□-force-nn`, `stable-□`, `□-stable-elim`, `Par-stable?`
--
-- NOT gathered here, on purpose:
--   * `CSP.Laws.FD.InterruptFD` / `ThrowFD` (2181 + 882 lines, imported by nothing
--     else) own the `△` / `Θ` (un)stability lemmas.  Pulling them in would make
--     every client of this module pay for the two heaviest files in the tree for
--     lemmas that only those files use.  Their generic parts (`mk-stable`,
--     `isStable-force-eq`) were hoisted to `Semantics.Stability` instead.
--   * `Semantics.DivergenceFree` / `CSP.Laws.DivFree.Closure` — the τ-Acc calculus
--     is the *other* answer to the same question; `stable→τ-Acc` is the bridge.
--
-- USAGE NOTE.  Everything below is re-exported, so a client normally needs only
-- `open import CSP.Laws.Stability.Closure E-≟`.  If the client ALSO imports one of
-- the gathered modules directly (`Semantics.Stability`, `Semantics.Refusals`,
-- `CSP.Laws.FD.ParallelRefusals`, …), the shared names become `[AmbiguousName]` —
-- two applications of the same parameterised module do not unify, even when they
-- name the identical definition.  Fix that with `hiding (…)` on one of the two
-- imports; do not drop the re-export.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types in this file.  (It is not
-- `--safe`: several of the modules it gathers from sit above `Semantics.DRImpliesFD`,
-- which carries the development's one certified classical postulate.)
------------------------------------------------------------------------

open import Level using (Level; Lift; lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Stability.Closure {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet

private
  variable
    ℓr ℓs ℓ₁ ℓ₂ ℓx : Level
    R  : Set ℓr
    S  : Set ℓs
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    A  : Set ℓ

-------------------------------------------------------------------------------------
-- §1.  Generic core — everything that holds for an arbitrary `E`/`I`.
--
-- `Semantics.Stability` is the single owner: it is postulate-free by design, so a
-- client that only needs stability never imports `Semantics.DRImpliesFD`'s classical
-- step.  Names re-exported here:
--   INTRO   `mk-stable`, `react-no-τ→stable`
--   ELIM    `stable→react`, `stable-react-τc`, `stable-not-sil`, `stable-not-ret`
--   USE     `stable-no-τ`, `stable→¬div`, `stable→τ*-refl`
--   MOVE    `isStable-force-eq`, `stable-force-eq`
-------------------------------------------------------------------------------------

-- the LTS is imported but NOT re-exported: every client already has its own
-- `Semantics.LTS`, and re-exporting ~30 more names here would only widen the
-- ambiguity surface described above.
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Stability {E = E} {I = ExtI E} public

-------------------------------------------------------------------------------------
-- §2.  Leaves.
-------------------------------------------------------------------------------------

open import Semantics.Refusals {E = E} {I = ExtI E}
  using (Offers; Refuses; deadlock-stable; deadlock-refuses) public

-- `Stop = react ∅v ∅t` is stable (the maximally-refusing CSP leaf)
Stop-stable : isStable (Stop {R = R})
Stop-stable _ _ = refl

open import CSP.Laws.FD.HideFD E-≟ using (hide-deadlock-stable) public

-------------------------------------------------------------------------------------
-- §3.  Prefixes and visible menus — all of the shape `react v ∅t`.
--
-- The development grew THREE names for this one fact (`prefix-stable` in `FDCong`,
-- `pfx-stable` in `InputDist`, `prefix₀-stable` in `FDLawsPrefixDist`); each proof is
-- the single clause `_ _ = refl`, so deleting the copies would save nothing.  They
-- are simply gathered here, together with the general `pchoice`/menu forms that
-- subsume them.
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.SlideCombine       E-≟ using (pchoice-stable) public
open import CSP.Laws.FD.InputDistMenu      E-≟ using (menu-stable)    public
open import CSP.Laws.FD.InputDist          E-≟ using (pfx-stable)     public
open import CSP.Laws.FD.FDLawsPrefixDist   E-≟ using (prefix₀-stable) public

-- the canonical prefix stability (`pfx-stable` under the operator's own name)
⟶-stable : (e : E A) (P : A → PTree E (ExtI E) R) → isStable (e ⟶ P)
⟶-stable = pfx-stable

-------------------------------------------------------------------------------------
-- §4.  The operators that are NEVER stable — an internal choice always has its two
--      τ's, and a slide always has its timeout τ.  These are what make a `Refuses`
--      goal on `⊓`/`▷` vacuous, so they are used as often as the positive lemmas.
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟ using (⊓-unstable) public
open import CSP.Laws.FD.ExtChoiceFD        E-≟
  using (▷-unstable; □-⊓-unstable; □-Lret-unstable; □-Rret-unstable)
  -- (`mk-stable`, `stable-not-ret`, `stable-no-τ` are NOT taken from here: they are
  --  aliases of the §1 generics and re-exporting both would make the name ambiguous)
  public

-------------------------------------------------------------------------------------
-- §5.  External choice.
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.ExtChoiceIdem E-≟ using (stable-double; double-force-eq) public

-------------------------------------------------------------------------------------
-- §6.  Parallel — the richest group: INTRO for the three stable shapes, ELIM into
--      the operand normal form, a `StableClass` classifier, and reassociation.
-------------------------------------------------------------------------------------

open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg) public
open import CSP.Laws.FD.ParallelRefusals E-≟
  using (Par-stable; Par-stable-termL; Par-stable-termR) public
open import CSP.Laws.FD.ParallelMonoFD E-≟
  using (ParNormal; Par-stable-normal) public
open import CSP.Laws.FD.ParallelAssocFail E-≟
  using (StableClass; bothS; termL; termR; Par-stable-classify;
         Par-stable-assoc-LR; Par-stable-assoc-RL) public

-------------------------------------------------------------------------------------
-- §7.  Hide — the one operator whose stability is CONDITIONAL: hiding turns an
--      offered `A`-event into a τ, so `P ∖ A` is stable only if `P` is stable AND
--      offers nothing in `A` (maximal progress).  `hide-stable-noOffA` is the
--      converse of that side condition.
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.HideMonoFD E-≟ using (hide-stable-elim; hide-stable-intro) public
open import CSP.Laws.FSim.HideCong E-≟ using (hide-stable-noOffA) public

-------------------------------------------------------------------------------------
-- §8.  Bind, sequential composition and iteration — stability passes through the
--      continuation layer in both directions (bind adds no τ of its own).
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.SeqDistR E-≟ using (>>-stable; >>-stable-inv) public
open import CSP.Laws.FD.IterateMonoFD E-≟
  using (bind-stable-intro; bind-stable-elim; iter-stable-intro; iter-stable-elim) public

-------------------------------------------------------------------------------------
-- §9.  THE GAPS.  What the survey above did NOT already contain.
--
-- The force- and branch-equations of `□` / `Par` are reused from the trace layer,
-- NOT re-derived; only the stability statements below are new.
-------------------------------------------------------------------------------------

open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; □-mt-tag0-eq; □-mt-tag1-eq; □-τ-tochoice; □-τ-tochoice-R)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (fPar-rr)

-- (9.1) the force equation for a `react|react` external choice.  `ExtChoiceIdem`
-- only had the DIAGONAL case (`double-force-eq`, for `P □ P`); this is the general
-- two-operand version, and it is what the `□` stability intro needs.
□-force-nn : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
             {vP  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcP : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
             {vQ  : (at : AnyTypes E)        → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcQ : (i  : AnyTypes (ExtI E)) → ContinueType i  (Maybe (PTree E (ExtI E) R))}
           → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → PTree.force (P □ Q)
             ≡ react (mergeVis vP vQ) (□-mt (react vP τcP) (react vQ τcQ) P Q)
□-force-nn {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q | eqP | eqQ
... | react _ _ | react _ _ | refl | refl = refl

-- (9.2) STABILITY INTRO for `□` in general.  Only the diagonal `stable-double`
-- (`isStable P → isStable (P □ P)`) existed.  The merged τ-map `□-mt` fires exactly
-- at the two `pair fin` tags — tag0 is `P`'s own τ-map, tag1 is `Q`'s — so both are
-- everywhere `nothing` when the operands are stable, and every other index shape of
-- `□-mt` is `nothing` by definition.
stable-□ : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
         → isStable P → isStable Q → isStable (P □ Q)
stable-□ {P = P} {Q = Q} stP stQ
  with stable→react {t = P} stP | stable→react {t = Q} stQ
... | vP , τcP , eqP , hP | vQ , τcQ , eqQ , hQ =
      mk-stable {t = P □ Q} (□-force-nn {P = P} {Q = Q} eqP eqQ) mt-branch
  where
    -- the merged τ-map is everywhere nothing (tag0 ↦ τcP, tag1 ↦ τcQ, rest ↦ nothing)
    mt-branch : ∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing
    mt-branch (_ , base _)            a = refl
    mt-branch (_ , fin)               a = refl
    mt-branch (_ , pair (base _) _)   a = refl
    mt-branch (_ , pair (pair _ _) _) a = refl
    mt-branch (_ , pair fin i) (lift fzero , a)        rewrite hP (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc fzero) , a) rewrite hQ (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

-- (9.3) STABILITY ELIM for `□`: the converse of (9.2), completing the `iff`.  Every
-- non-`react|react` shape of `P □ Q` carries a τ — two terminated operands give a
-- `ret` (same value) or an internal-choice node (different values); one terminated
-- operand keeps its √ reachable behind a τ (`□-Lret-unstable`/`□-Rret-unstable`); a
-- `sil` operand's own τ is merged in at its tag (`□-τ-tochoice`).  So a stable
-- `P □ Q` forces both operands to be `react` nodes with an empty τ-map.
□-stable-elim : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              → isStable (P □ Q) → isStable P × isStable Q
□-stable-elim {R = R} P Q st = go (PTree.force P) refl (PTree.force Q) refl
  where
    -- both terminated: `ret r` if the values agree, otherwise the `⊓` node — and an
    -- internal choice is never stable (`⊓-unstable`).
    rr : ∀ {r r′ : R} → PTree.force P ≡ ret r → PTree.force Q ≡ ret r′ → ⊥
    rr {r} {r′} eqP eqQ with r ≟ r′
    ... | yes refl = stable-not-ret {t = P □ Q} st (fL-A {P = P} {Q = Q} eqP eqQ)
    ... | no ¬eq   = ⊓-unstable P Q
                       (isStable-force-eq {t = P □ Q} {u = P ⊓ Q}
                                          (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) st)
    -- the nine force shapes; only `react|react` survives
    go : (nP : NodeKind E (ExtI E) R) → PTree.force P ≡ nP
       → (nQ : NodeKind E (ExtI E) R) → PTree.force Q ≡ nQ
       → isStable P × isStable Q
    go (ret r)       eqP (ret r′)      eqQ = ⊥-elim (rr eqP eqQ)
    go (ret r)       eqP (sil Q′)      eqQ =
      ⊥-elim (□-Lret-unstable P Q eqP (subst NonRet (sym eqQ) tt) st)
    go (ret r)       eqP (react _ _)   eqQ =
      ⊥-elim (□-Lret-unstable P Q eqP (subst NonRet (sym eqQ) tt) st)
    go (sil P′)      eqP (ret r′)      eqQ =
      ⊥-elim (□-Rret-unstable P Q (subst NonRet (sym eqP) tt) eqQ st)
    go (sil P′)      eqP (sil Q′)      eqQ =
      ⊥-elim (stable-no-τ st (□-τ-tochoice P Q (sSil eqP) eqQ tt))
    go (sil P′)      eqP (react _ _)   eqQ =
      ⊥-elim (stable-no-τ st (□-τ-tochoice P Q (sSil eqP) eqQ tt))
    go (react _ _)   eqP (ret r′)      eqQ =
      ⊥-elim (□-Rret-unstable P Q (subst NonRet (sym eqP) tt) eqQ st)
    go (react _ _)   eqP (sil Q′)      eqQ =
      ⊥-elim (stable-no-τ st (□-τ-tochoice-R P Q (sSil eqQ) eqP tt))
    go (react vP τcP) eqP (react vQ τcQ) eqQ =
        mk-stable {t = P} eqP hP , mk-stable {t = Q} eqQ hQ
      where
        -- the composite's τ-map, read off its known `react` force
        mtn : ∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing
        mtn = stable-react-τc {t = P □ Q} st (□-force-nn {P = P} {Q = Q} eqP eqQ)
        -- tag0 of that map IS `P`'s τ-map, so `P`'s is everywhere nothing …
        hP : ∀ i a → τcP i a ≡ nothing
        hP (B , i) a with τcP (B , i) a in tp
        ... | nothing = refl
        ... | just P₁ = case trans (sym (□-mt-tag0-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                      {P = P} {Q = Q} {iₚ = B , i} {aₚ = a}
                                                      {P₁ = P₁} tp))
                                   (mtn ((Lift ℓ (Fin 2) × B) , pair fin i) (lift fzero , a))
                        of λ ()
        -- … and tag1 is `Q`'s
        hQ : ∀ i a → τcQ i a ≡ nothing
        hQ (B , i) a with τcQ (B , i) a in tq
        ... | nothing = refl
        ... | just Q₁ = case trans (sym (□-mt-tag1-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                      {P = P} {Q = Q} {iₚ = B , i} {aₚ = a}
                                                      {Q₁ = Q₁} tq))
                                   (mtn ((Lift ℓ (Fin 2) × B) , pair fin i)
                                        (lift (fsuc fzero) , a))
                        of λ ()

-- (9.4) DECIDING stability of a parallel composite.  `Par-stable` / `-termL` / `-termR`
-- (intro) and `Par-stable-normal` (elim) together already form an IFF, but nobody had
-- packaged them as a DECISION: given the operands' stability decided, the composite's
-- is too.  The `ret` and `sil` shapes need no input at all — a terminated operand
-- contributes no τ, and a silent one contributes one unconditionally.
Par-stable? : ∀ {ℓr} {R₁ R₂ R : Set ℓr} (As : EventSet) (merge : Mg R₁ R₂ R)
              (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
            → Dec (isStable P) → Dec (isStable Q)
            → Dec (isStable (Par As merge P Q))
Par-stable? As merge P Q dP dQ = go dP dQ (PTree.force P) refl (PTree.force Q) refl
  where
    -- a `sil` operand's τ is mirrored by the composite, whichever side it is on
    silL : ∀ {P′} → PTree.force P ≡ sil P′ → ¬ isStable (Par As merge P Q)
    silL eqP st = stable-no-τ st (Par-τ-L As merge P Q (sSil eqP))
    silR : ∀ {Q′} → PTree.force Q ≡ sil Q′ → ¬ isStable (Par As merge P Q)
    silR eqQ st = stable-no-τ st (Par-τ-R As merge P Q (sSil eqQ))
    -- the nine force shapes
    go : Dec (isStable P) → Dec (isStable Q)
       → (nP : NodeKind E (ExtI E) _) → PTree.force P ≡ nP
       → (nQ : NodeKind E (ExtI E) _) → PTree.force Q ≡ nQ
       → Dec (isStable (Par As merge P Q))
    -- both terminated ⇒ the composite terminates too, and `ret` is never stable
    go _ _ (ret r₁)  eqP (ret r₂)     eqQ =
      no (λ st → stable-not-ret {t = Par As merge P Q} st (fPar-rr As merge eqP eqQ))
    go _ _ (ret r₁)  eqP (sil Q′)     eqQ = no (silR eqQ)
    go _ _ (sil P′)  eqP _            eqQ = no (silL eqP)
    go _ _ (react _ _) eqP (sil Q′)   eqQ = no (silR eqQ)
    -- one side terminated: the composite is stable exactly when the LIVE side is
    go _ dQ′ (ret r₁)  eqP (react _ _)  eqQ with dQ′
    ... | yes stQ = yes (Par-stable-termL As merge P Q eqP stQ)
    ... | no ¬stQ = no (λ st → ¬stQ (liveQ (Par-stable-normal As merge P Q st)))
      where
        -- every normal form of a stable composite whose left side is `ret` gives `Q` stable
        liveQ : ParNormal P Q → isStable Q
        liveQ (inj₁ (stP , stQ))              = stQ
        liveQ (inj₂ (inj₁ (_ , _ , stQ)))     = stQ
        liveQ (inj₂ (inj₂ (stP , _ , _)))     = ⊥-elim (stable-not-ret {t = P} stP eqP)
    go dP′ _ (react _ _) eqP (ret r₂)   eqQ with dP′
    ... | yes stP = yes (Par-stable-termR As merge P Q stP eqQ)
    ... | no ¬stP = no (λ st → ¬stP (liveP (Par-stable-normal As merge P Q st)))
      where
        -- mirror: a stable composite whose right side is `ret` gives `P` stable
        liveP : ParNormal P Q → isStable P
        liveP (inj₁ (stP , stQ))              = stP
        liveP (inj₂ (inj₁ (_ , _ , stQ)))     = ⊥-elim (stable-not-ret {t = Q} stQ eqQ)
        liveP (inj₂ (inj₂ (stP , _ , _)))     = stP
    -- both live: stable iff BOTH operands are
    go dP′ dQ′ (react _ _) eqP (react _ _) eqQ with dP′ | dQ′
    ... | yes stP | yes stQ = yes (Par-stable As merge P Q stP stQ)
    ... | no ¬stP | _       = no (λ st → ¬stP (bothP (Par-stable-normal As merge P Q st)))
      where
        -- with both operands `react`, the only reachable normal form is `both stable`
        bothP : ParNormal P Q → isStable P
        bothP (inj₁ (stP , _))            = stP
        bothP (inj₂ (inj₁ (_ , eqr , _))) = case trans (sym eqP) eqr of λ ()
        bothP (inj₂ (inj₂ (stP , _ , _))) = stP
    ... | yes stP | no ¬stQ = no (λ st → ¬stQ (bothQ (Par-stable-normal As merge P Q st)))
      where
        bothQ : ParNormal P Q → isStable Q
        bothQ (inj₁ (_ , stQ))            = stQ
        bothQ (inj₂ (inj₁ (_ , _ , stQ))) = stQ
        bothQ (inj₂ (inj₂ (_ , _ , eqr))) = case trans (sym eqQ) eqr of λ ()
