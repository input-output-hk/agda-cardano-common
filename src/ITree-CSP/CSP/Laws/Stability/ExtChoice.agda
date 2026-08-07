{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- STABILITY OF EXTERNAL CHOICE — the `□` half of the stability layer, split out
-- of `CSP.Laws.Stability.Closure` so that it can be imported CHEAPLY.
--
-- WHY THIS MODULE EXISTS.  `CSP.Laws.Stability.Closure` is a SURVEY: it gathers the
-- stability lemmas of every CSP operator, so its import closure is the union of the
-- FD modules that own them — TEN postulate-bearing modules, including the
-- `Par`/hide/iterate divergence layers and `Semantics.DRImpliesFD`.  A client that
-- only wants the two `□` facts (`CSP.Laws.FSim.ExtChoiceCong` is exactly such a
-- client) paid for all ten.  The `□` lemmas' OWN dependencies are far smaller:
--
--   `Semantics.Stability`                  — postulate-free by design
--   `CSP.Laws.Traces.TraceLawsExtChoice`   — postulate-free
--   `CSP.Laws.FD.FDLawsIChoiceAssoc`       — postulate-free (`⊓-unstable`)
--   `CSP.Laws.FD.ExtChoiceFD`              — carries ONE, via `ExtChoiceDivergence`
--
-- so this module's closure has exactly ONE postulate-bearing module,
-- `CSP.Laws.FD.ExtChoiceDivergence` (its two classical `Diverges→` inversions, both
-- certified from the single `dne` of `CSP.Laws.ClassicalFromLEM`).  That module is
-- unavoidable here — `□-Lret-unstable`/`□-Rret-unstable` live in `ExtChoiceFD`,
-- which imports it — but it is also already a DIRECT import of the `□` FSim
-- congruence, so for that client the borrow is now free.
--
-- Nothing below is new or re-proved: the three definitions are moved VERBATIM from
-- §9.1–§9.3 of `CSP.Laws.Stability.Closure`, which re-exports them `public` so every
-- existing client keeps working unchanged.  Their original `(9.n)` labels are kept
-- so the survey's contents list still reads across.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types in this file.
------------------------------------------------------------------------

open import Level using (Level; Lift; lift)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Stability.ExtChoice {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the generic stability core (`isStable`, `mk-stable`, `stable→react`,
-- `stable-react-τc`, `stable-not-ret`, `stable-no-τ`, `isStable-force-eq`)
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Stability {E = E} {I = ExtI E}

-- the `□` force- and branch-equations, reused from the trace layer, NOT re-derived
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; □-mt-tag0-eq; □-mt-tag1-eq; □-τ-tochoice; □-τ-tochoice-R)

-- an internal choice is never stable (its left τ-branch always fires)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟ using (⊓-unstable)

-- the `□` shapes with one terminated operand keep a √ behind a τ, so are unstable
open import CSP.Laws.FD.ExtChoiceFD E-≟ using (□-Lret-unstable; □-Rret-unstable)

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
