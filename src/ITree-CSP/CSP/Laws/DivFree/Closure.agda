{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Compositional divergence-freedom, step 1: the STRUCTURAL operator cases —
-- those where every τ of the composite is (or immediately becomes) a τ of an
-- operand, so no fairness / König argument is needed.
--
-- PRIMARY FORM: `τ-Acc` (τ-accessibility, `Semantics.DivergenceFree`), not
-- `¬ Diverges`.  Reason — the negative form is NOT constructively closed under
-- the operators.  To derive `¬ Diverges (P □ Q)` from `¬ Diverges P` and
-- `¬ Diverges Q` you must turn a divergence of `P □ Q` into a divergence of one
-- operand, which means deciding WHICH operand contributes infinitely many of the
-- τ's — a classical (König / pigeonhole) step.  `τ-Acc` is inductive, so the
-- same closure is a plain structural recursion on the operands' accessibility
-- proofs, with no classical input at all.  `τ-Acc→¬Div` then delivers the
-- `¬ Diverges` that `DRFromRel`'s `ndivL`/`ndivR` and `FSimFromRel`'s `ndivL`
-- actually ask for, and every lemma below has such a `*-no-Diverges` corollary.
--
-- DONE here:
--   * leaves            `Stop`, `deadlock`, `Ret`/`Skip`, `Tau`
--   * prefixes          `e ⟶ P`, `e ⟶₀ P`, `e ! v ⟶ P`, `pchoice v`
--   * internal choice   `P ⊓ Q`, `⨅Fin`
--   * slide / timeout   `P ▷ Q`          (needed by `□`, whose τ's slide)
--   * external choice   `P □ Q`
--   * parallel          `Par A merge P Q`, `_∥⇘_⇙_`, `_⦀_`, `⦀Fin`
--   * bind              `P >>= k`, `P >> Q`
--
-- NOT here (deliberately):
--   * HIDE `P ∖ A` — already done, and genuinely conditional: hiding CREATES
--     τ's, so it needs a certificate that the hidden set is not offered forever.
--     See `MAcc A P → ¬ Diverges (P ∖ A)` in `CSP.Laws.FD.HideDivergence`
--     (`MAcc` is that certificate).
--   * LOOP / ITERATE — also genuinely conditional.  `loop0 Skip` diverges: the
--     body returns immediately and the loop re-enters by a τ, so the τ-cycle is
--     visibly unguarded.  The missing hypothesis is CSP's "the body is guarded"
--     (performs a visible event before returning); note that Agda's productivity
--     check does NOT supply it — `div = sil div` is perfectly productive and
--     maximally divergent.  Intended shape for a later commit:
--         `Guarded B → τ-Acc B → τ-Acc (loop0 B)`
--     with `Guarded` ruling out a `ret` reachable by τ's alone.
--
-- No `postulate`, no `NON_TERMINATING`, no sized types, no `dne`/`Classical`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.DivFree.Closure {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟

-- `Diverges` is hidden from `LTS` because `Semantics.DivergenceFree` re-exports
-- the very same one (via `DRBisim`); importing both unqualified would clash.
open import Semantics.LTS {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DivergenceFree {E = E} {I = ExtI E}

-- per-operator τ-step INVERSIONS, reused rather than re-derived
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; □-τ-elim; □τR; cP; cQ; sPQ; sQP; chP; chQ)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (Par-τ-elim; ParτR; τL; τR)
open import CSP.Laws.Traces.TraceLawsBind E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindT-elim)

private
  variable
    ℓr ℓs ℓ₁ ℓ₂ : Level
    R  : Set ℓr
    S  : Set ℓs
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    A  : Set ℓ

-------------------------------------------------------------------------------------
-- §1.  Leaves — nodes with no τ at all (all discharged by `stable→τ-Acc`, whose
--      `isStable` obligation reduces to `λ _ _ → refl` because each of these
--      forces to `react _ ∅t`).
-------------------------------------------------------------------------------------

-- `Stop = react ∅v ∅t` is stable, hence τ-accessible
τ-Acc-Stop : τ-Acc (Stop {R = R})
τ-Acc-Stop = stable→τ-Acc (λ _ _ → refl)

-- … and therefore cannot diverge
Stop-no-Diverges : ¬ Diverges (Stop {R = R})
Stop-no-Diverges = τ-Acc→¬Div τ-Acc-Stop

-- `deadlock` (the generic empty react node) is stable
τ-Acc-deadlock : τ-Acc (deadlock {E = E} {I = ExtI E} {R = R})
τ-Acc-deadlock = stable→τ-Acc (λ _ _ → refl)

-- `Ret r` forces to `ret r`: no τ (it offers √, which is not a τ)
τ-Acc-Ret : (r : R) → τ-Acc (Ret r)
τ-Acc-Ret r = ret→τ-Acc refl

-- Skip = Ret tt
τ-Acc-Skip : ∀ {ℓx : Level} → τ-Acc (Skip {ℓx})
τ-Acc-Skip = τ-Acc-Ret tt

-- `Skip` cannot diverge
Skip-no-Diverges : ∀ {ℓx : Level} → ¬ Diverges (Skip {ℓx})
Skip-no-Diverges = τ-Acc→¬Div τ-Acc-Skip

-- `Tau P = sil P`: the one τ lands on `P`
τ-Acc-Tau : {P : PTree E (ExtI E) R} → τ-Acc P → τ-Acc (Tau P)
τ-Acc-Tau ap = sil→τ-Acc refl ap

-------------------------------------------------------------------------------------
-- §2.  Prefixes — `force = react _ ∅t`, so again stable.
-------------------------------------------------------------------------------------

-- the general stable visible menu `pchoice v` (the shape all prefixes share)
τ-Acc-pchoice : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
              → τ-Acc (pchoice v)
τ-Acc-pchoice v = stable→τ-Acc (λ _ _ → refl)

-- a visible menu never diverges (generalises `pchoice-no-Diverges` of `InterruptFD`)
pchoice-no-Diverges : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                    → ¬ Diverges (pchoice v)
pchoice-no-Diverges v = τ-Acc→¬Div (τ-Acc-pchoice v)

-- prefix `e ⟶ P`
τ-Acc-⟶ : (e : E A) (P : A → PTree E (ExtI E) R) → τ-Acc (e ⟶ P)
τ-Acc-⟶ e P = stable→τ-Acc (λ _ _ → refl)

-- the prefix can never diverge (the CANONICAL `prefix-no-Diverges`: it used to be
-- duplicated in `CSP.Laws.FD.InterruptFD` and `CSP.Laws.FD.ExtChoiceSlide`)
prefix-no-Diverges : (e : E A) (P : A → PTree E (ExtI E) R) → ¬ Diverges (e ⟶ P)
prefix-no-Diverges e P = τ-Acc→¬Div (τ-Acc-⟶ e P)

-- constant prefix `e ⟶₀ P` (= `Prefix e (λ _ → P)`)
τ-Acc-⟶₀ : (e : E A) (P : PTree E (ExtI E) R) → τ-Acc (e ⟶₀ P)
τ-Acc-⟶₀ e P = τ-Acc-⟶ e (λ _ → P)

-- output `e ! v ⟶ P`
τ-Acc-Output : ⦃ _ : DecEq A ⦄ (e : E A) (v : A) (P : PTree E (ExtI E) R)
             → τ-Acc (Output e v P)
τ-Acc-Output e v P = stable→τ-Acc (λ _ _ → refl)

-------------------------------------------------------------------------------------
-- §3.  Internal choice — `force (P ⊓ Q) = react ∅v (br2 P Q)`: the two τ's land
--      exactly on `P` and on `Q` (`⊓-τ-inv`), so no recursion is needed.
-------------------------------------------------------------------------------------

-- internal choice: both τ-successors are the operands themselves
τ-Acc-⊓ : {P Q : PTree E (ExtI E) R} → τ-Acc P → τ-Acc Q → τ-Acc (P ⊓ Q)
τ-Acc-⊓ {P = P} {Q = Q} ap aq = acc go
  where
    -- every τ out of `P ⊓ Q` is the left or the right branch
    go : ∀ {M} → (P ⊓ Q) ─[ τ ]─► M → τ-Acc M
    go st with ⊓-τ-inv P Q st
    ... | inj₁ refl = ap
    ... | inj₂ refl = aq

-- `¬ Diverges` corollary for internal choice.  `⊓` is the ONE operator whose
-- closure also holds in the purely NEGATIVE form: its τ-successors are literally
-- the operands, so a divergence of `P ⊓ Q` is a divergence of `P` or of `Q`
-- after one step — no fairness argument, hence no classical input.
⊓-no-Diverges : {P Q : PTree E (ExtI E) R}
              → ¬ Diverges P → ¬ Diverges Q → ¬ Diverges (P ⊓ Q)
⊓-no-Diverges {P = P} {Q = Q} np nq d with ⊓-τ-inv P Q (d .Diverges.step)
... | inj₁ eq = np (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = nq (subst Diverges eq (d .Diverges.rest))

-- replicated internal choice over `Fin (suc n)` (a right-nested fold of `⊓`)
τ-Acc-⨅Fin : (n : ℕ) (f : Fin (suc n) → PTree E (ExtI E) R)
           → (∀ i → τ-Acc (f i)) → τ-Acc (⨅Fin n f)
τ-Acc-⨅Fin zero    f af = af fzero
τ-Acc-⨅Fin (suc n) f af =
  τ-Acc-⊓ (af fzero) (τ-Acc-⨅Fin n (λ i → f (fsuc i)) (λ i → af (fsuc i)))

-------------------------------------------------------------------------------------
-- §4.  Slide / timeout — a τ of `P ▷ Q` is the timeout (→ `Q`) or a τ of `P`
--      sliding on (→ `P′ ▷ Q`).  Structural recursion on `P`'s accessibility.
-------------------------------------------------------------------------------------

-- sliding choice: recurse on the LEFT accessibility (`Q` is only ever reached whole)
τ-Acc-▷ : {P Q : PTree E (ExtI E) R} → τ-Acc P → τ-Acc Q → τ-Acc (P ▷ Q)
τ-Acc-▷ {P = P} {Q = Q} (acc f) aq = acc go
  where
    -- timeout lands on Q; P's own τ slides on as (P′ ▷ Q)
    go : ∀ {M} → (P ▷ Q) ─[ τ ]─► M → τ-Acc M
    go st with ▷-τ-elim P Q st
    ... | inj₁ refl              = aq
    ... | inj₂ (P′ , pτ , refl)  = τ-Acc-▷ (f pτ) aq

-- `¬ Diverges` corollary for the slide
▷-no-Diverges : {P Q : PTree E (ExtI E) R}
              → τ-Acc P → τ-Acc Q → ¬ Diverges (P ▷ Q)
▷-no-Diverges ap aq = τ-Acc→¬Div (τ-Acc-▷ ap aq)

-------------------------------------------------------------------------------------
-- §5.  External choice — SIX τ shapes (`□-τ-elim`): commit to an operand, slide
--      into a `▷`, or keep choosing.  Note this is why `▷` had to come first:
--      `P □ Q` genuinely steps into slide states.  Lexicographic recursion (the
--      `chQ` case keeps the left certificate and shrinks the right one).
-------------------------------------------------------------------------------------

-- external choice: closed under both operands being τ-accessible
τ-Acc-□ : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
        → τ-Acc P → τ-Acc Q → τ-Acc (P □ Q)
τ-Acc-□ {P = P} {Q = Q} (acc f) (acc g) = acc go
  where
    -- commit (cP/cQ), slide (sPQ/sQP) or choose on (chP/chQ)
    go : ∀ {M} → (P □ Q) ─[ τ ]─► M → τ-Acc M
    go st with □-τ-elim P Q st
    ... | cP refl           = acc f
    ... | cQ refl           = acc g
    ... | sPQ P′ pτ refl    = τ-Acc-▷ (f pτ) (acc g)
    ... | sQP Q′ qτ refl    = τ-Acc-▷ (g qτ) (acc f)
    ... | chP P′ pτ refl    = τ-Acc-□ (f pτ) (acc g)
    ... | chQ Q′ qτ refl    = τ-Acc-□ (acc f) (g qτ)

-- `¬ Diverges` corollary for external choice
□-no-Diverges : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
              → τ-Acc P → τ-Acc Q → ¬ Diverges (P □ Q)
□-no-Diverges ap aq = τ-Acc→¬Div (τ-Acc-□ ap aq)

-------------------------------------------------------------------------------------
-- §6.  Parallel — a τ of `Par A merge P Q` is a τ of exactly one operand, the
--      other being carried along unchanged (`Par-τ-elim`).  Lexicographic again.
-------------------------------------------------------------------------------------

-- generalised parallel: τ-accessible whenever both operands are
τ-Acc-Par : (As : EventSet) (merge : Mg R₁ R₂ R)
            {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
          → τ-Acc P → τ-Acc Q → τ-Acc (Par As merge P Q)
τ-Acc-Par As merge {P = P} {Q = Q} (acc f) (acc g) = acc go
  where
    -- the τ belongs to P (→ Par P′ Q) or to Q (→ Par P Q′)
    go : ∀ {M} → (Par As merge P Q) ─[ τ ]─► M → τ-Acc M
    go st with Par-τ-elim As merge P Q st
    ... | τL P′ pτ refl = τ-Acc-Par As merge (f pτ) (acc g)
    ... | τR Q′ qτ refl = τ-Acc-Par As merge (acc f) (g qτ)

-- `¬ Diverges` corollary for generalised parallel
Par-no-Diverges : (As : EventSet) (merge : Mg R₁ R₂ R)
                  {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
                → τ-Acc P → τ-Acc Q → ¬ Diverges (Par As merge P Q)
Par-no-Diverges As merge ap aq = τ-Acc→¬Div (τ-Acc-Par As merge ap aq)

-- CSP alphabetised parallel `P ∥⇘ A ⇙ Q`
τ-Acc-∥ : ∀ {ℓx : Level} {P Q : PTree E (ExtI E) (⊤ {ℓx})} (As : EventSet)
        → τ-Acc P → τ-Acc Q → τ-Acc (P ∥⇘ As ⇙ Q)
τ-Acc-∥ As ap aq = τ-Acc-Par As (λ _ _ → tt) ap aq

-- interleaving `P ⦀ Q` (parallel with an empty synchronisation set)
τ-Acc-⦀ : ∀ {ℓx : Level} {P Q : PTree E (ExtI E) (⊤ {ℓx})}
        → τ-Acc P → τ-Acc Q → τ-Acc (P ⦀ Q)
τ-Acc-⦀ ap aq = τ-Acc-Par ∅ES (λ _ _ → tt) ap aq

-- replicated interleaving over `Fin n` (empty case is `Skip`)
τ-Acc-⦀Fin : ∀ {ℓx : Level} (n : ℕ) (f : Fin n → PTree E (ExtI E) (⊤ {ℓx}))
           → (∀ i → τ-Acc (f i)) → τ-Acc (⦀Fin n f)
τ-Acc-⦀Fin zero    f af = τ-Acc-Skip
τ-Acc-⦀Fin (suc n) f af =
  τ-Acc-⦀ (af fzero) (τ-Acc-⦀Fin n (λ i → f (fsuc i)) (λ i → af (fsuc i)))

-------------------------------------------------------------------------------------
-- §7.  Bind — the τ-inversion is not in the trace laws yet, so it is derived here
--      from the three force equations.  Note bind inserts NO τ of its own: when
--      `P` returns, `force (P >>= k) ≡ force (k r)` literally, so the composite's
--      τ's are P's τ's (lifted) followed by those of the continuation.
-------------------------------------------------------------------------------------

-- inversion result for a τ out of `P >>= k`
data BindτR {ℓr ℓs} {R : Set ℓr} {S : Set ℓs}
            (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
            (M : PTree E (ExtI E) S) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr ⊔ ℓs) where
  bτL : (c : PTree E (ExtI E) R) → P ─[ τ ]─► c → M ≡ c >>= k → BindτR k P M
  bτK : (r : R) → PTree.force P ≡ ret r → (k r) ─[ τ ]─► M     → BindτR k P M

-- a τ of `P >>= k` is a τ of `P` (lifted) or, once `P` has returned, a τ of `k r`
bind-τ-elim : (k : R → PTree E (ExtI E) S) (P : PTree E (ExtI E) R)
              {M : PTree E (ExtI E) S}
            → (P >>= k) ─[ τ ]─► M → BindτR k P M
bind-τ-elim k P st with PTree.force P in eqP
... | ret r  = bτK r eqP (τ-step-transport (fBind-ret k P eqP) st)
... | sil c  = go st
  where
    -- the composite forces to `sil (c >>= k)`, so the τ is that single step
    go : ∀ {M} → (P >>= k) ─[ τ ]─► M → BindτR k P M
    go (sSil sileq) with trans (sym sileq) (fBind-sil k P eqP)
    ... | refl = bτL c (sSil eqP) refl
    go (sTau req _) with trans (sym req) (fBind-sil k P eqP)
    ... | ()
... | react v τc = go st
  where
    -- the composite's τ-part is `bindT k (react v τc)`; `bindT-elim` peels it
    go : ∀ {M} → (P >>= k) ─[ τ ]─► M → BindτR k P M
    go (sSil sileq) with trans (sym sileq) (fBind-react k P eqP)
    ... | ()
    go (sTau {i = i} {a = a} req br)
      with trans (sym req) (fBind-react k P eqP)
    ... | refl with bindT-elim k (react v τc) {i = i} {a = a} br
    ...   | c , veq , refl = bτL c (sTau eqP veq) refl

-- bind: τ-accessible when `P` is and every continuation `k r` is
τ-Acc->>= : {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
          → τ-Acc P → (∀ r → τ-Acc (k r)) → τ-Acc (P >>= k)
τ-Acc->>= {P = P} {k = k} (acc f) ak = acc go
  where
    -- P's τ lifts through the bind; after P returns we are inside `k r`
    go : ∀ {M} → (P >>= k) ─[ τ ]─► M → τ-Acc M
    go st with bind-τ-elim k P st
    ... | bτL c pτ refl  = τ-Acc->>= (f pτ) ak
    ... | bτK r _ kτ     = accSub (ak r) kτ

-- `¬ Diverges` corollary for bind
>>=-no-Diverges : {P : PTree E (ExtI E) R} {k : R → PTree E (ExtI E) S}
                → τ-Acc P → (∀ r → τ-Acc (k r)) → ¬ Diverges (P >>= k)
>>=-no-Diverges ap ak = τ-Acc→¬Div (τ-Acc->>= ap ak)

-- sequential composition `P >> Q` (= `P >>= λ _ → Q`)
τ-Acc->> : {P : PTree E (ExtI E) R} {Q : PTree E (ExtI E) S}
         → τ-Acc P → τ-Acc Q → τ-Acc (P >> Q)
τ-Acc->> ap aq = τ-Acc->>= ap (λ _ → aq)

-- `¬ Diverges` corollary for sequential composition
>>-no-Diverges : {P : PTree E (ExtI E) R} {Q : PTree E (ExtI E) S}
               → τ-Acc P → τ-Acc Q → ¬ Diverges (P >> Q)
>>-no-Diverges ap aq = τ-Acc→¬Div (τ-Acc->> ap aq)
