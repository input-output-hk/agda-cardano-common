{-# OPTIONS --guardedness #-}

-- CERTIFICATION ONLY — DO NOT USE THIS MODULE IN PROOFS.
--
-- This module exists solely to CERTIFY that the classical postulates of the FD
-- layer are derivable from a single double-negation-elimination axiom `dne`
-- (equivalently LEM) — i.e. that they are "just classical logic", not ad-hoc.
--
--   Postulate 1  ¬-divergent→normal   (convergence ⇒ reachable τ-normal-form)
--   Postulate 2  □-Diverges→          (the König step)
--   Postulate 3  △-Diverges→          (the interrupt König step)
--   Postulate 4  >>-Diverges→         (the bind König step)
--   Postulate 5  Par-Diverges→        (the parallel König step)
--   Postulate 6  loop-Diverges→       (the iterate / loop König step)
--   Postulate 7  offer-LEM            (decidability of an offer — a plain LEM instance)
--   Postulate 8  modA-transfer        (the hiding-divergence transfer across ≈DR)
--   Postulate 9  Hide-Diverges→       (¬DivModAC→MAccC — the hiding-divergence König step)
--
-- IMPORTANT:
--   * Nothing in the development imports this module, and NOTHING SHOULD.  Importing
--     it would leak the strong `dne` axiom into the FD layer, making the WHOLE layer
--     classical and defeating the point of the small, targeted postulates.
--   * The development uses the postulates DIRECTLY instead:
--       - `¬-divergent→normal` from Semantics.DRImpliesFD
--       - `□-Diverges→`        from CSP.Laws.FD.ExtChoiceDivergence
--       - `△-Diverges→`        from CSP.Laws.FD.InterruptDivergence
--       - `>>-Diverges→`       from CSP.Laws.FD.SeqDistR
--       - `Par-Diverges→`      from CSP.Laws.FD.ParallelDivergence
--       - `loop-Diverges→`     from CSP.Laws.FD.IterateFD
--       - `offer-LEM`          from CSP.Laws.FD.ParallelRefusals
--       - `modA-transfer`      from CSP.Laws.Bisim.DRCongruence
--       - `Hide-Diverges→`     from CSP.Laws.FD.HideDivergence
--   * So this file is a standalone soundness witness, kept green but never depended on.
--     Treat the names below (`¬-divergent→normal`, `□-Diverges→`, `△-Diverges→`,
--     `>>-Diverges→`, `Par-Diverges→`, `offer-LEM`, `dne`, helpers) as off-limits for any
--     actual law; use the direct postulates above.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq)

open import Process_Trees
open import Classical using (dne)

module CSP.Laws.ClassicalFromLEM {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators  E-≟
open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
open import Semantics.DRBisim   {E = E} {I = ExtI E}
  using (Diverges; DRbisim; _≈DR_)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□τR; cP; cQ; sPQ; sQP; chP; chQ; □-τ-elim; ▷-τ-elim)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (△τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim)
open import CSP.Laws.Bisim.IterCong  E-≟
  using (sil-τ-inv; react-τ-inv; fIter-r1; fIter-r2; fIter-sil; fIter-react; iterT-elim)
open import CSP.Laws.Bisim.LoopCong  E-≟ using (fBind-ret; fBind-sil; fBind-react; bindT-elim)
open import Semantics.Refusals  {E = E} {I = ExtI E} using (Offers)
open import CSP.Laws.Traces.TraceLawsParallel     E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟ using (Par-τ-elim; τL; τR)

private
  variable
    ℓr ℓs ℓ₁ ℓ₂ : Level
    R : Set ℓr
    S : Set ℓs
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂

-- THE single classical axiom — now shared from the common `Classical`
-- module (imported above). `((A → ⊥) → ⊥) → A` is definitionally `¬ ¬ A → A`,
-- so every `dne` use below is unchanged.

-------------------------------------------------------------------------------------
-- Derivation 1:  ¬-divergent→normal  from  dne.
-- A τ-normal-form is a state that is stable or terminated (ret).
-------------------------------------------------------------------------------------

Normal : PTree E (ExtI E) R → Set _
Normal {R = R} t = isStable t ⊎ Σ[ r ∈ R ] (PTree.force t ≡ ret r)

-- a non-normal state has an enabled τ (the react case uses dne to turn ¬∀ into ∃).
-- `with force t in eqf` abstracts force t inside `¬ Normal t`, so in the react branch
-- the `isStable` component has already reduced to `∀ i a → τc i a ≡ nothing`.
not-normal→τ : (t : PTree E (ExtI E) R) → ¬ Normal t → Σ[ t′ ∈ PTree E (ExtI E) R ] (t ─[ τ ]─► t′)
not-normal→τ t ¬nm with PTree.force t in eqf
... | ret r     = ⊥-elim (¬nm (inj₂ (r , refl)))
... | sil c     = c , sSil eqf
... | react v τc = dne (λ k → ¬nm (inj₁ (no-step k)))
  where
    no-step : ¬ (Σ[ t′ ∈ _ ] (t ─[ τ ]─► t′)) → ∀ i a → τc i a ≡ nothing
    no-step k i a with τc i a in eq
    ... | nothing = refl
    ... | just t′ = ⊥-elim (k (t′ , sTau eqf eq))

-- append a single τ to a τ*-run
τ*-snoc : {t s s′ : PTree E (ExtI E) R} → t ─[τ*]─► s → s ─[ τ ]─► s′ → t ─[τ*]─► s′
τ*-snoc p step = τ*-trans p (τ*-step step τ*-refl)

-- if NO reachable state from t is normal, then t diverges (corecursively follow the
-- enabled τ that every reachable non-normal state has)
build-div : (t : PTree E (ExtI E) R)
          → ¬ (Σ[ t′ ∈ PTree E (ExtI E) R ] (t ─[τ*]─► t′ × Normal t′))
          → (s : PTree E (ExtI E) R) → t ─[τ*]─► s → Diverges s
build-div t nrn s path .Diverges.next =
  proj₁ (not-normal→τ s (λ nm → nrn (s , path , nm)))
build-div t nrn s path .Diverges.step =
  proj₂ (not-normal→τ s (λ nm → nrn (s , path , nm)))
build-div t nrn s path .Diverges.rest =
  build-div t nrn (proj₁ (not-normal→τ s (λ nm → nrn (s , path , nm))))
                  (τ*-snoc path (proj₂ (not-normal→τ s (λ nm → nrn (s , path , nm)))))

¬-divergent→normal : (t : PTree E (ExtI E) R)
                   → ¬ Diverges t
                   → Σ[ t′ ∈ PTree E (ExtI E) R ] (t ─[τ*]─► t′ × Normal t′)
¬-divergent→normal t nd = dne (λ nrn → nd (build-div t nrn t τ*-refl))

-------------------------------------------------------------------------------------
-- Derivation 2:  □-Diverges→ (the König step) from dne.
-- Route: dne turns ¬ Diverges into ACCESSIBILITY of the τ-relation; then a
-- well-founded recursion (not coinduction) shows P □ Q cannot diverge when both
-- P and Q are accessible.  No infinite-pigeonhole choice is taken — the side is
-- decided structurally, one τ-step at a time, against a well-founded measure.
-------------------------------------------------------------------------------------

-- accessibility of the τ-relation (own copy, to control the constructor's arity)
data DAcc {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  dacc : (∀ {t′} → t ─[ τ ]─► t′ → DAcc t′) → DAcc t

accSub : {t t′ : PTree E (ExtI E) R} → DAcc t → t ─[ τ ]─► t′ → DAcc t′
accSub (dacc rs) step = rs step

-- an accessible state cannot diverge (well-founded recursion on the DAcc proof)
DAcc→¬Div : {t : PTree E (ExtI E) R} → DAcc t → ¬ Diverges t
DAcc→¬Div (dacc rs) d = DAcc→¬Div (rs (d .Diverges.step)) (d .Diverges.rest)

-- a non-accessible state has a τ-successor that is also non-accessible (via dne)
nonAcc→step : {t : PTree E (ExtI E) R}
            → ¬ DAcc t → Σ[ t′ ∈ PTree E (ExtI E) R ] ((t ─[ τ ]─► t′) × ¬ DAcc t′)
nonAcc→step nAcc = dne (λ k → nAcc (dacc (λ step → dne (λ na → k (_ , step , na)))))

-- …so a non-accessible state diverges (corecursively follow the non-accessible chain)
nonAcc→Div : {t : PTree E (ExtI E) R} → ¬ DAcc t → Diverges t
nonAcc→Div nAcc .Diverges.next = proj₁ (nonAcc→step nAcc)
nonAcc→Div nAcc .Diverges.step = proj₁ (proj₂ (nonAcc→step nAcc))
nonAcc→Div nAcc .Diverges.rest = nonAcc→Div (proj₂ (proj₂ (nonAcc→step nAcc)))

¬Div→DAcc : {t : PTree E (ExtI E) R} → ¬ Diverges t → DAcc t
¬Div→DAcc nd = dne (λ nAcc → nd (nonAcc→Div nAcc))

-- P ▷ Q can't diverge if P and Q are accessible (recursion on P's DAcc; the timeout
-- branch goes to Q and is killed by Q's accessibility)
▷-no-inf : {A B : PTree E (ExtI E) R}
         → DAcc A → DAcc B → ¬ Diverges (A ▷ B)
▷-no-inf {A = A} {B = B} (dacc rsA) aB d with ▷-τ-elim A B (d .Diverges.step)
... | inj₁ m≡B            = DAcc→¬Div aB (subst Diverges m≡B (d .Diverges.rest))
... | inj₂ (A' , Aτ , m≡) = ▷-no-inf (rsA Aτ) aB (subst Diverges m≡ (d .Diverges.rest))

-- P □ Q can't diverge if P and Q are accessible (recursion on (DAcc P, DAcc Q); the
-- commit branches go to a bare operand, the slide branches hand off to ▷-no-inf)
□-no-inf : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
         → DAcc P → DAcc Q → ¬ Diverges (P □ Q)
□-no-inf {P = P} {Q = Q} (dacc rsP) (dacc rsQ) d with □-τ-elim P Q (d .Diverges.step)
... | cP m≡P       = DAcc→¬Div (dacc rsP) (subst Diverges m≡P (d .Diverges.rest))
... | cQ m≡Q       = DAcc→¬Div (dacc rsQ) (subst Diverges m≡Q (d .Diverges.rest))
... | chP P' Pτ m≡ = □-no-inf (rsP Pτ) (dacc rsQ) (subst Diverges m≡ (d .Diverges.rest))
... | chQ Q' Qτ m≡ = □-no-inf (dacc rsP) (rsQ Qτ) (subst Diverges m≡ (d .Diverges.rest))
... | sPQ P' Pτ m≡ = ▷-no-inf (rsP Pτ) (dacc rsQ) (subst Diverges m≡ (d .Diverges.rest))
... | sQP Q' Qτ m≡ = ▷-no-inf (rsQ Qτ) (dacc rsP) (subst Diverges m≡ (d .Diverges.rest))

□-Diverges→ : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
            → Diverges (P □ Q) → Diverges P ⊎ Diverges Q
□-Diverges→ d =
  dne (λ k → □-no-inf (¬Div→DAcc (λ dP → k (inj₁ dP)))
                       (¬Div→DAcc (λ dQ → k (inj₂ dQ))) d)

-- the ▷ analogue (certifies the ▷-Diverges→ postulate too)
▷-Diverges→ : {A B : PTree E (ExtI E) R}
            → Diverges (A ▷ B) → Diverges A ⊎ Diverges B
▷-Diverges→ d =
  dne (λ k → ▷-no-inf (¬Div→DAcc (λ dA → k (inj₁ dA)))
                       (¬Div→DAcc (λ dB → k (inj₂ dB))) d)

-- P △ Q can't diverge if P and Q are accessible (recursion on (DAcc P, DAcc Q);
-- the ret/slide cases land the divergence on a bare operand, killed directly)
△-no-inf : {P Q : PTree E (ExtI E) R}
         → DAcc P → DAcc Q → ¬ Diverges (P △ Q)
△-no-inf {P = P} {Q = Q} (dacc rsP) (dacc rsQ) d
  with d .Diverges.next | d .Diverges.rest | △-τ-elim P Q (d .Diverges.step)
... | _ | dr | △τP Pτ    = △-no-inf (rsP Pτ) (dacc rsQ) dr
... | _ | dr | △τQ Qτ    = △-no-inf (dacc rsP) (rsQ Qτ) dr
... | _ | dr | △τQret _  = DAcc→¬Div (dacc rsQ) dr
... | _ | dr | △τ⊓P _    = DAcc→¬Div (dacc rsP) dr
... | _ | dr | △τ⊓Q _    = DAcc→¬Div (dacc rsQ) dr

-- the △ analogue (certifies the △-Diverges→ postulate in InterruptDivergence)
△-Diverges→ : {P Q : PTree E (ExtI E) R}
            → Diverges (P △ Q) → Diverges P ⊎ Diverges Q
△-Diverges→ d =
  dne (λ k → △-no-inf (¬Div→DAcc (λ dP → k (inj₁ dP)))
                       (¬Div→DAcc (λ dQ → k (inj₂ dQ))) d)

-------------------------------------------------------------------------------------
-- Derivation 4:  >>-Diverges→ (the bind König step) from dne.
-- An infinite τ-path of `P′ >> X` either stays in the P-phase forever (P′ diverges)
-- or P′ silently reaches a ret (the √-free splice, where force(P′>>X)=force X) and X
-- diverges.  Deciding WHICH is the König step.  Route mirrors □-Diverges→ exactly: a
-- well-founded recursion on DAcc P′ (the only operand whose τ's the P-phase follows),
-- with the X-exit recorded as the second disjunct rather than a second accessibility.
-------------------------------------------------------------------------------------

-- √-free weak reach (local copy of SeqDistR's `_⟹ₚ⟨_⟩_`, kept identical so the
-- statement below matches the postulate verbatim; this module imports nothing from the
-- FD-law layer that postulates it).
infix 4 _⟹ₚ⟨_⟩_
data _⟹ₚ⟨_⟩_ {ℓr} {R : Set ℓr}
    : PTree E (ExtI E) R → List Event → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  ⟹ₚ-refl : ∀ {p} → p ⟹ₚ⟨ [] ⟩ p
  ⟹ₚ-τ    : ∀ {p q r s}            → p ─[ τ ]─► q          → q ⟹ₚ⟨ s ⟩ r → p ⟹ₚ⟨ s ⟩ r
  ⟹ₚ-ev   : ∀ {p q r s} {e : Event} → p ─[ ev (evl e) ]─► q → q ⟹ₚ⟨ s ⟩ r → p ⟹ₚ⟨ e ∷ s ⟩ r

-- retarget a step across a force-equation (force-equal trees share outgoing steps)
retarget : {a b u : PTree E (ExtI E) R} {l : Label R}
         → PTree.force a ≡ PTree.force b → b ─[ l ]─► u → a ─[ l ]─► u
retarget eq (sRet eqf)    = sRet (trans eq eqf)
retarget eq (sSil eqf)    = sSil (trans eq eqf)
retarget eq (sVis eqf br) = sVis (trans eq eqf) br
retarget eq (sTau eqf br) = sTau (trans eq eqf) br

-- divergence transfers across a force-equation (only the first τ-step inspects force)
div-force-eq : {a b : PTree E (ExtI E) R} → PTree.force a ≡ PTree.force b → Diverges b → Diverges a
div-force-eq eq d .Diverges.next = d .Diverges.next
div-force-eq eq d .Diverges.step = retarget eq (d .Diverges.step)
div-force-eq eq d .Diverges.rest = d .Diverges.rest

-- bind τ-step inversion: a τ of `P′ >> X` is either the √-splice (P′ at ret, so the
-- node is X's) or a P-phase step (P′ ─τ→ P″, residual P″ >> X).
>>-τ-elim : (P′ : PTree E (ExtI E) R) (X : PTree E (ExtI E) S) {M : PTree E (ExtI E) S}
          → (P′ >> X) ─[ τ ]─► M
          → (Σ[ r ∈ R ] (PTree.force P′ ≡ ret r))
          ⊎ (Σ[ P″ ∈ PTree E (ExtI E) R ] (P′ ─[ τ ]─► P″) × (M ≡ P″ >> X))
>>-τ-elim P′ X step with PTree.force P′ in eqP
... | ret r     = inj₁ (r , refl)
... | sil c     = inj₂ (c , sSil eqP , sil-τ-inv (fBind-sil (λ _ → X) P′ eqP) step)
... | react v τc with react-τ-inv (fBind-react (λ _ → X) P′ eqP) step
...   | i , a , br with bindT-elim (λ _ → X) (react v τc) br
...     | t′ , vt , m≡ = inj₂ (t′ , sTau eqP vt , m≡)

-- P′ >> X cannot diverge if P′ is accessible AND P′ has no √-free silent run to a ret
-- with X diverging.  Well-founded recursion on DAcc P′ (X is fixed; its exit is the
-- second hypothesis, threaded by prepending each P-phase τ to the silent run).
>>-no-inf : {P′ : PTree E (ExtI E) R} {X : PTree E (ExtI E) S}
          → DAcc P′
          → ¬ (Σ[ P″ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
                 (P′ ⟹ₚ⟨ [] ⟩ P″) × (PTree.force P″ ≡ ret r) × Diverges X)
          → ¬ Diverges (P′ >> X)
>>-no-inf {P′ = P′} {X = X} (dacc rsP) noReach d
  with >>-τ-elim P′ X (d .Diverges.step)
... | inj₁ (r , eqP)        =
      noReach (P′ , r , ⟹ₚ-refl , eqP , div-force-eq (sym (fBind-ret (λ _ → X) P′ eqP)) d)
... | inj₂ (P″ , Pτ , m≡)   =
      >>-no-inf (rsP Pτ)
                (λ where (P‴ , r , reach , eqr , dX) →
                           noReach (P‴ , r , ⟹ₚ-τ Pτ reach , eqr , dX))
                (subst Diverges m≡ (d .Diverges.rest))

-- certifies the >>-Diverges→ postulate in SeqDistR
>>-Diverges→ : {P′ : PTree E (ExtI E) R} {X : PTree E (ExtI E) S}
             → Diverges (P′ >> X)
             → Diverges P′
             ⊎ (Σ[ P″ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
                  (P′ ⟹ₚ⟨ [] ⟩ P″) × (PTree.force P″ ≡ ret r) × Diverges X)
>>-Diverges→ {P′ = P′} {X = X} d =
  dne (λ k → >>-no-inf (¬Div→DAcc (λ dP → k (inj₁ dP)))
                       (λ w → k (inj₂ w)) d)

-------------------------------------------------------------------------------------
-- Derivation 5:  Par-Diverges→ (the parallel König step) from dne.
-- Same DAcc route as □-Diverges→: a τ of `Par P Q` is τL (P steps) or τR (Q steps)
-- (Par-τ-elim) — the chain stays in Par form (the both-offer overlap is reached only by a
-- visible event, never a τ), so there are no slide cases.  Hence Par P Q cannot diverge
-- when P and Q are both accessible.
-------------------------------------------------------------------------------------
Par-no-inf : (A : EventSet) (merge : Mg R₁ R₂ R)
             {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
           → DAcc P → DAcc Q → ¬ Diverges (Par A merge P Q)
Par-no-inf A merge {P = P} {Q = Q} (dacc rsP) (dacc rsQ) d
  with Par-τ-elim A merge P Q (d .Diverges.step)
... | τL P' Pτ m≡ = Par-no-inf A merge (rsP Pτ) (dacc rsQ) (subst Diverges m≡ (d .Diverges.rest))
... | τR Q' Qτ m≡ = Par-no-inf A merge (dacc rsP) (rsQ Qτ) (subst Diverges m≡ (d .Diverges.rest))

-- certifies the Par-Diverges→ postulate in ParallelDivergence
Par-Diverges→ : (A : EventSet) (merge : Mg R₁ R₂ R)
                {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
              → Diverges (Par A merge P Q) → Diverges P ⊎ Diverges Q
Par-Diverges→ A merge d =
  dne (λ k → Par-no-inf A merge (¬Div→DAcc (λ dP → k (inj₁ dP)))
                                (¬Div→DAcc (λ dQ → k (inj₂ dQ))) d)

-------------------------------------------------------------------------------------
-- Derivation 6:  loop-Diverges→ (the iterate / loop König step) from dne.
-- An infinite τ-path of `iter-bind Q (loopStep body)` either stays inside the
-- current iteration's source `Q` forever (Q diverges), or `Q` silently reaches a
-- loop-back (`ret (inj₁ tt)`), the iter-bind τ's into `loop0 body`, and the
-- residual loop diverges.  Deciding WHICH is the König step.  Route mirrors
-- `>>-Diverges→` exactly: a well-founded recursion on DAcc Q (the only operand
-- whose τ's the iteration follows), with the loop-back exit recorded as the
-- second disjunct (a silent reach + the residual `loop0 body` divergence),
-- threaded by prepending each Q-phase τ to the silent run.
-------------------------------------------------------------------------------------

-- local copies of the loop continuations (kept identical to CSP.Laws.FD.IterateFD's
-- `loop-k`/`loopStep`, so the statement below matches the postulate verbatim; this
-- module imports nothing from the FD-law layer that postulates `loop-Diverges→`).
loop-k : ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)
loop-k a′ = Ret (inj₁ a′)

loopStep : PTree E (ExtI E) (⊤ {ℓ}) → ⊤ {ℓ} → PTree E (ExtI E) (⊤ {ℓ} ⊎ R)
loopStep body a = body >>= loop-k

-- iter-bind τ-step inversion (specialised to the loop continuation `loopStep body`):
-- a τ of `iter-bind Q (loopStep body)` is either the loop-back (Q at `ret (inj₁ tt)`,
-- so the node τ's to `iter (loopStep body) tt = loop0 body`) or a Q-phase step
-- (Q ─τ→ Q′, residual `iter-bind Q′ (loopStep body)`).  The `ret (inj₂ r)` source
-- makes the node a `ret` (no τ), so that case is impossible.
iter-loopStep-τ-elim : (body : PTree E (ExtI E) (⊤ {ℓ})) (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
                       {M : PTree E (ExtI E) R}
                     → (iter-bind Q (loopStep body)) ─[ τ ]─► M
                     → ((PTree.force Q ≡ ret (inj₁ tt)) × (M ≡ loop0 body))
                     ⊎ (Σ[ Q′ ∈ PTree E (ExtI E) (⊤ {ℓ} ⊎ R) ]
                          (Q ─[ τ ]─► Q′) × (M ≡ iter-bind Q′ (loopStep body)))
iter-loopStep-τ-elim body Q step with PTree.force Q in eqQ
... | ret (inj₁ tt) = inj₁ (refl , sil-τ-inv (fIter-r1 (loopStep body) Q eqQ) step)
... | ret (inj₂ r)  = ⊥-elim (ret-no-τ (fIter-r2 (loopStep body) Q eqQ) step)
  where ret-no-τ : ∀ {ℓr} {R′ : Set ℓr} {t u : PTree E (ExtI E) R′} {x}
                 → PTree.force t ≡ ret x → t ─[ τ ]─► u → ⊥
        ret-no-τ eq (sSil ef)   with trans (sym eq) ef
        ...                        | ()
        ret-no-τ eq (sTau ef _) with trans (sym eq) ef
        ...                        | ()
... | sil c         = inj₂ (c , sSil eqQ , sil-τ-inv (fIter-sil (loopStep body) Q eqQ) step)
... | react v τc with react-τ-inv (fIter-react (loopStep body) Q eqQ) step
...   | i , a , br with iterT-elim (loopStep body) (react v τc) br
...     | t′ , vt , m≡ = inj₂ (t′ , sTau eqQ vt , m≡)

-- `iter-bind Q (loopStep body)` cannot diverge if Q is accessible AND Q has no
-- τ*-silent run to a `ret (inj₁ tt)` loop-back with `loop0 body` diverging.  A
-- well-founded recursion on DAcc Q (the loop continuation is fixed; its exit is
-- the second hypothesis, threaded by prepending each Q-phase τ to the silent run).
iter-no-inf : (body : PTree E (ExtI E) (⊤ {ℓ})) {Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R)}
            → DAcc Q
            → ¬ (Σ[ Qᵣ ∈ PTree E (ExtI E) (⊤ {ℓ} ⊎ R) ]
                   (Q ─[τ*]─► Qᵣ) × (PTree.force Qᵣ ≡ ret (inj₁ tt)) × Diverges (loop0 body))
            → ¬ Diverges (iter-bind Q (loopStep body))
iter-no-inf body {Q = Q} (dacc rsQ) noReach d
  with iter-loopStep-τ-elim body Q (d .Diverges.step)
... | inj₁ (eqQ , m≡)      =
      noReach (Q , τ*-refl , eqQ , subst Diverges m≡ (d .Diverges.rest))
... | inj₂ (Q′ , Qτ , m≡)  =
      iter-no-inf body (rsQ Qτ)
                  (λ where (Qᵣ , reach , eqr , dL) →
                             noReach (Qᵣ , τ*-step Qτ reach , eqr , dL))
                  (subst Diverges m≡ (d .Diverges.rest))

-- certifies the loop-Diverges→ postulate in CSP.Laws.FD.IterateFD
loop-Diverges→ : (body : PTree E (ExtI E) (⊤ {ℓ})) (Q : PTree E (ExtI E) (⊤ {ℓ} ⊎ R))
               → Diverges (iter-bind Q (loopStep body))
               → Diverges Q
               ⊎ (Σ[ Qᵣ ∈ PTree E (ExtI E) (⊤ {ℓ} ⊎ R) ]
                    (Q ─[τ*]─► Qᵣ) × (PTree.force Qᵣ ≡ ret (inj₁ tt))
                    × Diverges (loop0 body))
loop-Diverges→ body Q d =
  dne (λ k → iter-no-inf body (¬Div→DAcc (λ dQ → k (inj₁ dQ)))
                          (λ w → k (inj₂ w)) d)

-------------------------------------------------------------------------------------
-- Derivation 7:  offer-LEM from dne — a plain instance of the law of excluded middle
-- (every proposition, here `Offers t e`, is decidable classically).
-------------------------------------------------------------------------------------
-- certifies the offer-LEM postulate in ParallelRefusals
offer-LEM : (t : PTree E (ExtI E) R) (e : Event√ R) → Offers t e ⊎ ¬ Offers t e
offer-LEM t e = dne (λ k → k (inj₂ (λ o → k (inj₁ o))))

-------------------------------------------------------------------------------------
-- Derivation 8:  modA-transfer (the HIDING-divergence König step) from dne.
--
-- This certifies the SINGLE postulate of CSP.Laws.Bisim.DRCongruence, used to
-- complete the FULL divergence-respecting hiding congruence `cong-∖`.  The postulate
-- there reads (with `DivModA`/`ModAStep` its own local notions):
--
--     modA-transfer : DivModA A P → P ≈DR Q → DivModA A Q
--
-- `DivModA A t` is an infinite path of t-steps each of which is either a τ or a
-- HIDDEN A-event (a `ModAStep`).  Transferring it across `P ≈DR Q` is a genuine
-- classical König step: an A-event of P is matched by a WEAK visible A-step of Q
-- (τ*·a·τ*, ≥1 step, productive), but a τ of P is matched by a WEAK τ of Q that may
-- be EMPTY — so a P-path with only finitely many A-events eventually becomes a pure-τ
-- tail whose Q-image can stall.  Producing a Q-step each round needs the Σ⁰₂ decision
-- "is there an A-event ahead?", which is precisely the classical content discharged
-- here from `dne`.
--
-- ClassicalFromLEM does not (and must not) import DRCongruence, so we RE-STATE the
-- notions locally (`ModAStepC`/`DivModAC`, identical up to renaming) and certify the
-- principle in this context: `modA-transfer-cert`.  The correspondence with the
-- DRCongruence postulate is verbatim.
--
-- The classical pivot is the inductive predicate `EvA dm` = "an A-event occurs after
-- finitely many τ-only steps of the path `dm`".  `dne` decides `EvA dm ⊎ ¬ EvA dm`:
--   • ¬ EvA dm  ⇒  the path is purely τ from here ⇒ `Diverges P` ⇒ (via `≈DR`'s
--     `div→`) `Diverges Q` ⇒ a `DivModAC A Q` whose steps are all τ's.
--   • EvA dm    ⇒  finitely many τ's then an A-event; we thread them through the
--     bisim (τ's → possibly-empty Q-τ*-runs of `maτ`'s; the A-event → a nonempty
--     wev whose middle `a` is one `maE` step), guaranteeing ≥1 emitted Q-step before
--     the corecursive `modA-transfer-cert` resumes on the residual.
-------------------------------------------------------------------------------------

-- local re-statement of DRCongruence's ModAStep / DivModA (this module cannot import
-- DRCongruence without leaking `dne`).
data ModAStepC {ℓr} {R : Set ℓr} (A : EventSet)
              (t : PTree E (ExtI E) R) (t′ : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  maτ : t ─[ τ ]─► t′ → ModAStepC A t t′
  maE : {B : Set ℓ} {e : E B} {a : B} → A .EventSet.mem (B , e) a
      → t ─[ ev (evl (evLabel B e a)) ]─► t′ → ModAStepC A t t′

record DivModAC {ℓr} {R : Set ℓr} (A : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    {maNext} : PTree E (ExtI E) R
    maStep   : ModAStepC A t maNext
    maRest   : DivModAC A maNext
open DivModAC

-- every divergence is a DivModA path (each τ is an maτ step) — purely coinductive.
Div→DivModAC : (A : EventSet) {t : PTree E (ExtI E) R} → Diverges t → DivModAC A t
Div→DivModAC A d .maNext = d .Diverges.next
Div→DivModAC A d .maStep = maτ (d .Diverges.step)
Div→DivModAC A d .maRest = Div→DivModAC A (d .Diverges.rest)

-- "an A-event occurs after finitely many τ-only steps of the path `dm`" — inductive.
data EvA {ℓr} {R : Set ℓr} (A : EventSet)
     : {t : PTree E (ExtI E) R} → DivModAC A t → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  ev-here  : ∀ {t} (dm : DivModAC A t) {B : Set ℓ} {e : E B} {a : B}
               (mem : A .EventSet.mem (B , e) a)
               (st : t ─[ ev (evl (evLabel B e a)) ]─► dm .maNext)
           → dm .maStep ≡ maE mem st → EvA A dm
  ev-there : ∀ {t} (dm : DivModAC A t) (stτ : t ─[ τ ]─► dm .maNext)
           → dm .maStep ≡ maτ stτ
           → EvA A (dm .maRest) → EvA A dm

-- if the path never (eventually) shows an A-event, it is purely τ ⇒ Diverges.
-- the head must be an maτ (else `ev-here` gives `EvA dm`), and the tail also has
-- `¬ EvA` (else `ev-there` does) — coinductive, productive.
-- from `¬ EvA dm` the head must be an maτ; expose its τ-step and the head equation.
¬EvA-headτ : (A : EventSet) {t : PTree E (ExtI E) R} (dm : DivModAC A t)
           → ¬ EvA A dm
           → Σ[ stτ ∈ (t ─[ τ ]─► dm .maNext) ] (dm .maStep ≡ maτ stτ)
¬EvA-headτ A dm ¬e = go (dm .maStep) refl
  where
    go : (s : ModAStepC A _ (dm .maNext)) → dm .maStep ≡ s
       → Σ[ stτ ∈ (_ ─[ τ ]─► dm .maNext) ] (dm .maStep ≡ maτ stτ)
    go (maτ stτ)    eq = stτ , eq
    go (maE mem st) eq = ⊥-elim (¬e (ev-here dm mem st eq))

-- the head being a τ, `¬ EvA` propagates to the tail.
¬EvA-tail : (A : EventSet) {t : PTree E (ExtI E) R} (dm : DivModAC A t)
          → (¬e : ¬ EvA A dm) → ¬ EvA A (dm .maRest)
¬EvA-tail A dm ¬e er =
  ¬e (ev-there dm (proj₁ (¬EvA-headτ A dm ¬e)) (proj₂ (¬EvA-headτ A dm ¬e)) er)

¬EvA→Div : (A : EventSet) {t : PTree E (ExtI E) R} (dm : DivModAC A t)
         → ¬ EvA A dm → Diverges t
¬EvA→Div A dm ¬e .Diverges.next = dm .maNext
¬EvA→Div A dm ¬e .Diverges.step = proj₁ (¬EvA-headτ A dm ¬e)
¬EvA→Div A dm ¬e .Diverges.rest = ¬EvA→Div A (dm .maRest) (¬EvA-tail A dm ¬e)

-- THE CERTIFICATION.  A mutual block of three functions:
--   • `modA-transfer-cert` : the transfer itself, `dne`-decided each round.
--   • `consume-ev`         : dispatch on the inductive `EvA` witness (terminating
--                            recursion on `EvA`); reaches the A-event in finitely many
--                            τ-rounds, where it emits a genuine `maE` step.
--   • `consume-run`        : emit a pending Q-τ*-run as `maτ` steps (copattern,
--                            terminating recursion on the run), then continue.
-- Every cycle of the mutual recursion passes through a `DivModAC` constructor (a `maτ`
-- in `consume-run`, or the `maE` of the matched A-event in `consume-ev`), so the
-- corecursion is productive.  The two inductive recursions (`consume-ev` on `EvA`,
-- `consume-run` on the run) are terminating.
modA-transfer-cert : (A : EventSet) {P Q : PTree E (ExtI E) R}
                   → DivModAC A P → DRbisim R P Q → DivModAC A Q
consume-ev : (A : EventSet) {P Q : PTree E (ExtI E) R} (dm : DivModAC A P)
           → EvA A dm → DRbisim R P Q → DivModAC A Q
consume-run : (A : EventSet) {P Q Q′ : PTree E (ExtI E) R} (dm : DivModAC A P)
            → Q ─[τ*]─► Q′ → EvA A dm → DRbisim R P Q′ → DivModAC A Q

-- emit the pending Q-τ*-run head-by-head as `maτ` (guarded), then resume on `EvA`.
consume-run A dm τ*-refl                       evA pq = consume-ev A dm evA pq
consume-run A dm (τ*-step {t′ = t′} qτ run) evA pq .maNext = t′
consume-run A dm (τ*-step          qτ run) evA pq .maStep = maτ qτ
consume-run A dm (τ*-step          qτ run) evA pq .maRest = consume-run A dm run evA pq

-- ev-there: the head is a τ of P; match it by a (possibly empty) weak-τ run of Q,
-- emit it via `consume-run`, recurse structurally on the smaller `EvA` witness.
consume-ev A {P} {Q} dm (ev-there .dm stτ _ evRest) pq
  with pq .DRbisim.fwd .WSimF.on-tau stτ
... | _ , wτ Q→Q′ , P′≈Q′ = consume-run A (dm .maRest) Q→Q′ evRest P′≈Q′
-- ev-here: the head is a hidden A-event of P; match it by a WEAK visible A-step of Q
-- (τ*·a·τ*).  The middle `a` is a genuine `maE` step ⇒ ≥1 Q-step emitted, guarding
-- the corecursive `modA-transfer-cert` on the residual (the trailing τ* emitted first).
consume-ev A {P} {Q} dm (ev-here .dm mem st _) pq
  with pq .DRbisim.fwd .WSimF.on-ev st
... | _ , wev Q→Q₁ Q₁a Q₂→Q′ , P′≈Q′ = go Q→Q₁
  where
    -- emit a τ*-run as `maτ`'s ending in the corecursive transfer on the residual.
    goTail : ∀ {Qs} → Qs ─[τ*]─► _ → DivModAC A Qs
    goTail τ*-refl                    = modA-transfer-cert A (dm .maRest) P′≈Q′
    goTail (τ*-step {t′ = t″} qτ run) .maNext = t″
    goTail (τ*-step          qτ run) .maStep = maτ qτ
    goTail (τ*-step          qτ run) .maRest = goTail run
    -- the A-event `maE` step, with the trailing τ*-run (Q₂→Q′) emitted after it.
    tail : DivModAC A _
    tail .maNext = _
    tail .maStep = maE mem Q₁a
    tail .maRest = goTail Q₂→Q′
    -- emit the leading τ*-run (Q→Q₁) as `maτ`'s, then `tail`.  `maE` is the guard.
    go : ∀ {Qs} → Qs ─[τ*]─► _ → DivModAC A Qs
    go τ*-refl                    = tail
    go (τ*-step {t′ = t″} qτ run) .maNext = t″
    go (τ*-step          qτ run) .maStep = maτ qτ
    go (τ*-step          qτ run) .maRest = go run

modA-transfer-cert A {P} {Q} dm pq
  with dne (λ (k : ¬ (EvA A dm ⊎ ¬ EvA A dm)) → k (inj₂ (λ e → k (inj₁ e))))
... | inj₁ evA  = consume-ev A dm evA pq
... | inj₂ ¬evA = Div→DivModAC A (pq .DRbisim.div→ (¬EvA→Div A dm ¬evA))

-------------------------------------------------------------------------------------
-- Derivation 9:  Hide-Diverges→ (the HIDING-divergence König step) from dne.
--
-- This certifies the SINGLE postulate of CSP.Laws.FD.HideDivergence, used to refute
-- divergence under hiding (`¬ Diverges (P ∖ A)`) by a well-founded descent.  The
-- postulate there reads (with `DivModA`/`ModAStep` of DRCongruence — the SAME notions,
-- re-stated here as `DivModAC`/`ModAStepC`, identical up to renaming):
--
--     Hide-noinf-from-acc : MAccC A t → ¬ DivModAC A t        (constructive)
--     ¬DivModAC→MAccC      : ¬ DivModAC A t → MAccC A t        (classical, from dne)
--
-- `DivModAC A t` is an infinite path of t-steps each of which is a τ OR a hidden
-- A-event (a `ModAStepC`).  Hiding `∖ A` turns exactly such a path into a genuine
-- `Diverges (P ∖ A)` (DRCongruence's `modA→div∖`); conversely every divergence of
-- `P ∖ A` projects to one (DRCongruence's `div∖→modA`, constructive).  So refuting
-- `Diverges (P ∖ A)` ⇔ refuting `DivModAC A P`.
--
-- The route is the EXACT `DAcc` engine of Derivation 2/5, but over the modulo-A step
-- relation `ModAStepC` (τ ∪ hidden-A) instead of bare τ:  `MAccC A t` is accessibility
-- of `ModAStepC`; an accessible state cannot have an infinite modulo-A path
-- (well-founded recursion, constructive); from `dne`, a non-accessible state has a
-- non-accessible `ModAStepC`-successor, hence an infinite modulo-A path, so
-- `¬ DivModAC ⇒ MAccC`.  No infinite choice is taken — the successor is decided one
-- `ModAStepC` at a time against the well-founded `MAccC` measure.
-------------------------------------------------------------------------------------

-- accessibility of the modulo-A step relation (own copy, like DAcc)
data MAccC {ℓr} {R : Set ℓr} (A : EventSet) (t : PTree E (ExtI E) R)
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  macc : (∀ {t′} → ModAStepC A t t′ → MAccC A t′) → MAccC A t

-- an accessible state has no infinite modulo-A path (well-founded recursion on MAccC)
MAccC→¬DivModAC : (A : EventSet) {t : PTree E (ExtI E) R} → MAccC A t → ¬ DivModAC A t
MAccC→¬DivModAC A (macc rs) dm = MAccC→¬DivModAC A (rs (dm .maStep)) (dm .maRest)

-- a non-accessible state has a modulo-A successor that is also non-accessible (via dne)
nonMAccC→step : (A : EventSet) {t : PTree E (ExtI E) R}
              → ¬ MAccC A t
              → Σ[ t′ ∈ PTree E (ExtI E) R ] (ModAStepC A t t′ × ¬ MAccC A t′)
nonMAccC→step A nAcc =
  dne (λ k → nAcc (macc (λ step → dne (λ na → k (_ , step , na)))))

-- …so a non-accessible state has an infinite modulo-A path (corecursively follow it)
nonMAccC→DivModAC : (A : EventSet) {t : PTree E (ExtI E) R} → ¬ MAccC A t → DivModAC A t
nonMAccC→DivModAC A nAcc .maNext = proj₁ (nonMAccC→step A nAcc)
nonMAccC→DivModAC A nAcc .maStep = proj₁ (proj₂ (nonMAccC→step A nAcc))
nonMAccC→DivModAC A nAcc .maRest = nonMAccC→DivModAC A (proj₂ (proj₂ (nonMAccC→step A nAcc)))

-- certifies the Hide-Diverges→ postulate (classical half) in CSP.Laws.FD.HideDivergence
¬DivModAC→MAccC : (A : EventSet) {t : PTree E (ExtI E) R} → ¬ DivModAC A t → MAccC A t
¬DivModAC→MAccC A nd = dne (λ nAcc → nd (nonMAccC→DivModAC A nAcc))
