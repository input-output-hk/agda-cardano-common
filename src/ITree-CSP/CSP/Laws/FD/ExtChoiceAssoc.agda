{-# OPTIONS --guardedness #-}

-- External-choice associativity (FD).  COMPLETE — no postulates / holes / NON_TERMINATING.
--
--   □-assoc-FD : ((P □ Q) □ R₀) ≈FD (P □ (Q □ R₀))
--
-- DIVERGENCE half (□-assoc-⊑D / ⊒D): pure routing through □-div-elim / □-div-intro-L/R.
--
-- FAILURES half — the transfer □-assoc-fail-RL / -LR is PURE ROUTING once the trace is
-- split (the earlier "BLOCKED" note feared a nested √-slide / □-left-monotonicity bridge;
-- that route (elim → mono → intro) is indeed false at the empty trace, but splitting the
-- trace sidesteps it entirely):
--   • s ≡ []      : failures (P□Q) [] X is the CONJUNCTION failures P [] X × failures Q [] X
--                   (□-fail-nil-→ / □-fail-nil-←), so []-associativity is a ×-reassociation.
--                   The slide/commit τ-cases are VACUOUS at [] (ret / ▷ never reach a stable
--                   state by τ-only — ▷-ret-noreach-stable).
--   • s ≡ e ∷ s'  : □-failures-elim (forward ⊎) + ⊎-reassociation + □-fail-intro-cons-L/R
--                   (the leading event breaks the empty-trace refusal-intersection, so the
--                   non-empty intro is clean: lift leading τ's via □-fail-τ-pre-L/-R, commit
--                   the event via □-ev-toL/toR).
--
-- Supporting (this file): refuses-□-split / -join / -assoc-LR/RL (refl base), □-ev-toR,
-- □→▷-term-□R (nested √-slide bridge — kept, still the cleanest proof that it IS provable),
-- □-Rlive-τ-inv, □-τ-inv-full (force-carrying τ-inversion), □-fail-nil-→/← and the
-- □-fail-intro-cons-L/R / □-τ*-L/R helpers.

open import Level using (Level; Lift; lift; lower)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _⊑D_; _⊑F⊥_; _≈FD_)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (□-mt-tag0-eq; □-mt-tag1-eq; fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G;
         mergeVis-R-eq; mergeVis-LQ-eq; NonRet;
         □-τ-tochoice; □-τ-tochoice-R; □-τ-toslide)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepR; ⊓-stepL; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (evP; evQ; evPQ; □-ev-elim; react-τ-inv; □-mt-elim; □-slide-RQ-elim;
         □-slide-PR-elim; br2-elim; ret-no-τ; viewT-τ; ▷-τ-elim)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-div-elim; □-div-intro-L; □-div-intro-R; mk-stable; □-offers-L;
         □→▷-term-step-τ; □→▷-term-step-ev; □-Rret-τ-inv; □-Rret-unstable;
         □-τ-toQ; □-ev-toL; ⊓-no-ev; □-fail-τ-pre-L; τ→NonRet; □-failures-elim;
         ▷-unstable; stable-not-ret; fail-τ-prepend)
open import CSP.Laws.FD.ExtChoiceIdem E-≟
  using (stable-react; □-fail-τ-pre-R)
open import CSP.Laws.Traces.TraceLaws E-≟
  using (force-▷-react; force-▷-sil)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-unstable)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- refuses-□ split / join : the 3-way (association-independent) refl base.  A stable
-- P□Q (react/react with everywhere-nothing τ-branch) refuses X iff BOTH P and Q are
-- stable and refuse X.  Generalises stable-double / offers-double-elim of ExtChoiceIdem
-- to two distinct operands.
-------------------------------------------------------------------------------------

-- an offer of P□Q projects to an offer of one operand (any P,Q; via □-ev-elim)
offers-□-elim : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {e : Event√ R}
              → Offers (P □ Q) e → Offers P e ⊎ Offers Q e
offers-□-elim {P = P} {Q = Q} (M , step) with □-ev-elim P Q step
... | evP Pev      = inj₁ (_ , Pev)
... | evQ Qev      = inj₂ (_ , Qev)
... | evPQ Pev Qev = inj₁ (_ , Pev)

-- mirror of □-offers-L : a Q-offer lifts to an offer of P□Q (both react)
□-offers-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
             {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             {e : Event√ R} {M : PTree E (ExtI E) R}
           → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → Q ─[ ev e ]─► M → Offers (P □ Q) e
□-offers-R P Q eqP eqQx (sRet eqQ) = case trans (sym eqQx) eqQ of λ ()
□-offers-R P Q {vP = vP} eqP eqQx (sVis {v = vQ} {at = at} {a = a} eqQ brQ) with vP at a in eqVP
... | nothing = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                         (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)
... | just P₁ = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                         (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ)

-- P□Q is stable when both P and Q are (the merged τ-branch is everywhere nothing)
stable-□-join : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R}
              → isStable P → isStable Q → isStable (P □ Q)
stable-□-join {P = P} {Q = Q} stP stQ
  with stable-react {P = P} stP | stable-react {P = Q} stQ
... | vP , τcP , eqP , τcP-n | vQ , τcQ , eqQ , τcQ-n =
      mk-stable {t = P □ Q} pq-force mt-branch
  where
    pq-force : PTree.force (P □ Q)
             ≡ react (mergeVis vP vQ) (□-mt (react vP τcP) (react vQ τcQ) P Q)
    pq-force = fL-G {P = P} {Q = Q} eqP eqQ tt tt
    mt-branch : ∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing
    mt-branch (_ , base _)            a = refl
    mt-branch (_ , fin)               a = refl
    mt-branch (_ , pair (base _) _)   a = refl
    mt-branch (_ , pair (pair _ _) _) a = refl
    mt-branch (_ , pair fin i) (lift fzero , a)           rewrite τcP-n (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc fzero) , a)    rewrite τcQ-n (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

-- join: Refuses P X × Refuses Q X ⇒ Refuses (P□Q) X
refuses-□-join : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
               → Refuses P X → Refuses Q X → Refuses (P □ Q) X
refuses-□-join {P = P} {Q = Q} {X = X} (stP , noffP) (stQ , noffQ) =
  stable-□-join {P = P} {Q = Q} stP stQ , noff′
  where
    noff′ : ∀ e → X e → ¬ Offers (P □ Q) e
    noff′ e xe off with offers-□-elim {P = P} {Q = Q} off
    ... | inj₁ offP = noffP e xe offP
    ... | inj₂ offQ = noffQ e xe offQ

-- the react/react core (takes the force-equations as explicit args so the result type
-- is NOT with-generalised over force P / force Q)
refuses-□-split-react : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                       {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                       {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                     → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
                     → (∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing)
                     → (∀ e → X e → ¬ Offers (P □ Q) e)
                     → Refuses P X × Refuses Q X
refuses-□-split-react P Q {X = X} {vP = vP} {vQ = vQ} {τcP = τcP} {τcQ = τcQ} eqP eqQ mt-nothing noff =
  (stP , refP) , (stQ , refQ)
  where
    pn : ∀ i a → τcP i a ≡ nothing
    pn i a with τcP i a in eqt
    ... | nothing = refl
    ... | just P′ = case trans (sym (□-mt-tag0-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                  {P = P} {Q = Q} {iₚ = i} {aₚ = a} {P₁ = P′} eqt))
                               (mt-nothing ((Lift ℓ (Fin 2) × proj₁ i) , pair fin (proj₂ i))
                                           (lift fzero , a))
                    of λ ()
    qn : ∀ i a → τcQ i a ≡ nothing
    qn i a with τcQ i a in eqt
    ... | nothing = refl
    ... | just Q′ = case trans (sym (□-mt-tag1-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                  {P = P} {Q = Q} {iₚ = i} {aₚ = a} {Q₁ = Q′} eqt))
                               (mt-nothing ((Lift ℓ (Fin 2) × proj₁ i) , pair fin (proj₂ i))
                                           (lift (fsuc fzero) , a))
                    of λ ()
    stP : isStable P
    stP = mk-stable {t = P} eqP pn
    stQ : isStable Q
    stQ = mk-stable {t = Q} eqQ qn
    refP : ∀ e → X e → ¬ Offers P e
    refP e xe (P₁ , pstep) = noff e xe (□-offers-L P Q eqP eqQ pstep)
    refQ : ∀ e → X e → ¬ Offers Q e
    refQ e xe (Q₁ , qstep) = noff e xe (□-offers-R P Q eqP eqQ qstep)

-- a stable P□Q forces react/react with the merged τ-branch everywhere nothing; every
-- other shape has an always-enabled τ, contradicting stability.  The result type does
-- NOT mention isStable P / isStable Q, so the with-abstraction over force P is harmless.
stable-□-forces : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                → Refuses (P □ Q) X
                → Σ[ vP ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
                  Σ[ vQ ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
                  Σ[ τcP ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                  Σ[ τcQ ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                    (PTree.force P ≡ react vP τcP × PTree.force Q ≡ react vQ τcQ
                     × (∀ i a → □-mt (react vP τcP) (react vQ τcQ) P Q i a ≡ nothing))
stable-□-forces P Q {X = X} (st , noff)
  with PTree.force P | PTree.force Q
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = ⊥-elim (lower st)
...   | no ¬eq   = case st (Lift ℓ (Fin 2) , fin) (lift fzero) of λ ()
stable-□-forces P Q (st , noff) | ret rP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | ret rP | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | sil P′ | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | sil P′ | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | sil P′ | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | react vP τcP | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | react vP τcP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero) of λ ()
stable-□-forces P Q (st , noff) | react vP τcP | react vQ τcQ =
  vP , vQ , τcP , τcQ , refl , refl , st

-- split: Refuses (P□Q) X ⇒ Refuses P X × Refuses Q X.
refuses-□-split : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
                → Refuses (P □ Q) X → Refuses P X × Refuses Q X
refuses-□-split {P = P} {Q = Q} {X = X} ref@(st , noff)
  with stable-□-forces P Q ref
... | vP , vQ , τcP , τcQ , eqP , eqQ , mtn =
      refuses-□-split-react P Q eqP eqQ mtn noff

-------------------------------------------------------------------------------------
-- refuses-assoc : both directions of the refl base.
-------------------------------------------------------------------------------------

refuses-assoc-LR : ⦃ _ : DecEq R ⦄ {P Q R₀ : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
                 → Refuses ((P □ Q) □ R₀) X → Refuses (P □ (Q □ R₀)) X
refuses-assoc-LR {P = P} {Q = Q} {R₀ = R₀} ref
  with refuses-□-split {P = P □ Q} {Q = R₀} ref
... | refPQ , refR with refuses-□-split {P = P} {Q = Q} refPQ
...   | refP , refQ = refuses-□-join {P = P} {Q = Q □ R₀} refP
                                     (refuses-□-join {P = Q} {Q = R₀} refQ refR)

refuses-assoc-RL : ⦃ _ : DecEq R ⦄ {P Q R₀ : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
                 → Refuses (P □ (Q □ R₀)) X → Refuses ((P □ Q) □ R₀) X
refuses-assoc-RL {P = P} {Q = Q} {R₀ = R₀} ref
  with refuses-□-split {P = P} {Q = Q □ R₀} ref
... | refP , refQR with refuses-□-split {P = Q} {Q = R₀} refQR
...   | refQ , refR = refuses-□-join {P = P □ Q} {Q = R₀}
                                     (refuses-□-join {P = P} {Q = Q} refP refQ) refR

-------------------------------------------------------------------------------------
-- □-ev-toR : Q's visible/√ step lifts into P□Q reaching the SAME final state W
-- (mirror of □-ev-toL).
-------------------------------------------------------------------------------------

□-ev-toR : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ W : PTree E (ExtI E) R}
           {e : Event√ R} {s : List (Event√ R)}
         → Q ─[ ev e ]─► Q₁ → Q₁ ⟹⟨ s ⟩ W → (P □ Q) ⟹⟨ e ∷ s ⟩ W
□-ev-toR P Q {Q₁ = Q₁} (sVis {v = vQ} {at = at} {a = a} eqQ brQ) rest with PTree.force P in eqP
... | ret _ = ⟹-ev (sVis (fL-D {P = P} {Q = Q} eqP eqQ) brQ) rest
... | sil _ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                         (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl brQ)) rest
... | react vP τcP with vP at a in eqVP
...   | nothing = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)) rest
...   | just P₁ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                             (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ)) (⟹-τ (⊓-stepR P₁ Q₁) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest with PTree.force P in eqP
... | ret r′ with x ≟ r′
...   | yes refl = ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQ)) rest
...   | no ¬eq   = ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                             (fL-B {P = P} {Q = Q} eqP eqQ (λ eq → ¬eq (sym eq))) refl)
                       (⟹-ev (sRet eqQ) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest | sil _ =
  ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
            {a = lift fzero , lift fzero} (fL-E {P = P} {Q = Q} eqP eqQ) refl)
      (⟹-ev (sRet eqQ) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest | react _ _ =
  ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
            {a = lift fzero , lift fzero} (fL-F {P = P} {Q = Q} eqP eqQ) refl)
      (⟹-ev (sRet eqQ) rest)

-------------------------------------------------------------------------------------
-- □-assoc-⊒D : divergences ((P□Q)□R₀) ⊆ divergences (P□(Q□R₀))
-------------------------------------------------------------------------------------

□-assoc-⊒D : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
           → (P □ (Q □ R₀)) ⊑D ((P □ Q) □ R₀)
□-assoc-⊒D P Q R₀ d with □-div-elim {P = P □ Q} {Q = R₀} d
... | inj₂ dR = □-div-intro-R {P = P} {Q = Q □ R₀} (□-div-intro-R {P = Q} {Q = R₀} dR)
... | inj₁ dPQ with □-div-elim {P = P} {Q = Q} dPQ
...   | inj₁ dP = □-div-intro-L {P = P} {Q = Q □ R₀} dP
...   | inj₂ dQ = □-div-intro-R {P = P} {Q = Q □ R₀} (□-div-intro-L {P = Q} {Q = R₀} dQ)

-------------------------------------------------------------------------------------
-- □-assoc-⊑D : divergences (P□(Q□R₀)) ⊆ divergences ((P□Q)□R₀)
-------------------------------------------------------------------------------------

□-assoc-⊑D : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
           → ((P □ Q) □ R₀) ⊑D (P □ (Q □ R₀))
□-assoc-⊑D P Q R₀ d with □-div-elim {P = P} {Q = Q □ R₀} d
... | inj₁ dP = □-div-intro-L {P = P □ Q} {Q = R₀} (□-div-intro-L {P = P} {Q = Q} dP)
... | inj₂ dQR with □-div-elim {P = Q} {Q = R₀} dQR
...   | inj₁ dQ = □-div-intro-L {P = P □ Q} {Q = R₀} (□-div-intro-R {P = P} {Q = Q} dQ)
...   | inj₂ dR = □-div-intro-R {P = P □ Q} {Q = R₀} dR

-------------------------------------------------------------------------------------
-- THE NESTED √-SLIDE BRIDGE (unblocks the □-assoc failures τ-case):
--   failures ((P'□Q)□R₀) ⊆ failures ((P'▷Q)□R₀)   when force Q ≡ ret r, P' live.
-- This is the (·□R₀)-congruence of the single-level □→▷-term.  Proved by DIRECT
-- induction (NOT via □ failures-monotonicity, which is unprovable-at-[] through elim):
--   • the refl base is VACUOUS — P'□Q (Q≡ret, P' live) is never stable (□-Rret-unstable);
--   • □→▷-term-step-τ / □→▷-term-step-ev map every (P'□Q)-step to a (P'▷Q)-step reaching
--     the SAME state, so each outer step is converted-and-prepended and the tail reused;
--   • only the chQ case (R₀ itself steps) recurses.
-------------------------------------------------------------------------------------

-- force (P'□Q) is react (nonret) when P' is live and Q terminated
□-Lret-nonret : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r : R}
              → NonRet (PTree.force P) → PTree.force Q ≡ ret r
              → NonRet (PTree.force (P □ Q))
□-Lret-nonret-go : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {r : R}
                 → NonRet (PTree.force P) → PTree.force Q ≡ ret r
                 → (nP : NodeKind E (ExtI E) R) → PTree.force P ≡ nP
                 → NonRet (PTree.force (P □ Q))
□-Lret-nonret-go P Q ntP eqQ (sil P₁)      eqP = subst NonRet (sym (fL-E {P = P} {Q = Q} eqP eqQ)) tt
□-Lret-nonret-go P Q ntP eqQ (react vP τcP) eqP = subst NonRet (sym (fL-F {P = P} {Q = Q} eqP eqQ)) tt
□-Lret-nonret-go P Q ntP eqQ (ret r)       eqP = ⊥-elim (subst NonRet eqP ntP)

□-Lret-nonret P Q ntP eqQ = □-Lret-nonret-go P Q ntP eqQ (PTree.force P) refl

-- force (P'▷Q) is react (nonret) when P' is live — and we expose the witnesses
▷-live-react : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
            → NonRet (PTree.force P)
            → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
              Σ[ τc ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                (PTree.force (P ▷ Q) ≡ react v τc)
▷-live-react-go : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
               → NonRet (PTree.force P)
               → (nP : NodeKind E (ExtI E) R) → PTree.force P ≡ nP
               → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
                 Σ[ τc ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                   (PTree.force (P ▷ Q) ≡ react v τc)
▷-live-react-go P Q ntP (sil P₁)      eqP = _ , _ , force-▷-sil  {P = P} {Q = Q} eqP
▷-live-react-go P Q ntP (react vP τcP) eqP = _ , _ , force-▷-react {P = P} {Q = Q} eqP
▷-live-react-go P Q ntP (ret r)       eqP = ⊥-elim (subst NonRet eqP ntP)

▷-live-react P Q ntP = ▷-live-react-go P Q ntP (PTree.force P) refl

-- both-live τ-inversion: a τ-step of P□Q with both operands live is a choice on one side
-- (mirrors □-τ-elim's sil/react × sil/react rows, but discharges the ret rows by NonRet)
□-live-τ-inv : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → NonRet (PTree.force P) → NonRet (PTree.force Q) → (P □ Q) ─[ τ ]─► M
             → (Σ[ P' ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P') × (M ≡ P' □ Q)))
             ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] ((Q ─[ τ ]─► Q') × (M ≡ P □ Q')))
□-live-τ-inv P Q ntP ntQ step with PTree.force P in eqP | PTree.force Q in eqQ | ntP | ntQ
... | sil P' | sil Q' | _ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (sil Q') P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₁ (P'' , viewT-τ eqP veq , m≡)
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (Q'' , viewT-τ eqQ veq , m≡)
... | sil P' | react vQ τcQ | _ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₁ (P'' , viewT-τ eqP veq , m≡)
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (Q'' , viewT-τ eqQ veq , m≡)
... | react vP τcP | sil Q' | _ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₁ (P'' , viewT-τ eqP veq , m≡)
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (Q'' , viewT-τ eqQ veq , m≡)
... | react vP τcP | react vQ τcQ | _ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₁ (P'' , viewT-τ eqP veq , m≡)
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (Q'' , viewT-τ eqQ veq , m≡)
... | ret _ | _      | () | _
... | _     | ret _  | _  | ()

-- the bridge itself
□→▷-term-□R : ⦃ _ : DecEq R ⦄ (P' Q R₀ : PTree E (ExtI E) R) {r : R}
              {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
            → NonRet (PTree.force P') → PTree.force Q ≡ ret r
            → ((P' □ Q) □ R₀) ⟹⟨ s ⟩ W → Refuses W X
            → failures ((P' ▷ Q) □ R₀) s X
□→▷-term-□R P' Q R₀ ntP' eqQ ⟹-refl ref =
  ⊥-elim (□-Rret-unstable P' Q ntP' eqQ
            (proj₁ (proj₁ (refuses-□-split {P = P' □ Q} {Q = R₀} ref))))
□→▷-term-□R P' Q R₀ ntP' eqQ (⟹-τ step rest) ref with PTree.force R₀ in eqR
... | ret r₀
      with □-Rret-τ-inv (P' □ Q) R₀ (□-Lret-nonret P' Q ntP' eqQ) eqR step
...   | inj₁ refl =
        _ , ⟹-τ (□-τ-toQ (P' ▷ Q) R₀
                   (subst NonRet (sym (proj₂ (proj₂ (▷-live-react P' Q ntP')))) tt) eqR)
                 rest , ref
...   | inj₂ (A' , Astep , refl) =
        _ , ⟹-τ (□-τ-toslide (P' ▷ Q) R₀ (□→▷-term-step-τ P' Q ntP' eqQ Astep) eqR) rest , ref
□→▷-term-□R P' Q R₀ ntP' eqQ (⟹-τ step rest) ref | sil R₀'
      with □-live-τ-inv (P' □ Q) R₀ (□-Lret-nonret P' Q ntP' eqQ) (subst NonRet (sym eqR) tt) step
...   | inj₁ (A' , Astep , refl) =
        _ , ⟹-τ (□-τ-tochoice (P' ▷ Q) R₀ (□→▷-term-step-τ P' Q ntP' eqQ Astep) eqR tt) rest , ref
...   | inj₂ (R₀′ , Rstep , refl) =
        let (v , τc , eqB)        = ▷-live-react P' Q ntP'
            (W₂ , reach₂ , ref₂)  = □→▷-term-□R P' Q R₀′ ntP' eqQ rest ref
        in _ , ⟹-τ (□-τ-tochoice-R (P' ▷ Q) R₀ Rstep eqB tt) reach₂ , ref₂
□→▷-term-□R P' Q R₀ ntP' eqQ (⟹-τ step rest) ref | react vR τcR
      with □-live-τ-inv (P' □ Q) R₀ (□-Lret-nonret P' Q ntP' eqQ) (subst NonRet (sym eqR) tt) step
...   | inj₁ (A' , Astep , refl) =
        _ , ⟹-τ (□-τ-tochoice (P' ▷ Q) R₀ (□→▷-term-step-τ P' Q ntP' eqQ Astep) eqR tt) rest , ref
...   | inj₂ (R₀′ , Rstep , refl) =
        let (v , τc , eqB)        = ▷-live-react P' Q ntP'
            (W₂ , reach₂ , ref₂)  = □→▷-term-□R P' Q R₀′ ntP' eqQ rest ref
        in _ , ⟹-τ (□-τ-tochoice-R (P' ▷ Q) R₀ Rstep eqB tt) reach₂ , ref₂
□→▷-term-□R P' Q R₀ ntP' eqQ (⟹-ev step rest) ref with □-ev-elim (P' □ Q) R₀ step
... | evP Pev = _ , □-ev-toL (P' ▷ Q) R₀ (□→▷-term-step-ev P' Q ntP' eqQ Pev) rest , ref
... | evQ Qev = _ , □-ev-toR (P' ▷ Q) R₀ Qev rest , ref
... | evPQ {P₁ = A₁} {Q₁ = R₀₁} Pev Qev with rest
...   | ⟹-refl          = ⊥-elim (⊓-unstable A₁ R₀₁ (proj₁ ref))
...   | ⟹-ev step₀ _    = ⊥-elim (⊓-no-ev step₀)
...   | ⟹-τ step₀ rest₀ with ⊓-τ-inv A₁ R₀₁ step₀
...     | inj₁ refl =
          _ , □-ev-toL (P' ▷ Q) R₀ (□→▷-term-step-ev P' Q ntP' eqQ Pev) rest₀ , ref
...     | inj₂ refl =
          _ , □-ev-toR (P' ▷ Q) R₀ Qev rest₀ , ref

-------------------------------------------------------------------------------------
-- □-Rlive-τ-inv : τ-step inversion of P □ Q₂ when the RIGHT operand Q₂ is live (the
-- case that arises with Q₂ = Q□R₀ in the associativity transfer, since □ is always
-- react).  Mirrors □-Rret-τ-inv but for a live right operand: cP commit (P terminated),
-- chP / chQ choice, or sQP slide (P terminated, Q₂ slides).  (cQ / sPQ need Q₂ ≡ ret,
-- excluded by NonRet.)
-------------------------------------------------------------------------------------
□-Rlive-τ-inv : ⦃ _ : DecEq R ⦄ (P Q₂ : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
              → NonRet (PTree.force Q₂) → (P □ Q₂) ─[ τ ]─► M
              → (Σ[ r ∈ R ] (PTree.force P ≡ ret r × M ≡ P))
              ⊎ (Σ[ P' ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P') × (M ≡ P' □ Q₂)))
              ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] ((Q₂ ─[ τ ]─► Q') × (M ≡ P □ Q')))
              ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
                   ((Q₂ ─[ τ ]─► Q') × (PTree.force P ≡ ret r) × (M ≡ Q' ▷ P)))
□-Rlive-τ-inv P Q₂ ntQ2 step with PTree.force P in eqP | PTree.force Q₂ in eqQ | ntQ2
... | ret rP | sil Q' | _ =
      case react-τ-inv (fL-C {P = P} {Q = Q₂} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-RQ-elim P (sil Q') {i = i} {a = a} breq of λ where
          (inj₁ m≡P) → inj₁ (rP , refl , m≡P)
          (inj₂ (j , a' , Q'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (Q'' , rP , viewT-τ eqQ veq , refl , m≡)))
... | ret rP | react vQ τcQ | _ =
      case react-τ-inv (fL-D {P = P} {Q = Q₂} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} breq of λ where
          (inj₁ m≡P) → inj₁ (rP , refl , m≡P)
          (inj₂ (j , a' , Q'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (Q'' , rP , viewT-τ eqQ veq , refl , m≡)))
... | sil P' | sil Q' | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q₂} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (sil Q') P Q₂ {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡)))
... | sil P' | react vQ τcQ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q₂} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) P Q₂ {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡)))
... | react vP τcP | sil Q' | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q₂} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') P Q₂ {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡)))
... | react vP τcP | react vQ τcQ | _ =
      case react-τ-inv (fL-G {P = P} {Q = Q₂} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) P Q₂ {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡)))
... | _ | ret _ | ()

-------------------------------------------------------------------------------------
-- □-τ-inv-full : the FORCE-CARRYING τ-step inversion of P □ Q (the generic □-τ-elim
-- drops the force premises needed to build the regrouped target).  Six shapes, each
-- carrying its force witnesses:  cP/cQ (commit to a terminated operand), chP/chQ
-- (choice, the other operand live), sPQ/sQP (slide over a terminated operand).
-------------------------------------------------------------------------------------
□-τ-inv-full : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → (P □ Q) ─[ τ ]─► M
             → (Σ[ rP ∈ R ] (PTree.force P ≡ ret rP × M ≡ P))
             ⊎ (Σ[ rQ ∈ R ] (PTree.force Q ≡ ret rQ × M ≡ Q))
             ⊎ (Σ[ P' ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P') × (M ≡ P' □ Q)))
             ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] ((Q ─[ τ ]─► Q') × (M ≡ P □ Q')))
             ⊎ (Σ[ P' ∈ PTree E (ExtI E) R ] Σ[ rQ ∈ R ]
                  ((P ─[ τ ]─► P') × (PTree.force Q ≡ ret rQ) × (M ≡ P' ▷ Q)))
             ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] Σ[ rP ∈ R ]
                  ((Q ─[ τ ]─► Q') × (PTree.force P ≡ ret rP) × (M ≡ Q' ▷ P)))
□-τ-inv-full P Q step with PTree.force P in eqP | PTree.force Q in eqQ
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = ⊥-elim (ret-no-τ (fL-A {P = P} {Q = Q} eqP eqQ) step)
...   | no ¬eq =
        case react-τ-inv (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) step of λ where
          (i , a , breq) → case br2-elim P Q {i = i} {a = a} breq of λ where
            (inj₁ m≡P) → inj₁ (rP , refl , m≡P)
            (inj₂ m≡Q) → inj₂ (inj₁ (rQ , refl , m≡Q))
□-τ-inv-full P Q step | ret rP | sil Q' =
      case react-τ-inv (fL-C {P = P} {Q = Q} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-RQ-elim P (sil Q') {i = i} {a = a} breq of λ where
          (inj₁ m≡P) → inj₁ (rP , refl , m≡P)
          (inj₂ (j , a' , Q'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (Q'' , rP , viewT-τ eqQ veq , refl , m≡)))))
□-τ-inv-full P Q step | ret rP | react vQ τcQ =
      case react-τ-inv (fL-D {P = P} {Q = Q} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} breq of λ where
          (inj₁ m≡P) → inj₁ (rP , refl , m≡P)
          (inj₂ (j , a' , Q'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (Q'' , rP , viewT-τ eqQ veq , refl , m≡)))))
□-τ-inv-full P Q step | sil P' | ret rQ =
      case react-τ-inv (fL-E {P = P} {Q = Q} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-PR-elim (sil P') Q {i = i} {a = a} breq of λ where
          (inj₁ m≡Q) → inj₂ (inj₁ (rQ , refl , m≡Q))
          (inj₂ (j , a' , P'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (P'' , rQ , viewT-τ eqP veq , refl , m≡)))))
□-τ-inv-full P Q step | react vP τcP | ret rQ =
      case react-τ-inv (fL-F {P = P} {Q = Q} eqP eqQ) step of λ where
        (i , a , breq) → case □-slide-PR-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
          (inj₁ m≡Q) → inj₂ (inj₁ (rQ , refl , m≡Q))
          (inj₂ (j , a' , P'' , veq , m≡)) →
            inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (P'' , rQ , viewT-τ eqP veq , refl , m≡)))))
□-τ-inv-full P Q step | sil P' | sil Q' =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (sil Q') P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡)))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡))))
□-τ-inv-full P Q step | sil P' | react vQ τcQ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡)))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡))))
□-τ-inv-full P Q step | react vP τcP | sil Q' =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡)))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡))))
□-τ-inv-full P Q step | react vP τcP | react vQ τcQ =
      case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
        (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
          (inj₁ (j , a' , P'' , veq , m≡)) → inj₂ (inj₂ (inj₁ (P'' , viewT-τ eqP veq , m≡)))
          (inj₂ (j , a' , Q'' , veq , m≡)) → inj₂ (inj₂ (inj₂ (inj₁ (Q'' , viewT-τ eqQ veq , m≡))))

-------------------------------------------------------------------------------------
-- NON-EMPTY failures INTRO: failures A (e∷s) X → failures (A□R₀)(e∷s) X (and mirror).
-- The leading event breaks the empty-trace refusal-intersection obstruction: lift the
-- leading τ's via □-fail-τ-pre-L/-R (√-slide handled there), commit the event via
-- □-ev-toL/toR (which drops the other operand), then reuse the tail unchanged.
-------------------------------------------------------------------------------------
□-fail-intro-cons-L : ⦃ _ : DecEq R ⦄ (A R₀ : PTree E (ExtI E) R) {e : Event√ R}
                      {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                    → A ⟹⟨ e ∷ s ⟩ W → Refuses W X → failures ((A □ R₀)) (e ∷ s) X
□-fail-intro-cons-L A R₀ (⟹-τ {q = A'} step rest) ref =
  let (W₂ , reach₂ , ref₂) = □-fail-intro-cons-L A' R₀ rest ref
  in □-fail-τ-pre-L A A' R₀ (τ→NonRet step) step reach₂ ref₂
□-fail-intro-cons-L A R₀ (⟹-ev step rest) ref =
  _ , □-ev-toL A R₀ step rest , ref

□-fail-intro-cons-R : ⦃ _ : DecEq R ⦄ (A R₀ : PTree E (ExtI E) R) {e : Event√ R}
                      {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                    → R₀ ⟹⟨ e ∷ s ⟩ W → Refuses W X → failures ((A □ R₀)) (e ∷ s) X
□-fail-intro-cons-R A R₀ (⟹-τ {q = R₀'} step rest) ref =
  let (W₂ , reach₂ , ref₂) = □-fail-intro-cons-R A R₀' rest ref
  in □-fail-τ-pre-R A R₀ R₀' (τ→NonRet step) step reach₂ ref₂
□-fail-intro-cons-R A R₀ (⟹-ev step rest) ref =
  _ , □-ev-toR A R₀ step rest , ref

-------------------------------------------------------------------------------------
-- NIL-trace failures of □ is the CONJUNCTION of operand nil-failures (the empty-trace
-- refusal-intersection).  This is what makes []-associativity a ×-reassociation.
-- Forward (→): a stable refuser reached by τ-only projects to BOTH operands.  The
-- slide/commit τ-cases (cP/cQ/sPQ/sQP) are VACUOUS at [] because ret/▷ never reach a
-- stable state by τ-only.
-------------------------------------------------------------------------------------

-- A ▷ B with B terminated can never reach a stable state by τ-only (timeout → ret,
-- slide stays ▷; neither is stable).
▷-ret-noreach-stable : ⦃ _ : DecEq R ⦄ (A B : PTree E (ExtI E) R) {r : R}
                       {W : PTree E (ExtI E) R}
                     → PTree.force B ≡ ret r → (A ▷ B) ⟹⟨ [] ⟩ W → isStable W → ⊥
▷-ret-noreach-stable A B eqB ⟹-refl stW = ▷-unstable A B stW
▷-ret-noreach-stable A B eqB (⟹-τ step rest) stW with ▷-τ-elim A B step
... | inj₂ (A' , Astep , refl) = ▷-ret-noreach-stable A' B eqB rest stW
... | inj₁ refl with rest
...   | ⟹-refl        = stable-not-ret {t = B} eqB stW
...   | ⟹-τ step′ _   = ret-no-τ eqB step′

□-fail-nil-→ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
               {W : PTree E (ExtI E) R}
             → (P □ Q) ⟹⟨ [] ⟩ W → Refuses W X
             → failures P [] X × failures Q [] X
□-fail-nil-→ P Q ⟹-refl ref with refuses-□-split {P = P} {Q = Q} ref
... | refP , refQ = (P , ⟹-refl , refP) , (Q , ⟹-refl , refQ)
□-fail-nil-→ P Q (⟹-τ step rest) ref with □-τ-inv-full P Q step
... | inj₁ (rP , eqP , refl) with rest
...   | ⟹-refl       = ⊥-elim (stable-not-ret {t = P} eqP (proj₁ ref))
...   | ⟹-τ step′ _  = ⊥-elim (ret-no-τ eqP step′)
□-fail-nil-→ P Q (⟹-τ step rest) ref | inj₂ (inj₁ (rQ , eqQ , refl)) with rest
...   | ⟹-refl       = ⊥-elim (stable-not-ret {t = Q} eqQ (proj₁ ref))
...   | ⟹-τ step′ _  = ⊥-elim (ret-no-τ eqQ step′)
□-fail-nil-→ P Q (⟹-τ step rest) ref | inj₂ (inj₂ (inj₁ (P' , Pτ , refl)))
  with □-fail-nil-→ P' Q rest ref
... | fP' , fQ = fail-τ-prepend Pτ fP' , fQ
□-fail-nil-→ P Q (⟹-τ step rest) ref | inj₂ (inj₂ (inj₂ (inj₁ (Q' , Qτ , refl))))
  with □-fail-nil-→ P Q' rest ref
... | fP , fQ' = fP , fail-τ-prepend Qτ fQ'
□-fail-nil-→ P Q (⟹-τ step rest) ref | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (P' , rQ , Pτ , eqQ , refl))))) =
  ⊥-elim (▷-ret-noreach-stable P' Q eqQ rest (proj₁ ref))
□-fail-nil-→ P Q (⟹-τ step rest) ref | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (Q' , rP , Qτ , eqP , refl))))) =
  ⊥-elim (▷-ret-noreach-stable Q' P eqP rest (proj₁ ref))

-- Converse (←): join two operand nil-failures into a P□Q nil-failure.  Lift P's τ-path
-- into P□Q keeping Q (□-τ*-L, Q live since failures Q []X forces NonRet), then Q's
-- τ-path keeping the stabilised W_P (□-τ*-R), and join the two stable refusers.
⟹-[]-trans : ⦃ _ : DecEq R ⦄ {P M : PTree E (ExtI E) R} {s : List (Event√ R)}
             {W : PTree E (ExtI E) R}
           → P ⟹⟨ [] ⟩ M → M ⟹⟨ s ⟩ W → P ⟹⟨ s ⟩ W
⟹-[]-trans ⟹-refl            tr = tr
⟹-[]-trans (⟹-τ step rest)   tr = ⟹-τ step (⟹-[]-trans rest tr)

fail-nil-NonRet-go : ⦃ _ : DecEq R ⦄ (Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                     (nQ : NodeKind E (ExtI E) R) → PTree.force Q ≡ nQ
                   → failures Q [] X → NonRet (PTree.force Q)
fail-nil-NonRet-go Q (sil _)    eqQ f                          = subst NonRet (sym eqQ) tt
fail-nil-NonRet-go Q (react _ _) eqQ f                          = subst NonRet (sym eqQ) tt
fail-nil-NonRet-go Q (ret r)    eqQ (W , ⟹-refl , ref)         = ⊥-elim (stable-not-ret {t = Q} eqQ (proj₁ ref))
fail-nil-NonRet-go Q (ret r)    eqQ (W , ⟹-τ step _ , ref)     = ⊥-elim (ret-no-τ eqQ step)

fail-nil-NonRet : ⦃ _ : DecEq R ⦄ (Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
                → failures Q [] X → NonRet (PTree.force Q)
fail-nil-NonRet Q f = fail-nil-NonRet-go Q (PTree.force Q) refl f

□-τ*-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) (nQ : NodeKind E (ExtI E) R)
         {P* : PTree E (ExtI E) R}
       → PTree.force Q ≡ nQ → NonRet nQ → P ⟹⟨ [] ⟩ P* → (P □ Q) ⟹⟨ [] ⟩ (P* □ Q)
□-τ*-L P Q nQ eqQ ntQ ⟹-refl              = ⟹-refl
□-τ*-L P Q nQ eqQ ntQ (⟹-τ {q = P'} step rest) =
  ⟹-τ (□-τ-tochoice P Q step eqQ ntQ) (□-τ*-L P' Q nQ eqQ ntQ rest)

□-τ*-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) (nP : NodeKind E (ExtI E) R)
         {Q* : PTree E (ExtI E) R}
       → PTree.force P ≡ nP → NonRet nP → Q ⟹⟨ [] ⟩ Q* → (P □ Q) ⟹⟨ [] ⟩ (P □ Q*)
□-τ*-R P Q nP eqP ntP ⟹-refl              = ⟹-refl
□-τ*-R P Q nP eqP ntP (⟹-τ {q = Q'} step rest) =
  ⟹-τ (□-τ-tochoice-R P Q step eqP ntP) (□-τ*-R P Q' nP eqP ntP rest)

□-fail-nil-← : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {X : Event√ R → Set ℓx}
             → failures P [] X → failures Q [] X → failures (P □ Q) [] X
□-fail-nil-← P Q (W_P , reachP , refP) (W_Q , reachQ , refQ)
  with stable-react {P = W_P} (proj₁ refP)
... | vWP , τcWP , eqWP , _ =
      (W_P □ W_Q)
      , ⟹-[]-trans (□-τ*-L P Q (PTree.force Q) refl (fail-nil-NonRet Q (W_Q , reachQ , refQ)) reachP)
                    (□-τ*-R W_P Q (react vWP τcWP) eqWP tt reachQ)
      , refuses-□-join {P = W_P} {Q = W_Q} refP refQ

-------------------------------------------------------------------------------------
-- THE FAILURES TRANSFER — now pure routing.  Case the trace:
--   []     : nil-conjunction (□-fail-nil-→/←) + ×-reassociation;
--   e ∷ s' : □-failures-elim (forward ⊎) + ⊎-reassociation + □-fail-intro-cons-L/R.
-------------------------------------------------------------------------------------
□-assoc-fail-RL : ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                → failures (P □ (Q □ R₀)) s X → failures ((P □ Q) □ R₀) s X
□-assoc-fail-RL P Q R₀ {s = []} (W , reach , ref)
  with □-fail-nil-→ P (Q □ R₀) reach ref
... | fP , (W' , reach' , ref') with □-fail-nil-→ Q R₀ reach' ref'
...   | fQ , fR = □-fail-nil-← (P □ Q) R₀ (□-fail-nil-← P Q fP fQ) fR
□-assoc-fail-RL P Q R₀ {s = x ∷ s'} (W , reach , ref)
  with □-failures-elim P (Q □ R₀) reach ref
... | inj₁ (W_P , reachP , refP) =
      let (W₁ , reach₁ , ref₁) = □-fail-intro-cons-L P Q reachP refP
      in □-fail-intro-cons-L (P □ Q) R₀ reach₁ ref₁
... | inj₂ (W' , reach' , ref') with □-failures-elim Q R₀ reach' ref'
...   | inj₁ (W_Q , reachQ , refQ) =
        let (W₁ , reach₁ , ref₁) = □-fail-intro-cons-R P Q reachQ refQ
        in □-fail-intro-cons-L (P □ Q) R₀ reach₁ ref₁
...   | inj₂ (W_R , reachR , refR) = □-fail-intro-cons-R (P □ Q) R₀ reachR refR

□-assoc-fail-LR : ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                → failures ((P □ Q) □ R₀) s X → failures (P □ (Q □ R₀)) s X
□-assoc-fail-LR P Q R₀ {s = []} (W , reach , ref)
  with □-fail-nil-→ (P □ Q) R₀ reach ref
... | (W' , reach' , ref') , fR with □-fail-nil-→ P Q reach' ref'
...   | fP , fQ = □-fail-nil-← P (Q □ R₀) fP (□-fail-nil-← Q R₀ fQ fR)
□-assoc-fail-LR P Q R₀ {s = x ∷ s'} (W , reach , ref)
  with □-failures-elim (P □ Q) R₀ reach ref
... | inj₂ (W_R , reachR , refR) =
      let (W₁ , reach₁ , ref₁) = □-fail-intro-cons-R Q R₀ reachR refR
      in □-fail-intro-cons-R P (Q □ R₀) reach₁ ref₁
... | inj₁ (W' , reach' , ref') with □-failures-elim P Q reach' ref'
...   | inj₁ (W_P , reachP , refP) = □-fail-intro-cons-L P (Q □ R₀) reachP refP
...   | inj₂ (W_Q , reachQ , refQ) =
        let (W₁ , reach₁ , ref₁) = □-fail-intro-cons-L Q R₀ reachQ refQ
        in □-fail-intro-cons-R P (Q □ R₀) reach₁ ref₁

-------------------------------------------------------------------------------------
-- ASSEMBLY: external-choice associativity in the failures-divergences model.
--   □-assoc-FD : ((P □ Q) □ R₀) ≈FD (P □ (Q □ R₀))
-- failures⊥ = failures ⊎ divergences; route each summand to its transfer (failures via
-- □-assoc-fail-RL/LR, divergences via the already-proven □-assoc-⊑D/⊒D).
-------------------------------------------------------------------------------------
□-assoc-⊑F⊥ : ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
            → ((P □ Q) □ R₀) ⊑F⊥ (P □ (Q □ R₀))
□-assoc-⊑F⊥ P Q R₀ (inj₁ f) = inj₁ (□-assoc-fail-RL P Q R₀ f)
□-assoc-⊑F⊥ P Q R₀ (inj₂ d) = inj₂ (□-assoc-⊑D P Q R₀ d)

□-assoc-⊒F⊥ : ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
            → (P □ (Q □ R₀)) ⊑F⊥ ((P □ Q) □ R₀)
□-assoc-⊒F⊥ P Q R₀ (inj₁ f) = inj₁ (□-assoc-fail-LR P Q R₀ f)
□-assoc-⊒F⊥ P Q R₀ (inj₂ d) = inj₂ (□-assoc-⊒D P Q R₀ d)

□-assoc-FD : ⦃ _ : DecEq R ⦄ (P Q R₀ : PTree E (ExtI E) R)
           → ((P □ Q) □ R₀) ≈FD (P □ (Q □ R₀))
□-assoc-FD P Q R₀ =
  (□-assoc-⊑F⊥ P Q R₀ , □-assoc-⊑D P Q R₀) ,
  (□-assoc-⊒F⊥ P Q R₀ , □-assoc-⊒D P Q R₀)
