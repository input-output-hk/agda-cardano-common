{-# OPTIONS --guardedness #-}

-- Failures-divergences law (U13.26, ▷-failures characterisation), FD-direct:
--
--   ▷-failures-char-FD :  (P ▷ Q)  ≈FD  ((P □ Q) ⊓ Q)        [ NonRet (force P) ]
--
-- The side-condition NonRet (force P) is ESSENTIAL: if force P = ret r the spike's ▷
-- eager-resolves (P ▷ Q = ret r), but (ret r □ Q) ⊓ Q ≠ ret r.  With P live the timeout
--   ▷-timeout P Q eqP nt : (P ▷ Q) ─[τ]→ Q  fires and is the spine of the whole proof.
--
-- It is NOT a DR-bisim: the RHS reaches the intermediate P □ Q which offers init P ∪ init Q,
-- whereas the LHS P ▷ Q only ever offers init P (it must fire the timeout to access Q).
-- ≈FD abstracts that away.  Write LHS = P ▷ Q, RHS = (P □ Q) ⊓ Q.
--
--   ≈FD = ((LHS⊇F⊥RHS, LHS⊇D RHS) , (RHS⊇F⊥LHS, RHS⊇D LHS))   (X ⊇F⊥ Y = f⊥(Y) → f⊥(X)).
--
-- EASY (RHS recovers every LHS failure⊥/divergence): decompose a failure of P▷Q into a
-- failure of P□Q (event-led / P-slide cases, via □-fail-τ-pre-L / □-ev-toL) or of Q (the
-- timeout target), then ⊓-failures←l / ⊓-failures←r; divergences via ▷-div-elim then □-div-intro.
-- HARD (LHS recovers every RHS failure⊥/divergence): the failures summand of P□Q routes
-- through the WORKER □→▷-fail, recursing on (Pc □ Qc) ⟹⟨s⟩ W carrying P▷Q ─τ*→ Pc▷Q and
-- Q ─τ*→ Qc, so a stable Pc□Qc (which refuses LESS than the unstable P▷Q would at its root)
-- is recovered by firing the timeout and reaching the stable Qc (refusing the same X).

open import Level using (Level; Lift; lift; lower)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using () renaming (tt to tt0)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open import Process_Trees using (react-injective)

module CSP.Laws.FD.SlideFailuresChar {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures; τ*-then)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; empty-div; failures⊥;
         _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures-elim; ▷-failures-elim; □-failures⊥-elim; □-div-elim;
         □-reach-div; ▷-reach-div;
         □-div-intro-L; □-div-intro-R; ▷-reach-intro-L; □-refl-fail;
         stable-no-τ; stable-not-ret; mk-stable; ▷-unstable;
         fail-τ-prepend; fail-ev-prepend; div-τ-prepend; div-ev-prepend; mk-div;
         □-ev-toL; □-fail-τ-pre-L; □→▷-term; term-fail-▷; slide-term-fail;
         □-τ-toQ; □-Rret-unstable; □-Rret-τ-inv; τ→NonRet)
open import CSP.Laws.Traces.TraceLaws E-≟
  using (force-▷-ret; force-▷-react; force-▷-sil; ▷-τ-L; ▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□τR; cP; cQ; sPQ; sQP; chP; chQ; □-τ-elim;
         □evR; evP; evQ; evPQ; □-ev-elim; ▷-τ-elim; ▷-ev-elim; ▷-timeout;
         react-τ-inv; □-mt-elim; viewT-τ)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; □-τ-tochoice; □-τ-toslide;
         fL-A; fL-B; fL-E; fL-F; fL-G; □-mt-tag0-eq; □-mt-tag1-eq;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures→; ⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r;
         ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- Set-level divergence wrappers for the slide (built from the reach-* lemmas).
-------------------------------------------------------------------------------------

-- divergences (A ▷ B) ⊆ divergences A ∪ divergences B
▷-div-elim : (A B : PTree E (ExtI E) R) {s : List (Event√ R)}
           → divergences (A ▷ B) s → divergences A s ⊎ divergences B s
▷-div-elim A B d with ▷-reach-div A B (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dA = inj₁ (subst (divergences A) (sym (d .IsDivergence.split))
                            (div-extension-closed dA))
... | inj₂ dB = inj₂ (subst (divergences B) (sym (d .IsDivergence.split))
                            (div-extension-closed dB))

-- divergences A ⊆ divergences (A ▷ B)
▷-div-intro-L : (A B : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences A s → divergences (A ▷ B) s
▷-div-intro-L A B d = subst (divergences (A ▷ B)) (sym (d .IsDivergence.split))
  (div-extension-closed (▷-reach-intro-L A B (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-- divergences B ⊆ divergences (A ▷ B) when A is non-ret: fire the timeout first.
▷-div-intro-R : (A B : PTree E (ExtI E) R) {nA : NodeKind E (ExtI E) R} {s : List (Event√ R)}
              → PTree.force A ≡ nA → NonRet nA → divergences B s → divergences (A ▷ B) s
▷-div-intro-R A B eqA ntA d = div-τ-prepend (▷-timeout A B eqA ntA) d

-------------------------------------------------------------------------------------
-- EASY direction.  RHS = (P □ Q) ⊓ Q recovers every LHS = P ▷ Q failure⊥ / divergence.
-------------------------------------------------------------------------------------

-- decompose a failure reached from P ▷ Q into a failure of P □ Q (event-led / P-slide) or
-- of Q (the timeout target).  Recurses on the P▷Q big-step; P▷Q is unstable so ⟹-refl is
-- vacuous.  A P-event lifts into P□Q (□-ev-toL); a P-slide τ lifts the recovered P'□Q
-- failure back to P□Q (□-fail-τ-pre-L); the timeout τ → Q yields a failure of Q.
▷→□Q-fail : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → (P ▷ Q) ⟹⟨ s ⟩ W → Refuses W X
  → failures (P □ Q) s X ⊎ failures Q s X
▷→□Q-fail P Q ⟹-refl (st , _) = ⊥-elim (▷-unstable P Q st)
▷→□Q-fail P Q (⟹-τ step rest) ref with ▷-τ-elim P Q step
... | inj₁ refl = inj₂ (_ , rest , ref)
... | inj₂ (P' , Pτ , refl) with ▷→□Q-fail P' Q rest ref
...   | inj₁ (W₂ , r₂ , rf₂) = inj₁ (□-fail-τ-pre-L P P' Q (τ→NonRet Pτ) Pτ r₂ rf₂)
...   | inj₂ fQ              = inj₂ fQ
▷→□Q-fail P Q (⟹-ev step rest) ref =
  inj₁ (_ , □-ev-toL P Q (▷-ev-elim P Q step) rest , ref)

-- ⊆F⊥ (component 3): RHS recovers every LHS stable failure⊥.
char-⊆F⊥ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
         → ((P □ Q) ⊓ Q) ⊇F⊥ (P ▷ Q)
char-⊆F⊥ P Q nt (inj₁ (W , reach , ref)) with ▷→□Q-fail P Q reach ref
... | inj₁ fPQ = inj₁ (⊓-failures←l (P □ Q) Q fPQ)
... | inj₂ fQ  = inj₁ (⊓-failures←r (P □ Q) Q fQ)
char-⊆F⊥ P Q nt (inj₂ d) with ▷-div-elim P Q d
... | inj₁ dP = inj₂ (⊓-div←l (P □ Q) Q (□-div-intro-L {P = P} {Q = Q} dP))
... | inj₂ dQ = inj₂ (⊓-div←r (P □ Q) Q dQ)

-- ⊆D (component 4): RHS recovers every LHS divergence.
char-⊆D : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
        → ((P □ Q) ⊓ Q) ⊇D (P ▷ Q)
char-⊆D P Q nt d with ▷-div-elim P Q d
... | inj₁ dP = ⊓-div←l (P □ Q) Q (□-div-intro-L {P = P} {Q = Q} dP)
... | inj₂ dQ = ⊓-div←r (P □ Q) Q dQ

-------------------------------------------------------------------------------------
-- HARD ⊇D (component 2): LHS = P ▷ Q recovers every RHS = (P □ Q) ⊓ Q divergence.
-------------------------------------------------------------------------------------

char-⊇D : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
        → (P ▷ Q) ⊇D ((P □ Q) ⊓ Q)
char-⊇D P Q nt d with ⊓-div→ (P □ Q) Q d
... | inj₂ dQ = ▷-div-intro-R P Q refl nt dQ
... | inj₁ dPQ with □-div-elim {P = P} {Q = Q} dPQ
...   | inj₁ dP = ▷-div-intro-L P Q dP
...   | inj₂ dQ = ▷-div-intro-R P Q refl nt dQ

-------------------------------------------------------------------------------------
-- HARD ⊇F⊥ (component 1) — THE CRUX.  LHS = P ▷ Q recovers every RHS = (P□Q)⊓Q failure.
--
-- The failures summand routes through the WORKER □→▷-fail.  Helpers first.
-------------------------------------------------------------------------------------

-- R-mirror of □-offers-L : a visible step of Q lifts to an offer of P □ Q.
□-offers-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
             {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             {τcP τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             {e : Event√ R} {M : PTree E (ExtI E) R}
           → PTree.force P ≡ react vP τcP → PTree.force Q ≡ react vQ τcQ
           → Q ─[ ev e ]─► M → Offers (P □ Q) e
□-offers-R P Q eqP eqQx (sRet eqQ) = case trans (sym eqQx) eqQ of λ ()
□-offers-R P Q {vP = vP} eqP eqQx (sVis {v = vQ} {at = at} {a = a} eqQ brQ) with vP at a in eqVP
... | nothing = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt0 tt0) (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)
... | just P₁ = _ , sVis (fL-G {P = P} {Q = Q} eqP eqQ tt0 tt0) (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ)

-- R-mirror of □-refl-fail : a stable P □ Q refuses X ⇒ Q refuses X at [].
-- (We only need the Q-side: every stable Pc□Qc has Qc stable & refusing X, so the joint
-- refusal is recoverable from Q after the timeout.)
□-refl-fail-R : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
              → Refuses (P □ Q) X → failures Q [] X
□-refl-fail-R {P = P} {Q = Q} (st , noff) with PTree.force P in eqP | PTree.force Q in eqQ
□-refl-fail-R {P = P} {Q = Q} (st , noff) | ret rP | ret rQ with rP ≟ rQ
... | yes refl = ⊥-elim (lower st)
... | no ¬eq   = case st (Lift ℓ (Fin 2) , fin) (lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | ret rP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | ret rP | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | sil P′ | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | sil P′ | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | react vP τcP | ret rQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | react vP τcP | sil Q′ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift (fsuc fzero) , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} (st , noff) | sil P′ | react vQ τcQ =
  case st ((Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin) (lift fzero , lift fzero) of λ ()
□-refl-fail-R {P = P} {Q = Q} {X = X} (st , noff) | react vP τcP | react vQ τcQ =
  Q , ⟹-refl , stQ , refQ
  where
    qn : ∀ i a → τcQ i a ≡ nothing
    qn i a with τcQ i a in eqt
    ... | nothing = refl
    ... | just Q′ = case trans (sym (□-mt-tag1-eq {nP = react vP τcP} {nQ = react vQ τcQ}
                                                  {P = P} {Q = Q} {iₚ = i} {aₚ = a} {Q₁ = Q′} eqt))
                               (st ((Lift ℓ (Fin 2) × proj₁ i) , pair fin (proj₂ i)) (lift (fsuc fzero) , a))
                    of λ ()
    stQ : isStable Q
    stQ = mk-stable {t = Q} eqQ qn
    refQ : ∀ e → X e → ¬ Offers Q e
    refQ e xe (Q₁ , qstep) = noff e xe (□-offers-R P Q eqP eqQ qstep)

-- order-preserving slide→choice (terminated RIGHT): a τ-step of P′ ▷ Qc (Qc terminated)
-- is a τ-step of P′ □ Qc reaching the SAME state.
slide→□-τ-R : ⦃ _ : DecEq R ⦄ (P′ Qc : PTree E (ExtI E) R) {r : R} {M : PTree E (ExtI E) R}
            → PTree.force Qc ≡ ret r → (P′ ▷ Qc) ─[ τ ]─► M → (P′ □ Qc) ─[ τ ]─► M
slide→□-τ-R P′ Qc eqQc step with PTree.force P′ in eqP′
... | ret r'' = ⊥-elim (ret-no-τ-▷ step)
  where
    ret-no-τ-▷ : ∀ {M} → (P′ ▷ Qc) ─[ τ ]─► M → ⊥
    ret-no-τ-▷ (sSil eq)   = case trans (sym (force-▷-ret {P = P′} {Q = Qc} eqP′)) eq of λ ()
    ret-no-τ-▷ (sTau eq _) = case trans (sym (force-▷-ret {P = P′} {Q = Qc} eqP′)) eq of λ ()
... | sil P'' with ▷-τ-elim P′ Qc step
...   | inj₁ refl = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                        {a = lift fzero , lift fzero} (fL-E {P = P′} {Q = Qc} eqP′ eqQc) refl
...   | inj₂ (P' , Pτ , refl) = □-τ-toslide P′ Qc Pτ eqQc
slide→□-τ-R P′ Qc eqQc step | react vP τcP with ▷-τ-elim P′ Qc step
...   | inj₁ refl = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                        {a = lift fzero , lift fzero} (fL-F {P = P′} {Q = Qc} eqP′ eqQc) refl
...   | inj₂ (P' , Pτ , refl) = □-τ-toslide P′ Qc Pτ eqQc

slide→□-ev-R : ⦃ _ : DecEq R ⦄ (P′ Qc : PTree E (ExtI E) R) {r : R}
               {e′ : Event√ R} {M W : PTree E (ExtI E) R} {s : List (Event√ R)}
             → PTree.force Qc ≡ ret r → (P′ ▷ Qc) ─[ ev e′ ]─► M → M ⟹⟨ s ⟩ W
             → (P′ □ Qc) ⟹⟨ e′ ∷ s ⟩ W
slide→□-ev-R P′ Qc {r = r} eqQc step rest with ▷-ev-elim P′ Qc step
... | sVis {at = at} {a = a} eqP′v brP = ⟹-ev (sVis (fL-F {P = P′} {Q = Qc} eqP′v eqQc) brP) rest
... | sRet {x = r''} eqP′v with r'' ≟ r
...   | yes refl = ⟹-ev (sRet (fL-A {P = P′} {Q = Qc} eqP′v eqQc)) rest
...   | no ¬eq   = ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                             (fL-B {P = P′} {Q = Qc} eqP′v eqQc ¬eq) refl)
                       (⟹-ev (sRet eqP′v) rest)

-- failures of the slide P′ ▷ Qc (Qc terminated) ⊆ failures of P′ □ Qc (order preserved).
slide-term-fail-R : ⦃ _ : DecEq R ⦄ (P′ Qc : PTree E (ExtI E) R) {r : R}
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → PTree.force Qc ≡ ret r → (P′ ▷ Qc) ⟹⟨ s ⟩ W → Refuses W X → failures (P′ □ Qc) s X
slide-term-fail-R P′ Qc eqQc ⟹-refl (st , _)     = ⊥-elim (▷-unstable P′ Qc st)
slide-term-fail-R P′ Qc eqQc (⟹-τ step rest) ref = _ , ⟹-τ (slide→□-τ-R P′ Qc eqQc step) rest , ref
slide-term-fail-R P′ Qc eqQc (⟹-ev step rest) ref = _ , slide→□-ev-R P′ Qc eqQc step rest , ref

-- custom τ-inversion for Pc □ Qc with BOTH operands live (NonRet): the τ is Pc's own
-- (→ Pc'□Qc) or Qc's own (→ Pc□Qc′).  Mirrors ExtChoiceSlide.□-Sτ-inv cases (1)/(2),
-- generalised to an arbitrary live Pc.  Forces matched concretely so no slide/commit shape
-- can arise (both operands NonRet).
□-live-τ-inv : ⦃ _ : DecEq R ⦄ (Pc Qc : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
  → NonRet (PTree.force Pc) → NonRet (PTree.force Qc)
  → (Pc □ Qc) ─[ τ ]─► M
  → (Σ[ Pc′ ∈ PTree E (ExtI E) R ] ((Pc ─[ τ ]─► Pc′) × (M ≡ Pc′ □ Qc)))
  ⊎ (Σ[ Qc′ ∈ PTree E (ExtI E) R ] ((Qc ─[ τ ]─► Qc′) × (M ≡ Pc □ Qc′)))
□-live-τ-inv Pc Qc ntP ntQ step with PTree.force Pc in eqP | PTree.force Qc in eqQ
□-live-τ-inv Pc Qc ntP ntQ step | ret _ | _ = ⊥-elim ntP
□-live-τ-inv Pc Qc ntP ntQ step | sil P' | ret _ = ⊥-elim ntQ
□-live-τ-inv Pc Qc ntP ntQ step | react _ _ | ret _ = ⊥-elim ntQ
□-live-τ-inv Pc Qc ntP ntQ step | sil P' | sil Q' =
  case react-τ-inv (fL-G {P = Pc} {Q = Qc} eqP eqQ tt0 tt0) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (sil Q') Pc Qc {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , Pc' , veq , m≡)) → inj₁ (Pc' , viewT-τ {j = j} {a' = a'} eqP veq , m≡)
      (inj₂ (j , a' , Qc' , veq , m≡)) → inj₂ (Qc' , viewT-τ {j = j} {a' = a'} eqQ veq , m≡)
□-live-τ-inv Pc Qc ntP ntQ step | sil P' | react vQ τcQ =
  case react-τ-inv (fL-G {P = Pc} {Q = Qc} eqP eqQ tt0 tt0) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) Pc Qc {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , Pc' , veq , m≡)) → inj₁ (Pc' , viewT-τ {j = j} {a' = a'} eqP veq , m≡)
      (inj₂ (j , a' , Qc' , veq , m≡)) → inj₂ (Qc' , viewT-τ {j = j} {a' = a'} eqQ veq , m≡)
□-live-τ-inv Pc Qc ntP ntQ step | react vP τcP | sil Q' =
  case react-τ-inv (fL-G {P = Pc} {Q = Qc} eqP eqQ tt0 tt0) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') Pc Qc {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , Pc' , veq , m≡)) → inj₁ (Pc' , viewT-τ {j = j} {a' = a'} eqP veq , m≡)
      (inj₂ (j , a' , Qc' , veq , m≡)) → inj₂ (Qc' , viewT-τ {j = j} {a' = a'} eqQ veq , m≡)
□-live-τ-inv Pc Qc ntP ntQ step | react vP τcP | react vQ τcQ =
  case react-τ-inv (fL-G {P = Pc} {Q = Qc} eqP eqQ tt0 tt0) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) Pc Qc {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , Pc' , veq , m≡)) → inj₁ (Pc' , viewT-τ {j = j} {a' = a'} eqP veq , m≡)
      (inj₂ (j , a' , Qc' , veq , m≡)) → inj₂ (Qc' , viewT-τ {j = j} {a' = a'} eqQ veq , m≡)

-------------------------------------------------------------------------------------
-- THE WORKER □→▷-fail : failures(Pc □ Qc) ⊆ failures(P ▷ Q).
-- Recurses on (Pc □ Qc) ⟹⟨s⟩ W, carrying:
--   pref : (P ▷ Q) ─[τ*]─► (Pc ▷ Q)   (P's internal slide evolution; Q fixed)
--   qw   : Q ─[τ*]─► Qc                (Q's internal evolution, replayed AFTER the timeout)
-- and the side-condition nt : NonRet (force P) (so the ROOT timeout P▷Q ─τ→ Q always fires).
--
-- Routing principle: the timeout P▷Q ─τ→ Q fires from the ROOT P (NonRet), reaching the
-- ORIGINAL Q; any Qc-side behaviour is replayed via qw after that timeout.  Pc-side events
-- replay via pref + the slide's own offer (▷-ev-L).  A stable Pc□Qc refuses X jointly with
-- Qc, so its refusal is recovered through Q (□-refl-fail-R).
-------------------------------------------------------------------------------------

-- route a Qc-side behaviour back through the root timeout: P▷Q ─τ→ Q ─τ*(qw)→ Qc ⟹ W.
route-Q : ⦃ _ : DecEq R ⦄ (P Q Qc : PTree E (ExtI E) R) → NonRet (PTree.force P) →
    {s : List (Event√ R)} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc → Qc ⟹⟨ s ⟩ W → (P ▷ Q) ⟹⟨ s ⟩ W
route-Q P Q Qc nt qw qreach = ⟹-τ (▷-timeout P Q refl nt) (τ*-then qw qreach)

-- forward declarations of the mutually-recursive worker pieces (Pc live).
□→▷-fail : ⦃ _ : DecEq R ⦄ (P Q Pc Qc : PTree E (ExtI E) R) → NonRet (PTree.force P) →
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → (P ▷ Q) ─[τ*]─► (Pc ▷ Q) → Q ─[τ*]─► Qc
  → (Pc □ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures (P ▷ Q) s X

□→▷-fail-τ-Plive : ⦃ _ : DecEq R ⦄ (P Q Pc Qc : PTree E (ExtI E) R)
    → NonRet (PTree.force P) → NonRet (PTree.force Pc) →
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {M W : PTree E (ExtI E) R}
  → (P ▷ Q) ─[τ*]─► (Pc ▷ Q) → Q ─[τ*]─► Qc
  → (Pc □ Qc) ─[ τ ]─► M → M ⟹⟨ s ⟩ W → Refuses W X
  → failures (P ▷ Q) s X

□→▷-fail-ev : ⦃ _ : DecEq R ⦄ (P Q Pc Qc : PTree E (ExtI E) R) → NonRet (PTree.force P) →
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {M W : PTree E (ExtI E) R} {e : Event√ R}
  → (P ▷ Q) ─[τ*]─► (Pc ▷ Q) → Q ─[τ*]─► Qc
  → (Pc □ Qc) ─[ ev e ]─► M → M ⟹⟨ s ⟩ W → Refuses W X
  → failures (P ▷ Q) (e ∷ s) X

-- the slide residual worker: Pc' slides over a TERMINATED Qc (force Qc ≡ ret r).  Recurses
-- on the slide big-step (structurally), routing Pc'-events via pref and the √-timeout via Q.
▷→▷-fail : ⦃ _ : DecEq R ⦄ (P Q Pc′ Qc : PTree E (ExtI E) R) {r : R} → NonRet (PTree.force P) →
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → PTree.force Qc ≡ ret r
  → (P ▷ Q) ─[τ*]─► (Pc′ ▷ Q) → Q ─[τ*]─► Qc
  → (Pc′ ▷ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures (P ▷ Q) s X

-- Pc terminated (force Pc ≡ ret r).  Then Pc ▷ Q forces to ret r (eager).  Split the
-- Pc□Qc failure with □-failures-elim: the Pc-side (a √r, since ret is not stable so no
-- ⟹-refl refusal — handled inside term-fail-▷) lifts to failures(Pc▷Q) via term-fail-▷,
-- prefixed by pref; the Qc-side routes through the root timeout (route-Q).
□→▷-Pret : ⦃ _ : DecEq R ⦄ (P Q Pc Qc : PTree E (ExtI E) R) {r : R} → NonRet (PTree.force P) →
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → PTree.force Pc ≡ ret r
  → (P ▷ Q) ─[τ*]─► (Pc ▷ Q) → Q ─[τ*]─► Qc
  → (Pc □ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures (P ▷ Q) s X
□→▷-Pret P Q Pc Qc nt eqPc pref qw reach ref with □-failures-elim Pc Qc reach ref
... | inj₁ (W₂ , pcr , rf₂) =
      let (W₃ , r₃ , rf₃) = term-fail-▷ Pc Q eqPc pcr rf₂
      in _ , τ*-then pref r₃ , rf₃
... | inj₂ (W₂ , qcr , rf₂) = _ , route-Q P Q Qc nt qw qcr , rf₂

□→▷-fail P Q Pc Qc nt pref qw reach ref with PTree.force Pc in eqPc
-- Pc terminated: delegate to □→▷-Pret (handles the cP/cQ/sQP shapes uniformly).
... | ret r = □→▷-Pret P Q Pc Qc nt eqPc pref qw reach ref
-- Pc live: recurse on the big-step.
□→▷-fail P Q Pc Qc nt pref qw ⟹-refl ref | sil _ =
  let (W₂ , r₂ , rf₂) = □-refl-fail-R {P = Pc} {Q = Qc} ref
  in _ , route-Q P Q Qc nt qw r₂ , rf₂
□→▷-fail P Q Pc Qc nt pref qw ⟹-refl ref | react _ _ =
  let (W₂ , r₂ , rf₂) = □-refl-fail-R {P = Pc} {Q = Qc} ref
  in _ , route-Q P Q Qc nt qw r₂ , rf₂
-- Pc live, τ-step.
□→▷-fail P Q Pc Qc nt pref qw (⟹-τ step rest) ref | sil _ =
  □→▷-fail-τ-Plive P Q Pc Qc nt (subst NonRet (sym eqPc) tt0) pref qw step rest ref
□→▷-fail P Q Pc Qc nt pref qw (⟹-τ step rest) ref | react _ _ =
  □→▷-fail-τ-Plive P Q Pc Qc nt (subst NonRet (sym eqPc) tt0) pref qw step rest ref
-- Pc live, ev-step.
□→▷-fail P Q Pc Qc nt pref qw (⟹-ev step rest) ref | sil _ =
  □→▷-fail-ev P Q Pc Qc nt pref qw step rest ref
□→▷-fail P Q Pc Qc nt pref qw (⟹-ev step rest) ref | react _ _ =
  □→▷-fail-ev P Q Pc Qc nt pref qw step rest ref

-- Pc live, a τ-step of Pc□Qc.  Split on force Qc: Qc=ret (Pc-live, Qc-term) uses
-- □-Rret-τ-inv (cQ→route-Q ; sPQ→ slide-term-fail-R then recurse); both-live uses
-- □-live-τ-inv (chP→extend pref & recurse ; chQ→extend qw & recurse).
□→▷-fail-τ-Plive P Q Pc Qc nt ntPc pref qw step rest ref with PTree.force Qc in eqQc
... | ret r with □-Rret-τ-inv Pc Qc ntPc eqQc step
...   | inj₁ refl = _ , route-Q P Q Qc nt qw rest , ref
...   | inj₂ (Pc' , Pcτ , refl) =
        ▷→▷-fail P Q Pc' Qc nt eqQc (τ*-trans pref (τ*-step (▷-τ-L Pcτ) τ*-refl)) qw rest ref
□→▷-fail-τ-Plive P Q Pc Qc nt ntPc pref qw step rest ref | sil _ with □-live-τ-inv Pc Qc ntPc (subst NonRet (sym eqQc) tt0) step
...   | inj₁ (Pc' , Pcτ , refl) =
        □→▷-fail P Q Pc' Qc nt (τ*-trans pref (τ*-step (▷-τ-L Pcτ) τ*-refl)) qw rest ref
...   | inj₂ (Qc' , Qcτ , refl) =
        □→▷-fail P Q Pc Qc' nt pref (τ*-trans qw (τ*-step Qcτ τ*-refl)) rest ref
□→▷-fail-τ-Plive P Q Pc Qc nt ntPc pref qw step rest ref | react _ _ with □-live-τ-inv Pc Qc ntPc (subst NonRet (sym eqQc) tt0) step
...   | inj₁ (Pc' , Pcτ , refl) =
        □→▷-fail P Q Pc' Qc nt (τ*-trans pref (τ*-step (▷-τ-L Pcτ) τ*-refl)) qw rest ref
...   | inj₂ (Qc' , Qcτ , refl) =
        □→▷-fail P Q Pc Qc' nt pref (τ*-trans qw (τ*-step Qcτ τ*-refl)) rest ref

□→▷-fail-ev P Q Pc Qc nt pref qw step rest ref with □-ev-elim Pc Qc step
-- Pc's event: replay via pref + the slide's offer (▷-ev-L).
... | evP Pev = _ , τ*-then pref (⟹-ev (▷-ev-L {Q = Q} Pev) rest) , ref
-- Qc's event: route through the root timeout, then Qc's event.
... | evQ Qev = _ , route-Q P Q Qc nt qw (⟹-ev Qev rest) , ref
-- both offer the event (→ Pc₁ ⊓ Qc₁): split the ⊓-residual failure.
... | evPQ {P₁ = Pc₁} {Q₁ = Qc₁} Pev Qev with ⊓-failures→ Pc₁ Qc₁ (_ , rest , ref)
...   | inj₁ fP₁ = _ , τ*-then pref (⟹-ev (▷-ev-L {Q = Q} Pev) (proj₁ (proj₂ fP₁))) , proj₂ (proj₂ fP₁)
...   | inj₂ fQ₁ = _ , route-Q P Q Qc nt qw (⟹-ev Qev (proj₁ (proj₂ fQ₁))) , proj₂ (proj₂ fQ₁)

▷→▷-fail P Q Pc′ Qc nt eqQc pref qw ⟹-refl (st , _) = ⊥-elim (▷-unstable Pc′ Qc st)
▷→▷-fail P Q Pc′ Qc nt eqQc pref qw (⟹-τ step rest) ref with ▷-τ-elim Pc′ Qc step
... | inj₁ refl = _ , route-Q P Q Qc nt qw rest , ref
... | inj₂ (Pc″ , Pcτ , refl) =
      ▷→▷-fail P Q Pc″ Qc nt eqQc (τ*-trans pref (τ*-step (▷-τ-L Pcτ) τ*-refl)) qw rest ref
▷→▷-fail P Q Pc′ Qc nt eqQc pref qw (⟹-ev step rest) ref =
  _ , τ*-then pref (⟹-ev (▷-ev-L {Q = Q} (▷-ev-elim Pc′ Qc step)) rest) , ref

-------------------------------------------------------------------------------------
-- HARD ⊇F⊥ (component 1): LHS = P ▷ Q recovers every RHS = (P□Q)⊓Q stable failure⊥.
-- ⊓-failures⊥→ splits into the (P□Q)-summand or the Q-summand; (P□Q)'s failures route
-- through the worker □→▷-fail (initial Pc=P, Qc=Q, both witnesses refl), its divergences
-- through ⊇D; Q's failures/divergences prepend the root timeout.
-------------------------------------------------------------------------------------

char-⊇F⊥ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
         → (P ▷ Q) ⊇F⊥ ((P □ Q) ⊓ Q)
char-⊇F⊥ P Q nt f with ⊓-failures⊥→ (P □ Q) Q f
... | inj₂ (inj₁ (W , qreach , qref)) =
      inj₁ (_ , route-Q P Q Q nt τ*-refl qreach , qref)
... | inj₂ (inj₂ dQ) = inj₂ (▷-div-intro-R P Q refl nt dQ)
... | inj₁ (inj₁ (W , reach , ref)) =
      inj₁ (□→▷-fail P Q P Q nt τ*-refl τ*-refl reach ref)
... | inj₁ (inj₂ d) with □-div-elim {P = P} {Q = Q} d
...   | inj₁ dP = inj₂ (▷-div-intro-L P Q dP)
...   | inj₂ dQ = inj₂ (▷-div-intro-R P Q refl nt dQ)

-------------------------------------------------------------------------------------
-- THE LAW (U13.26, ▷-failures characterisation).
--   ≈FD = ((P▷Q ⊇F⊥ RHS, P▷Q ⊇D RHS) , (RHS ⊇F⊥ P▷Q, RHS ⊇D P▷Q)).
-------------------------------------------------------------------------------------

▷-failures-char-FD : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                     (P Q : PTree E (ExtI E) R) → NonRet (PTree.force P)
                   → (P ▷ Q) ≈FD ((P □ Q) ⊓ Q)
▷-failures-char-FD P Q nt =
  (char-⊇F⊥ P Q nt , char-⊇D P Q nt) ,
  (char-⊆F⊥ P Q nt , char-⊆D P Q nt)
