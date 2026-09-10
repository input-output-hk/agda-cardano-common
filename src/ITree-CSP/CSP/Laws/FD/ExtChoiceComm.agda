{-# OPTIONS --guardedness #-}

-- External-choice commutativity.
--
-- Two proofs:
--   • □-comm-FD : (P □ Q) ≈FD (Q □ P)   — FD-DIRECT, pure routing through the
--     associativity infrastructure: failures comm = ×-comm at [] (□-fail-nil-→/←),
--     ⊎-comm at e∷s' (□-failures-elim + □-fail-intro-cons-L/R); divergences via
--     □-div-elim / □-div-intro swapped.
--   • □-comm     : (P □ Q) ∼  (Q □ P)   — STRONG bisimulation (added below), which
--     ALSO yields ≈FD via drbisim→≈FD ∘ sbisim→drbisim (□-comm-FD′).

open import Level using (Level; Lift; lift)
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

module CSP.Laws.FD.ExtChoiceComm {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Bisim               {E = E} {I = ExtI E}
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (failures; _⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; _⊇F⊥_; _⊇D_; _≈FD_; IsDivergence)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures-elim; □-div-elim; □-div-intro-L; □-div-intro-R;
         □-τ-toQ; □-τ-toP; mk-stable)
open import CSP.Laws.FD.ExtChoiceAssoc E-≟
  using (□-fail-nil-→; □-fail-nil-←; □-fail-intro-cons-L; □-fail-intro-cons-R)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G; NonRet;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq;
         □-τ-tochoice; □-τ-tochoice-R; □-τ-toslide; □-τ-toslide-R)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (react-τ-inv; br2-elim; □-slide-RQ-elim; □-slide-PR-elim; □-mt-elim;
         mergeVis-elim; viewT-τ; ret-no-τ; □-force-ret-inv)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-comm)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- FD-DIRECT commutativity.
-------------------------------------------------------------------------------------

-- failures(P□Q) ⊆ failures(Q□P): []-trace is ×-comm of the nil-conjunction; e∷s' is
-- ⊎-comm of the elim/intro-cons decomposition.
□-comm-fail : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {s : List (Event√ R)} {X : Event√ R → Set ℓx}
            → failures (P □ Q) s X → failures (Q □ P) s X
□-comm-fail P Q {s = []} (W , reach , ref) with □-fail-nil-→ P Q reach ref
... | fP , fQ = □-fail-nil-← Q P fQ fP
□-comm-fail P Q {s = x ∷ s'} (W , reach , ref) with □-failures-elim P Q reach ref
... | inj₁ (W_P , reachP , refP) = □-fail-intro-cons-R Q P reachP refP
... | inj₂ (W_Q , reachQ , refQ) = □-fail-intro-cons-L Q P reachQ refQ

-- divergences(P□Q) ⊆ divergences(Q□P)
□-comm-div : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {s : List (Event√ R)}
           → divergences (P □ Q) s → divergences (Q □ P) s
□-comm-div P Q d with □-div-elim {P = P} {Q = Q} d
... | inj₁ dP = □-div-intro-R {P = Q} {Q = P} dP
... | inj₂ dQ = □-div-intro-L {P = Q} {Q = P} dQ

□-comm-⊇F⊥ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ⊇F⊥ (Q □ P)
□-comm-⊇F⊥ P Q (inj₁ f) = inj₁ (□-comm-fail Q P f)
□-comm-⊇F⊥ P Q (inj₂ d) = inj₂ (□-comm-div Q P d)

□-comm-⊇D : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ⊇D (Q □ P)
□-comm-⊇D P Q d = □-comm-div Q P d

□-comm-FD : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ≈FD (Q □ P)
□-comm-FD P Q =
  (□-comm-⊇F⊥ P Q , □-comm-⊇D P Q) , (□-comm-⊇F⊥ Q P , □-comm-⊇D Q P)

-------------------------------------------------------------------------------------
-- STRONG-BISIMULATION commutativity:  (P □ Q) ∼ (Q □ P).
-- Not force-equal (mergeVis' both-offer gives P₁⊓Q₁ vs Q₁⊓P₁, and the τ-tags swap),
-- so a genuine coinductive bisimulation: each (P□Q)-step is matched by the mirror
-- (Q□P)-step (via the swapped commit/slide/choice constructors), continuations related
-- by □-comm (choice), ⊓-comm (both-offer event), or reflexivity (commit/slide/√).
-------------------------------------------------------------------------------------

-- mirror of □-force-ret-inv (force(P□Q)≡ret r ⇒ force Q≡ret r)
□-force-ret-inv-R : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r : R}
                  → PTree.force (P □ Q) ≡ ret r → PTree.force Q ≡ ret r
□-force-ret-inv-R {P = P} {Q = Q} eqf with PTree.force P | PTree.force Q
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = eqf
...   | no  _    = case eqf of λ ()
□-force-ret-inv-R eqf | ret _    | sil _    = case eqf of λ ()
□-force-ret-inv-R eqf | ret _    | react _ _ = case eqf of λ ()
□-force-ret-inv-R eqf | sil _    | ret _    = case eqf of λ ()
□-force-ret-inv-R eqf | sil _    | sil _    = case eqf of λ ()
□-force-ret-inv-R eqf | sil _    | react _ _ = case eqf of λ ()
□-force-ret-inv-R eqf | react _ _ | ret _    = case eqf of λ ()
□-force-ret-inv-R eqf | react _ _ | sil _    = case eqf of λ ()
□-force-ret-inv-R eqf | react _ _ | react _ _ = case eqf of λ ()

□-comm : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ∼ (Q □ P)

-- τ-step transfer (P□Q ⇒ Q□P), case force P | force Q so every constructor has its eqs.
□-comm-tau : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
           → (P □ Q) ─[ τ ]─► M
           → Σ[ M′ ∈ PTree E (ExtI E) R ] (((Q □ P) ─[ τ ]─► M′) × (M ∼ M′))
□-comm-tau P Q step with PTree.force P in eqP | PTree.force Q in eqQ
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = ⊥-elim (ret-no-τ (fL-A {P = P} {Q = Q} eqP eqQ) step)
...   | no ¬eq = case react-τ-inv (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) step of λ where
        (i , a , breq) → case br2-elim P Q {i = i} {a = a} breq of λ where
          (inj₁ refl) → P , sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                                  (fL-B {P = Q} {Q = P} eqQ eqP (λ e → ¬eq (sym e))) refl
                          , sbisim-refl P
          (inj₂ refl) → Q , sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                                  (fL-B {P = Q} {Q = P} eqQ eqP (λ e → ¬eq (sym e))) refl
                          , sbisim-refl Q
□-comm-tau P Q step | ret rP | sil Q' =
  case react-τ-inv (fL-C {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-RQ-elim P (sil Q') {i = i} {a = a} breq of λ where
      (inj₁ refl) → P , □-τ-toQ Q P (subst NonRet (sym eqQ) tt) eqP , sbisim-refl P
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' ▷ P) , □-τ-toslide Q P (viewT-τ eqQ veq) eqP , sbisim-refl (Q'' ▷ P)
□-comm-tau P Q step | ret rP | react vQ τcQ =
  case react-τ-inv (fL-D {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} breq of λ where
      (inj₁ refl) → P , □-τ-toQ Q P (subst NonRet (sym eqQ) tt) eqP , sbisim-refl P
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' ▷ P) , □-τ-toslide Q P (viewT-τ eqQ veq) eqP , sbisim-refl (Q'' ▷ P)
□-comm-tau P Q step | sil P' | ret rQ =
  case react-τ-inv (fL-E {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-PR-elim (sil P') Q {i = i} {a = a} breq of λ where
      (inj₁ refl) → Q , □-τ-toP Q P eqQ (subst NonRet (sym eqP) tt) , sbisim-refl Q
      (inj₂ (j , a' , P'' , veq , refl)) →
        (P'' ▷ Q) , □-τ-toslide-R Q P (viewT-τ eqP veq) eqQ , sbisim-refl (P'' ▷ Q)
□-comm-tau P Q step | react vP τcP | ret rQ =
  case react-τ-inv (fL-F {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-PR-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
      (inj₁ refl) → Q , □-τ-toP Q P eqQ (subst NonRet (sym eqP) tt) , sbisim-refl Q
      (inj₂ (j , a' , P'' , veq , refl)) →
        (P'' ▷ Q) , □-τ-toslide-R Q P (viewT-τ eqP veq) eqQ , sbisim-refl (P'' ▷ Q)
□-comm-tau P Q step | sil P' | sil Q' =
  case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (sil Q') P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P'' , veq , refl)) →
        (Q □ P'') , □-τ-tochoice-R Q P (viewT-τ eqP veq) eqQ tt , □-comm P'' Q
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' □ P) , □-τ-tochoice Q P (viewT-τ eqQ veq) eqP tt , □-comm P Q''
□-comm-tau P Q step | sil P' | react vQ τcQ =
  case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P'' , veq , refl)) →
        (Q □ P'') , □-τ-tochoice-R Q P (viewT-τ eqP veq) eqQ tt , □-comm P'' Q
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' □ P) , □-τ-tochoice Q P (viewT-τ eqQ veq) eqP tt , □-comm P Q''
□-comm-tau P Q step | react vP τcP | sil Q' =
  case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P'' , veq , refl)) →
        (Q □ P'') , □-τ-tochoice-R Q P (viewT-τ eqP veq) eqQ tt , □-comm P'' Q
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' □ P) , □-τ-tochoice Q P (viewT-τ eqQ veq) eqP tt , □-comm P Q''
□-comm-tau P Q step | react vP τcP | react vQ τcQ =
  case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P'' , veq , refl)) →
        (Q □ P'') , □-τ-tochoice-R Q P (viewT-τ eqP veq) eqQ tt , □-comm P'' Q
      (inj₂ (j , a' , Q'' , veq , refl)) →
        (Q'' □ P) , □-τ-tochoice Q P (viewT-τ eqQ veq) eqP tt , □-comm P Q''

-- visible/√-step transfer.  sRet (√) is uniform; sVis cases force P | force Q and
-- rebuilds the offer through the swapped node (mergeVis-elim splits the both-live case).
□-comm-ev : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {e : Event√ R} {M : PTree E (ExtI E) R}
          → (P □ Q) ─[ ev e ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ] (((Q □ P) ─[ ev e ]─► M′) × (M ∼ M′))
□-comm-ev P Q (sRet eqf) =
  _ , sRet (fL-A {P = Q} {Q = P} (□-force-ret-inv-R {P = P} {Q = Q} eqf) (□-force-ret-inv {P = P} {Q = Q} eqf))
    , sbisim-refl _
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) with PTree.force P in eqP | PTree.force Q in eqQ
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = case eqf of λ ()
...   | no ¬eq   = case (subst (λ f → f at a ≡ just _)
                          (sym (proj₁ (react-injective eqf))) br)
                       of λ ()
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | ret rP | sil Q' =
  case (subst (λ f → f at a ≡ just _)
         (sym (proj₁ (react-injective eqf))) br)
      of λ ()
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | ret rP | react vQ τcQ =
  _ , sVis (fL-F {P = Q} {Q = P} eqQ eqP)
           (subst (λ f → f at a ≡ just _)
                  (sym (proj₁ (react-injective eqf))) br)
    , sbisim-refl _
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | sil P' | ret rQ =
  case (subst (λ f → f at a ≡ just _)
         (sym (proj₁ (react-injective eqf))) br)
      of λ ()
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | react vP τcP | ret rQ =
  _ , sVis (fL-D {P = Q} {Q = P} eqQ eqP)
           (subst (λ f → f at a ≡ just _)
                  (sym (proj₁ (react-injective eqf))) br)
    , sbisim-refl _
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | sil P' | sil Q' =
  case mergeVis-elim ∅v ∅v at a
         (subst (λ f → f at a ≡ just _)
                (sym (proj₁ (react-injective eqf))) br)
      of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , () , _)))
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | sil P' | react vQ τcQ =
  case mergeVis-elim ∅v vQ at a
         (subst (λ f → f at a ≡ just _)
                (sym (proj₁ (react-injective eqf))) br)
      of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (∅n , vQm))) →
          _ , sVis (fL-G {P = Q} {Q = P} eqQ eqP tt tt) (mergeVis-L-eq {vP = vQ} {vQ = ∅v} vQm refl)
            , sbisim-refl _
        (inj₂ (inj₂ (_ , _ , () , _)))
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | react vP τcP | sil Q' =
  case mergeVis-elim vP ∅v at a
         (subst (λ f → f at a ≡ just _)
                (sym (proj₁ (react-injective eqf))) br)
      of λ where
        (inj₁ (vPm , _)) →
          _ , sVis (fL-G {P = Q} {Q = P} eqQ eqP tt tt) (mergeVis-R-eq {vP = ∅v} {vQ = vP} refl vPm)
            , sbisim-refl _
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , _ , () , _)))
□-comm-ev P Q (sVis {at = at} {a = a} eqf br) | react vP τcP | react vQ τcQ =
  case mergeVis-elim vP vQ at a
         (subst (λ f → f at a ≡ just _)
                (sym (proj₁ (react-injective eqf))) br)
      of λ where
        (inj₁ (vPm , vQn)) →
          _ , sVis (fL-G {P = Q} {Q = P} eqQ eqP tt tt) (mergeVis-R-eq {vP = vQ} {vQ = vP} vQn vPm)
            , sbisim-refl _
        (inj₂ (inj₁ (vPn , vQm))) →
          _ , sVis (fL-G {P = Q} {Q = P} eqQ eqP tt tt) (mergeVis-L-eq {vP = vQ} {vQ = vP} vQm vPn)
            , sbisim-refl _
        (inj₂ (inj₂ (P₁ , Q₁ , vPm , vQm , refl))) →
          (Q₁ ⊓ P₁) , sVis (fL-G {P = Q} {Q = P} eqQ eqP tt tt) (mergeVis-LQ-eq {vP = vQ} {vQ = vP} vQm vPm)
                    , ⊓-comm P₁ Q₁

□-comm P Q .Sbisim.fwd .SSimF.on-ev  = □-comm-ev  P Q
□-comm P Q .Sbisim.fwd .SSimF.on-tau = □-comm-tau P Q
□-comm P Q .Sbisim.bwd .SSimF.on-ev  = □-comm-ev  Q P
□-comm P Q .Sbisim.bwd .SSimF.on-tau = □-comm-tau Q P

-- the lifted FD law (independent proof of □-comm-FD via the strong bisimulation)
□-comm-FD′ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ≈FD (Q □ P)
□-comm-FD′ P Q = drbisim→≈FD (sbisim→drbisim (□-comm P Q))

-------------------------------------------------------------------------------------
-- UNIT law:  P □ Stop ≈FD P   (Stop = react ∅v ∅t is the unit of □).
-- FD-DIRECT again: Stop refuses everything at [] and offers/diverges nothing, so the
-- nil-conjunction collapses to failures P, the cons-disjunction's Stop-summand is empty,
-- and div Stop is empty.
-------------------------------------------------------------------------------------

-- Stop facts (mirror of the deadlock lemmas, for the named CSP process Stop).
Stop-no-offer : ⦃ _ : DecEq R ⦄ {e : Event√ R} {t′ : PTree E (ExtI E) R}
              → ¬ (Stop {R = R} ─[ ev e ]─► t′)
Stop-no-offer (sRet ())
Stop-no-offer (sVis refl ())

Stop-no-τ : ⦃ _ : DecEq R ⦄ {t′ : PTree E (ExtI E) R} → ¬ (Stop {R = R} ─[ τ ]─► t′)
Stop-no-τ (sSil ())
Stop-no-τ (sTau refl ())

Stop-refuses : ⦃ _ : DecEq R ⦄ {X : Event√ R → Set ℓx} → Refuses (Stop {R = R}) X
Stop-refuses = mk-stable {t = Stop} refl (λ i a → refl) , λ e _ (_ , step) → Stop-no-offer step

Stop-fail-nil : ⦃ _ : DecEq R ⦄ {X : Event√ R → Set ℓx} → failures (Stop {R = R}) [] X
Stop-fail-nil = Stop , ⟹-refl , Stop-refuses

Stop-no-fail-cons : ⦃ _ : DecEq R ⦄ {x : Event√ R} {s′ : List (Event√ R)} {W : PTree E (ExtI E) R}
                  → Stop {R = R} ⟹⟨ x ∷ s′ ⟩ W → ⊥
Stop-no-fail-cons (⟹-τ step _)  = Stop-no-τ step
Stop-no-fail-cons (⟹-ev step _) = Stop-no-offer step

Stop-no-div : ⦃ _ : DecEq R ⦄ {s : List (Event√ R)} → divergences (Stop {R = R}) s → ⊥
Stop-no-div d with IsDivergence.reach d
... | ⟹-refl       = Stop-no-τ (IsDivergence.divwit d .Diverges.step)
... | ⟹-τ step _   = Stop-no-τ step
... | ⟹-ev step _  = Stop-no-offer step

-- failures intro / elim and divergence elim specialised to the Stop summand.
□-Stop-fail-intro : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) {s : List (Event√ R)}
                    {X : Event√ R → Set ℓx}
                  → failures P s X → failures (P □ Stop) s X
□-Stop-fail-intro P {s = []}      f                 = □-fail-nil-← P Stop f Stop-fail-nil
□-Stop-fail-intro P {s = x ∷ s′} (W , reach , ref) = □-fail-intro-cons-L P Stop reach ref

□-Stop-fail-elim : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) {s : List (Event√ R)}
                   {X : Event√ R → Set ℓx}
                 → failures (P □ Stop) s X → failures P s X
□-Stop-fail-elim P {s = []} (W , reach , ref) with □-fail-nil-→ P Stop reach ref
... | fP , _ = fP
□-Stop-fail-elim P {s = x ∷ s′} (W , reach , ref) with □-failures-elim P Stop reach ref
... | inj₁ fP                 = fP
... | inj₂ (W′ , reach′ , _)  = ⊥-elim (Stop-no-fail-cons reach′)

□-Stop-div-elim : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) {s : List (Event√ R)}
                → divergences (P □ Stop) s → divergences P s
□-Stop-div-elim P d with □-div-elim {P = P} {Q = Stop} d
... | inj₁ dP    = dP
... | inj₂ dStop = ⊥-elim (Stop-no-div dStop)

□-Stop-⊇F⊥ : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → (P □ Stop) ⊇F⊥ P
□-Stop-⊇F⊥ P (inj₁ f) = inj₁ (□-Stop-fail-intro P f)
□-Stop-⊇F⊥ P (inj₂ d) = inj₂ (□-div-intro-L {P = P} {Q = Stop} d)

□-Stop-⊆F⊥ : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → P ⊇F⊥ (P □ Stop)
□-Stop-⊆F⊥ P (inj₁ f) = inj₁ (□-Stop-fail-elim P f)
□-Stop-⊆F⊥ P (inj₂ d) = inj₂ (□-Stop-div-elim P d)

□-Stop-FD : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → (P □ Stop) ≈FD P
□-Stop-FD P =
  (□-Stop-⊇F⊥ P , □-div-intro-L {P = P} {Q = Stop}) , (□-Stop-⊆F⊥ P , □-Stop-div-elim P)
