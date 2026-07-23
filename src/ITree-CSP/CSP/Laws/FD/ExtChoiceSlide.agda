{-# OPTIONS --guardedness #-}

-- Failures-divergences law (U13.15, extc-slide), built FD-direct:
--
--   □-slide-FD :  (((e ⟶ P) ▷ P′) □ Q)  ≈FD  ((e ⟶ P) ▷ (P′ □ Q))
--
-- The external-choice analogue of InterruptFD.△-slide-dist-FD.  Unlike interrupt, the
-- prefix continuation P is UNCHANGED on the RHS: a visible event resolves the external
-- choice and discards Q.  Only the post-timeout P′ becomes P′ □ Q.
--
-- It is NOT a DR-bisimulation: the LHS  ((e⟶P)▷P′) □ Q  can advance Q by an internal
-- τ while KEEPING the offer e + timeout open, whereas the RHS can only progress Q after
-- firing the timeout (losing the offer e).  So this is proved FD-direct: the four
-- refinement components separately.  Divergences project cleanly through the generic
-- □-/▷- elim/intro; the failures ⊒ direction needs a worker that recurses on the
-- LHS big-step (mirroring △-slide-fail-elim), carrying a witness  Q ─τ*→ Qc.

open import Level using (Level; Lift; lift; lower)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
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

module CSP.Laws.FD.ExtChoiceSlide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; empty-div; failures⊥;
         _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans)
open import CSP.Laws.FD.ExtChoiceDivergence E-≟ using (□-Diverges→; ▷-Diverges→)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures-elim; ▷-failures-elim; □-failures⊥-elim; □-div-elim;
         □-reach-div; ▷-reach-div; □-Diverges-L; □-Diverges-R; ▷-Diverges-L;
         □-div-intro-L; □-div-intro-R; □-reach-intro-L; □-reach-intro-R; ▷-reach-intro-L;
         □-fail-τ-pre-L; □-ev-toL; slide-term-fail; term-fail-▷; □→▷-term; □-τ-toQ;
         □→▷-Pret; □-τ-toP; □-failures-elim-top;
         stable-no-τ; stable-not-ret; mk-stable; ▷-unstable; fail-τ-prepend; fail-ev-prepend;
         mk-div; div-τ-prepend; div-ev-prepend)
open import CSP.Laws.Traces.TraceLaws E-≟
  using (force-▷-ret; force-▷-react; force-▷-sil; ▷-τ-L; ▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□τR; cP; cQ; sPQ; sQP; chP; chQ; □-τ-elim;
         □evR; evP; evQ; evPQ; □-ev-elim; ▷-τ-elim; ▷-ev-elim; ▷-timeout;
         viewT-τ; □-slide-PR-elim; □-mt-elim; mergeVis-elim)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq;
         □-τ-tochoice; □-τ-toslide; □-τ-tochoice-R; □-τ-toslide-R)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟ using (⊓-failures→)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr
    A : Set ℓ

-------------------------------------------------------------------------------------
-- Shared facts about the prefix / slide head.
-------------------------------------------------------------------------------------

-- the prefix can never diverge: force (e⟶P) ≡ react _ ∅t and a τ needs a `just` out of ∅t
prefix-no-Diverges : (e : E A) (P : A → PTree E (ExtI E) R) → ¬ Diverges (e ⟶ P)
prefix-no-Diverges e P d with d .Diverges.step
... | sSil sile = case sile of λ ()
... | sTau {i = i} {a = a} refl br = case br of λ ()

-- the prefix has no τ-step (force = react _ ∅t)
prefix-no-τ : (e : E A) (P : A → PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
            → (e ⟶ P) ─[ τ ]─► M → ⊥
prefix-no-τ e P (sSil sile) = case sile of λ ()
prefix-no-τ e P (sTau refl br) = case br of λ ()

-- S = (e⟶P) ▷ P′ forces to the slide node — NonRet
force-S-react : (e : E A) (P : A → PTree E (ExtI E) R) (P′ : PTree E (ExtI E) R)
             → PTree.force ((e ⟶ P) ▷ P′)
               ≡ react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)
force-S-react e P P′ = force-▷-react {P = e ⟶ P} {Q = P′} refl

-------------------------------------------------------------------------------------
-- Set-level divergence wrappers for the slide (built from the reach-* lemmas).
-------------------------------------------------------------------------------------

-- divergences (A ▷ B) ⊆ divergences A ∪ divergences B  (mirror of □-div-elim)
▷-div-elim : (A B : PTree E (ExtI E) R) {s : List (Event√ R)}
           → divergences (A ▷ B) s → divergences A s ⊎ divergences B s
▷-div-elim A B d with ▷-reach-div A B (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dA = inj₁ (subst (divergences A) (sym (d .IsDivergence.split))
                            (div-extension-closed dA))
... | inj₂ dB = inj₂ (subst (divergences B) (sym (d .IsDivergence.split))
                            (div-extension-closed dB))

-- divergences A ⊆ divergences (A ▷ B)  (mirror of □-div-intro-L)
▷-div-intro-L : (A B : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences A s → divergences (A ▷ B) s
▷-div-intro-L A B d = subst (divergences (A ▷ B)) (sym (d .IsDivergence.split))
  (div-extension-closed (▷-reach-intro-L A B (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-- divergences B ⊆ divergences (A ▷ B) when A is non-ret: fire the timeout first.
▷-div-intro-R : (A B : PTree E (ExtI E) R) {nA : NodeKind E (ExtI E) R} {s : List (Event√ R)}
              → PTree.force A ≡ nA → NonRet nA → divergences B s → divergences (A ▷ B) s
▷-div-intro-R A B eqA ntA d = div-τ-prepend (▷-timeout A B eqA ntA) d

-------------------------------------------------------------------------------------
-- Divergence directions.  Both project cleanly through the generic eliminators /
-- introducers — no worker needed.
--   LHS = ((e⟶P) ▷ P′) □ Q ,   RHS = (e⟶P) ▷ (P′ □ Q).
-------------------------------------------------------------------------------------

-- ⊑D : LHS recovers every RHS divergence.
-- ▷-div-elim splits a RHS-divergence into divergences(e⟶P) [impossible] ⊎
-- divergences(P′□Q); the latter splits (□-div-elim) into P′ or Q.  P′ → ▷-div-intro-L
-- into S, then □-div-intro-L into LHS; Q → □-div-intro-R into LHS.
□-slide-⊑D : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → (((e ⟶ P) ▷ P′) □ Q) ⊑D ((e ⟶ P) ▷ (P′ □ Q))
□-slide-⊑D e P P′ Q d with ▷-div-elim (e ⟶ P) (P′ □ Q) d
... | inj₁ dpre = □-div-intro-L {P = (e ⟶ P) ▷ P′} {Q = Q} (▷-div-intro-L (e ⟶ P) P′ dpre)
... | inj₂ dP′Q with □-div-elim {P = P′} {Q = Q} dP′Q
...   | inj₁ dP′ = □-div-intro-L {P = (e ⟶ P) ▷ P′} {Q = Q}
                     (▷-div-intro-R (e ⟶ P) P′ refl tt0 dP′)
...   | inj₂ dQ  = □-div-intro-R {P = (e ⟶ P) ▷ P′} {Q = Q} dQ

-- ⊒D : RHS recovers every LHS divergence.
-- □-div-elim splits a LHS-divergence into divergences S ⊎ divergences Q.
--   divergences S = divergences ((e⟶P)▷P′) splits (▷-div-elim) into (e⟶P) [→ RHS via
--   ▷-div-intro-L] or P′ [→ P′□Q via □-div-intro-L, then RHS via ▷-div-intro-R].
--   divergences Q → P′□Q via □-div-intro-R, then RHS via ▷-div-intro-R.
□-slide-⊒D : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → ((e ⟶ P) ▷ (P′ □ Q)) ⊑D (((e ⟶ P) ▷ P′) □ Q)
□-slide-⊒D e P P′ Q d with □-div-elim {P = (e ⟶ P) ▷ P′} {Q = Q} d
... | inj₁ dS with ▷-div-elim (e ⟶ P) P′ dS
...   | inj₁ dpre = ▷-div-intro-L (e ⟶ P) (P′ □ Q) dpre
...   | inj₂ dP′  = ▷-div-intro-R (e ⟶ P) (P′ □ Q) refl tt0
                      (□-div-intro-L {P = P′} {Q = Q} dP′)
□-slide-⊒D e P P′ Q d | inj₂ dQ =
  ▷-div-intro-R (e ⟶ P) (P′ □ Q) refl tt0 (□-div-intro-R {P = P′} {Q = Q} dQ)

-------------------------------------------------------------------------------------
-- Failures directions.
--   LHS = ((e⟶P) ▷ P′) □ Q ,   RHS = (e⟶P) ▷ (P′ □ Q),   S = (e⟶P) ▷ P′.
-------------------------------------------------------------------------------------

-- ⊑F⊥ (EASY: LHS recovers every RHS stable failure).  Worker recursing on RHS's big-step.
-- RHS's only steps are the timeout τ (→ P′□Q) and a prefix event x (→ P x).  The timeout
-- is matched by S's own τ (S ─τ→ P′) lifted to S□Q (□-fail-τ-pre-L), and a prefix event
-- is matched by S offering x (▷-ev-L) lifted to S□Q (□-ev-toL, discarding Q).  The
-- ⟹-refl base is discharged because RHS is unstable (it always has the timeout τ).
□-slide-RHS-fail→LHS : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → ((e ⟶ P) ▷ (P′ □ Q)) ⟹⟨ s ⟩ W → Refuses W X
  → failures (((e ⟶ P) ▷ P′) □ Q) s X
□-slide-RHS-fail→LHS e P P′ Q ⟹-refl (st , _) =
  ⊥-elim (stable-no-τ st (▷-timeout (e ⟶ P) (P′ □ Q) refl tt0))
□-slide-RHS-fail→LHS e P P′ Q (⟹-τ step rest) ref
  with ▷-τ-elim (e ⟶ P) (P′ □ Q) step
... | inj₁ refl =
      □-fail-τ-pre-L ((e ⟶ P) ▷ P′) P′ Q tt0
                     (▷-timeout (e ⟶ P) P′ refl tt0) rest ref
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ e P Pτ)
□-slide-RHS-fail→LHS e P P′ Q (⟹-ev step rest) ref
  with ▷-ev-elim (e ⟶ P) (P′ □ Q) step
... | sVis {at = at} {a = a} eqf brM =
      _ , □-ev-toL ((e ⟶ P) ▷ P′) Q
            (▷-ev-L {Q = P′} (sVis {at = at} {a = a} eqf brM)) rest
        , ref
... | sRet eqf = case eqf of λ ()

□-slide-⊑F⊥ : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → (((e ⟶ P) ▷ P′) □ Q) ⊑F⊥ ((e ⟶ P) ▷ (P′ □ Q))
□-slide-⊑F⊥ e P P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (□-slide-RHS-fail→LHS e P P′ Q reach ref)
□-slide-⊑F⊥ e P P′ Q (inj₂ d) = inj₂ (□-slide-⊑D e P P′ Q d)

-- HARD failures direction (⊒F⊥): RHS recovers every LHS stable failure.
--
-- A worker recursing on the LHS big-step (S □ Qc) ⟹⟨s⟩ W, mirroring △-slide-fail-elim,
-- carrying a witness  Q ─τ*→ Qc  so Qc-behaviours map back through the RHS's ORIGINAL Q
-- after the (single) RHS timeout.  S = (e⟶P) ▷ P′ is fixed and react (live).

-- custom τ-inversion for S □ Qc with S live (force S ≡ react …).  Four shapes:
--   (1) S's own τ, Qc live      → M ≡ S′ □ Qc           (carries force Qc ≡ react/sil)
--   (2) Qc's own τ              → M ≡ S □ Qc′
--   (3) Qc terminated, S's τ    → M ≡ S′ ▷ Qc           (slide-PR tag1)
--   (4) Qc terminated, commit   → M ≡ Qc                (slide-PR tag0)
□-Sτ-inv : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Qc : PTree E (ExtI E) R)
    {M : PTree E (ExtI E) R}
  → (((e ⟶ P) ▷ P′) □ Qc) ─[ τ ]─► M
  → (Σ[ S′ ∈ PTree E (ExtI E) R ] ((((e ⟶ P) ▷ P′) ─[ τ ]─► S′) × (M ≡ S′ □ Qc)))
  ⊎ (Σ[ Qc′ ∈ PTree E (ExtI E) R ] ((Qc ─[ τ ]─► Qc′) × (M ≡ ((e ⟶ P) ▷ P′) □ Qc′)))
  ⊎ (Σ[ S′ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
        ((((e ⟶ P) ▷ P′) ─[ τ ]─► S′) × (PTree.force Qc ≡ ret r) × (M ≡ S′ ▷ Qc)))
  ⊎ (Σ[ r ∈ R ] ((PTree.force Qc ≡ ret r) × (M ≡ Qc)))
□-Sτ-inv e P P′ Qc (sSil eqf) with PTree.force Qc
... | ret r     = case eqf of λ ()
... | sil Qc₁   = case eqf of λ ()
... | react _ _ = case eqf of λ ()
□-Sτ-inv e P P′ Qc (sTau {i = i} {a = a} eqf br) with PTree.force Qc in eqQc
-- Qc terminated: force(S□Qc) = react vS (□-slide-PR (force S) Qc) (fL-F).
... | ret r
      with □-slide-PR-elim (react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)) Qc
             {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ m≡Qc                     = inj₂ (inj₂ (inj₂ (r , refl , m≡Qc)))
...   | inj₂ (j , a′ , S′ , veq , m≡) =
        inj₂ (inj₂ (inj₁ (S′ , r , viewT-τ {j = j} {a' = a′} (force-S-react e P P′) veq , refl , m≡)))
-- Qc live: force(S□Qc) = react (merge…) (□-mt (force S) (force Qc) S Qc) (fL-G).
□-Sτ-inv e P P′ Qc (sTau {i = i} {a = a} eqf br) | sil Qc₁
      with □-mt-elim (react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)) (sil Qc₁)
             ((e ⟶ P) ▷ P′) Qc {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ (j , a′ , S′ , veq , m≡)  = inj₁ (S′ , viewT-τ {j = j} {a' = a′} (force-S-react e P P′) veq , m≡)
...   | inj₂ (j , a′ , Qc′ , veq , m≡) = inj₂ (inj₁ (Qc′ , viewT-τ {j = j} {a' = a′} eqQc veq , m≡))
□-Sτ-inv e P P′ Qc (sTau {i = i} {a = a} eqf br) | react vQ τcQ
      with □-mt-elim (react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)) (react vQ τcQ)
             ((e ⟶ P) ▷ P′) Qc {i = i} {a = a}
             (subst (λ f → f i a ≡ _) (sym (proj₂ (react-injective eqf))) br)
...   | inj₁ (j , a′ , S′ , veq , m≡)  = inj₁ (S′ , viewT-τ {j = j} {a' = a′} (force-S-react e P P′) veq , m≡)
...   | inj₂ (j , a′ , Qc′ , veq , m≡) = inj₂ (inj₁ (Qc′ , viewT-τ {j = j} {a' = a′} eqQc veq , m≡))

-- R-mirror of □-fail-τ-pre-L : a failure of P□Q′ (after Q's τ Q→Q′) is a failure of P□Q.
□-fail-τ-pre-R : ⦃ _ : DecEq R ⦄ (P Q Q′ : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
               → NonRet (PTree.force Q) → Q ─[ τ ]─► Q′ → (P □ Q′) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P □ Q) s X
□-fail-τ-pre-R P Q Q′ ntQ step reach′ ref with PTree.force P in eqP
... | sil _    = _ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt0) reach′ , ref
... | react _ _ = _ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt0) reach′ , ref
... | ret _ with PTree.force Q′ in eqQ′
...   | sil _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q′ eqP (subst NonRet (sym eqQ′) tt0) reach′ ref
        in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂
...   | react _ _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q′ eqP (subst NonRet (sym eqQ′) tt0) reach′ ref
        in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂
...   | ret _ with □-failures-elim-top {P = P} {Q = Q′} (_ , reach′ , ref)
...     | inj₂ fQ′ =
          let (W₂ , r₂ , rf₂) = term-fail-▷ Q′ P eqQ′ (proj₁ (proj₂ fQ′)) (proj₂ (proj₂ fQ′))
          in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂
...     | inj₁ fP  = _ , ⟹-τ (□-τ-toP P Q eqP ntQ) (proj₁ (proj₂ fP)) , proj₂ (proj₂ fP)

-- R-mirror of □-ev-toL : Q's visible/√ step lifts into P □ Q reaching the SAME final state.
□-ev-toR : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ W : PTree E (ExtI E) R}
           {e : Event√ R} {s : List (Event√ R)}
         → Q ─[ ev e ]─► Q₁ → Q₁ ⟹⟨ s ⟩ W → (P □ Q) ⟹⟨ e ∷ s ⟩ W
□-ev-toR P Q {Q₁ = Q₁} (sVis {v = vQ} {at = at} {a = a} eqQ brQ) rest with PTree.force P in eqP
... | ret _ = ⟹-ev (sVis (fL-D {P = P} {Q = Q} eqP eqQ) brQ) rest
... | sil _ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt0 tt0)
                         (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl brQ)) rest
... | react vP τcP with vP at a in eqVP
...   | nothing = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt0 tt0)
                             (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)) rest
...   | just P₁ = ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt0 tt0)
                             (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ)) (⟹-τ (⊓-stepR P₁ Q₁) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest with PTree.force P in eqP
... | ret r′ with r′ ≟ x
...   | yes refl = ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQ)) rest
...   | no ¬eq   = ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                             (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl)
                       (⟹-ev (sRet eqQ) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest | sil _ =
  ⟹-τ (□-τ-toQ P Q (subst NonRet (sym eqP) tt0) eqQ) (⟹-ev (sRet eqQ) rest)
□-ev-toR P Q (sRet {x = x} eqQ) rest | react _ _ =
  ⟹-τ (□-τ-toQ P Q (subst NonRet (sym eqP) tt0) eqQ) (⟹-ev (sRet eqQ) rest)

-- S □ Qc always has a τ-move (S's timeout lifted into the choice).
□-S-has-τ : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Qc : PTree E (ExtI E) R)
  → Σ[ M ∈ PTree E (ExtI E) R ] ((((e ⟶ P) ▷ P′) □ Qc) ─[ τ ]─► M)
□-S-has-τ e P P′ Qc with PTree.force Qc in eqQc
... | ret _     = _ , □-τ-toslide ((e ⟶ P) ▷ P′) Qc (▷-timeout (e ⟶ P) P′ refl tt0) eqQc
... | sil _     = _ , □-τ-tochoice ((e ⟶ P) ▷ P′) Qc (▷-timeout (e ⟶ P) P′ refl tt0) eqQc tt0
... | react _ _ = _ , □-τ-tochoice ((e ⟶ P) ▷ P′) Qc (▷-timeout (e ⟶ P) P′ refl tt0) eqQc tt0

-- S □ Qc is unstable.
□-S-unstable : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Qc : PTree E (ExtI E) R)
  → ¬ isStable (((e ⟶ P) ▷ P′) □ Qc)
□-S-unstable e P P′ Qc st = stable-no-τ st (proj₂ (□-S-has-τ e P P′ Qc))

-- S's visible offer is recovered by the RHS (before the timeout): S = (e⟶P)▷P′ offers e to
-- P a, and RHS = (e⟶P)▷(P′□Q) offers e to the SAME P a (prefix continuation unchanged).
slide-RHS-ev-step : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {x : Event√ R} {M : PTree E (ExtI E) R}
  → ((e ⟶ P) ▷ P′) ─[ ev x ]─► M
  → ((e ⟶ P) ▷ (P′ □ Q)) ─[ ev x ]─► M
slide-RHS-ev-step e P P′ Q step with ▷-ev-elim (e ⟶ P) P′ step
... | sVis {at = at} {a = a} eqf brP = ▷-ev-L {Q = P′ □ Q} (sVis {at = at} {a = a} eqf brP)
... | sRet eqf = case eqf of λ ()

-- the RHS timeout: RHS ─τ→ (P′□Q).  Prepend it to lift a (P′□Q)-failure.
slide-RHS-timeout-fail-prepend : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx}
  → failures (P′ □ Q) s X
  → failures ((e ⟶ P) ▷ (P′ □ Q)) s X
slide-RHS-timeout-fail-prepend e P P′ Q f =
  fail-τ-prepend (▷-timeout (e ⟶ P) (P′ □ Q) refl tt0) f

-- iterate □-fail-τ-pre-R over a τ*-chain on the right operand of P′ □ ·.
□-τ*-fail-prepend-R : ⦃ _ : DecEq R ⦄ (P′ Qa Qc : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx}
  → Qa ─[τ*]─► Qc → failures (P′ □ Qc) s X → failures (P′ □ Qa) s X
□-τ*-fail-prepend-R P′ Qa Qc τ*-refl                f = f
□-τ*-fail-prepend-R P′ Qa Qc (τ*-step {t′ = Q1} sQ rest) f =
  let (W , reach , ref) = □-τ*-fail-prepend-R P′ Q1 Qc rest f
  in □-fail-τ-pre-R P′ Qa Q1 (τ→NonRet-Qa sQ) sQ reach ref
  where
    τ→NonRet-Qa : ∀ {M} → Qa ─[ τ ]─► M → NonRet (PTree.force Qa)
    τ→NonRet-Qa (sSil eq)   = subst NonRet (sym eq) tt0
    τ→NonRet-Qa (sTau eq _) = subst NonRet (sym eq) tt0

-- R-mirror of slide-term-fail: when Qc terminates, a failure of the slide P′ ▷ Qc is a
-- failure of P′ □ Qc.  (Qc on the RIGHT, unlike slide-term-fail which has it on the LEFT.)
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

slide-term-fail-R : ⦃ _ : DecEq R ⦄ (P′ Qc : PTree E (ExtI E) R) {r : R}
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → PTree.force Qc ≡ ret r → (P′ ▷ Qc) ⟹⟨ s ⟩ W → Refuses W X → failures (P′ □ Qc) s X
slide-term-fail-R P′ Qc eqQc ⟹-refl (st , _)     = ⊥-elim (▷-unstable P′ Qc st)
slide-term-fail-R P′ Qc eqQc (⟹-τ step rest) ref = _ , ⟹-τ (slide→□-τ-R P′ Qc eqQc step) rest , ref
slide-term-fail-R P′ Qc eqQc (⟹-ev step rest) ref = _ , slide→□-ev-R P′ Qc eqQc step rest , ref

-- a failure reached from a TERMINATED Qc lifts into P′ □ Qc.  P′ live: prepend the
-- √-commit τ (P′□Qc ─τ→ Qc, □-τ-toQ).  P′ terminated: route via term-fail-▷ on the
-- terminated Qc (slide Qc▷P′) and slide-term-fail's mirror is avoided by □→▷-Pret.
term-Qc-fail-□R : ⦃ _ : DecEq R ⦄ (P′ Qc : PTree E (ExtI E) R) {r : R}
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → PTree.force Qc ≡ ret r → Qc ⟹⟨ s ⟩ W → Refuses W X → failures (P′ □ Qc) s X
term-Qc-fail-□R P′ Qc eqQc reach ref with PTree.force P′ in eqP′
... | sil _    = _ , ⟹-τ (□-τ-toQ P′ Qc (subst NonRet (sym eqP′) tt0) eqQc) reach , ref
... | react _ _ = _ , ⟹-τ (□-τ-toQ P′ Qc (subst NonRet (sym eqP′) tt0) eqQc) reach , ref
-- P′ also terminated: failures of P′□Qc factor; the terminated Qc's run is a failures(P′□Qc)
-- via the √-mirror □→▷-Pret (Qc live? no — Qc terminated, so use term-fail-▷ on Qc and the
-- slide bridge).  We get it directly from □-ev-toR / the ret|ret structure of P′□Qc.
-- P′ also terminated.  Qc=ret: the run from Qc is refl (vacuous: ret not stable) or a √-event.
... | ret r′ with reach
...   | ⟹-refl   = ⊥-elim (stable-not-ret {t = Qc} eqQc (proj₁ ref))
...   | ⟹-τ stp _ = ⊥-elim (ret-no-τ-Qc stp)
  where
    ret-no-τ-Qc : ∀ {M} → Qc ─[ τ ]─► M → ⊥
    ret-no-τ-Qc (sSil eq)   = case trans (sym eqQc) eq of λ ()
    ret-no-τ-Qc (sTau eq _) = case trans (sym eqQc) eq of λ ()
...   | ⟹-ev stp rest′ = _ , □-ev-toR P′ Qc stp rest′ , ref

-------------------------------------------------------------------------------------
-- The HARD worker (failures ⊒): RHS recovers every LHS stable failure.
-- Recurses on (S □ Qc) ⟹⟨s⟩ W (S = (e⟶P)▷P′ fixed), carrying q* : Q ─τ*→ Qc, so the
-- post-timeout RHS state P′□Q recovers the Qc-side behaviours via □-τ*-fail-prepend-R.
-------------------------------------------------------------------------------------

□-slide-fail-elim : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q Qc : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc
  → (((e ⟶ P) ▷ P′) □ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures ((e ⟶ P) ▷ (P′ □ Q)) s X
-- base: Refuses (S□Qc) needs it stable — but S□Qc is unstable.
□-slide-fail-elim e P P′ Q Qc q* ⟹-refl (st , _) =
  ⊥-elim (□-S-unstable e P P′ Qc st)
-- τ-step: invert via □-Sτ-inv.
□-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref with □-Sτ-inv e P P′ Qc step
-- (1) S's own τ, Qc live (→ S′ □ Qc).  Only S's timeout (→ P′□Qc); prefix-τ impossible.
... | inj₁ (S′ , Sτ , refl) with ▷-τ-elim (e ⟶ P) P′ Sτ
...   | inj₁ refl =
        slide-RHS-timeout-fail-prepend e P P′ Q
          (□-τ*-fail-prepend-R P′ Q Qc q* (_ , rest , ref))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ e P Pτ)
-- (2) Qc's own τ (→ S □ Qc′): recurse, extending q*.
□-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | inj₂ (inj₁ (Qc′ , Qcτ , refl)) =
      □-slide-fail-elim e P P′ Q Qc′ (τ*-trans q* (τ*-step Qcτ τ*-refl)) rest ref
-- (3) Qc terminated, S's τ slides on (→ S′ ▷ Qc).  S′ = P′ (timeout); prefix-τ impossible.
-- The rest is a run of P′▷Qc; slide-term-fail-R lifts it to a failure of P′□Qc (Qc terminated).
□-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | inj₂ (inj₂ (inj₁ (S′ , r , Sτ , eqQc , refl)))
      with ▷-τ-elim (e ⟶ P) P′ Sτ
...   | inj₁ refl =
        slide-RHS-timeout-fail-prepend e P P′ Q
          (□-τ*-fail-prepend-R P′ Q Qc q*
            (slide-term-fail-R P′ Qc eqQc rest ref))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ e P Pτ)
-- (4) Qc terminated, commit to Qc (→ Qc).  The rest run is from Qc (terminated): a √-commit.
□-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | inj₂ (inj₂ (inj₂ (r , eqQc , refl))) =
      slide-RHS-timeout-fail-prepend e P P′ Q
        (□-τ*-fail-prepend-R P′ Q Qc q*
          (term-Qc-fail-□R P′ Qc eqQc rest ref))
-- ev-step: invert via □-ev-elim S Qc.
□-slide-fail-elim e P P′ Q Qc q* (⟹-ev step rest) ref with □-ev-elim ((e ⟶ P) ▷ P′) Qc step
-- S's event (→ P a): RHS offers it (before timeout) to the SAME P a.
... | evP {M = M} sS = fail-ev-prepend (slide-RHS-ev-step e P P′ Q sS) (_ , rest , ref)
-- Qc's event (→ Qc₁): RHS times out, then P′□Q fires it (Q ─τ*→ Qc ─[ev]→ Qc₁).
... | evQ {M = Qc₁} sQ =
      slide-RHS-timeout-fail-prepend e P P′ Q
        (□-τ*-fail-prepend-R P′ Q Qc q*
          (_ , □-ev-toR P′ Qc sQ rest , ref))
-- both offer the event (→ P₁ ⊓ Qc₁): the ⊓ resolves to P a (RHS event) or Qc₁ (timeout path).
... | evPQ {P₁ = P₁} {Q₁ = Qc₁} sS sQ with ⊓-failures→ P₁ Qc₁ (_ , rest , ref)
...   | inj₁ fP₁ = fail-ev-prepend (slide-RHS-ev-step e P P′ Q sS) fP₁
...   | inj₂ fQc₁ =
        slide-RHS-timeout-fail-prepend e P P′ Q
          (□-τ*-fail-prepend-R P′ Q Qc q*
            (_ , □-ev-toR P′ Qc sQ (proj₁ (proj₂ fQc₁)) , proj₂ (proj₂ fQc₁)))

-- HARD (RHS recovers LHS): a failures⊥ of LHS routes through □-slide-fail-elim (failures
-- summand — a DIRECT ≈FD, so the elim already targets RHS) / □-slide-⊒D (divergence summand).
□-slide-⊒F⊥ : ⦃ _ : DecEq R ⦄
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → ((e ⟶ P) ▷ (P′ □ Q)) ⊑F⊥ (((e ⟶ P) ▷ P′) □ Q)
□-slide-⊒F⊥ e P P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (□-slide-fail-elim e P P′ Q Q τ*-refl reach ref)
□-slide-⊒F⊥ e P P′ Q (inj₂ d) = inj₂ (□-slide-⊒D e P P′ Q d)

-------------------------------------------------------------------------------------
-- THE LAW (U13.15, extc-slide): pair the two ⊑F⊥ and the two ⊑D refinements.
-------------------------------------------------------------------------------------

□-slide-FD : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ} ⦃ _ : DecEq R ⦄
             (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
           → (((e ⟶ P) ▷ P′) □ Q) ≈FD ((e ⟶ P) ▷ (P′ □ Q))
□-slide-FD e P P′ Q =
  (□-slide-⊑F⊥ e P P′ Q , □-slide-⊑D e P P′ Q) ,
  (□-slide-⊒F⊥ e P P′ Q , □-slide-⊒D e P P′ Q)
