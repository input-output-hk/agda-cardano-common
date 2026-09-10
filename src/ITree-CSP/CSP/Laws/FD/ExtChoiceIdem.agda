{-# OPTIONS --guardedness #-}

-- Failures-divergences idempotence of external choice:  P □ P ≈FD P.
--
-- Reuses the □ FD machinery from ExtChoiceFD:
--   • the ELIM direction (P ⊇F⊥ (P□P), P ⊇D (P□P)) is just □-failures⊥-elim / □-div-elim.
--   • the divergence INTRO ((P□P) ⊇D P) is □-div-intro-L.
--   • the failures INTRO ((P□P) ⊇F⊥ P) is the only real work: a failure of P lifts to a
--     failure of P□P.  Done by induction on the big-step P ⟹⟨s⟩ W with a LOCKSTEP τ-case:
--     P─τ→P₁ advances BOTH copies (right via □-fail-τ-pre-R, left via □-fail-τ-pre-L), and
--     the ⟹-refl base uses refuses-double (a stable P refuses ⇒ P□P refuses the same set).

open import Level using (Level; Lift; lift; lower)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceIdem {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
-- generic stability facts (`stable-react` below is a thin alias for `stable→react`)
import Semantics.Stability {E = E} {I = ExtI E} as S
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; □-τ-tochoice-R; □-τ-toslide-R)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures⊥-elim; □-div-elim; □-div-intro-L; □-ev-toL; □-fail-τ-pre-L;
         □-τ-toP; □→▷-Pret; term-fail-▷;
         □-failures-elim-top; fail-τ-prepend; τ→NonRet; mk-stable)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- The right-τ-prepend, mirror of □-fail-τ-pre-L (which prepends a LEFT τ).  A failure
-- of P □ Q′ with Q ─[τ]→ Q′ is a failure of P □ Q; conditions on `force P`.
-------------------------------------------------------------------------------------

□-fail-τ-pre-R : ⦃ _ : DecEq R ⦄ (P Q Q′ : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
               → NonRet (PTree.force Q) → Q ─[ τ ]─► Q′ → (P □ Q′) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P □ Q) s X
□-fail-τ-pre-R P Q Q′ ntQ step reach′ ref with PTree.force P in eqP
... | sil _    = _ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt) reach′ , ref
... | react _ _ = _ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt) reach′ , ref
... | ret _ with PTree.force Q′ in eqQ′
...   | sil _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q′ eqP (subst NonRet (sym eqQ′) tt) reach′ ref
        in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂
...   | react _ _ =
        let (W₂ , r₂ , rf₂) = □→▷-Pret P Q′ eqP (subst NonRet (sym eqQ′) tt) reach′ ref
        in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂
...   | ret _ with □-failures-elim-top {P = P} {Q = Q′} (_ , reach′ , ref)
...     | inj₁ fP = _ , ⟹-τ (□-τ-toP P Q eqP ntQ) (proj₁ (proj₂ fP)) , proj₂ (proj₂ fP)
...     | inj₂ fQ′ =
          let (W₂ , r₂ , rf₂) = term-fail-▷ Q′ P eqQ′ (proj₁ (proj₂ fQ′)) (proj₂ (proj₂ fQ′))
          in _ , ⟹-τ (□-τ-toslide-R P Q step eqP) r₂ , rf₂

-------------------------------------------------------------------------------------
-- refuses-double : a STABLE P refusing X ⇒ P□P refuses X (the empty-trace base case).
-------------------------------------------------------------------------------------

-- a stable P has force ≡ react vP τcP with τcP everywhere nothing
-- (an alias for the generic `Semantics.Stability.stable→react`).
stable-react : {P : PTree E (ExtI E) R} → isStable P
            → Σ[ vP ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
              Σ[ τcP ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                (PTree.force P ≡ react vP τcP × (∀ i a → τcP i a ≡ nothing))
stable-react {P = P} = S.stable→react {t = P}

-- force(P□P) = react (mergeVis vP vP) (□-mt ..) when force P = react vP τcP
double-force-eq : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                → PTree.force P ≡ react vP τcP
                → PTree.force (P □ P)
                  ≡ react (mergeVis vP vP) (□-mt (react vP τcP) (react vP τcP) P P)
double-force-eq {P = P} eqP with PTree.force P | eqP
... | react _ _ | refl = refl

mergeVis-nn : {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {at : AnyTypes E} {a : proj₁ at}
            → vP at a ≡ nothing → vQ at a ≡ nothing → mergeVis vP vQ at a ≡ nothing
mergeVis-nn {vP = vP} {vQ = vQ} {at = at} {a = a} eP eQ with vP at a | vQ at a
... | nothing | nothing = refl
... | just _  | _       = case eP of λ ()
... | nothing | just _  = case eQ of λ ()

-- a visible offer of P□P projects to a visible offer of P (when force P = react vP τcP)
offers-double-elim : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R}
                     {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                     {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                     {e : Event√ R}
                   → PTree.force P ≡ react vP τcP → Offers (P □ P) e → Offers P e
offers-double-elim {P = P} {vP = vP} {τcP = τcP} eqP (M , sRet eqf) =
  case trans (sym eqf) (double-force-eq {P = P} eqP) of λ ()
offers-double-elim {P = P} {vP = vP} {τcP = τcP} eqP (M , sVis {v = v′} {at = at} {a = a} eqf br)
  with vP at a in eqV
... | just M′  = M′ , sVis eqP eqV
... | nothing  =
      case trans (sym br)
                 (trans (cong (λ f → f at a)
                              (proj₁ (react-injective (trans (sym eqf) (double-force-eq {P = P} eqP)))))
                        (mergeVis-nn {vP = vP} {vQ = vP} {at = at} {a = a} eqV eqV))
      of λ ()

-- P□P is stable when P is (the merged τ-branch is everywhere nothing)
stable-double : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} → isStable P → isStable (P □ P)
stable-double {P = P} st with stable-react {P = P} st
... | vP , τcP , eqP , τc-n =
  mk-stable {t = P □ P} (double-force-eq {P = P} eqP) mt-branch
  where
    mt-branch : ∀ i a → □-mt (react vP τcP) (react vP τcP) P P i a ≡ nothing
    mt-branch (_ , base _)            a = refl
    mt-branch (_ , fin)               a = refl
    mt-branch (_ , pair (base _) _)   a = refl
    mt-branch (_ , pair (pair _ _) _) a = refl
    mt-branch (_ , pair fin i) (lift fzero , a)        rewrite τc-n (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc fzero) , a) rewrite τc-n (_ , i) a = refl
    mt-branch (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

refuses-double : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
               → Refuses P X → Refuses (P □ P) X
refuses-double {P = P} {X = X} (st , noff) = stable-double {P = P} st , noff′
  where
    eqP = proj₁ (proj₂ (proj₂ (stable-react {P = P} st)))
    noff′ : ∀ e → X e → ¬ Offers (P □ P) e
    noff′ e xe off = noff e xe (offers-double-elim {P = P} eqP off)

-------------------------------------------------------------------------------------
-- The failures INTRO: a (stable-)failure of P lifts to a failure of P □ P.  Induction
-- on the big-step P ⟹⟨s⟩ W.  The τ-case advances BOTH copies in lockstep: rewind the
-- right via □-fail-τ-pre-R, then the left via □-fail-τ-pre-L.
-------------------------------------------------------------------------------------

idem-fail-intro : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R)
                  {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
                → P ⟹⟨ s ⟩ W → Refuses W X → failures (P □ P) s X
idem-fail-intro P ⟹-refl ref = P □ P , ⟹-refl , refuses-double ref
idem-fail-intro P (⟹-ev step rest) ref = _ , □-ev-toL P P step rest , ref
idem-fail-intro P (⟹-τ {q = P₁} step rest) ref
  with idem-fail-intro P₁ rest ref
... | W₁ , reach₁ , ref₁
      with □-fail-τ-pre-L P P₁ P₁ (τ→NonRet step) step reach₁ ref₁
...     | W₂ , reach₂ , ref₂ =
          □-fail-τ-pre-R P P P₁ (τ→NonRet step) step reach₂ ref₂

-------------------------------------------------------------------------------------
-- The four refinements and the law.
-------------------------------------------------------------------------------------

-- ELIM (easy):  P ⊇F⊥ (P□P)
idem-⊆F⊥ : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} → P ⊇F⊥ (P □ P)
idem-⊆F⊥ {P = P} f = [ (λ x → x) , (λ x → x) ]′ (□-failures⊥-elim {P = P} {Q = P} f)

-- ELIM (easy):  P ⊇D (P□P)
idem-⊆D : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} → P ⊇D (P □ P)
idem-⊆D {P = P} d = [ (λ x → x) , (λ x → x) ]′ (□-div-elim {P = P} {Q = P} d)

-- INTRO div (easy):  (P□P) ⊇D P
idem-⊇D : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} → (P □ P) ⊇D P
idem-⊇D {P = P} = □-div-intro-L {P = P} {Q = P}

-- INTRO failures (the work):  (P□P) ⊇F⊥ P
idem-⊇F⊥ : ⦃ _ : DecEq R ⦄ {P : PTree E (ExtI E) R} → (P □ P) ⊇F⊥ P
idem-⊇F⊥ {P = P} (inj₁ (W , reach , ref)) = inj₁ (idem-fail-intro P reach ref)
idem-⊇F⊥ {P = P} (inj₂ d)                 = inj₂ (□-div-intro-L {P = P} {Q = P} d)

-- THE LAW: external choice is idempotent (FD-equality)
□-idem-FD : ⦃ _ : DecEq R ⦄ (P : PTree E (ExtI E) R) → (P □ P) ≈FD P
□-idem-FD P = (idem-⊇F⊥ , idem-⊇D) , (idem-⊆F⊥ , idem-⊆D)
