{-# OPTIONS --guardedness #-}

-- Renaming distributes over external choice (T3.14):
--   (P □ Q) ⟦ inv ⟧ⁱ ≈FD (P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ).
--
-- Proved as a STRONG bisimulation `(P□Q)⟦inv⟧ⁱ ∼ (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)`, lifted to
-- `≈FD` via `drbisim→≈FD ∘ sbisim→drbisim` (the same lift as RenameIChoiceDist /
-- ExtChoiceComm).  Renaming is structural: it relabels visible events 1-1 (via `inv`),
-- re-indexes the τ-branches 1-1, and preserves `ret`, so it commutes with the offer/τ
-- structure of `□`.
--
-- The bisim is a FAMILY over (P,Q) and is genuinely coinductive: a τ-residual of the
-- `chP`/`chQ` shape (both operands live, one does an internal τ) recurses on the SAME
-- law at the residual (P′,Q)/(P,Q′).  It is therefore defined MUTUALLY with its REVERSE
-- (`rename-□-dist-∼` / `rename-□-dist-∼R`) so the backward direction's residual refers
-- to the reverse WITHOUT `sbisim-sym` (which would unguard) — the ExtChoiceComm /
-- ParallelUnit pattern.
--
-- Two structural subtleties:
--   • The overlap event (`evPQ`: both offer the renamed event, residual P₁ ⊓ Q₁) is
--     handled by REUSING `rename-⊓-dist-∼` imported from RenameIChoiceDist.
--   • The slide residuals (`sPQ`/`sQP`) need rename to distribute over `▷`; we prove a
--     small auxiliary STRONG bisim `rename-▷-dist-∼` (also mutual/reversed) for it.
--     (These cases fire only when the opposite operand is `ret`, but the auxiliary is
--      proved for GENERAL operands, which is cleaner.)

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.RenameEChoiceDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_□_; _⊓_; _▷_; ∅v; viewV)
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)

open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁; invRel; invPreimg; rnFan; rnCollect)
open import CSP.Laws.FD.RenameIChoiceDist E-≟ using (rename-⊓-dist-∼)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; ren-τ-fwd; ren-ev-fwd; ren-τ-inv; ren-ev-inv; ren-vis-just;
         force-ren-ret; force-ren-sil; force-ren-react;
         force-ren-sil-inv; force-ren-react-inv; force-ren-ret-inv)
open import CSP.Laws.Traces.TraceLaws E-≟
  using (force-▷-ret; ▷-ev-L; ▷-τ-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G;
         mergeVis-L-eq; mergeVis-R-eq; mergeVis-LQ-eq;
         □-τ-toslide; □-τ-tochoice; □-τ-toslide-R; □-τ-tochoice-R)
open import CSP.Laws.FD.ExtChoiceFD E-≟ using (□-τ-toP; □-τ-toQ)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (□-τ-elim; □-ev-elim;
         ▷-τ-elim; ▷-ev-elim; ▷-τ-nonret; ▷-timeout;
         react-τ-inv; br2-elim; □-slide-RQ-elim; □-slide-PR-elim; □-mt-elim;
         mergeVis-elim; viewT-τ;
         ret-no-τ; □-force-ret-inv)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- force-INVERSIONS needed to map a renamed non-ret node back to a source non-ret node.
-------------------------------------------------------------------------------------

-- if force (A ⟦ inv ⟧ⁱ) ≡ ret r then force A ≡ ret r (re-export of the inversion).
force-ren-ret-inv′ : ∀ {inv} {A : PTree E (ExtI E) R} {r}
                   → PTree.force (A ⟦ inv ⟧ⁱ) ≡ ret r → PTree.force A ≡ ret r
force-ren-ret-inv′ {A = A} eq with PTree.force A
... | ret _     = eq
... | sil _     = case eq of λ ()
... | react _ _ = case eq of λ ()

-- A renamed node that is non-ret comes from a non-ret source node.  (case on the
-- renamed force shape, invert each through the dedicated renameInv inversions.)
ren-nonret-inv : (inv : _) (A : PTree E (ExtI E) R)
                   {nAr : NodeKind E (ExtI E) R}
               → PTree.force (A ⟦ inv ⟧ⁱ) ≡ nAr → NonRet nAr
               → Σ[ nA ∈ NodeKind E (ExtI E) R ] (PTree.force A ≡ nA) × NonRet nA
ren-nonret-inv inv A {nAr = ret r}      eqAr ntAr = ⊥-elim ntAr
ren-nonret-inv inv A {nAr = sil A'r}    eqAr ntAr
  with force-ren-sil-inv {inv = inv} {P = A} eqAr
... | A₁ , eqA , _ = sil A₁ , eqA , tt
ren-nonret-inv inv A {nAr = react v τc} eqAr ntAr
  with force-ren-react-inv {inv = inv} {P = A} eqAr
... | vA , τcA , eqA , _ , _ = react vA τcA , eqA , tt

-- a renamed node is non-ret given the source is non-ret.
ren-nonret-fwd : (inv : _) (A : PTree E (ExtI E) R)
                   {nA : NodeKind E (ExtI E) R}
               → PTree.force A ≡ nA → NonRet nA
               → Σ[ nAr ∈ NodeKind E (ExtI E) R ] (PTree.force (A ⟦ inv ⟧ⁱ) ≡ nAr) × NonRet nAr
ren-nonret-fwd inv A {nA = ret r}      eqA ntA = ⊥-elim ntA
ren-nonret-fwd inv A {nA = sil A'}     eqA ntA =
  _ , force-ren-sil {inv = inv} {P = A} eqA , tt
ren-nonret-fwd inv A {nA = react v τc} eqA ntA =
  _ , force-ren-react {inv = inv} {P = A} eqA , tt

-------------------------------------------------------------------------------------
-- AUXILIARY: rename distributes over ▷ (also a mutual/reversed strong bisimulation).
-------------------------------------------------------------------------------------

rename-▷-dist-∼  : (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                   (A B : PTree E (ExtI E) R)
                 → ((A ▷ B) ⟦ inv ⟧ⁱ) ∼ ((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ))
rename-▷-dist-∼R : (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                   (A B : PTree E (ExtI E) R)
                 → ((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) ∼ ((A ▷ B) ⟦ inv ⟧ⁱ)

-- forward event handler:  (A▷B)⟦inv⟧ⁱ  ⟶  (A⟦inv⟧ⁱ)▷(B⟦inv⟧ⁱ)
▷-fwd-ev : (inv : _) (A B : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((A ▷ B) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M′) × (M ∼ M′)
▷-fwd-ev inv A B step with ren-ev-inv step
... | inj₁ (at , a , bt , b , M₁ , ABev , inveq , refl , refl) =
      let Aev = ▷-ev-elim A B ABev
      in (M₁ ⟦ inv ⟧ⁱ) , ▷-ev-L (ren-ev-fwd Aev inveq) , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
... | inj₂ (r , refl , eqret , refl) =
      deadlock , sRet (force-▷-ret {P = A ⟦ inv ⟧ⁱ} {Q = B ⟦ inv ⟧ⁱ}
                        (force-ren-ret {P = A} (▷-force-ret-A eqret)))
               , sbisim-refl deadlock
  where
    -- force (A ▷ B) ≡ ret r ⇒ force A ≡ ret r
    ▷-force-ret-A : PTree.force (A ▷ B) ≡ ret r → PTree.force A ≡ ret r
    ▷-force-ret-A eqf with PTree.force A
    ... | ret r'      = eqf
    ... | sil _       = case eqf of λ ()
    ... | react _ _   = case eqf of λ ()

-- forward tau handler
▷-fwd-tau : (inv : _) (A B : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
          → ((A ▷ B) ⟦ inv ⟧ⁱ) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              (((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × (M ∼ M′)
▷-fwd-tau inv A B step with ren-τ-inv step
... | M₁ , ABτ , refl with ▷-τ-elim A B ABτ
...   | inj₁ refl =
        case ▷-τ-nonret A B ABτ of λ where
          (nA , eqA , ntA) → case ren-nonret-fwd inv A eqA ntA of λ where
            (nAr , eqAr , ntAr) →
              (B ⟦ inv ⟧ⁱ) , ▷-timeout (A ⟦ inv ⟧ⁱ) (B ⟦ inv ⟧ⁱ) eqAr ntAr
                           , sbisim-refl (B ⟦ inv ⟧ⁱ)
...   | inj₂ (A' , Aτ , refl) =
        ((A' ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) , ▷-τ-L (ren-τ-fwd Aτ) , rename-▷-dist-∼ inv A' B

-- backward event handler:  (A⟦inv⟧ⁱ)▷(B⟦inv⟧ⁱ)  ⟶  (A▷B)⟦inv⟧ⁱ
▷-bwd-ev : (inv : _) (A B : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((A ▷ B) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M′) × (M ∼ M′)
▷-bwd-ev inv A B step with ren-ev-inv (▷-ev-elim (A ⟦ inv ⟧ⁱ) (B ⟦ inv ⟧ⁱ) step)
... | inj₁ (at , a , bt , b , M₁ , Aev , inveq , refl , refl) =
      (M₁ ⟦ inv ⟧ⁱ) , ren-ev-fwd (▷-ev-L Aev) inveq , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
... | inj₂ (r , refl , eqret , refl) =
      deadlock , ren-ev-fwd-√ , sbisim-refl deadlock
  where
    -- force A ≡ ret r ⇒ force (A ▷ B) ≡ ret r ⇒ a √ from (A▷B)⟦inv⟧ⁱ
    ren-ev-fwd-√ : ((A ▷ B) ⟦ inv ⟧ⁱ) ─[ ev (√ r) ]─► deadlock
    ren-ev-fwd-√ = sRet (force-ren-ret {P = A ▷ B} (force-▷-ret {P = A} {Q = B} eqret))

-- backward tau handler
▷-bwd-tau : (inv : _) (A B : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
          → ((A ⟦ inv ⟧ⁱ) ▷ (B ⟦ inv ⟧ⁱ)) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              (((A ▷ B) ⟦ inv ⟧ⁱ) ─[ τ ]─► M′) × (M ∼ M′)
▷-bwd-tau inv A B step with ▷-τ-elim (A ⟦ inv ⟧ⁱ) (B ⟦ inv ⟧ⁱ) step
... | inj₁ refl =
      case ▷-τ-nonret (A ⟦ inv ⟧ⁱ) (B ⟦ inv ⟧ⁱ) step of λ where
        (nAr , eqAr , ntAr) → case ren-nonret-inv inv A eqAr ntAr of λ where
          (nA , eqA , ntA) →
            (B ⟦ inv ⟧ⁱ) , ren-τ-fwd (▷-timeout A B eqA ntA)
                         , sbisim-refl (B ⟦ inv ⟧ⁱ)
... | inj₂ (A'r , Aτr , refl) with ren-τ-inv Aτr
...   | A₁ , Aτ , refl =
        ((A₁ ▷ B) ⟦ inv ⟧ⁱ) , ren-τ-fwd (▷-τ-L Aτ) , rename-▷-dist-∼R inv A₁ B

rename-▷-dist-∼ inv A B .Sbisim.fwd .SSimF.on-ev  = ▷-fwd-ev  inv A B
rename-▷-dist-∼ inv A B .Sbisim.fwd .SSimF.on-tau = ▷-fwd-tau inv A B
rename-▷-dist-∼ inv A B .Sbisim.bwd .SSimF.on-ev  = ▷-bwd-ev  inv A B
rename-▷-dist-∼ inv A B .Sbisim.bwd .SSimF.on-tau = ▷-bwd-tau inv A B

rename-▷-dist-∼R inv A B .Sbisim.fwd .SSimF.on-ev  = ▷-bwd-ev  inv A B
rename-▷-dist-∼R inv A B .Sbisim.fwd .SSimF.on-tau = ▷-bwd-tau inv A B
rename-▷-dist-∼R inv A B .Sbisim.bwd .SSimF.on-ev  = ▷-fwd-ev  inv A B
rename-▷-dist-∼R inv A B .Sbisim.bwd .SSimF.on-tau = ▷-fwd-tau inv A B

-------------------------------------------------------------------------------------
-- MAIN: rename distributes over □ (mutual/reversed strong bisimulation).
-------------------------------------------------------------------------------------

rename-□-dist-∼  : ⦃ _ : DecEq R ⦄ (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                   (P Q : PTree E (ExtI E) R)
                 → ((P □ Q) ⟦ inv ⟧ⁱ) ∼ ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ))
rename-□-dist-∼R : ⦃ _ : DecEq R ⦄ (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                   (P Q : PTree E (ExtI E) R)
                 → ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ∼ ((P □ Q) ⟦ inv ⟧ⁱ)

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

-- the renamed offer at a source-non-offer is nothing (no fan-in: invPreimg is a singleton).
ren-vis-nothing :
    ∀ {inv} {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {bt b at a}
  → inv bt b ≡ just (at , a) → vP at a ≡ nothing
  → rnFan (invRel inv) (invPreimg inv) (rnCollect vP (invPreimg inv bt b)) ≡ nothing
ren-vis-nothing {inv = inv} {vP = vP} {bt = bt} {b = b} eq-inv eq-v
  with inv bt b | eq-inv
... | just (at , a) | refl with vP at a | eq-v
...   | nothing | refl = refl

-- the renamed visible-offer map of a source map vA (the shape force-ren-react produces).
RenMap : (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
       → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
       → (bt : AnyTypes E) → proj₁ bt → Maybe (PTree E (ExtI E) R)
RenMap inv vA bt b = rnFan (invRel inv) (invPreimg inv) (rnCollect vA (invPreimg inv bt b))

-- the renamed force shape of a non-ret operand (commodity wrapper over ren-nonret-fwd).
ren-NonRet-force : (inv : _) (A : PTree E (ExtI E) R) {nA : NodeKind E (ExtI E) R}
                 → PTree.force A ≡ nA → NonRet nA → NonRet (PTree.force (A ⟦ inv ⟧ⁱ))
ren-NonRet-force inv A eqA ntA with ren-nonret-fwd inv A eqA ntA
... | nAr , eqAr , ntAr = subst NonRet (sym eqAr) ntAr

-------------------------------------------------------------------------------------
-- MAIN handlers (forward declarations; bodies follow, then the wiring).
-------------------------------------------------------------------------------------

-- forward visible/√ : (P□Q)⟦inv⟧ⁱ  ⟶  (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)
□-fwd-ev : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R)
             {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((P □ Q) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M′) × (M ∼ M′)

-- forward τ : (P□Q)⟦inv⟧ⁱ  ⟶  (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)
□-fwd-tau : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
          → ((P □ Q) ⟦ inv ⟧ⁱ) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              (((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × (M ∼ M′)

-- forward τ, both operands live (the choice τ-tag; recurses on the law).
□-fwd-tau-both : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R)
                   (nP nQ : NodeKind E (ExtI E) R)
                   {M₁ : PTree E (ExtI E) R}
               → PTree.force P ≡ nP → PTree.force Q ≡ nQ → NonRet nP → NonRet nQ
               → (P □ Q) ─[ τ ]─► M₁
               → Σ[ M′ ∈ PTree E (ExtI E) R ]
                   (((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × ((M₁ ⟦ inv ⟧ⁱ) ∼ M′)

-- backward visible/√ : (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)  ⟶  (P□Q)⟦inv⟧ⁱ
□-bwd-ev : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R)
             {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((P □ Q) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M′) × (M ∼ M′)

-- backward τ : (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)  ⟶  (P□Q)⟦inv⟧ⁱ
□-bwd-tau : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
          → ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              (((P □ Q) ⟦ inv ⟧ⁱ) ─[ τ ]─► M′) × (M ∼ M′)

-- backward τ, both operands live (renamed sides non-ret).
bwd-both : ⦃ _ : DecEq R ⦄ (inv : _) (P Q : PTree E (ExtI E) R)
             (nP nQ : NodeKind E (ExtI E) R)
             {M₁ : PTree E (ExtI E) R}
         → PTree.force (P ⟦ inv ⟧ⁱ) ≡ nP → PTree.force (Q ⟦ inv ⟧ⁱ) ≡ nQ
         → NonRet nP → NonRet nQ → NonRet (PTree.force P) → NonRet (PTree.force Q)
         → ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M₁
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((P □ Q) ⟦ inv ⟧ⁱ) ─[ τ ]─► M′) × (M₁ ∼ M′)

□-fwd-ev inv P Q step with ren-ev-inv step
... | inj₂ (r , refl , eqret , refl) =
      deadlock
    , sRet (fL-A {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                 (force-ren-ret {P = P} (□-force-ret-inv {P = P} {Q = Q} eqret))
                 (force-ren-ret {P = Q} (□-force-ret-inv-R {P = P} {Q = Q} eqret)))
    , sbisim-refl deadlock
... | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
      with PTree.force P in eqP | PTree.force Q in eqQ
...   | ret rP | ret rQ with rP ≟ rQ
...     | yes refl = case eqf of λ ()
...     | no ¬eq   = case (subst (λ f → f at a ≡ just _)
                            (sym (proj₁ (react-injective eqf))) br) of λ ()
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | ret rP | sil Q' =
      case (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ ()
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | ret rP | react vQ τcQ =
      (M₁ ⟦ inv ⟧ⁱ)
    , sVis (fL-D {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                 (force-ren-ret {P = P} eqP) (force-ren-react {P = Q} eqQ))
           (ren-vis-just {inv = inv} inveq
              (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br))
    , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | sil P' | ret rQ =
      case (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ ()
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | react vP τcP | ret rQ =
      (M₁ ⟦ inv ⟧ⁱ)
    , sVis (fL-F {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                 (force-ren-react {P = P} eqP) (force-ren-ret {P = Q} eqQ))
           (ren-vis-just {inv = inv} inveq
              (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br))
    , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | sil P' | sil Q' =
      case mergeVis-elim ∅v ∅v at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , () , _)))
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | sil P' | react vQ τcQ =
      case mergeVis-elim ∅v vQ at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (_ , vQm))) →
          (M₁ ⟦ inv ⟧ⁱ)
            , sVis (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                         (force-ren-sil {P = P} eqP) (force-ren-react {P = Q} eqQ) tt tt)
                   (mergeVis-R-eq {vP = ∅v} {vQ = RenMap inv vQ} refl
                                  (ren-vis-just {inv = inv} {vP = vQ} inveq vQm))
            , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₂ (_ , _ , () , _)))
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | react vP τcP | sil Q' =
      case mergeVis-elim vP ∅v at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (vPm , _)) →
          (M₁ ⟦ inv ⟧ⁱ)
            , sVis (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                         (force-ren-react {P = P} eqP) (force-ren-sil {P = Q} eqQ) tt tt)
                   (mergeVis-L-eq {vP = RenMap inv vP} {vQ = ∅v}
                                  (ren-vis-just {inv = inv} {vP = vP} inveq vPm) refl)
            , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , _ , () , _)))
□-fwd-ev inv P Q step | inj₁ (at , a , bt , b , M₁ , sVis eqf br , inveq , refl , refl)
    | react vP τcP | react vQ τcQ =
      case mergeVis-elim vP vQ at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (vPm , vQn)) →
          (M₁ ⟦ inv ⟧ⁱ)
            , sVis (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                         (force-ren-react {P = P} eqP) (force-ren-react {P = Q} eqQ) tt tt)
                   (mergeVis-L-eq {vP = RenMap inv vP} {vQ = RenMap inv vQ}
                                  (ren-vis-just {inv = inv} {vP = vP} inveq vPm)
                                  (ren-vis-nothing {inv = inv} {vP = vQ} inveq vQn))
            , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₁ (vPn , vQm))) →
          (M₁ ⟦ inv ⟧ⁱ)
            , sVis (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                         (force-ren-react {P = P} eqP) (force-ren-react {P = Q} eqQ) tt tt)
                   (mergeVis-R-eq {vP = RenMap inv vP} {vQ = RenMap inv vQ}
                                  (ren-vis-nothing {inv = inv} {vP = vP} inveq vPn)
                                  (ren-vis-just {inv = inv} {vP = vQ} inveq vQm))
            , sbisim-refl (M₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₂ (P₁ , Q₁ , vPm , vQm , refl))) →
          ((P₁ ⟦ inv ⟧ⁱ) ⊓ (Q₁ ⟦ inv ⟧ⁱ))
            , sVis (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                         (force-ren-react {P = P} eqP) (force-ren-react {P = Q} eqQ) tt tt)
                   (mergeVis-LQ-eq {vP = RenMap inv vP} {vQ = RenMap inv vQ}
                                   (ren-vis-just {inv = inv} {vP = vP} inveq vPm)
                                   (ren-vis-just {inv = inv} {vP = vQ} inveq vQm))
            , rename-⊓-dist-∼ inv P₁ Q₁

-- forward τ : (P□Q)⟦inv⟧ⁱ  ⟶  (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)
□-fwd-tau inv P Q step with ren-τ-inv step
... | M₁ , PQτ , refl with PTree.force P in eqP | PTree.force Q in eqQ
...   | ret rP | ret rQ with rP ≟ rQ
...     | yes refl = ⊥-elim (ret-no-τ (fL-A {P = P} {Q = Q} eqP eqQ) PQτ)
...     | no ¬eq = case react-τ-inv (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) PQτ of λ where
          (i , a , breq) → case br2-elim P Q {i = i} {a = a} breq of λ where
            (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                        , sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                               (fL-B {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                                     (force-ren-ret {P = P} eqP) (force-ren-ret {P = Q} eqQ) ¬eq) refl
                        , sbisim-refl (P ⟦ inv ⟧ⁱ)
            (inj₂ refl) → (Q ⟦ inv ⟧ⁱ)
                        , sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                               (fL-B {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ}
                                     (force-ren-ret {P = P} eqP) (force-ren-ret {P = Q} eqQ) ¬eq) refl
                        , sbisim-refl (Q ⟦ inv ⟧ⁱ)
□-fwd-tau inv P Q step | M₁ , PQτ , refl | ret rP | sil Q' =
  case react-τ-inv (fL-C {P = P} {Q = Q} eqP eqQ) PQτ of λ where
    (i , a , breq) → case □-slide-RQ-elim P (sil Q') {i = i} {a = a} breq of λ where
      (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                  , □-τ-toP (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                            (force-ren-ret {P = P} eqP) (ren-NonRet-force inv Q eqQ tt)
                  , sbisim-refl (P ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , Q'' , veq , refl)) →
        ((Q'' ⟦ inv ⟧ⁱ) ▷ (P ⟦ inv ⟧ⁱ))
          , □-τ-toslide-R (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                          (ren-τ-fwd (viewT-τ eqQ veq)) (force-ren-ret {P = P} eqP)
          , rename-▷-dist-∼ inv Q'' P
□-fwd-tau inv P Q step | M₁ , PQτ , refl | ret rP | react vQ τcQ =
  case react-τ-inv (fL-D {P = P} {Q = Q} eqP eqQ) PQτ of λ where
    (i , a , breq) → case □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} breq of λ where
      (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                  , □-τ-toP (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                            (force-ren-ret {P = P} eqP) (ren-NonRet-force inv Q eqQ tt)
                  , sbisim-refl (P ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , Q'' , veq , refl)) →
        ((Q'' ⟦ inv ⟧ⁱ) ▷ (P ⟦ inv ⟧ⁱ))
          , □-τ-toslide-R (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                          (ren-τ-fwd (viewT-τ eqQ veq)) (force-ren-ret {P = P} eqP)
          , rename-▷-dist-∼ inv Q'' P
□-fwd-tau inv P Q step | M₁ , PQτ , refl | sil P' | ret rQ =
  case react-τ-inv (fL-E {P = P} {Q = Q} eqP eqQ) PQτ of λ where
    (i , a , breq) → case □-slide-PR-elim (sil P') Q {i = i} {a = a} breq of λ where
      (inj₁ refl) → (Q ⟦ inv ⟧ⁱ)
                  , □-τ-toQ (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                            (ren-NonRet-force inv P eqP tt) (force-ren-ret {P = Q} eqQ)
                  , sbisim-refl (Q ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , P'' , veq , refl)) →
        ((P'' ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))
          , □-τ-toslide (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                        (ren-τ-fwd (viewT-τ eqP veq)) (force-ren-ret {P = Q} eqQ)
          , rename-▷-dist-∼ inv P'' Q
□-fwd-tau inv P Q step | M₁ , PQτ , refl | react vP τcP | ret rQ =
  case react-τ-inv (fL-F {P = P} {Q = Q} eqP eqQ) PQτ of λ where
    (i , a , breq) → case □-slide-PR-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
      (inj₁ refl) → (Q ⟦ inv ⟧ⁱ)
                  , □-τ-toQ (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                            (ren-NonRet-force inv P eqP tt) (force-ren-ret {P = Q} eqQ)
                  , sbisim-refl (Q ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , P'' , veq , refl)) →
        ((P'' ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))
          , □-τ-toslide (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                        (ren-τ-fwd (viewT-τ eqP veq)) (force-ren-ret {P = Q} eqQ)
          , rename-▷-dist-∼ inv P'' Q
□-fwd-tau inv P Q step | M₁ , PQτ , refl | sil P' | sil Q' =
  □-fwd-tau-both inv P Q (sil P') (sil Q') eqP eqQ tt tt PQτ
□-fwd-tau inv P Q step | M₁ , PQτ , refl | sil P' | react vQ τcQ =
  □-fwd-tau-both inv P Q (sil P') (react vQ τcQ) eqP eqQ tt tt PQτ
□-fwd-tau inv P Q step | M₁ , PQτ , refl | react vP τcP | sil Q' =
  □-fwd-tau-both inv P Q (react vP τcP) (sil Q') eqP eqQ tt tt PQτ
□-fwd-tau inv P Q step | M₁ , PQτ , refl | react vP τcP | react vQ τcQ =
  □-fwd-tau-both inv P Q (react vP τcP) (react vQ τcQ) eqP eqQ tt tt PQτ

-- both operands live: the source τ is a choice-τ of P or of Q (recurse on the law).
□-fwd-tau-both inv P Q nP nQ eqP eqQ ntP ntQ PQτ =
  case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ ntP ntQ) PQτ of λ where
    (i , a , breq) → case □-mt-elim nP nQ P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , refl)) →
        ((P' ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ))
          , □-τ-tochoice (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                         (ren-τ-fwd (viewT-τ eqP veq)) refl (ren-NonRet-force inv Q eqQ ntQ)
          , rename-□-dist-∼ inv P' Q
      (inj₂ (j , a' , Q' , veq , refl)) →
        ((P ⟦ inv ⟧ⁱ) □ (Q' ⟦ inv ⟧ⁱ))
          , □-τ-tochoice-R (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ)
                           (ren-τ-fwd (viewT-τ eqQ veq)) refl (ren-NonRet-force inv P eqP ntP)
          , rename-□-dist-∼ inv P Q'

-------------------------------------------------------------------------------------
-- BACKWARD handlers: (P⟦inv⟧ⁱ)□(Q⟦inv⟧ⁱ)  ⟶  (P□Q)⟦inv⟧ⁱ
-------------------------------------------------------------------------------------

-- A renamed react node inverts to a source react node + the source offer it came from.
ren-react-offer-inv :
    (inv : _) (A : PTree E (ExtI E) R)
      {v′ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc′ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
  → PTree.force (A ⟦ inv ⟧ⁱ) ≡ react v′ τc′ → v′ at a ≡ just M
  → Σ[ at₀ ∈ AnyTypes E ] Σ[ a₀ ∈ proj₁ at₀ ] Σ[ A₁ ∈ PTree E (ExtI E) R ]
      Σ[ vA ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
      Σ[ τcA ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
        (inv at a ≡ just (at₀ , a₀)) × (PTree.force A ≡ react vA τcA)
        × (vA at₀ a₀ ≡ just A₁) × (M ≡ A₁ ⟦ inv ⟧ⁱ)
ren-react-offer-inv inv A {at = at} {a = a} eqr off
  with ren-ev-inv {P = A} (sVis {at = at} {a = a} eqr off)
... | inj₁ (at₀ , a₀ , bt , b , A₁ , sVis {v = vA} {τc = τcA} eqA offA , inveq , refl , refl) =
      at₀ , a₀ , A₁ , vA , τcA , inveq , eqA , offA , refl

-- a renamed non-offer at (at,a) decoded through inv to (at₀,a₀) is a source non-offer.
ren-vis-nothing-inv :
    ∀ {inv} {vA : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {at a at₀ a₀}
  → inv at a ≡ just (at₀ , a₀)
  → rnFan (invRel inv) (invPreimg inv) (rnCollect vA (invPreimg inv at a)) ≡ nothing
  → vA at₀ a₀ ≡ nothing
ren-vis-nothing-inv {inv = inv} {vA = vA} {at = at} {a = a} inveq eqn
  with inv at a | inveq
... | just (at₀ , a₀) | refl with vA at₀ a₀ in eqv
...   | nothing = refl
...   | just A₁  = case eqn of λ ()

-- backward visible/√.  Mirror of □-fwd-ev on the renamed force-pair.
□-bwd-ev inv P Q (sRet eqf) = deadlock , √step , sbisim-refl deadlock
  where
    rP : PTree.force P ≡ ret _
    rP = force-ren-ret-inv {P = P} (□-force-ret-inv {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqf)
    rQ : PTree.force Q ≡ ret _
    rQ = force-ren-ret-inv {P = Q} (□-force-ret-inv-R {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqf)
    √step : ((P □ Q) ⟦ inv ⟧ⁱ) ─[ ev (√ _) ]─► deadlock
    √step = sRet (force-ren-ret {P = P □ Q} (fL-A {P = P} {Q = Q} rP rQ))
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br)
  with PTree.force (P ⟦ inv ⟧ⁱ) in eqPr | PTree.force (Q ⟦ inv ⟧ⁱ) in eqQr
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = case eqf of λ ()
...   | no ¬eq   = case (subst (λ f → f at a ≡ just _)
                          (sym (proj₁ (react-injective eqf))) br) of λ ()
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | ret rP | sil Q'r =
      case (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ ()
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | ret rP | react vQr τcQr =
  case ren-react-offer-inv inv Q eqQr
         (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
    (at₀ , a₀ , Q₁ , vQ , τcQ , inveq , eqQ , offQ , refl) →
      (Q₁ ⟦ inv ⟧ⁱ)
        , ren-ev-fwd (sVis (fL-D {P = P} {Q = Q} (force-ren-ret-inv {P = P} eqPr) eqQ) offQ) inveq
        , sbisim-refl (Q₁ ⟦ inv ⟧ⁱ)
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | sil P'r | ret rQ =
      case (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ ()
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | react vP'r τcP'r | ret rQ =
  case ren-react-offer-inv inv P eqPr
         (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
    (at₀ , a₀ , P₁ , vP , τcP , inveq , eqP , offP , refl) →
      (P₁ ⟦ inv ⟧ⁱ)
        , ren-ev-fwd (sVis (fL-F {P = P} {Q = Q} eqP (force-ren-ret-inv {P = Q} eqQr)) offP) inveq
        , sbisim-refl (P₁ ⟦ inv ⟧ⁱ)
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | sil P'r | sil Q'r =
      case mergeVis-elim ∅v ∅v at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , () , _)))
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | sil P'r | react vQr τcQr =
      case mergeVis-elim ∅v vQr at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (() , _))
        (inj₂ (inj₁ (_ , vQrm))) →
          case force-ren-sil-inv {P = P} eqPr of λ where
            (P₁ , eqP , _) → case ren-react-offer-inv inv Q eqQr vQrm of λ where
              (at₀ , a₀ , Q₁ , vQ , τcQ , inveq , eqQ , offQ , refl) →
                (Q₁ ⟦ inv ⟧ⁱ)
                  , ren-ev-fwd
                      (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                            (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl offQ)) inveq
                  , sbisim-refl (Q₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₂ (_ , _ , () , _)))
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | react vP'r τcP'r | sil Q'r =
      case mergeVis-elim vP'r ∅v at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (vP'rm , _)) →
          case force-ren-sil-inv {P = Q} eqQr of λ where
            (Q₁ , eqQ , _) → case ren-react-offer-inv inv P eqPr vP'rm of λ where
              (at₀ , a₀ , P₁ , vP , τcP , inveq , eqP , offP , refl) →
                (P₁ ⟦ inv ⟧ⁱ)
                  , ren-ev-fwd
                      (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                            (mergeVis-L-eq {vP = vP} {vQ = ∅v} offP refl)) inveq
                  , sbisim-refl (P₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₁ (_ , ())))
        (inj₂ (inj₂ (_ , _ , _ , () , _)))
□-bwd-ev inv P Q (sVis {at = at} {a = a} eqf br) | react vP'r τcP'r | react vQr τcQr =
      case mergeVis-elim vP'r vQr at a
             (subst (λ f → f at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (vP'rm , vQrn)) →
          case force-ren-react-inv {P = Q} eqQr of λ where
            (vQ , τcQ , eqQ , refl , _) → case ren-react-offer-inv inv P eqPr vP'rm of λ where
              (at₀ , a₀ , P₁ , vP , τcP , inveq , eqP , offP , refl) →
                (P₁ ⟦ inv ⟧ⁱ)
                  , ren-ev-fwd
                      (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                            (mergeVis-L-eq {vP = vP} {vQ = vQ} offP
                               (ren-vis-nothing-inv {vA = vQ} inveq vQrn))) inveq
                  , sbisim-refl (P₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₁ (vP'rn , vQrm))) →
          case force-ren-react-inv {P = P} eqPr of λ where
            (vP , τcP , eqP , refl , _) → case ren-react-offer-inv inv Q eqQr vQrm of λ where
              (at₀ , a₀ , Q₁ , vQ , τcQ , inveq , eqQ , offQ , refl) →
                (Q₁ ⟦ inv ⟧ⁱ)
                  , ren-ev-fwd
                      (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                            (mergeVis-R-eq {vP = vP} {vQ = vQ}
                               (ren-vis-nothing-inv {vA = vP} inveq vP'rn) offQ)) inveq
                  , sbisim-refl (Q₁ ⟦ inv ⟧ⁱ)
        (inj₂ (inj₂ (P₁r , Q₁r , vP'rm , vQrm , refl))) →
          case ren-react-offer-inv inv P eqPr vP'rm of λ where
            (at₀ , a₀ , P₁ , vP , τcP , inveqP , eqP , offP , refl) →
              case ren-react-offer-inv inv Q eqQr vQrm of λ where
                (at₁ , a₁ , Q₁ , vQ , τcQ , inveqQ , eqQ , offQ , refl) →
                  ((P₁ ⊓ Q₁) ⟦ inv ⟧ⁱ)
                    , ren-ev-fwd
                        (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                              (mergeVis-LQ-eq {vP = vP} {vQ = vQ} offP
                                 (alignQ {vQ = vQ} inveqP inveqQ offQ))) inveqP
                    , sbisim-sym (rename-⊓-dist-∼ inv P₁ Q₁)
  where
    -- the two source offers share the source index (inj is value-injective on inv).
    alignQ : ∀ {at₀ a₀ at₁ a₁}
               {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {Q₁ : PTree E (ExtI E) R}
           → inv at a ≡ just (at₀ , a₀) → inv at a ≡ just (at₁ , a₁) → vQ at₁ a₁ ≡ just Q₁
           → vQ at₀ a₀ ≡ just Q₁
    alignQ {vQ = vQ} {Q₁ = Q₁} ip iq off =
      subst (λ ce → vQ (proj₁ ce) (proj₂ ce) ≡ just Q₁)
            (just-injective (trans (sym iq) ip)) off

-- backward τ.  Classify on the renamed operands' force shapes (mirror of □-comm-tau),
-- invert the renamed τ to a source τ, build the source step, push it forward.
□-bwd-tau inv P Q step with PTree.force (P ⟦ inv ⟧ⁱ) in eqPr | PTree.force (Q ⟦ inv ⟧ⁱ) in eqQr
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = ⊥-elim (ret-no-τ (fL-A {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr) step)
...   | no ¬eq = case react-τ-inv (fL-B {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr ¬eq) step of λ where
        (i , a , breq) → case br2-elim (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) {i = i} {a = a} breq of λ where
          (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                      , ren-τ-fwd (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                                        (fL-B {P = P} {Q = Q}
                                              (force-ren-ret-inv {P = P} eqPr)
                                              (force-ren-ret-inv {P = Q} eqQr) ¬eq) refl)
                      , sbisim-refl (P ⟦ inv ⟧ⁱ)
          (inj₂ refl) → (Q ⟦ inv ⟧ⁱ)
                      , ren-τ-fwd (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                                        (fL-B {P = P} {Q = Q}
                                              (force-ren-ret-inv {P = P} eqPr)
                                              (force-ren-ret-inv {P = Q} eqQr) ¬eq) refl)
                      , sbisim-refl (Q ⟦ inv ⟧ⁱ)
□-bwd-tau inv P Q step | ret rP | sil Q'r =
  case react-τ-inv (fL-C {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr) step of λ where
    (i , a , breq) → case □-slide-RQ-elim (P ⟦ inv ⟧ⁱ) (sil Q'r) {i = i} {a = a} breq of λ where
      (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                  , ren-τ-fwd (□-τ-toP P Q (force-ren-ret-inv {P = P} eqPr) (Qnr eqQr))
                  , sbisim-refl (P ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , Q'' , veq , refl)) → case ren-τ-inv {P = Q} (viewT-τ eqQr veq) of λ where
        (Q₁ , Qτ , refl) →
          ((Q₁ ▷ P) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-toslide-R P Q Qτ (force-ren-ret-inv {P = P} eqPr))
            , rename-▷-dist-∼R inv Q₁ P
  where
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ sil Q'r → NonRet (PTree.force Q)
    Qnr e with force-ren-sil-inv {P = Q} e
    ... | Q₁ , eqQ , _ = subst NonRet (sym eqQ) tt
□-bwd-tau inv P Q step | ret rP | react vQr τcQr =
  case react-τ-inv (fL-D {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr) step of λ where
    (i , a , breq) → case □-slide-RQ-elim (P ⟦ inv ⟧ⁱ) (react vQr τcQr) {i = i} {a = a} breq of λ where
      (inj₁ refl) → (P ⟦ inv ⟧ⁱ)
                  , ren-τ-fwd (□-τ-toP P Q (force-ren-ret-inv {P = P} eqPr) (Qnr eqQr))
                  , sbisim-refl (P ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , Q'' , veq , refl)) → case ren-τ-inv {P = Q} (viewT-τ eqQr veq) of λ where
        (Q₁ , Qτ , refl) →
          ((Q₁ ▷ P) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-toslide-R P Q Qτ (force-ren-ret-inv {P = P} eqPr))
            , rename-▷-dist-∼R inv Q₁ P
  where
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ react vQr τcQr → NonRet (PTree.force Q)
    Qnr e with force-ren-react-inv {P = Q} e
    ... | vQ , τcQ , eqQ , _ , _ = subst NonRet (sym eqQ) tt
□-bwd-tau inv P Q step | sil P'r | ret rQ =
  case react-τ-inv (fL-E {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr) step of λ where
    (i , a , breq) → case □-slide-PR-elim (sil P'r) (Q ⟦ inv ⟧ⁱ) {i = i} {a = a} breq of λ where
      (inj₁ refl) → (Q ⟦ inv ⟧ⁱ)
                  , ren-τ-fwd (□-τ-toQ P Q (Pnr eqPr) (force-ren-ret-inv {P = Q} eqQr))
                  , sbisim-refl (Q ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , P'' , veq , refl)) → case ren-τ-inv {P = P} (viewT-τ eqPr veq) of λ where
        (P₁ , Pτ , refl) →
          ((P₁ ▷ Q) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-toslide P Q Pτ (force-ren-ret-inv {P = Q} eqQr))
            , rename-▷-dist-∼R inv P₁ Q
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil P'r → NonRet (PTree.force P)
    Pnr e with force-ren-sil-inv {P = P} e
    ... | P₁ , eqP , _ = subst NonRet (sym eqP) tt
□-bwd-tau inv P Q step | react vP'r τcP'r | ret rQ =
  case react-τ-inv (fL-F {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr) step of λ where
    (i , a , breq) → case □-slide-PR-elim (react vP'r τcP'r) (Q ⟦ inv ⟧ⁱ) {i = i} {a = a} breq of λ where
      (inj₁ refl) → (Q ⟦ inv ⟧ⁱ)
                  , ren-τ-fwd (□-τ-toQ P Q (Pnr eqPr) (force-ren-ret-inv {P = Q} eqQr))
                  , sbisim-refl (Q ⟦ inv ⟧ⁱ)
      (inj₂ (j , a' , P'' , veq , refl)) → case ren-τ-inv {P = P} (viewT-τ eqPr veq) of λ where
        (P₁ , Pτ , refl) →
          ((P₁ ▷ Q) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-toslide P Q Pτ (force-ren-ret-inv {P = Q} eqQr))
            , rename-▷-dist-∼R inv P₁ Q
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ react vP'r τcP'r → NonRet (PTree.force P)
    Pnr e with force-ren-react-inv {P = P} e
    ... | vP , τcP , eqP , _ , _ = subst NonRet (sym eqP) tt
□-bwd-tau inv P Q step | sil P'r | sil Q'r =
  bwd-both inv P Q (sil P'r) (sil Q'r) eqPr eqQr tt tt (Pnr eqPr) (Qnr eqQr) step
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil P'r → NonRet (PTree.force P)
    Pnr e with force-ren-sil-inv {P = P} e
    ... | P₁ , eqP , _ = subst NonRet (sym eqP) tt
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ sil Q'r → NonRet (PTree.force Q)
    Qnr e with force-ren-sil-inv {P = Q} e
    ... | Q₁ , eqQ , _ = subst NonRet (sym eqQ) tt
□-bwd-tau inv P Q step | sil P'r | react vQr τcQr =
  bwd-both inv P Q (sil P'r) (react vQr τcQr) eqPr eqQr tt tt (Pnr eqPr) (Qnr eqQr) step
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ sil P'r → NonRet (PTree.force P)
    Pnr e with force-ren-sil-inv {P = P} e
    ... | P₁ , eqP , _ = subst NonRet (sym eqP) tt
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ react vQr τcQr → NonRet (PTree.force Q)
    Qnr e with force-ren-react-inv {P = Q} e
    ... | vQ , τcQ , eqQ , _ , _ = subst NonRet (sym eqQ) tt
□-bwd-tau inv P Q step | react vP'r τcP'r | sil Q'r =
  bwd-both inv P Q (react vP'r τcP'r) (sil Q'r) eqPr eqQr tt tt (Pnr eqPr) (Qnr eqQr) step
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ react vP'r τcP'r → NonRet (PTree.force P)
    Pnr e with force-ren-react-inv {P = P} e
    ... | vP , τcP , eqP , _ , _ = subst NonRet (sym eqP) tt
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ sil Q'r → NonRet (PTree.force Q)
    Qnr e with force-ren-sil-inv {P = Q} e
    ... | Q₁ , eqQ , _ = subst NonRet (sym eqQ) tt
□-bwd-tau inv P Q step | react vP'r τcP'r | react vQr τcQr =
  bwd-both inv P Q (react vP'r τcP'r) (react vQr τcQr) eqPr eqQr tt tt (Pnr eqPr) (Qnr eqQr) step
  where
    Pnr : PTree.force (P ⟦ inv ⟧ⁱ) ≡ react vP'r τcP'r → NonRet (PTree.force P)
    Pnr e with force-ren-react-inv {P = P} e
    ... | vP , τcP , eqP , _ , _ = subst NonRet (sym eqP) tt
    Qnr : PTree.force (Q ⟦ inv ⟧ⁱ) ≡ react vQr τcQr → NonRet (PTree.force Q)
    Qnr e with force-ren-react-inv {P = Q} e
    ... | vQ , τcQ , eqQ , _ , _ = subst NonRet (sym eqQ) tt

-- backward τ, both renamed operands live: a choice-τ of P⟦⟧ or Q⟦⟧.  Invert to a
-- source τ, rebuild the source choice step, recurse on the law (reverse direction).
bwd-both inv P Q nP nQ eqPr eqQr nrP nrQ ntP ntQ step =
  case react-τ-inv (fL-G {P = P ⟦ inv ⟧ⁱ} {Q = Q ⟦ inv ⟧ⁱ} eqPr eqQr nrP nrQ) step of λ where
    (i , a , breq) → case □-mt-elim nP nQ (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P'r , veq , refl)) → case ren-τ-inv {P = P} (viewT-τ eqPr veq) of λ where
        (P₁ , Pτ , refl) →
          ((P₁ □ Q) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-tochoice P Q Pτ refl ntQ)
            , rename-□-dist-∼R inv P₁ Q
      (inj₂ (j , a' , Q'r , veq , refl)) → case ren-τ-inv {P = Q} (viewT-τ eqQr veq) of λ where
        (Q₁ , Qτ , refl) →
          ((P □ Q₁) ⟦ inv ⟧ⁱ)
            , ren-τ-fwd (□-τ-tochoice-R P Q Qτ refl ntP)
            , rename-□-dist-∼R inv P Q₁


rename-□-dist-∼  inv P Q .Sbisim.fwd .SSimF.on-ev  = □-fwd-ev  inv P Q
rename-□-dist-∼  inv P Q .Sbisim.fwd .SSimF.on-tau = □-fwd-tau inv P Q
rename-□-dist-∼  inv P Q .Sbisim.bwd .SSimF.on-ev  = □-bwd-ev  inv P Q
rename-□-dist-∼  inv P Q .Sbisim.bwd .SSimF.on-tau = □-bwd-tau inv P Q
rename-□-dist-∼R inv P Q .Sbisim.fwd .SSimF.on-ev  = □-bwd-ev  inv P Q
rename-□-dist-∼R inv P Q .Sbisim.fwd .SSimF.on-tau = □-bwd-tau inv P Q
rename-□-dist-∼R inv P Q .Sbisim.bwd .SSimF.on-ev  = □-fwd-ev  inv P Q
rename-□-dist-∼R inv P Q .Sbisim.bwd .SSimF.on-tau = □-fwd-tau inv P Q

rename-□-dist-FD : ⦃ _ : DecEq R ⦄
                   (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                   (P Q : PTree E (ExtI E) R)
                 → ((P □ Q) ⟦ inv ⟧ⁱ) ≈FD ((P ⟦ inv ⟧ⁱ) □ (Q ⟦ inv ⟧ⁱ))
rename-□-dist-FD inv P Q = drbisim→≈FD (sbisim→drbisim (rename-□-dist-∼ inv P Q))
