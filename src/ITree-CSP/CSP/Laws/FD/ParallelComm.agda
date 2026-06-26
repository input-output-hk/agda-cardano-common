{-# OPTIONS --guardedness #-}

-- Parallel commutativity (⊤ / interleaving case) via STRONG BISIMULATION.
--
--   Par⊤-comm   : Par⊤ A P Q ∼ Par⊤ A Q P
--   Par⊤-comm-FD : Par⊤ A P Q ≈FD Par⊤ A Q P   (lifted)
--   ⦀-comm-FD   : (P ⦀ Q) ≈FD (Q ⦀ P)                     (cs = ∅ instance)
--
-- The ⊤-merge (λ _ _ → tt) is symmetric, so the two composites are genuinely
-- bisimilar (no merge-flip needed: the √ value is tt on both sides).  Each step of
-- Par P Q is matched by the mirror step of Par Q P:
--   • on-tau : Par-τ-elim → Par-τ-R / Par-τ-L, continuation Par-comm;
--   • on-ev  : force-case (par-pVis-elim keeps the offer witnesses) → the swapped
--     sync / solo / both / √ constructor; the both-offer overlap node
--     (Par P' Q)⊓(Par P Q') needs a second mutual bisimulation, overlap-comm.

open import Level using (Level; Lift; lift)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt1)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ParallelComm {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open EventSet
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Bisim               {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync; par-pVis-sync-eq;
         fPar-nn; fPar-er; fPar-re)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (ParτR; τL; τR; Par-τ-elim; par-pVis-elim; par-hVisL-elim; par-hVisR-elim;
         Par-force-ret-inv; fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (brBoth-τ-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟
  using (par-pVis-soloL-eq; par-pVis-soloR-eq; par-pVis-both-eq;
         par-hVisL-eq; par-hVisR-eq; brBoth-commitL; brBoth-commitR)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr : Level

  -- the symmetric ⊤-merge
  tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
  tm _ _ = tt

-------------------------------------------------------------------------------------
-- the strong bisimulation (mutual with the overlap-node bisimulation)
-------------------------------------------------------------------------------------

-- both operands silent ⇒ no visible offer (par-pVis is ∅ there): used to discharge
-- the sil|sil case of the event transfer.
sil-sil-no-vis : (A : EventSet) (P Q P' Q' : PTree E (ExtI E) (⊤ {ℓr}))
                 {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) (⊤ {ℓr})}
               → par-pVis A tm (sil P') (sil Q') P Q at a ≡ just M → ⊥
sil-sil-no-vis A P Q P' Q' {at = at} {a = a} {M = M} eq
  with par-pVis-elim A tm (sil P') (sil Q') P Q {at = at} {a = a} {M = M} eq
... | inj₁ (_ , _ , _ , () , _ , _)
... | inj₂ (inj₁ (_ , _ , _ , () , _ , _))
... | inj₂ (inj₂ (inj₁ (_ , _ , () , _ , _)))
... | inj₂ (inj₂ (inj₂ (_ , _ , _ , () , _)))

Par-comm : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
         → (Par A tm P Q) ∼ (Par A tm Q P)

-- the both-offer overlap node (Par P' Q) ⊓ (Par P Q') is bisimilar to its mirror
overlap-comm : (A : EventSet) (P Q P' Q' : PTree E (ExtI E) (⊤ {ℓr}))
             → (ptree (react (λ _ _ → nothing) (par-brBoth A tm P Q P' Q')))
             ∼ (ptree (react (λ _ _ → nothing) (par-brBoth A tm Q P Q' P')))

Par-comm-tau : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
               {M : PTree E (ExtI E) (⊤ {ℓr})}
             → (Par A tm P Q) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] (((Par A tm Q P) ─[ τ ]─► M′) × (M ∼ M′))
Par-comm-tau A P Q step with Par-τ-elim A tm P Q step
... | τL P' Pτ refl = Par A tm Q P' , Par-τ-R A tm Q P Pτ , Par-comm A P' Q
... | τR Q' Qτ refl = Par A tm Q' P , Par-τ-L A tm Q P Qτ , Par-comm A P Q'

Par-comm-ev : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
              {M : PTree E (ExtI E) (⊤ {ℓr})} {e : Event√ (⊤ {ℓr})}
            → (Par A tm P Q) ─[ ev e ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] (((Par A tm Q P) ─[ ev e ]─► M′) × (M ∼ M′))
Par-comm-ev A P Q (sRet eqf) with Par-force-ret-inv A tm eqf
... | r₁ , r₂ , fpP , fpQ , refl = deadlock , sRet (fPar-rr A tm fpQ fpP) , sbisim-refl deadlock
Par-comm-ev A P Q (sVis {at = at} {a = a} {t′ = M} eqf br) with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r₁ | ret r₂ = case eqf of λ ()
... | ret r₁ | sil Q' = case eqf of λ ()
... | sil P' | ret r₂ = case eqf of λ ()
... | ret r₁ | react vQ τcQ =
      case par-hVisR-elim A tm P (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (Q' , ¬p , vQeq , refl) →
          Par A tm Q' P
          , sVis (fPar-er A tm eqQ eqP) (par-hVisL-eq A tm P ¬p vQeq)
          , Par-comm A P Q'
... | react vP τcP | ret r₂ =
      case par-hVisL-elim A tm Q (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (P' , ¬p , vPeq , refl) →
          Par A tm Q P'
          , sVis (fPar-re A tm eqQ eqP) (par-hVisR-eq A tm Q ¬p vPeq)
          , Par-comm A P' Q
... | sil P' | sil Q' =
      ⊥-elim (sil-sil-no-vis A P Q P' Q' {at = at} {a = a} {M = M}
                (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br))
... | sil P' | react vQ τcQ =
      case par-pVis-elim A tm (sil P') (react vQ τcQ) P Q
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (_ , _ , _ , () , _ , _))
        (inj₂ (inj₁ (_ , _ , _ , () , _ , _)))
        (inj₂ (inj₂ (inj₁ (_ , _ , () , _ , _))))
        (inj₂ (inj₂ (inj₂ (Q'' , ¬p , vPeq , vQeq , refl)))) →
          Par A tm Q'' P , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
            (par-pVis-soloL-eq A tm (react vQ τcQ) (sil P') Q P ¬p vQeq vPeq) , Par-comm A P Q''
... | react vP τcP | sil Q' =
      case par-pVis-elim A tm (react vP τcP) (sil Q') P Q
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (_ , _ , _ , _ , () , _))
        (inj₂ (inj₁ (_ , _ , _ , _ , () , _)))
        (inj₂ (inj₂ (inj₁ (P'' , ¬p , vPeq , vQeq , refl)))) →
          Par A tm Q P'' , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
            (par-pVis-soloR-eq A tm (sil Q') (react vP τcP) Q P ¬p vQeq vPeq) , Par-comm A P'' Q
        (inj₂ (inj₂ (inj₂ (_ , _ , _ , () , _))))
... | react vP τcP | react vQ τcQ =
      case par-pVis-elim A tm (react vP τcP) (react vQ τcQ) P Q
             (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (P'' , Q'' , p , vPeq , vQeq , refl)) →
          Par A tm Q'' P'' , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
            (par-pVis-sync-eq A tm (react vQ τcQ) (react vP τcP) Q P p vQeq vPeq) , Par-comm A P'' Q''
        (inj₂ (inj₁ (P'' , Q'' , ¬p , vPeq , vQeq , refl))) →
          ptree (react (λ _ _ → nothing) (par-brBoth A tm Q P Q'' P''))
          , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
              (par-pVis-both-eq A tm (react vQ τcQ) (react vP τcP) Q P ¬p vQeq vPeq)
          , overlap-comm A P Q P'' Q''
        (inj₂ (inj₂ (inj₁ (P'' , ¬p , vPeq , vQeq , refl)))) →
          Par A tm Q P'' , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
            (par-pVis-soloR-eq A tm (react vQ τcQ) (react vP τcP) Q P ¬p vQeq vPeq) , Par-comm A P'' Q
        (inj₂ (inj₂ (inj₂ (Q'' , ¬p , vPeq , vQeq , refl)))) →
          Par A tm Q'' P , sVis (fPar-nn A tm eqQ eqP tt1 tt1)
            (par-pVis-soloL-eq A tm (react vQ τcQ) (react vP τcP) Q P ¬p vQeq vPeq) , Par-comm A P Q''

Par-comm A P Q .Sbisim.fwd .SSimF.on-ev  = Par-comm-ev  A P Q
Par-comm A P Q .Sbisim.fwd .SSimF.on-tau = Par-comm-tau A P Q
Par-comm A P Q .Sbisim.bwd .SSimF.on-ev  = Par-comm-ev  A Q P
Par-comm A P Q .Sbisim.bwd .SSimF.on-tau = Par-comm-tau A Q P

-- overlap-comm: on-tau crosses the two τ tags; on-ev is vacuous (vis ≡ ∅).
overlap-comm A P Q P' Q' .Sbisim.fwd .SSimF.on-ev (sRet ())
overlap-comm A P Q P' Q' .Sbisim.fwd .SSimF.on-ev (sVis refl ())
overlap-comm A P Q P' Q' .Sbisim.fwd .SSimF.on-tau step with brBoth-τ-elim A tm P Q P' Q' step
... | inj₁ refl = Par A tm Q P' , brBoth-commitR A tm Q P Q' P' , Par-comm A P' Q
... | inj₂ refl = Par A tm Q' P , brBoth-commitL A tm Q P Q' P' , Par-comm A P Q'
overlap-comm A P Q P' Q' .Sbisim.bwd = overlap-comm A Q P Q' P' .Sbisim.fwd

-------------------------------------------------------------------------------------
-- the FD laws (lifted)
-------------------------------------------------------------------------------------

Par⊤-comm-FD : (A : EventSet) (P Q : PTree E (ExtI E) (⊤ {ℓr}))
             → (P ∥⇘ A ⇙ Q) ≈FD (Q ∥⇘ A ⇙ P)
Par⊤-comm-FD A P Q = drbisim→≈FD (sbisim→drbisim (Par-comm A P Q))

⦀-comm-FD : (P Q : PTree E (ExtI E) (⊤ {ℓr})) → (P ⦀ Q) ≈FD (Q ⦀ P)
⦀-comm-FD P Q = Par⊤-comm-FD ∅ES P Q
