{-# OPTIONS --guardedness #-}

-- Strong bisimulation is an UNCONDITIONAL congruence for the generalised CSP
-- parallel `Par` (and hence for `_∥⇘_⇙_` and `_⦀_`).
--
--   cong-Par-∼  : P ∼ P′ → Q ∼ Q′ → (Par A merge P Q) ∼ (Par A merge P′ Q′)
--   cong-Par⊤-∼ : the ⊤-merge instance (CSP alphabetised parallel)
--   cong-⦀-∼    : the interleaving instance (`Par ∅ES`)
--
-- Unlike the ≈DR congruence `cong-⦀` (Bisim/DRCongruence), there is NO `Sep` side
-- condition: `∼` matches single steps and does not abstract τ, so a partner's silent
-- steps can never be interleaved into a mismatch.  The proof is the `Par-comm`
-- (Laws/FD/ParallelComm) shape with the two sides related by hypotheses instead of
-- swapped:
--   • on-tau : Par-τ-elim → Par-τ-L / Par-τ-R on the primed side;
--   • on-ev  : force-case + par-pVis-elim (which records the idle operand's NON-offer)
--     → Par-sync / Par-soloL / Par-soloR / Par-both / the joint √.
-- Two facts carry the case distinction across the hypotheses: `ret-∼` (termination is
-- preserved) and `noOffer-∼` (a non-offer at an event is preserved — an offer of P′
-- would transfer BACK to P by the bwd half).  The both-offer collision node needs a
-- second mutual bisimulation, `cong-overlap-∼`, exactly as `overlap-comm` did.

open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt1)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.Bisim.ParallelCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync; Par-soloL; Par-soloR; fPar-nn)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (ParτR; τL; τR; Par-τ-elim; par-pVis-elim; par-hVisL-elim; par-hVisR-elim;
         Par-force-ret-inv; fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟
  using (par-pVis-both-eq; brBoth-commitL; brBoth-commitR)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (brBoth-τ-elim; brBoth-no-ev)

private
  variable
    ℓ₁ ℓ₂ ℓs ℓr : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs
    Rg : Set ℓr

-------------------------------------------------------------------------------------
-- transfer facts: what a strong bisimulation preserves besides steps
-------------------------------------------------------------------------------------

-- a `√ r` step can only be issued by a node forced to `ret r`
√-force : {t M : PTree E (ExtI E) Rg} {r : Rg}
        → t ─[ ev (√ r) ]─► M → PTree.force t ≡ ret r
√-force (sRet eqf) = eqf

-- termination (and its VALUE) transfers along `∼`: the √-label pins `r` down
ret-∼ : {P P′ : PTree E (ExtI E) Rg} {r : Rg}
      → P ∼ P′ → PTree.force P ≡ ret r → PTree.force P′ ≡ ret r
ret-∼ p∼ eqP = √-force (proj₁ (proj₂ (p∼ .Sbisim.fwd .SSimF.on-ev (sRet eqP))))

-- a visible step contradicts a non-offer of the very same event
ev-noOffer-⊥ : {P M : PTree E (ExtI E) Rg} {X : Set ℓ} {e : E X} {a : X}
             → P ─[ ev (evl (evLabel X e a)) ]─► M
             → viewV (PTree.force P) (X , e) a ≡ nothing → ⊥
ev-noOffer-⊥ {X = X} {e = e} {a = a} st nq with ev-inv st
... | v , τc , eqf , br =
      case trans (sym br) (subst (λ n → viewV n (X , e) a ≡ nothing) eqf nq) of λ ()

-- transport a non-offer stated on a KNOWN node shape into the un-forced form that
-- `Par-soloL` / `Par-soloR` consume
noOffer-force : (P : PTree E (ExtI E) Rg) {n : NodeKind E (ExtI E) Rg}
                {at : AnyTypes E} {a : proj₁ at}
              → PTree.force P ≡ n → viewV n at a ≡ nothing
              → viewV (PTree.force P) at a ≡ nothing
noOffer-force P refl nq = nq

-- `∼` preserves "offers nothing at this event": an offer of P′ would transfer BACK to
-- P through the backward half, contradicting P's non-offer
noOffer-∼ : (P P′ : PTree E (ExtI E) Rg) {at : AnyTypes E} {a : proj₁ at}
          → P ∼ P′ → viewV (PTree.force P) at a ≡ nothing
          → viewV (PTree.force P′) at a ≡ nothing
noOffer-∼ P P′ {at = at} {a = a} p∼ nq with PTree.force P′ in eqP′
... | ret _  = refl
... | sil _  = refl
... | react v τc with v at a in veq
...   | nothing = refl
...   | just X  =
        ⊥-elim (ev-noOffer-⊥
                  (proj₁ (proj₂ (p∼ .Sbisim.bwd .SSimF.on-ev
                                   (sVis {at = at} {a = a} eqP′ veq))))
                  nq)

-------------------------------------------------------------------------------------
-- two structural facts about `Par`'s own node
-------------------------------------------------------------------------------------

-- both operands silent ⇒ no visible offer (par-pVis is ∅ there)
sil-sil-no-vis : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P P₀ : PTree E (ExtI E) R₁) (Q Q₀ : PTree E (ExtI E) R₂)
                 {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
               → par-pVis A merge (sil P₀) (sil Q₀) P Q at a ≡ just M → ⊥
sil-sil-no-vis A merge P P₀ Q Q₀ {at = at} {a = a} {M = M} eq
  with par-pVis-elim A merge (sil P₀) (sil Q₀) P Q {at = at} {a = a} {M = M} eq
... | inj₁ (_ , _ , _ , () , _ , _)
... | inj₂ (inj₁ (_ , _ , _ , () , _ , _))
... | inj₂ (inj₂ (inj₁ (_ , _ , () , _ , _)))
... | inj₂ (inj₂ (inj₂ (_ , _ , _ , () , _)))

-- both operands offer the same event OUTSIDE `A` ⇒ the composite steps into the inline
-- both-offer collision node (the ⊓-shaped `par-brBoth`); mirrors `Par-sync`
Par-both : (A : EventSet) (merge : Mg R₁ R₂ R)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           {X : Set ℓ} {e : E X} {a : X}
           {P₁ : PTree E (ExtI E) R₁} {Q₁ : PTree E (ExtI E) R₂}
         → ¬ A .mem (X , e) a
         → P ─[ ev (evl (evLabel X e a)) ]─► P₁
         → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
         → (Par A merge P Q) ─[ ev (evl (evLabel X e a)) ]─►
             (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
Par-both A merge P Q ¬cs (sVis {v = vP} {τc = τcP} eqP brP)
                         (sVis {v = vQ} {τc = τcQ} eqQ brQ) =
  sVis (fPar-nn A merge eqP eqQ tt1 tt1)
       (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q ¬cs brP brQ)

-------------------------------------------------------------------------------------
-- the congruence (mutual with the collision-node bisimulation)
-------------------------------------------------------------------------------------

-- strong bisimulation is an UNCONDITIONAL congruence for CSP parallel: unlike the ≈DR
-- congruence `cong-Par⊤` there is no `Sep` side condition, because `∼` does not abstract
-- τ and so cannot be broken by the interleaving of a partner's silent steps
cong-Par-∼ : (A : EventSet) (merge : Mg R₁ R₂ R)
             {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
           → P ∼ P′ → Q ∼ Q′ → (Par A merge P Q) ∼ (Par A merge P′ Q′)

-- the both-offer collision node is congruent in all four operands
cong-overlap-∼ : (A : EventSet) (merge : Mg R₁ R₂ R)
                 {P P′ P₁ P₁′ : PTree E (ExtI E) R₁}
                 {Q Q′ Q₁ Q₁′ : PTree E (ExtI E) R₂}
               → P ∼ P′ → Q ∼ Q′ → P₁ ∼ P₁′ → Q₁ ∼ Q₁′
               → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P  Q  P₁  Q₁)))
                 ∼ (ptree (react (λ _ _ → nothing) (par-brBoth A merge P′ Q′ P₁′ Q₁′)))

-- a τ of the composite is one operand's τ; replay it on the matching operand
cong-Par-tau : (A : EventSet) (merge : Mg R₁ R₂ R)
               {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
             → P ∼ P′ → Q ∼ Q′ → {M : PTree E (ExtI E) R}
             → (Par A merge P Q) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ]
                 (((Par A merge P′ Q′) ─[ τ ]─► M′) × (M ∼ M′))

-- a visible/√ step of the composite, replayed on the primed pair
cong-Par-ev : (A : EventSet) (merge : Mg R₁ R₂ R)
              {P P′ : PTree E (ExtI E) R₁} {Q Q′ : PTree E (ExtI E) R₂}
            → P ∼ P′ → Q ∼ Q′ → {M : PTree E (ExtI E) R} {e : Event√ R}
            → (Par A merge P Q) ─[ ev e ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) R ]
                (((Par A merge P′ Q′) ─[ ev e ]─► M′) × (M ∼ M′))

-- the collision node's only steps are the two commit-τs
cong-overlap-tau : (A : EventSet) (merge : Mg R₁ R₂ R)
                   {P P′ P₁ P₁′ : PTree E (ExtI E) R₁}
                   {Q Q′ Q₁ Q₁′ : PTree E (ExtI E) R₂}
                 → P ∼ P′ → Q ∼ Q′ → P₁ ∼ P₁′ → Q₁ ∼ Q₁′ → {M : PTree E (ExtI E) R}
                 → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
                   ─[ τ ]─► M
                 → Σ[ M′ ∈ PTree E (ExtI E) R ]
                     (((ptree (react (λ _ _ → nothing) (par-brBoth A merge P′ Q′ P₁′ Q₁′)))
                        ─[ τ ]─► M′)
                      × (M ∼ M′))

-- the collision node's visible map is empty, so its `on-ev` obligation is vacuous
-- (the target `N` stays free, so this one clause serves both fwd and bwd)
cong-overlap-ev : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
                  {N M : PTree E (ExtI E) R} {e : Event√ R}
                → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
                  ─[ ev e ]─► M
                → Σ[ M′ ∈ PTree E (ExtI E) R ] ((N ─[ ev e ]─► M′) × (M ∼ M′))

cong-Par-tau A merge {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} p∼ q∼ step
  with Par-τ-elim A merge P Q step
... | τL P₁ Pτ refl =
      case p∼ .Sbisim.fwd .SSimF.on-tau Pτ of λ where
        (P₂ , Pτ′ , p₁∼) →
          Par A merge P₂ Q′ , Par-τ-L A merge P′ Q′ Pτ′ , cong-Par-∼ A merge p₁∼ q∼
... | τR Q₁ Qτ refl =
      case q∼ .Sbisim.fwd .SSimF.on-tau Qτ of λ where
        (Q₂ , Qτ′ , q₁∼) →
          Par A merge P′ Q₂ , Par-τ-R A merge P′ Q′ Qτ′ , cong-Par-∼ A merge p∼ q₁∼

cong-Par-ev A merge p∼ q∼ (sRet eqf) with Par-force-ret-inv A merge eqf
... | r₁ , r₂ , fpP , fpQ , refl =
      deadlock
      , sRet (fPar-rr A merge (ret-∼ p∼ fpP) (ret-∼ q∼ fpQ))
      , sbisim-refl deadlock
cong-Par-ev A merge {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} p∼ q∼
            (sVis {at = at} {a = a} {t′ = M} eqf br)
  with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r₁ | ret r₂ = case eqf of λ ()
... | ret r₁ | sil Q₀ = case eqf of λ ()
... | sil P₀ | ret r₂ = case eqf of λ ()
-- P terminated, Q offering: only Q can move, and P′ still offers nothing
... | ret r₁ | react vQ τcQ =
      case par-hVisR-elim A merge P
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br) of λ where
        (Q₁ , ¬p , vQeq , refl) →
          case q∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqQ vQeq) of λ where
            (Q₂ , Qev , q₁∼) →
              Par A merge P′ Q₂
              , Par-soloR A merge P′ Q′ ¬p Qev
                  (noOffer-∼ P P′ {at = at} {a = a} p∼
                     (noOffer-force P {at = at} {a = a} eqP refl))
              , cong-Par-∼ A merge p∼ q₁∼
-- Q terminated, P offering: the mirror
... | react vP τcP | ret r₂ =
      case par-hVisL-elim A merge Q
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br) of λ where
        (P₁ , ¬p , vPeq , refl) →
          case p∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqP vPeq) of λ where
            (P₂ , Pev , p₁∼) →
              Par A merge P₂ Q′
              , Par-soloL A merge P′ Q′ ¬p Pev
                  (noOffer-∼ Q Q′ {at = at} {a = a} q∼
                     (noOffer-force Q {at = at} {a = a} eqQ refl))
              , cong-Par-∼ A merge p₁∼ q∼
... | sil P₀ | sil Q₀ =
      ⊥-elim (sil-sil-no-vis A merge P P₀ Q Q₀ {at = at} {a = a} {M = M}
                (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br))
-- P silent, Q offering: only the solo-R branch of par-pVis can fire
... | sil P₀ | react vQ τcQ =
      case par-pVis-elim A merge (sil P₀) (react vQ τcQ) P Q
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (_ , _ , _ , () , _ , _))
        (inj₂ (inj₁ (_ , _ , _ , () , _ , _)))
        (inj₂ (inj₂ (inj₁ (_ , _ , () , _ , _))))
        (inj₂ (inj₂ (inj₂ (Q₁ , ¬p , _ , vQeq , refl)))) →
          case q∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqQ vQeq) of λ where
            (Q₂ , Qev , q₁∼) →
              Par A merge P′ Q₂
              , Par-soloR A merge P′ Q′ ¬p Qev
                  (noOffer-∼ P P′ {at = at} {a = a} p∼
                     (noOffer-force P {at = at} {a = a} eqP refl))
              , cong-Par-∼ A merge p∼ q₁∼
-- Q silent, P offering: the mirror
... | react vP τcP | sil Q₀ =
      case par-pVis-elim A merge (react vP τcP) (sil Q₀) P Q
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (_ , _ , _ , _ , () , _))
        (inj₂ (inj₁ (_ , _ , _ , _ , () , _)))
        (inj₂ (inj₂ (inj₁ (P₁ , ¬p , vPeq , _ , refl)))) →
          case p∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqP vPeq) of λ where
            (P₂ , Pev , p₁∼) →
              Par A merge P₂ Q′
              , Par-soloL A merge P′ Q′ ¬p Pev
                  (noOffer-∼ Q Q′ {at = at} {a = a} q∼
                     (noOffer-force Q {at = at} {a = a} eqQ refl))
              , cong-Par-∼ A merge p₁∼ q∼
        (inj₂ (inj₂ (inj₂ (_ , _ , _ , () , _))))
-- both live: sync / both-offer collision / solo-L / solo-R
... | react vP τcP | react vQ τcQ =
      case par-pVis-elim A merge (react vP τcP) (react vQ τcQ) P Q
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br) of λ where
        (inj₁ (P₁ , Q₁ , p , vPeq , vQeq , refl)) →
          case p∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqP vPeq) of λ where
            (P₂ , Pev , p₁∼) →
              case q∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqQ vQeq) of λ where
                (Q₂ , Qev , q₁∼) →
                  Par A merge P₂ Q₂
                  , Par-sync A merge P′ Q′ p Pev Qev
                  , cong-Par-∼ A merge p₁∼ q₁∼
        (inj₂ (inj₁ (P₁ , Q₁ , ¬p , vPeq , vQeq , refl))) →
          case p∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqP vPeq) of λ where
            (P₂ , Pev , p₁∼) →
              case q∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqQ vQeq) of λ where
                (Q₂ , Qev , q₁∼) →
                  ptree (react (λ _ _ → nothing) (par-brBoth A merge P′ Q′ P₂ Q₂))
                  , Par-both A merge P′ Q′ ¬p Pev Qev
                  , cong-overlap-∼ A merge p∼ q∼ p₁∼ q₁∼
        (inj₂ (inj₂ (inj₁ (P₁ , ¬p , vPeq , vQeq , refl)))) →
          case p∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqP vPeq) of λ where
            (P₂ , Pev , p₁∼) →
              Par A merge P₂ Q′
              , Par-soloL A merge P′ Q′ ¬p Pev
                  (noOffer-∼ Q Q′ {at = at} {a = a} q∼
                     (noOffer-force Q {at = at} {a = a} eqQ vQeq))
              , cong-Par-∼ A merge p₁∼ q∼
        (inj₂ (inj₂ (inj₂ (Q₁ , ¬p , vPeq , vQeq , refl)))) →
          case q∼ .Sbisim.fwd .SSimF.on-ev (sVis {at = at} {a = a} eqQ vQeq) of λ where
            (Q₂ , Qev , q₁∼) →
              Par A merge P′ Q₂
              , Par-soloR A merge P′ Q′ ¬p Qev
                  (noOffer-∼ P P′ {at = at} {a = a} p∼
                     (noOffer-force P {at = at} {a = a} eqP vPeq))
              , cong-Par-∼ A merge p∼ q₁∼

cong-overlap-tau A merge {P = P} {P′ = P′} {P₁ = P₁} {P₁′ = P₁′}
                         {Q = Q} {Q′ = Q′} {Q₁ = Q₁} {Q₁′ = Q₁′} p∼ q∼ p₁∼ q₁∼ step
  with brBoth-τ-elim A merge P Q P₁ Q₁ step
... | inj₁ refl =
      Par A merge P₁′ Q′ , brBoth-commitL A merge P′ Q′ P₁′ Q₁′ , cong-Par-∼ A merge p₁∼ q∼
... | inj₂ refl =
      Par A merge P′ Q₁′ , brBoth-commitR A merge P′ Q′ P₁′ Q₁′ , cong-Par-∼ A merge p∼ q₁∼

cong-overlap-ev A merge P Q P₁ Q₁ step = ⊥-elim (brBoth-no-ev A merge P Q P₁ Q₁ step)

cong-Par-∼ A merge p∼ q∼ .Sbisim.fwd .SSimF.on-ev  = cong-Par-ev  A merge p∼ q∼
cong-Par-∼ A merge p∼ q∼ .Sbisim.fwd .SSimF.on-tau = cong-Par-tau A merge p∼ q∼
cong-Par-∼ A merge p∼ q∼ .Sbisim.bwd .SSimF.on-ev  =
  cong-Par-ev  A merge (sbisim-sym p∼) (sbisim-sym q∼)
cong-Par-∼ A merge p∼ q∼ .Sbisim.bwd .SSimF.on-tau =
  cong-Par-tau A merge (sbisim-sym p∼) (sbisim-sym q∼)

cong-overlap-∼ A merge {P = P} {P₁ = P₁} {Q = Q} {Q₁ = Q₁}
               p∼ q∼ p₁∼ q₁∼ .Sbisim.fwd .SSimF.on-ev = cong-overlap-ev A merge P Q P₁ Q₁
cong-overlap-∼ A merge p∼ q∼ p₁∼ q₁∼ .Sbisim.fwd .SSimF.on-tau =
  cong-overlap-tau A merge p∼ q∼ p₁∼ q₁∼
cong-overlap-∼ A merge {P′ = P′} {P₁′ = P₁′} {Q′ = Q′} {Q₁′ = Q₁′}
               p∼ q∼ p₁∼ q₁∼ .Sbisim.bwd .SSimF.on-ev = cong-overlap-ev A merge P′ Q′ P₁′ Q₁′
cong-overlap-∼ A merge p∼ q∼ p₁∼ q₁∼ .Sbisim.bwd .SSimF.on-tau =
  cong-overlap-tau A merge (sbisim-sym p∼) (sbisim-sym q∼) (sbisim-sym p₁∼) (sbisim-sym q₁∼)

-------------------------------------------------------------------------------------
-- the two CSP instances
-------------------------------------------------------------------------------------

-- the ⊤-merge instance, matching `Par⊤` / the CSP alphabetised-parallel sugar
cong-Par⊤-∼ : (A : EventSet) {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
            → P ∼ P′ → Q ∼ Q′ → (P ∥⇘ A ⇙ Q) ∼ (P′ ∥⇘ A ⇙ Q′)
cong-Par⊤-∼ A = cong-Par-∼ A (λ _ _ → tt)

-- interleaving is `Par ∅ES` at the ⊤-merge
cong-⦀-∼ : {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
         → P ∼ P′ → Q ∼ Q′ → (P ⦀ Q) ∼ (P′ ⦀ Q′)
cong-⦀-∼ = cong-Par-∼ ∅ES (λ _ _ → tt)
