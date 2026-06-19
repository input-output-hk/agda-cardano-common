{-# OPTIONS --guardedness #-}

-- SPIKE: the GENERAL sequential-composition ≈-congruence (arbitrary continuation).
--   >>=-cong : P ≈ P′ → (∀ r → k r ≈ k′ r) → (P >>= k) ≈ (P′ >>= k′)
-- The hard part is the ret-boundary: when P rets r, P >>= k IS k r (force-equal), and
-- the matching weak step of P′ >>= k′ must (i) τ*-reach the ret state and (ii) replay
-- k′ r's weak step from a tree only FORCE-equal to k′ r.  Handled by transport helpers
-- (retarget / force-≡→≈ / weak-transport-τ,-ev / ═-prepend-τ*) + wbisim-trans.
-- No postulates, no NON_TERMINATING.

open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.Bisim.BindCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators   E-≟
open import Semantics.LTS        {E = E} {I = ExtI E}
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.IterCong   E-≟ using (ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv)
open import CSP.Laws.Bisim.LoopCong   E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindT-eq; bindV-eq; bindT-elim; bindV-elim;
         bind-τ; bind-ev; bind-τ*; ≈-reaches-ret)

private
  variable
    ℓr ℓs ℓx : Level
    R : Set ℓr
    S : Set ℓs
    X : Set ℓx

-------------------------------------------------------------------------------------
-- transport helpers across force-equal trees
-------------------------------------------------------------------------------------

-- retarget a single step along a force-equation
retarget : {a b u : PTree E (ExtI E) X} {l : Label X}
         → PTree.force a ≡ PTree.force b → b ─[ l ]─► u → a ─[ l ]─► u
retarget eq (sRet eqf)    = sRet (trans eq eqf)
retarget eq (sSil eqf)    = sSil (trans eq eqf)
retarget eq (sVis eqf br) = sVis (trans eq eqf) br
retarget eq (sTau eqf br) = sTau (trans eq eqf) br

-- force-equal trees are weakly bisimilar
force-≡→≈ : {p q : PTree E (ExtI E) X} → PTree.force p ≡ PTree.force q → p ≈ q
force-≡→≈ eq .Wbisim.fwd .WSimF.on-ev  step = _ , wev τ*-refl (retarget (sym eq) step) τ*-refl , wbisim-refl _
force-≡→≈ eq .Wbisim.fwd .WSimF.on-tau step = _ , wτ (τ*-step (retarget (sym eq) step) τ*-refl) , wbisim-refl _
force-≡→≈ eq .Wbisim.bwd .WSimF.on-ev  step = _ , wev τ*-refl (retarget eq step) τ*-refl , wbisim-refl _
force-≡→≈ eq .Wbisim.bwd .WSimF.on-tau step = _ , wτ (τ*-step (retarget eq step) τ*-refl) , wbisim-refl _

-- prepend a τ* to a weak step
═-prepend-τ* : {p q u : PTree E (ExtI E) X} {l : Label X}
             → p ─[τ*]─► q → q ═[ l ]═► u → p ═[ l ]═► u
═-prepend-τ* pre (wτ  q→u)              = wτ  (τ*-trans pre q→u)
═-prepend-τ* pre (wev q→q′ evstep q″→u) = wev (τ*-trans pre q→q′) evstep q″→u

-- replay a weak step across a force-equation (endpoint may shift to a ≈-related state)
weak-transport-τ : {p q u : PTree E (ExtI E) X} → PTree.force p ≡ PTree.force q
                 → q ─[τ*]─► u → Σ[ u′ ∈ PTree E (ExtI E) X ] (p ─[τ*]─► u′) × (u′ ≈ u)
weak-transport-τ eq τ*-refl          = _ , τ*-refl , force-≡→≈ eq
weak-transport-τ eq (τ*-step st rest) = _ , τ*-step (retarget eq st) rest , wbisim-refl _

weak-transport-ev : {p q u : PTree E (ExtI E) X} {l : Event√ X} → PTree.force p ≡ PTree.force q
                  → q ═[ ev l ]═► u → Σ[ u′ ∈ PTree E (ExtI E) X ] (p ═[ ev l ]═► u′) × (u′ ≈ u)
weak-transport-ev eq (wev τ*-refl         evstep q″→u) = _ , wev τ*-refl (retarget eq evstep) q″→u , wbisim-refl _
weak-transport-ev eq (wev (τ*-step st rs) evstep q″→u) = _ , wev (τ*-step (retarget eq st) rs) evstep q″→u , wbisim-refl _

-------------------------------------------------------------------------------------
-- the general congruence (mutual coinduction)
-------------------------------------------------------------------------------------

>>=-cong : (k k′ : R → PTree E (ExtI E) S) → (∀ r → (k r) ≈ (k′ r))
         → {P P′ : PTree E (ExtI E) R} → P ≈ P′ → (P >>= k) ≈ (P′ >>= k′)
>>=-sim : (k k′ : R → PTree E (ExtI E) S) → (∀ r → (k r) ≈ (k′ r))
        → {P P′ : PTree E (ExtI E) R} → P ≈ P′ → WSimF (Wbisim S) (P >>= k) (P′ >>= k′)

>>=-cong k k′ kk′ PP′ .Wbisim.fwd = >>=-sim k k′ kk′ PP′
>>=-cong k k′ kk′ PP′ .Wbisim.bwd = >>=-sim k′ k (λ r → wbisim-sym (kk′ r)) (wbisim-sym PP′)

>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-tau step with PTree.force P in eqP
... | ret r with kk′ r .Wbisim.fwd .WSimF.on-tau (retarget (sym (fBind-ret k P eqP)) step)
               | ≈-reaches-ret PP′ eqP
...   | u′ , wτ kr′→u′ , uu′ | p′ , P′→p′ , fp′ with weak-transport-τ (fBind-ret k′ p′ fp′) kr′→u′
...     | u″ , p′k′→u″ , u″≈u′ =
          u″ , ═-prepend-τ* (bind-τ* k′ P′→p′) (wτ p′k′→u″) , wbisim-trans uu′ (wbisim-sym u″≈u′)
>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-tau step | sil c
  with sil-τ-inv (fBind-sil k P eqP) step | PP′ .Wbisim.fwd .WSimF.on-tau (sSil eqP)
...   | refl | c′ , wτ P′→c′ , cc′ = c′ >>= k′ , wτ (bind-τ* k′ P′→c′) , >>=-cong k k′ kk′ cc′
>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-tau step | react v τc
  with react-τ-inv (fBind-react k P eqP) step
...   | i , a , br with bindT-elim k (react v τc) br
...     | t″ , vτ , refl with PP′ .Wbisim.fwd .WSimF.on-tau (sTau eqP vτ)
...       | t‴ , wτ P′→t‴ , rel = t‴ >>= k′ , wτ (bind-τ* k′ P′→t‴) , >>=-cong k k′ kk′ rel

>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-ev step with PTree.force P in eqP
... | sil c = ⊥-elim (sil-no-ev (fBind-sil k P eqP) step)
>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-ev step | ret r
  with kk′ r .Wbisim.fwd .WSimF.on-ev (retarget (sym (fBind-ret k P eqP)) step)
     | ≈-reaches-ret PP′ eqP
...   | u′ , kr′═u′ , uu′ | p′ , P′→p′ , fp′ with weak-transport-ev (fBind-ret k′ p′ fp′) kr′═u′
...     | u″ , p′k′═u″ , u″≈u′ =
          u″ , ═-prepend-τ* (bind-τ* k′ P′→p′) p′k′═u″ , wbisim-trans uu′ (wbisim-sym u″≈u′)
>>=-sim k k′ kk′ {P = P} {P′ = P′} PP′ .WSimF.on-ev step | react v τc with step
... | sRet eqf = ⊥-elim (case trans (sym (fBind-react k P eqP)) eqf of λ ())
... | sVis {at = at} {a = a} eqf br with bindV-elim k (react v τc)
        (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective (trans (sym (fBind-react k P eqP)) eqf)))) br)
...   | t″ , vv , refl with PP′ .Wbisim.fwd .WSimF.on-ev (sVis eqP vv)
...     | t‴ , wev P′→p′ p′ev q′→t‴ , rel =
          t‴ >>= k′
        , wev (bind-τ* k′ P′→p′) (bind-ev k′ _ p′ev) (bind-τ* k′ q′→t‴)
        , >>=-cong k k′ kk′ rel
