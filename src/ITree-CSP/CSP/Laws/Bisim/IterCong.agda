{-# OPTIONS --guardedness #-}

-- SPIKE: iteration is a CONGRUENCE for weak bisimulation (the coinductive route).
--   iter-bind-cong : (∀ a → k a ≈ k′ a) → t ≈ t′ → iter-bind t k ≈ iter-bind t′ k′
--   iter-cong      : (∀ a → k a ≈ k′ a) → (∀ a → iter k a ≈ iter k′ a)
-- The body hypothesis is the STEP-WISE relation ≈ (not the global ⊑T), so no
-- step-closure postulate is needed; ≈ ⟹ trace-equivalence via traces-respects-≈.
-- Mutual coinduction (iter-bind-cong / iter-bind-sim) guarded by the loop-τ.
-- No postulates, no NON_TERMINATING.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.Bisim.IterCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators   E-≟
open import Semantics.LTS        {E = E} {I = ExtI E}
open import Semantics.WeakBisim  {E = E} {I = ExtI E}

private
  variable
    ℓr ℓx : Level
    A : Set ℓ
    R : Set ℓr
    X : Set ℓx

-------------------------------------------------------------------------------------
-- generic single-step inversions (LTS level)
-------------------------------------------------------------------------------------

ret-no-τ : {t u : PTree E (ExtI E) X} {r : X} → PTree.force t ≡ ret r → t ─[ τ ]─► u → ⊥
ret-no-τ eqf (sSil sileq)    = case trans (sym sileq) eqf of λ ()
ret-no-τ eqf (sTau extceq _) = case trans (sym extceq) eqf of λ ()

sil-τ-inv : {t c u : PTree E (ExtI E) X} → PTree.force t ≡ sil c → t ─[ τ ]─► u → u ≡ c
sil-τ-inv eqf (sSil sileq)    = sil-injective (trans (sym sileq) eqf)
sil-τ-inv eqf (sTau extceq _) = ⊥-elim (sil≢react (trans (sym eqf) extceq))

sil-no-ev : {t c u : PTree E (ExtI E) X} {l : Event√ X} → PTree.force t ≡ sil c → t ─[ ev l ]─► u → ⊥
sil-no-ev sile (sRet eqf)   = case trans (sym sile) eqf of λ ()
sil-no-ev sile (sVis eqf _) = case trans (sym sile) eqf of λ ()

react-τ-inv : {t u : PTree E (ExtI E) X}
               {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) X))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) X))}
           → PTree.force t ≡ react v τc → t ─[ τ ]─► u
           → Σ[ i ∈ AnyTypes (ExtI E) ] Σ[ a ∈ proj₁ i ] (τc i a ≡ just u)
react-τ-inv eqf (sSil sileq) = ⊥-elim (sil≢react (trans (sym sileq) eqf))
react-τ-inv {u = u} eqf (sTau {i = i} {a = a} extceq breq) =
  i , a , subst (λ g → g i a ≡ just u) (sym (proj₂ (react-injective (trans (sym eqf) extceq)))) breq

-------------------------------------------------------------------------------------
-- force-equation lemmas for iter-bind
-------------------------------------------------------------------------------------

fIter-r1 : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {a′ : A}
         → PTree.force t ≡ ret (inj₁ a′) → PTree.force (iter-bind t k) ≡ sil (iter k a′)
fIter-r1 k t eqt with PTree.force t
... | ret (inj₁ _) = case eqt of λ { refl → refl }
... | ret (inj₂ _) = case eqt of λ ()
... | sil _        = case eqt of λ ()
... | react _ _     = case eqt of λ ()

fIter-r2 : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {r : R}
         → PTree.force t ≡ ret (inj₂ r) → PTree.force (iter-bind t k) ≡ ret r
fIter-r2 k t eqt with PTree.force t
... | ret (inj₂ _) = case eqt of λ { refl → refl }
... | ret (inj₁ _) = case eqt of λ ()
... | sil _        = case eqt of λ ()
... | react _ _     = case eqt of λ ()

fIter-sil : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {c : PTree E (ExtI E) (A ⊎ R)}
          → PTree.force t ≡ sil c → PTree.force (iter-bind t k) ≡ sil (iter-bind c k)
fIter-sil k t eqt with PTree.force t
... | sil _        = case eqt of λ { refl → refl }
... | ret _        = case eqt of λ ()
... | react _ _     = case eqt of λ ()

fIter-react : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R))
               {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (A ⊎ R)))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) (A ⊎ R)))}
           → PTree.force t ≡ react v τc
           → PTree.force (iter-bind t k) ≡ react (iterV k (react v τc)) (iterT k (react v τc))
fIter-react k t eqt with PTree.force t
... | react _ _     = case eqt of λ { refl → refl }
... | ret _        = case eqt of λ ()
... | sil _        = case eqt of λ ()

-------------------------------------------------------------------------------------
-- branch-equation lemmas for iterV / iterT
-------------------------------------------------------------------------------------

iterT-eq : (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
             {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) (A ⊎ R)}
         → viewT nP i a ≡ just t′ → iterT k nP i a ≡ just (iter-bind t′ k)
iterT-eq k nP {i = i} {a = a} ve with viewT nP i a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

iterT-elim : (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {u : PTree E (ExtI E) R}
           → iterT k nP i a ≡ just u
           → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] (viewT nP i a ≡ just t′) × (u ≡ iter-bind t′ k)
iterT-elim k nP {i = i} {a = a} eq with viewT nP i a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

iterV-eq : (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
             {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) (A ⊎ R)}
         → viewV nP at a ≡ just t′ → iterV k nP at a ≡ just (iter-bind t′ k)
iterV-eq k nP {at = at} {a = a} ve with viewV nP at a
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

iterV-elim : (k : A → PTree E (ExtI E) (A ⊎ R)) (nP : NodeKind E (ExtI E) (A ⊎ R))
               {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
           → iterV k nP at a ≡ just u
           → Σ[ t′ ∈ PTree E (ExtI E) (A ⊎ R) ] (viewV nP at a ≡ just t′) × (u ≡ iter-bind t′ k)
iterV-elim k nP {at = at} {a = a} eq with viewV nP at a
... | just t′ = t′ , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-------------------------------------------------------------------------------------
-- threading lemmas: iter-bind propagates t's own τ / visible steps
-------------------------------------------------------------------------------------

iter-bind-τ : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {c : PTree E (ExtI E) (A ⊎ R)}
            → t ─[ τ ]─► c → iter-bind t k ─[ τ ]─► iter-bind c k
iter-bind-τ k t (sSil eqf)                      = sSil (fIter-sil k t eqf)
iter-bind-τ k t (sTau {v = v} {τc = τc} eqf br) = sTau (fIter-react k t eqf) (iterT-eq k (react v τc) br)

iter-bind-ev : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R))
                 {B : Set ℓ} {e : E B} {a : B} {c : PTree E (ExtI E) (A ⊎ R)}
             → t ─[ ev (evl (evLabel B e a)) ]─► c → iter-bind t k ─[ ev (evl (evLabel B e a)) ]─► iter-bind c k
iter-bind-ev k t (sVis {v = v} {τc = τc} eqf br) = sVis (fIter-react k t eqf) (iterV-eq k (react v τc) br)

iter-bind-τ* : (k : A → PTree E (ExtI E) (A ⊎ R)) {t c : PTree E (ExtI E) (A ⊎ R)}
             → t ─[τ*]─► c → iter-bind t k ─[τ*]─► iter-bind c k
iter-bind-τ* k τ*-refl          = τ*-refl
iter-bind-τ* k (τ*-step st rest) = τ*-step (iter-bind-τ k _ st) (iter-bind-τ* k rest)

-- the loop-τ (t done with inj₁ a′ ⇒ loop) and the terminal √ (t done with inj₂ r)
iter-loop-τ : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {a′ : A}
            → PTree.force t ≡ ret (inj₁ a′) → iter-bind t k ─[ τ ]─► iter k a′
iter-loop-τ k t eqt = sSil (fIter-r1 k t eqt)

iter-stop-√ : (k : A → PTree E (ExtI E) (A ⊎ R)) (t : PTree E (ExtI E) (A ⊎ R)) {r : R}
            → PTree.force t ≡ ret (inj₂ r) → iter-bind t k ─[ ev (√ r) ]─► deadlock
iter-stop-√ k t eqt = sRet (fIter-r2 k t eqt)

-- from t ≈ t′ and t poised at ret X, t′ weakly reaches a state poised at ret X
≈-reaches-ret : {t t′ : PTree E (ExtI E) (A ⊎ R)} {Y : A ⊎ R}
              → t ≈ t′ → PTree.force t ≡ ret Y
              → Σ[ p′ ∈ PTree E (ExtI E) (A ⊎ R) ] (t′ ─[τ*]─► p′) × (PTree.force p′ ≡ ret Y)
≈-reaches-ret tt′ eqt with tt′ .Wbisim.fwd .WSimF.on-ev (sRet eqt)
... | _ , wev t′→p′ (sRet fp′) _ , _ = _ , t′→p′ , fp′

-------------------------------------------------------------------------------------
-- the congruence (mutual coinduction)
-------------------------------------------------------------------------------------

iter-bind-cong : (k k′ : A → PTree E (ExtI E) (A ⊎ R)) → (∀ a → (k a) ≈ (k′ a))
               → {t t′ : PTree E (ExtI E) (A ⊎ R)} → t ≈ t′ → (iter-bind t k) ≈ (iter-bind t′ k′)
iter-bind-sim : (k k′ : A → PTree E (ExtI E) (A ⊎ R)) → (∀ a → (k a) ≈ (k′ a))
              → {t t′ : PTree E (ExtI E) (A ⊎ R)} → t ≈ t′
              → WSimF (Wbisim R) (iter-bind t k) (iter-bind t′ k′)

iter-bind-cong k k′ kk′ tt′ .Wbisim.fwd = iter-bind-sim k k′ kk′ tt′
iter-bind-cong k k′ kk′ tt′ .Wbisim.bwd = iter-bind-sim k′ k (λ a → wbisim-sym (kk′ a)) (wbisim-sym tt′)

iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-tau step with PTree.force t in eqt
... | ret (inj₂ r) = ⊥-elim (ret-no-τ (fIter-r2 k t eqt) step)
... | ret (inj₁ a′) with sil-τ-inv (fIter-r1 k t eqt) step | ≈-reaches-ret tt′ eqt
...   | refl | p′ , t′→p′ , fp′ =
        iter k′ a′
      , wτ (τ*-trans (iter-bind-τ* k′ t′→p′) (τ*-step (iter-loop-τ k′ p′ fp′) τ*-refl))
      , iter-bind-cong k k′ kk′ (kk′ a′)
iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-tau step | sil c
  with sil-τ-inv (fIter-sil k t eqt) step | tt′ .Wbisim.fwd .WSimF.on-tau (sSil eqt)
...   | refl | c′ , wτ t′→c′ , cc′ =
        iter-bind c′ k′ , wτ (iter-bind-τ* k′ t′→c′) , iter-bind-cong k k′ kk′ cc′
iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-tau step | react v τc
  with react-τ-inv (fIter-react k t eqt) step
...   | i , a , br with iterT-elim k (react v τc) br
...     | t″ , vτ , refl with tt′ .Wbisim.fwd .WSimF.on-tau (sTau eqt vτ)
...       | t‴ , wτ t′→t‴ , rel =
            iter-bind t‴ k′ , wτ (iter-bind-τ* k′ t′→t‴) , iter-bind-cong k k′ kk′ rel

iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-ev step with PTree.force t in eqt
... | ret (inj₁ a′) = ⊥-elim (sil-no-ev (fIter-r1 k t eqt) step)
... | sil c         = ⊥-elim (sil-no-ev (fIter-sil k t eqt) step)
... | ret (inj₂ r) with step
...   | sRet eqf with trans (sym (fIter-r2 k t eqt)) eqf | ≈-reaches-ret tt′ eqt
...     | refl | p′ , t′→p′ , fp′ =
          deadlock , wev (iter-bind-τ* k′ t′→p′) (iter-stop-√ k′ p′ fp′) τ*-refl , wbisim-refl deadlock
iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-ev step | ret (inj₂ r) | sVis eqf _ =
  ⊥-elim (case trans (sym (fIter-r2 k t eqt)) eqf of λ ())
iter-bind-sim k k′ kk′ {t = t} {t′ = t′} tt′ .WSimF.on-ev step | react v τc with step
...   | sRet eqf = ⊥-elim (case trans (sym (fIter-react k t eqt)) eqf of λ ())
...   | sVis {at = at} {a = a} eqf br
        with iterV-elim k (react v τc)
               (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective (trans (sym (fIter-react k t eqt)) eqf)))) br)
...     | t″ , vv , refl with tt′ .Wbisim.fwd .WSimF.on-ev (sVis eqt vv)
...       | t‴ , wev t′→p′ p′ev q′→t‴ , rel =
            iter-bind t‴ k′
          , wev (iter-bind-τ* k′ t′→p′) (iter-bind-ev k′ _ p′ev) (iter-bind-τ* k′ q′→t‴)
          , iter-bind-cong k k′ kk′ rel

-------------------------------------------------------------------------------------
-- iteration is a ≈-congruence
-------------------------------------------------------------------------------------

iter-cong : {k k′ : A → PTree E (ExtI E) (A ⊎ R)}
          → (∀ a → (k a) ≈ (k′ a)) → (∀ a → (iter k a) ≈ (iter k′ a))
iter-cong {k = k} {k′ = k′} kk′ a = iter-bind-cong k k′ kk′ (kk′ a)
