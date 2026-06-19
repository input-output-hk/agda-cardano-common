{-# OPTIONS --guardedness #-}

-- ;-assoc (T6.3 / U7.x) = the monad ASSOCIATIVITY law:
--   (P >>= j) >>= k  ∼  P >>= (λ r → j r >>= k)
-- a genuine coinductive strong bisimulation over the double bind.  Proved with the same
-- guardedness engineering as bind-ret (SeqLaws): the with-HEAVY decomposition of a step
-- (decompose-ev/τ-fwd/bwd) lives OUTSIDE the mutual block and does NO corecursion; the
-- with-FREE assemblers (mk-*) sit INSIDE the block with the corecursive call directly
-- under the Σ constructor; and a mutual REVERSED bisim bind-assocR avoids sbisim-sym.
--
-- The crux is the ret-boundary: when force P = ret r, BOTH sides are force-equal to
-- (j r) >>= k — LHS via fBind-cong over force(P>>=j)=force(j r), RHS via fBind-ret over
-- the η-expansion (j r >>= k) = (λ r → j r >>= k) r — so that subtree needs no
-- recursion.  At sil/react the two sides step in lock-step to children related, after the
-- bindV/bindT view-fusion, by bind-assoc on the residual.

open import Level using (Level)
open import Data.Maybe using (just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.FD.SeqAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_>>=_; bindV; bindT)
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.FD.SeqLaws            E-≟ using (retarget; sbisim-force-eq)
open import CSP.Laws.Bisim.IterCong        E-≟
  using (ret-no-τ; sil-no-ev; sil-τ-inv; react-τ-inv)
open import CSP.Laws.Bisim.LoopCong        E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim; bindV-eq; bindT-eq)

private
  variable
    ℓr ℓs ℓt : Level
    R : Set ℓr
    S : Set ℓs
    T : Set ℓt

-- force(_>>=k) depends only on the force of its argument.
fBind-cong : (k : S → PTree E (ExtI E) T) (a b : PTree E (ExtI E) S)
           → PTree.force a ≡ PTree.force b
           → PTree.force (a >>= k) ≡ PTree.force (b >>= k)
fBind-cong k a b eq with PTree.force a | PTree.force b | eq
... | ret r     | .(ret r)     | refl = refl
... | sil c     | .(sil c)     | refl = refl
... | react v τc | .(react v τc) | refl = refl

-- ret-boundary: both sides are force-equal to (j r) >>= k.
assoc-ret-eq : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
               (P : PTree E (ExtI E) R) {r : R}
             → PTree.force P ≡ ret r
             → PTree.force ((P >>= j) >>= k) ≡ PTree.force (P >>= (λ r → j r >>= k))
assoc-ret-eq j k P {r = r} eqP =
  trans (fBind-cong k (P >>= j) (j r) (fBind-ret j P eqP))
        (sym (fBind-ret (λ r → j r >>= k) P eqP))

-------------------------------------------------------------------------------------
-- decomposition (with-heavy, NO corecursion, outside the mutual block)
-------------------------------------------------------------------------------------

-- forward: a step of (P>>=j)>>=k becomes a step of P>>=(λr→j r>>=k) + residual.
decompose-ev-fwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
                   (P : PTree E (ExtI E) R) {l : Event√ T} {M : PTree E (ExtI E) T}
  → ((P >>= j) >>= k) ─[ ev l ]─► M
  → ((P >>= (λ r → j r >>= k)) ─[ ev l ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         ((P >>= (λ r → j r >>= k)) ─[ ev l ]─► (s >>= (λ r → j r >>= k)))
         × (M ≡ ((s >>= j) >>= k)))
decompose-ev-fwd j k P step with PTree.force P in eqP
... | ret r  = inj₁ (retarget (sym (assoc-ret-eq j k P eqP)) step)
... | sil c  = ⊥-elim (sil-no-ev (fBind-sil k (P >>= j) (fBind-sil j P eqP)) step)
... | react v τc with step
...   | sRet eqf = ⊥-elim (case trans (sym (fBind-react k (P >>= j) (fBind-react j P eqP))) eqf of λ ())
...   | sVis {at = at} {a = a} eqf br
        with bindV-elim k (react (bindV j (react v τc)) (bindT j (react v τc)))
               (subst (λ g → g at a ≡ just _)
                      (sym (proj₁ (react-injective
                        (trans (sym (fBind-react k (P >>= j) (fBind-react j P eqP))) eqf)))) br)
...     | t , vt , refl with bindV-elim j (react v τc) vt
...       | s , vs , refl =
            inj₂ (s
                 , sVis (fBind-react (λ r → j r >>= k) P eqP)
                        (bindV-eq (λ r → j r >>= k) (react v τc) vs)
                 , refl)

decompose-τ-fwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
                  (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) T}
  → ((P >>= j) >>= k) ─[ τ ]─► M
  → ((P >>= (λ r → j r >>= k)) ─[ τ ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         ((P >>= (λ r → j r >>= k)) ─[ τ ]─► (s >>= (λ r → j r >>= k)))
         × (M ≡ ((s >>= j) >>= k)))
decompose-τ-fwd j k P step with PTree.force P in eqP
... | ret r  = inj₁ (retarget (sym (assoc-ret-eq j k P eqP)) step)
... | sil c with sil-τ-inv (fBind-sil k (P >>= j) (fBind-sil j P eqP)) step
...   | refl = inj₂ (c , sSil (fBind-sil (λ r → j r >>= k) P eqP) , refl)
decompose-τ-fwd j k P step | react v τc
  with react-τ-inv (fBind-react k (P >>= j) (fBind-react j P eqP)) step
... | i , a , br with bindT-elim k (react (bindV j (react v τc)) (bindT j (react v τc))) br
...   | t , vt , refl with bindT-elim j (react v τc) vt
...     | s , vs , refl =
          inj₂ (s
               , sTau (fBind-react (λ r → j r >>= k) P eqP)
                      (bindT-eq (λ r → j r >>= k) (react v τc) vs)
               , refl)

-- backward: a step of P>>=(λr→j r>>=k) becomes a step of (P>>=j)>>=k + residual.
decompose-ev-bwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
                   (P : PTree E (ExtI E) R) {l : Event√ T} {M : PTree E (ExtI E) T}
  → ((P >>= (λ r → j r >>= k))) ─[ ev l ]─► M
  → (((P >>= j) >>= k) ─[ ev l ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         (((P >>= j) >>= k) ─[ ev l ]─► ((s >>= j) >>= k))
         × (M ≡ (s >>= (λ r → j r >>= k))))
decompose-ev-bwd j k P step with PTree.force P in eqP
... | ret r  = inj₁ (retarget (assoc-ret-eq j k P eqP) step)
... | sil c  = ⊥-elim (sil-no-ev (fBind-sil (λ r → j r >>= k) P eqP) step)
... | react v τc with step
...   | sRet eqf = ⊥-elim (case trans (sym (fBind-react (λ r → j r >>= k) P eqP)) eqf of λ ())
...   | sVis {at = at} {a = a} eqf br
        with bindV-elim (λ r → j r >>= k) (react v τc)
               (subst (λ g → g at a ≡ just _)
                      (sym (proj₁ (react-injective
                        (trans (sym (fBind-react (λ r → j r >>= k) P eqP)) eqf)))) br)
...     | s , vs , refl =
          inj₂ (s
               , sVis (fBind-react k (P >>= j) (fBind-react j P eqP))
                      (bindV-eq k (react (bindV j (react v τc)) (bindT j (react v τc)))
                                (bindV-eq j (react v τc) vs))
               , refl)

decompose-τ-bwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
                  (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) T}
  → ((P >>= (λ r → j r >>= k))) ─[ τ ]─► M
  → (((P >>= j) >>= k) ─[ τ ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         (((P >>= j) >>= k) ─[ τ ]─► ((s >>= j) >>= k))
         × (M ≡ (s >>= (λ r → j r >>= k))))
decompose-τ-bwd j k P step with PTree.force P in eqP
... | ret r  = inj₁ (retarget (assoc-ret-eq j k P eqP) step)
... | sil c with sil-τ-inv (fBind-sil (λ r → j r >>= k) P eqP) step
...   | refl = inj₂ (c , sSil (fBind-sil k (P >>= j) (fBind-sil j P eqP)) , refl)
decompose-τ-bwd j k P step | react v τc
  with react-τ-inv (fBind-react (λ r → j r >>= k) P eqP) step
... | i , a , br with bindT-elim (λ r → j r >>= k) (react v τc) br
...   | s , vs , refl =
        inj₂ (s
             , sTau (fBind-react k (P >>= j) (fBind-react j P eqP))
                    (bindT-eq k (react (bindV j (react v τc)) (bindT j (react v τc)))
                              (bindT-eq j (react v τc) vs))
             , refl)

-------------------------------------------------------------------------------------
-- the mutual block: with-free assemblers + reversed bisim
-------------------------------------------------------------------------------------

bind-assoc  : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
              (P : PTree E (ExtI E) R)
            → ((P >>= j) >>= k) ∼ (P >>= (λ r → j r >>= k))
bind-assocR : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
              (P : PTree E (ExtI E) R)
            → (P >>= (λ r → j r >>= k)) ∼ ((P >>= j) >>= k)

mk-ev-fwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
            {P : PTree E (ExtI E) R} {l : Event√ T} {M : PTree E (ExtI E) T}
  → ((P >>= (λ r → j r >>= k)) ─[ ev l ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         ((P >>= (λ r → j r >>= k)) ─[ ev l ]─► (s >>= (λ r → j r >>= k)))
         × (M ≡ ((s >>= j) >>= k)))
  → Σ[ M′ ∈ PTree E (ExtI E) T ] ((P >>= (λ r → j r >>= k)) ─[ ev l ]─► M′ × Sbisim T M M′)
mk-τ-fwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
           {P : PTree E (ExtI E) R} {M : PTree E (ExtI E) T}
  → ((P >>= (λ r → j r >>= k)) ─[ τ ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         ((P >>= (λ r → j r >>= k)) ─[ τ ]─► (s >>= (λ r → j r >>= k)))
         × (M ≡ ((s >>= j) >>= k)))
  → Σ[ M′ ∈ PTree E (ExtI E) T ] ((P >>= (λ r → j r >>= k)) ─[ τ ]─► M′ × Sbisim T M M′)

mk-ev-bwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
            {P : PTree E (ExtI E) R} {l : Event√ T} {M : PTree E (ExtI E) T}
  → (((P >>= j) >>= k) ─[ ev l ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         (((P >>= j) >>= k) ─[ ev l ]─► ((s >>= j) >>= k))
         × (M ≡ (s >>= (λ r → j r >>= k))))
  → Σ[ M′ ∈ PTree E (ExtI E) T ] (((P >>= j) >>= k) ─[ ev l ]─► M′ × Sbisim T M M′)
mk-τ-bwd : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
           {P : PTree E (ExtI E) R} {M : PTree E (ExtI E) T}
  → (((P >>= j) >>= k) ─[ τ ]─► M)
    ⊎ (Σ[ s ∈ PTree E (ExtI E) R ]
         (((P >>= j) >>= k) ─[ τ ]─► ((s >>= j) >>= k))
         × (M ≡ (s >>= (λ r → j r >>= k))))
  → Σ[ M′ ∈ PTree E (ExtI E) T ] (((P >>= j) >>= k) ─[ τ ]─► M′ × Sbisim T M M′)

bind-assoc  j k P .Sbisim.fwd .SSimF.on-ev  step = mk-ev-fwd j k (decompose-ev-fwd j k P step)
bind-assoc  j k P .Sbisim.fwd .SSimF.on-tau step = mk-τ-fwd  j k (decompose-τ-fwd  j k P step)
bind-assoc  j k P .Sbisim.bwd .SSimF.on-ev  step = mk-ev-bwd j k (decompose-ev-bwd j k P step)
bind-assoc  j k P .Sbisim.bwd .SSimF.on-tau step = mk-τ-bwd  j k (decompose-τ-bwd  j k P step)
bind-assocR j k P .Sbisim.fwd .SSimF.on-ev  step = mk-ev-bwd j k (decompose-ev-bwd j k P step)
bind-assocR j k P .Sbisim.fwd .SSimF.on-tau step = mk-τ-bwd  j k (decompose-τ-bwd  j k P step)
bind-assocR j k P .Sbisim.bwd .SSimF.on-ev  step = mk-ev-fwd j k (decompose-ev-fwd j k P step)
bind-assocR j k P .Sbisim.bwd .SSimF.on-tau step = mk-τ-fwd  j k (decompose-τ-fwd  j k P step)

mk-ev-fwd j k (inj₁ rstep)               = _ , rstep , sbisim-refl _
mk-ev-fwd j k (inj₂ (s , rstep , refl))  = _ , rstep , bind-assoc  j k s
mk-τ-fwd  j k (inj₁ rstep)               = _ , rstep , sbisim-refl _
mk-τ-fwd  j k (inj₂ (s , rstep , refl))  = _ , rstep , bind-assoc  j k s
mk-ev-bwd j k (inj₁ lstep)               = _ , lstep , sbisim-refl _
mk-ev-bwd j k (inj₂ (s , lstep , refl))  = _ , lstep , bind-assocR j k s
mk-τ-bwd  j k (inj₁ lstep)               = _ , lstep , sbisim-refl _
mk-τ-bwd  j k (inj₂ (s , lstep , refl))  = _ , lstep , bind-assocR j k s

-- the law at ≈FD
seq-assoc-∼ : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
              (P : PTree E (ExtI E) R)
            → ((P >>= j) >>= k) ∼ (P >>= (λ r → j r >>= k))
seq-assoc-∼ = bind-assoc

seq-assoc-FD : (j : R → PTree E (ExtI E) S) (k : S → PTree E (ExtI E) T)
               (P : PTree E (ExtI E) R)
             → ((P >>= j) >>= k) ≈FD (P >>= (λ r → j r >>= k))
seq-assoc-FD j k P = drbisim→≈FD (sbisim→drbisim (bind-assoc j k P))
