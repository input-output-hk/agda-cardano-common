{-# OPTIONS --guardedness #-}

-- SPIKE: external-choice trace ELIMINATION + monotonicity on the pure-react layer.
--   ▷-trace-elim : traces (P ▷ Q) s → traces P s ⊎ traces Q s
--   □-trace-elim : traces (P □ Q) s → traces P s ⊎ traces Q s
--   □-mono-⊑ᵀ    : P ⊑T P′ → Q ⊑T Q′ → (P □ Q) ⊑T (P′ □ Q′)   (via elim + ⊑ᵀ-□-L/R)
-- Both elims invert the operator's transitions (each step of P □ Q / P ▷ Q is a step
-- of P, of Q, or a τ keeping the choice/slide alive); recursion is on the big-step.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsExtChoiceMono {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators        E-≟
open import Semantics.LTS             {E = E} {I = ExtI E}
open import Semantics.Failures        {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLaws        E-≟
  using (force-▷-ret; force-▷-react; force-▷-sil; ⊓-trace-elim;
         ⊑ᵀ-⊓-L; ⊑ᵀ-⊓-R; ⊑ᵀ-▷-L; ▷-τ-L; ▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟
  using (NonRet; fL-A; fL-B; fL-C; fL-D; fL-E; fL-F; fL-G; ⊑ᵀ-□-L; ⊑ᵀ-□-R)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- ▷ transition inversions
-------------------------------------------------------------------------------------

-- a τ-source `viewT nP j a' ≡ just P'` is a real τ-step of P
viewT-τ : {P : PTree E (ExtI E) R} {nP : NodeKind E (ExtI E) R}
            {j : AnyTypes (ExtI E)} {a' : proj₁ j} {P' : PTree E (ExtI E) R}
        → PTree.force P ≡ nP → viewT nP j a' ≡ just P' → P ─[ τ ]─► P'
viewT-τ {nP = ret _}    eqP veq = case veq of λ ()
viewT-τ {nP = react v τc} eqP veq = sTau eqP veq
viewT-τ {nP = sil P₁} {j = _ , base _}   eqP veq = case veq of λ ()
viewT-τ {nP = sil P₁} {j = _ , pair _ _} eqP veq = case veq of λ ()
viewT-τ {nP = sil P₁} {j = _ , fin} {a' = lift fzero}      eqP veq = case veq of λ { refl → sSil eqP }
viewT-τ {nP = sil P₁} {j = _ , fin} {a' = lift (fsuc _)}   eqP veq = case veq of λ ()

-- a `just M` out of ▷-slide is the timeout (M ≡ Q) or P's own τ (M ≡ P' ▷ Q)
▷-slide-elim : (nP : NodeKind E (ExtI E) R) (Q : PTree E (ExtI E) R)
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
             → ▷-slide nP Q i a ≡ just M
             → (M ≡ Q)
             ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
                  (viewT nP j a' ≡ just P') × (M ≡ P' ▷ Q))
▷-slide-elim nP Q {_ , base _}            eq = case eq of λ ()
▷-slide-elim nP Q {_ , fin}               eq = case eq of λ ()
▷-slide-elim nP Q {_ , pair (base _) _}   eq = case eq of λ ()
▷-slide-elim nP Q {_ , pair (pair _ _) _} eq = case eq of λ ()
▷-slide-elim nP Q {_ , pair fin j} {lift fzero        , a'} eq = inj₁ (sym (just-injective eq))
▷-slide-elim nP Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nP (_ , j) a' in veq
... | just P' = inj₂ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
▷-slide-elim nP Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- force (P ▷ Q) ≡ ret r ⇒ force P ≡ ret r
▷-force-ret-inv : {P Q : PTree E (ExtI E) R} {r : R}
                → PTree.force (P ▷ Q) ≡ ret r → PTree.force P ≡ ret r
▷-force-ret-inv {P = P} eqf with PTree.force P
... | ret r'      = eqf
... | sil P'      = case eqf of λ ()
... | react vP τcP = case eqf of λ ()

-- generic inversions against a known force shape
ret-no-τ : {t M : PTree E (ExtI E) R} {r : R} → PTree.force t ≡ ret r → t ─[ τ ]─► M → ⊥
ret-no-τ eqf (sSil sileq)    = case (trans (sym sileq) eqf) of λ ()
ret-no-τ eqf (sTau extceq _) = case (trans (sym extceq) eqf) of λ ()

react-τ-inv : {t M : PTree E (ExtI E) R}
               {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → PTree.force t ≡ react v τc → t ─[ τ ]─► M
           → Σ[ i ∈ AnyTypes (ExtI E) ] Σ[ a ∈ proj₁ i ] (τc i a ≡ just M)
react-τ-inv eqf (sSil sileq) = ⊥-elim (sil≢react (trans (sym sileq) eqf))
react-τ-inv {M = M} eqf (sTau {i = i} {a = a} extceq breq) =
  i , a , subst (λ g → g i a ≡ just M)
                (sym (proj₂ (react-injective (trans (sym eqf) extceq)))) breq

-- if P ▷ Q offers a (just M) at `at a`, then P itself offers it there
▷-force-react-inv : {P Q : PTree E (ExtI E) R}
                     {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                     {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                     {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                 → PTree.force (P ▷ Q) ≡ react v τc → v at a ≡ just M
                 → Σ[ vP ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
                   Σ[ τcP ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                     (PTree.force P ≡ react vP τcP) × (vP at a ≡ just M)
-- (the `with` rewrites force P everywhere — in eqf and the goal — to the forced shape)
▷-force-react-inv {P = P} {Q = Q} {at = at} {a = a} eqf breq with PTree.force P
... | ret r       = case eqf of λ ()
... | sil P'      = case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()
... | react vP τcP = vP , τcP , refl , subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq

-- a τ-step of P ▷ Q is the timeout (→ Q) or P's own τ (→ P′ ▷ Q)
▷-τ-elim : (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
         → (P ▷ Q) ─[ τ ]─► M
         → (M ≡ Q) ⊎ (Σ[ P' ∈ PTree E (ExtI E) R ] (P ─[ τ ]─► P') × (M ≡ P' ▷ Q))
▷-τ-elim P Q step with PTree.force P in eqP
... | ret r  = ⊥-elim (ret-no-τ (force-▷-ret {P = P} {Q = Q} eqP) step)
... | sil P' = case react-τ-inv (force-▷-sil {P = P} {Q = Q} eqP) step of λ where
    (i , a , breq) → case ▷-slide-elim (sil P') Q {i = i} {a = a} breq of λ where
      (inj₁ m≡Q)                      → inj₁ m≡Q
      (inj₂ (j , a' , P' , veq , m≡)) → inj₂ (P' , viewT-τ eqP veq , m≡)
... | react vP τcP = case react-τ-inv (force-▷-react {P = P} {Q = Q} eqP) step of λ where
    (i , a , breq) → case ▷-slide-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
      (inj₁ m≡Q)                      → inj₁ m≡Q
      (inj₂ (j , a' , P' , veq , m≡)) → inj₂ (P' , viewT-τ eqP veq , m≡)

-- a visible step of P ▷ Q is a visible step of P (to the same successor)
▷-ev-elim : (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R} {e : Event√ R}
          → (P ▷ Q) ─[ ev e ]─► M → P ─[ ev e ]─► M
▷-ev-elim P Q (sRet eqf) = sRet (▷-force-ret-inv {P = P} {Q = Q} eqf)
▷-ev-elim P Q (sVis {at = at} {a = a} eqf breq) =
  case ▷-force-react-inv {P = P} {Q = Q} eqf breq of λ where
    (vP , τcP , eqP , breq') → sVis eqP breq'

-------------------------------------------------------------------------------------
-- ▷-trace-elim : traces (P ▷ Q) s → traces P s ⊎ traces Q s
-------------------------------------------------------------------------------------

▷-trace-elim : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
             → (P ▷ Q) ⟹⟨ s ⟩ Rt → traces P s ⊎ traces Q s
▷-trace-elim P Q ⟹-refl = inj₁ (P , ⟹-refl)
▷-trace-elim P Q (⟹-τ {q = M} step rest) with ▷-τ-elim P Q step
... | inj₁ refl                = inj₂ (_ , rest)
... | inj₂ (P' , Pτ , refl) with ▷-trace-elim P' Q rest
...   | inj₁ (Rt' , tP')       = inj₁ (Rt' , ⟹-τ Pτ tP')
...   | inj₂ tQ                = inj₂ tQ
▷-trace-elim P Q (⟹-ev step rest) = inj₁ (_ , ⟹-ev (▷-ev-elim P Q step) rest)

-------------------------------------------------------------------------------------
-- □ continuation inversions (mirroring ▷-slide-elim)
-------------------------------------------------------------------------------------

-- br2 (the ⊓-shape used for ret|ret with different values): tag0 → P, tag1 → Q
br2-elim : (P Q : PTree E (ExtI E) R) {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
         → br2 P Q i a ≡ just M → (M ≡ P) ⊎ (M ≡ Q)
br2-elim P Q {_ , base _}   eq = case eq of λ ()
br2-elim P Q {_ , pair _ _} eq = case eq of λ ()
br2-elim P Q {_ , fin} {lift fzero}             eq = inj₁ (sym (just-injective eq))
br2-elim P Q {_ , fin} {lift (fsuc fzero)}      eq = inj₂ (sym (just-injective eq))
br2-elim P Q {_ , fin} {lift (fsuc (fsuc _))}   eq = case eq of λ ()

-- P terminated, Q live: tag0 → P (commit), tag1 → Q's τ (→ Q′ ▷ P)
□-slide-RQ-elim : (P : PTree E (ExtI E) R) (nQ : NodeKind E (ExtI E) R)
                    {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
                → □-slide-RQ P nQ i a ≡ just M
                → (M ≡ P)
                ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ Q' ∈ PTree E (ExtI E) R ]
                     (viewT nQ j a' ≡ just Q') × (M ≡ Q' ▷ P))
□-slide-RQ-elim P nQ {_ , base _}            eq = case eq of λ ()
□-slide-RQ-elim P nQ {_ , fin}               eq = case eq of λ ()
□-slide-RQ-elim P nQ {_ , pair (base _) _}   eq = case eq of λ ()
□-slide-RQ-elim P nQ {_ , pair (pair _ _) _} eq = case eq of λ ()
□-slide-RQ-elim P nQ {_ , pair fin j} {lift fzero        , a'} eq = inj₁ (sym (just-injective eq))
□-slide-RQ-elim P nQ {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nQ (_ , j) a' in veq
... | just Q' = inj₂ ((_ , j) , a' , Q' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
□-slide-RQ-elim P nQ {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- P live, Q terminated: tag0 → Q (commit), tag1 → P's τ (→ P′ ▷ Q)
□-slide-PR-elim : (nP : NodeKind E (ExtI E) R) (Q : PTree E (ExtI E) R)
                    {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
                → □-slide-PR nP Q i a ≡ just M
                → (M ≡ Q)
                ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
                     (viewT nP j a' ≡ just P') × (M ≡ P' ▷ Q))
□-slide-PR-elim nP Q {_ , base _}            eq = case eq of λ ()
□-slide-PR-elim nP Q {_ , fin}               eq = case eq of λ ()
□-slide-PR-elim nP Q {_ , pair (base _) _}   eq = case eq of λ ()
□-slide-PR-elim nP Q {_ , pair (pair _ _) _} eq = case eq of λ ()
□-slide-PR-elim nP Q {_ , pair fin j} {lift fzero        , a'} eq = inj₁ (sym (just-injective eq))
□-slide-PR-elim nP Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nP (_ , j) a' in veq
... | just P' = inj₂ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
□-slide-PR-elim nP Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- both live: tag0 → P's τ (→ P′ □ Q), tag1 → Q's τ (→ P □ Q′)
□-mt-elim : ⦃ _ : DecEq R ⦄ (nP nQ : NodeKind E (ExtI E) R) (P Q : PTree E (ExtI E) R)
              {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
          → □-mt nP nQ P Q i a ≡ just M
          → (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
               (viewT nP j a' ≡ just P') × (M ≡ P' □ Q))
          ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ Q' ∈ PTree E (ExtI E) R ]
               (viewT nQ j a' ≡ just Q') × (M ≡ P □ Q'))
□-mt-elim nP nQ P Q {_ , base _}            eq = case eq of λ ()
□-mt-elim nP nQ P Q {_ , fin}               eq = case eq of λ ()
□-mt-elim nP nQ P Q {_ , pair (base _) _}   eq = case eq of λ ()
□-mt-elim nP nQ P Q {_ , pair (pair _ _) _} eq = case eq of λ ()
□-mt-elim nP nQ P Q {_ , pair fin j} {lift fzero        , a'} eq with viewT nP (_ , j) a' in veq
... | just P' = inj₁ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
□-mt-elim nP nQ P Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nQ (_ , j) a' in veq
... | just Q' = inj₂ ((_ , j) , a' , Q' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
□-mt-elim nP nQ P Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- merged offers: P only, Q only, or both (→ P₁ ⊓ Q₁)
mergeVis-elim : (vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                  (at : AnyTypes E) (a : proj₁ at) {M : PTree E (ExtI E) R}
              → mergeVis vP vQ at a ≡ just M
              → ((vP at a ≡ just M) × (vQ at a ≡ nothing))
              ⊎ ((vP at a ≡ nothing) × (vQ at a ≡ just M))
              ⊎ (Σ[ P₁ ∈ PTree E (ExtI E) R ] Σ[ Q₁ ∈ PTree E (ExtI E) R ]
                   (vP at a ≡ just P₁) × (vQ at a ≡ just Q₁) × (M ≡ P₁ ⊓ Q₁))
mergeVis-elim vP vQ at a eq with vP at a | vQ at a
... | just p  | nothing = inj₁ (eq , refl)
... | nothing | just q  = inj₂ (inj₁ (refl , eq))
... | just p  | just q  = inj₂ (inj₂ (p , q , refl , refl , sym (just-injective eq)))
... | nothing | nothing = case eq of λ ()

-- force (P □ Q) ≡ ret r ⇒ force P ≡ ret r  (the only ret-producing clause is ret|ret-yes)
□-force-ret-inv : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r : R}
                → PTree.force (P □ Q) ≡ ret r → PTree.force P ≡ ret r
□-force-ret-inv {P = P} {Q = Q} eqf with PTree.force P | PTree.force Q
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = eqf
...   | no  _    = case eqf of λ ()
□-force-ret-inv eqf | ret _    | sil _    = case eqf of λ ()
□-force-ret-inv eqf | ret _    | react _ _ = case eqf of λ ()
□-force-ret-inv eqf | sil _    | ret _    = case eqf of λ ()
□-force-ret-inv eqf | sil _    | sil _    = case eqf of λ ()
□-force-ret-inv eqf | sil _    | react _ _ = case eqf of λ ()
□-force-ret-inv eqf | react _ _ | ret _    = case eqf of λ ()
□-force-ret-inv eqf | react _ _ | sil _    = case eqf of λ ()
□-force-ret-inv eqf | react _ _ | react _ _ = case eqf of λ ()

-------------------------------------------------------------------------------------
-- □-τ-elim : a τ-step of P □ Q is one of six shapes (commit / slide / choice, L or R)
-------------------------------------------------------------------------------------

data □τR {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (P Q M : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  cP  : M ≡ P → □τR P Q M
  cQ  : M ≡ Q → □τR P Q M
  sPQ : (P' : PTree E (ExtI E) R) → P ─[ τ ]─► P' → M ≡ P' ▷ Q → □τR P Q M
  sQP : (Q' : PTree E (ExtI E) R) → Q ─[ τ ]─► Q' → M ≡ Q' ▷ P → □τR P Q M
  chP : (P' : PTree E (ExtI E) R) → P ─[ τ ]─► P' → M ≡ P' □ Q → □τR P Q M
  chQ : (Q' : PTree E (ExtI E) R) → Q ─[ τ ]─► Q' → M ≡ P □ Q' → □τR P Q M

□-τ-elim : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
         → (P □ Q) ─[ τ ]─► M → □τR P Q M
□-τ-elim P Q step with PTree.force P in eqP | PTree.force Q in eqQ
... | ret rP | ret rQ = case rP ≟ rQ of λ where
    (yes refl) → ⊥-elim (ret-no-τ (fL-A {P = P} {Q = Q} eqP eqQ) step)
    (no  ¬eq)  → case react-τ-inv (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) step of λ where
      (i , a , breq) → case br2-elim P Q {i = i} {a = a} breq of λ where
        (inj₁ m≡P) → cP m≡P
        (inj₂ m≡Q) → cQ m≡Q
... | ret rP | sil Q' = case react-τ-inv (fL-C {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-RQ-elim P (sil Q') {i = i} {a = a} breq of λ where
      (inj₁ m≡P)                      → cP m≡P
      (inj₂ (j , a' , Q' , veq , m≡)) → sQP Q' (viewT-τ eqQ veq) m≡
... | ret rP | react vQ τcQ = case react-τ-inv (fL-D {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-RQ-elim P (react vQ τcQ) {i = i} {a = a} breq of λ where
      (inj₁ m≡P)                      → cP m≡P
      (inj₂ (j , a' , Q' , veq , m≡)) → sQP Q' (viewT-τ eqQ veq) m≡
... | sil P' | ret rQ = case react-τ-inv (fL-E {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-PR-elim (sil P') Q {i = i} {a = a} breq of λ where
      (inj₁ m≡Q)                      → cQ m≡Q
      (inj₂ (j , a' , P' , veq , m≡)) → sPQ P' (viewT-τ eqP veq) m≡
... | react vP τcP | ret rQ = case react-τ-inv (fL-F {P = P} {Q = Q} eqP eqQ) step of λ where
    (i , a , breq) → case □-slide-PR-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
      (inj₁ m≡Q)                      → cQ m≡Q
      (inj₂ (j , a' , P' , veq , m≡)) → sPQ P' (viewT-τ eqP veq) m≡
... | sil P' | sil Q' = case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (sil Q') P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , m≡)) → chP P' (viewT-τ eqP veq) m≡
      (inj₂ (j , a' , Q' , veq , m≡)) → chQ Q' (viewT-τ eqQ veq) m≡
... | sil P' | react vQ τcQ = case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (sil P') (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , m≡)) → chP P' (viewT-τ eqP veq) m≡
      (inj₂ (j , a' , Q' , veq , m≡)) → chQ Q' (viewT-τ eqQ veq) m≡
... | react vP τcP | sil Q' = case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (sil Q') P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , m≡)) → chP P' (viewT-τ eqP veq) m≡
      (inj₂ (j , a' , Q' , veq , m≡)) → chQ Q' (viewT-τ eqQ veq) m≡
... | react vP τcP | react vQ τcQ = case react-τ-inv (fL-G {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case □-mt-elim (react vP τcP) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , m≡)) → chP P' (viewT-τ eqP veq) m≡
      (inj₂ (j , a' , Q' , veq , m≡)) → chQ Q' (viewT-τ eqQ veq) m≡

-------------------------------------------------------------------------------------
-- □-ev-elim : a visible/√ step of P □ Q is a step of P, of Q, or of both (→ P₁ ⊓ Q₁)
-------------------------------------------------------------------------------------

data □evR {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
     : PTree E (ExtI E) R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  evP  : ∀ {e M}        → P ─[ ev e ]─► M  → □evR P Q M e
  evQ  : ∀ {e M}        → Q ─[ ev e ]─► M  → □evR P Q M e
  evPQ : ∀ {e P₁ Q₁}    → P ─[ ev e ]─► P₁ → Q ─[ ev e ]─► Q₁ → □evR P Q (P₁ ⊓ Q₁) e

-- the visible-offer inversion (eqf is rewritten by the `with`; ret|ret needs r ≟ r)
□-vis-inv : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
              {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
          → PTree.force (P □ Q) ≡ react v τc → v at a ≡ just M
          → □evR P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
□-vis-inv P Q {at = at} {a = a} eqf breq with PTree.force P in eqP | PTree.force Q in eqQ
□-vis-inv P Q eqf breq | ret rP | ret rQ with rP ≟ rQ
□-vis-inv P Q eqf breq | ret rP | ret rQ | yes refl = case eqf of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | ret rP | ret rQ | no ¬eq =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | ret rP | sil Q' =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | ret rP | react vQ τcQ =
  evQ (sVis eqQ (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq))
□-vis-inv P Q {at = at} {a = a} eqf breq | sil P' | ret rQ =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | react vP τcP | ret rQ =
  evP (sVis eqP (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq))
□-vis-inv P Q {at = at} {a = a} eqf breq | sil P' | sil Q' =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | sil P' | react vQ τcQ =
  case mergeVis-elim ∅v vQ at a (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
    (inj₁ (∅M , _))              → case ∅M of λ ()
    (inj₂ (inj₁ (_ , vQM)))      → evQ (sVis eqQ vQM)
    (inj₂ (inj₂ (_ , _ , ∅P , _ , _))) → case ∅P of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | react vP τcP | sil Q' =
  case mergeVis-elim vP ∅v at a (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
    (inj₁ (vPM , _))             → evP (sVis eqP vPM)
    (inj₂ (inj₁ (_ , ∅M)))       → case ∅M of λ ()
    (inj₂ (inj₂ (_ , _ , _ , ∅Q , _))) → case ∅Q of λ ()
□-vis-inv P Q {at = at} {a = a} eqf breq | react vP τcP | react vQ τcQ =
  case mergeVis-elim vP vQ at a (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
    (inj₁ (vPM , _))                       → evP (sVis eqP vPM)
    (inj₂ (inj₁ (_ , vQM)))                → evQ (sVis eqQ vQM)
    (inj₂ (inj₂ (P₁ , Q₁ , vPP₁ , vQQ₁ , m≡))) →
      case m≡ of λ { refl → evPQ (sVis eqP vPP₁) (sVis eqQ vQQ₁) }

□-ev-elim : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R} {e : Event√ R}
          → (P □ Q) ─[ ev e ]─► M → □evR P Q M e
□-ev-elim P Q (sRet eqf)                     = evP (sRet (□-force-ret-inv {P = P} {Q = Q} eqf))
□-ev-elim P Q (sVis {at = at} {a = a} eqf breq) = □-vis-inv P Q eqf breq

-------------------------------------------------------------------------------------
-- □-trace-elim : traces (P □ Q) s → traces P s ⊎ traces Q s, then □-mono.
-------------------------------------------------------------------------------------

□-trace-elim : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {R' : PTree E (ExtI E) R}
             → (P □ Q) ⟹⟨ s ⟩ R' → traces P s ⊎ traces Q s
□-trace-elim P Q ⟹-refl = inj₁ (P , ⟹-refl)
□-trace-elim P Q (⟹-τ step rest) with □-τ-elim P Q step
... | cP refl = inj₁ (_ , rest)
... | cQ refl = inj₂ (_ , rest)
... | sPQ P' Pτ refl with ▷-trace-elim P' Q rest
...   | inj₁ (Rt , tP') = inj₁ (Rt , ⟹-τ Pτ tP')
...   | inj₂ tQ         = inj₂ tQ
□-trace-elim P Q (⟹-τ step rest) | sQP Q' Qτ refl with ▷-trace-elim Q' P rest
...   | inj₁ (Rt , tQ') = inj₂ (Rt , ⟹-τ Qτ tQ')
...   | inj₂ tP         = inj₁ tP
□-trace-elim P Q (⟹-τ step rest) | chP P' Pτ refl with □-trace-elim P' Q rest
...   | inj₁ (Rt , tP') = inj₁ (Rt , ⟹-τ Pτ tP')
...   | inj₂ tQ         = inj₂ tQ
□-trace-elim P Q (⟹-τ step rest) | chQ Q' Qτ refl with □-trace-elim P Q' rest
...   | inj₁ tP         = inj₁ tP
...   | inj₂ (Rt , tQ') = inj₂ (Rt , ⟹-τ Qτ tQ')
□-trace-elim P Q (⟹-ev step rest) with □-ev-elim P Q step
... | evP Pev = inj₁ (_ , ⟹-ev Pev rest)
... | evQ Qev = inj₂ (_ , ⟹-ev Qev rest)
... | evPQ {P₁ = P₁} {Q₁ = Q₁} Pev Qev with ⊓-trace-elim P₁ Q₁ (_ , rest)
...   | inj₁ (Rt , tP₁) = inj₁ (Rt , ⟹-ev Pev tP₁)
...   | inj₂ (Rt , tQ₁) = inj₂ (Rt , ⟹-ev Qev tQ₁)

-- external choice is ⊑ᵀ-monotone (elim P′ □ Q′ into a side, then re-introduce into P □ Q)
□-mono-⊑ᵀ : ⦃ _ : DecEq R ⦄ {P Q P′ Q′ : PTree E (ExtI E) R}
          → P ⊑T P′ → Q ⊑T Q′ → (P □ Q) ⊑T (P′ □ Q′)
□-mono-⊑ᵀ {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} p⊑ q⊑ s (_ , bs) with □-trace-elim P′ Q′ bs
... | inj₁ tP′ = ⊑ᵀ-□-L P Q s (p⊑ s tP′)
... | inj₂ tQ′ = ⊑ᵀ-□-R P Q s (q⊑ s tQ′)

-------------------------------------------------------------------------------------
-- □ is trace-equivalent to ⊓ (both inclusions in hand: intros give ⊇, elims give ⊆)
-------------------------------------------------------------------------------------

-- traces (P ⊓ Q) ⊆ traces (P □ Q)
□⊑⊓ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ⊑T (P ⊓ Q)
□⊑⊓ P Q s tr with ⊓-trace-elim P Q tr
... | inj₁ tP = ⊑ᵀ-□-L P Q s tP
... | inj₂ tQ = ⊑ᵀ-□-R P Q s tQ

-- traces (P □ Q) ⊆ traces (P ⊓ Q)
⊓⊑□ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑T (P □ Q)
⊓⊑□ P Q s (_ , bs) with □-trace-elim P Q bs
... | inj₁ tP = ⊑ᵀ-⊓-L P Q s tP
... | inj₂ tQ = ⊑ᵀ-⊓-R P Q s tQ

-- trace equivalence (mutual refinement)
□≈T⊓ : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → ((P □ Q) ⊑T (P ⊓ Q)) × ((P ⊓ Q) ⊑T (P □ Q))
□≈T⊓ P Q = □⊑⊓ P Q , ⊓⊑□ P Q

-------------------------------------------------------------------------------------
-- ▷ is ⊑ᵀ-monotone in its RIGHT argument.
-- (NOT in the left, and ⊑ᵀ-▷-R is FALSE: a terminating P discards the timeout, so
--  `Skip ▷ Q = Skip`.  But the timeout only fires when P is non-ret, and there Q's
--  traces are reachable — so right-monotonicity holds.)
-------------------------------------------------------------------------------------

-- any τ-step out of P ▷ Q witnesses that P has not terminated (force P ≠ ret)
▷-τ-nonret : (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
           → (P ▷ Q) ─[ τ ]─► M
           → Σ[ nP ∈ NodeKind E (ExtI E) R ] (PTree.force P ≡ nP) × NonRet nP
▷-τ-nonret P Q step with PTree.force P in eqP
... | ret r       = ⊥-elim (ret-no-τ (force-▷-ret {P = P} {Q = Q} eqP) step)
... | sil P'      = sil P'      , refl , tt
... | react vP τcP = react vP τcP , refl , tt

-- the always-available timeout, given P is non-ret
▷-timeout : (P Q : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
          → PTree.force P ≡ nP → NonRet nP → (P ▷ Q) ─[ τ ]─► Q
▷-timeout P Q {sil P'}      eqP _ =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift fzero , lift fzero} (force-▷-sil {P = P} {Q = Q} eqP) refl
▷-timeout P Q {react vP τcP} eqP _ =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift fzero , lift fzero} (force-▷-react {P = P} {Q = Q} eqP) refl

▷-mono-R-aux : (P Q Q′ : PTree E (ExtI E) R) → Q ⊑T Q′
             → {s : List (Event√ R)} {R' : PTree E (ExtI E) R}
             → (P ▷ Q′) ⟹⟨ s ⟩ R' → traces (P ▷ Q) s
▷-mono-R-aux P Q Q′ q⊑ ⟹-refl = (P ▷ Q) , ⟹-refl
▷-mono-R-aux P Q Q′ q⊑ (⟹-τ step rest) with ▷-τ-elim P Q′ step
... | inj₁ refl = case ▷-τ-nonret P Q′ step of λ where
    (nP , eqP , ntP) → case q⊑ _ (_ , rest) of λ where
      (RQ , qbs) → RQ , ⟹-τ (▷-timeout P Q eqP ntP) qbs
... | inj₂ (P'' , Pτ , refl) = case ▷-mono-R-aux P'' Q Q′ q⊑ rest of λ where
    (R'' , rec) → R'' , ⟹-τ (▷-τ-L {Q = Q} Pτ) rec
▷-mono-R-aux P Q Q′ q⊑ (⟹-ev step rest) =
  _ , ⟹-ev (▷-ev-L {Q = Q} (▷-ev-elim P Q′ step)) rest

▷-mono-R : (P Q Q′ : PTree E (ExtI E) R) → Q ⊑T Q′ → (P ▷ Q) ⊑T (P ▷ Q′)
▷-mono-R P Q Q′ q⊑ s (_ , bs) = ▷-mono-R-aux P Q Q′ q⊑ bs
