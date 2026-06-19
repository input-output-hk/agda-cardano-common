{-# OPTIONS --guardedness #-}

-- SPIKE: external-choice trace refinement  (P □ Q) ⊑T P  on the pure-react layer.
-- Every trace of P is a trace of P □ Q.  The proof recurses on the big-step
-- P ⟹⟨ s ⟩ P′ (hence total — no NON_TERMINATING), mirroring each move of P:
--   * P's τ          → P □ Q does the matching τ (→ P₁ □ Q, or → P₁ ▷ Q if Q done);
--   * P's event e    → P □ Q offers e (→ P₁, or → P₁ ⊓ Q₁ then τ if Q also offers e);
--   * P's √ (P done) → P □ Q does √ directly (Q done, same value) or τ-commits to P.
-- The event-overlap case lands on an internal choice P₁ ⊓ Q₁ with a clean τ-step
-- (⊓-stepL), so NO postulate is needed (unlike the original ndbr|ndbr handling).

open import Level using (Level; Lift; lift)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsExtChoice {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators  E-≟
open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.Failures  {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.Laws      E-≟ using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.Traces.TraceLaws E-≟ using (⊑ᵀ-▷-L)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- a node is non-terminal (covers the `nP | nQ` merge clause of □)
NonRet : NodeKind E (ExtI E) R → Set
NonRet (ret _)    = ⊥
NonRet (sil _)    = ⊤
NonRet (react _ _) = ⊤

-------------------------------------------------------------------------------------
-- force-equation lemmas: their goal mentions force (P □ Q), so re-doing the
-- `with force P | force Q` lets _□_ reduce (cf. the original force-□-* helpers).
-------------------------------------------------------------------------------------

-- both terminate with the same value ⇒ ret r
fL-A : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r : R}
     → PTree.force P ≡ ret r → PTree.force Q ≡ ret r → PTree.force (P □ Q) ≡ ret r
fL-A {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = case eqP of λ { refl → refl }
...   | no  neq  = case eqP of λ { refl → case eqQ of λ { refl → ⊥-elim (neq refl) } }
fL-A eqP eqQ | ret _    | sil _    = case eqQ of λ ()
fL-A eqP eqQ | ret _    | react _ _ = case eqQ of λ ()
fL-A eqP eqQ | sil _    | _        = case eqP of λ ()
fL-A eqP eqQ | react _ _ | _        = case eqP of λ ()

-- both terminate with different values ⇒ P ⊓ Q shape (react ∅v (br2 P Q))
fL-B : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r r' : R}
     → PTree.force P ≡ ret r → PTree.force Q ≡ ret r' → ¬ (r ≡ r')
     → PTree.force (P □ Q) ≡ react ∅v (br2 P Q)
fL-B {P = P} {Q = Q} eqP eqQ ¬eq with PTree.force P | PTree.force Q
... | ret rP | ret rQ with rP ≟ rQ
...   | yes refl = case eqP of λ { refl → case eqQ of λ { refl → ⊥-elim (¬eq refl) } }
...   | no  _    = refl
fL-B eqP eqQ ¬eq | ret _    | sil _    = case eqQ of λ ()
fL-B eqP eqQ ¬eq | ret _    | react _ _ = case eqQ of λ ()
fL-B eqP eqQ ¬eq | sil _    | _        = case eqP of λ ()
fL-B eqP eqQ ¬eq | react _ _ | _        = case eqP of λ ()

-- P done, Q silent
fL-C : ⦃ _ : DecEq R ⦄ {P Q Q' : PTree E (ExtI E) R} {r : R}
     → PTree.force P ≡ ret r → PTree.force Q ≡ sil Q'
     → PTree.force (P □ Q) ≡ react ∅v (□-slide-RQ P (sil Q'))
fL-C {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret _    | sil _    = case eqQ of λ { refl → refl }
... | ret _    | ret _    = case eqQ of λ ()
... | ret _    | react _ _ = case eqQ of λ ()
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- P done, Q offering
fL-D : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r : R}
       {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
       {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
     → PTree.force P ≡ ret r → PTree.force Q ≡ react vQ τcQ
     → PTree.force (P □ Q) ≡ react vQ (□-slide-RQ P (react vQ τcQ))
fL-D {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret _    | react _ _ = case eqQ of λ { refl → refl }
... | ret _    | ret _    = case eqQ of λ ()
... | ret _    | sil _    = case eqQ of λ ()
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- P silent, Q done
fL-E : ⦃ _ : DecEq R ⦄ {P P' Q : PTree E (ExtI E) R} {r : R}
     → PTree.force P ≡ sil P' → PTree.force Q ≡ ret r
     → PTree.force (P □ Q) ≡ react ∅v (□-slide-PR (sil P') Q)
fL-E {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | sil _    | ret _    = case eqP of λ { refl → refl }
... | sil _    | sil _    = case eqQ of λ ()
... | sil _    | react _ _ = case eqQ of λ ()
... | ret _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- P offering, Q done
fL-F : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {r : R}
       {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
       {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
     → PTree.force P ≡ react vP τcP → PTree.force Q ≡ ret r
     → PTree.force (P □ Q) ≡ react vP (□-slide-PR (react vP τcP) Q)
fL-F {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | react _ _ | ret _    = case eqP of λ { refl → refl }
... | react _ _ | sil _    = case eqQ of λ ()
... | react _ _ | react _ _ = case eqQ of λ ()
... | ret _    | _        = case eqP of λ ()
... | sil _    | _        = case eqP of λ ()

-- neither terminates ⇒ merged offers + merged τ
fL-G : ⦃ _ : DecEq R ⦄ {P Q : PTree E (ExtI E) R} {nP nQ : NodeKind E (ExtI E) R}
     → PTree.force P ≡ nP → PTree.force Q ≡ nQ → NonRet nP → NonRet nQ
     → PTree.force (P □ Q) ≡ react (mergeVis (viewV nP) (viewV nQ)) (□-mt nP nQ P Q)
fL-G {P = P} {Q = Q} eqP eqQ ntP ntQ with PTree.force P | PTree.force Q
... | sil _    | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | sil _    | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _    | _        = case eqP of λ { refl → ⊥-elim ntP }
... | sil _    | ret _    = case eqQ of λ { refl → ⊥-elim ntQ }
... | react _ _ | ret _    = case eqQ of λ { refl → ⊥-elim ntQ }

-------------------------------------------------------------------------------------
-- branch-equation lemmas: each continuation is top-level, so `with`-matching the
-- same scrutinee here makes it reduce.
-------------------------------------------------------------------------------------

-- □-mt tag0 = P's own τ  (→ P₁ □ Q)
□-mt-tag0-eq : ⦃ _ : DecEq R ⦄ {nP nQ : NodeKind E (ExtI E) R} {P Q : PTree E (ExtI E) R}
                 {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {P₁ : PTree E (ExtI E) R}
             → viewT nP iₚ aₚ ≡ just P₁
             → □-mt nP nQ P Q ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                              (lift fzero , aₚ)
               ≡ just (P₁ □ Q)
□-mt-tag0-eq {nP = nP} {iₚ = iₚ} {aₚ = aₚ} ve with viewT nP (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- □-slide-PR tag1 = the live operand's own τ  (→ P₁ ▷ Q)
□-slide-PR-tag1-eq : {nP : NodeKind E (ExtI E) R} {Q : PTree E (ExtI E) R}
                       {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {P₁ : PTree E (ExtI E) R}
                   → viewT nP iₚ aₚ ≡ just P₁
                   → □-slide-PR nP Q ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                                     (lift (fsuc fzero) , aₚ)
                     ≡ just (P₁ ▷ Q)
□-slide-PR-tag1-eq {nP = nP} {iₚ = iₚ} {aₚ = aₚ} ve with viewT nP (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- merged offers: P offers, Q does not  (→ P₁)
mergeVis-L-eq : {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
              → vP at a ≡ just P₁ → vQ at a ≡ nothing → mergeVis vP vQ at a ≡ just P₁
mergeVis-L-eq {vP = vP} {vQ = vQ} {at = at} {a = a} eqP eqQ with vP at a | vQ at a
... | just _  | nothing = case eqP of λ { refl → refl }
... | just _  | just _  = case eqQ of λ ()
... | nothing | _       = case eqP of λ ()

-- merged offers: both P and Q offer  (→ P₁ ⊓ Q₁)
mergeVis-LQ-eq : {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 {at : AnyTypes E} {a : proj₁ at} {P₁ Q₁ : PTree E (ExtI E) R}
               → vP at a ≡ just P₁ → vQ at a ≡ just Q₁ → mergeVis vP vQ at a ≡ just (P₁ ⊓ Q₁)
mergeVis-LQ-eq {vP = vP} {vQ = vQ} {at = at} {a = a} eqP eqQ with vP at a | vQ at a
... | just _  | just _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | just _  | nothing = case eqQ of λ ()
... | nothing | _       = case eqP of λ ()

-------------------------------------------------------------------------------------
-- transition lemmas: P's τ-move, mirrored by P □ Q
-------------------------------------------------------------------------------------

-- Q not terminated ⇒ the merged-τ branch fires (→ P₁ □ Q)
□-τ-tochoice : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P₁ : PTree E (ExtI E) R}
                 {nQ : NodeKind E (ExtI E) R}
             → P ─[ τ ]─► P₁ → PTree.force Q ≡ nQ → NonRet nQ
             → (P □ Q) ─[ τ ]─► (P₁ □ Q)
□-τ-tochoice P Q {P₁ = P₁} {nQ = nQ} (sSil eqP) eqQ ntQ =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift fzero , lift fzero}
       (fL-G {P = P} {Q = Q} eqP eqQ tt ntQ)
       (□-mt-tag0-eq {nP = sil P₁} {nQ = nQ} {P = P} {Q = Q}
                     {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} {P₁ = P₁} refl)
□-τ-tochoice P Q {P₁ = P₁} {nQ = nQ} (sTau {v = vP} {τc = τcP} {i = iₚ} {a = aₚ} eqP brP) eqQ ntQ =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
       {a = lift fzero , aₚ}
       (fL-G {P = P} {Q = Q} eqP eqQ tt ntQ)
       (□-mt-tag0-eq {nP = react vP τcP} {nQ = nQ} {P = P} {Q = Q}
                     {iₚ = iₚ} {aₚ = aₚ} {P₁ = P₁} brP)

-- Q terminated ⇒ the slide's tag1 fires (→ P₁ ▷ Q)
□-τ-toslide : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P₁ : PTree E (ExtI E) R} {r : R}
            → P ─[ τ ]─► P₁ → PTree.force Q ≡ ret r
            → (P □ Q) ─[ τ ]─► (P₁ ▷ Q)
□-τ-toslide P Q {P₁ = P₁} (sSil eqP) eqQ =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift (fsuc fzero) , lift fzero}
       (fL-E {P = P} {Q = Q} eqP eqQ)
       (□-slide-PR-tag1-eq {nP = sil P₁} {Q = Q}
                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} {P₁ = P₁} refl)
□-τ-toslide P Q {P₁ = P₁} (sTau {v = vP} {τc = τcP} {i = iₚ} {a = aₚ} eqP brP) eqQ =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
       {a = lift (fsuc fzero) , aₚ}
       (fL-F {P = P} {Q = Q} eqP eqQ)
       (□-slide-PR-tag1-eq {nP = react vP τcP} {Q = Q}
                           {iₚ = iₚ} {aₚ = aₚ} {P₁ = P₁} brP)

-------------------------------------------------------------------------------------
-- P's event (visible or √), mirrored by P □ Q
-------------------------------------------------------------------------------------

□-ev-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {P₁ P′ : PTree E (ExtI E) R}
           {e : Event√ R} {s : List (Event√ R)}
       → P ─[ ev e ]─► P₁ → P₁ ⟹⟨ s ⟩ P′ → traces (P □ Q) (e ∷ s)
-- P offers a visible event
□-ev-L P Q {P₁ = P₁} (sVis {v = vP} {at = at} {a = a} eqP brP) rest with PTree.force Q in eqQ
... | ret _       = _ , ⟹-ev (sVis (fL-F {P = P} {Q = Q} eqP eqQ) brP) rest
... | sil _       = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                    (mergeVis-L-eq {vP = vP} {vQ = ∅v} brP refl)) rest
... | react vQ τcQ with vQ at a in eqVQ
...   | nothing = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                  (mergeVis-L-eq {vP = vP} {vQ = vQ} brP eqVQ)) rest
...   | just Q₁ = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                  (mergeVis-LQ-eq {vP = vP} {vQ = vQ} brP eqVQ))
                            (⟹-τ (⊓-stepL P₁ Q₁) rest)
-- P done ⇒ √; either P □ Q does √ directly, or it τ-commits to P then √
□-ev-L P Q (sRet {x = x} eqP) rest with PTree.force Q in eqQ
... | ret r'   with x ≟ r'
...   | yes refl = _ , ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQ)) rest
...   | no  ¬eq  = _ , ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
                                 (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl)
                            (⟹-ev (sRet eqP) rest)
□-ev-L P Q (sRet {x = x} eqP) rest | sil Q' =
  _ , ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                {a = lift fzero , lift fzero} (fL-C {P = P} {Q = Q} eqP eqQ) refl)
            (⟹-ev (sRet eqP) rest)
□-ev-L P Q (sRet {x = x} eqP) rest | react vQ τcQ =
  _ , ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                {a = lift fzero , lift fzero} (fL-D {P = P} {Q = Q} eqP eqQ) refl)
            (⟹-ev (sRet eqP) rest)

-------------------------------------------------------------------------------------
-- main theorem:  (P □ Q) ⊑T P  — every trace of P is a trace of P □ Q.
-- Recursion is on the big-step P ⟹⟨ s ⟩ P′, hence total (no NON_TERMINATING).
-------------------------------------------------------------------------------------

□-introL : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
           {s : List (Event√ R)} {P′ : PTree E (ExtI E) R}
         → P ⟹⟨ s ⟩ P′ → traces (P □ Q) s
□-introL P Q ⟹-refl = (P □ Q) , ⟹-refl
□-introL P Q (⟹-τ {q = P₁} step rest) with PTree.force Q in eqQ
... | ret _    with ⊑ᵀ-▷-L P₁ Q _ (_ , rest)
...   | R′ , rec = R′ , ⟹-τ (□-τ-toslide P Q step eqQ) rec
□-introL P Q (⟹-τ {q = P₁} step rest) | sil _    with □-introL P₁ Q rest
...   | R′ , rec = R′ , ⟹-τ (□-τ-tochoice P Q step eqQ tt) rec
□-introL P Q (⟹-τ {q = P₁} step rest) | react _ _ with □-introL P₁ Q rest
...   | R′ , rec = R′ , ⟹-τ (□-τ-tochoice P Q step eqQ tt) rec
□-introL P Q (⟹-ev step rest) = □-ev-L P Q step rest

⊑ᵀ-□-L : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ⊑T P
⊑ᵀ-□-L P Q s (_ , bs) = □-introL P Q bs

-------------------------------------------------------------------------------------
-- (P □ Q) ⊑T Q  — the mirror; Q's moves use tag1 of the continuations, the
-- event-overlap resolves to P₁ ⊓ Q₁ via ⊓-stepR.
-------------------------------------------------------------------------------------

-- □-mt tag1 = Q's own τ  (→ P □ Q₁)
□-mt-tag1-eq : ⦃ _ : DecEq R ⦄ {nP nQ : NodeKind E (ExtI E) R} {P Q : PTree E (ExtI E) R}
                 {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {Q₁ : PTree E (ExtI E) R}
             → viewT nQ iₚ aₚ ≡ just Q₁
             → □-mt nP nQ P Q ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                              (lift (fsuc fzero) , aₚ)
               ≡ just (P □ Q₁)
□-mt-tag1-eq {nQ = nQ} {iₚ = iₚ} {aₚ = aₚ} ve with viewT nQ (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- □-slide-RQ tag1 = Q's own τ (P terminated)  (→ Q₁ ▷ P)
□-slide-RQ-tag1-eq : {P : PTree E (ExtI E) R} {nQ : NodeKind E (ExtI E) R}
                       {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {Q₁ : PTree E (ExtI E) R}
                   → viewT nQ iₚ aₚ ≡ just Q₁
                   → □-slide-RQ P nQ ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                                     (lift (fsuc fzero) , aₚ)
                     ≡ just (Q₁ ▷ P)
□-slide-RQ-tag1-eq {nQ = nQ} {iₚ = iₚ} {aₚ = aₚ} ve with viewT nQ (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

-- merged offers: Q offers, P does not  (→ Q₁)
mergeVis-R-eq : {vP vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
              → vP at a ≡ nothing → vQ at a ≡ just Q₁ → mergeVis vP vQ at a ≡ just Q₁
mergeVis-R-eq {vP = vP} {vQ = vQ} {at = at} {a = a} eqP eqQ with vP at a | vQ at a
... | nothing | just _  = case eqQ of λ { refl → refl }
... | nothing | nothing = case eqQ of λ ()
... | just _  | _       = case eqP of λ ()

-- Q's τ, mirrored (P not terminated ⇒ merged-τ tag1 → P □ Q₁)
□-τ-tochoice-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ : PTree E (ExtI E) R}
                   {nP : NodeKind E (ExtI E) R}
               → Q ─[ τ ]─► Q₁ → PTree.force P ≡ nP → NonRet nP
               → (P □ Q) ─[ τ ]─► (P □ Q₁)
□-τ-tochoice-R P Q {Q₁ = Q₁} {nP = nP} (sSil eqQ) eqP ntP =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift (fsuc fzero) , lift fzero}
       (fL-G {P = P} {Q = Q} eqP eqQ ntP tt)
       (□-mt-tag1-eq {nP = nP} {nQ = sil Q₁} {P = P} {Q = Q}
                     {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} {Q₁ = Q₁} refl)
□-τ-tochoice-R P Q {Q₁ = Q₁} {nP = nP} (sTau {v = vQ} {τc = τcQ} {i = iₚ} {a = aₚ} eqQ brQ) eqP ntP =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
       {a = lift (fsuc fzero) , aₚ}
       (fL-G {P = P} {Q = Q} eqP eqQ ntP tt)
       (□-mt-tag1-eq {nP = nP} {nQ = react vQ τcQ} {P = P} {Q = Q}
                     {iₚ = iₚ} {aₚ = aₚ} {Q₁ = Q₁} brQ)

-- Q's τ, mirrored (P terminated ⇒ slide tag1 → Q₁ ▷ P)
□-τ-toslide-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ : PTree E (ExtI E) R} {r : R}
              → Q ─[ τ ]─► Q₁ → PTree.force P ≡ ret r
              → (P □ Q) ─[ τ ]─► (Q₁ ▷ P)
□-τ-toslide-R P Q {Q₁ = Q₁} (sSil eqQ) eqP =
  sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
       {a = lift (fsuc fzero) , lift fzero}
       (fL-C {P = P} {Q = Q} eqP eqQ)
       (□-slide-RQ-tag1-eq {P = P} {nQ = sil Q₁}
                           {iₚ = Lift ℓ (Fin 1) , fin} {aₚ = lift fzero} {Q₁ = Q₁} refl)
□-τ-toslide-R P Q {Q₁ = Q₁} (sTau {v = vQ} {τc = τcQ} {i = iₚ} {a = aₚ} eqQ brQ) eqP =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)}
       {a = lift (fsuc fzero) , aₚ}
       (fL-D {P = P} {Q = Q} eqP eqQ)
       (□-slide-RQ-tag1-eq {P = P} {nQ = react vQ τcQ}
                           {iₚ = iₚ} {aₚ = aₚ} {Q₁ = Q₁} brQ)

-- Q's event (visible or √), mirrored by P □ Q
□-ev-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) {Q₁ P′ : PTree E (ExtI E) R}
           {e : Event√ R} {s : List (Event√ R)}
       → Q ─[ ev e ]─► Q₁ → Q₁ ⟹⟨ s ⟩ P′ → traces (P □ Q) (e ∷ s)
□-ev-R P Q {Q₁ = Q₁} (sVis {v = vQ} {at = at} {a = a} eqQ brQ) rest with PTree.force P in eqP
... | ret _       = _ , ⟹-ev (sVis (fL-D {P = P} {Q = Q} eqP eqQ) brQ) rest
... | sil _       = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                    (mergeVis-R-eq {vP = ∅v} {vQ = vQ} refl brQ)) rest
... | react vP τcP with vP at a in eqVP
...   | nothing = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                  (mergeVis-R-eq {vP = vP} {vQ = vQ} eqVP brQ)) rest
...   | just P₁ = _ , ⟹-ev (sVis (fL-G {P = P} {Q = Q} eqP eqQ tt tt)
                                  (mergeVis-LQ-eq {vP = vP} {vQ = vQ} eqVP brQ))
                            (⟹-τ (⊓-stepR P₁ Q₁) rest)
□-ev-R P Q (sRet {x = x} eqQ) rest with PTree.force P in eqP
... | ret r'   with r' ≟ x
...   | yes refl = _ , ⟹-ev (sRet (fL-A {P = P} {Q = Q} eqP eqQ)) rest
...   | no  ¬eq  = _ , ⟹-τ (sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                                 (fL-B {P = P} {Q = Q} eqP eqQ ¬eq) refl)
                            (⟹-ev (sRet eqQ) rest)
□-ev-R P Q (sRet {x = x} eqQ) rest | sil P' =
  _ , ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                {a = lift fzero , lift fzero} (fL-E {P = P} {Q = Q} eqP eqQ) refl)
            (⟹-ev (sRet eqQ) rest)
□-ev-R P Q (sRet {x = x} eqQ) rest | react vP τcP =
  _ , ⟹-τ (sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                {a = lift fzero , lift fzero} (fL-F {P = P} {Q = Q} eqP eqQ) refl)
            (⟹-ev (sRet eqQ) rest)

□-introR : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R)
           {s : List (Event√ R)} {Q′ : PTree E (ExtI E) R}
         → Q ⟹⟨ s ⟩ Q′ → traces (P □ Q) s
□-introR P Q ⟹-refl = (P □ Q) , ⟹-refl
□-introR P Q (⟹-τ {q = Q₁} step rest) with PTree.force P in eqP
... | ret _    with ⊑ᵀ-▷-L Q₁ P _ (_ , rest)
...   | R′ , rec = R′ , ⟹-τ (□-τ-toslide-R P Q step eqP) rec
□-introR P Q (⟹-τ {q = Q₁} step rest) | sil _    with □-introR P Q₁ rest
...   | R′ , rec = R′ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt) rec
□-introR P Q (⟹-τ {q = Q₁} step rest) | react _ _ with □-introR P Q₁ rest
...   | R′ , rec = R′ , ⟹-τ (□-τ-tochoice-R P Q step eqP tt) rec
□-introR P Q (⟹-ev step rest) = □-ev-R P Q step rest

⊑ᵀ-□-R : ⦃ _ : DecEq R ⦄ (P Q : PTree E (ExtI E) R) → (P □ Q) ⊑T Q
⊑ᵀ-□-R P Q s (_ , bs) = □-introR P Q bs

