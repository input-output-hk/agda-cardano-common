{-# OPTIONS --guardedness #-}

-- SPIKE: trace INTRODUCTION (Layer 2, intro half) and MONOTONICITY (Layer 3) for the
-- generalised parallel Par.
--   Par-trace-intro : from P-trace, Q-trace and a ParInter witness, build the composite
--                     trace of Par P Q (the converse of Par-trace-elim).
--   Par-mono-⊑ᵀ     : P₁ ⊑T P₂ → Q₁ ⊑T Q₂ → (Par P₁ Q₁) ⊑T (Par P₂ Q₂)
--                     (de-interleave P₂Q₂'s trace, transport each side, re-interleave).
-- The solo intros account for the both-offer-outside-`A` overlap (the event reaches the inline
-- ⊓-shaped node, then a commit-τ picks the side); the joint √ uses ret|ret ⇒ √(merge r₁ r₂).
-- No postulates, no NON_TERMINATING.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsParallelMono {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open EventSet
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_; ⊑T-refl)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟
  using (Mg; fPar-er; fPar-re; fPar-nn; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟ using (fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- the overlap-node commits (mirror ⊓-stepL / ⊓-stepR)
-------------------------------------------------------------------------------------

brBoth-commitL : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                   (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
               → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
                 ─[ τ ]─► (Par A merge P₁ Q)
brBoth-commitL A merge P Q P₁ Q₁ = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero} refl refl

brBoth-commitR : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                   (P₁ : PTree E (ExtI E) R₁) (Q₁ : PTree E (ExtI E) R₂)
               → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
                 ─[ τ ]─► (Par A merge P Q₁)
brBoth-commitR A merge P Q P₁ Q₁ = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

-------------------------------------------------------------------------------------
-- branch-equation INTRO lemmas for the visible continuations
-------------------------------------------------------------------------------------

par-hVisL-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                 {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁))}
                 (Q : PTree E (ExtI E) R₂) {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R₁}
             → ¬ A .mem at a → vP at a ≡ just P₁
             → par-hVisL A merge vP Q at a ≡ just (Par A merge P₁ Q)
par-hVisL-eq A merge {vP = vP} Q {at = at} {a = a} ¬cs veq with A .dec at a
... | yes p  = ⊥-elim (¬cs p)
... | no  _  with vP at a
...   | just _  = case veq of λ { refl → refl }
...   | nothing = case veq of λ ()

par-hVisR-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁)
                 {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂))}
                 {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R₂}
             → ¬ A .mem at a → vQ at a ≡ just Q₁
             → par-hVisR A merge P vQ at a ≡ just (Par A merge P Q₁)
par-hVisR-eq A merge P {vQ = vQ} {at = at} {a = a} ¬cs veq with A .dec at a
... | yes p  = ⊥-elim (¬cs p)
... | no  _  with vQ at a
...   | just _  = case veq of λ { refl → refl }
...   | nothing = case veq of λ ()

par-pVis-soloL-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                      (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                      (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                      {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R₁}
                  → ¬ A .mem at a → viewV nP at a ≡ just P₁ → viewV nQ at a ≡ nothing
                  → par-pVis A merge nP nQ P Q at a ≡ just (Par A merge P₁ Q)
par-pVis-soloL-eq A merge nP nQ P Q {at = at} {a = a} ¬cs vPeq vQeq
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes p  | _       | _       = ⊥-elim (¬cs p)
... | no  _  | just _  | nothing = case vPeq of λ { refl → refl }
... | no  _  | just _  | just _  = case vQeq of λ ()
... | no  _  | nothing | _       = case vPeq of λ ()

par-pVis-soloR-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                      (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                      (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                      {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R₂}
                  → ¬ A .mem at a → viewV nP at a ≡ nothing → viewV nQ at a ≡ just Q₁
                  → par-pVis A merge nP nQ P Q at a ≡ just (Par A merge P Q₁)
par-pVis-soloR-eq A merge nP nQ P Q {at = at} {a = a} ¬cs vPeq vQeq
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes p  | _       | _       = ⊥-elim (¬cs p)
... | no  _  | nothing | just _  = case vQeq of λ { refl → refl }
... | no  _  | just _  | _       = case vPeq of λ ()
... | no  _  | nothing | nothing = case vQeq of λ ()

par-pVis-both-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {at : AnyTypes E} {a : proj₁ at}
                     {P₁ : PTree E (ExtI E) R₁} {Q₁ : PTree E (ExtI E) R₂}
                 → ¬ A .mem at a → viewV nP at a ≡ just P₁ → viewV nQ at a ≡ just Q₁
                 → par-pVis A merge nP nQ P Q at a
                   ≡ just (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P₁ Q₁)))
par-pVis-both-eq A merge nP nQ P Q {at = at} {a = a} ¬cs vPeq vQeq
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes p  | _       | _       = ⊥-elim (¬cs p)
... | no  _  | just _  | just _  = case vPeq of λ { refl → case vQeq of λ { refl → refl } }
... | no  _  | just _  | nothing = case vQeq of λ ()
... | no  _  | nothing | _       = case vPeq of λ ()

-------------------------------------------------------------------------------------
-- solo-event reach: prepend a single outside-`A` event (possibly via the overlap + commit)
-------------------------------------------------------------------------------------

Par-soloL-reach : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {P₁ : PTree E (ExtI E) R₁}
                    {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                → ¬ A .mem (X , e) a
                → P ─[ ev (evl (evLabel X e a)) ]─► P₁
                → (Par A merge P₁ Q) ⟹⟨ s ⟩ Rt
                → (Par A merge P Q) ⟹⟨ evl (evLabel X e a) ∷ s ⟩ Rt
Par-soloL-reach A merge P Q {X = X} {e = e} {a = a} {P₁ = P₁} ¬cs (sVis {v = vP} {τc = τcP} eqP veqP) cont
  with PTree.force Q in eqQ
... | ret r₂ = ⟹-ev (sVis (fPar-er A merge eqP eqQ)
                          (par-hVisL-eq A merge {vP = vP} Q {at = X , e} {a = a} ¬cs veqP)) cont
... | sil Q' = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                          (par-pVis-soloL-eq A merge (react vP τcP) (sil Q') P Q
                                             {at = X , e} {a = a} ¬cs veqP refl)) cont
... | react vQ τcQ with vQ (X , e) a in vqeq
...   | nothing = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                            (par-pVis-soloL-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                               {at = X , e} {a = a} ¬cs veqP vqeq)) cont
...   | just Q₁ = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                            (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                              {at = X , e} {a = a} ¬cs veqP vqeq))
                        (⟹-τ (brBoth-commitL A merge P Q P₁ Q₁) cont)

Par-soloR-reach : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {Q₁ : PTree E (ExtI E) R₂}
                    {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                → ¬ A .mem (X , e) a
                → Q ─[ ev (evl (evLabel X e a)) ]─► Q₁
                → (Par A merge P Q₁) ⟹⟨ s ⟩ Rt
                → (Par A merge P Q) ⟹⟨ evl (evLabel X e a) ∷ s ⟩ Rt
Par-soloR-reach A merge P Q {X = X} {e = e} {a = a} {Q₁ = Q₁} ¬cs (sVis {v = vQ} {τc = τcQ} eqQ veqQ) cont
  with PTree.force P in eqP
... | ret r₁ = ⟹-ev (sVis (fPar-re A merge eqP eqQ)
                          (par-hVisR-eq A merge P {vQ = vQ} {at = X , e} {a = a} ¬cs veqQ)) cont
... | sil P' = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                          (par-pVis-soloR-eq A merge (sil P') (react vQ τcQ) P Q
                                             {at = X , e} {a = a} ¬cs refl veqQ)) cont
... | react vP τcP with vP (X , e) a in vpeq
...   | nothing = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                            (par-pVis-soloR-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                               {at = X , e} {a = a} ¬cs vpeq veqQ)) cont
...   | just P₁ = ⟹-ev (sVis (fPar-nn A merge eqP eqQ tt₀ tt₀)
                            (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                              {at = X , e} {a = a} ¬cs vpeq veqQ))
                        (⟹-τ (brBoth-commitR A merge P Q P₁ Q₁) cont)

-------------------------------------------------------------------------------------
-- Par-trace-intro : re-interleave a P-trace and a Q-trace per a ParInter witness
-------------------------------------------------------------------------------------

Par-trace-intro : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    {P' : PTree E (ExtI E) R₁} {Q' : PTree E (ExtI E) R₂}
                    {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                → P ⟹⟨ sP ⟩ P' → Q ⟹⟨ sQ ⟩ Q' → ParInter A merge sP sQ s
                → traces (Par A merge P Q) s
Par-trace-intro A merge P Q (⟹-τ Pτ restP) Qbs PI =
  case Par-trace-intro A merge _ Q restP Qbs PI of λ where
    (Rt , bs) → Rt , ⟹-τ (Par-τ-L A merge P Q Pτ) bs
Par-trace-intro A merge P Q Pbs (⟹-τ Qτ restQ) PI =
  case Par-trace-intro A merge P _ Pbs restQ PI of λ where
    (Rt , bs) → Rt , ⟹-τ (Par-τ-R A merge P Q Qτ) bs
Par-trace-intro A merge P Q ⟹-refl ⟹-refl pnil = Par A merge P Q , ⟹-refl
Par-trace-intro A merge P Q (⟹-ev Pev restP) (⟹-ev Qev restQ) (psync csat PI) =
  case Par-trace-intro A merge _ _ restP restQ PI of λ where
    (Rt , bs) → Rt , ⟹-ev (Par-sync A merge P Q csat Pev Qev) bs
Par-trace-intro A merge P Q (⟹-ev Pev restP) Qbs (psoloL ¬cs PI) =
  case Par-trace-intro A merge _ Q restP Qbs PI of λ where
    (Rt , bs) → Rt , Par-soloL-reach A merge P Q ¬cs Pev bs
Par-trace-intro A merge P Q Pbs (⟹-ev Qev restQ) (psoloR ¬cs PI) =
  case Par-trace-intro A merge P _ Pbs restQ PI of λ where
    (Rt , bs) → Rt , Par-soloR-reach A merge P Q ¬cs Qev bs
Par-trace-intro A merge P Q (⟹-ev (sRet eqPr) restP) (⟹-ev (sRet eqQr) restQ) p√ =
  deadlock , ⟹-ev (sRet (fPar-rr A merge eqPr eqQr)) ⟹-refl

-------------------------------------------------------------------------------------
-- Layer 3: Par is ⊑ᵀ-monotone (in BOTH arguments simultaneously)
-------------------------------------------------------------------------------------

Par-mono-⊑ᵀ : (A : EventSet) (merge : Mg R₁ R₂ R)
                {P₁ P₂ : PTree E (ExtI E) R₁} {Q₁ Q₂ : PTree E (ExtI E) R₂}
            → P₁ ⊑T P₂ → Q₁ ⊑T Q₂
            → (Par A merge P₁ Q₁) ⊑T (Par A merge P₂ Q₂)
Par-mono-⊑ᵀ A merge {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} p⊑ q⊑ s (_ , bs)
  with Par-trace-elim A merge P₂ Q₂ bs
... | sP , sQ , P₂' , Q₂' , rP₂ , rQ₂ , inter
  with p⊑ sP (P₂' , rP₂) | q⊑ sQ (Q₂' , rQ₂)
... | P₁' , rP₁ | Q₁' , rQ₁ = Par-trace-intro A merge P₁ Q₁ rP₁ rQ₁ inter

-------------------------------------------------------------------------------------
-- CSP parallel sugar and interleaving folds are ⊑ᵀ-monotone
-------------------------------------------------------------------------------------

-- CSP alphabetised parallel is ⊑T-monotone in both operands: `_∥⇘_⇙_` is `Par⊤`,
-- so this is `Par-mono-⊑ᵀ` at the ⊤-merge
∥-mono-⊑T : ∀ {ℓr} (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
          → P₁ ⊑T P₂ → Q₁ ⊑T Q₂ → (P₁ ∥⇘ A ⇙ Q₁) ⊑T (P₂ ∥⇘ A ⇙ Q₂)
∥-mono-⊑T A = Par-mono-⊑ᵀ A (λ _ _ → tt)

-- interleaving is ⊑T-monotone in both operands: `_⦀_` is `Par ∅ES`
⦀-mono-⊑ᵀ : ∀ {ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) (⊤ {ℓr})}
          → P₁ ⊑T P₂ → Q₁ ⊑T Q₂ → (P₁ ⦀ Q₁) ⊑T (P₂ ⦀ Q₂)
⦀-mono-⊑ᵀ = Par-mono-⊑ᵀ ∅ES (λ _ _ → tt)

-- `⦀Fin` is ⊑T-monotone in its family, pointwise and unconditionally; the base case
-- is `Skip`, which refines itself
⦀Fin-mono-⊑ᵀ : ∀ {ℓr} {n : ℕ} {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
             → (∀ i → f i ⊑T g i) → ⦀Fin n f ⊑T ⦀Fin n g
⦀Fin-mono-⊑ᵀ {n = zero}  h = ⊑T-refl Skip
⦀Fin-mono-⊑ᵀ {n = suc n} h = ⦀-mono-⊑ᵀ (h fzero) (⦀Fin-mono-⊑ᵀ (λ i → h (fsuc i)))

-- `⦀Fin⁺` is ⊑T-monotone in its family; unlike `⦀Fin-mono-⊑ᵀ` the base case is the
-- leaf itself (`⦀Fin⁺ zero f = f fzero`), not `Skip`
⦀Fin⁺-mono-⊑ᵀ : ∀ {ℓr} {n : ℕ} {f g : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
              → (∀ i → f i ⊑T g i) → ⦀Fin⁺ n f ⊑T ⦀Fin⁺ n g
⦀Fin⁺-mono-⊑ᵀ {n = zero}  h = h fzero
⦀Fin⁺-mono-⊑ᵀ {n = suc n} h = ⦀-mono-⊑ᵀ (h fzero) (⦀Fin⁺-mono-⊑ᵀ (λ i → h (fsuc i)))

-- `⦀⋆` is ⊑T-monotone in its list of operands (base `⦀⋆ [] = Skip`)
⦀⋆-mono-⊑ᵀ : ∀ {ℓr} {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
           → Pointwise _⊑T_ Ps Qs → ⦀⋆ Ps ⊑T ⦀⋆ Qs
⦀⋆-mono-⊑ᵀ []ᵖ       = ⊑T-refl Skip
⦀⋆-mono-⊑ᵀ (p ∷ᵖ ps) = ⦀-mono-⊑ᵀ p (⦀⋆-mono-⊑ᵀ ps)

-- `∥⁺` is ⊑T-monotone in head + tail list (non-empty fold: `∥⁺ A P [] = P`)
∥⁺-mono-⊑ᵀ : ∀ {ℓr} (A : EventSet) {P₁ P₂ : PTree E (ExtI E) (⊤ {ℓr})}
               {Ps Qs : List (PTree E (ExtI E) (⊤ {ℓr}))}
           → P₁ ⊑T P₂ → Pointwise _⊑T_ Ps Qs → ∥⁺ A P₁ Ps ⊑T ∥⁺ A P₂ Qs
∥⁺-mono-⊑ᵀ A hP []ᵖ       = hP
∥⁺-mono-⊑ᵀ A hP (q ∷ᵖ qs) = ∥-mono-⊑T A hP (∥⁺-mono-⊑ᵀ A q qs)

-- `∥Fin` is ⊑T-monotone in its `Fin (suc n)`-indexed family (non-empty fold)
∥Fin-mono-⊑ᵀ : ∀ {ℓr} (A : EventSet) {n : ℕ} {f g : Fin (suc n) → PTree E (ExtI E) (⊤ {ℓr})}
             → (∀ i → f i ⊑T g i) → ∥Fin A n f ⊑T ∥Fin A n g
∥Fin-mono-⊑ᵀ A {n = zero}  h = h fzero
∥Fin-mono-⊑ᵀ A {n = suc n} h =
  ∥-mono-⊑T A (h fzero) (∥Fin-mono-⊑ᵀ A (λ i → h (fsuc i)))
