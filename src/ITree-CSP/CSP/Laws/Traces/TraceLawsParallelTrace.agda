{-# OPTIONS --guardedness #-}

-- SPIKE: trace-level de-interleaving for the GENERALISED parallel Par.
--   ParInter A merge sP sQ s : `s` is an `A`-synchronised interleaving of the P-trace
--     sP (over Event√ R₁) and the Q-trace sQ (over Event√ R₂); merge enters only at
--     the joint √ (p√).  This is Layer 0 of the Par-mono chain.
--   Par-trace-elim : every trace of Par P Q decomposes into a trace of P, a trace of Q,
--     and a ParInter witness (Layer 2, the elim half).
-- Built on the single-step inversions Par-τ-elim / Par-ev-elim (Layer 1).  No postulates:
-- the both-offer-outside-`A` overlap (`evBoth`, an inline ⊓-shaped node that is force-equal but
-- NOT definitionally equal to (Par P′ Q) ⊓ (Par P Q′)) is de-interleaved by the dedicated
-- Par-brBoth-trace-elim rather than via ⊓-trace-elim + funext.

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsParallelTrace {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open EventSet
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (react-τ-inv)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- Layer 0: the `A`-synchronised interleaving relation
-------------------------------------------------------------------------------------

data ParInter {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
              (A : EventSet) (merge : Mg R₁ R₂ R)
     : List (Event√ R₁) → List (Event√ R₂) → List (Event√ R)
     → Set (lsuc ℓ ⊔ ℓe ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓs) where
  pnil   : ParInter A merge [] [] []
  psync  : ∀ {X} {e : E X} {a : X} {sP sQ s} → A .mem (X , e) a
         → ParInter A merge sP sQ s
         → ParInter A merge (evl (evLabel X e a) ∷ sP)
                             (evl (evLabel X e a) ∷ sQ)
                             (evl (evLabel X e a) ∷ s)
  psoloL : ∀ {X} {e : E X} {a : X} {sP sQ s} → ¬ A .mem (X , e) a
         → ParInter A merge sP sQ s
         → ParInter A merge (evl (evLabel X e a) ∷ sP) sQ (evl (evLabel X e a) ∷ s)
  psoloR : ∀ {X} {e : E X} {a : X} {sP sQ s} → ¬ A .mem (X , e) a
         → ParInter A merge sP sQ s
         → ParInter A merge sP (evl (evLabel X e a) ∷ sQ) (evl (evLabel X e a) ∷ s)
  p√     : ∀ {r₁ : R₁} {r₂ : R₂}
         → ParInter A merge (√ r₁ ∷ []) (√ r₂ ∷ []) (√ (merge r₁ r₂) ∷ [])

-------------------------------------------------------------------------------------
-- inversions for the inline both-offer overlap node and for deadlock
-------------------------------------------------------------------------------------

-- the inline node's τ commits to (Par P′ Q) [tag0] or (Par P Q′) [tag1]
par-brBoth-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                    (P' : PTree E (ExtI E) R₁) (Q' : PTree E (ExtI E) R₂)
                    {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
                → par-brBoth A merge P Q P' Q' i a ≡ just M
                → (M ≡ Par A merge P' Q) ⊎ (M ≡ Par A merge P Q')
par-brBoth-elim A merge P Q P' Q' {_ , base _}   eq = case eq of λ ()
par-brBoth-elim A merge P Q P' Q' {_ , pair _ _} eq = case eq of λ ()
par-brBoth-elim A merge P Q P' Q' {_ , fin} {lift fzero}             eq = inj₁ (sym (just-injective eq))
par-brBoth-elim A merge P Q P' Q' {_ , fin} {lift (fsuc fzero)}      eq = inj₂ (sym (just-injective eq))
par-brBoth-elim A merge P Q P' Q' {_ , fin} {lift (fsuc (fsuc _))}   eq = case eq of λ ()

brBoth-τ-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  (P' : PTree E (ExtI E) R₁) (Q' : PTree E (ExtI E) R₂)
                  {M : PTree E (ExtI E) R}
              → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ─[ τ ]─► M
              → (M ≡ Par A merge P' Q) ⊎ (M ≡ Par A merge P Q')
brBoth-τ-elim A merge P Q P' Q' step =
  case react-τ-inv refl step of λ where
    (i , a , breq) → par-brBoth-elim A merge P Q P' Q' {i = i} {a = a} breq

brBoth-no-ev : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 (P' : PTree E (ExtI E) R₁) (Q' : PTree E (ExtI E) R₂)
                 {M : PTree E (ExtI E) R} {e : Event√ R}
             → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ─[ ev e ]─► M → ⊥
brBoth-no-ev A merge P Q P' Q' (sRet eqf)                = case eqf of λ ()
brBoth-no-ev A merge P Q P' Q' (sVis {at = at} {a = a} eqf breq) =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()

deadlock-no-τ : {M : PTree E (ExtI E) R} → deadlock ─[ τ ]─► M → ⊥
deadlock-no-τ (sSil eqf)              = case eqf of λ ()
deadlock-no-τ (sTau {i = i} {a = a} eqf breq) =
  case (subst (λ g → g i a ≡ just _) (sym (proj₂ (react-injective eqf))) breq) of λ ()

deadlock-no-ev : {M : PTree E (ExtI E) R} {e : Event√ R} → deadlock ─[ ev e ]─► M → ⊥
deadlock-no-ev (sRet eqf)             = case eqf of λ ()
deadlock-no-ev (sVis {at = at} {a = a} eqf breq) =
  case (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ ()

-------------------------------------------------------------------------------------
-- Layer 2 (elim half): Par-trace-elim, mutual with the overlap-node de-interleaver
-------------------------------------------------------------------------------------

mutual
  Par-trace-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                 → (Par A merge P Q) ⟹⟨ s ⟩ Rt
                 → Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
                   Σ[ P' ∈ PTree E (ExtI E) R₁ ] Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                     (P ⟹⟨ sP ⟩ P') × (Q ⟹⟨ sQ ⟩ Q') × ParInter A merge sP sQ s
  Par-trace-elim A merge P Q ⟹-refl =
    [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil
  Par-trace-elim A merge P Q (⟹-τ step rest) with Par-τ-elim A merge P Q step
  ... | τL P'' Pτ refl = case Par-trace-elim A merge P'' Q rest of λ where
          (sP , sQ , P' , Q' , rP , rQ , inter) →
            sP , sQ , P' , Q' , ⟹-τ Pτ rP , rQ , inter
  ... | τR Q'' Qτ refl = case Par-trace-elim A merge P Q'' rest of λ where
          (sP , sQ , P' , Q' , rP , rQ , inter) →
            sP , sQ , P' , Q' , rP , ⟹-τ Qτ rQ , inter
  Par-trace-elim A merge P Q (⟹-ev step rest) with Par-ev-elim A merge P Q step
  ... | evSync {X = X} {e = e} {a = a} csat Pev Qev =
          case Par-trace-elim A merge _ _ rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter) →
              (evl (evLabel X e a) ∷ sP) , (evl (evLabel X e a) ∷ sQ) , P' , Q' ,
              ⟹-ev Pev rP , ⟹-ev Qev rQ , psync csat inter
  ... | evL {X = X} {e = e} {a = a} ¬csat Pev =
          case Par-trace-elim A merge _ Q rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter) →
              (evl (evLabel X e a) ∷ sP) , sQ , P' , Q' ,
              ⟹-ev Pev rP , rQ , psoloL ¬csat inter
  ... | evR {X = X} {e = e} {a = a} ¬csat Qev =
          case Par-trace-elim A merge P _ rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter) →
              sP , (evl (evLabel X e a) ∷ sQ) , P' , Q' ,
              rP , ⟹-ev Qev rQ , psoloR ¬csat inter
  ... | evBoth ¬csat Pev Qev = Par-brBoth-trace-elim A merge P Q _ _ ¬csat Pev Qev rest
  ... | ev√ {r₁ = r₁} {r₂ = r₂} fpP fpQ = case rest of λ where
          ⟹-refl       → (√ r₁ ∷ []) , (√ r₂ ∷ []) , deadlock , deadlock ,
                          ⟹-ev (sRet fpP) ⟹-refl , ⟹-ev (sRet fpQ) ⟹-refl , p√
          (⟹-τ st _)   → ⊥-elim (deadlock-no-τ st)
          (⟹-ev st _)  → ⊥-elim (deadlock-no-ev st)

  -- de-interleave a trace starting from the inline both-offer overlap node, given the
  -- already-fired outside-`A` event was offered by both P (→ P′) and Q (→ Q′)
  Par-brBoth-trace-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                            (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                            (P' : PTree E (ExtI E) R₁) (Q' : PTree E (ExtI E) R₂)
                            {X : Set ℓ} {e : E X} {a : X}
                            {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                        → ¬ A .mem (X , e) a
                        → P ─[ ev (evl (evLabel X e a)) ]─► P'
                        → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
                        → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ⟹⟨ s ⟩ Rt
                        → Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
                          Σ[ Pr ∈ PTree E (ExtI E) R₁ ] Σ[ Qr ∈ PTree E (ExtI E) R₂ ]
                            (P ⟹⟨ sP ⟩ Pr) × (Q ⟹⟨ sQ ⟩ Qr)
                            × ParInter A merge sP sQ (evl (evLabel X e a) ∷ s)
  Par-brBoth-trace-elim A merge P Q P' Q' {X = X} {e = e} {a = a} ¬csat Pev Qev ⟹-refl =
    (evl (evLabel X e a) ∷ []) , [] , P' , Q ,
    ⟹-ev Pev ⟹-refl , ⟹-refl , psoloL ¬csat pnil
  Par-brBoth-trace-elim A merge P Q P' Q' {X = X} {e = e} {a = a} ¬csat Pev Qev (⟹-τ step rest)
    with brBoth-τ-elim A merge P Q P' Q' step
  ... | inj₁ refl = case Par-trace-elim A merge P' Q rest of λ where
          (sP , sQ , Pr , Qr , rP , rQ , inter) →
            (evl (evLabel X e a) ∷ sP) , sQ , Pr , Qr ,
            ⟹-ev Pev rP , rQ , psoloL ¬csat inter
  ... | inj₂ refl = case Par-trace-elim A merge P Q' rest of λ where
          (sP , sQ , Pr , Qr , rP , rQ , inter) →
            sP , (evl (evLabel X e a) ∷ sQ) , Pr , Qr ,
            rP , ⟹-ev Qev rQ , psoloR ¬csat inter
  Par-brBoth-trace-elim A merge P Q P' Q' ¬csat Pev Qev (⟹-ev step rest) =
    ⊥-elim (brBoth-no-ev A merge P Q P' Q' step)

-------------------------------------------------------------------------------------
-- Par-trace-elim-eq : Par-trace-elim STRENGTHENED with the residual identity, needed by
-- the failures-half of parallel associativity (the terminated outer-leaf case): either
-- the reached state IS `Par P' Q'` (the no-√ spine), or it is force-react (deadlock /
-- overlap node), hence NOT ret — so a `force Rt ≡ ret` hypothesis forces the first case
-- and then `Par-force-ret-inv` pushes the termination down to the operands.
-------------------------------------------------------------------------------------
mutual
  Par-trace-elim-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                        (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                        {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                    → (Par A merge P Q) ⟹⟨ s ⟩ Rt
                    → Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
                      Σ[ P' ∈ PTree E (ExtI E) R₁ ] Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                        (P ⟹⟨ sP ⟩ P') × (Q ⟹⟨ sQ ⟩ Q') × ParInter A merge sP sQ s
                        × ((Rt ≡ Par A merge P' Q')
                           ⊎ (¬ (Σ[ r ∈ R ] (PTree.force Rt ≡ ret r))))
  Par-trace-elim-eq A merge P Q ⟹-refl =
    [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil , inj₁ refl
  Par-trace-elim-eq A merge P Q (⟹-τ step rest) with Par-τ-elim A merge P Q step
  ... | τL P'' Pτ refl = case Par-trace-elim-eq A merge P'' Q rest of λ where
          (sP , sQ , P' , Q' , rP , rQ , inter , idEq) →
            sP , sQ , P' , Q' , ⟹-τ Pτ rP , rQ , inter , idEq
  ... | τR Q'' Qτ refl = case Par-trace-elim-eq A merge P Q'' rest of λ where
          (sP , sQ , P' , Q' , rP , rQ , inter , idEq) →
            sP , sQ , P' , Q' , rP , ⟹-τ Qτ rQ , inter , idEq
  Par-trace-elim-eq A merge P Q (⟹-ev step rest) with Par-ev-elim A merge P Q step
  ... | evSync {X = X} {e = e} {a = a} csat Pev Qev =
          case Par-trace-elim-eq A merge _ _ rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter , idEq) →
              (evl (evLabel X e a) ∷ sP) , (evl (evLabel X e a) ∷ sQ) , P' , Q' ,
              ⟹-ev Pev rP , ⟹-ev Qev rQ , psync csat inter , idEq
  ... | evL {X = X} {e = e} {a = a} ¬csat Pev =
          case Par-trace-elim-eq A merge _ Q rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter , idEq) →
              (evl (evLabel X e a) ∷ sP) , sQ , P' , Q' ,
              ⟹-ev Pev rP , rQ , psoloL ¬csat inter , idEq
  ... | evR {X = X} {e = e} {a = a} ¬csat Qev =
          case Par-trace-elim-eq A merge P _ rest of λ where
            (sP , sQ , P' , Q' , rP , rQ , inter , idEq) →
              sP , (evl (evLabel X e a) ∷ sQ) , P' , Q' ,
              rP , ⟹-ev Qev rQ , psoloR ¬csat inter , idEq
  ... | evBoth ¬csat Pev Qev = Par-brBoth-trace-elim-eq A merge P Q _ _ ¬csat Pev Qev rest
  ... | ev√ {r₁ = r₁} {r₂ = r₂} fpP fpQ = case rest of λ where
          ⟹-refl       → (√ r₁ ∷ []) , (√ r₂ ∷ []) , deadlock , deadlock ,
                          ⟹-ev (sRet fpP) ⟹-refl , ⟹-ev (sRet fpQ) ⟹-refl , p√ ,
                          inj₂ (λ { (_ , ()) })
          (⟹-τ st _)   → ⊥-elim (deadlock-no-τ st)
          (⟹-ev st _)  → ⊥-elim (deadlock-no-ev st)

  Par-brBoth-trace-elim-eq : (A : EventSet) (merge : Mg R₁ R₂ R)
                               (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                               (P' : PTree E (ExtI E) R₁) (Q' : PTree E (ExtI E) R₂)
                               {X : Set ℓ} {e : E X} {a : X}
                               {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                           → ¬ A .mem (X , e) a
                           → P ─[ ev (evl (evLabel X e a)) ]─► P'
                           → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
                           → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ⟹⟨ s ⟩ Rt
                           → Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
                             Σ[ Pr ∈ PTree E (ExtI E) R₁ ] Σ[ Qr ∈ PTree E (ExtI E) R₂ ]
                               (P ⟹⟨ sP ⟩ Pr) × (Q ⟹⟨ sQ ⟩ Qr)
                               × ParInter A merge sP sQ (evl (evLabel X e a) ∷ s)
                               × ((Rt ≡ Par A merge Pr Qr)
                                  ⊎ (¬ (Σ[ r ∈ R ] (PTree.force Rt ≡ ret r))))
  Par-brBoth-trace-elim-eq A merge P Q P' Q' {X = X} {e = e} {a = a} ¬csat Pev Qev ⟹-refl =
    (evl (evLabel X e a) ∷ []) , [] , P' , Q ,
    ⟹-ev Pev ⟹-refl , ⟹-refl , psoloL ¬csat pnil , inj₂ (λ { (_ , ()) })
  Par-brBoth-trace-elim-eq A merge P Q P' Q' {X = X} {e = e} {a = a} ¬csat Pev Qev (⟹-τ step rest)
    with brBoth-τ-elim A merge P Q P' Q' step
  ... | inj₁ refl = case Par-trace-elim-eq A merge P' Q rest of λ where
          (sP , sQ , Pr , Qr , rP , rQ , inter , idEq) →
            (evl (evLabel X e a) ∷ sP) , sQ , Pr , Qr ,
            ⟹-ev Pev rP , rQ , psoloL ¬csat inter , idEq
  ... | inj₂ refl = case Par-trace-elim-eq A merge P Q' rest of λ where
          (sP , sQ , Pr , Qr , rP , rQ , inter , idEq) →
            sP , (evl (evLabel X e a) ∷ sQ) , Pr , Qr ,
            rP , ⟹-ev Qev rQ , psoloR ¬csat inter , idEq
  Par-brBoth-trace-elim-eq A merge P Q P' Q' ¬csat Pev Qev (⟹-ev step rest) =
    ⊥-elim (brBoth-no-ev A merge P Q P' Q' step)
