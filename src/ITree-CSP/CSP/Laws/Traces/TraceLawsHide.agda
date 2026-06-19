{-# OPTIONS --guardedness #-}

-- SPIKE: hiding is ⊑ᵀ-monotone, on the FIXED react Hide operator (τ-namespace split so
-- nested hides never collide — see CSP.Operators hide-hTau: tag0 propagates ALL of P's τ's,
-- tag1 carries newly-hidden events).  Full chain:
--   Hide-τ / Hide-keep / Hide-hidden / Hide-√ : single-step intros
--   Hide-τ-elim / Hide-ev-elim                : single-step inversions
--   HideTr cs s′ s : `s` is `s′` with the cs-events deleted (the de-hiding relation)
--   Hide-trace-elim / Hide-trace-intro         : the two trace directions
--   Hide-mono-⊑ᵀ : P ⊑T Q → (P ∖ cs) ⊑T (Q ∖ cs)
-- No postulates, no NON_TERMINATING.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsHide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open EventSet
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (react-τ-inv; ret-no-τ; viewT-τ)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟ using (viewV-ev; sil-τ-inv)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (deadlock-no-τ; deadlock-no-ev)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- force-equation lemmas
-------------------------------------------------------------------------------------

fHide-ret : (A : EventSet) (P : PTree E (ExtI E) R) {r : R}
          → PTree.force P ≡ ret r → PTree.force (P ∖ A) ≡ ret r
fHide-ret A P eqP with PTree.force P
... | ret _    = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fHide-sil : (A : EventSet) (P : PTree E (ExtI E) R) {c : PTree E (ExtI E) R}
          → PTree.force P ≡ sil c → PTree.force (P ∖ A) ≡ sil (c ∖ A)
fHide-sil A P eqP with PTree.force P
... | sil _    = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

fHide-react : (A : EventSet) (P : PTree E (ExtI E) R)
               {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → PTree.force P ≡ react v τc
           → PTree.force (P ∖ A)
             ≡ react (hide-hVis A (react v τc)) (hide-hTau A (react v τc))
fHide-react A P eqP with PTree.force P
... | react _ _ = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | sil _    = case eqP of λ ()

fHide-ret-inv : (A : EventSet) (P : PTree E (ExtI E) R) {r : R}
              → PTree.force (P ∖ A) ≡ ret r → PTree.force P ≡ ret r
fHide-ret-inv A P eqf with PTree.force P
... | ret _    = eqf
... | sil _    = case eqf of λ ()
... | react _ _ = case eqf of λ ()

-------------------------------------------------------------------------------------
-- branch-equation INTRO lemmas
-------------------------------------------------------------------------------------

hide-hVis-keep-eq : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                      {at : AnyTypes E} {a : proj₁ at} {P' : PTree E (ExtI E) R}
                  → ¬ A .mem at a → viewV nP at a ≡ just P'
                  → hide-hVis A nP at a ≡ just (P' ∖ A)
hide-hVis-keep-eq A nP {at = at} {a = a} ¬c veq with A .dec at a
... | yes p = ⊥-elim (¬c p)
... | no  _ with viewV nP at a
...   | just _  = case veq of λ { refl → refl }
...   | nothing = case veq of λ ()

hide-hTau-tag0-eq : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                      {iₚ : AnyTypes (ExtI E)} {aₚ : proj₁ iₚ} {P' : PTree E (ExtI E) R}
                  → viewT nP iₚ aₚ ≡ just P'
                  → hide-hTau A nP ((Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ))
                                   (lift fzero , aₚ)
                    ≡ just (P' ∖ A)
hide-hTau-tag0-eq A nP {iₚ = iₚ} {aₚ = aₚ} ve with viewT nP (proj₁ iₚ , proj₂ iₚ) aₚ
... | just _  = case ve of λ { refl → refl }
... | nothing = case ve of λ ()

hide-hTau-tag1-eq : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                      {B : Set ℓ} {e : E B} {a : B} {P' : PTree E (ExtI E) R}
                  → A .mem (B , e) a → viewV nP (B , e) a ≡ just P'
                  → hide-hTau A nP ((Lift ℓ (Fin 2) × B) , pair fin (base e))
                                   (lift (fsuc fzero) , a)
                    ≡ just (P' ∖ A)
hide-hTau-tag1-eq A nP {B = B} {e = e} {a = a} csat veq with A .dec (B , e) a
... | no ¬c = ⊥-elim (¬c csat)
... | yes _ with viewV nP (B , e) a
...   | just _  = case veq of λ { refl → refl }
...   | nothing = case veq of λ ()

-------------------------------------------------------------------------------------
-- branch-equation ELIM lemmas
-------------------------------------------------------------------------------------

hide-hVis-elim : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                   {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
               → hide-hVis A nP at a ≡ just M
               → (¬ A .mem at a) × Σ[ P' ∈ PTree E (ExtI E) R ]
                   (viewV nP at a ≡ just P') × (M ≡ P' ∖ A)
hide-hVis-elim A nP {at = at} {a = a} eq with A .dec at a
... | yes _ = case eq of λ ()
... | no ¬c with viewV nP at a
...   | just P' = ¬c , P' , refl , sym (just-injective eq)
...   | nothing = case eq of λ ()

-- a `just` out of the tag1 emitter is a hidden visible event
hide-emit-elim : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                   {B : Set ℓ} (i′ : ExtI E B) (a′ : B) {M : PTree E (ExtI E) R}
               → hide-emit A nP i′ a′ ≡ just M
               → Σ[ at ∈ AnyTypes E ] Σ[ a'' ∈ proj₁ at ] Σ[ P' ∈ PTree E (ExtI E) R ]
                   A .mem at a'' × (viewV nP at a'' ≡ just P') × (M ≡ P' ∖ A)
hide-emit-elim A nP (base e) a′ eq with A .dec (_ , e) a′
... | yes c with viewV nP (_ , e) a′ in veq
...   | just P' = (_ , e) , a′ , P' , c , veq , sym (just-injective eq)
...   | nothing = case eq of λ ()
hide-emit-elim A nP (base e) a′ eq | no _ = case eq of λ ()
hide-emit-elim A nP (pair _ _) a′ eq = case eq of λ ()
hide-emit-elim A nP fin       a′ eq = case eq of λ ()

hide-hTau-elim : (A : EventSet) (nP : NodeKind E (ExtI E) R)
                   {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
               → hide-hTau A nP i a ≡ just M
               → (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
                    (viewT nP j a' ≡ just P') × (M ≡ P' ∖ A))
               ⊎ (Σ[ at ∈ AnyTypes E ] Σ[ a' ∈ proj₁ at ] Σ[ P' ∈ PTree E (ExtI E) R ]
                    A .mem at a' × (viewV nP at a' ≡ just P') × (M ≡ P' ∖ A))
hide-hTau-elim A nP {i = _ , pair fin i′} {a = lift fzero , a′} eq with viewT nP (_ , i′) a′ in veq
... | just P' = inj₁ ((_ , i′) , a′ , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
hide-hTau-elim A nP {i = _ , pair fin i′} {a = lift (fsuc fzero) , a′} eq =
  inj₂ (hide-emit-elim A nP i′ a′ eq)
hide-hTau-elim A nP {i = _ , pair fin i′} {a = lift (fsuc (fsuc _)) , a′} eq = case eq of λ ()
hide-hTau-elim A nP {i = _ , base _} eq = case eq of λ ()
hide-hTau-elim A nP {i = _ , fin} eq = case eq of λ ()
hide-hTau-elim A nP {i = _ , pair (base _) _} eq = case eq of λ ()
hide-hTau-elim A nP {i = _ , pair (pair _ _) _} eq = case eq of λ ()

-------------------------------------------------------------------------------------
-- single-step INTRO lemmas
-------------------------------------------------------------------------------------

-- P's own τ propagates (tag0, unconditional — the key property the fix restores)
Hide-τ : (A : EventSet) (P : PTree E (ExtI E) R) {P' : PTree E (ExtI E) R}
       → P ─[ τ ]─► P' → (P ∖ A) ─[ τ ]─► (P' ∖ A)
Hide-τ A P (sSil eqf) = sSil (fHide-sil A P eqf)
Hide-τ A P (sTau {v = vP} {τc = τcP} {i = iₚ} {a = aₚ} eqP brP) =
  sTau {i = (Lift ℓ (Fin 2) × proj₁ iₚ) , pair fin (proj₂ iₚ)} {a = lift fzero , aₚ}
       (fHide-react A P eqP)
       (hide-hTau-tag0-eq A (react vP τcP) {iₚ = iₚ} {aₚ = aₚ} brP)

-- a non-hidden visible event survives
Hide-keep : (A : EventSet) (P : PTree E (ExtI E) R)
              {B : Set ℓ} {e : E B} {a : B} {P' : PTree E (ExtI E) R}
          → ¬ A .mem (B , e) a → P ─[ ev (evl (evLabel B e a)) ]─► P'
          → (P ∖ A) ─[ ev (evl (evLabel B e a)) ]─► (P' ∖ A)
Hide-keep A P {B = B} {e = e} {a = a} ¬c (sVis {v = vP} {τc = τcP} eqP veqP) =
  sVis (fHide-react A P eqP)
       (hide-hVis-keep-eq A (react vP τcP) {at = B , e} {a = a} ¬c veqP)

-- a hidden visible event becomes a τ (tag1)
Hide-hidden : (A : EventSet) (P : PTree E (ExtI E) R)
                {B : Set ℓ} {e : E B} {a : B} {P' : PTree E (ExtI E) R}
            → A .mem (B , e) a → P ─[ ev (evl (evLabel B e a)) ]─► P'
            → (P ∖ A) ─[ τ ]─► (P' ∖ A)
Hide-hidden A P {B = B} {e = e} {a = a} csat (sVis {v = vP} {τc = τcP} eqP veqP) =
  sTau {i = (Lift ℓ (Fin 2) × B) , pair fin (base e)} {a = lift (fsuc fzero) , a}
       (fHide-react A P eqP)
       (hide-hTau-tag1-eq A (react vP τcP) {B = B} {e = e} {a = a} csat veqP)

-- √ propagates
Hide-√ : (A : EventSet) (P : PTree E (ExtI E) R) {r : R}
       → PTree.force P ≡ ret r → (P ∖ A) ─[ ev (√ r) ]─► deadlock
Hide-√ A P eqP = sRet (fHide-ret A P eqP)

-------------------------------------------------------------------------------------
-- single-step ELIM lemmas
-------------------------------------------------------------------------------------

data HideτR {ℓr} {R : Set ℓr} (A : EventSet)
            (P : PTree E (ExtI E) R) (M : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  hτP : (P' : PTree E (ExtI E) R) → P ─[ τ ]─► P' → M ≡ P' ∖ A → HideτR A P M
  hτH : {B : Set ℓ} {e : E B} {a : B} (P' : PTree E (ExtI E) R)
      → A .mem (B , e) a → P ─[ ev (evl (evLabel B e a)) ]─► P' → M ≡ P' ∖ A → HideτR A P M

hide-hTau-inv : (A : EventSet) {P : PTree E (ExtI E) R} {nP : NodeKind E (ExtI E) R}
                  {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
              → PTree.force P ≡ nP → hide-hTau A nP i a ≡ just M → HideτR A P M
hide-hTau-inv A {nP = nP} {i = i} {a = a} eqP breq
  with hide-hTau-elim A nP {i = i} {a = a} breq
... | inj₁ (j , a' , P' , veq , refl)       = hτP P' (viewT-τ eqP veq) refl
... | inj₂ (at , a' , P' , c , veq , refl)  = hτH P' c (viewV-ev eqP veq) refl

Hide-τ-elim : (A : EventSet) (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
            → (P ∖ A) ─[ τ ]─► M → HideτR A P M
Hide-τ-elim A P step with PTree.force P in eqP
... | ret r       = ⊥-elim (ret-no-τ (fHide-ret A P eqP) step)
... | sil c       = case sil-τ-inv (fHide-sil A P eqP) step of λ { refl → hτP c (sSil eqP) refl }
... | react vP τcP = case react-τ-inv (fHide-react A P eqP) step of λ where
        (i , a , breq) → hide-hTau-inv A {i = i} {a = a} eqP breq

data HideevR {ℓr} {R : Set ℓr} (A : EventSet) (P : PTree E (ExtI E) R)
     : PTree E (ExtI E) R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  heV : {B : Set ℓ} {e : E B} {a : B} (P' : PTree E (ExtI E) R)
      → ¬ A .mem (B , e) a → P ─[ ev (evl (evLabel B e a)) ]─► P'
      → HideevR A P (P' ∖ A) (evl (evLabel B e a))
  he√ : {r : R} → PTree.force P ≡ ret r → HideevR A P deadlock (√ r)

hide-hVis-inv : (A : EventSet) (P : PTree E (ExtI E) R)
                  {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
              → PTree.force (P ∖ A) ≡ react v τc → v at a ≡ just M
              → HideevR A P M (evl (evLabel (proj₁ at) (proj₂ at) a))
hide-hVis-inv A P {at = at} {a = a} eqf breq with PTree.force P in eqP
... | ret r       = case eqf of λ ()
... | sil c       = case eqf of λ ()
... | react vP τcP =
        case hide-hVis-elim A (react vP τcP) {at = at} {a = a}
               (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
          (¬c , P' , veq , refl) → heV P' ¬c (viewV-ev {nP = react vP τcP} eqP veq)

Hide-ev-elim : (A : EventSet) (P : PTree E (ExtI E) R)
                 {M : PTree E (ExtI E) R} {e : Event√ R}
             → (P ∖ A) ─[ ev e ]─► M → HideevR A P M e
Hide-ev-elim A P (sRet eqf)        = he√ (fHide-ret-inv A P eqf)
Hide-ev-elim A P (sVis eqf breq)   = hide-hVis-inv A P eqf breq

-------------------------------------------------------------------------------------
-- the de-hiding relation: `s` is `s′` with the cs-events deleted
-------------------------------------------------------------------------------------

data HideTr {ℓr} {R : Set ℓr} (A : EventSet)
     : List (Event√ R) → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  hnil  : HideTr A [] []
  hkeep : ∀ {B} {e : E B} {a : B} {s' s} → ¬ A .mem (B , e) a
        → HideTr A s' s → HideTr A (evl (evLabel B e a) ∷ s') (evl (evLabel B e a) ∷ s)
  hdrop : ∀ {B} {e : E B} {a : B} {s' s} → A .mem (B , e) a
        → HideTr A s' s → HideTr A (evl (evLabel B e a) ∷ s') s
  h√    : ∀ {r : R} → HideTr A (√ r ∷ []) (√ r ∷ [])

-------------------------------------------------------------------------------------
-- Hide-trace-elim : a trace of P ∖ cs de-hides to a trace of P (cs-events deleted)
-------------------------------------------------------------------------------------

Hide-trace-elim : (A : EventSet) (P : PTree E (ExtI E) R)
                    {s : List (Event√ R)} {Rt : PTree E (ExtI E) R}
                → (P ∖ A) ⟹⟨ s ⟩ Rt
                → Σ[ s' ∈ List (Event√ R) ] Σ[ P' ∈ PTree E (ExtI E) R ]
                    (P ⟹⟨ s' ⟩ P') × HideTr A s' s
Hide-trace-elim A P ⟹-refl = [] , P , ⟹-refl , hnil
Hide-trace-elim A P (⟹-τ step rest) with Hide-τ-elim A P step
... | hτP P'' Pτ refl = case Hide-trace-elim A P'' rest of λ where
        (s' , Pr , r , h) → s' , Pr , ⟹-τ Pτ r , h
... | hτH {B = B} {e = e} {a = a} P'' csat Pev refl = case Hide-trace-elim A P'' rest of λ where
        (s' , Pr , r , h) → (evl (evLabel B e a) ∷ s') , Pr , ⟹-ev Pev r , hdrop csat h
Hide-trace-elim A P (⟹-ev step rest) with Hide-ev-elim A P step
... | heV {B = B} {e = e} {a = a} P'' ¬csat Pev = case Hide-trace-elim A P'' rest of λ where
        (s' , Pr , r , h) → (evl (evLabel B e a) ∷ s') , Pr , ⟹-ev Pev r , hkeep ¬csat h
... | he√ {r = r} fpP = case rest of λ where
        ⟹-refl      → (√ r ∷ []) , deadlock , ⟹-ev (sRet fpP) ⟹-refl , h√
        (⟹-τ st _)  → ⊥-elim (deadlock-no-τ st)
        (⟹-ev st _) → ⊥-elim (deadlock-no-ev st)

-------------------------------------------------------------------------------------
-- Hide-trace-intro : re-hide a P-trace per a HideTr witness
-------------------------------------------------------------------------------------

Hide-trace-intro : (A : EventSet) (P : PTree E (ExtI E) R)
                     {P' : PTree E (ExtI E) R} {s' : List (Event√ R)} {s : List (Event√ R)}
                 → P ⟹⟨ s' ⟩ P' → HideTr A s' s → traces (P ∖ A) s
Hide-trace-intro A P (⟹-τ Pτ restP) h =
  case Hide-trace-intro A _ restP h of λ where
    (Rt , bs) → Rt , ⟹-τ (Hide-τ A P Pτ) bs
Hide-trace-intro A P ⟹-refl hnil = (P ∖ A) , ⟹-refl
Hide-trace-intro A P (⟹-ev Pev restP) (hkeep ¬csat h) =
  case Hide-trace-intro A _ restP h of λ where
    (Rt , bs) → Rt , ⟹-ev (Hide-keep A P ¬csat Pev) bs
Hide-trace-intro A P (⟹-ev Pev restP) (hdrop csat h) =
  case Hide-trace-intro A _ restP h of λ where
    (Rt , bs) → Rt , ⟹-τ (Hide-hidden A P csat Pev) bs
Hide-trace-intro A P (⟹-ev (sRet fpP) restP) h√ =
  deadlock , ⟹-ev (Hide-√ A P fpP) ⟹-refl

-------------------------------------------------------------------------------------
-- Hide is ⊑ᵀ-monotone
-------------------------------------------------------------------------------------

Hide-mono-⊑ᵀ : (A : EventSet) {P Q : PTree E (ExtI E) R}
             → P ⊑T Q → (P ∖ A) ⊑T (Q ∖ A)
Hide-mono-⊑ᵀ A {P = P} {Q = Q} P⊑Q s (_ , bs) with Hide-trace-elim A Q bs
... | s' , Q' , rQ , h with P⊑Q s' (Q' , rQ)
...   | P' , rP = Hide-trace-intro A P rP h
