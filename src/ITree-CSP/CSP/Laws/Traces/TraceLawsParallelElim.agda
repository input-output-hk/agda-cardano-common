{-# OPTIONS --guardedness #-}

-- SPIKE: single-step transition ELIMINATION (inversion) lemmas for the GENERALISED
-- parallel Par (P : PTree R₁, Q : PTree R₂, joint √ combined by merge : R₁→R₂→R).
-- This is Layer 1 of the Par-mono chain (cf. □-τ-elim / □-ev-elim in
-- TraceLawsExtChoiceMono).  Each step of `Par P Q` is inverted into the operand
-- step(s) that produced it:
--   Par-τ-elim  : a τ is P's τ (→ Par P′ Q) or Q's τ (→ Par P Q′).
--   Par-ev-elim : a visible/√ step is a sync (both in `A`), a solo (one outside `A`),
--                 a both-offer-outside-`A` event (→ the inline ⊓ overlap), or a joint √.
-- The trace-level de-interleaving (Par-trace-elim) and Par-mono build on these.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
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

module CSP.Laws.Traces.TraceLawsParallelElim {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators           E-≟
open EventSet
open import Semantics.LTS                {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsParallel  E-≟
  using (Mg; fPar-sr; fPar-er; fPar-rs; fPar-re; fPar-nn)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (react-τ-inv; ret-no-τ; viewT-τ)

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- generic step-inversion helpers
-------------------------------------------------------------------------------------

-- a node forced to `sil t′` makes exactly the τ-step to t′
sil-τ-inv : ∀ {ℓr} {Rg : Set ℓr} {t t' M : PTree E (ExtI E) Rg}
          → PTree.force t ≡ sil t' → t ─[ τ ]─► M → M ≡ t'
sil-τ-inv eqf (sSil sileq)    = sil-injective (trans (sym sileq) eqf)
sil-τ-inv eqf (sTau extceq _) = ⊥-elim (sil≢react (trans (sym eqf) extceq))

-- a visible offer `viewV nP at a ≡ just P′` is a real visible step of P
viewV-ev : ∀ {ℓr} {Rg : Set ℓr} {P : PTree E (ExtI E) Rg} {nP : NodeKind E (ExtI E) Rg}
             {at : AnyTypes E} {a : proj₁ at} {P' : PTree E (ExtI E) Rg}
         → PTree.force P ≡ nP → viewV nP at a ≡ just P'
         → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P'
viewV-ev {nP = ret _}     eqP veq = case veq of λ ()
viewV-ev {nP = sil _}     eqP veq = case veq of λ ()
viewV-ev {nP = react v τc} eqP veq = sVis eqP veq

-------------------------------------------------------------------------------------
-- the both-terminate force inversion (force (Par P Q) ≡ ret x ⇒ P,Q both at ret)
-------------------------------------------------------------------------------------

Par-force-ret-inv : (A : EventSet) (merge : Mg R₁ R₂ R)
                      {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {x : R}
                  → PTree.force (Par A merge P Q) ≡ ret x
                  → Σ[ r₁ ∈ R₁ ] Σ[ r₂ ∈ R₂ ]
                      (PTree.force P ≡ ret r₁) × (PTree.force Q ≡ ret r₂) × (x ≡ merge r₁ r₂)
Par-force-ret-inv A merge {P = P} {Q = Q} eqf with PTree.force P | PTree.force Q
... | ret r₁ | ret r₂     = r₁ , r₂ , refl , refl , (case eqf of λ { refl → refl })
... | ret _  | sil _      = case eqf of λ ()
... | ret _  | react _ _   = case eqf of λ ()
... | sil _  | ret _      = case eqf of λ ()
... | sil _  | sil _      = case eqf of λ ()
... | sil _  | react _ _   = case eqf of λ ()
... | react _ _ | ret _    = case eqf of λ ()
... | react _ _ | sil _    = case eqf of λ ()
... | react _ _ | react _ _ = case eqf of λ ()

-------------------------------------------------------------------------------------
-- branch-equation ELIM lemmas for the named continuations
-------------------------------------------------------------------------------------

-- P done, Q live: Q's own τ fires through par-hTauR
par-hTauR-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P : PTree E (ExtI E) R₁)
                   {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₂))}
                   {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
               → par-hTauR A merge P τcQ i a ≡ just M
               → Σ[ Q' ∈ PTree E (ExtI E) R₂ ] (τcQ i a ≡ just Q') × (M ≡ Par A merge P Q')
par-hTauR-elim A merge P {τcQ = τcQ} {i = i} {a = a} eq with τcQ i a
... | just Q' = Q' , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-- Q done, P live: P's own τ fires through par-hTauL
par-hTauL-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                   {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R₁))}
                   (Q : PTree E (ExtI E) R₂)
                   {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
               → par-hTauL A merge τcP Q i a ≡ just M
               → Σ[ P' ∈ PTree E (ExtI E) R₁ ] (τcP i a ≡ just P') × (M ≡ Par A merge P' Q)
par-hTauL-elim A merge {τcP = τcP} Q {i = i} {a = a} eq with τcP i a
... | just P' = P' , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-- P done, Q live: Q's visible offer fires through par-hVisR (only outside `A`)
par-hVisR-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P : PTree E (ExtI E) R₁)
                   {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂))}
                   {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
               → par-hVisR A merge P vQ at a ≡ just M
               → Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                   (¬ A .mem at a) × (vQ at a ≡ just Q') × (M ≡ Par A merge P Q')
par-hVisR-elim A merge P {vQ = vQ} {at = at} {a = a} eq with A .dec at a
... | yes _ = case eq of λ ()
... | no ¬p with vQ at a
...   | just Q' = Q' , ¬p , refl , sym (just-injective eq)
...   | nothing = case eq of λ ()

-- Q done, P live: P's visible offer fires through par-hVisL (only outside `A`)
par-hVisL-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                   {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁))}
                   (Q : PTree E (ExtI E) R₂)
                   {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
               → par-hVisL A merge vP Q at a ≡ just M
               → Σ[ P' ∈ PTree E (ExtI E) R₁ ]
                   (¬ A .mem at a) × (vP at a ≡ just P') × (M ≡ Par A merge P' Q)
par-hVisL-elim A merge {vP = vP} Q {at = at} {a = a} eq with A .dec at a
... | yes _ = case eq of λ ()
... | no ¬p with vP at a
...   | just P' = P' , ¬p , refl , sym (just-injective eq)
...   | nothing = case eq of λ ()

-- both live: par-pTau is P's τ at tag0 (→ Par P′ Q) ⊕ Q's τ at tag1 (→ Par P Q′)
par-pTau-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
              → par-pTau A merge nP nQ P Q i a ≡ just M
              → (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R₁ ]
                   (viewT nP j a' ≡ just P') × (M ≡ Par A merge P' Q))
              ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                   (viewT nQ j a' ≡ just Q') × (M ≡ Par A merge P Q'))
par-pTau-elim A merge nP nQ P Q {_ , base _}            eq = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , fin}               eq = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , pair (base _) _}   eq = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , pair (pair _ _) _} eq = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , pair fin j} {lift fzero        , a'} eq
  with viewT nP (_ , j) a' in veq
... | just P' = inj₁ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq
  with viewT nQ (_ , j) a' in veq
... | just Q' = inj₂ ((_ , j) , a' , Q' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
par-pTau-elim A merge nP nQ P Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- both live: par-pVis is sync (in `A`, both offer), both-offer-outside-`A` (→ inline ⊓), or solo
par-pVis-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (nP : NodeKind E (ExtI E) R₁) (nQ : NodeKind E (ExtI E) R₂)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
              → par-pVis A merge nP nQ P Q at a ≡ just M
              → (Σ[ P' ∈ PTree E (ExtI E) R₁ ] Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                   A .mem at a × (viewV nP at a ≡ just P') × (viewV nQ at a ≡ just Q')
                   × (M ≡ Par A merge P' Q'))
              ⊎ (Σ[ P' ∈ PTree E (ExtI E) R₁ ] Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                   (¬ A .mem at a) × (viewV nP at a ≡ just P') × (viewV nQ at a ≡ just Q')
                   × (M ≡ ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))))
              ⊎ (Σ[ P' ∈ PTree E (ExtI E) R₁ ]
                   (¬ A .mem at a) × (viewV nP at a ≡ just P') × (viewV nQ at a ≡ nothing)
                   × (M ≡ Par A merge P' Q))
              ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R₂ ]
                   (¬ A .mem at a) × (viewV nP at a ≡ nothing) × (viewV nQ at a ≡ just Q')
                   × (M ≡ Par A merge P Q'))
par-pVis-elim A merge nP nQ P Q {at = at} {a = a} eq
  with A .dec at a | viewV nP at a | viewV nQ at a
... | yes p  | just P' | just Q' = inj₁ (P' , Q' , p , refl , refl , sym (just-injective eq))
... | yes _  | just _  | nothing = case eq of λ ()
... | yes _  | nothing | _       = case eq of λ ()
... | no ¬p  | just P' | just Q' = inj₂ (inj₁ (P' , Q' , ¬p , refl , refl , sym (just-injective eq)))
... | no ¬p  | just P' | nothing = inj₂ (inj₂ (inj₁ (P' , ¬p , refl , refl , sym (just-injective eq))))
... | no ¬p  | nothing | just Q' = inj₂ (inj₂ (inj₂ (Q' , ¬p , refl , refl , sym (just-injective eq))))
... | no _   | nothing | nothing = case eq of λ ()

-------------------------------------------------------------------------------------
-- Par-τ-elim : a τ-step of Par P Q is P's τ (→ Par P′ Q) or Q's τ (→ Par P Q′)
-------------------------------------------------------------------------------------

data ParτR {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
           (A : EventSet) (merge : Mg R₁ R₂ R)
           (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           (M : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓs) where
  τL : (P' : PTree E (ExtI E) R₁) → P ─[ τ ]─► P' → M ≡ Par A merge P' Q → ParτR A merge P Q M
  τR : (Q' : PTree E (ExtI E) R₂) → Q ─[ τ ]─► Q' → M ≡ Par A merge P Q' → ParτR A merge P Q M

-- force (Par P Q) ≡ ret r witnesses a τ is impossible there
fPar-rr : (A : EventSet) (merge : Mg R₁ R₂ R)
          {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂} {r₁ : R₁} {r₂ : R₂}
        → PTree.force P ≡ ret r₁ → PTree.force Q ≡ ret r₂
        → PTree.force (Par A merge P Q) ≡ ret (merge r₁ r₂)
fPar-rr A merge {P = P} {Q = Q} eqP eqQ with PTree.force P | PTree.force Q
... | ret _    | ret _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | ret _    | sil _    = case eqQ of λ ()
... | ret _    | react _ _ = case eqQ of λ ()
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

-- a τ landing in par-pTau, decoded into the operand step that produced it
par-pTau-inv : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {nP : NodeKind E (ExtI E) R₁} {nQ : NodeKind E (ExtI E) R₂}
                 {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
             → PTree.force P ≡ nP → PTree.force Q ≡ nQ
             → par-pTau A merge nP nQ P Q i a ≡ just M
             → ParτR A merge P Q M
par-pTau-inv A merge P Q {nP} {nQ} {i = i} {a = a} eqP eqQ breq
  with par-pTau-elim A merge nP nQ P Q {i = i} {a = a} breq
... | inj₁ (j , a' , P' , veq , refl) = τL P' (viewT-τ eqP veq) refl
... | inj₂ (j , a' , Q' , veq , refl) = τR Q' (viewT-τ eqQ veq) refl

Par-τ-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
             (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂) {M : PTree E (ExtI E) R}
           → (Par A merge P Q) ─[ τ ]─► M → ParτR A merge P Q M
Par-τ-elim A merge P Q step with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r₁ | ret r₂ = ⊥-elim (ret-no-τ (fPar-rr A merge eqP eqQ) step)
... | ret r₁ | sil Q' = case sil-τ-inv (fPar-rs A merge eqP eqQ) step of λ { refl → τR Q' (sSil eqQ) refl }
... | sil P' | ret r₂ = case sil-τ-inv (fPar-sr A merge eqP eqQ) step of λ { refl → τL P' (sSil eqP) refl }
... | ret r₁ | react vQ τcQ = case react-τ-inv (fPar-re A merge eqP eqQ) step of λ where
    (i , a , breq) → case par-hTauR-elim A merge P {τcQ = τcQ} {i = i} {a = a} breq of λ where
      (Q' , teq , refl) → τR Q' (viewT-τ {nP = react vQ τcQ} eqQ teq) refl
... | react vP τcP | ret r₂ = case react-τ-inv (fPar-er A merge eqP eqQ) step of λ where
    (i , a , breq) → case par-hTauL-elim A merge {τcP = τcP} Q {i = i} {a = a} breq of λ where
      (P' , teq , refl) → τL P' (viewT-τ {nP = react vP τcP} eqP teq) refl
... | sil P' | sil Q' = case react-τ-inv (fPar-nn A merge eqP eqQ tt tt) step of λ where
    (i , a , breq) → par-pTau-inv A merge P Q {i = i} {a = a} eqP eqQ breq
... | sil P' | react vQ τcQ = case react-τ-inv (fPar-nn A merge eqP eqQ tt tt) step of λ where
    (i , a , breq) → par-pTau-inv A merge P Q {i = i} {a = a} eqP eqQ breq
... | react vP τcP | sil Q' = case react-τ-inv (fPar-nn A merge eqP eqQ tt tt) step of λ where
    (i , a , breq) → par-pTau-inv A merge P Q {i = i} {a = a} eqP eqQ breq
... | react vP τcP | react vQ τcQ = case react-τ-inv (fPar-nn A merge eqP eqQ tt tt) step of λ where
    (i , a , breq) → par-pTau-inv A merge P Q {i = i} {a = a} eqP eqQ breq

-------------------------------------------------------------------------------------
-- Par-ev-elim : a visible/√ step of Par P Q
-------------------------------------------------------------------------------------

data ParevR {ℓ₁ ℓ₂ ℓs} {R₁ : Set ℓ₁} {R₂ : Set ℓ₂} {R : Set ℓs}
            (A : EventSet) (merge : Mg R₁ R₂ R)
            (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
     : PTree E (ExtI E) R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓs) where
  -- a shared cs event: both operands step on it
  evSync : ∀ {X} {e : E X} {a : X} {P' Q'}
         → A .mem (X , e) a
         → P ─[ ev (evl (evLabel X e a)) ]─► P'
         → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
         → ParevR A merge P Q (Par A merge P' Q') (evl (evLabel X e a))
  -- a solo (outside `A`) event from P (Q either live or terminated)
  evL    : ∀ {X} {e : E X} {a : X} {P'}
         → ¬ A .mem (X , e) a → P ─[ ev (evl (evLabel X e a)) ]─► P'
         → ParevR A merge P Q (Par A merge P' Q) (evl (evLabel X e a))
  -- a solo (outside `A`) event from Q
  evR    : ∀ {X} {e : E X} {a : X} {Q'}
         → ¬ A .mem (X , e) a → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
         → ParevR A merge P Q (Par A merge P Q') (evl (evLabel X e a))
  -- both offer the same outside-`A` event ⇒ the inline overlap node (Par P′ Q) ⊓ (Par P Q′)
  evBoth : ∀ {X} {e : E X} {a : X} {P' Q'}
         → ¬ A .mem (X , e) a
         → P ─[ ev (evl (evLabel X e a)) ]─► P'
         → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
         → ParevR A merge P Q
             (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q')))
             (evl (evLabel X e a))
  -- joint termination: both at ret ⇒ √ (merge r₁ r₂)
  ev√    : ∀ {r₁ : R₁} {r₂ : R₂}
         → PTree.force P ≡ ret r₁ → PTree.force Q ≡ ret r₂
         → ParevR A merge P Q deadlock (√ (merge r₁ r₂))

-- a visible offer landing in par-pVis, decoded
par-pVis-inv : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {nP : NodeKind E (ExtI E) R₁} {nQ : NodeKind E (ExtI E) R₂}
                 {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
             → PTree.force P ≡ nP → PTree.force Q ≡ nQ
             → par-pVis A merge nP nQ P Q at a ≡ just M
             → ParevR A merge P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
par-pVis-inv A merge P Q {nP} {nQ} {at = at} {a = a} eqP eqQ breq
  with par-pVis-elim A merge nP nQ P Q {at = at} {a = a} breq
... | inj₁ (P' , Q' , p , vPeq , vQeq , refl) =
        evSync p (viewV-ev {at = at} {a = a} eqP vPeq) (viewV-ev {at = at} {a = a} eqQ vQeq)
... | inj₂ (inj₁ (P' , Q' , ¬p , vPeq , vQeq , refl)) =
        evBoth ¬p (viewV-ev {at = at} {a = a} eqP vPeq) (viewV-ev {at = at} {a = a} eqQ vQeq)
... | inj₂ (inj₂ (inj₁ (P' , ¬p , vPeq , vQeq , refl))) =
        evL ¬p (viewV-ev {at = at} {a = a} eqP vPeq)
... | inj₂ (inj₂ (inj₂ (Q' , ¬p , vPeq , vQeq , refl))) =
        evR ¬p (viewV-ev {at = at} {a = a} eqQ vQeq)

-- the visible-offer inversion: by (force P , force Q) shape
Par-vis-inv : (A : EventSet) (merge : Mg R₁ R₂ R)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
            → PTree.force (Par A merge P Q) ≡ react v τc → v at a ≡ just M
            → ParevR A merge P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
Par-vis-inv A merge P Q {at = at} {a = a} eqf breq
  with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r₁ | ret r₂ = case eqf of λ ()
... | ret r₁ | sil Q' = case eqf of λ ()
... | sil P' | ret r₂ = case eqf of λ ()
... | ret r₁ | react vQ τcQ =
        case par-hVisR-elim A merge P {vQ = vQ} {at = at} {a = a}
               (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
          (Q' , ¬p , vQeq , refl) → evR ¬p (viewV-ev {nP = react vQ τcQ} {at = at} {a = a} eqQ vQeq)
... | react vP τcP | ret r₂ =
        case par-hVisL-elim A merge {vP = vP} Q {at = at} {a = a}
               (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq) of λ where
          (P' , ¬p , vPeq , refl) → evL ¬p (viewV-ev {nP = react vP τcP} {at = at} {a = a} eqP vPeq)
... | sil P' | sil Q' =
        par-pVis-inv A merge P Q eqP eqQ
          (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq)
... | sil P' | react vQ τcQ =
        par-pVis-inv A merge P Q eqP eqQ
          (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq)
... | react vP τcP | sil Q' =
        par-pVis-inv A merge P Q eqP eqQ
          (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq)
... | react vP τcP | react vQ τcQ =
        par-pVis-inv A merge P Q eqP eqQ
          (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) breq)

Par-ev-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
              (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
              {M : PTree E (ExtI E) R} {e : Event√ R}
            → (Par A merge P Q) ─[ ev e ]─► M → ParevR A merge P Q M e
Par-ev-elim A merge P Q (sRet eqf) =
  case Par-force-ret-inv A merge eqf of λ where
    (r₁ , r₂ , fpP , fpQ , refl) → ev√ fpP fpQ
Par-ev-elim A merge P Q (sVis eqf breq) = Par-vis-inv A merge P Q eqf breq
