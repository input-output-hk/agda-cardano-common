{-# OPTIONS --guardedness #-}

-- SPIKE: LTS step-inversion lemmas for the Throw operator `_⟦_▷_` on the pure-react
-- layer.  (Interrupt `_△_` inversions are a SEPARATE later task — not here.)
--   Θ-τ-elim  : a τ-step of P ⟦ A ▷ Q is a τ-step of P keeping the throw alive.
--   Θ-ev-elim : a visible/√ step of P ⟦ A ▷ Q is either P's √ (Θdone), a P-event in A
--               that throws to Q (Θthrow), or a P-event not in A that continues (Θpass).

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsThrowInterrupt {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators        E-≟
open import Semantics.LTS             {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)

open EventSet

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- Part 1: force-equation lemmas
-- Their GOAL mentions `force (P ⟦ A ▷ Q)`, so re-doing the `with PTree.force P`
-- here lets the `_⟦_▷_` clause reduce (cf. force-▷-ret/-sil/-react).
-------------------------------------------------------------------------------------

force-Θ-ret : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {A} {r}
            → PTree.force P ≡ ret r → PTree.force (P ⟦ A ▷ Q) ≡ ret r
force-Θ-ret {P = P} eqP with PTree.force P
... | ret _    = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

force-Θ-react : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {A}
                 {v τc} → PTree.force P ≡ react v τc
             → PTree.force (P ⟦ A ▷ Q) ≡ react (Θ-vis A (react v τc) Q) (Θ-τ A (react v τc) Q)
force-Θ-react {P = P} eqP with PTree.force P
... | react _ _ = case eqP of λ { refl → refl }
... | sil _    = case eqP of λ ()
... | ret _    = case eqP of λ ()

force-Θ-sil : ∀ {ℓr} {R : Set ℓr} {P Q P₁ : PTree E (ExtI E) R} {A}
            → PTree.force P ≡ sil P₁
            → PTree.force (P ⟦ A ▷ Q) ≡ react (Θ-vis A (sil P₁) Q) (Θ-τ A (sil P₁) Q)
force-Θ-sil {P = P} eqP with PTree.force P
... | sil _    = case eqP of λ { refl → refl }
... | ret _    = case eqP of λ ()
... | react _ _ = case eqP of λ ()

-------------------------------------------------------------------------------------
-- generic inversions against a known force shape (cf. TraceLawsExtChoiceMono)
-------------------------------------------------------------------------------------

-- a τ-source `viewT nP j a' ≡ just P'` is a real τ-step of P
viewT-τ : {P : PTree E (ExtI E) R} {nP : NodeKind E (ExtI E) R}
            {j : AnyTypes (ExtI E)} {a' : proj₁ j} {P' : PTree E (ExtI E) R}
        → PTree.force P ≡ nP → viewT nP j a' ≡ just P' → P ─[ τ ]─► P'
viewT-τ {nP = ret _}    eqP veq = case veq of λ ()
viewT-τ {nP = react v τc} eqP veq = sTau eqP veq
viewT-τ {nP = sil P₁} {j = _ , base _}   eqP veq = case veq of λ ()
viewT-τ {nP = sil P₁} {j = _ , pair _ _} eqP veq = case veq of λ ()
viewT-τ {nP = sil P₁} {j = _ , fin} {a' = lift fzero}    eqP veq = case veq of λ { refl → sSil eqP }
viewT-τ {nP = sil P₁} {j = _ , fin} {a' = lift (fsuc _)} eqP veq = case veq of λ ()

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

-------------------------------------------------------------------------------------
-- Part 2: τ-inversion.  A τ-step of P ⟦ A ▷ Q is P's own τ (→ P′ ⟦ A ▷ Q).
-------------------------------------------------------------------------------------

-- the τ-branch of Θ produces `just (P′ ⟦ A ▷ Q)` exactly when viewT (force P) fires
Θ-τ-source : (nP : NodeKind E (ExtI E) R) (A : EventSet) (Q : PTree E (ExtI E) R)
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
           → Θ-τ A nP Q i a ≡ just M
           → Σ[ P′ ∈ PTree E (ExtI E) R ] (viewT nP i a ≡ just P′) × (M ≡ (P′ ⟦ A ▷ Q))
Θ-τ-source nP A Q {i = i} {a = a} eq with viewT nP i a
... | just P′ = P′ , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

Θ-τ-elim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {A} {M : PTree E (ExtI E) R}
         → (P ⟦ A ▷ Q) ─[ τ ]─► M
         → Σ[ P′ ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P′) × (M ≡ (P′ ⟦ A ▷ Q)))
Θ-τ-elim P Q {A = A} step with PTree.force P in eqP
... | ret r  = ⊥-elim (ret-no-τ (force-Θ-ret {P = P} {Q = Q} {A = A} eqP) step)
... | sil P₁ = case react-τ-inv (force-Θ-sil {P = P} {Q = Q} {A = A} eqP) step of λ where
    (i , a , breq) → case Θ-τ-source (sil P₁) A Q {i = i} {a = a} breq of λ where
      (P′ , veq , m≡) → P′ , viewT-τ eqP veq , m≡
... | react vP τcP = case react-τ-inv (force-Θ-react {P = P} {Q = Q} {A = A} eqP) step of λ where
    (i , a , breq) → case Θ-τ-source (react vP τcP) A Q {i = i} {a = a} breq of λ where
      (P′ , veq , m≡) → P′ , viewT-τ eqP veq , m≡

-------------------------------------------------------------------------------------
-- Part 3: ev/√-inversion.
-------------------------------------------------------------------------------------

data ΘevR {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) (A : EventSet)
     : PTree E (ExtI E) R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  Θthrow : ∀ {at a P₁}     → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
                           → A .mem at a
                           → ΘevR P Q A Q (evl (evLabel (proj₁ at) (proj₂ at) a))
  Θpass  : ∀ {at a P₁}     → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
                           → ¬ (A .mem at a)
                           → ΘevR P Q A (P₁ ⟦ A ▷ Q) (evl (evLabel (proj₁ at) (proj₂ at) a))
  Θdone  : ∀ {r}           → PTree.force P ≡ ret r → ΘevR P Q A deadlock (√ r)

-- force (P ⟦ A ▷ Q) ≡ ret r ⇒ force P ≡ ret r (the only ret-producing clause)
Θ-force-ret-inv : {P Q : PTree E (ExtI E) R} {A : EventSet} {r : R}
                → PTree.force (P ⟦ A ▷ Q) ≡ ret r → PTree.force P ≡ ret r
Θ-force-ret-inv {P = P} eqf with PTree.force P
... | ret r'      = eqf
... | sil P'      = case eqf of λ ()
... | react vP τcP = case eqf of λ ()

-- shared: given force P ≡ nP and Θ-vis A nP Q at a ≡ just M, build the ΘevR.
-- `viewV nP at a ≡ just …` forces nP to be `react …` (ret/sil offer ∅v ≡ nothing),
-- so we case on nP to expose the react shape that `sVis` needs (then A .dec at a
-- decides throw / continue).
Θ-vis-go : (P Q : PTree E (ExtI E) R) (A : EventSet)
             {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
             (nP : NodeKind E (ExtI E) R)
         → PTree.force P ≡ nP → Θ-vis A nP Q at a ≡ just M
         → ΘevR P Q A M (evl (evLabel (proj₁ at) (proj₂ at) a))
Θ-vis-go P Q A {at = at} {a = a} (ret _)     eqPnP eq = case eq of λ ()
Θ-vis-go P Q A {at = at} {a = a} (sil _)     eqPnP eq = case eq of λ ()
Θ-vis-go P Q A {at = at} {a = a} (react v τc) eqPnP eq with v at a in vveq
... | nothing = case eq of λ ()
... | just P′ with A .dec at a
...   | yes m  = case eq of λ { refl → Θthrow {P₁ = P′} (sVis eqPnP vveq) m }
...   | no  ¬m = case eq of λ { refl → Θpass  {P₁ = P′} (sVis eqPnP vveq) ¬m }

-- the visible offer Θ-vis A (force P) Q at a ≡ just M splits: P offers it at `at a`
-- (via viewV → a real visible step of P), then A's decision throws (M ≡ Q) or
-- continues (M ≡ P′ ⟦ A ▷ Q).
Θ-vis-inv : (P Q : PTree E (ExtI E) R) (A : EventSet)
              {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
          → PTree.force (P ⟦ A ▷ Q) ≡ react v τc → v at a ≡ just M
          → ΘevR P Q A M (evl (evLabel (proj₁ at) (proj₂ at) a))
Θ-vis-inv P Q A {at = at} {a = a} {M = M} eqf breq with PTree.force P in eqP
... | ret r =
  -- force (P ⟦ A ▷ Q) reduces to ret r here, contradicting react
  case eqf of λ ()
... | sil P₁ =
  -- force (P ⟦ A ▷ Q) reduces to react (Θ-vis A (sil P₁) Q) …, so v ≡ Θ-vis A (sil P₁) Q
  let breq′ : Θ-vis A (sil P₁) Q at a ≡ just M
      breq′ = subst (λ g → g at a ≡ just M)
                    (sym (proj₁ (react-injective eqf)))
                    breq
  in Θ-vis-go P Q A (sil P₁) eqP breq′
... | react vP τcP =
  let breq′ : Θ-vis A (react vP τcP) Q at a ≡ just M
      breq′ = subst (λ g → g at a ≡ just M)
                    (sym (proj₁ (react-injective eqf)))
                    breq
  in Θ-vis-go P Q A (react vP τcP) eqP breq′

Θ-ev-elim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {A} {M} {e}
          → (P ⟦ A ▷ Q) ─[ ev e ]─► M → ΘevR P Q A M e
Θ-ev-elim P Q {A = A} (sRet eqf) = Θdone (Θ-force-ret-inv {P = P} {Q = Q} {A = A} eqf)
Θ-ev-elim P Q {A = A} (sVis {at = at} {a = a} eqf breq) = Θ-vis-inv P Q A eqf breq

-------------------------------------------------------------------------------------
-- Part 4: the INTRO (forward) step lemmas and the two DIVERGENCE directions for Throw.
--
-- HOISTED VERBATIM from `CSP.Laws.FD.ThrowFD` (which now re-exports them `public`, so its
-- API is unchanged).  They live here so that the FSim layer can reuse them without pulling
-- the whole FD law-suite — and with it the classical `Semantics.DRImpliesFD` — into its
-- import closure; this module is `--safe` clean and postulate-free.
-------------------------------------------------------------------------------------

-- P's τ-step lifts through the throw: (P ⟦ A ▷ Q) ─[τ]→ (P′ ⟦ A ▷ Q).
-- Throw's τ-space IS P's own τ-space (no pair-fin tag): Θ-τ reads `viewT (force P)`,
-- which is exactly what a P-τ exposes.  The forward analogue of Θ-τ-elim's source.
Θ-τ-lift-P : {P P′ Q : PTree E (ExtI E) R} {A : EventSet}
           → P ─[ τ ]─► P′ → (P ⟦ A ▷ Q) ─[ τ ]─► (P′ ⟦ A ▷ Q)
-- sSil: force P ≡ sil P′; viewT (sil P′) (_,fin) (lift fzero) = just P′, so
-- Θ-τ A (sil P′) Q (_,fin) (lift fzero) = just (P′ ⟦ A ▷ Q).
Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q} {A = A} (sSil eqP) =
  sTau {i = _ , fin {n = 1}} {a = lift fzero}
       (force-Θ-sil {P = P} {Q = Q} {A = A} eqP)
       (Θ-tag eqP)
  where
    Θ-tag : PTree.force P ≡ sil P′
          → Θ-τ A (sil P′) Q (_ , fin {n = 1}) (lift fzero) ≡ just (P′ ⟦ A ▷ Q)
    Θ-tag _ = refl
-- sTau: force P ≡ react v τc, τc i a ≡ just P′, and viewT (react v τc) i a = τc i a,
-- so Θ-τ A (react v τc) Q i a = just (P′ ⟦ A ▷ Q).
Θ-τ-lift-P {P = P} {P′ = P′} {Q = Q} {A = A} (sTau {v = v} {τc = τc} {i = i} {a = a} eqP brP) =
  sTau {i = i} {a = a}
       (force-Θ-react {P = P} {Q = Q} {A = A} eqP)
       (Θ-tag brP)
  where
    Θ-tag : τc i a ≡ just P′
          → Θ-τ A (react v τc) Q i a ≡ just (P′ ⟦ A ▷ Q)
    Θ-tag b rewrite b = refl

-- Diverges P lifts to Diverges (P ⟦ A ▷ Q).  COPATTERN form (guarded via .rest);
-- all case analysis is inside the with-free Θ-τ-lift-P.
Θ-Diverges-L : {P Q : PTree E (ExtI E) R} {A : EventSet}
             → Diverges P → Diverges (P ⟦ A ▷ Q)
Θ-Diverges-L {Q = Q} {A = A} divP .Diverges.next = (divP .Diverges.next) ⟦ A ▷ Q
Θ-Diverges-L {Q = Q} {A = A} divP .Diverges.step =
  Θ-τ-lift-P {P′ = divP .Diverges.next} {Q = Q} {A = A} (divP .Diverges.step)
Θ-Diverges-L {Q = Q} {A = A} divP .Diverges.rest = Θ-Diverges-L {Q = Q} {A = A} (divP .Diverges.rest)

-- one τ of (P ⟦ A ▷ Q) is a τ of P keeping the throw alive; reconstruct the residual
-- divergence at the SAME index (M ≡ P′ ⟦ A ▷ Q refines `rest`).  No case-split here.
Θ-div-step : {P Q : PTree E (ExtI E) R} {A : EventSet}
           → Diverges (P ⟦ A ▷ Q)
           → Σ[ P′ ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► P′) × Diverges (P′ ⟦ A ▷ Q))
Θ-div-step {P = P} {Q = Q} {A = A} d
  with Θ-τ-elim P Q (d .Diverges.step)
... | (P′ , sP , m≡) = P′ , sP , subst Diverges m≡ (d .Diverges.rest)

Θ-Diverges→ : {P Q : PTree E (ExtI E) R} {A : EventSet}
            → Diverges (P ⟦ A ▷ Q) → Diverges P
Θ-Diverges→ {P = P} {Q = Q} {A = A} d .Diverges.next =
  proj₁ (Θ-div-step {P = P} {Q = Q} {A = A} d)
Θ-Diverges→ {P = P} {Q = Q} {A = A} d .Diverges.step =
  proj₁ (proj₂ (Θ-div-step {P = P} {Q = Q} {A = A} d))
Θ-Diverges→ {P = P} {Q = Q} {A = A} d .Diverges.rest =
  Θ-Diverges→ {Q = Q} {A = A} (proj₂ (proj₂ (Θ-div-step {P = P} {Q = Q} {A = A} d)))

-- the throw fires: P offers an A-event, control transfers to X (P discarded).
-- The sVis carries `force P ≡ react v τc` and `v at a ≡ just P′` (= viewV (react …) at a);
-- force-Θ-react reduces force (P⟦A▷X) to react (Θ-vis …) …, and the tag lemma evaluates
-- Θ-vis at a (rewrite the offer, then the yes-branch of A .dec) to `just X`.
Θ-throw-step : {P P′ X : PTree E (ExtI E) R} {A : EventSet} {at : AnyTypes E} {a : proj₁ at}
             → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′ → A .mem at a
             → (P ⟦ A ▷ X) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► X
Θ-throw-step {P = P} {P′ = P′} {X = X} {A = A} {at = at} {a = a} (sVis {v = v} {τc = τc} eqP veq) m =
  sVis {at = at} {a = a}
       (force-Θ-react {P = P} {Q = X} {A = A} eqP)
       (Θ-vis-throw veq m)
  where
    Θ-vis-throw : v at a ≡ just P′ → A .mem at a → Θ-vis A (react v τc) X at a ≡ just X
    Θ-vis-throw vq mm rewrite vq with A .dec at a
    ... | yes _  = refl
    ... | no ¬m  = ⊥-elim (¬m mm)

-- the throw passes: P offers a non-A event, P continues under the throw.
Θ-pass-step : {P P′ X : PTree E (ExtI E) R} {A : EventSet} {at : AnyTypes E} {a : proj₁ at}
            → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P′ → ¬ (A .mem at a)
            → (P ⟦ A ▷ X) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P′ ⟦ A ▷ X)
Θ-pass-step {P = P} {P′ = P′} {X = X} {A = A} {at = at} {a = a} (sVis {v = v} {τc = τc} eqP veq) ¬m =
  sVis {at = at} {a = a}
       (force-Θ-react {P = P} {Q = X} {A = A} eqP)
       (Θ-vis-pass veq ¬m)
  where
    Θ-vis-pass : v at a ≡ just P′ → ¬ (A .mem at a)
               → Θ-vis A (react v τc) X at a ≡ just (P′ ⟦ A ▷ X)
    Θ-vis-pass vq ¬mm rewrite vq with A .dec at a
    ... | yes m  = ⊥-elim (¬mm m)
    ... | no  _  = refl


-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- INTERRUPT  `_△_`  LTS step-inversions.  Structurally analogous to Throw but with
-- TWO live operands (cf. □-τ-elim / □-ev-elim in TraceLawsExtChoiceMono): a τ-step is
-- P's τ, Q's τ, or Q's √-interrupt; a visible step is P's, Q's, or a both-offer ⊓.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-------------------------------------------------------------------------------------
-- Part 1: force-equation lemmas.  Re-doing `with PTree.force P | PTree.force Q` here
-- lets the `_△_` clause reduce; the NonRet args discharge the ret-firing clauses.
-------------------------------------------------------------------------------------

force-△-Pret : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {r}
             → PTree.force P ≡ ret r → PTree.force (P △ Q) ≡ react ∅v (br2 P Q)
force-△-Pret {P = P} {Q = Q} eqP with PTree.force P | PTree.force Q
... | ret _    | _        = case eqP of λ { refl → refl }
... | sil _    | _        = case eqP of λ ()
... | react _ _ | _        = case eqP of λ ()

force-△-LR : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {nP} {r′}
           → PTree.force P ≡ nP → PTree.force Q ≡ ret r′ → NonRet nP
           → PTree.force (P △ Q) ≡ react (△-merge-Qret nP Q) (△-slide-Qret nP Q)
force-△-LR {P = P} {Q = Q} eqP eqQ ntP with PTree.force P | PTree.force Q
... | ret _    | _        = ⊥-elim (subst NonRet (sym eqP) ntP)
... | sil _    | ret _    = case eqP of λ { refl → refl }
... | react _ _ | ret _    = case eqP of λ { refl → refl }
... | sil _    | sil _    = case eqQ of λ ()
... | sil _    | react _ _ = case eqQ of λ ()
... | react _ _ | sil _    = case eqQ of λ ()
... | react _ _ | react _ _ = case eqQ of λ ()

force-△-mt : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {nP nQ}
           → PTree.force P ≡ nP → PTree.force Q ≡ nQ → NonRet nP → NonRet nQ
           → PTree.force (P △ Q) ≡ react (△-merge nP nQ Q) (△-τ nP nQ P Q)
force-△-mt {P = P} {Q = Q} eqP eqQ ntP ntQ with PTree.force P | PTree.force Q
... | ret _    | _        = ⊥-elim (subst NonRet (sym eqP) ntP)
... | sil _    | ret _    = ⊥-elim (subst NonRet (sym eqQ) ntQ)
... | react _ _ | ret _    = ⊥-elim (subst NonRet (sym eqQ) ntQ)
... | sil _    | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | sil _    | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | sil _    = case eqP of λ { refl → case eqQ of λ { refl → refl } }
... | react _ _ | react _ _ = case eqP of λ { refl → case eqQ of λ { refl → refl } }

-------------------------------------------------------------------------------------
-- Part 2: τ-inversion.  A τ-step of P △ Q is P's τ (→ P′ △ Q), Q's τ (→ P △ Q′),
-- or Q's √-interrupt (Q terminated, slide tag0 → M ≡ Q).
-------------------------------------------------------------------------------------

data △τR {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) : PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  △τP    : ∀ {P′} → P ─[ τ ]─► P′ → △τR P Q (P′ △ Q)
  △τQ    : ∀ {Q′} → Q ─[ τ ]─► Q′ → △τR P Q (P △ Q′)
  △τQret : ∀ {r′} → PTree.force Q ≡ ret r′ → △τR P Q Q
  △τ⊓P   : ∀ {r}  → PTree.force P ≡ ret r → △τR P Q P     -- P⊓Q resolves to P (then terminates √r)
  △τ⊓Q   : ∀ {r}  → PTree.force P ≡ ret r → △τR P Q Q     -- P⊓Q resolves to Q (interrupt handler)

-- a `just M` out of △-slide-Qret (Q terminated) is the √-interrupt (M ≡ Q) or P's τ
△-slide-Qret-elim : (nP : NodeKind E (ExtI E) R) (Q : PTree E (ExtI E) R)
                      {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
                  → △-slide-Qret nP Q i a ≡ just M
                  → (M ≡ Q)
                  ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
                       (viewT nP j a' ≡ just P') × (M ≡ (P' △ Q)))
△-slide-Qret-elim nP Q {_ , base _}            eq = case eq of λ ()
△-slide-Qret-elim nP Q {_ , fin}               eq = case eq of λ ()
△-slide-Qret-elim nP Q {_ , pair (base _) _}   eq = case eq of λ ()
△-slide-Qret-elim nP Q {_ , pair (pair _ _) _} eq = case eq of λ ()
△-slide-Qret-elim nP Q {_ , pair fin j} {lift fzero        , a'} eq = inj₁ (sym (just-injective eq))
△-slide-Qret-elim nP Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nP (_ , j) a' in veq
... | just P' = inj₂ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
△-slide-Qret-elim nP Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- a `just M` out of △-τ (both live) is P's τ (→ P′ △ Q) or Q's τ (→ P △ Q′)
△-τ-source : (nP nQ : NodeKind E (ExtI E) R) (P Q : PTree E (ExtI E) R)
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
           → △-τ nP nQ P Q i a ≡ just M
           → (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ P' ∈ PTree E (ExtI E) R ]
                (viewT nP j a' ≡ just P') × (M ≡ (P' △ Q)))
           ⊎ (Σ[ j ∈ AnyTypes (ExtI E) ] Σ[ a' ∈ proj₁ j ] Σ[ Q' ∈ PTree E (ExtI E) R ]
                (viewT nQ j a' ≡ just Q') × (M ≡ (P △ Q')))
△-τ-source nP nQ P Q {_ , base _}            eq = case eq of λ ()
△-τ-source nP nQ P Q {_ , fin}               eq = case eq of λ ()
△-τ-source nP nQ P Q {_ , pair (base _) _}   eq = case eq of λ ()
△-τ-source nP nQ P Q {_ , pair (pair _ _) _} eq = case eq of λ ()
△-τ-source nP nQ P Q {_ , pair fin j} {lift fzero        , a'} eq with viewT nP (_ , j) a' in veq
... | just P' = inj₁ ((_ , j) , a' , P' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
△-τ-source nP nQ P Q {_ , pair fin j} {lift (fsuc fzero) , a'} eq with viewT nQ (_ , j) a' in veq
... | just Q' = inj₂ ((_ , j) , a' , Q' , veq , sym (just-injective eq))
... | nothing = case eq of λ ()
△-τ-source nP nQ P Q {_ , pair fin j} {lift (fsuc (fsuc _)) , a'} eq = case eq of λ ()

-- a `just M` out of `br2 P Q` (the P⊓Q node, fired when force P ≡ ret r): the
-- nondeterministic resolution to P (tag0) or Q (tag1).
br2-source : (P Q : PTree E (ExtI E) R)
               {i : AnyTypes (ExtI E)} {a : proj₁ i} {M : PTree E (ExtI E) R}
           → br2 P Q i a ≡ just M → (M ≡ P) ⊎ (M ≡ Q)
br2-source P Q {_ , base _}   eq = case eq of λ ()
br2-source P Q {_ , pair _ _} eq = case eq of λ ()
br2-source P Q {_ , fin} {a = lift fzero}               eq = inj₁ (sym (just-injective eq))
br2-source P Q {_ , fin} {a = lift (fsuc fzero)}        eq = inj₂ (sym (just-injective eq))
br2-source P Q {_ , fin} {a = lift (fsuc (fsuc _))}     eq = case eq of λ ()

△-τ-elim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
         → (P △ Q) ─[ τ ]─► M → △τR P Q M
△-τ-elim P Q step with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r  | _        = case react-τ-inv (force-△-Pret {P = P} {Q = Q} eqP) step of λ where
    (i , a , breq) → case br2-source P Q {i = i} {a = a} breq of λ where
      (inj₁ refl) → △τ⊓P eqP
      (inj₂ refl) → △τ⊓Q eqP
... | sil P₁ | ret r′    = case react-τ-inv (force-△-LR {P = P} {Q = Q} eqP eqQ tt) step of λ where
    (i , a , breq) → case △-slide-Qret-elim (sil P₁) Q {i = i} {a = a} breq of λ where
      (inj₁ refl)                     → △τQret eqQ
      (inj₂ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
... | react vP τcP | ret r′ = case react-τ-inv (force-△-LR {P = P} {Q = Q} eqP eqQ tt) step of λ where
    (i , a , breq) → case △-slide-Qret-elim (react vP τcP) Q {i = i} {a = a} breq of λ where
      (inj₁ refl)                     → △τQret eqQ
      (inj₂ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
... | sil P₁ | sil Q₁ = case react-τ-inv (force-△-mt {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case △-τ-source (sil P₁) (sil Q₁) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
      (inj₂ (j , a' , Q' , veq , refl)) → △τQ (viewT-τ eqQ veq)
... | sil P₁ | react vQ τcQ = case react-τ-inv (force-△-mt {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case △-τ-source (sil P₁) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
      (inj₂ (j , a' , Q' , veq , refl)) → △τQ (viewT-τ eqQ veq)
... | react vP τcP | sil Q₁ = case react-τ-inv (force-△-mt {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case △-τ-source (react vP τcP) (sil Q₁) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
      (inj₂ (j , a' , Q' , veq , refl)) → △τQ (viewT-τ eqQ veq)
... | react vP τcP | react vQ τcQ = case react-τ-inv (force-△-mt {P = P} {Q = Q} eqP eqQ tt tt) step of λ where
    (i , a , breq) → case △-τ-source (react vP τcP) (react vQ τcQ) P Q {i = i} {a = a} breq of λ where
      (inj₁ (j , a' , P' , veq , refl)) → △τP (viewT-τ eqP veq)
      (inj₂ (j , a' , Q' , veq , refl)) → △τQ (viewT-τ eqQ veq)

-------------------------------------------------------------------------------------
-- Part 3: ev/√-inversion.  A visible step of P △ Q is P's event (→ P₁ △ Q), Q's event
-- (the interrupt fires, → Q₁), a both-offer ⊓ (→ (P₁△Q) ⊓ Q₁ as the literal react),
-- or P's √ (Q dead-or-alive, → deadlock).
-------------------------------------------------------------------------------------

-- a `just P'` offer out of `viewV nP at a` is a real visible step of P.
-- viewV is ∅v on ret/sil (so just is impossible there); on react it is the vis-part,
-- and `sVis eqP` rebuilds the operand step. (cf. Throw's Θ-vis-go arm.)
viewV-ev : {P : PTree E (ExtI E) R} {nP : NodeKind E (ExtI E) R}
             {at : AnyTypes E} {a : proj₁ at} {P' : PTree E (ExtI E) R}
         → PTree.force P ≡ nP → viewV nP at a ≡ just P'
         → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P'
viewV-ev {nP = ret _}      eqP veq = case veq of λ ()
viewV-ev {nP = sil _}      eqP veq = case veq of λ ()
viewV-ev {nP = react v τc}  eqP veq = sVis eqP veq

data △evR {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) : PTree E (ExtI E) R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  △evP  : ∀ {at a P₁} → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
                      → △evR P Q (P₁ △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a))
  △evQ  : ∀ {at a Q₁} → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q₁
                      → △evR P Q Q₁ (evl (evLabel (proj₁ at) (proj₂ at) a))
  △evPQ : ∀ {at a P₁ Q₁} → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P₁
                         → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q₁
                         → △evR P Q (ptree (react ∅v (△-br2 P₁ Q Q₁))) (evl (evLabel (proj₁ at) (proj₂ at) a))

-- a `just M` out of △-merge-Qret (Q terminated): P offers it at `at a` (→ M ≡ P'△Q).
△-merge-Qret-source : (nP : NodeKind E (ExtI E) R) (Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                    → △-merge-Qret nP Q at a ≡ just M
                    → Σ[ P' ∈ PTree E (ExtI E) R ] (viewV nP at a ≡ just P') × (M ≡ (P' △ Q))
△-merge-Qret-source nP Q {at = at} {a = a} eq with viewV nP at a
... | just P' = P' , refl , sym (just-injective eq)
... | nothing = case eq of λ ()

-- a `just M` out of △-merge (both live): P-only offer (M ≡ P'△Q), Q-only offer
-- (interrupt fires, M ≡ Q'), or both-offer ⊓ (M ≡ the literal react node).
△-merge-source : (nP nQ : NodeKind E (ExtI E) R) (Q : PTree E (ExtI E) R)
                   {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
               → △-merge nP nQ Q at a ≡ just M
               → (Σ[ P' ∈ PTree E (ExtI E) R ] (viewV nP at a ≡ just P') × (viewV nQ at a ≡ nothing) × (M ≡ (P' △ Q)))
               ⊎ (Σ[ Q' ∈ PTree E (ExtI E) R ] (viewV nQ at a ≡ just Q') × (M ≡ Q'))
               ⊎ (Σ[ P' ∈ PTree E (ExtI E) R ] Σ[ Q' ∈ PTree E (ExtI E) R ]
                    (viewV nP at a ≡ just P') × (viewV nQ at a ≡ just Q')
                    × (M ≡ ptree (react ∅v (△-br2 P' Q Q'))))
△-merge-source nP nQ Q {at = at} {a = a} eq with viewV nP at a | viewV nQ at a
... | just P' | nothing = inj₁ (P' , refl , refl , sym (just-injective eq))
... | nothing | just Q' = inj₂ (inj₁ (Q' , refl , sym (just-injective eq)))
... | just P' | just Q' = inj₂ (inj₂ (P' , Q' , refl , refl , sym (just-injective eq)))
... | nothing | nothing = case eq of λ ()

-- Q terminated: the offer is △-merge-Qret nP Q; only a P-offer can fire (→ △evP).
-- `eqf` (force (P △ Q) ≡ react v τc, already reduced to react (△-merge-Qret nP Q) … by the
-- caller's `with` abstraction) re-types the sVis offer `breq` onto △-merge-Qret.
△-merge-Qret-case : (P Q : PTree E (ExtI E) R) (nP : NodeKind E (ExtI E) R)
                      {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  → PTree.force P ≡ nP
                  → v ≡ △-merge-Qret nP Q → v at a ≡ just M
                  → △evR P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
△-merge-Qret-case P Q nP {at = at} {a = a} {M = M} eqPnP veq breq =
  let breq′ : △-merge-Qret nP Q at a ≡ just M
      breq′ = subst (λ g → g at a ≡ just M) veq breq
  in case △-merge-Qret-source nP Q breq′ of λ where
       (P' , vveq , refl) → △evP {P₁ = P'} (viewV-ev eqPnP vveq)

-- both live: offer is △-merge nP nQ Q; P-only (△evP), Q-only (△evQ), or both (△evPQ).
△-merge-case : (P Q : PTree E (ExtI E) R) (nP nQ : NodeKind E (ExtI E) R)
                 {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R}
                 {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
             → PTree.force P ≡ nP → PTree.force Q ≡ nQ
             → v ≡ △-merge nP nQ Q → v at a ≡ just M
             → △evR P Q M (evl (evLabel (proj₁ at) (proj₂ at) a))
△-merge-case P Q nP nQ {at = at} {a = a} {M = M} eqPnP eqQnQ veq breq =
  let breq′ : △-merge nP nQ Q at a ≡ just M
      breq′ = subst (λ g → g at a ≡ just M) veq breq
  in case △-merge-source nP nQ Q breq′ of λ where
       (inj₁ (P' , vPeq , _ , refl))            → △evP {P₁ = P'} (viewV-ev eqPnP vPeq)
       (inj₂ (inj₁ (Q' , vQeq , refl)))         → △evQ {Q₁ = Q'} (viewV-ev eqQnQ vQeq)
       -- the index is the literal ptree (react ∅v (△-br2 P' Q Q')) ⇒ closes by refl
       -- (it is NOT definitionally (P'△Q) ⊓ Q': coinductive records lack η).
       (inj₂ (inj₂ (P' , Q' , vPeq , vQeq , refl))) →
         △evPQ {P₁ = P'} {Q₁ = Q'} (viewV-ev eqPnP vPeq) (viewV-ev eqQnQ vQeq)

△-ev-elim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {M} {e}
          → (P △ Q) ─[ ev e ]─► M → △evR P Q M e
-- A `sRet` step needs force (P △ Q) ≡ ret x, but every `_△_` clause produces an
-- `react` node (the P=ret clause is now P⊓Q = react ∅v (br2 P Q)).  So `sRet` is
-- impossible: re-run the force split so `force (P △ Q)` reduces to the relevant
-- react, then `react … ≡ ret x` is absurd.
△-ev-elim P Q (sRet eqf) with PTree.force P in eqP | PTree.force Q in eqQ
... | ret r      | _           = case eqf of λ ()
... | sil P₁     | ret r′       = case eqf of λ ()
... | react vP τcP | ret r′      = case eqf of λ ()
... | sil P₁     | sil Q₁       = case eqf of λ ()
... | sil P₁     | react vQ τcQ  = case eqf of λ ()
... | react vP τcP | sil Q₁      = case eqf of λ ()
... | react vP τcP | react vQ τcQ = case eqf of λ ()
-- The `with … in eqP/eqQ` abstraction reduces `force (P △ Q)` IN PLACE, so the sVis's
-- `eqf : force (P △ Q) ≡ react v τc` already presents the reduced node — `react-injective
-- eqf` then equates v with the merge offer used by △-merge[-Qret]-case (no force-△-*
-- lemma needed for the offer; sym of the proj₁ gives `v ≡ △-merge…`).
△-ev-elim P Q (sVis {at = at} {a = a} {t′ = M} eqf breq) with PTree.force P in eqP | PTree.force Q in eqQ
-- force (P △ Q) reduces in place to react ∅v (br2 P Q): the P⊓Q node offers NO visible
-- event (∅v), so the sVis offer `breq : v at a ≡ just M` becomes `∅v at a ≡ just M`,
-- i.e. `nothing ≡ just M` (react-injective eqf gives ∅v ≡ v).
... | ret r      | _          =
        case (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) breq) of λ ()
... | sil P₁     | ret r′      = △-merge-Qret-case P Q (sil P₁)      eqP     (sym (proj₁ (react-injective eqf))) breq
... | react vP τcP | ret r′     = △-merge-Qret-case P Q (react vP τcP) eqP     (sym (proj₁ (react-injective eqf))) breq
... | sil P₁     | sil Q₁      = △-merge-case P Q (sil P₁)      (sil Q₁)      eqP eqQ (sym (proj₁ (react-injective eqf))) breq
... | sil P₁     | react vQ τcQ = △-merge-case P Q (sil P₁)      (react vQ τcQ) eqP eqQ (sym (proj₁ (react-injective eqf))) breq
... | react vP τcP | sil Q₁     = △-merge-case P Q (react vP τcP) (sil Q₁)      eqP eqQ (sym (proj₁ (react-injective eqf))) breq
... | react vP τcP | react vQ τcQ = △-merge-case P Q (react vP τcP) (react vQ τcQ) eqP eqQ (sym (proj₁ (react-injective eqf))) breq
