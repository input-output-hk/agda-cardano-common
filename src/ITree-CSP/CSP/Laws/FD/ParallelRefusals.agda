{-# OPTIONS --guardedness #-}

-- Parallel refusals: the operational FOUNDATION for the parallel stable-failures law.
--
-- An immediate visible offer of `Par P Q` decomposes by the `A`-split rule:
--   • a shared (in `A`) event is offered  ⟺  BOTH operands offer it (evSync);
--   • an outside-`A` event is offered     ⟺  P offers it OR Q offers it (evL / evR / evBoth).
-- and a √ is offered ⟺ both operands have terminated (ev√).  These are the CONSTRUCTIVE
-- offer-inversion (Par-offer-elim / -√) and offer-introduction (Par-offer-sync /
-- -soloL / -soloR) lemmas — repackagings of the LTS-level Par-ev-elim / Par-sync and
-- the par-pVis-*-eq node equalities.  The refusal SET decomposition (which needs the
-- classical offer-LEM, like the König divergence step) is built on top of these.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.ParallelRefusals {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Refusals {E = E} {I = ExtI E} using (Offers; Refuses; deadlock-no-offer)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟
  using (Mg; Par-sync; fPar-er; fPar-re; fPar-nn)
open import CSP.Laws.Traces.TraceLawsParallelMono   E-≟
  using (Par-soloL-reach; Par-soloR-reach;
         par-hVisL-eq; par-hVisR-eq; par-pVis-soloL-eq; par-pVis-soloR-eq; par-pVis-both-eq)
open import CSP.Laws.Traces.TraceLawsParallelElim   E-≟
  using (ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim)
open import CSP.Laws.Traces.TraceLawsExtChoice      E-≟ using (NonRet)

private
  variable
    ℓ₁ ℓ₂ ℓs ℓx ℓa ℓb ℓc : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- OFFER ELIMINATION : a visible offer of Par P Q is a cs-split of operand offers.
-------------------------------------------------------------------------------------
Par-offer-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {f : E X} {a : X}
               → Offers (Par A merge P Q) (evl (evLabel X f a))
               → (   A .mem (X , f) a × Offers P (evl (evLabel X f a)) × Offers Q (evl (evLabel X f a)))
               ⊎ (¬ A .mem (X , f) a × (Offers P (evl (evLabel X f a)) ⊎ Offers Q (evl (evLabel X f a))))
Par-offer-elim A merge P Q (M , step) with Par-ev-elim A merge P Q step
... | evSync csat Pev Qev = inj₁ (csat , (_ , Pev) , (_ , Qev))
... | evL   ¬csat Pev     = inj₂ (¬csat , inj₁ (_ , Pev))
... | evR   ¬csat Qev     = inj₂ (¬csat , inj₂ (_ , Qev))
... | evBoth ¬csat Pev Qev = inj₂ (¬csat , inj₁ (_ , Pev))

-- a √-offer of Par P Q ⟺ both operands have terminated (force ≡ ret).
Par-offer-elim-√ : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                   {r : R}
                 → Offers (Par A merge P Q) (√ r)
                 → Σ[ r₁ ∈ R₁ ] Σ[ r₂ ∈ R₂ ]
                     (PTree.force P ≡ ret r₁ × PTree.force Q ≡ ret r₂ × r ≡ merge r₁ r₂)
Par-offer-elim-√ A merge P Q (M , step) with Par-ev-elim A merge P Q step
... | ev√ {r₁ = r₁} {r₂ = r₂} eqP eqQ = r₁ , r₂ , eqP , eqQ , refl

-------------------------------------------------------------------------------------
-- OFFER INTRODUCTION : rebuild a Par offer from the operands' offers + cs-status.
-------------------------------------------------------------------------------------
-- a shared (in `A`) event offered by BOTH operands is offered by the composite (one step).
Par-offer-sync : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {f : E X} {a : X}
               → A .mem (X , f) a
               → Offers P (evl (evLabel X f a)) → Offers Q (evl (evLabel X f a))
               → Offers (Par A merge P Q) (evl (evLabel X f a))
Par-offer-sync A merge P Q csat (P' , Pev) (Q' , Qev) =
  Par A merge P' Q' , Par-sync A merge P Q csat Pev Qev

-- an outside-`A` event offered by P (regardless of Q) is offered by the composite — a
-- SINGLE step (the first step of Par-soloL-reach: solo into Par P₁ Q, or, when Q also
-- offers it, into the both-offer overlap node).
Par-offer-soloL : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  {X : Set ℓ} {f : E X} {a : X}
                → ¬ A .mem (X , f) a → Offers P (evl (evLabel X f a))
                → Offers (Par A merge P Q) (evl (evLabel X f a))
Par-offer-soloL A merge P Q {X = X} {f = f} {a = a} ¬cs (P₁ , sVis {v = vP} {τc = τcP} eqP veqP)
  with PTree.force Q in eqQ
... | ret r₂ = _ , sVis (fPar-er A merge eqP eqQ)
                       (par-hVisL-eq A merge {vP = vP} Q {at = X , f} {a = a} ¬cs veqP)
... | sil Q' = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                       (par-pVis-soloL-eq A merge (react vP τcP) (sil Q') P Q
                                          {at = X , f} {a = a} ¬cs veqP refl)
... | react vQ τcQ with vQ (X , f) a in vqeq
...   | nothing = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                           (par-pVis-soloL-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                              {at = X , f} {a = a} ¬cs veqP vqeq)
...   | just Q₁ = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                           (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                             {at = X , f} {a = a} ¬cs veqP vqeq)

Par-offer-soloR : (A : EventSet) (merge : Mg R₁ R₂ R)
                  (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                  {X : Set ℓ} {f : E X} {a : X}
                → ¬ A .mem (X , f) a → Offers Q (evl (evLabel X f a))
                → Offers (Par A merge P Q) (evl (evLabel X f a))
Par-offer-soloR A merge P Q {X = X} {f = f} {a = a} ¬cs (Q₁ , sVis {v = vQ} {τc = τcQ} eqQ veqQ)
  with PTree.force P in eqP
... | ret r₁ = _ , sVis (fPar-re A merge eqP eqQ)
                       (par-hVisR-eq A merge P {vQ = vQ} {at = X , f} {a = a} ¬cs veqQ)
... | sil P' = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                       (par-pVis-soloR-eq A merge (sil P') (react vQ τcQ) P Q
                                          {at = X , f} {a = a} ¬cs refl veqQ)
... | react vP τcP with vP (X , f) a in vpeq
...   | nothing = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                           (par-pVis-soloR-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                              {at = X , f} {a = a} ¬cs vpeq veqQ)
...   | just P₁ = _ , sVis (fPar-nn A merge eqP eqQ tt tt)
                           (par-pVis-both-eq A merge (react vP τcP) (react vQ τcQ) P Q
                                             {at = X , f} {a = a} ¬cs vpeq veqQ)

-------------------------------------------------------------------------------------
-- THE REFUSAL-SET SPLIT.  A composite refusal X over Event√ R is a parallel split of
-- operand refusals XP (over R₁) and XQ (over R₂) by the `A`-rule on visible events:
--   • a shared (in `A`) event refused by the composite is refused by AT LEAST one operand;
--   • an outside-`A` event refused by the composite is refused by BOTH operands.
-- (Ticks are handled by the composite's own structure — a stable both-react Par offers
--  no √ — so ParRef leaves them unconstrained.)  Purely set-theoretic ⇒ associative.
-------------------------------------------------------------------------------------
MaxRef : (t : PTree E (ExtI E) R) → Event√ R → Set _
MaxRef t e = ¬ Offers t e

ParRef : (A : EventSet) → (Event√ R → Set ℓa) → (Event√ R₁ → Set ℓb) → (Event√ R₂ → Set ℓc)
       → Set (lsuc ℓ ⊔ ℓe ⊔ ℓa ⊔ ℓb ⊔ ℓc)
ParRef {R = R} {R₁ = R₁} {R₂ = R₂} A X XP XQ =
    (∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → X (evl (evLabel Y f a))
        → XP (evl (evLabel Y f a)) ⊎ XQ (evl (evLabel Y f a)))
  × (∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
        → XP (evl (evLabel Y f a)) × XQ (evl (evLabel Y f a)))

-------------------------------------------------------------------------------------
-- the classical offer-LEM, used ONLY for the cs-event split (an immediate offer is
-- decidable).  CERTIFIED sound from the single `dne` axiom in ClassicalFromLEM
-- (Derivation 6 — a plain LEM instance); postulated directly per the FD-layer convention.
-- (Off-cs and tick splits are CONSTRUCTIVE, via Par-offer-soloL/R and Par-offer-elim-√.)
-------------------------------------------------------------------------------------
postulate
  offer-LEM : (t : PTree E (ExtI E) R) (e : Event√ R) → Offers t e ⊎ ¬ Offers t e

-------------------------------------------------------------------------------------
-- STABLE-LEAF refusal ELIMINATION (both operands stable): the composite's maximal
-- refusal splits into the operands' maximal refusals.  Only the cs-clause is classical.
-------------------------------------------------------------------------------------
Par-Refuses-elim-both : (A : EventSet) (merge : Mg R₁ R₂ R)
                        (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                        {X : Event√ R → Set ℓx}
                      → isStable P* → isStable Q*
                      → Refuses (Par A merge P* Q*) X
                      → Refuses P* (MaxRef P*) × Refuses Q* (MaxRef Q*)
                        × ParRef A X (MaxRef P*) (MaxRef Q*)
Par-Refuses-elim-both A merge P* Q* stP stQ (_ , refC) =
    (stP , λ e me → me) , (stQ , λ e me → me) , (csCl , ncsCl)
  where
    csCl : ∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → _
         → MaxRef P* (evl (evLabel Y f a)) ⊎ MaxRef Q* (evl (evLabel Y f a))
    csCl f a csat Xe with offer-LEM Q* (evl (evLabel _ f a))
    ... | inj₂ ¬oQ = inj₂ ¬oQ
    ... | inj₁ oQ  = inj₁ λ oP → refC (evl (evLabel _ f a)) Xe
                                       (Par-offer-sync A merge P* Q* csat oP oQ)
    ncsCl : ∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → _
          → MaxRef P* (evl (evLabel Y f a)) × MaxRef Q* (evl (evLabel Y f a))
    ncsCl f a ¬csat Xe =
        (λ oP → refC (evl (evLabel _ f a)) Xe (Par-offer-soloL A merge P* Q* ¬csat oP))
      , (λ oQ → refC (evl (evLabel _ f a)) Xe (Par-offer-soloR A merge P* Q* ¬csat oQ))

-------------------------------------------------------------------------------------
-- stability plumbing (local copies of the ExtChoiceFD helpers) + Par-stable.
-------------------------------------------------------------------------------------
-- a stable state forces to an react node whose τ-branch function is everywhere nothing.
stable→react : {t : PTree E (ExtI E) R} → isStable t
            → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) ]
              Σ[ τc ∈ ((i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))) ]
                (PTree.force t ≡ react v τc × (∀ i a → τc i a ≡ nothing))
stable→react {t = t} st with PTree.force t | st
... | ret _    | lift ()
... | sil _    | lift ()
... | react v τc | h = v , τc , refl , h

-- a state whose force is ret is not stable.
stable-not-ret : {t : PTree E (ExtI E) R} {r : R} → PTree.force t ≡ ret r → isStable t → ⊥
stable-not-ret {t = t} eqf st with PTree.force t | st
... | ret _    | lift ()
... | sil _    | lift ()
... | react _ _ | _ = case eqf of λ ()

-- build stability from "the τ-branch function is everywhere nothing".
mk-stable : {t : PTree E (ExtI E) R}
            {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → PTree.force t ≡ react v τc → (∀ i a → τc i a ≡ nothing) → isStable t
mk-stable {t = t} eqf h with PTree.force t
... | react _ _ with refl ← eqf = h

-- the parallel of two stable operands is stable: both force to react (not ret/sil),
-- so Par lands in the general react|react node, and par-pTau is everywhere nothing
-- because each operand's own τ-branches are (viewT (react _ τc) = τc).
Par-stable : (A : EventSet) (merge : Mg R₁ R₂ R)
             (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
           → isStable P* → isStable Q* → isStable (Par A merge P* Q*)
Par-stable A merge P* Q* stP stQ
  with stable→react {t = P*} stP | stable→react {t = Q*} stQ
... | vP , τcP , eqP , hP | vQ , τcQ , eqQ , hQ =
      mk-stable {t = Par A merge P* Q*}
                (fPar-nn A merge {P = P*} {Q = Q*} eqP eqQ tt tt) pTauNothing
  where
    pTauNothing : ∀ i a → par-pTau A merge (react vP τcP) (react vQ τcQ) P* Q* i a ≡ nothing
    pTauNothing (_ , base _)            _              = refl
    pTauNothing (_ , fin)               _              = refl
    pTauNothing (_ , pair (base _) _)   _              = refl
    pTauNothing (_ , pair (pair _ _) _) _              = refl
    pTauNothing (_ , pair fin i) (lift fzero , a)        rewrite hP (_ , i) a = refl
    pTauNothing (_ , pair fin i) (lift (fsuc fzero) , a) rewrite hQ (_ , i) a = refl
    pTauNothing (_ , pair fin i) (lift (fsuc (fsuc _)) , a)                   = refl

-------------------------------------------------------------------------------------
-- STABLE-LEAF refusal INTRODUCTION (both operands stable): reassemble a composite
-- refusal X from the operand refusals XP, XQ and a ParRef split.  Constructive
-- (offer-elim contrapositive); the dual of Par-Refuses-elim-both.
-------------------------------------------------------------------------------------
Par-Refuses-intro-both : (A : EventSet) (merge : Mg R₁ R₂ R)
                         (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                         {X : Event√ R → Set ℓx} {XP : Event√ R₁ → Set ℓa} {XQ : Event√ R₂ → Set ℓb}
                       → isStable P* → isStable Q*
                       → Refuses P* XP → Refuses Q* XQ → ParRef A X XP XQ
                       → Refuses (Par A merge P* Q*) X
Par-Refuses-intro-both A merge P* Q* stP stQ (_ , refP) (_ , refQ) (csCl , ncsCl) =
    Par-stable A merge P* Q* stP stQ , noOffer
  where
    noOffer : ∀ e → _ → ¬ Offers (Par A merge P* Q*) e
    noOffer (evl (evLabel Y f a)) Xe oPar with Par-offer-elim A merge P* Q* oPar
    ... | inj₁ (csat , oP , oQ) =
            [ (λ xpf → refP (evl (evLabel Y f a)) xpf oP)
            , (λ xqf → refQ (evl (evLabel Y f a)) xqf oQ) ]′ (csCl f a csat Xe)
    ... | inj₂ (¬csat , inj₁ oP) =
            refP (evl (evLabel Y f a)) (proj₁ (ncsCl f a ¬csat Xe)) oP
    ... | inj₂ (¬csat , inj₂ oQ) =
            refQ (evl (evLabel Y f a)) (proj₂ (ncsCl f a ¬csat Xe)) oQ
    noOffer (√ r) Xe oPar with Par-offer-elim-√ A merge P* Q* oPar
    ... | r₁ , r₂ , eqP , _ , _ = stable-not-ret {t = P*} eqP stP

-------------------------------------------------------------------------------------
-- HALF-TERMINATED leaves (distributed termination).  When one operand has reached
-- `ret`, the composite is a par-hVisL/R node: it can NEITHER terminate (the joint √
-- needs both at ret) NOR fire any `A` event (the terminated side can't synchronise);
-- it offers exactly the OTHER operand's outside-`A` events.  So the terminated operand is
-- not a stable failure — it contributes "refuses all `A` events + √" — and the leaf
-- decomposition is just the live operand's refusal of the outside-`A` part of X.
-------------------------------------------------------------------------------------
-- a terminated state offers no visible (evl) event — only its √ (via sRet).
ret-no-vis-offer : {t : PTree E (ExtI E) R} {r : R} {A : Set ℓ} {f : E A} {a : A}
                 → PTree.force t ≡ ret r → ¬ Offers t (evl (evLabel A f a))
ret-no-vis-offer eqf (_ , sVis eqf′ _) = case trans (sym eqf) eqf′ of λ ()

-- the parallel of a terminated P and a stable Q is stable (par-hVisR, no τ since Q τ-free).
Par-stable-termL : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂) {r₁ : R₁}
                 → PTree.force P* ≡ ret r₁ → isStable Q* → isStable (Par A merge P* Q*)
Par-stable-termL A merge P* Q* eqP stQ with stable→react {t = Q*} stQ
... | vQ , τcQ , eqQ , hQ =
      mk-stable {t = Par A merge P* Q*}
                (fPar-re A merge {P = P*} {Q = Q*} eqP eqQ) hTauNothing
  where
    hTauNothing : ∀ i a → par-hTauR A merge P* τcQ i a ≡ nothing
    hTauNothing i a rewrite hQ i a = refl

Par-stable-termR : (A : EventSet) (merge : Mg R₁ R₂ R)
                   (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂) {r₂ : R₂}
                 → isStable P* → PTree.force Q* ≡ ret r₂ → isStable (Par A merge P* Q*)
Par-stable-termR A merge P* Q* stP eqQ with stable→react {t = P*} stP
... | vP , τcP , eqP , hP =
      mk-stable {t = Par A merge P* Q*}
                (fPar-er A merge {P = P*} {Q = Q*} eqP eqQ) hTauNothing
  where
    hTauNothing : ∀ i a → par-hTauL A merge τcP Q* i a ≡ nothing
    hTauNothing i a rewrite hP i a = refl

-- ELIM : a terminated-left composite's refusal yields the live (right) operand's
-- refusal of the outside-`A` part of X (`A` events + ticks are refused by the dead side).
Par-Refuses-elim-termL : (A : EventSet) (merge : Mg R₁ R₂ R)
                         (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                         {r₁ : R₁} {X : Event√ R → Set ℓx}
                       → PTree.force P* ≡ ret r₁ → isStable Q*
                       → Refuses (Par A merge P* Q*) X
                       → Refuses Q* (MaxRef Q*)
                         × (∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
                              → MaxRef Q* (evl (evLabel Y f a)))
Par-Refuses-elim-termL A merge P* Q* eqP stQ (_ , refW) =
    (stQ , λ e me → me)
  , λ f a ¬csat Xe oQ → refW (evl (evLabel _ f a)) Xe
                             (Par-offer-soloR A merge P* Q* ¬csat oQ)

Par-Refuses-elim-termR : (A : EventSet) (merge : Mg R₁ R₂ R)
                         (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                         {r₂ : R₂} {X : Event√ R → Set ℓx}
                       → isStable P* → PTree.force Q* ≡ ret r₂
                       → Refuses (Par A merge P* Q*) X
                       → Refuses P* (MaxRef P*)
                         × (∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
                              → MaxRef P* (evl (evLabel Y f a)))
Par-Refuses-elim-termR A merge P* Q* stP eqQ (_ , refW) =
    (stP , λ e me → me)
  , λ f a ¬csat Xe oP → refW (evl (evLabel _ f a)) Xe
                             (Par-offer-soloL A merge P* Q* ¬csat oP)

-- INTRO : reassemble a terminated-left composite's refusal from the live operand's
-- refusal of the outside-`A` part of X.  (`A` events are refused because the dead operand
-- can't synchronise; ticks because the composite is react, not ret.)
Par-Refuses-intro-termL : (A : EventSet) (merge : Mg R₁ R₂ R)
                          (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                          {r₁ : R₁} {X : Event√ R → Set ℓx} {XQ : Event√ R₂ → Set ℓb}
                        → PTree.force P* ≡ ret r₁ → isStable Q*
                        → Refuses Q* XQ
                        → (∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
                             → XQ (evl (evLabel Y f a)))
                        → Refuses (Par A merge P* Q*) X
Par-Refuses-intro-termL A merge P* Q* {r₁ = r₁} eqP stQ (_ , refQ) offcs =
    Par-stable-termL A merge P* Q* eqP stQ , noOffer
  where
    noOffer : ∀ e → _ → ¬ Offers (Par A merge P* Q*) e
    noOffer (evl (evLabel Y f a)) Xe oPar with Par-offer-elim A merge P* Q* oPar
    ... | inj₁ (_ , oP , _)        = ret-no-vis-offer eqP oP
    ... | inj₂ (_ , inj₁ oP)       = ret-no-vis-offer eqP oP
    ... | inj₂ (¬csat , inj₂ oQ)   = refQ (evl (evLabel Y f a)) (offcs f a ¬csat Xe) oQ
    noOffer (√ r) Xe oPar with Par-offer-elim-√ A merge P* Q* oPar
    ... | _ , _ , _ , eqQ , _ = stable-not-ret {t = Q*} eqQ stQ

Par-Refuses-intro-termR : (A : EventSet) (merge : Mg R₁ R₂ R)
                          (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                          {r₂ : R₂} {X : Event√ R → Set ℓx} {XP : Event√ R₁ → Set ℓa}
                        → isStable P* → PTree.force Q* ≡ ret r₂
                        → Refuses P* XP
                        → (∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → X (evl (evLabel Y f a))
                             → XP (evl (evLabel Y f a)))
                        → Refuses (Par A merge P* Q*) X
Par-Refuses-intro-termR A merge P* Q* {r₂ = r₂} stP eqQ (_ , refP) offcs =
    Par-stable-termR A merge P* Q* stP eqQ , noOffer
  where
    noOffer : ∀ e → _ → ¬ Offers (Par A merge P* Q*) e
    noOffer (evl (evLabel Y f a)) Xe oPar with Par-offer-elim A merge P* Q* oPar
    ... | inj₁ (_ , _ , oQ)        = ret-no-vis-offer eqQ oQ
    ... | inj₂ (¬csat , inj₁ oP)   = refP (evl (evLabel Y f a)) (offcs f a ¬csat Xe) oP
    ... | inj₂ (_ , inj₂ oQ)       = ret-no-vis-offer eqQ oQ
    noOffer (√ r) Xe oPar with Par-offer-elim-√ A merge P* Q* oPar
    ... | _ , _ , eqP , _ , _ = stable-not-ret {t = P*} eqP stP

-------------------------------------------------------------------------------------
-- UNIFORM stable-leaf refusal law (subsumes both-stable + half-terminated): the
-- ParRef split against the operands' MAXIMAL refusals holds for ANY stable Par,
-- because MaxRef of a terminated (ret) operand vacuously refuses every visible event
-- (ret offers only √).  This is the form the failures THREADING uses.
-------------------------------------------------------------------------------------
-- a stable state offers no √ (a √-offer is sRet, which needs force ≡ ret).
stable-no-√-offer : {t : PTree E (ExtI E) R} {r : R} → isStable t → ¬ Offers t (√ r)
stable-no-√-offer {t = t} st (_ , sRet eq) = stable-not-ret {t = t} eq st

-- ELIM (stability-free): a composite refusal routes to the operands' max-refusals.
Par-Refuses→ParRef : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                     {X : Event√ R → Set ℓx}
                   → Refuses (Par A merge P* Q*) X
                   → ParRef A X (MaxRef P*) (MaxRef Q*)
Par-Refuses→ParRef A merge P* Q* (_ , refC) = (csCl , ncsCl)
  where
    csCl : ∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → _
         → MaxRef P* (evl (evLabel Y f a)) ⊎ MaxRef Q* (evl (evLabel Y f a))
    csCl f a csat Xe with offer-LEM Q* (evl (evLabel _ f a))
    ... | inj₂ ¬oQ = inj₂ ¬oQ
    ... | inj₁ oQ  = inj₁ λ oP → refC (evl (evLabel _ f a)) Xe
                                       (Par-offer-sync A merge P* Q* csat oP oQ)
    ncsCl : ∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → _
          → MaxRef P* (evl (evLabel Y f a)) × MaxRef Q* (evl (evLabel Y f a))
    ncsCl f a ¬csat Xe =
        (λ oP → refC (evl (evLabel _ f a)) Xe (Par-offer-soloL A merge P* Q* ¬csat oP))
      , (λ oQ → refC (evl (evLabel _ f a)) Xe (Par-offer-soloR A merge P* Q* ¬csat oQ))

-- INTRO (needs only the COMPOSITE's stability): rebuild a composite refusal from a
-- ParRef split.  The √-case is discharged by stability (no operand casing needed).
ParRef→Par-Refuses : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P* : PTree E (ExtI E) R₁) (Q* : PTree E (ExtI E) R₂)
                     {X : Event√ R → Set ℓx}
                   → isStable (Par A merge P* Q*)
                   → ParRef A X (MaxRef P*) (MaxRef Q*)
                   → Refuses (Par A merge P* Q*) X
ParRef→Par-Refuses A merge P* Q* stPar (csCl , ncsCl) = stPar , noOffer
  where
    noOffer : ∀ e → _ → ¬ Offers (Par A merge P* Q*) e
    noOffer (evl (evLabel Y f a)) Xe oPar with Par-offer-elim A merge P* Q* oPar
    ... | inj₁ (csat , oP , oQ) = [ (λ np → np oP) , (λ nq → nq oQ) ]′ (csCl f a csat Xe)
    ... | inj₂ (¬csat , inj₁ oP) = proj₁ (ncsCl f a ¬csat Xe) oP
    ... | inj₂ (¬csat , inj₂ oQ) = proj₂ (ncsCl f a ¬csat Xe) oQ
    noOffer (√ r) Xe oPar = stable-no-√-offer {t = Par A merge P* Q*} stPar oPar

-------------------------------------------------------------------------------------
-- MaxRef-of-Par connection + ParRef reassociation (for parallel associativity).
-- maxref-par-* BUILD a composite max-refusal from the operands' (offer-elim, no
-- stability); ParRef-build-R/L re-bracket the cs-split via these + the free inner ParRef.
-------------------------------------------------------------------------------------
maxref-par-cs : (A : EventSet) (merge : Mg R₁ R₂ R)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                {X : Set ℓ} {f : E X} {a : X}
              → A .mem (X , f) a → MaxRef P (evl (evLabel X f a)) ⊎ MaxRef Q (evl (evLabel X f a))
              → MaxRef (Par A merge P Q) (evl (evLabel X f a))
maxref-par-cs A merge P Q csat sm oPar with Par-offer-elim A merge P Q oPar
... | inj₁ (_ , oP , oQ)     = [ (λ mP → mP oP) , (λ mQ → mQ oQ) ]′ sm
... | inj₂ (¬csat , _)       = ⊥-elim (¬csat csat)

maxref-par-ncs : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {X : Set ℓ} {f : E X} {a : X}
               → ¬ A .mem (X , f) a
               → MaxRef P (evl (evLabel X f a)) → MaxRef Q (evl (evLabel X f a))
               → MaxRef (Par A merge P Q) (evl (evLabel X f a))
maxref-par-ncs A merge P Q ¬csat mP mQ oPar with Par-offer-elim A merge P Q oPar
... | inj₁ (csat , _ , _)    = ⊥-elim (¬csat csat)
... | inj₂ (_ , inj₁ oP)     = mP oP
... | inj₂ (_ , inj₂ oQ)     = mQ oQ

-- re-bracket the cs-split of a composite refusal X from (P∥Q,R) to (P,Q∥R).  The
-- (P∥Q)-refusal set A_PQ is ABSTRACT (the inner ParRef is supplied), so no (P∥Q)*≡Par
-- P* Q* identity is needed — A_PQ is whatever the inner Par-failures-elim produced.
ParRef-build-R : (A : EventSet) (merge : Mg R R R)
                 (P* Q* R* : PTree E (ExtI E) R)
                 {X : Event√ R → Set ℓx} (A_PQ : Event√ R → Set ℓa)
               → ParRef A X A_PQ (MaxRef R*)
               → ParRef A A_PQ (MaxRef P*) (MaxRef Q*)
               → ParRef A X (MaxRef P*) (MaxRef (Par A merge Q* R*))
ParRef-build-R A merge P* Q* R* A_PQ (oCs , oNcs) (iCs , iNcs) = (csCl , ncsCl)
  where
    csCl : ∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → _
         → MaxRef P* (evl (evLabel Y f a)) ⊎ MaxRef (Par A merge Q* R*) (evl (evLabel Y f a))
    csCl f a csat Xe with oCs f a csat Xe
    ... | inj₂ mR = inj₂ (maxref-par-cs A merge Q* R* csat (inj₂ mR))
    ... | inj₁ mPQ with iCs f a csat mPQ
    ...   | inj₁ mP = inj₁ mP
    ...   | inj₂ mQ = inj₂ (maxref-par-cs A merge Q* R* csat (inj₁ mQ))
    ncsCl : ∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → _
          → MaxRef P* (evl (evLabel Y f a)) × MaxRef (Par A merge Q* R*) (evl (evLabel Y f a))
    ncsCl f a ¬csat Xe with oNcs f a ¬csat Xe
    ... | mPQ , mR with iNcs f a ¬csat mPQ
    ...   | mP , mQ = mP , maxref-par-ncs A merge Q* R* ¬csat mQ mR

-- mirror: re-bracket from (P,Q∥R) to (P∥Q,R) (the Q∥R-refusal set A_QR abstract).
ParRef-build-L : (A : EventSet) (merge : Mg R R R)
                 (P* Q* R* : PTree E (ExtI E) R)
                 {X : Event√ R → Set ℓx} (A_QR : Event√ R → Set ℓa)
               → ParRef A X (MaxRef P*) A_QR
               → ParRef A A_QR (MaxRef Q*) (MaxRef R*)
               → ParRef A X (MaxRef (Par A merge P* Q*)) (MaxRef R*)
ParRef-build-L A merge P* Q* R* A_QR (oCs , oNcs) (iCs , iNcs) = (csCl , ncsCl)
  where
    csCl : ∀ {Y} (f : E Y) (a : Y) → A .mem (Y , f) a → _
         → MaxRef (Par A merge P* Q*) (evl (evLabel Y f a)) ⊎ MaxRef R* (evl (evLabel Y f a))
    csCl f a csat Xe with oCs f a csat Xe
    ... | inj₁ mP = inj₁ (maxref-par-cs A merge P* Q* csat (inj₁ mP))
    ... | inj₂ mQR with iCs f a csat mQR
    ...   | inj₁ mQ = inj₁ (maxref-par-cs A merge P* Q* csat (inj₂ mQ))
    ...   | inj₂ mR = inj₂ mR
    ncsCl : ∀ {Y} (f : E Y) (a : Y) → ¬ A .mem (Y , f) a → _
          → MaxRef (Par A merge P* Q*) (evl (evLabel Y f a)) × MaxRef R* (evl (evLabel Y f a))
    ncsCl f a ¬csat Xe with oNcs f a ¬csat Xe
    ... | mP , mQR with iNcs f a ¬csat mQR
    ...   | mQ , mR = maxref-par-ncs A merge P* Q* ¬csat mP mQ , mR
