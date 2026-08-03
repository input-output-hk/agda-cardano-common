{-# OPTIONS --guardedness #-}

-- Failures-divergences theory of interrupt `_△_`, the SKIP / ret row of UCS Fig 13.6:
-- when P can terminate immediately (force P ≡ ret r), the interrupt collapses to a
-- pure internal choice, i.e.  P △ Q ≈FD P ⊓ Q.
--
-- The proof is a one-liner once we observe `force (P △ Q) ≡ force (P ⊓ Q)`
-- (both are `react ∅v (br2 P Q)` when P terminates).  Equal-force trees are strongly
-- bisimilar (sbisim-force-eq), and strong bisim ⇒ ≈FD via sbisim→drbisim then
-- drbisim→≈FD.

open import Level using (Level; Lift; lift; lower)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to tt0)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees

module CSP.Laws.FD.InterruptFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Bisim               {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; _⊑F⊥_; _⊑D_; _⊑FD_; IsDivergence; divergences; failures⊥; div-extension-closed)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.Failures            {E = E} {I = ExtI E} using (failures)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E}
  using (drbisim→≈FD; stable-no-τ; isStable-force-eq)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
-- prefix / visible-menu non-divergence (canonical versions; used to be duplicated here)
open import CSP.Laws.DivFree.Closure E-≟ using (prefix-no-Diverges; pchoice-no-Diverges)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsThrowInterrupt E-≟
  using (force-△-Pret; force-△-LR; force-△-mt;
         △τR; △τP; △τQ; △τQret; △τ⊓P; △τ⊓Q; △-τ-elim;
         △evR; △evP; △evQ; △evPQ; △-ev-elim)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-div→; ⊓-div←l; ⊓-div←r;
         ⊓-failures→; ⊓-failures←l; ⊓-failures←r;
         ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)
open import CSP.Laws.FD.InterruptDivergence E-≟ using (△-Diverges→)
open import CSP.Laws.FD.ExtChoiceDivergence E-≟ using (▷-Diverges→)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; ▷-ev-elim; ▷-timeout)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-react)
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans)

-------------------------------------------------------------------------------------
-- Step 1: two trees with equal `force` are strongly bisimilar.
-- Every LTS step is determined by `PTree.force` (each constructor carries a
-- `PTree.force p ≡ <node>` premise), so a step of `t` transports to the SAME step
-- of `u` to the SAME target by rewriting the force-premise across the equality.

sbisim-force-eq : ∀ {ℓr} {R : Set ℓr} {t u : PTree E (ExtI E) R}
                → PTree.force t ≡ PTree.force u → Sbisim R t u
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev (sRet feq)    = _ , sRet (trans (sym eq) feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev (sVis feq br) = _ , sVis (trans (sym eq) feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau (sSil feq)   = _ , sSil (trans (sym eq) feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau (sTau feq br) = _ , sTau (trans (sym eq) feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev (sRet feq)    = _ , sRet (trans eq feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev (sVis feq br) = _ , sVis (trans eq feq) br , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau (sSil feq)   = _ , sSil (trans eq feq) , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau (sTau feq br) = _ , sTau (trans eq feq) br , sbisim-refl _

-------------------------------------------------------------------------------------
-- Step 2: the law.  force-△-Pret gives `force (P △ Q) ≡ react ∅v (br2 P Q)`, and
-- `force (P ⊓ Q)` is definitionally `react ∅v (br2 P Q)`, so the forces agree.

△-Pret-⊓ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R} {r}
         → PTree.force P ≡ ret r → (P △ Q) ≈FD (P ⊓ Q)
△-Pret-⊓ {P = P} {Q = Q} eqP =
  drbisim→≈FD (sbisim→drbisim (sbisim-force-eq (force-△-Pret {P = P} {Q = Q} eqP)))

-------------------------------------------------------------------------------------
-- Step 3: SKIP corollary.  Skip = Ret tt, so force Skip = ret tt and eqP = refl.

Skip-△-⊓ : ∀ {ℓr} {Q : PTree E (ExtI E) (⊤ {ℓr})} → (Skip △ Q) ≈FD (Skip ⊓ Q)
Skip-△-⊓ {Q = Q} = △-Pret-⊓ {P = Skip} {Q = Q} refl

-------------------------------------------------------------------------------------
-- The DIV row of UCS Fig 13.6: when P diverges, both P △ Q and P ⊓ Q root-diverge,
-- so both are ⊥ in the FD model and hence ≈FD.
-------------------------------------------------------------------------------------

-- (1) a root-divergent process diverges on EVERY trace: take the empty prefix.
root-div→all-div : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} {s}
                 → Diverges P → divergences P s
root-div→all-div {P = P} {s = s} divP = record
  { prefix  = []
  ; suffix  = s
  ; split   = refl
  ; witness = P
  ; reach   = ⟹-refl
  ; divwit  = divP
  }

-- (2) two root-divergent processes are FD-equivalent: each refusal/divergence claim
-- is discharged by the divergence summand of failures⊥ (and by all-div for ⊑D).
root-div→≈FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
             → Diverges P → Diverges Q → P ≈FD Q
root-div→≈FD {P = P} {Q = Q} divP divQ =
  ( ( (λ _ → inj₂ (root-div→all-div divP))     -- P ⊑F⊥ Q
    , (λ _ → root-div→all-div divP) )           -- P ⊑D  Q
  , ( (λ _ → inj₂ (root-div→all-div divQ))     -- Q ⊑F⊥ P
    , (λ _ → root-div→all-div divQ) ) )         -- Q ⊑D  P

-------------------------------------------------------------------------------------
-- (3) P's τ-step lifts through the interrupt: (P △ Q) ─[τ]→ (P′ △ Q).
-- A P-τ exposes `viewT (force P) j a ≡ just P′`; the interrupt's τ-part fires this on
-- tag0 (`lift fzero`) when Q is live (△-τ) or on tag1 (`lift (fsuc fzero)`) when Q has
-- terminated (△-slide-Qret).  The forward analogue of △-τ-elim's △τP arm.
-------------------------------------------------------------------------------------

-- shared continuation: given P's viewT-witness, build the lifted τ-step of P △ Q.
△-τ-lift-go : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E (ExtI E) R}
                {nP : NodeKind E (ExtI E) R} {j : AnyTypes (ExtI E)} {a : proj₁ j}
            → PTree.force P ≡ nP → NonRet nP → viewT nP j a ≡ just P′
            → (P △ Q) ─[ τ ]─► (P′ △ Q)
△-τ-lift-go {P = P} {Q = Q} {P′ = P′} {nP = nP} {j = _ , jj} {a = a} eqP ntP veq
  with PTree.force Q in eqQ
... | ret r′ =
  -- Q terminated: P's τ is on △-slide-Qret tag1 (lift (fsuc fzero))
  sTau {i = _ , pair (fin {n = 2}) jj} {a = lift (fsuc fzero) , a}
       (force-△-LR {P = P} {Q = Q} eqP eqQ ntP)
       (△-slide-tag1 veq)
  where
    △-slide-tag1 : viewT nP (_ , jj) a ≡ just P′
                 → △-slide-Qret nP Q (_ , pair (fin {n = 2}) jj) (lift (fsuc fzero) , a) ≡ just (P′ △ Q)
    △-slide-tag1 v rewrite v = refl
... | sil Q₁ =
  -- Q live: P's τ is on △-τ tag0 (lift fzero)
  sTau {i = _ , pair (fin {n = 2}) jj} {a = lift fzero , a}
       (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
       (△-mt-tag0 veq)
  where
    △-mt-tag0 : viewT nP (_ , jj) a ≡ just P′
              → △-τ nP (sil Q₁) P Q (_ , pair (fin {n = 2}) jj) (lift fzero , a) ≡ just (P′ △ Q)
    △-mt-tag0 v rewrite v = refl
... | react vQ τcQ =
  sTau {i = _ , pair (fin {n = 2}) jj} {a = lift fzero , a}
       (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
       (△-mt-tag0 veq)
  where
    △-mt-tag0 : viewT nP (_ , jj) a ≡ just P′
              → △-τ nP (react vQ τcQ) P Q (_ , pair (fin {n = 2}) jj) (lift fzero , a) ≡ just (P′ △ Q)
    △-mt-tag0 v rewrite v = refl

△-τ-lift-P : ∀ {ℓr} {R : Set ℓr} {P P′ Q : PTree E (ExtI E) R}
           → P ─[ τ ]─► P′ → (P △ Q) ─[ τ ]─► (P′ △ Q)
-- sSil: force P ≡ sil P′; viewT (sil P′) (_ , fin) (lift fzero) = oneτ P′ … = just P′
△-τ-lift-P {P′ = P′} {Q = Q} (sSil eqP) =
  △-τ-lift-go {Q = Q} {j = _ , fin {n = 1}} {a = lift fzero} eqP tt0 refl
-- sTau: force P ≡ react v τc, τc j a ≡ just P′, and viewT (react v τc) j a = τc j a
△-τ-lift-P {Q = Q} (sTau {i = j} {a = a} eqP brP) =
  △-τ-lift-go {Q = Q} {j = j} {a = a} eqP tt0 brP

-------------------------------------------------------------------------------------
-- (4) Diverges P lifts to Diverges (P △ Q).  COPATTERN form so the corecursion is
-- guarded; all case analysis is inside the with-free △-τ-lift-P.
-------------------------------------------------------------------------------------

△-Diverges-L : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
             → Diverges P → Diverges (P △ Q)
△-Diverges-L {Q = Q} divP .Diverges.next = (divP .Diverges.next) △ Q
△-Diverges-L {Q = Q} divP .Diverges.step =
  △-τ-lift-P {P′ = divP .Diverges.next} {Q = Q} (divP .Diverges.step)
△-Diverges-L {Q = Q} divP .Diverges.rest = △-Diverges-L {Q = Q} (divP .Diverges.rest)

-------------------------------------------------------------------------------------
-- (5) Diverges P lifts to Diverges (P ⊓ Q)  [trivial: P⊓Q ─τ→ P, then P diverges].
-------------------------------------------------------------------------------------

⊓-Diverges-L : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
             → Diverges P → Diverges (P ⊓ Q)
⊓-Diverges-L {P = P}         divP .Diverges.next = P
⊓-Diverges-L {P = P} {Q = Q} divP .Diverges.step = ⊓-stepL P Q
⊓-Diverges-L                 divP .Diverges.rest = divP

-------------------------------------------------------------------------------------
-- (6) the div row.
-------------------------------------------------------------------------------------

△-div-row : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
          → Diverges P → (P △ Q) ≈FD (P ⊓ Q)
△-div-row {P = P} {Q = Q} divP =
  root-div→≈FD (△-Diverges-L {P = P} {Q = Q} divP) (⊓-Diverges-L {P = P} {Q = Q} divP)


private
  variable
    ℓr : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- (7) Q's τ-step lifts through the interrupt: (P △ Q) ─[τ]→ (P △ Q′), when P is live.
-- Both operands run; Q's τ fires on △-τ's tag1 (lift (fsuc fzero)).  Mirror of
-- △-τ-lift-go but on the RIGHT operand.  Needs P (and Q) NonRet.
-------------------------------------------------------------------------------------

△-τ-lift-Q-go : ∀ {P Q Q′ : PTree E (ExtI E) R}
                  {nP nQ : NodeKind E (ExtI E) R} {j : AnyTypes (ExtI E)} {a : proj₁ j}
              → PTree.force P ≡ nP → NonRet nP
              → PTree.force Q ≡ nQ → NonRet nQ → viewT nQ j a ≡ just Q′
              → (P △ Q) ─[ τ ]─► (P △ Q′)
△-τ-lift-Q-go {P = P} {Q = Q} {Q′ = Q′} {nP = nP} {nQ = nQ} {j = _ , jj} {a = a}
              eqP ntP eqQ ntQ veq =
  sTau {i = _ , pair (fin {n = 2}) jj} {a = lift (fsuc fzero) , a}
       (force-△-mt {P = P} {Q = Q} eqP eqQ ntP ntQ)
       (△-τ-tag1 veq)
  where
    △-τ-tag1 : viewT nQ (_ , jj) a ≡ just Q′
             → △-τ nP nQ P Q (_ , pair (fin {n = 2}) jj) (lift (fsuc fzero) , a) ≡ just (P △ Q′)
    △-τ-tag1 v rewrite v = refl

△-τ-lift-Q : ∀ {P Q Q′ : PTree E (ExtI E) R}
           → NonRet (PTree.force P) → Q ─[ τ ]─► Q′ → (P △ Q) ─[ τ ]─► (P △ Q′)
△-τ-lift-Q ntP (sSil eqQ) =
  △-τ-lift-Q-go {j = _ , fin {n = 1}} {a = lift fzero} refl ntP eqQ tt0 refl
△-τ-lift-Q ntP (sTau {i = j} {a = a} eqQ brQ) =
  △-τ-lift-Q-go {j = j} {a = a} refl ntP eqQ tt0 brQ

-------------------------------------------------------------------------------------
-- (8) Diverges Q lifts to Diverges (P △ Q).  force P ≡ ret ⇒ P△Q = P⊓Q ─τ→ Q (br2
-- tag1) then Diverges Q; P live ⇒ lift Q's τ-chain via △-τ-lift-Q.  COPATTERN form.
-------------------------------------------------------------------------------------

-- force P ≡ ret r ⇒ P△Q ─τ→ Q (the br2 tag1).
△-τ-Pret-toQ : (P Q : PTree E (ExtI E) R) {r : R}
             → PTree.force P ≡ ret r → (P △ Q) ─[ τ ]─► Q
△-τ-Pret-toQ P Q eqP =
  sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
       (force-△-Pret {P = P} {Q = Q} eqP) refl

-- P live throughout: each Q-τ fires △-τ's tag1, keeping force P NonRet fixed.
△-Diverges-R-live : (P Q : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
                  → PTree.force P ≡ nP → NonRet nP → Diverges Q → Diverges (P △ Q)
△-Diverges-R-live P Q eqP ntP d .Diverges.next = P △ (d .Diverges.next)
△-Diverges-R-live P Q eqP ntP d .Diverges.step =
  △-τ-lift-Q {P = P} (subst NonRet (sym eqP) ntP) (d .Diverges.step)
△-Diverges-R-live P Q eqP ntP d .Diverges.rest =
  △-Diverges-R-live P _ eqP ntP (d .Diverges.rest)

△-Diverges-R : ∀ {P Q : PTree E (ExtI E) R} → Diverges Q → Diverges (P △ Q)
△-Diverges-R {P = P} {Q = Q} d with PTree.force P in eqP
... | ret r    = record { next = Q ; step = △-τ-Pret-toQ P Q eqP ; rest = d }
... | sil _    = △-Diverges-R-live P Q eqP tt0 d
... | react _ _ = △-Diverges-R-live P Q eqP tt0 d

-------------------------------------------------------------------------------------
-- (9) divergence-record plumbing.
-------------------------------------------------------------------------------------

div-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)}
              → P ─[ τ ]─► P′ → divergences P′ s → divergences P s
div-τ-prepend step d = record
  { prefix = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = d .IsDivergence.split  ; witness = d .IsDivergence.witness
  ; reach  = ⟹-τ step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

div-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
               → P ─[ ev e ]─► P′ → divergences P′ s → divergences P (e ∷ s)
div-ev-prepend {e = e} step d = record
  { prefix = e ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (e ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = ⟹-ev step (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

-- divergence reached from a longer big-step to a fresh witness (prefix = whole trace).
mk-div-from : {P W : PTree E (ExtI E) R} {pre : List (Event√ R)}
            → P ⟹⟨ pre ⟩ W → Diverges W → divergences P pre
mk-div-from {pre = pre} reach divw = record
  { prefix = pre ; suffix = [] ; split = sym (++-identityʳ pre)
  ; witness = _ ; reach = reach ; divwit = divw }

-------------------------------------------------------------------------------------
-- (10) the ⊓ König step is trivial: P₁⊓P₂'s only τ-targets are P₁,P₂.
-------------------------------------------------------------------------------------

⊓-Diverges→ : {P₁ P₂ : PTree E (ExtI E) R}
            → Diverges (P₁ ⊓ P₂) → Diverges P₁ ⊎ Diverges P₂
⊓-Diverges→ {P₁ = P₁} {P₂ = P₂} d with ⊓-τ-inv P₁ P₂ (d .Diverges.step)
... | inj₁ eq = inj₁ (subst Diverges eq (d .Diverges.rest))
... | inj₂ eq = inj₂ (subst Diverges eq (d .Diverges.rest))

-------------------------------------------------------------------------------------
-- Part 3a: the EASY direction.
-- divergences ((P₁△Q)⊓(P₂△Q)) s → divergences ((P₁⊓P₂)△Q) s.  ⊓-div→ splits; prepend
-- the ⊓-resolving τ (P₁⊓P₂)△Q ─τ→ Pᵢ△Q (= △-τ-lift-P (⊓-stepL/R)).
-------------------------------------------------------------------------------------

△-⊓L-dist-⊑D : (P₁ P₂ Q : PTree E (ExtI E) R)
             → ((P₁ ⊓ P₂) △ Q) ⊑D ((P₁ △ Q) ⊓ (P₂ △ Q))
△-⊓L-dist-⊑D P₁ P₂ Q d with ⊓-div→ (P₁ △ Q) (P₂ △ Q) d
... | inj₁ dP₁ = div-τ-prepend (△-τ-lift-P {Q = Q} (⊓-stepL P₁ P₂)) dP₁
... | inj₂ dP₂ = div-τ-prepend (△-τ-lift-P {Q = Q} (⊓-stepR P₁ P₂)) dP₂

-------------------------------------------------------------------------------------
-- Part 3b: the HARD direction, via a distribution-specific elim.  Helpers first.
-------------------------------------------------------------------------------------

-- bridge: force P ≡ ret r ⇒ divergences (P△Q) ↔ divergences (P⊓Q) (from △-Pret-⊓).
△-to-⊓ : (P Qa : PTree E (ExtI E) R) {r : R} {s : List (Event√ R)}
       → PTree.force P ≡ ret r → divergences (P △ Qa) s → divergences (P ⊓ Qa) s
△-to-⊓ P Qa eqP = proj₂ (proj₂ (△-Pret-⊓ {P = P} {Q = Qa} eqP))

⊓-to-△ : (P Qa : PTree E (ExtI E) R) {r : R} {s : List (Event√ R)}
       → PTree.force P ≡ ret r → divergences (P ⊓ Qa) s → divergences (P △ Qa) s
⊓-to-△ P Qa eqP = proj₂ (proj₁ (△-Pret-⊓ {P = P} {Q = Qa} eqP))

-- (Pᵢ△Q′) divergence → (Pᵢ△Q) divergence, prepending Q's τ.  Pᵢ live: △-τ-lift-Q.
-- force Pᵢ ≡ ret r: Pᵢ△ · = Pᵢ⊓ · (≈FD); split with ⊓-div→ — Pᵢ-divergence transfers
-- back unchanged (⊓-div←l), Q′-divergence prepends Q─τ→Q′ first (⊓-div←r).
△-τ-prepend-Q : (Pᵢ Qa Qa′ : PTree E (ExtI E) R) {s : List (Event√ R)}
              → Qa ─[ τ ]─► Qa′ → divergences (Pᵢ △ Qa′) s → divergences (Pᵢ △ Qa) s
△-τ-prepend-Q Pᵢ Qa Qa′ sQa d with PTree.force Pᵢ in eqPi
... | sil _    = div-τ-prepend (△-τ-lift-Q {P = Pᵢ} (subst NonRet (sym eqPi) tt0) sQa) d
... | react _ _ = div-τ-prepend (△-τ-lift-Q {P = Pᵢ} (subst NonRet (sym eqPi) tt0) sQa) d
... | ret r    with ⊓-div→ Pᵢ Qa′ (△-to-⊓ Pᵢ Qa′ eqPi d)
...   | inj₁ dPi  = ⊓-to-△ Pᵢ Qa eqPi (⊓-div←l Pᵢ Qa dPi)
...   | inj₂ dQa′ = ⊓-to-△ Pᵢ Qa eqPi (⊓-div←r Pᵢ Qa (div-τ-prepend sQa dQa′))

-- force Q ≡ ret r′ ⇒ (P △ Q) ─τ→ Q (the √-interrupt commit), for ANY P: P live fires
-- the slide tag0, P=ret fires the br2 tag1.
△-toQ-Qret : (P Q : PTree E (ExtI E) R) {r′ : R}
           → PTree.force Q ≡ ret r′ → (P △ Q) ─[ τ ]─► Q
△-toQ-Qret P Q eqQ with PTree.force P in eqP
... | ret r    = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
                      (force-△-Pret {P = P} {Q = Q} eqP) refl
... | sil _    = sTau {i = _ , pair (fin {n = 2}) (fin {n = 1})} {a = lift fzero , lift fzero}
                      (force-△-LR {P = P} {Q = Q} eqP eqQ tt0) refl
... | react _ _ = sTau {i = _ , pair (fin {n = 2}) (fin {n = 1})} {a = lift fzero , lift fzero}
                      (force-△-LR {P = P} {Q = Q} eqP eqQ tt0) refl

-- P₁⊓P₂ offers no visible event ⇒ a P-event step is impossible.
⊓-ev-impossible : (P₁ P₂ : PTree E (ExtI E) R) {e : Event√ R} {M : PTree E (ExtI E) R}
                → (P₁ ⊓ P₂) ─[ ev e ]─► M → ⊥
⊓-ev-impossible P₁ P₂ (sRet ())
⊓-ev-impossible P₁ P₂ (sVis refl ())

-- prepend a single visible step + a τ to a divergence (the both-offer commit path).
div-ev-τ-prepend : {P P′ P″ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                 → P ─[ ev e ]─► P′ → P′ ─[ τ ]─► P″ → divergences P″ s → divergences P (e ∷ s)
div-ev-τ-prepend stepe stepτ d = record
  { prefix = _ ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (_ ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = ⟹-ev stepe (⟹-τ stepτ (d .IsDivergence.reach)) ; divwit = d .IsDivergence.divwit }

-- prepend a τ then a visible step (the P=ret commit-to-Q path).
div-τ-ev-prepend : {P P′ P″ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                 → P ─[ τ ]─► P′ → P′ ─[ ev e ]─► P″ → divergences P″ s → divergences P (e ∷ s)
div-τ-ev-prepend stepτ stepe d = record
  { prefix = _ ∷ d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split  = cong (_ ∷_) (d .IsDivergence.split) ; witness = d .IsDivergence.witness
  ; reach  = ⟹-τ stepτ (⟹-ev stepe (d .IsDivergence.reach)) ; divwit = d .IsDivergence.divwit }

-- merge-offer equations (mirror mergeVis-L-eq / mergeVis-LQ-eq): match △-merge's own
-- `with viewV nP at a | viewV nQ at a`, then case on the offer-equality proofs.
△-merge-noP : {Q Q₁ : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {nP : NodeKind E (ExtI E) R}
            → viewV nP at a ≡ nothing → vQ at a ≡ just Q₁
            → △-merge nP (react vQ τcQ) Q at a ≡ just Q₁
△-merge-noP {at = at} {a = a} {vQ = vQ} {nP = nP} vp vq with viewV nP at a | vQ at a
... | nothing | just _  = case vq of λ { refl → refl }
... | nothing | nothing = case vq of λ ()
... | just _  | _       = case vp of λ ()

△-merge-bothP : {Q Q₁ P' : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                  {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {nP : NodeKind E (ExtI E) R}
              → viewV nP at a ≡ just P' → vQ at a ≡ just Q₁
              → △-merge nP (react vQ τcQ) Q at a ≡ just (ptree (react ∅v (△-br2 P' Q Q₁)))
△-merge-bothP {at = at} {a = a} {vQ = vQ} {nP = nP} vp vq with viewV nP at a | vQ at a
... | just _  | just _  = case vp of λ { refl → case vq of λ { refl → refl } }
... | just _  | nothing = case vq of λ ()
... | nothing | _       = case vp of λ ()

-- the both-offer node's τ (br2 tag1) reaches Q₁
△-br2-τ-tag1 : {Q Q₁ P' : PTree E (ExtI E) R}
             → ptree (react ∅v (△-br2 P' Q Q₁)) ─[ τ ]─► Q₁
△-br2-τ-tag1 = sTau {i = Lift ℓ (Fin 2) , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- Q's event reaches a divergent Q₁ THROUGH the interrupt P △ Q (any P).  Builds a
-- `divergences (P △ Q)` from a `divergences Q₁`, prepending the event:
--   • force P ≡ ret r  : P△Q = P⊓Q ─τ→ Q ─[ev]→ Q₁           (τ then ev)
--   • P live, P doesn't offer e : P△Q ─[ev]→ Q₁ directly      (the interrupt fires)
--   • P live, P offers e (→P') : P△Q ─[ev]→ both-offer node ─τ→ Q₁  (ev then τ)
△-Q-ev-prepend : (P Q : PTree E (ExtI E) R)
                   {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R} {s : List (Event√ R)}
               → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q₁
               → divergences Q₁ s
               → divergences (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
-- P live: split on whether P offers the same event.  Factored out so the nested
-- `with viewV` lives in its own clause (avoids `... | react` after a nested with).
△-Q-ev-prepend-live : (P Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
                        {s : List (Event√ R)} {nP : NodeKind E (ExtI E) R}
                        {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    → PTree.force P ≡ nP → NonRet nP
                    → PTree.force Q ≡ react vQ τcQ → vQ at a ≡ just Q₁ → divergences Q₁ s
                    → divergences (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
△-Q-ev-prepend-live P Q {at = at} {a = a} {Q₁ = Q₁} {nP = nP} {vQ = vQ} {τcQ = τcQ} eqP ntP eqQ brQ d
  with viewV nP at a in eqVP
... | nothing = div-ev-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
                        (△-merge-noP {Q = Q} {Q₁ = Q₁} {at = at} {a = a}
                                     {vQ = vQ} {τcQ = τcQ} {nP = nP} eqVP brQ)) d
... | just P' = div-ev-τ-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
                        (△-merge-bothP {Q = Q} {Q₁ = Q₁} {P' = P'} {at = at} {a = a}
                                       {vQ = vQ} {τcQ = τcQ} {nP = nP} eqVP brQ))
                  (△-br2-τ-tag1 {Q = Q} {Q₁ = Q₁} {P' = P'}) d

-- P=ret ⇒ P△Q = react ∅v (br2 P Q) ─τ→ Q (br2 tag1)
△-toQ-Pret : (P Q : PTree E (ExtI E) R) {r : R}
           → PTree.force P ≡ ret r → (P △ Q) ─[ τ ]─► Q
△-toQ-Pret P Q eqP =
  sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)}
       (force-△-Pret {P = P} {Q = Q} eqP) refl

△-Q-ev-prepend P Q {at = at} {a = a} {Q₁ = Q₁} (sVis {v = vQ} {τc = τcQ} {at = at} {a = a} eqQ brQ) d
  with PTree.force P in eqP
... | ret r       = div-τ-ev-prepend (△-toQ-Pret P Q eqP) (sVis eqQ brQ) d
... | sil P₁      = △-Q-ev-prepend-live P Q eqP tt0 eqQ brQ d
... | react vP τcP = △-Q-ev-prepend-live P Q eqP tt0 eqQ brQ d

-------------------------------------------------------------------------------------
-- the distribution-specific divergence elimination (recursion on the big-step).
-------------------------------------------------------------------------------------

△-⊓L-reach-div : (P₁ P₂ Q : PTree E (ExtI E) R)
                 {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
               → ((P₁ ⊓ P₂) △ Q) ⟹⟨ pre ⟩ W → Diverges W
               → divergences (P₁ △ Q) pre ⊎ divergences (P₂ △ Q) pre

-- base: Diverges ((P₁⊓P₂)△Q).  △-Diverges→ ⇒ Diverges (P₁⊓P₂) or Diverges Q.
△-⊓L-reach-div P₁ P₂ Q ⟹-refl divW with △-Diverges→ {P = P₁ ⊓ P₂} {Q = Q} divW
... | inj₂ dQ = inj₁ (root-div→all-div (△-Diverges-R {P = P₁} {Q = Q} dQ))
... | inj₁ d⊓ with ⊓-Diverges→ d⊓
...   | inj₁ dP₁ = inj₁ (root-div→all-div (△-Diverges-L {P = P₁} {Q = Q} dP₁))
...   | inj₂ dP₂ = inj₂ (root-div→all-div (△-Diverges-L {P = P₂} {Q = Q} dP₂))

-- τ-step: invert with △-τ-elim.
△-⊓L-reach-div P₁ P₂ Q (⟹-τ step rest) divW with △-τ-elim (P₁ ⊓ P₂) Q step
-- P₁⊓P₂'s own τ resolves the choice to Pᵢ: the continuation big-step is from Pᵢ△Q.
... | △τP s⊓ with ⊓-τ-inv P₁ P₂ s⊓
...   | inj₁ refl = inj₁ (mk-div-from rest divW)
...   | inj₂ refl = inj₂ (mk-div-from rest divW)
-- Q's τ: recurse (witness Q′) ⇒ divergences (Pᵢ△Q′); map back via △-τ-prepend-Q.
△-⊓L-reach-div P₁ P₂ Q (⟹-τ step rest) divW | △τQ {Q′ = Q′} sQ
  with △-⊓L-reach-div P₁ P₂ Q′ rest divW
...   | inj₁ dP₁ = inj₁ (△-τ-prepend-Q P₁ Q Q′ sQ dP₁)
...   | inj₂ dP₂ = inj₂ (△-τ-prepend-Q P₂ Q Q′ sQ dP₂)
-- Q's √-interrupt (force Q ≡ ret r′ ⇒ M ≡ Q): the rest big-step is from Q.
△-⊓L-reach-div P₁ P₂ Q (⟹-τ step rest) divW | △τQret eqQ =
  inj₁ (div-τ-prepend (△-toQ-Qret P₁ Q eqQ) (mk-div-from rest divW))
-- △τ⊓P / △τ⊓Q carry force (P₁⊓P₂) ≡ ret r — impossible (it is react ∅v (br2 …)).
△-⊓L-reach-div P₁ P₂ Q (⟹-τ step rest) divW | △τ⊓P eqPr = case eqPr of λ ()
△-⊓L-reach-div P₁ P₂ Q (⟹-τ step rest) divW | △τ⊓Q eqPr = case eqPr of λ ()

-- ev-step: invert with △-ev-elim.  Only Q's event can fire (△evP/△evPQ impossible).
△-⊓L-reach-div P₁ P₂ Q (⟹-ev step rest) divW with △-ev-elim (P₁ ⊓ P₂) Q step
... | △evP s⊓    = case ⊓-ev-impossible P₁ P₂ s⊓ of λ ()
... | △evPQ s⊓ _ = case ⊓-ev-impossible P₁ P₂ s⊓ of λ ()
... | △evQ {Q₁ = Q₁} sQ =
      inj₁ (△-Q-ev-prepend P₁ Q sQ (mk-div-from rest divW))

-------------------------------------------------------------------------------------
-- the HARD refinement: route the elim through ⊓-div←l / ⊓-div←r.
-------------------------------------------------------------------------------------

△-⊓L-div-elim : (P₁ P₂ Q : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences ((P₁ ⊓ P₂) △ Q) s
              → divergences (P₁ △ Q) s ⊎ divergences (P₂ △ Q) s
△-⊓L-div-elim P₁ P₂ Q d
  with △-⊓L-reach-div P₁ P₂ Q (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dP₁ = inj₁ (subst (divergences (P₁ △ Q)) (sym (d .IsDivergence.split))
                             (div-extension-closed dP₁))
... | inj₂ dP₂ = inj₂ (subst (divergences (P₂ △ Q)) (sym (d .IsDivergence.split))
                             (div-extension-closed dP₂))

△-⊓L-dist-⊒D : (P₁ P₂ Q : PTree E (ExtI E) R)
             → ((P₁ △ Q) ⊓ (P₂ △ Q)) ⊑D ((P₁ ⊓ P₂) △ Q)
△-⊓L-dist-⊒D P₁ P₂ Q d with △-⊓L-div-elim P₁ P₂ Q d
... | inj₁ dP₁ = ⊓-div←l (P₁ △ Q) (P₂ △ Q) dP₁
... | inj₂ dP₂ = ⊓-div←r (P₁ △ Q) (P₂ △ Q) dP₂

-------------------------------------------------------------------------------------
-- The FAILURES half of the left-⊓ distributive law.
--
-- Mirrors the divergence half: a failures-specific worker (△-⊓L-fail-elim) with the
-- SAME case analysis as △-⊓L-reach-div, with `Refuses W X` replacing `Diverges W`.
-------------------------------------------------------------------------------------

private
  variable
    ℓx : Level

-------------------------------------------------------------------------------------
-- (A) transfer a single LTS step / failure across an equal-force initial state.
-- Every step constructor carries a `force p ≡ <node>` premise, so the step transports
-- by composing that premise with the force-equality.  Refusals depend only on `force`,
-- so they transfer too.  This is the bare-failures analogue of sbisim-force-eq.
-------------------------------------------------------------------------------------

step-force-eq : {t u M : PTree E (ExtI E) R} {l : Label R}
              → PTree.force t ≡ PTree.force u → t ─[ l ]─► M → u ─[ l ]─► M
step-force-eq eq (sRet feq)    = sRet (trans (sym eq) feq)
step-force-eq eq (sVis feq br) = sVis (trans (sym eq) feq) br
step-force-eq eq (sSil feq)    = sSil (trans (sym eq) feq)
step-force-eq eq (sTau feq br) = sTau (trans (sym eq) feq) br

-- `mk-stable` (stability intro) and `isStable-force-eq` (stability transports along an
-- equal force) used to be re-proved here; both are generic and now come from
-- `Semantics.Stability` via the `Semantics.DRImpliesFD` re-export above.

Refuses-force-eq : {t u : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
                 → PTree.force t ≡ PTree.force u → Refuses t X → Refuses u X
Refuses-force-eq {t = t} {u = u} eq (st , noff) =
  isStable-force-eq {t = t} {u = u} eq st ,
  λ e xe (M , ustep) → noff e xe (M , step-force-eq {t = u} {u = t} (sym eq) ustep)

fail-force-eq : {t u : PTree E (ExtI E) R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
              → PTree.force t ≡ PTree.force u → failures t s X → failures u s X
fail-force-eq eq (W , ⟹-refl , ref)       = _ , ⟹-refl , Refuses-force-eq eq ref
fail-force-eq eq (W , ⟹-τ step rest , ref) = W , ⟹-τ (step-force-eq eq step) rest , ref
fail-force-eq eq (W , ⟹-ev step rest , ref) = W , ⟹-ev (step-force-eq eq step) rest , ref

-- bare-failures bridge: force P ≡ ret r ⇒ failures(P△Qa) ↔ failures(P⊓Qa).
-- force-△-Pret gives force(P△Qa) ≡ react ∅v (br2 P Qa) ≡ force(P⊓Qa) definitionally.
△-fail-to-⊓ : (P Qa : PTree E (ExtI E) R) {r : R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
            → PTree.force P ≡ ret r → failures (P △ Qa) s X → failures (P ⊓ Qa) s X
△-fail-to-⊓ P Qa eqP = fail-force-eq (force-△-Pret {P = P} {Q = Qa} eqP)

⊓-fail-to-△ : (P Qa : PTree E (ExtI E) R) {r : R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
            → PTree.force P ≡ ret r → failures (P ⊓ Qa) s X → failures (P △ Qa) s X
⊓-fail-to-△ P Qa eqP = fail-force-eq (sym (force-△-Pret {P = P} {Q = Qa} eqP))

-------------------------------------------------------------------------------------
-- (B) failure prependers (rebuild the witness through a leading step / step pair),
-- the failures analogues of div-τ-prepend / div-ev-prepend / div-ev-τ-prepend /
-- div-τ-ev-prepend.
-------------------------------------------------------------------------------------

fail-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
               → P ─[ τ ]─► P′ → failures P′ s X → failures P s X
fail-τ-prepend step (W , reach , ref) = W , ⟹-τ step reach , ref

fail-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                  {X : Event√ R → Set ℓx}
                → P ─[ ev e ]─► P′ → failures P′ s X → failures P (e ∷ s) X
fail-ev-prepend step (W , reach , ref) = W , ⟹-ev step reach , ref

fail-ev-τ-prepend : {P P′ P″ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                    {X : Event√ R → Set ℓx}
                  → P ─[ ev e ]─► P′ → P′ ─[ τ ]─► P″ → failures P″ s X → failures P (e ∷ s) X
fail-ev-τ-prepend stepe stepτ (W , reach , ref) = W , ⟹-ev stepe (⟹-τ stepτ reach) , ref

fail-τ-ev-prepend : {P P′ P″ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)}
                    {X : Event√ R → Set ℓx}
                  → P ─[ τ ]─► P′ → P′ ─[ ev e ]─► P″ → failures P″ s X → failures P (e ∷ s) X
fail-τ-ev-prepend stepτ stepe (W , reach , ref) = W , ⟹-τ stepτ (⟹-ev stepe reach) , ref

-------------------------------------------------------------------------------------
-- (C) (Pᵢ△Q′) failure → (Pᵢ△Q) failure, prepending Q's τ.  Failures analogue of
-- △-τ-prepend-Q.  Pᵢ live: △-τ-lift-Q.  force Pᵢ ≡ ret r: Pᵢ△ · = Pᵢ⊓ · (equal force);
-- split via ⊓-failures→ — Pᵢ-failure transfers back (⊓-failures←l), Q′-failure prepends
-- Q─τ→Q′ first (⊓-failures←r).
-------------------------------------------------------------------------------------

△-τ-fail-prepend-Q : (Pᵢ Qa Qa′ : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                   → Qa ─[ τ ]─► Qa′ → failures (Pᵢ △ Qa′) s X → failures (Pᵢ △ Qa) s X
△-τ-fail-prepend-Q Pᵢ Qa Qa′ sQa f with PTree.force Pᵢ in eqPi
... | sil _    = fail-τ-prepend (△-τ-lift-Q {P = Pᵢ} (subst NonRet (sym eqPi) tt0) sQa) f
... | react _ _ = fail-τ-prepend (△-τ-lift-Q {P = Pᵢ} (subst NonRet (sym eqPi) tt0) sQa) f
... | ret r    with ⊓-failures→ Pᵢ Qa′ (△-fail-to-⊓ Pᵢ Qa′ eqPi f)
...   | inj₁ fPi  = ⊓-fail-to-△ Pᵢ Qa eqPi (⊓-failures←l Pᵢ Qa fPi)
...   | inj₂ fQa′ = ⊓-fail-to-△ Pᵢ Qa eqPi (⊓-failures←r Pᵢ Qa (fail-τ-prepend sQa fQa′))

-------------------------------------------------------------------------------------
-- (D) interrupt-fire prepend for FAILURES: Q's event reaches Q₁ through P △ Q (any P).
-- Failures analogue of △-Q-ev-prepend; same three step-construction arms.
-------------------------------------------------------------------------------------

△-Q-ev-fail-prepend : (P Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
                        {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                    → Q ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q₁
                    → failures Q₁ s X
                    → failures (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) X
△-Q-ev-fail-prepend-live : (P Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {Q₁ : PTree E (ExtI E) R}
                        {s : List (Event√ R)} {X : Event√ R → Set ℓx} {nP : NodeKind E (ExtI E) R}
                        {vQ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τcQ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    → PTree.force P ≡ nP → NonRet nP
                    → PTree.force Q ≡ react vQ τcQ → vQ at a ≡ just Q₁ → failures Q₁ s X
                    → failures (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) X
△-Q-ev-fail-prepend-live P Q {at = at} {a = a} {Q₁ = Q₁} {nP = nP} {vQ = vQ} {τcQ = τcQ} eqP ntP eqQ brQ f
  with viewV nP at a in eqVP
... | nothing = fail-ev-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
                        (△-merge-noP {Q = Q} {Q₁ = Q₁} {at = at} {a = a}
                                     {vQ = vQ} {τcQ = τcQ} {nP = nP} eqVP brQ)) f
... | just P' = fail-ev-τ-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ ntP tt0)
                        (△-merge-bothP {Q = Q} {Q₁ = Q₁} {P' = P'} {at = at} {a = a}
                                       {vQ = vQ} {τcQ = τcQ} {nP = nP} eqVP brQ))
                  (△-br2-τ-tag1 {Q = Q} {Q₁ = Q₁} {P' = P'}) f

△-Q-ev-fail-prepend P Q {at = at} {a = a} {Q₁ = Q₁} (sVis {v = vQ} {τc = τcQ} {at = at} {a = a} eqQ brQ) f
  with PTree.force P in eqP
... | ret r       = fail-τ-ev-prepend (△-toQ-Pret P Q eqP) (sVis eqQ brQ) f
... | sil P₁      = △-Q-ev-fail-prepend-live P Q eqP tt0 eqQ brQ f
... | react vP τcP = △-Q-ev-fail-prepend-live P Q eqP tt0 eqQ brQ f

-------------------------------------------------------------------------------------
-- (E) (P₁⊓P₂)△Q is unstable: it has the τ-step to P₁△Q (the ⊓-resolving τ lifted
-- through the interrupt), and a stable state performs no τ.
-------------------------------------------------------------------------------------

△-⊓L-unstable : {P₁ P₂ Q : PTree E (ExtI E) R} → ¬ isStable ((P₁ ⊓ P₂) △ Q)
△-⊓L-unstable {P₁ = P₁} {P₂ = P₂} {Q = Q} st =
  stable-no-τ st (△-τ-lift-P {Q = Q} (⊓-stepL P₁ P₂))

-------------------------------------------------------------------------------------
-- (F) the distribution-specific stable-failures elimination (recursion on the
-- big-step).  SAME case split as △-⊓L-reach-div with `Refuses W X` for `Diverges W`.
-------------------------------------------------------------------------------------

△-⊓L-fail-elim : (P₁ P₂ Q : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
               → ((P₁ ⊓ P₂) △ Q) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P₁ △ Q) s X ⊎ failures (P₂ △ Q) s X

-- base: Refuses ((P₁⊓P₂)△Q) X gives isStable — contradicted by △-⊓L-unstable.
△-⊓L-fail-elim P₁ P₂ Q ⟹-refl (st , _) =
  ⊥-elim (△-⊓L-unstable {P₁ = P₁} {P₂ = P₂} {Q = Q} st)

-- τ-step: invert with △-τ-elim.
△-⊓L-fail-elim P₁ P₂ Q (⟹-τ step rest) ref with △-τ-elim (P₁ ⊓ P₂) Q step
-- P₁⊓P₂'s own τ resolves the choice to Pᵢ: the continuation failure is from Pᵢ△Q.
... | △τP s⊓ with ⊓-τ-inv P₁ P₂ s⊓
...   | inj₁ refl = inj₁ (_ , rest , ref)
...   | inj₂ refl = inj₂ (_ , rest , ref)
-- Q's τ: recurse (witness Q′) ⇒ failures (Pᵢ△Q′); map back via △-τ-fail-prepend-Q.
△-⊓L-fail-elim P₁ P₂ Q (⟹-τ step rest) ref | △τQ {Q′ = Q′} sQ
  with △-⊓L-fail-elim P₁ P₂ Q′ rest ref
...   | inj₁ fP₁ = inj₁ (△-τ-fail-prepend-Q P₁ Q Q′ sQ fP₁)
...   | inj₂ fP₂ = inj₂ (△-τ-fail-prepend-Q P₂ Q Q′ sQ fP₂)
-- Q's √-interrupt (force Q ≡ ret r′ ⇒ M ≡ Q): the rest failure is from Q.
△-⊓L-fail-elim P₁ P₂ Q (⟹-τ step rest) ref | △τQret eqQ =
  inj₁ (fail-τ-prepend (△-toQ-Qret P₁ Q eqQ) (_ , rest , ref))
-- △τ⊓P / △τ⊓Q carry force (P₁⊓P₂) ≡ ret r — impossible (it is react ∅v (br2 …)).
△-⊓L-fail-elim P₁ P₂ Q (⟹-τ step rest) ref | △τ⊓P eqPr = case eqPr of λ ()
△-⊓L-fail-elim P₁ P₂ Q (⟹-τ step rest) ref | △τ⊓Q eqPr = case eqPr of λ ()

-- ev-step: invert with △-ev-elim.  Only Q's event can fire (△evP/△evPQ impossible).
△-⊓L-fail-elim P₁ P₂ Q (⟹-ev step rest) ref with △-ev-elim (P₁ ⊓ P₂) Q step
... | △evP s⊓    = case ⊓-ev-impossible P₁ P₂ s⊓ of λ ()
... | △evPQ s⊓ _ = case ⊓-ev-impossible P₁ P₂ s⊓ of λ ()
... | △evQ {Q₁ = Q₁} sQ =
      inj₁ (△-Q-ev-fail-prepend P₁ Q sQ (_ , rest , ref))

-------------------------------------------------------------------------------------
-- (G) the two failures⊥ refinements.
-------------------------------------------------------------------------------------

-- prepend a τ to a failures⊥ (failures triple OR divergence record).
failures⊥-τ-prepend : {A B : PTree E (ExtI E) R} {s : List (Event√ R)} {C : Event√ R → Set ℓr}
                    → A ─[ τ ]─► B → failures⊥ B s C → failures⊥ A s C
failures⊥-τ-prepend step (inj₁ f) = inj₁ (fail-τ-prepend step f)
failures⊥-τ-prepend step (inj₂ d) = inj₂ (div-τ-prepend step d)

-- EASY (intro): a failures⊥ of (P₁△Q)⊓(P₂△Q) splits; prepend the ⊓-resolving τ.
△-⊓L-dist-⊑F⊥ : (P₁ P₂ Q : PTree E (ExtI E) R)
              → ((P₁ ⊓ P₂) △ Q) ⊑F⊥ ((P₁ △ Q) ⊓ (P₂ △ Q))
△-⊓L-dist-⊑F⊥ P₁ P₂ Q f with ⊓-failures⊥→ (P₁ △ Q) (P₂ △ Q) f
... | inj₁ fP₁ = failures⊥-τ-prepend (△-τ-lift-P {Q = Q} (⊓-stepL P₁ P₂)) fP₁
... | inj₂ fP₂ = failures⊥-τ-prepend (△-τ-lift-P {Q = Q} (⊓-stepR P₁ P₂)) fP₂

-- HARD (elim): a failures⊥ of (P₁⊓P₂)△Q routes through △-⊓L-fail-elim / △-⊓L-div-elim.
△-⊓L-dist-⊒F⊥ : (P₁ P₂ Q : PTree E (ExtI E) R)
              → ((P₁ △ Q) ⊓ (P₂ △ Q)) ⊑F⊥ ((P₁ ⊓ P₂) △ Q)
△-⊓L-dist-⊒F⊥ P₁ P₂ Q (inj₁ (W , reach , ref)) with △-⊓L-fail-elim P₁ P₂ Q reach ref
... | inj₁ fP₁ = ⊓-failures⊥←l (P₁ △ Q) (P₂ △ Q) (inj₁ fP₁)
... | inj₂ fP₂ = ⊓-failures⊥←r (P₁ △ Q) (P₂ △ Q) (inj₁ fP₂)
△-⊓L-dist-⊒F⊥ P₁ P₂ Q (inj₂ d) with △-⊓L-div-elim P₁ P₂ Q d
... | inj₁ dP₁ = ⊓-failures⊥←l (P₁ △ Q) (P₂ △ Q) (inj₂ dP₁)
... | inj₂ dP₂ = ⊓-failures⊥←r (P₁ △ Q) (P₂ △ Q) (inj₂ dP₂)

-------------------------------------------------------------------------------------
-- (H) the law: pair the two ⊑F⊥ and the two ⊑D refinements.
-------------------------------------------------------------------------------------

△-⊓L-dist-FD : (P₁ P₂ Q : PTree E (ExtI E) R)
             → ((P₁ ⊓ P₂) △ Q) ≈FD ((P₁ △ Q) ⊓ (P₂ △ Q))
△-⊓L-dist-FD P₁ P₂ Q =
  (△-⊓L-dist-⊑F⊥ P₁ P₂ Q , △-⊓L-dist-⊑D P₁ P₂ Q) ,
  (△-⊓L-dist-⊒F⊥ P₁ P₂ Q , △-⊓L-dist-⊒D P₁ P₂ Q)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- The RIGHT-⊓ distributive law (divergence half):
--      P △ (Q₁ ⊓ Q₂)  ≈D  (P △ Q₁) ⊓ (P △ Q₂)
--
-- Mirror of the LEFT law with the internal choice on the Q-side.  The decisive
-- simplification: Q₁⊓Q₂ = react ∅v (br2 Q₁ Q₂) OFFERS NO VISIBLE EVENT, so a P-event
-- of P △ (Q₁⊓Q₂) fires the interrupt's P-only `△-merge` arm cleanly to P′△(Q₁⊓Q₂)
-- (no both-offer node ever arises on this combined tree).
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- the both-offer node's τ (br2 tag0) reaches P'△Q  (mirror of △-br2-τ-tag1)
△-br2-τ-tag0 : {Q P' Q₁ : PTree E (ExtI E) R}
             → ptree (react ∅v (△-br2 P' Q Q₁)) ─[ τ ]─► (P' △ Q)
△-br2-τ-tag0 = sTau {i = Lift ℓ (Fin 2) , fin {n = 2}} {a = lift fzero} refl refl

-- force P ≡ ret r ⇒ P△Q = react ∅v (br2 P Q) ─τ→ P (the br2 tag0, P-summand of the ⊓).
△-toP-Pret : (P Q : PTree E (ExtI E) R) {r : R}
           → PTree.force P ≡ ret r → (P △ Q) ─[ τ ]─► P
△-toP-Pret P Q eqP =
  sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero}
       (force-△-Pret {P = P} {Q = Q} eqP) refl

-- merge-offer equation when only P offers (mirror of △-merge-noP, P/Q swapped):
-- viewV nP at a ≡ just P' and viewV nQ at a ≡ nothing ⇒ △-merge fires the P-only arm.
△-merge-noQ : {Q P' : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                {nP nQ : NodeKind E (ExtI E) R}
            → viewV nP at a ≡ just P' → viewV nQ at a ≡ nothing
            → △-merge nP nQ Q at a ≡ just (P' △ Q)
△-merge-noQ {at = at} {a = a} {nP = nP} {nQ = nQ} vp vq with viewV nP at a | viewV nQ at a
... | just _  | nothing = case vp of λ { refl → refl }
... | just _  | just _  = case vq of λ ()
... | nothing | _       = case vp of λ ()

-- the both-offer merge equation in the general `viewV nP / viewV nQ` form
-- (△-merge-bothP was specialised to nQ ≡ react vQ τcQ).
△-merge-bothP-PQ : {Q P' Q₁ : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                     {nP nQ : NodeKind E (ExtI E) R}
                 → viewV nP at a ≡ just P' → viewV nQ at a ≡ just Q₁
                 → △-merge nP nQ Q at a ≡ just (ptree (react ∅v (△-br2 P' Q Q₁)))
△-merge-bothP-PQ {at = at} {a = a} {nP = nP} {nQ = nQ} vp vq
  with viewV nP at a | viewV nQ at a
... | just _  | just _  = case vp of λ { refl → case vq of λ { refl → refl } }
... | just _  | nothing = case vq of λ ()
... | nothing | _       = case vp of λ ()

-- Q terminated, P offers e ⇒ △-merge-Qret fires the P-only arm to P₁△Q.
△-merge-Qret-noQ : {Q P' : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
                     {nP : NodeKind E (ExtI E) R}
                 → viewV nP at a ≡ just P' → △-merge-Qret nP Q at a ≡ just (P' △ Q)
△-merge-Qret-noQ {at = at} {a = a} {nP = nP} vp with viewV nP at a
... | just _  = case vp of λ { refl → refl }
... | nothing = case vp of λ ()

-- P's event reaches a divergent P₁ THROUGH the interrupt P △ Q (P live, ANY Q).  The
-- P-side mirror of △-Q-ev-prepend.  Cases on Q:
--   • Q terminated (force Q ≡ ret r′)  : P△Q ─[ev]→ P₁△Q via △-merge-Qret (P-only)
--   • Q live, doesn't offer e          : P△Q ─[ev]→ P₁△Q directly (P-only merge arm)
--   • Q live, offers e (→Q₁)           : P△Q ─[ev]→ both-offer node ─τ→ P₁△Q (ev+τ tag0)
-- Builds a `divergences (P△Q) (e ∷ s)` from `divergences (P₁△Q) s`.
△-P-ev-prepend : (P Q : PTree E (ExtI E) R)
                   {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
                   {s : List (Event√ R)}
                   {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
               → PTree.force P ≡ react vP τcP → vP at a ≡ just P₁
               → divergences (P₁ △ Q) s
               → divergences (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
-- factored worker for the two LIVE Q sub-cases (nested `with viewV` in its own clause).
△-P-ev-prepend-live : (P Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
                        {s : List (Event√ R)} {nQ : NodeKind E (ExtI E) R}
                        {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    → PTree.force P ≡ react vP τcP → vP at a ≡ just P₁
                    → PTree.force Q ≡ nQ → NonRet nQ → divergences (P₁ △ Q) s
                    → divergences (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
△-P-ev-prepend-live P Q {at = at} {a = a} {P₁ = P₁} {nQ = nQ} {vP = vP} {τcP = τcP} eqP brP eqQ ntQ d
  with viewV nQ at a in eqVQ
... | nothing = div-ev-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ tt0 ntQ)
                        (△-merge-noQ {Q = Q} {P' = P₁} {at = at} {a = a}
                                     {nP = react vP τcP} {nQ = nQ} brP eqVQ)) d
... | just Q₁ = div-ev-τ-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ tt0 ntQ)
                        (△-merge-bothP-PQ {Q = Q} {P' = P₁} {Q₁ = Q₁} {at = at} {a = a}
                                          {nP = react vP τcP} {nQ = nQ} brP eqVQ))
                  (△-br2-τ-tag0 {Q = Q} {P' = P₁} {Q₁ = Q₁}) d

△-P-ev-prepend P Q {at = at} {a = a} {P₁ = P₁} {vP = vP} {τcP = τcP} eqP brP d
  with PTree.force Q in eqQ
... | ret r′   = div-ev-prepend
                   (sVis (force-△-LR {P = P} {Q = Q} eqP eqQ tt0)
                         (△-merge-Qret-noQ {Q = Q} {P' = P₁} {at = at} {a = a}
                                           {nP = react vP τcP} brP)) d
... | sil _    = △-P-ev-prepend-live P Q eqP brP eqQ tt0 d
... | react _ _ = △-P-ev-prepend-live P Q eqP brP eqQ tt0 d

-------------------------------------------------------------------------------------
-- the EASY direction (intro):
-- divergences ((P△Q₁)⊓(P△Q₂)) s → divergences (P△(Q₁⊓Q₂)) s.
-- ⊓-div→ splits into divergences (P△Qᵢ) s; map each to divergences (P△(Q₁⊓Q₂)) s.
-------------------------------------------------------------------------------------

-- divergences (P △ Qᵢ) s → divergences (P △ (Q₁⊓Q₂)) s, where Qᵢ ∈ {Q₁,Q₂} and
-- `Q₁⊓Q₂ ─τ→ Qᵢ` is the supplied resolving τ.  P live: lift that τ through △ on the
-- Q-side.  P=ret: P△· = P⊓· (equal force); split via ⊓-div→ — a P-divergence transfers
-- back (⊓-div←l), a Qᵢ-divergence becomes a (Q₁⊓Q₂)-divergence (⊓-div←l/r via the same
-- resolving τ) ⇒ the right summand (⊓-div←r).
△-Qi→Q⊓ : (P Q₁ Q₂ Qᵢ : PTree E (ExtI E) R) {s : List (Event√ R)}
        → ((Q₁ ⊓ Q₂) ─[ τ ]─► Qᵢ)
        → (divergences Qᵢ s → divergences (Q₁ ⊓ Q₂) s)
        → divergences (P △ Qᵢ) s → divergences (P △ (Q₁ ⊓ Q₂)) s
△-Qi→Q⊓ P Q₁ Q₂ Qᵢ sQ ⊓-back d with PTree.force P in eqP
... | sil _    = div-τ-prepend (△-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) sQ) d
... | react _ _ = div-τ-prepend (△-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) sQ) d
... | ret r    with ⊓-div→ P Qᵢ (△-to-⊓ P Qᵢ eqP d)
...   | inj₁ dP  = ⊓-to-△ P (Q₁ ⊓ Q₂) eqP (⊓-div←l P (Q₁ ⊓ Q₂) dP)
...   | inj₂ dQᵢ = ⊓-to-△ P (Q₁ ⊓ Q₂) eqP (⊓-div←r P (Q₁ ⊓ Q₂) (⊓-back dQᵢ))

△-⊓R-dist-⊑D : (P Q₁ Q₂ : PTree E (ExtI E) R)
             → (P △ (Q₁ ⊓ Q₂)) ⊑D ((P △ Q₁) ⊓ (P △ Q₂))
△-⊓R-dist-⊑D P Q₁ Q₂ d with ⊓-div→ (P △ Q₁) (P △ Q₂) d
... | inj₁ dQ₁ = △-Qi→Q⊓ P Q₁ Q₂ Q₁ (⊓-stepL Q₁ Q₂) (⊓-div←l Q₁ Q₂) dQ₁
... | inj₂ dQ₂ = △-Qi→Q⊓ P Q₁ Q₂ Q₂ (⊓-stepR Q₁ Q₂) (⊓-div←r Q₁ Q₂) dQ₂

-------------------------------------------------------------------------------------
-- the HARD direction (elim): a distribution-specific divergence elimination, recursing
-- on the big-step P△(Q₁⊓Q₂) ⟹⟨pre⟩ W.  Mirror of △-⊓L-reach-div with ⊓ on the Q-side.
-------------------------------------------------------------------------------------

△-⊓R-reach-div : (P Q₁ Q₂ : PTree E (ExtI E) R)
                 {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
               → (P △ (Q₁ ⊓ Q₂)) ⟹⟨ pre ⟩ W → Diverges W
               → divergences (P △ Q₁) pre ⊎ divergences (P △ Q₂) pre

-- base: Diverges (P△(Q₁⊓Q₂)).  △-Diverges→ ⇒ Diverges P or Diverges (Q₁⊓Q₂).
△-⊓R-reach-div P Q₁ Q₂ ⟹-refl divW with △-Diverges→ {P = P} {Q = Q₁ ⊓ Q₂} divW
... | inj₁ dP  = inj₁ (root-div→all-div (△-Diverges-L {P = P} {Q = Q₁} dP))
... | inj₂ d⊓Q with ⊓-Diverges→ d⊓Q
...   | inj₁ dQ₁ = inj₁ (root-div→all-div (△-Diverges-R {P = P} {Q = Q₁} dQ₁))
...   | inj₂ dQ₂ = inj₂ (root-div→all-div (△-Diverges-R {P = P} {Q = Q₂} dQ₂))

-- τ-step: invert with △-τ-elim.
△-⊓R-reach-div P Q₁ Q₂ (⟹-τ step rest) divW with △-τ-elim P (Q₁ ⊓ Q₂) step
-- P's own τ (→ P′△(Q₁⊓Q₂)): recurse, prepend P's τ to BOTH summands via △-τ-lift-P.
... | △τP {P′ = P′} sP with △-⊓R-reach-div P′ Q₁ Q₂ rest divW
...   | inj₁ dQ₁ = inj₁ (div-τ-prepend (△-τ-lift-P {Q = Q₁} sP) dQ₁)
...   | inj₂ dQ₂ = inj₂ (div-τ-prepend (△-τ-lift-P {Q = Q₂} sP) dQ₂)
-- Q₁⊓Q₂'s own τ resolves the choice to Qᵢ: the continuation big-step is from P△Qᵢ.
△-⊓R-reach-div P Q₁ Q₂ (⟹-τ step rest) divW | △τQ sQ with ⊓-τ-inv Q₁ Q₂ sQ
...   | inj₁ refl = inj₁ (mk-div-from rest divW)
...   | inj₂ refl = inj₂ (mk-div-from rest divW)
-- △τQret: force (Q₁⊓Q₂) ≡ ret r′ — impossible (it is react ∅v (br2 …)).
△-⊓R-reach-div P Q₁ Q₂ (⟹-τ step rest) divW | △τQret eqQr = case eqQr of λ ()
-- △τ⊓P (force P ≡ ret r, M ≡ P): rest big-step is from P; prepend P△(Q₁⊓Q₂) ─τ→ P
-- (br2 tag0, the △-toQ-Pret-style step) — but here we land on the P summand.
△-⊓R-reach-div P Q₁ Q₂ (⟹-τ step rest) divW | △τ⊓P eqPr =
  inj₁ (div-τ-prepend (△-toP-Pret P Q₁ eqPr) (mk-div-from rest divW))
-- △τ⊓Q (force P ≡ ret r, M ≡ Q₁⊓Q₂): rest big-step is from Q₁⊓Q₂; ⊓-div→ splits the
-- divergence, and since force P ≡ ret r, P△Qᵢ ─τ→ Qᵢ (the br2 tag1) prepends.
△-⊓R-reach-div P Q₁ Q₂ (⟹-τ step rest) divW | △τ⊓Q eqPr
  with ⊓-div→ Q₁ Q₂ (mk-div-from rest divW)
...   | inj₁ dQ₁ = inj₁ (div-τ-prepend (△-toQ-Pret P Q₁ eqPr) dQ₁)
...   | inj₂ dQ₂ = inj₂ (div-τ-prepend (△-toQ-Pret P Q₂ eqPr) dQ₂)

-- ev-step: invert with △-ev-elim.  Only P's event can fire: Q₁⊓Q₂ = react ∅v offers
-- nothing, so △evQ/△evPQ are impossible (their Q-step contradicts ∅v).
△-⊓R-reach-div P Q₁ Q₂ (⟹-ev step rest) divW with △-ev-elim P (Q₁ ⊓ Q₂) step
... | △evQ  sQ   = case ⊓-ev-impossible Q₁ Q₂ sQ of λ ()
... | △evPQ _ sQ = case ⊓-ev-impossible Q₁ Q₂ sQ of λ ()
-- P's event (→ P₁△(Q₁⊓Q₂)): recurse, prepend P's event via △-P-ev-prepend on each
-- summand (Q₁⊓Q₂ offers nothing ⇒ the P-only merge arm; instantiated at Qᵢ which may
-- offer e — △-P-ev-prepend handles both sub-cases).
△-⊓R-reach-div P Q₁ Q₂ (⟹-ev step rest) divW | △evP {P₁ = P₁} sP
  with △-⊓R-reach-div P₁ Q₁ Q₂ rest divW | sP
...   | inj₁ dQ₁ | sVis {at = at} {a = a} eqP brP = inj₁ (△-P-ev-prepend P Q₁ eqP brP dQ₁)
...   | inj₂ dQ₂ | sVis {at = at} {a = a} eqP brP = inj₂ (△-P-ev-prepend P Q₂ eqP brP dQ₂)

-------------------------------------------------------------------------------------
-- the HARD refinement: route the elim through ⊓-div←l / ⊓-div←r.
-------------------------------------------------------------------------------------

△-⊓R-div-elim : (P Q₁ Q₂ : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences (P △ (Q₁ ⊓ Q₂)) s
              → divergences (P △ Q₁) s ⊎ divergences (P △ Q₂) s
△-⊓R-div-elim P Q₁ Q₂ d
  with △-⊓R-reach-div P Q₁ Q₂ (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dQ₁ = inj₁ (subst (divergences (P △ Q₁)) (sym (d .IsDivergence.split))
                             (div-extension-closed dQ₁))
... | inj₂ dQ₂ = inj₂ (subst (divergences (P △ Q₂)) (sym (d .IsDivergence.split))
                             (div-extension-closed dQ₂))

△-⊓R-dist-⊒D : (P Q₁ Q₂ : PTree E (ExtI E) R)
             → ((P △ Q₁) ⊓ (P △ Q₂)) ⊑D (P △ (Q₁ ⊓ Q₂))
△-⊓R-dist-⊒D P Q₁ Q₂ d with △-⊓R-div-elim P Q₁ Q₂ d
... | inj₁ dQ₁ = ⊓-div←l (P △ Q₁) (P △ Q₂) dQ₁
... | inj₂ dQ₂ = ⊓-div←r (P △ Q₁) (P △ Q₂) dQ₂

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- The RIGHT-⊓ distributive law (FAILURES half + assembly):
--      P △ (Q₁ ⊓ Q₂)  ≈FD  (P △ Q₁) ⊓ (P △ Q₂)
--
-- Mirror of the LEFT failures half (and of the RIGHT divergence half above): a
-- failures-specific worker (△-⊓R-fail-elim) with the SAME case analysis as
-- △-⊓R-reach-div, with `Refuses W X` replacing `Diverges W`.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- (I) P's event reaches a refusing P₁ THROUGH the interrupt P △ Q (P live, ANY Q).
-- FAILURES analogue of △-P-ev-prepend; same three step-construction arms.
△-P-ev-fail-prepend : (P Q : PTree E (ExtI E) R)
                   {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
                   {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                   {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
               → PTree.force P ≡ react vP τcP → vP at a ≡ just P₁
               → failures (P₁ △ Q) s X
               → failures (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) X
△-P-ev-fail-prepend-live : (P Q : PTree E (ExtI E) R)
                        {at : AnyTypes E} {a : proj₁ at} {P₁ : PTree E (ExtI E) R}
                        {s : List (Event√ R)} {X : Event√ R → Set ℓx} {nQ : NodeKind E (ExtI E) R}
                        {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                        {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    → PTree.force P ≡ react vP τcP → vP at a ≡ just P₁
                    → PTree.force Q ≡ nQ → NonRet nQ → failures (P₁ △ Q) s X
                    → failures (P △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) X
△-P-ev-fail-prepend-live P Q {at = at} {a = a} {P₁ = P₁} {nQ = nQ} {vP = vP} {τcP = τcP} eqP brP eqQ ntQ f
  with viewV nQ at a in eqVQ
... | nothing = fail-ev-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ tt0 ntQ)
                        (△-merge-noQ {Q = Q} {P' = P₁} {at = at} {a = a}
                                     {nP = react vP τcP} {nQ = nQ} brP eqVQ)) f
... | just Q₁ = fail-ev-τ-prepend
                  (sVis (force-△-mt {P = P} {Q = Q} eqP eqQ tt0 ntQ)
                        (△-merge-bothP-PQ {Q = Q} {P' = P₁} {Q₁ = Q₁} {at = at} {a = a}
                                          {nP = react vP τcP} {nQ = nQ} brP eqVQ))
                  (△-br2-τ-tag0 {Q = Q} {P' = P₁} {Q₁ = Q₁}) f

△-P-ev-fail-prepend P Q {at = at} {a = a} {P₁ = P₁} {vP = vP} {τcP = τcP} eqP brP f
  with PTree.force Q in eqQ
... | ret r′   = fail-ev-prepend
                   (sVis (force-△-LR {P = P} {Q = Q} eqP eqQ tt0)
                         (△-merge-Qret-noQ {Q = Q} {P' = P₁} {at = at} {a = a}
                                           {nP = react vP τcP} brP)) f
... | sil _    = △-P-ev-fail-prepend-live P Q eqP brP eqQ tt0 f
... | react _ _ = △-P-ev-fail-prepend-live P Q eqP brP eqQ tt0 f

-------------------------------------------------------------------------------------
-- (J) P △ (Q₁⊓Q₂) is unstable: it always has a τ-step (the Q-resolving τ lifted
-- through the interrupt when P is live, or the br2 tag0 when P terminates), and a
-- stable state performs no τ.
-------------------------------------------------------------------------------------

-- P △ (Q₁⊓Q₂) always performs a τ.  Factored out so the `with PTree.force P`
-- abstraction does not capture the (unrelated) `isStable` hypothesis.
△-⊓R-some-τ : (P Q₁ Q₂ : PTree E (ExtI E) R)
            → Σ[ M ∈ PTree E (ExtI E) R ] ((P △ (Q₁ ⊓ Q₂)) ─[ τ ]─► M)
△-⊓R-some-τ P Q₁ Q₂ with PTree.force P in eqP
... | ret r    = P , △-toP-Pret P (Q₁ ⊓ Q₂) eqP
... | sil _    = (P △ Q₁) , △-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) (⊓-stepL Q₁ Q₂)
... | react _ _ = (P △ Q₁) , △-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) (⊓-stepL Q₁ Q₂)

△-⊓R-unstable : {P Q₁ Q₂ : PTree E (ExtI E) R} → ¬ isStable (P △ (Q₁ ⊓ Q₂))
△-⊓R-unstable {P = P} {Q₁ = Q₁} {Q₂ = Q₂} st =
  stable-no-τ st (proj₂ (△-⊓R-some-τ P Q₁ Q₂))

-------------------------------------------------------------------------------------
-- (K) the distribution-specific stable-failures elimination (recursion on the
-- big-step).  SAME case split as △-⊓R-reach-div with `Refuses W X` for `Diverges W`.
-------------------------------------------------------------------------------------

△-⊓R-fail-elim : (P Q₁ Q₂ : PTree E (ExtI E) R)
                 {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
               → (P △ (Q₁ ⊓ Q₂)) ⟹⟨ s ⟩ W → Refuses W X
               → failures (P △ Q₁) s X ⊎ failures (P △ Q₂) s X

-- base: Refuses (P△(Q₁⊓Q₂)) X gives isStable — contradicted by △-⊓R-unstable.
△-⊓R-fail-elim P Q₁ Q₂ ⟹-refl (st , _) =
  ⊥-elim (△-⊓R-unstable {P = P} {Q₁ = Q₁} {Q₂ = Q₂} st)

-- τ-step: invert with △-τ-elim.
△-⊓R-fail-elim P Q₁ Q₂ (⟹-τ step rest) ref with △-τ-elim P (Q₁ ⊓ Q₂) step
-- P's own τ (→ P′△(Q₁⊓Q₂)): recurse, prepend P's τ to BOTH summands via △-τ-lift-P.
... | △τP {P′ = P′} sP with △-⊓R-fail-elim P′ Q₁ Q₂ rest ref
...   | inj₁ fQ₁ = inj₁ (fail-τ-prepend (△-τ-lift-P {Q = Q₁} sP) fQ₁)
...   | inj₂ fQ₂ = inj₂ (fail-τ-prepend (△-τ-lift-P {Q = Q₂} sP) fQ₂)
-- Q₁⊓Q₂'s own τ resolves the choice to Qᵢ: the continuation failure is from P△Qᵢ.
△-⊓R-fail-elim P Q₁ Q₂ (⟹-τ step rest) ref | △τQ sQ with ⊓-τ-inv Q₁ Q₂ sQ
...   | inj₁ refl = inj₁ (_ , rest , ref)
...   | inj₂ refl = inj₂ (_ , rest , ref)
-- △τQret: force (Q₁⊓Q₂) ≡ ret r′ — impossible (it is react ∅v (br2 …)).
△-⊓R-fail-elim P Q₁ Q₂ (⟹-τ step rest) ref | △τQret eqQr = case eqQr of λ ()
-- △τ⊓P (force P ≡ ret r, M ≡ P): rest failure is from P; prepend P△Q₁ ─τ→ P (br2 tag0).
△-⊓R-fail-elim P Q₁ Q₂ (⟹-τ step rest) ref | △τ⊓P eqPr =
  inj₁ (fail-τ-prepend (△-toP-Pret P Q₁ eqPr) (_ , rest , ref))
-- △τ⊓Q (force P ≡ ret r, M ≡ Q₁⊓Q₂): rest failure is from Q₁⊓Q₂; ⊓-failures→ splits it,
-- and since force P ≡ ret r, P△Qᵢ ─τ→ Qᵢ (the br2 tag1) prepends.
△-⊓R-fail-elim P Q₁ Q₂ (⟹-τ step rest) ref | △τ⊓Q eqPr
  with ⊓-failures→ Q₁ Q₂ (_ , rest , ref)
...   | inj₁ fQ₁ = inj₁ (fail-τ-prepend (△-toQ-Pret P Q₁ eqPr) fQ₁)
...   | inj₂ fQ₂ = inj₂ (fail-τ-prepend (△-toQ-Pret P Q₂ eqPr) fQ₂)

-- ev-step: invert with △-ev-elim.  Only P's event can fire: Q₁⊓Q₂ = react ∅v offers
-- nothing, so △evQ/△evPQ are impossible (their Q-step contradicts ∅v).
△-⊓R-fail-elim P Q₁ Q₂ (⟹-ev step rest) ref with △-ev-elim P (Q₁ ⊓ Q₂) step
... | △evQ  sQ   = case ⊓-ev-impossible Q₁ Q₂ sQ of λ ()
... | △evPQ _ sQ = case ⊓-ev-impossible Q₁ Q₂ sQ of λ ()
-- P's event (→ P₁△(Q₁⊓Q₂)): recurse, prepend P's event via △-P-ev-fail-prepend.
△-⊓R-fail-elim P Q₁ Q₂ (⟹-ev step rest) ref | △evP {P₁ = P₁} sP
  with △-⊓R-fail-elim P₁ Q₁ Q₂ rest ref | sP
...   | inj₁ fQ₁ | sVis {at = at} {a = a} eqP brP = inj₁ (△-P-ev-fail-prepend P Q₁ eqP brP fQ₁)
...   | inj₂ fQ₂ | sVis {at = at} {a = a} eqP brP = inj₂ (△-P-ev-fail-prepend P Q₂ eqP brP fQ₂)

-------------------------------------------------------------------------------------
-- (L) the two failures⊥ refinements.
-------------------------------------------------------------------------------------

-- failures⊥ analogue of △-Qi→Q⊓ (the divergence intro-mapper):
-- failures⊥ (P△Qᵢ) s B → failures⊥ (P△(Q₁⊓Q₂)) s B, where `Q₁⊓Q₂ ─τ→ Qᵢ` is the
-- supplied resolving τ.  The divergence summand reuses △-Qi→Q⊓; the failures summand
-- mirrors it: P live ⇒ lift the resolving τ through △ on the Q-side; P=ret ⇒ P△· = P⊓·
-- (equal force), split via ⊓-failures→, P-failure transfers back (⊓-failures←l), a
-- Qᵢ-failure becomes a (Q₁⊓Q₂)-failure (the supplied ⊓-back) ⇒ ⊓-failures←r.
△-Qi→Q⊓-f : (P Q₁ Q₂ Qᵢ : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
          → ((Q₁ ⊓ Q₂) ─[ τ ]─► Qᵢ)
          → (∀ {Y : Event√ R → Set ℓx} → failures Qᵢ s Y → failures (Q₁ ⊓ Q₂) s Y)
          → failures (P △ Qᵢ) s X → failures (P △ (Q₁ ⊓ Q₂)) s X
△-Qi→Q⊓-f P Q₁ Q₂ Qᵢ sQ ⊓-back f with PTree.force P in eqP
... | sil _    = fail-τ-prepend (△-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) sQ) f
... | react _ _ = fail-τ-prepend (△-τ-lift-Q {P = P} (subst NonRet (sym eqP) tt0) sQ) f
... | ret r    with ⊓-failures→ P Qᵢ (△-fail-to-⊓ P Qᵢ eqP f)
...   | inj₁ fP  = ⊓-fail-to-△ P (Q₁ ⊓ Q₂) eqP (⊓-failures←l P (Q₁ ⊓ Q₂) fP)
...   | inj₂ fQᵢ = ⊓-fail-to-△ P (Q₁ ⊓ Q₂) eqP (⊓-failures←r P (Q₁ ⊓ Q₂) (⊓-back fQᵢ))

△-Qi→Q⊓-f⊥ : (P Q₁ Q₂ Qᵢ : PTree E (ExtI E) R) {s : List (Event√ R)} {B : Event√ R → Set ℓr}
           → ((Q₁ ⊓ Q₂) ─[ τ ]─► Qᵢ)
           → (∀ {Y : Event√ R → Set ℓr} → failures Qᵢ s Y → failures (Q₁ ⊓ Q₂) s Y)
           → (divergences Qᵢ s → divergences (Q₁ ⊓ Q₂) s)
           → failures⊥ (P △ Qᵢ) s B → failures⊥ (P △ (Q₁ ⊓ Q₂)) s B
△-Qi→Q⊓-f⊥ P Q₁ Q₂ Qᵢ sQ ⊓-back-f ⊓-back-d (inj₁ f) =
  inj₁ (△-Qi→Q⊓-f P Q₁ Q₂ Qᵢ sQ ⊓-back-f f)
△-Qi→Q⊓-f⊥ P Q₁ Q₂ Qᵢ sQ ⊓-back-f ⊓-back-d (inj₂ d) =
  inj₂ (△-Qi→Q⊓ P Q₁ Q₂ Qᵢ sQ ⊓-back-d d)

-- EASY (intro): a failures⊥ of (P△Q₁)⊓(P△Q₂) splits; map each summand to P△(Q₁⊓Q₂).
△-⊓R-dist-⊑F⊥ : (P Q₁ Q₂ : PTree E (ExtI E) R)
              → (P △ (Q₁ ⊓ Q₂)) ⊑F⊥ ((P △ Q₁) ⊓ (P △ Q₂))
△-⊓R-dist-⊑F⊥ P Q₁ Q₂ f with ⊓-failures⊥→ (P △ Q₁) (P △ Q₂) f
... | inj₁ fQ₁ = △-Qi→Q⊓-f⊥ P Q₁ Q₂ Q₁ (⊓-stepL Q₁ Q₂) (⊓-failures←l Q₁ Q₂) (⊓-div←l Q₁ Q₂) fQ₁
... | inj₂ fQ₂ = △-Qi→Q⊓-f⊥ P Q₁ Q₂ Q₂ (⊓-stepR Q₁ Q₂) (⊓-failures←r Q₁ Q₂) (⊓-div←r Q₁ Q₂) fQ₂

-- HARD (elim): a failures⊥ of P△(Q₁⊓Q₂) routes through △-⊓R-fail-elim / △-⊓R-div-elim.
△-⊓R-dist-⊒F⊥ : (P Q₁ Q₂ : PTree E (ExtI E) R)
              → ((P △ Q₁) ⊓ (P △ Q₂)) ⊑F⊥ (P △ (Q₁ ⊓ Q₂))
△-⊓R-dist-⊒F⊥ P Q₁ Q₂ (inj₁ (W , reach , ref)) with △-⊓R-fail-elim P Q₁ Q₂ reach ref
... | inj₁ fQ₁ = ⊓-failures⊥←l (P △ Q₁) (P △ Q₂) (inj₁ fQ₁)
... | inj₂ fQ₂ = ⊓-failures⊥←r (P △ Q₁) (P △ Q₂) (inj₁ fQ₂)
△-⊓R-dist-⊒F⊥ P Q₁ Q₂ (inj₂ d) with △-⊓R-div-elim P Q₁ Q₂ d
... | inj₁ dQ₁ = ⊓-failures⊥←l (P △ Q₁) (P △ Q₂) (inj₂ dQ₁)
... | inj₂ dQ₂ = ⊓-failures⊥←r (P △ Q₁) (P △ Q₂) (inj₂ dQ₂)

-------------------------------------------------------------------------------------
-- (M) the law: pair the two ⊑F⊥ and the two ⊑D refinements.
-------------------------------------------------------------------------------------

△-⊓R-dist-FD : (P Q₁ Q₂ : PTree E (ExtI E) R)
             → (P △ (Q₁ ⊓ Q₂)) ≈FD ((P △ Q₁) ⊓ (P △ Q₂))
△-⊓R-dist-FD P Q₁ Q₂ =
  (△-⊓R-dist-⊑F⊥ P Q₁ Q₂ , △-⊓R-dist-⊑D P Q₁ Q₂) ,
  (△-⊓R-dist-⊒F⊥ P Q₁ Q₂ , △-⊓R-dist-⊒D P Q₁ Q₂)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- The STEP law ⟨△-step⟩ (UCS 7.5 / Fig 13.6):
--      (e ⟶ P) △ (f ⟶ Q)  ≈FD  (e ⟶ (λ x → P x △ (f ⟶ Q))) □ (f ⟶ Q)
--
-- Both sides are STABLE pure-visible `react` nodes: a prefix is `react _ ∅t`, so the
-- interrupt's τ-part (△-τ, which reads each side's `viewT = ∅t`) and the external
-- choice's τ-part (□-mt, ditto) are everywhere `nothing`.  Neither side performs a τ,
-- so a strong bisimulation only has to match the VISIBLE offers.  We build the
-- `Sbisim` directly and push it through sbisim→drbisim then drbisim→≈FD.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- Step 1 — the overlap-continuation bridge.  When BOTH prefixes offer the same event,
-- the interrupt's `△-merge` yields `ptree (react ∅v (△-br2 P₁ Q Q₁))`, whereas the
-- external choice's `mergeMaybe (just _) (just _)` yields `(P₁ △ Q) ⊓ Q₁`.  These force
-- to `react ∅v (△-br2 P₁ Q Q₁)` and `react ∅v (br2 (P₁△Q) Q₁)` respectively — pointwise
-- equal τ-branch functions, but NOT definitionally equal (η on the branch function).
-- The two branch functions agree at every index, so each τ-step of one lands on the
-- SAME target the other reaches, and we close with `sbisim-refl`.

-- pointwise agreement of the two τ-branch functions.
△-br2≐br2 : ∀ {ℓr} {R : Set ℓr} (P₁ Q Q₁ : PTree E (ExtI E) R)
            (i : AnyTypes (ExtI E)) (a : proj₁ i)
          → △-br2 P₁ Q Q₁ i a ≡ br2 (P₁ △ Q) Q₁ i a
△-br2≐br2 P₁ Q Q₁ (_ , fin)      (lift fzero)               = refl
△-br2≐br2 P₁ Q Q₁ (_ , fin)      (lift (fsuc fzero))        = refl
△-br2≐br2 P₁ Q Q₁ (_ , fin)      (lift (fsuc (fsuc _)))     = refl
△-br2≐br2 P₁ Q Q₁ (_ , base _)   _                          = refl
△-br2≐br2 P₁ Q Q₁ (_ , pair _ _) _                          = refl

△-br2∼⊓ : ∀ {ℓr} {R : Set ℓr} (P₁ Q Q₁ : PTree E (ExtI E) R)
        → Sbisim R (ptree (react ∅v (△-br2 P₁ Q Q₁))) ((P₁ △ Q) ⊓ Q₁)
-- fwd: a τ of the `△-br2` node transports to the SAME target via `br2` (and back).
△-br2∼⊓ P₁ Q Q₁ .Sbisim.fwd .SSimF.on-ev (sVis refl ())
△-br2∼⊓ P₁ Q Q₁ .Sbisim.fwd .SSimF.on-tau (sTau {i = i} {a = a} refl br) =
  _ , sTau {i = i} {a = a} refl (trans (sym (△-br2≐br2 P₁ Q Q₁ i a)) br) , sbisim-refl _
△-br2∼⊓ P₁ Q Q₁ .Sbisim.bwd .SSimF.on-ev (sVis refl ())
△-br2∼⊓ P₁ Q Q₁ .Sbisim.bwd .SSimF.on-tau (sTau {i = i} {a = a} refl br) =
  _ , sTau {i = i} {a = a} refl (trans (△-br2≐br2 P₁ Q Q₁ i a) br) , sbisim-refl _

-------------------------------------------------------------------------------------
-- Step 2 — the offer-matching strong bisimulation.
--
-- LHS = (e⟶P) △ (f⟶Q)        forces to  react (△-merge nE nF (f⟶Q)) (△-τ nE nF _ _)
-- RHS = (e⟶P′) □ (f⟶Q)        forces to  react (mergeVis (viewV nE′) (viewV nF))
--                                              (□-mt nE′ nF _ _)
--   where  P′ = λ x → P x △ (f ⟶ Q),  nE = react (Prefix-cont e P) ∅t,  etc.
-- Both τ-parts read each operand's `viewT = ∅t` (the prefix has no τ), so they are
-- everywhere `nothing`: no τ-step on either side.  We only match visible offers.
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {A B : Set ℓ}
         (e : E A) (P : A → PTree E (ExtI E) R)
         (f : E B) (Q : B → PTree E (ExtI E) R) where

  private
    P′ : A → PTree E (ExtI E) R
    P′ x = P x △ (f ⟶ Q)

    nE nF : NodeKind E (ExtI E) R
    nE = react (Prefix-cont e P) ∅t
    nF = react (Prefix-cont f Q) ∅t

    nE′ : NodeKind E (ExtI E) R
    nE′ = react (Prefix-cont e P′) ∅t

    LHS RHS : PTree E (ExtI E) R
    LHS = (e ⟶ P) △ (f ⟶ Q)
    RHS = (e ⟶ P′) □ (f ⟶ Q)

  -- LHS forces to the both-live interrupt node (both prefixes are NonRet).
  force-LHS : PTree.force LHS ≡ react (△-merge nE nF (f ⟶ Q)) (△-τ nE nF (e ⟶ P) (f ⟶ Q))
  force-LHS = force-△-mt {P = e ⟶ P} {Q = f ⟶ Q} refl refl tt0 tt0

  -- RHS forces to the both-live external-choice node (definitional: both prefixes react).
  force-RHS : PTree.force RHS ≡ react (mergeVis (viewV nE′) (viewV nF)) (□-mt nE′ nF (e ⟶ P′) (f ⟶ Q))
  force-RHS = refl

  -- The single offer-relation lemma: at every (at , a) the LHS visible offer and the
  -- RHS visible offer are both `nothing`, or both `just` with strongly-bisimilar
  -- targets.  Derived directly by casing the two prefix decisions `E-≟ (A,e) at` and
  -- `E-≟ (B,f) at`, which is exactly what both `△-merge`/`Prefix-cont` and
  -- `mergeVis`/`Prefix-cont` dispatch on.
  step-offer : (at : AnyTypes E) (a : proj₁ at) {t : PTree E (ExtI E) R}
             → △-merge nE nF (f ⟶ Q) at a ≡ just t
             → Σ[ u ∈ PTree E (ExtI E) R ]
                 (mergeVis (viewV nE′) (viewV nF) at a ≡ just u × Sbisim R t u)
  step-offer at a eq with E-≟ (A , e) at | E-≟ (B , f) at
  -- e offers, f does not: △-merge fires P-side wrapped; mergeVis = just (P′ x)
  ... | yes refl | no _ rewrite eq = _ , refl , sbisim-refl _
  -- f offers (interrupt fires), e does not: △-merge = just (Q y); mergeVis = just (Q y)
  ... | no _ | yes refl rewrite eq = _ , refl , sbisim-refl _
  -- both offer the same event: △-merge = just (react ∅v (△-br2 ..)); mergeVis = just (..⊓..)
  ... | yes refl | yes refl with eq
  ...   | refl = _ , refl , △-br2∼⊓ _ (f ⟶ Q) _
  -- neither offers: △-merge = nothing, contradiction with the `just` premise.
  step-offer at a eq | no _ | no _ = case eq of λ ()

  -- the reverse offer-relation lemma (RHS offer ⇒ matching LHS offer, ∼-related targets).
  step-offer⁻ : (at : AnyTypes E) (a : proj₁ at) {u : PTree E (ExtI E) R}
              → mergeVis (viewV nE′) (viewV nF) at a ≡ just u
              → Σ[ t ∈ PTree E (ExtI E) R ]
                  (△-merge nE nF (f ⟶ Q) at a ≡ just t × Sbisim R t u)
  step-offer⁻ at a eq with E-≟ (A , e) at | E-≟ (B , f) at
  ... | yes refl | no _ rewrite eq = _ , refl , sbisim-refl _
  ... | no _ | yes refl rewrite eq = _ , refl , sbisim-refl _
  ... | yes refl | yes refl with eq
  ...   | refl = _ , refl , △-br2∼⊓ _ (f ⟶ Q) _
  step-offer⁻ at a eq | no _ | no _ = case eq of λ ()

  -- no τ on either side: LHS τ-part is △-τ (reads each prefix's viewT = ∅t ⇒ nothing);
  -- RHS τ-part is □-mt (ditto).  Both branch functions are everywhere `nothing`.
  △-τ-prefixes-⊥ : ∀ {t} → LHS ─[ τ ]─► t → ⊥
  △-τ-prefixes-⊥ (sSil sile) = case trans (sym sile) force-LHS of λ ()
  △-τ-prefixes-⊥ (sTau {i = _ , base _}   refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , fin}      refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , pair (base _)   _} refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , pair (pair _ _) _} refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift fzero        , a} refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , a} refl ())
  △-τ-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , a} refl ())

  □-mt-prefixes-⊥ : ∀ {u} → RHS ─[ τ ]─► u → ⊥
  □-mt-prefixes-⊥ (sSil sile) = case sile of λ ()
  □-mt-prefixes-⊥ (sTau {i = _ , base _}   refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , fin}      refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , pair (base _)   _} refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , pair (pair _ _) _} refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift fzero        , a} refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , a} refl ())
  □-mt-prefixes-⊥ (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , a} refl ())

  △-step-sbisim : Sbisim R LHS RHS
  -- fwd
  △-step-sbisim .Sbisim.fwd .SSimF.on-ev (sVis eqf br)
    with refl ← trans (sym force-LHS) eqf
    with (u , eqRHS , rel) ← step-offer _ _ br =
      u , sVis force-RHS eqRHS , rel
  △-step-sbisim .Sbisim.fwd .SSimF.on-tau step = case △-τ-prefixes-⊥ step of λ ()
  -- bwd
  △-step-sbisim .Sbisim.bwd .SSimF.on-ev (sVis eqf br)
    with refl ← trans (sym force-RHS) eqf
    with (t , eqLHS , rel) ← step-offer⁻ _ _ br =
      t , sVis force-LHS eqLHS , sbisim-sym rel
  △-step-sbisim .Sbisim.bwd .SSimF.on-tau step = case □-mt-prefixes-⊥ step of λ ()

-------------------------------------------------------------------------------------
-- Step 3 — assemble: strong bisim ⇒ ≈DR ⇒ ≈FD.
-------------------------------------------------------------------------------------

△-step-FD : ∀ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄ {A B : Set ℓ}
            (e : E A) (P : A → PTree E (ExtI E) R)
            (f : E B) (Q : B → PTree E (ExtI E) R)
          → ((e ⟶ P) △ (f ⟶ Q)) ≈FD ((e ⟶ (λ x → P x △ (f ⟶ Q))) □ (f ⟶ Q))
△-step-FD e P f Q =
  drbisim→≈FD (sbisim→drbisim (△-step-sbisim e P f Q))

-------------------------------------------------------------------------------------
-- ⟨△-step⟩ over the full prefix-CHOICE menus (U7.5 proper, A,B = event SETS):
--      (?x:A→P) △ (?x:B→Q)  ≈FD  (?x:A→(P △ (?x:B→Q))) □ (?x:B→Q)
--    = (pchoice v) △ (pchoice w)  ≈FD  (pchoice (△-cont-menu v w)) □ (pchoice w)
-- with △-cont-menu v w at a = map (·△ pchoice w) (v at a)  (each v-offer wrapped ·△rhs).
-- The single-channel `△-step-FD` is the instance v=Prefix-cont e P, w=Prefix-cont f Q.
-- Same strong-bisim shape: both sides STABLE pure-visible (τ-parts △-τ/□-mt read
-- viewT (react _ ∅t) = ∅t = nothing); offers matched by casing `v at a | w at a`
-- (replacing the single-channel `E-≟` casing), reusing `△-br2∼⊓` for the both-offer ⊓.
-------------------------------------------------------------------------------------

-- the A-side continuation menu: each surviving v-offer wrapped as (·△ pchoice w).
△-cont-menu : ∀ {ℓr} {R : Set ℓr}
              (v w : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
            → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
△-cont-menu v w at a = map (λ Pc → Pc △ pchoice w) (v at a)

module _ {ℓr} {R : Set ℓr} ⦃ _ : DecEq R ⦄
         (v w : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) where

  private
    nEv nFw : NodeKind E (ExtI E) R
    nEv = react v ∅t
    nFw = react w ∅t

    nE′v : NodeKind E (ExtI E) R
    nE′v = react (△-cont-menu v w) ∅t

    LHSm RHSm : PTree E (ExtI E) R
    LHSm = (pchoice v) △ (pchoice w)
    RHSm = (pchoice (△-cont-menu v w)) □ (pchoice w)

    force-LHSm : PTree.force LHSm
               ≡ react (△-merge nEv nFw (pchoice w)) (△-τ nEv nFw (pchoice v) (pchoice w))
    force-LHSm = force-△-mt {P = pchoice v} {Q = pchoice w} refl refl tt0 tt0

    force-RHSm : PTree.force RHSm
               ≡ react (mergeVis (viewV nE′v) (viewV nFw)) (□-mt nE′v nFw (pchoice (△-cont-menu v w)) (pchoice w))
    force-RHSm = refl

    step-offer-m : (at : AnyTypes E) (a : proj₁ at) {t : PTree E (ExtI E) R}
                 → △-merge nEv nFw (pchoice w) at a ≡ just t
                 → Σ[ u ∈ PTree E (ExtI E) R ]
                     (mergeVis (viewV nE′v) (viewV nFw) at a ≡ just u × Sbisim R t u)
    step-offer-m at a eq with v at a | w at a
    ... | just Pc | nothing rewrite eq = _ , refl , sbisim-refl _
    ... | nothing | just Qc rewrite eq = _ , refl , sbisim-refl _
    ... | just Pc | just Qc with eq
    ...   | refl = _ , refl , △-br2∼⊓ _ (pchoice w) _
    step-offer-m at a eq | nothing | nothing = case eq of λ ()

    step-offer⁻-m : (at : AnyTypes E) (a : proj₁ at) {u : PTree E (ExtI E) R}
                  → mergeVis (viewV nE′v) (viewV nFw) at a ≡ just u
                  → Σ[ t ∈ PTree E (ExtI E) R ]
                      (△-merge nEv nFw (pchoice w) at a ≡ just t × Sbisim R t u)
    step-offer⁻-m at a eq with v at a | w at a
    ... | just Pc | nothing rewrite eq = _ , refl , sbisim-refl _
    ... | nothing | just Qc rewrite eq = _ , refl , sbisim-refl _
    ... | just Pc | just Qc with eq
    ...   | refl = _ , refl , △-br2∼⊓ _ (pchoice w) _
    step-offer⁻-m at a eq | nothing | nothing = case eq of λ ()

    △-τ-⊥m : ∀ {t} → LHSm ─[ τ ]─► t → ⊥
    △-τ-⊥m (sSil sile) = case trans (sym sile) force-LHSm of λ ()
    △-τ-⊥m (sTau {i = _ , base _}   refl ())
    △-τ-⊥m (sTau {i = _ , fin}      refl ())
    △-τ-⊥m (sTau {i = _ , pair (base _)   _} refl ())
    △-τ-⊥m (sTau {i = _ , pair (pair _ _) _} refl ())
    △-τ-⊥m (sTau {i = _ , pair fin _} {a = lift fzero        , a} refl ())
    △-τ-⊥m (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , a} refl ())
    △-τ-⊥m (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , a} refl ())

    □-mt-⊥m : ∀ {u} → RHSm ─[ τ ]─► u → ⊥
    □-mt-⊥m (sSil sile) = case sile of λ ()
    □-mt-⊥m (sTau {i = _ , base _}   refl ())
    □-mt-⊥m (sTau {i = _ , fin}      refl ())
    □-mt-⊥m (sTau {i = _ , pair (base _)   _} refl ())
    □-mt-⊥m (sTau {i = _ , pair (pair _ _) _} refl ())
    □-mt-⊥m (sTau {i = _ , pair fin _} {a = lift fzero        , a} refl ())
    □-mt-⊥m (sTau {i = _ , pair fin _} {a = lift (fsuc fzero) , a} refl ())
    □-mt-⊥m (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , a} refl ())

    △-step-menu-sbisim : Sbisim R LHSm RHSm
    △-step-menu-sbisim .Sbisim.fwd .SSimF.on-ev (sVis eqf br)
      with refl ← trans (sym force-LHSm) eqf
      with (u , eqRHS , rel) ← step-offer-m _ _ br =
        u , sVis force-RHSm eqRHS , rel
    △-step-menu-sbisim .Sbisim.fwd .SSimF.on-tau step = case △-τ-⊥m step of λ ()
    △-step-menu-sbisim .Sbisim.bwd .SSimF.on-ev (sVis eqf br)
      with refl ← trans (sym force-RHSm) eqf
      with (t , eqLHS , rel) ← step-offer⁻-m _ _ br =
        t , sVis force-LHSm eqLHS , sbisim-sym rel
    △-step-menu-sbisim .Sbisim.bwd .SSimF.on-tau step = case □-mt-⊥m step of λ ()

  -- (?x:A→P) △ (?x:B→Q)  ≈FD  (?x:A→(P △ (?x:B→Q))) □ (?x:B→Q)     (menu version of U7.5)
  △-step-menu-FD : ((pchoice v) △ (pchoice w))
                 ≈FD ((pchoice (△-cont-menu v w)) □ (pchoice w))
  △-step-menu-FD = drbisim→≈FD (sbisim→drbisim △-step-menu-sbisim)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- The SLIDING-P row of UCS Fig 13.6, DIVERGENCE half:
--      ((e ⟶ P) ▷ P′) △ Q  ≈D  (e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)
--
-- Write  S = (e ⟶ P) ▷ P′,  LHS = S △ Q,  RHS = (e ⟶ P″) ▷ (P′ △ Q),  P″ x = P x △ Q.
--
--   * `force S = react (Prefix-cont e P) (▷-slide (force (e⟶P)) P′)` — NonRet; S's only
--     τ is the timeout S ─τ→ P′ (its (e⟶P)-own-τ uses viewT ∅t = nothing), and its only
--     visible offer is P's prefix offer x ⇒ S ─[ev x]→ P x.
--   * RHS's only τ is the timeout RHS ─τ→ P′△Q; RHS's only visible offer is x ⇒ RHS
--     ─[ev x]→ P x △ Q (= P″ x).
--   * LHS and RHS AGREE on the e-events (→ P x △ Q) and the timeout τ (→ P′△Q).  LHS
--     ADDITIONALLY weaves Q (its τ-steps and interrupt events); that extra weaving is
--     FD-invisible — the slide node is unstable — which is what makes the law hold.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

private
  variable
    A : Set ℓ

-- S = (e⟶P) ▷ P′ forces to the slide node — NonRet, so its e-events / timeout classify
-- via ▷-ev-elim / ▷-τ-elim.
force-S-react : (e : E A) (P : A → PTree E (ExtI E) R) (P′ : PTree E (ExtI E) R)
             → PTree.force ((e ⟶ P) ▷ P′)
               ≡ react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)
force-S-react e P P′ = force-▷-react {P = e ⟶ P} {Q = P′} refl

-- iterate △-τ-prepend-Q over a τ*-chain on the right operand.
△-τ*-prepend-Q : (Pᵢ Qa Qc : PTree E (ExtI E) R) {s : List (Event√ R)}
               → Qa ─[τ*]─► Qc → divergences (Pᵢ △ Qc) s → divergences (Pᵢ △ Qa) s
△-τ*-prepend-Q Pᵢ Qa Qc τ*-refl              d = d
△-τ*-prepend-Q Pᵢ Qa Qc (τ*-step {t′ = Q1} sQ rest) d =
  △-τ-prepend-Q Pᵢ Qa Q1 sQ (△-τ*-prepend-Q Pᵢ Q1 Qc rest d)

-- a finite τ-chain in front of a divergence is still a divergence.
τ*-Diverges : {t u : PTree E (ExtI E) R} → t ─[τ*]─► u → Diverges u → Diverges t
τ*-Diverges τ*-refl              d = d
τ*-Diverges (τ*-step sτ rest)    d .Diverges.next = _
τ*-Diverges (τ*-step sτ rest)    d .Diverges.step = sτ
τ*-Diverges (τ*-step sτ rest)    d .Diverges.rest = τ*-Diverges rest d

-------------------------------------------------------------------------------------
-- Direction 1 — `⊑D` (EASY): LHS recovers every RHS divergence.
-- Every RHS-step (a prefix event, or the timeout τ) is matched by an LHS-step to the
-- SAME continuation, so a divergence record of RHS maps to one of LHS step-by-step.
-- No recursion: once RHS takes any step the rest reaches a root-divergent W, giving a
-- `divergences (target) pre`; the matching LHS step prepends.
-------------------------------------------------------------------------------------

-- RHS's prefix offer at (at , a) ⇒ LHS = S △ Q offers it too (S's prefix offer wrapped):
-- the two prefixes `e⟶P` (under S) and `e⟶(λx→ P x △ Q)` (under RHS) dispatch on the
-- SAME `E-≟ (A,e) at`; when it fires, RHS's target P x △ Q is exactly the △-wrap of S's
-- target P x.  So a divergence after RHS's event becomes one after LHS's event.
slide-RHS-ev→LHS-div :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R} {s : List (Event√ R)}
  → Prefix-cont e (λ x → P x △ Q) at a ≡ just M
  → divergences M s
  → divergences (((e ⟶ P) ▷ P′) △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
slide-RHS-ev→LHS-div {A = A} e P P′ Q {at = at} {a = a} brM d with E-≟ (A , e) at
... | yes refl = △-P-ev-prepend ((e ⟶ P) ▷ P′) Q
                   {at = at} {a = a} {P₁ = P a}
                   (force-S-react e P P′)
                   (slide-S-offer)
                   (subst (λ z → divergences z _) (sym (just-injective brM)) d)
  where
    -- S's visible offer at (A,e) a is P a (the slide drops the continuation): it is
    -- exactly `Prefix-cont e P (A,e) a`, which fires `yes refl` to `just (P a)`.
    slide-S-offer : Prefix-cont e P at a ≡ just (P a)
    slide-S-offer with E-≟ (A , e) at
    ... | yes refl = refl
    ... | no ¬eq   = ⊥-elim (¬eq refl)
... | no ¬eq = case brM of λ ()

slide-RHS-reach-div :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
  → ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) ⟹⟨ pre ⟩ W → Diverges W
  → divergences (((e ⟶ P) ▷ P′) △ Q) pre
-- base: Diverges RHS ⇒ (▷-Diverges→) Diverges (e⟶P″) [impossible] or Diverges (P′△Q).
slide-RHS-reach-div e P P′ Q ⟹-refl divW
  with ▷-Diverges→ {P = e ⟶ (λ x → P x △ Q)} {Q = P′ △ Q} divW
... | inj₁ dpre = ⊥-elim (prefix-no-Diverges e (λ x → P x △ Q) dpre)
... | inj₂ dP′Q = div-τ-prepend
                    (△-τ-lift-P {Q = Q} (▷-timeout (e ⟶ P) P′ (refl) tt0))
                    (root-div→all-div dP′Q)
-- τ-step of RHS: the timeout (→ P′△Q) or the prefix's own τ (impossible).
slide-RHS-reach-div e P P′ Q (⟹-τ step rest) divW
  with ▷-τ-elim (e ⟶ (λ x → P x △ Q)) (P′ △ Q) step
... | inj₁ refl = div-τ-prepend
                    (△-τ-lift-P {Q = Q} (▷-timeout (e ⟶ P) P′ refl tt0))
                    (mk-div-from rest divW)
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ Pτ)
  where
    prefix-no-τ : ∀ {M} → (e ⟶ (λ x → P x △ Q)) ─[ τ ]─► M → ⊥
    prefix-no-τ (sSil sile) = case sile of λ ()
    prefix-no-τ (sTau refl br) = case br of λ ()
-- ev-step of RHS: a prefix event x ⇒ RHS → P x △ Q; LHS matches via slide-RHS-ev→LHS-div.
slide-RHS-reach-div e P P′ Q (⟹-ev step rest) divW
  with ▷-ev-elim (e ⟶ (λ x → P x △ Q)) (P′ △ Q) step
... | sVis {at = at} {a = a} eqf brM =
      slide-RHS-ev→LHS-div e P P′ Q
        {at = at} {a = a}
        (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) brM)
        (mk-div-from rest divW)
slide-RHS-reach-div e P P′ Q (⟹-ev step rest) divW | sRet eqf =
      ⊥-elim (case eqf of λ ())

△-slide-dist-⊑D : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                  (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
                → (((e ⟶ P) ▷ P′) △ Q) ⊑D ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q))
△-slide-dist-⊑D e P P′ Q d =
  subst (divergences (((e ⟶ P) ▷ P′) △ Q)) (sym (d .IsDivergence.split))
    (div-extension-closed
      (slide-RHS-reach-div e P P′ Q (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-------------------------------------------------------------------------------------
-- Direction 2 — `⊒D` (HARD): RHS recovers every LHS divergence.
--
-- LHS = S △ Q can additionally weave Q (Q's τ-steps and interrupt events) on top of the
-- shared offers; we must show those extra LHS behaviours are still RHS-divergences.  The
-- worker recurses on the big-step LHS ⟹⟨pre⟩ W (Diverges W), casing the FIRST step via
-- `△-τ-elim S Qc` / `△-ev-elim S Qc`.  Q evolves (Qc) under the woven τ-steps; we carry a
-- witness `Q ─τ*→ Qc` so every Qc-divergence maps back through RHS's ORIGINAL Q.
-------------------------------------------------------------------------------------

-- the both-offer node N = react ∅v (△-br2 P₁ Qc Qc₁): a τ goes to tag0 (P₁△Qc) or tag1 (Qc₁).
△-br2-node-τ-inv : (P₁ Qc Qc₁ : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
                 → ptree (react ∅v (△-br2 P₁ Qc Qc₁)) ─[ τ ]─► M
                 → (M ≡ (P₁ △ Qc)) ⊎ (M ≡ Qc₁)
△-br2-node-τ-inv P₁ Qc Qc₁ (sSil ())
△-br2-node-τ-inv P₁ Qc Qc₁ (sTau {i = _ , base _}   refl ())
△-br2-node-τ-inv P₁ Qc Qc₁ (sTau {i = _ , pair _ _} refl ())
△-br2-node-τ-inv P₁ Qc Qc₁ (sTau {i = _ , fin} {a = lift fzero}           refl refl) = inj₁ refl
△-br2-node-τ-inv P₁ Qc Qc₁ (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl refl) = inj₂ refl
△-br2-node-τ-inv P₁ Qc Qc₁ (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())

-- N is unstable (it always has tag0's τ).
△-br2-node-unstable : (P₁ Qc Qc₁ : PTree E (ExtI E) R)
                    → ¬ isStable (ptree (react ∅v (△-br2 P₁ Qc Qc₁)))
△-br2-node-unstable P₁ Qc Qc₁ st = case st (Lift ℓ (Fin 2) , fin) (lift fzero) of λ ()

-- a big-step out of N peels into its two τ-children.
△-br2-node-peel : (P₁ Qc Qc₁ : PTree E (ExtI E) R)
                    {s : List (Event√ R)} {W : PTree E (ExtI E) R}
                → ptree (react ∅v (△-br2 P₁ Qc Qc₁)) ⟹⟨ s ⟩ W
                → ((ptree (react ∅v (△-br2 P₁ Qc Qc₁)) ≡ W) × (s ≡ []))
                ⊎ ((P₁ △ Qc) ⟹⟨ s ⟩ W) ⊎ (Qc₁ ⟹⟨ s ⟩ W)
△-br2-node-peel P₁ Qc Qc₁ ⟹-refl = inj₁ (refl , refl)
△-br2-node-peel P₁ Qc Qc₁ (⟹-τ step rest) with △-br2-node-τ-inv P₁ Qc Qc₁ step
... | inj₁ refl = inj₂ (inj₁ rest)
... | inj₂ refl = inj₂ (inj₂ rest)
△-br2-node-peel P₁ Qc Qc₁ (⟹-ev (sRet ()) _)
△-br2-node-peel P₁ Qc Qc₁ (⟹-ev (sVis refl ()) _)

-- divergence of N splits to a divergence of one τ-child (mirror of ⊓-div→).
△-br2-node-div→ : (P₁ Qc Qc₁ : PTree E (ExtI E) R) {s : List (Event√ R)}
                → divergences (ptree (react ∅v (△-br2 P₁ Qc Qc₁))) s
                → divergences (P₁ △ Qc) s ⊎ divergences Qc₁ s
△-br2-node-div→ P₁ Qc Qc₁ {s = s} d with △-br2-node-peel P₁ Qc Qc₁ (d .IsDivergence.reach)
... | inj₂ (inj₁ reachL) =
        inj₁ (record { prefix = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
                     ; split  = d .IsDivergence.split  ; witness = d .IsDivergence.witness
                     ; reach  = reachL                 ; divwit  = d .IsDivergence.divwit })
... | inj₂ (inj₂ reachR) =
        inj₂ (record { prefix = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
                     ; split  = d .IsDivergence.split  ; witness = d .IsDivergence.witness
                     ; reach  = reachR                 ; divwit  = d .IsDivergence.divwit })
... | inj₁ (eqW , _) with subst Diverges (sym eqW) (d .IsDivergence.divwit)
...   | dN with △-br2-node-τ-inv P₁ Qc Qc₁ (dN .Diverges.step)
...     | inj₁ eqL = inj₁ (record { prefix = [] ; suffix = s ; split = refl
                                  ; witness = P₁ △ Qc ; reach = ⟹-refl
                                  ; divwit = subst Diverges eqL (dN .Diverges.rest) })
...     | inj₂ eqR = inj₂ (record { prefix = [] ; suffix = s ; split = refl
                                  ; witness = Qc₁ ; reach = ⟹-refl
                                  ; divwit = subst Diverges eqR (dN .Diverges.rest) })

-- RHS recovers S's visible offer wrapped with Q: S ─[ev x]→ S₁ ⇒ RHS ─[ev x]→ S₁ △ Q.
-- (S₁ is P's prefix continuation P a; RHS's prefix offers P″ a = P a △ Q = S₁ △ Q.)
slide-RHS-ev-step :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {x : Event√ R} {S₁ : PTree E (ExtI E) R}
  → ((e ⟶ P) ▷ P′) ─[ ev x ]─► S₁
  → ((e ⟶ (λ y → P y △ Q)) ▷ (P′ △ Q)) ─[ ev x ]─► (S₁ △ Q)
slide-RHS-ev-step {A = A} e P P′ Q {S₁ = S₁} step
  with ▷-ev-elim (e ⟶ P) P′ step
... | sVis {at = at} {a = a} eqf brP
      with brP′ ← subst (λ g → g at a ≡ just S₁) (sym (proj₁ (react-injective eqf))) brP
      with E-≟ (A , e) at
...     | no ¬eq   = case brP′ of λ ()
...     | yes refl = case (just-injective brP′) of λ where
              refl → sVis {at = at} {a = a}
                       (force-▷-react {P = e ⟶ (λ y → P y △ Q)} {Q = P′ △ Q} refl)
                       offerRHS
  where
    -- with `E-≟ (A,e) (A,e) = yes refl`, RHS's prefix offer reduces to `just (P a △ Q)`.
    offerRHS : Prefix-cont e (λ y → P y △ Q) at a ≡ just (P a △ Q)
    offerRHS with E-≟ (A , e) at
    ... | yes refl = refl
    ... | no ¬eq   = ⊥-elim (¬eq refl)

-- the RHS timeout: (e⟶P″) ▷ (P′△Q) ─τ→ P′△Q.  Prepend it to lift a (P′△Q)-divergence.
slide-RHS-timeout-prepend :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R) {s : List (Event√ R)}
  → divergences (P′ △ Q) s
  → divergences ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) s
slide-RHS-timeout-prepend e P P′ Q d =
  div-τ-prepend (▷-timeout (e ⟶ (λ x → P x △ Q)) (P′ △ Q) refl tt0) d

-- the worker.  S = (e⟶P) ▷ P′ fixed; Qc the (τ*-)evolved right operand; q* : Q ─τ*→ Qc.
△-slide-reach-div-go :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q Qc : PTree E (ExtI E) R)
    {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc
  → (((e ⟶ P) ▷ P′) △ Qc) ⟹⟨ pre ⟩ W → Diverges W
  → divergences ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) pre
-- base: root-divergence of S △ Qc ⇒ Diverges S or Diverges Qc.
△-slide-reach-div-go e P P′ Q Qc q* ⟹-refl divW
  with △-Diverges→ {P = (e ⟶ P) ▷ P′} {Q = Qc} divW
... | inj₂ dQc with τ*-Diverges q* dQc
...   | dQ = slide-RHS-timeout-prepend e P P′ Q
              (root-div→all-div (△-Diverges-R {P = P′} {Q = Q} dQ))
△-slide-reach-div-go e P P′ Q Qc q* ⟹-refl divW | inj₁ dS
  with ▷-Diverges→ {P = e ⟶ P} {Q = P′} dS
...   | inj₁ dpre = ⊥-elim (prefix-no-Diverges e P dpre)
...   | inj₂ dP′  = slide-RHS-timeout-prepend e P P′ Q
                      (root-div→all-div (△-Diverges-L {P = P′} {Q = Q} dP′))
-- τ-step: invert via △-τ-elim S Qc.
△-slide-reach-div-go e P P′ Q Qc q* (⟹-τ step rest) divW
  with △-τ-elim ((e ⟶ P) ▷ P′) Qc step
-- S's own τ: the slide timeout (→ P′) or the prefix's own τ (impossible) ⇒ M = P′△Qc.
... | △τP sS with ▷-τ-elim (e ⟶ P) P′ sS
...   | inj₁ refl = slide-RHS-timeout-prepend e P P′ Q
                      (△-τ*-prepend-Q P′ Q Qc q* (mk-div-from rest divW))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ Pτ)
  where
    prefix-no-τ : ∀ {M} → (e ⟶ P) ─[ τ ]─► M → ⊥
    prefix-no-τ (sSil sile) = case sile of λ ()
    prefix-no-τ (sTau refl br) = case br of λ ()
-- Qc's τ (→ S △ Qc′): recurse, extending q* with this τ.
△-slide-reach-div-go e P P′ Q Qc q* (⟹-τ step rest) divW | △τQ {Q′ = Qc′} sQ =
      △-slide-reach-div-go e P P′ Q Qc′ (τ*-trans q* (τ*-step sQ τ*-refl)) rest divW
-- Qc's √-interrupt (force Qc ≡ ret r′ ⇒ M ≡ Qc): the rest big-step is from Qc.
△-slide-reach-div-go e P P′ Q Qc q* (⟹-τ step rest) divW | △τQret eqQcr =
      slide-RHS-timeout-prepend e P P′ Q
        (△-τ*-prepend-Q P′ Q Qc q*
          (div-τ-prepend (△-toQ-Qret P′ Qc eqQcr) (mk-div-from rest divW)))
-- △τ⊓P / △τ⊓Q carry force S ≡ ret r — impossible (force S = react …).
△-slide-reach-div-go e P P′ Q Qc q* (⟹-τ step rest) divW | △τ⊓P eqSr =
      case trans (sym (force-S-react e P P′)) eqSr of λ ()
△-slide-reach-div-go e P P′ Q Qc q* (⟹-τ step rest) divW | △τ⊓Q eqSr =
      case trans (sym (force-S-react e P P′)) eqSr of λ ()
-- ev-step: invert via △-ev-elim S Qc.
△-slide-reach-div-go e P P′ Q Qc q* (⟹-ev step rest) divW
  with △-ev-elim ((e ⟶ P) ▷ P′) Qc step
-- S's event (→ P₁△Qc): RHS offers it (wrapped) — direct prepend, P₁△Qc → P₁△Q via q*.
... | △evP {P₁ = P₁} sS =
      div-ev-prepend (slide-RHS-ev-step e P P′ Q sS)
                     (△-τ*-prepend-Q P₁ Q Qc q* (mk-div-from rest divW))
-- Qc's interrupt event (→ Qc₁): recover via timeout, then P′△Qc fires Qc's offer.
... | △evQ {Q₁ = Qc₁} sQ =
      slide-RHS-timeout-prepend e P P′ Q
        (△-τ*-prepend-Q P′ Q Qc q*
          (△-Q-ev-prepend P′ Qc sQ (mk-div-from rest divW)))
-- both offer the event: the both-offer node splits to P₁△Qc (RHS event) or Qc₁ (timeout).
... | △evPQ {P₁ = P₁} {Q₁ = Qc₁} sS sQ
      with △-br2-node-div→ P₁ Qc Qc₁ (mk-div-from rest divW)
...   | inj₁ dL = div-ev-prepend (slide-RHS-ev-step e P P′ Q sS)
                                 (△-τ*-prepend-Q P₁ Q Qc q* dL)
...   | inj₂ dR = slide-RHS-timeout-prepend e P P′ Q
                   (△-τ*-prepend-Q P′ Q Qc q*
                     (△-Q-ev-prepend P′ Qc sQ dR))

△-slide-dist-⊒D : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                  (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
                → ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) ⊑D (((e ⟶ P) ▷ P′) △ Q)
△-slide-dist-⊒D e P P′ Q d =
  subst (divergences ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q))) (sym (d .IsDivergence.split))
    (div-extension-closed
      (△-slide-reach-div-go e P P′ Q Q τ*-refl
        (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- The SLIDING-P row of UCS Fig 13.6, FAILURES half + assembly:
--      ((e ⟶ P) ▷ P′) △ Q  ≈FD  (e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)
--
-- Mirrors the divergence half: a failures-specific worker (△-slide-fail-elim) with the
-- SAME case analysis as △-slide-reach-div-go, with `Refuses W X` replacing `Diverges W`
-- and `failures` / `fail-*-prepend` replacing `divergences` / `div-*-prepend`.  The refl
-- base needs NO König step — it is discharged by the unstability of LHS = S △ Qc.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

-- Step 1 — LHS = S △ Qc is unstable: S = (e⟶P)▷P′ has the always-enabled timeout τ
-- S ─τ→ P′, so LHS ─τ→ P′△Qc (lift via △-τ-lift-P), and a stable state performs no τ.
△-slide-unstable : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                   {e : E A} {P : A → PTree E (ExtI E) R} {P′ Q : PTree E (ExtI E) R}
                 → ¬ isStable ((((e ⟶ P) ▷ P′) △ Q))
△-slide-unstable {e = e} {P = P} {P′ = P′} {Q = Q} st =
  stable-no-τ st (△-τ-lift-P {Q = Q} (▷-timeout (e ⟶ P) P′ refl tt0))

-- iterate △-τ-fail-prepend-Q over a τ*-chain on the right operand (failures analogue of
-- △-τ*-prepend-Q).
△-τ*-fail-prepend-Q : (Pᵢ Qa Qc : PTree E (ExtI E) R)
                        {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                    → Qa ─[τ*]─► Qc → failures (Pᵢ △ Qc) s X → failures (Pᵢ △ Qa) s X
△-τ*-fail-prepend-Q Pᵢ Qa Qc τ*-refl                f = f
△-τ*-fail-prepend-Q Pᵢ Qa Qc (τ*-step {t′ = Q1} sQ rest) f =
  △-τ-fail-prepend-Q Pᵢ Qa Q1 sQ (△-τ*-fail-prepend-Q Pᵢ Q1 Qc rest f)

-- the RHS timeout: (e⟶P″) ▷ (P′△Q) ─τ→ P′△Q.  Prepend it to lift a (P′△Q)-failure.
slide-RHS-timeout-fail-prepend :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx}
  → failures (P′ △ Q) s X
  → failures ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) s X
slide-RHS-timeout-fail-prepend e P P′ Q f =
  fail-τ-prepend (▷-timeout (e ⟶ (λ x → P x △ Q)) (P′ △ Q) refl tt0) f

-- failure of the both-offer node N = react ∅v (△-br2 P₁ Qc Qc₁) splits to a failure of one
-- τ-child (failures analogue of △-br2-node-div→).  The refl peel-case yields `Refuses N X`,
-- but N is unstable (△-br2-node-unstable) ⇒ contradiction.
△-br2-node-fail→ : (P₁ Qc Qc₁ : PTree E (ExtI E) R)
                     {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                 → failures (ptree (react ∅v (△-br2 P₁ Qc Qc₁))) s X
                 → failures (P₁ △ Qc) s X ⊎ failures Qc₁ s X
△-br2-node-fail→ P₁ Qc Qc₁ (W , reach , ref) with △-br2-node-peel P₁ Qc Qc₁ reach
... | inj₂ (inj₁ reachL) = inj₁ (W , reachL , ref)
... | inj₂ (inj₂ reachR) = inj₂ (W , reachR , ref)
... | inj₁ (eqW , _) =
      ⊥-elim (△-br2-node-unstable P₁ Qc Qc₁
                (subst isStable (sym eqW) (proj₁ ref)))

-- Step 2 — the distribution-specific stable-failures elimination (recursion on the
-- big-step).  S = (e⟶P)▷P′ fixed; Qc the (τ*-)evolved right operand; q* : Q ─τ*→ Qc.
-- SAME case split as △-slide-reach-div-go with `Refuses W X` for `Diverges W`.
△-slide-fail-elim :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q Qc : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc
  → (((e ⟶ P) ▷ P′) △ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) s X
-- base: Refuses (S△Qc) gives isStable (S△Qc) — but S△Qc is unstable.  No König needed.
△-slide-fail-elim e P P′ Q Qc q* ⟹-refl (st , _) =
  ⊥-elim (△-slide-unstable {e = e} {P = P} {P′ = P′} {Q = Qc} st)
-- τ-step: invert via △-τ-elim S Qc.
△-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref
  with △-τ-elim ((e ⟶ P) ▷ P′) Qc step
-- S's own τ: the slide timeout (→ P′) or the prefix's own τ (impossible) ⇒ M = P′△Qc.
... | △τP sS with ▷-τ-elim (e ⟶ P) P′ sS
...   | inj₁ refl = slide-RHS-timeout-fail-prepend e P P′ Q
                      (△-τ*-fail-prepend-Q P′ Q Qc q* (_ , rest , ref))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ Pτ)
  where
    prefix-no-τ : ∀ {M} → (e ⟶ P) ─[ τ ]─► M → ⊥
    prefix-no-τ (sSil sile) = case sile of λ ()
    prefix-no-τ (sTau refl br) = case br of λ ()
-- Qc's τ (→ S △ Qc′): recurse, extending q* with this τ.
△-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | △τQ {Q′ = Qc′} sQ =
      △-slide-fail-elim e P P′ Q Qc′ (τ*-trans q* (τ*-step sQ τ*-refl)) rest ref
-- Qc's √-interrupt (force Qc ≡ ret r′ ⇒ M ≡ Qc): the rest big-step is from Qc.
△-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | △τQret eqQcr =
      slide-RHS-timeout-fail-prepend e P P′ Q
        (△-τ*-fail-prepend-Q P′ Q Qc q*
          (fail-τ-prepend (△-toQ-Qret P′ Qc eqQcr) (_ , rest , ref)))
-- △τ⊓P / △τ⊓Q carry force S ≡ ret r — impossible (force S = react …).
△-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | △τ⊓P eqSr =
      case trans (sym (force-S-react e P P′)) eqSr of λ ()
△-slide-fail-elim e P P′ Q Qc q* (⟹-τ step rest) ref | △τ⊓Q eqSr =
      case trans (sym (force-S-react e P P′)) eqSr of λ ()
-- ev-step: invert via △-ev-elim S Qc.
△-slide-fail-elim e P P′ Q Qc q* (⟹-ev step rest) ref
  with △-ev-elim ((e ⟶ P) ▷ P′) Qc step
-- S's event (→ P₁△Qc): RHS offers it (wrapped) — direct prepend, P₁△Qc → P₁△Q via q*.
... | △evP {P₁ = P₁} sS =
      fail-ev-prepend (slide-RHS-ev-step e P P′ Q sS)
                      (△-τ*-fail-prepend-Q P₁ Q Qc q* (_ , rest , ref))
-- Qc's interrupt event (→ Qc₁): recover via timeout, then P′△Qc fires Qc's offer.
... | △evQ {Q₁ = Qc₁} sQ =
      slide-RHS-timeout-fail-prepend e P P′ Q
        (△-τ*-fail-prepend-Q P′ Q Qc q*
          (△-Q-ev-fail-prepend P′ Qc sQ (_ , rest , ref)))
-- both offer the event: the both-offer node splits to P₁△Qc (RHS event) or Qc₁ (timeout).
... | △evPQ {P₁ = P₁} {Q₁ = Qc₁} sS sQ
      with △-br2-node-fail→ P₁ Qc Qc₁ (_ , rest , ref)
...   | inj₁ fL = fail-ev-prepend (slide-RHS-ev-step e P P′ Q sS)
                                  (△-τ*-fail-prepend-Q P₁ Q Qc q* fL)
...   | inj₂ fR = slide-RHS-timeout-fail-prepend e P P′ Q
                   (△-τ*-fail-prepend-Q P′ Q Qc q*
                     (△-Q-ev-fail-prepend P′ Qc sQ fR))

-------------------------------------------------------------------------------------
-- Step 3 — the two failures⊥ refinements.
-------------------------------------------------------------------------------------

-- LHS = S△Qa matches S's wrapped visible offer of S₁ at (at,a) to S₁△Qa.  S offers S₁
-- (the slide drops the continuation); if Qa ALSO offers x the merge lands on the both-offer
-- node, whose tag0 τ reaches S₁△Qa — so it is a `⟹` (ev then optional τ).  Generic over
-- the offered continuation S₁.  Forward declarations first (no mutual block).
slide-LHS-live : (S Qa S₁ : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at}
    {nQ : NodeKind E (ExtI E) R} {W : PTree E (ExtI E) R} {s : List (Event√ R)}
    {vS : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
    {τcS : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
  → PTree.force S ≡ react vS τcS → vS at a ≡ just S₁
  → PTree.force Qa ≡ nQ → NonRet nQ
  → (S₁ △ Qa) ⟹⟨ s ⟩ W
  → (S △ Qa) ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s ⟩ W
slide-LHS-live S Qa S₁ {at = at} {a = a} {nQ = nQ} {vS = vS} {τcS = τcS} eqS brS eqQa ntQ mrest
  with viewV nQ at a in eqVQ
... | nothing = ⟹-ev (sVis (force-△-mt {P = S} {Q = Qa} eqS eqQa tt0 ntQ)
                            (△-merge-noQ {Q = Qa} {P' = S₁} {at = at} {a = a}
                                         {nP = react vS τcS} {nQ = nQ} brS eqVQ)) mrest
... | just Q₁ = ⟹-ev (sVis (force-△-mt {P = S} {Q = Qa} eqS eqQa tt0 ntQ)
                            (△-merge-bothP-PQ {Q = Qa} {P' = S₁} {Q₁ = Q₁}
                                              {at = at} {a = a}
                                              {nP = react vS τcS} {nQ = nQ} brS eqVQ))
                      (⟹-τ (△-br2-τ-tag0 {Q = Qa} {P' = S₁} {Q₁ = Q₁}) mrest)

slide-LHS-go : (S Qa S₁ : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at}
    {W : PTree E (ExtI E) R} {s : List (Event√ R)}
    {vS : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
    {τcS : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
  → PTree.force S ≡ react vS τcS → vS at a ≡ just S₁
  → (S₁ △ Qa) ⟹⟨ s ⟩ W
  → (S △ Qa) ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s ⟩ W
slide-LHS-go S Qa S₁ {at = at} {a = a} {vS = vS} {τcS = τcS} eqS brS mrest
  with PTree.force Qa in eqQa
... | ret r′   = ⟹-ev (sVis (force-△-LR {P = S} {Q = Qa} eqS eqQa tt0)
                             (△-merge-Qret-noQ {Q = Qa} {P' = S₁} {at = at} {a = a}
                                               {nP = react vS τcS} brS)) mrest
... | sil _    = slide-LHS-live S Qa S₁ eqS brS eqQa tt0 mrest
... | react _ _ = slide-LHS-live S Qa S₁ eqS brS eqQa tt0 mrest

-- a prefix offer of RHS at (at,a) ⇒ LHS = S△Q matches it to the SAME target.  Both prefixes
-- dispatch on `E-≟ (A,e) at`; when it fires, RHS's target P a △ Q is the △-wrap of S's
-- offered continuation P a, which slide-LHS-go reaches.
slide-LHS-ev-match : (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at} {M W : PTree E (ExtI E) R} {s : List (Event√ R)}
  → Prefix-cont e (λ x → P x △ Q) at a ≡ just M
  → M ⟹⟨ s ⟩ W
  → (((e ⟶ P) ▷ P′) △ Q)
      ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s ⟩ W
slide-LHS-ev-match {A = A} e P P′ Q {at = at} {a = a} {M = M} brM mrest
  with E-≟ (A , e) at
... | yes refl =
        slide-LHS-go ((e ⟶ P) ▷ P′) Q (P a)
          (force-S-react e P P′) slide-S-offer
          (subst (λ z → z ⟹⟨ _ ⟩ _) (sym (just-injective brM)) mrest)
  where
    slide-S-offer : Prefix-cont e P at a ≡ just (P a)
    slide-S-offer with E-≟ (A , e) at
    ... | yes refl = refl
    ... | no ¬eq   = ⊥-elim (¬eq refl)
... | no ¬eq = case brM of λ ()

-- forward failures simulation: an RHS run reaching a REFUSING state W is matched by an
-- LHS = S△Q run to the SAME W (same Refuses).  RHS's only steps are the timeout τ (→ P′△Q)
-- and a prefix event x (→ P x △ Q); LHS matches each (timeout τ lifted, or S's wrapped event
-- via slide-LHS-ev-match), and the ⟹-refl base is discharged because RHS is unstable (it
-- always has the timeout τ) so `Refuses RHS X` is impossible.
slide-RHS-fail→LHS :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) ⟹⟨ s ⟩ W → Refuses W X
  → failures (((e ⟶ P) ▷ P′) △ Q) s X
-- base: Refuses RHS X gives isStable RHS — but RHS has the timeout τ.
slide-RHS-fail→LHS e P P′ Q ⟹-refl (st , _) =
  ⊥-elim (stable-no-τ st (▷-timeout (e ⟶ (λ x → P x △ Q)) (P′ △ Q) refl tt0))
slide-RHS-fail→LHS e P P′ Q (⟹-τ step rest) ref
  with ▷-τ-elim (e ⟶ (λ x → P x △ Q)) (P′ △ Q) step
-- RHS's timeout (→ P′△Q): rest+ref is failures (P′△Q) s X; lift LHS = S△Q ─τ→ P′△Q.
... | inj₁ refl =
      fail-τ-prepend (△-τ-lift-P {Q = Q} (▷-timeout (e ⟶ P) P′ refl tt0))
                     (_ , rest , ref)
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ Pτ)
  where
    prefix-no-τ : ∀ {M} → (e ⟶ (λ x → P x △ Q)) ─[ τ ]─► M → ⊥
    prefix-no-τ (sSil sile) = case sile of λ ()
    prefix-no-τ (sTau refl br) = case br of λ ()
slide-RHS-fail→LHS e P P′ Q (⟹-ev step rest) ref
  with ▷-ev-elim (e ⟶ (λ x → P x △ Q)) (P′ △ Q) step
-- RHS's prefix event x (→ P x △ Q): the rest run already witnesses failures (P x △ Q) s X;
-- the matching LHS event-segment (slide-LHS-ev-match) prefixes it to the SAME refusing W.
... | sVis {at = at} {a = a} eqf brM =
      _ , slide-LHS-ev-match e P P′ Q
            {at = at} {a = a}
            (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) brM)
            rest
        , ref
slide-RHS-fail→LHS e P P′ Q (⟹-ev step rest) ref | sRet eqf = ⊥-elim (case eqf of λ ())

-- EASY (LHS simulates RHS): a failures⊥ of RHS transfers to LHS.  The divergence summand
-- is △-slide-dist-⊑D; the failures summand replays via slide-RHS-fail→LHS (same W, same
-- Refuses) — RHS being unstable discharges the empty-run base cleanly.
△-slide-dist-⊑F⊥ : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                   (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
                 → (((e ⟶ P) ▷ P′) △ Q) ⊑F⊥ ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q))
△-slide-dist-⊑F⊥ e P P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (slide-RHS-fail→LHS e P P′ Q reach ref)
△-slide-dist-⊑F⊥ e P P′ Q (inj₂ d) = inj₂ (△-slide-dist-⊑D e P P′ Q d)

-- HARD (RHS recovers LHS): a failures⊥ of LHS routes through △-slide-fail-elim (failures
-- summand — a DIRECT ≈FD, so the elim already targets RHS) / △-slide-dist-⊒D (divergence
-- summand).
△-slide-dist-⊒F⊥ : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                   (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
                 → ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q)) ⊑F⊥ (((e ⟶ P) ▷ P′) △ Q)
△-slide-dist-⊒F⊥ e P P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (△-slide-fail-elim e P P′ Q Q τ*-refl reach ref)
△-slide-dist-⊒F⊥ e P P′ Q (inj₂ d) = inj₂ (△-slide-dist-⊒D e P P′ Q d)

-------------------------------------------------------------------------------------
-- Step 4 — the law: pair the two ⊑F⊥ and the two ⊑D refinements.
-------------------------------------------------------------------------------------

△-slide-dist-FD : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
                  (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
                → (((e ⟶ P) ▷ P′) △ Q) ≈FD ((e ⟶ (λ x → P x △ Q)) ▷ (P′ △ Q))
△-slide-dist-FD e P P′ Q =
  (△-slide-dist-⊑F⊥ e P P′ Q , △-slide-dist-⊑D e P P′ Q) ,
  (△-slide-dist-⊒F⊥ e P P′ Q , △-slide-dist-⊒D e P P′ Q)

-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------
-- MENU version of the SLIDING-P interrupt law (UCS Fig 13.6 over a prefix-CHOICE):
--   ((pchoice v) ▷ P′) △ Q  ≈FD  (pchoice (△Q-menu v Q)) ▷ (P′ △ Q)
-- where  △Q-menu v Q at a = map (·△ Q) (v at a)   ( = ?x:A→(P x △ Q) ).
-- The single-channel △-slide-dist-FD is the instance v = Prefix-cont e P.  SAME
-- FD-direct structure; only the prefix-specific lemmas are re-derived over `v`
-- (every `E-≟ (A,e) at` split becomes a `v at a` split), and everything generic
-- (△-br2-node-*, slide-LHS-go/live, △-τ*-(fail-)prepend-Q, △-Diverges-*, …) is reused.
-------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------

△Q-menu : ∀ {ℓr} {R : Set ℓr}
          (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          (Q : PTree E (ExtI E) R)
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
△Q-menu v Q at a = map (λ Pc → Pc △ Q) (v at a)

pchoice-no-τ : ∀ {ℓr} {R : Set ℓr}
               {w : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {M : PTree E (ExtI E) R}
             → (pchoice w) ─[ τ ]─► M → ⊥
pchoice-no-τ (sSil sile)   = case sile of λ ()
pchoice-no-τ (sTau refl br) = case br of λ ()

force-Sm-react : ∀ {ℓr} {R : Set ℓr}
                 (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                 (P′ : PTree E (ExtI E) R)
               → PTree.force ((pchoice v) ▷ P′) ≡ react v (▷-slide (react v ∅t) P′)
force-Sm-react v P′ = force-▷-react {P = pchoice v} {Q = P′} refl

-- RHS recovers S's visible offer wrapped with Q: S ─[ev x]→ S₁ ⇒ RHS ─[ev x]→ S₁ △ Q.
slide-RHS-ev-step-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R) {x : Event√ R} {S₁ : PTree E (ExtI E) R}
  → ((pchoice v) ▷ P′) ─[ ev x ]─► S₁
  → ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) ─[ ev x ]─► (S₁ △ Q)
slide-RHS-ev-step-m v P′ Q {S₁ = S₁} step with ▷-ev-elim (pchoice v) P′ step
... | sVis {at = at} {a = a} eqf brP =
      sVis {at = at} {a = a}
           (force-▷-react {P = pchoice (△Q-menu v Q)} {Q = P′ △ Q} refl)
           (cong (map (λ Pc → Pc △ Q))
                 (subst (λ g → g at a ≡ just S₁) (sym (proj₁ (react-injective eqf))) brP))

-- the RHS timeout: prepend it to lift a (P′△Q)-divergence.
slide-RHS-timeout-prepend-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R) {s : List (Event√ R)}
  → divergences (P′ △ Q) s
  → divergences ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) s
slide-RHS-timeout-prepend-m v P′ Q d =
  div-τ-prepend (▷-timeout (pchoice (△Q-menu v Q)) (P′ △ Q) refl tt0) d

-- Direction 1 — ⊑D : LHS recovers every RHS divergence.
slide-RHS-ev→LHS-div-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at} {M : PTree E (ExtI E) R} {s : List (Event√ R)}
  → △Q-menu v Q at a ≡ just M
  → divergences M s
  → divergences (((pchoice v) ▷ P′) △ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s)
slide-RHS-ev→LHS-div-m v P′ Q {at = at} {a = a} brM d with v at a in eqv
... | just Pc = △-P-ev-prepend ((pchoice v) ▷ P′) Q {at = at} {a = a} {P₁ = Pc}
                  (force-Sm-react v P′) eqv
                  (subst (λ z → divergences z _) (sym (just-injective brM)) d)
... | nothing = case brM of λ ()

slide-RHS-reach-div-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R)
    {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
  → ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) ⟹⟨ pre ⟩ W → Diverges W
  → divergences (((pchoice v) ▷ P′) △ Q) pre
slide-RHS-reach-div-m v P′ Q ⟹-refl divW
  with ▷-Diverges→ {P = pchoice (△Q-menu v Q)} {Q = P′ △ Q} divW
... | inj₁ dpre = ⊥-elim (pchoice-no-Diverges (△Q-menu v Q) dpre)
... | inj₂ dP′Q = div-τ-prepend
                    (△-τ-lift-P {Q = Q} (▷-timeout (pchoice v) P′ refl tt0))
                    (root-div→all-div dP′Q)
slide-RHS-reach-div-m v P′ Q (⟹-τ step rest) divW
  with ▷-τ-elim (pchoice (△Q-menu v Q)) (P′ △ Q) step
... | inj₁ refl = div-τ-prepend
                    (△-τ-lift-P {Q = Q} (▷-timeout (pchoice v) P′ refl tt0))
                    (mk-div-from rest divW)
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (pchoice-no-τ Pτ)
slide-RHS-reach-div-m v P′ Q (⟹-ev step rest) divW
  with ▷-ev-elim (pchoice (△Q-menu v Q)) (P′ △ Q) step
... | sVis {at = at} {a = a} eqf brM =
      slide-RHS-ev→LHS-div-m v P′ Q {at = at} {a = a}
        (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) brM)
        (mk-div-from rest divW)

△-slide-dist-⊑D-m : ∀ {ℓr} {R : Set ℓr}
                    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                    (P′ Q : PTree E (ExtI E) R)
                  → (((pchoice v) ▷ P′) △ Q) ⊑D ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q))
△-slide-dist-⊑D-m v P′ Q d =
  subst (divergences (((pchoice v) ▷ P′) △ Q)) (sym (d .IsDivergence.split))
    (div-extension-closed
      (slide-RHS-reach-div-m v P′ Q (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-- Direction 2 — ⊒D : RHS recovers every LHS divergence (the woven-Q worker).
△-slide-reach-div-go-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q Qc : PTree E (ExtI E) R)
    {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc
  → (((pchoice v) ▷ P′) △ Qc) ⟹⟨ pre ⟩ W → Diverges W
  → divergences ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) pre
△-slide-reach-div-go-m v P′ Q Qc q* ⟹-refl divW
  with △-Diverges→ {P = (pchoice v) ▷ P′} {Q = Qc} divW
... | inj₂ dQc with τ*-Diverges q* dQc
...   | dQ = slide-RHS-timeout-prepend-m v P′ Q
              (root-div→all-div (△-Diverges-R {P = P′} {Q = Q} dQ))
△-slide-reach-div-go-m v P′ Q Qc q* ⟹-refl divW | inj₁ dS
  with ▷-Diverges→ {P = pchoice v} {Q = P′} dS
...   | inj₁ dpre = ⊥-elim (pchoice-no-Diverges v dpre)
...   | inj₂ dP′  = slide-RHS-timeout-prepend-m v P′ Q
                      (root-div→all-div (△-Diverges-L {P = P′} {Q = Q} dP′))
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-τ step rest) divW
  with △-τ-elim ((pchoice v) ▷ P′) Qc step
... | △τP sS with ▷-τ-elim (pchoice v) P′ sS
...   | inj₁ refl = slide-RHS-timeout-prepend-m v P′ Q
                      (△-τ*-prepend-Q P′ Q Qc q* (mk-div-from rest divW))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (pchoice-no-τ Pτ)
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-τ step rest) divW | △τQ {Q′ = Qc′} sQ =
      △-slide-reach-div-go-m v P′ Q Qc′ (τ*-trans q* (τ*-step sQ τ*-refl)) rest divW
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-τ step rest) divW | △τQret eqQcr =
      slide-RHS-timeout-prepend-m v P′ Q
        (△-τ*-prepend-Q P′ Q Qc q*
          (div-τ-prepend (△-toQ-Qret P′ Qc eqQcr) (mk-div-from rest divW)))
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-τ step rest) divW | △τ⊓P eqSr =
      case trans (sym (force-Sm-react v P′)) eqSr of λ ()
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-τ step rest) divW | △τ⊓Q eqSr =
      case trans (sym (force-Sm-react v P′)) eqSr of λ ()
△-slide-reach-div-go-m v P′ Q Qc q* (⟹-ev step rest) divW
  with △-ev-elim ((pchoice v) ▷ P′) Qc step
... | △evP {P₁ = P₁} sS =
      div-ev-prepend (slide-RHS-ev-step-m v P′ Q sS)
                     (△-τ*-prepend-Q P₁ Q Qc q* (mk-div-from rest divW))
... | △evQ {Q₁ = Qc₁} sQ =
      slide-RHS-timeout-prepend-m v P′ Q
        (△-τ*-prepend-Q P′ Q Qc q*
          (△-Q-ev-prepend P′ Qc sQ (mk-div-from rest divW)))
... | △evPQ {P₁ = P₁} {Q₁ = Qc₁} sS sQ
      with △-br2-node-div→ P₁ Qc Qc₁ (mk-div-from rest divW)
...   | inj₁ dL = div-ev-prepend (slide-RHS-ev-step-m v P′ Q sS)
                                 (△-τ*-prepend-Q P₁ Q Qc q* dL)
...   | inj₂ dR = slide-RHS-timeout-prepend-m v P′ Q
                   (△-τ*-prepend-Q P′ Q Qc q*
                     (△-Q-ev-prepend P′ Qc sQ dR))

△-slide-dist-⊒D-m : ∀ {ℓr} {R : Set ℓr}
                    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                    (P′ Q : PTree E (ExtI E) R)
                  → ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) ⊑D (((pchoice v) ▷ P′) △ Q)
△-slide-dist-⊒D-m v P′ Q d =
  subst (divergences ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q))) (sym (d .IsDivergence.split))
    (div-extension-closed
      (△-slide-reach-div-go-m v P′ Q Q τ*-refl
        (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-- FAILURES half.
△-slide-unstable-m : ∀ {ℓr} {R : Set ℓr}
                     {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                     {P′ Q : PTree E (ExtI E) R}
                   → ¬ isStable ((((pchoice v) ▷ P′) △ Q))
△-slide-unstable-m {v = v} {P′ = P′} {Q = Q} st =
  stable-no-τ st (△-τ-lift-P {Q = Q} (▷-timeout (pchoice v) P′ refl tt0))

slide-RHS-timeout-fail-prepend-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
  → failures (P′ △ Q) s X
  → failures ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) s X
slide-RHS-timeout-fail-prepend-m v P′ Q f =
  fail-τ-prepend (▷-timeout (pchoice (△Q-menu v Q)) (P′ △ Q) refl tt0) f

△-slide-fail-elim-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q Qc : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → Q ─[τ*]─► Qc
  → (((pchoice v) ▷ P′) △ Qc) ⟹⟨ s ⟩ W → Refuses W X
  → failures ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) s X
△-slide-fail-elim-m v P′ Q Qc q* ⟹-refl (st , _) =
  ⊥-elim (△-slide-unstable-m {v = v} {P′ = P′} {Q = Qc} st)
△-slide-fail-elim-m v P′ Q Qc q* (⟹-τ step rest) ref
  with △-τ-elim ((pchoice v) ▷ P′) Qc step
... | △τP sS with ▷-τ-elim (pchoice v) P′ sS
...   | inj₁ refl = slide-RHS-timeout-fail-prepend-m v P′ Q
                      (△-τ*-fail-prepend-Q P′ Q Qc q* (_ , rest , ref))
...   | inj₂ (P'' , Pτ , refl) = ⊥-elim (pchoice-no-τ Pτ)
△-slide-fail-elim-m v P′ Q Qc q* (⟹-τ step rest) ref | △τQ {Q′ = Qc′} sQ =
      △-slide-fail-elim-m v P′ Q Qc′ (τ*-trans q* (τ*-step sQ τ*-refl)) rest ref
△-slide-fail-elim-m v P′ Q Qc q* (⟹-τ step rest) ref | △τQret eqQcr =
      slide-RHS-timeout-fail-prepend-m v P′ Q
        (△-τ*-fail-prepend-Q P′ Q Qc q*
          (fail-τ-prepend (△-toQ-Qret P′ Qc eqQcr) (_ , rest , ref)))
△-slide-fail-elim-m v P′ Q Qc q* (⟹-τ step rest) ref | △τ⊓P eqSr =
      case trans (sym (force-Sm-react v P′)) eqSr of λ ()
△-slide-fail-elim-m v P′ Q Qc q* (⟹-τ step rest) ref | △τ⊓Q eqSr =
      case trans (sym (force-Sm-react v P′)) eqSr of λ ()
△-slide-fail-elim-m v P′ Q Qc q* (⟹-ev step rest) ref
  with △-ev-elim ((pchoice v) ▷ P′) Qc step
... | △evP {P₁ = P₁} sS =
      fail-ev-prepend (slide-RHS-ev-step-m v P′ Q sS)
                      (△-τ*-fail-prepend-Q P₁ Q Qc q* (_ , rest , ref))
... | △evQ {Q₁ = Qc₁} sQ =
      slide-RHS-timeout-fail-prepend-m v P′ Q
        (△-τ*-fail-prepend-Q P′ Q Qc q*
          (△-Q-ev-fail-prepend P′ Qc sQ (_ , rest , ref)))
... | △evPQ {P₁ = P₁} {Q₁ = Qc₁} sS sQ
      with △-br2-node-fail→ P₁ Qc Qc₁ (_ , rest , ref)
...   | inj₁ fL = fail-ev-prepend (slide-RHS-ev-step-m v P′ Q sS)
                                  (△-τ*-fail-prepend-Q P₁ Q Qc q* fL)
...   | inj₂ fR = slide-RHS-timeout-fail-prepend-m v P′ Q
                   (△-τ*-fail-prepend-Q P′ Q Qc q*
                     (△-Q-ev-fail-prepend P′ Qc sQ fR))

slide-LHS-ev-match-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R)
    {at : AnyTypes E} {a : proj₁ at} {M W : PTree E (ExtI E) R} {s : List (Event√ R)}
  → △Q-menu v Q at a ≡ just M
  → M ⟹⟨ s ⟩ W
  → (((pchoice v) ▷ P′) △ Q) ⟹⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s ⟩ W
slide-LHS-ev-match-m v P′ Q {at = at} {a = a} {M = M} brM mrest with v at a in eqv
... | just Pc =
        slide-LHS-go ((pchoice v) ▷ P′) Q Pc
          (force-Sm-react v P′) eqv
          (subst (λ z → z ⟹⟨ _ ⟩ _) (sym (just-injective brM)) mrest)
... | nothing = case brM of λ ()

slide-RHS-fail→LHS-m :
    ∀ {ℓr} {R : Set ℓr}
    (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
    (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) ⟹⟨ s ⟩ W → Refuses W X
  → failures (((pchoice v) ▷ P′) △ Q) s X
slide-RHS-fail→LHS-m v P′ Q ⟹-refl (st , _) =
  ⊥-elim (stable-no-τ st (▷-timeout (pchoice (△Q-menu v Q)) (P′ △ Q) refl tt0))
slide-RHS-fail→LHS-m v P′ Q (⟹-τ step rest) ref
  with ▷-τ-elim (pchoice (△Q-menu v Q)) (P′ △ Q) step
... | inj₁ refl =
      fail-τ-prepend (△-τ-lift-P {Q = Q} (▷-timeout (pchoice v) P′ refl tt0))
                     (_ , rest , ref)
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (pchoice-no-τ Pτ)
slide-RHS-fail→LHS-m v P′ Q (⟹-ev step rest) ref
  with ▷-ev-elim (pchoice (△Q-menu v Q)) (P′ △ Q) step
... | sVis {at = at} {a = a} eqf brM =
      _ , slide-LHS-ev-match-m v P′ Q {at = at} {a = a}
            (subst (λ g → g at a ≡ just _) (sym (proj₁ (react-injective eqf))) brM)
            rest
        , ref

△-slide-dist-⊑F⊥-m : ∀ {ℓr} {R : Set ℓr}
                     (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                     (P′ Q : PTree E (ExtI E) R)
                   → (((pchoice v) ▷ P′) △ Q) ⊑F⊥ ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q))
△-slide-dist-⊑F⊥-m v P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (slide-RHS-fail→LHS-m v P′ Q reach ref)
△-slide-dist-⊑F⊥-m v P′ Q (inj₂ d) = inj₂ (△-slide-dist-⊑D-m v P′ Q d)

△-slide-dist-⊒F⊥-m : ∀ {ℓr} {R : Set ℓr}
                     (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                     (P′ Q : PTree E (ExtI E) R)
                   → ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q)) ⊑F⊥ (((pchoice v) ▷ P′) △ Q)
△-slide-dist-⊒F⊥-m v P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (△-slide-fail-elim-m v P′ Q Q τ*-refl reach ref)
△-slide-dist-⊒F⊥-m v P′ Q (inj₂ d) = inj₂ (△-slide-dist-⊒D-m v P′ Q d)

-- ((pchoice v) ▷ P′) △ Q  ≈FD  (pchoice (△Q-menu v Q)) ▷ (P′ △ Q)      (menu Fig 13.6)
△-slide-dist-menu-FD : ∀ {ℓr} {R : Set ℓr}
                       (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                       (P′ Q : PTree E (ExtI E) R)
                     → (((pchoice v) ▷ P′) △ Q) ≈FD ((pchoice (△Q-menu v Q)) ▷ (P′ △ Q))
△-slide-dist-menu-FD v P′ Q =
  (△-slide-dist-⊑F⊥-m v P′ Q , △-slide-dist-⊑D-m v P′ Q) ,
  (△-slide-dist-⊒F⊥-m v P′ Q , △-slide-dist-⊒D-m v P′ Q)
