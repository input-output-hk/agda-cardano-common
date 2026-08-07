{-# OPTIONS --guardedness #-}

-- LIFTING / STABILITY / OFFER machinery for the BINARY ALPHABETISED PARALLEL
-- `_⟦ A ∥ B ⟧_` (= `αpar A B _,_`) — the αpar analogue of the τ*/weak lifts of
-- `CSP.Laws.FSim.ParCong` together with the stability-classification and offer
-- elim/intro/monotonicity layer of `CSP.Laws.FD.ParallelRefusals` /
-- `CSP.Laws.FD.ParallelMonoFD`.  This module is the SUPPORTING layer an FSim
-- congruence for `⟦A∥B⟧` consumes; it declares NO postulate, no hole, no
-- NON_TERMINATING and no sized type, and it changes nothing that already exists.
--
-- WHY NO `Sep`-STYLE SIDE CONDITION.  `αpar` routes every visible event
-- DETERMINATELY by alphabet membership (`e ∈ A∩B` → both operands, `e ∈ A∖B` → P,
-- `e ∈ B∖A` → Q, `e ∉ A∪B` → refused), so `αpar-pVis` never builds the inline
-- overlap node `⊓` that forces `Par`'s `Sep A P Q` hypothesis: the inversion
-- datatype `αVisR` has no `evBoth` analogue.  Offer routing is MONOTONE in each
-- operand's offer set, which is exactly what `αpar-offer-mono` below exploits.
--
-- THE SIL-PRIORITY CAVEAT (the one structural difference from `Par`, and the reason
-- the lemmas below are not literal transcriptions of the `Par-…` ones).  `αpar`'s
-- `force` gives a `sil`-headed operand ABSOLUTE priority:
--     sil P′     | _        → sil (αpar P′ Q)
--     ret r      | sil Q′   → sil (αpar P  Q′)
--     react _ _  | sil Q′   → sil (αpar P  Q′)
-- while `Par` routes a `sil` head through its generic `react` node (`par-pTau`).
-- Hence the UNCONDITIONAL `Par-τ-L` / `Par-τ*-L` analogues are FALSE here: from
-- `αpar P Q` with `P` react-headed and `Q` sil-headed the composite's ONLY move is
-- Q's, so `(P ⟦A∥B⟧ Q) ─[τ*]─► (P′ ⟦A∥B⟧ Q)` cannot hold for `P′ ≢ P` (and no
-- Q-existential repairs it — a silently divergent `Q` starves `P` forever).  Every
-- lift below therefore carries a `NoSil` hypothesis on the operand that has to
-- STAND STILL, discharged by `noSil-ret` / `noSil-react` / `noSil-stable`.  The
-- τ-flush, which moves BOTH operands in the operator's own priority order, needs
-- `NoSil` only at the two ENDPOINTS — and a `ret` or a stable endpoint satisfies it,
-- which is what makes the flush usable for the `stab` field of an FSim.

open import Level using (Level; Lift; lift; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.AlphaParallelLift
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open PTree

open import Semantics.LTS
open import Semantics.WeakBisim
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev)
open import Semantics.Refusals using (Offers)
open import Semantics.Stability
  using (mk-stable; stable→react; stable-not-sil; stable-not-ret; stable-react-τc)

import CSP.Operators {ℓ} {ℓe} {E} E-≟ as CSPOps
open CSPOps using
  ( EventSet
  ; _⟦_∥_⟧_
  ; αpar-pVis; αpar-pTau
  ; αpar-hVisR; αpar-hTauR
  ; αpar-hVisL; αpar-hTauL
  ; αpar-sync-step; αpar-soloL-step; αpar-soloR-step
  )
open EventSet

open import CSP.Laws.AlphaParallel E-≟
  using ( αpar-sil-L; αpar-sil-R; αpar-τ-L; αpar-τ-R
        ; αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-√-step-inv )

-- the visible-offer map of a `react` node (an abbreviation, so that every signature
-- below can give its `react` witnesses an explicit type)
VMap : ∀ {ℓi ℓr} (I : Set ℓ → Set ℓi) (R : Set ℓr) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
VMap I R = (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))

-- the τ-branch map of a `react` node
TMap : ∀ {ℓi ℓr} (I : Set ℓ → Set ℓi) (R : Set ℓr) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
TMap I R = (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))

-------------------------------------------------------------------------------------
-- `NoSil`: the "this operand's head is not a `sil`" predicate the sil-priority of
-- `αpar` forces on every one-sided lift, with its three introduction forms.
-------------------------------------------------------------------------------------

-- the head of `t` is not a `sil` node (exactly the shape `αpar-sil-R` demands)
NoSil : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → PTree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
NoSil {I = I} {R = R} t = ∀ {u : PTree E (ExtI I) R} → t .force ≢ sil u

-- a terminated head is not a `sil` head
noSil-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {t : PTree E (ExtI I) R} {r : R} → t .force ≡ ret r → NoSil t
noSil-ret eq e = case trans (sym eq) e of λ ()

-- a `react` head is not a `sil` head
noSil-react : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {t : PTree E (ExtI I) R}
              {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI I) R))}
              {τc : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))}
            → t .force ≡ react v τc → NoSil t
noSil-react eq e = case trans (sym eq) e of λ ()

-- a stable state is `react`-headed, hence not `sil`-headed
noSil-stable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {t : PTree E (ExtI I) R} → isStable t → NoSil t
noSil-stable {t = t} st eq = ⊥-elim (stable-not-sil {t = t} st eq)

-- a state that offers a visible event is `react`-headed, hence not `sil`-headed
noSil-of-ev : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {t t′ : PTree E (ExtI I) R} {X : Set ℓ} {f : E X} {a : X}
            → t ─[ ev (evl (evLabel X f a)) ]─► t′ → NoSil t
noSil-of-ev {t = t} (sVis eqf _) = noSil-react {t = t} eqf

-- a √ step comes from a `ret` node carrying exactly the ticked value
√-source : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {t t′ : PTree E (ExtI I) R} {r : R}
         → t ─[ ev (√ r) ]─► t′ → t .force ≡ ret r
√-source (sRet eq) = eq

-------------------------------------------------------------------------------------
-- FORCE-REDUCTION witnesses for the head-pairs the existing `AlphaParallel` layer
-- does not expose (the ones with a `ret` or a `sil` on one side).
-------------------------------------------------------------------------------------

-- both operands `react`-headed ⇒ the composite is the fused `react` node
fαpar-nn : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
           {vP : VMap I R} {τcP : TMap I R} {vQ : VMap I S} {τcQ : TMap I S}
         → P .force ≡ react vP τcP → Q .force ≡ react vQ τcQ
         → (P ⟦ A ∥ B ⟧ Q) .force
             ≡ react (αpar-pVis A B _,_ vP vQ P Q) (αpar-pTau A B _,_ τcP τcQ P Q)
fαpar-nn A B eqP eqQ rewrite eqP | eqQ = refl

-- P terminated, Q `react`-headed ⇒ the composite is the `αpar-hVisR`/`-hTauR` node
fαpar-rn : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {r : R}
           {vQ : VMap I S} {τcQ : TMap I S}
         → P .force ≡ ret r → Q .force ≡ react vQ τcQ
         → (P ⟦ A ∥ B ⟧ Q) .force
             ≡ react (αpar-hVisR A B _,_ r vQ P Q) (αpar-hTauR A B _,_ r τcQ P Q)
fαpar-rn A B eqP eqQ rewrite eqP | eqQ = refl

-- Q terminated, P `react`-headed ⇒ the composite is the `αpar-hVisL`/`-hTauL` node
fαpar-nr : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {s : S}
           {vP : VMap I R} {τcP : TMap I R}
         → P .force ≡ react vP τcP → Q .force ≡ ret s
         → (P ⟦ A ∥ B ⟧ Q) .force
             ≡ react (αpar-hVisL A B _,_ s vP P Q) (αpar-hTauL A B _,_ s τcP P Q)
fαpar-nr A B eqP eqQ rewrite eqP | eqQ = refl

-- both operands terminated ⇒ the composite terminates with the merged (paired) value
fαpar-rr : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {r : R} {s : S}
         → P .force ≡ ret r → Q .force ≡ ret s
         → (P ⟦ A ∥ B ⟧ Q) .force ≡ ret (r , s)
fαpar-rr A B eqP eqQ rewrite eqP | eqQ = refl

-- P `sil`-headed ⇒ the composite is `sil`, advancing P (operator clause 1)
fαpar-sl : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
         → P .force ≡ sil P′ → (P ⟦ A ∥ B ⟧ Q) .force ≡ sil (P′ ⟦ A ∥ B ⟧ Q)
fαpar-sl A B eqP rewrite eqP = refl

-- P terminated, Q `sil`-headed ⇒ the composite is `sil`, advancing Q
fαpar-rs : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S} {r : R}
         → P .force ≡ ret r → Q .force ≡ sil Q′
         → (P ⟦ A ∥ B ⟧ Q) .force ≡ sil (P ⟦ A ∥ B ⟧ Q′)
fαpar-rs A B eqP eqQ rewrite eqP | eqQ = refl

-- P `react`-headed, Q `sil`-headed ⇒ the composite is `sil`, advancing Q
fαpar-ns : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (A B : EventSet)
           {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
           {vP : VMap I R} {τcP : TMap I R}
         → P .force ≡ react vP τcP → Q .force ≡ sil Q′
         → (P ⟦ A ∥ B ⟧ Q) .force ≡ sil (P ⟦ A ∥ B ⟧ Q′)
fαpar-ns A B eqP eqQ rewrite eqP | eqQ = refl

-------------------------------------------------------------------------------------
-- BRANCH-MAP equations for the half-terminated nodes (the `Par`-side analogues are
-- `par-hTauR-eq` / `par-hVisL-eq` …).  Each says: the composite's fused map carries
-- the live operand's own branch at the SAME index.
-------------------------------------------------------------------------------------

-- P terminated: the composite's τ-map forwards Q's τ-branch verbatim
αpar-hTauR-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S} {r : R}
                {τcQ : TMap I S}
                {i : AnyTypes (ExtI I)} {a : proj₁ i}
              → τcQ i a ≡ just Q′
              → αpar-hTauR A B _,_ r τcQ P Q i a ≡ just (P ⟦ A ∥ B ⟧ Q′)
αpar-hTauR-eq A B bQ rewrite bQ = refl

-- Q terminated: the composite's τ-map forwards P's τ-branch verbatim
αpar-hTauL-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {s : S}
                {τcP : TMap I R}
                {i : AnyTypes (ExtI I)} {a : proj₁ i}
              → τcP i a ≡ just P′
              → αpar-hTauL A B _,_ s τcP P Q i a ≡ just (P′ ⟦ A ∥ B ⟧ Q)
αpar-hTauL-eq A B bP rewrite bP = refl

-- P terminated: a `B∖A` offer of Q is the composite's offer (Q acts solo)
αpar-hVisR-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S} {r : R}
                {vQ : VMap I S}
                {X : Set ℓ} {f : E X} {a : X}
              → ¬ A .mem (X , f) a → B .mem (X , f) a → vQ (X , f) a ≡ just Q′
              → αpar-hVisR A B _,_ r vQ P Q (X , f) a ≡ just (P ⟦ A ∥ B ⟧ Q′)
αpar-hVisR-eq A B {X = X} {f = f} {a = a} ¬mA mB bQ with A .dec (X , f) a | B .dec (X , f) a
... | no _   | yes _  rewrite bQ = refl
... | no _   | no ¬mB = ⊥-elim (¬mB mB)
... | yes mA | _      = ⊥-elim (¬mA mA)

-- Q terminated: an `A∖B` offer of P is the composite's offer (P acts solo)
αpar-hVisL-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {s : S}
                {vP : VMap I R}
                {X : Set ℓ} {f : E X} {a : X}
              → A .mem (X , f) a → ¬ B .mem (X , f) a → vP (X , f) a ≡ just P′
              → αpar-hVisL A B _,_ s vP P Q (X , f) a ≡ just (P′ ⟦ A ∥ B ⟧ Q)
αpar-hVisL-eq A B {X = X} {f = f} {a = a} mA ¬mB bP with A .dec (X , f) a | B .dec (X , f) a
... | yes _  | no _   rewrite bP = refl
... | yes _  | yes mB = ⊥-elim (¬mB mB)
... | no ¬mA | _      = ⊥-elim (¬mA mA)

-- both `react`-headed: P's τ sits at composite tag 0 of the fused τ-map
αpar-pTauL-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
                {τcP : TMap I R} {τcQ : TMap I S}
                {X : Set ℓ} {ii : ExtI I X} {a : X}
              → τcP (X , ii) a ≡ just P′
              → αpar-pTau A B _,_ τcP τcQ P Q (_ , pair (fin {n = 2}) ii) (lift fzero , a)
                  ≡ just (P′ ⟦ A ∥ B ⟧ Q)
αpar-pTauL-eq A B bP rewrite bP = refl

-- both `react`-headed: Q's τ sits at composite tag 1 of the fused τ-map
αpar-pTauR-eq : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
                {τcP : TMap I R} {τcQ : TMap I S}
                {X : Set ℓ} {ii : ExtI I X} {a : X}
              → τcQ (X , ii) a ≡ just Q′
              → αpar-pTau A B _,_ τcP τcQ P Q (_ , pair (fin {n = 2}) ii)
                          (lift (fsuc fzero) , a)
                  ≡ just (P ⟦ A ∥ B ⟧ Q′)
αpar-pTauR-eq A B bQ rewrite bQ = refl

-------------------------------------------------------------------------------------
-- SINGLE-STEP lifts at a HALF-TERMINATED head (the cases `αpar-τ-L`/`-R` and
-- `αpar-soloL-step`/`-soloR-step`, which both require TWO `react` heads, do not cover).
-------------------------------------------------------------------------------------

-- P terminated, Q `react`-headed: Q's τ is a composite τ (P stays put)
αpar-τ-retL : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              (A B : EventSet)
              {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S} {r : R}
              {vQ : VMap I S} {τcQ : TMap I S}
              {i : AnyTypes (ExtI I)} {a : proj₁ i}
            → P .force ≡ ret r → Q .force ≡ react vQ τcQ → τcQ i a ≡ just Q′
            → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-τ-retL A B {P = P} {Q = Q} {Q′ = Q′} {r = r} {vQ = vQ} {τcQ = τcQ}
            {i = i} {a = a} eqP eqQ bQ =
  sTau (fαpar-rn A B {P = P} {Q = Q} {r = r} {vQ = vQ} {τcQ = τcQ} eqP eqQ)
       (αpar-hTauR-eq A B {P = P} {Q = Q} {Q′ = Q′} {r = r} {τcQ = τcQ}
                      {i = i} {a = a} bQ)

-- Q terminated, P `react`-headed: P's τ is a composite τ (Q stays put)
αpar-τ-retR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              (A B : EventSet)
              {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {s : S}
              {vP : VMap I R} {τcP : TMap I R}
              {i : AnyTypes (ExtI I)} {a : proj₁ i}
            → P .force ≡ react vP τcP → Q .force ≡ ret s → τcP i a ≡ just P′
            → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-τ-retR A B {P = P} {P′ = P′} {Q = Q} {s = s} {vP = vP} {τcP = τcP}
            {i = i} {a = a} eqP eqQ bP =
  sTau (fαpar-nr A B {P = P} {Q = Q} {s = s} {vP = vP} {τcP = τcP} eqP eqQ)
       (αpar-hTauL-eq A B {P = P} {P′ = P′} {Q = Q} {s = s} {τcP = τcP}
                      {i = i} {a = a} bP)

-- Q terminated: an `A∖B` event of P is a composite solo step
αpar-soloL-step-retR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                       (A B : EventSet)
                       {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
                       {s : S} {vP : VMap I R} {τcP : TMap I R}
                       {X : Set ℓ} {f : E X} {a : X}
                     → A .mem (X , f) a → ¬ B .mem (X , f) a
                     → P .force ≡ react vP τcP → vP (X , f) a ≡ just P′
                     → Q .force ≡ ret s
                     → (P ⟦ A ∥ B ⟧ Q) ─[ ev (evl (evLabel X f a)) ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-soloL-step-retR A B {P = P} {P′ = P′} {Q = Q} {s = s} {vP = vP} {τcP = τcP}
                     {X = X} {f = f} {a = a} mA ¬mB eqP bP eqQ =
  sVis (fαpar-nr A B {P = P} {Q = Q} {s = s} {vP = vP} {τcP = τcP} eqP eqQ)
       (αpar-hVisL-eq A B {P = P} {P′ = P′} {Q = Q} {s = s} {vP = vP}
                      {X = X} {f = f} {a = a} mA ¬mB bP)

-- P terminated: a `B∖A` event of Q is a composite solo step
αpar-soloR-step-retL : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                       (A B : EventSet)
                       {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
                       {r : R} {vQ : VMap I S} {τcQ : TMap I S}
                       {X : Set ℓ} {f : E X} {a : X}
                     → ¬ A .mem (X , f) a → B .mem (X , f) a
                     → P .force ≡ ret r
                     → Q .force ≡ react vQ τcQ → vQ (X , f) a ≡ just Q′
                     → (P ⟦ A ∥ B ⟧ Q) ─[ ev (evl (evLabel X f a)) ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-soloR-step-retL A B {P = P} {Q = Q} {Q′ = Q′} {r = r} {vQ = vQ} {τcQ = τcQ}
                     {X = X} {f = f} {a = a} ¬mA mB eqP eqQ bQ =
  sVis (fαpar-rn A B {P = P} {Q = Q} {r = r} {vQ = vQ} {τcQ = τcQ} eqP eqQ)
       (αpar-hVisR-eq A B {P = P} {Q = Q} {Q′ = Q′} {r = r} {vQ = vQ}
                      {X = X} {f = f} {a = a} ¬mA mB bQ)

-- both terminated: the composite performs the joint √ carrying the merged pair
αpar-√-step : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              (A B : EventSet)
              {P : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S} {r : R} {s : S}
            → P .force ≡ ret r → Q .force ≡ ret s
            → (P ⟦ A ∥ B ⟧ Q) ─[ ev (√ (r , s)) ]─► deadlock
αpar-√-step A B eqP eqQ = sRet (fαpar-rr A B eqP eqQ)

-------------------------------------------------------------------------------------
-- HEAD-SHAPE-FREE single-step lifts: ONE τ (resp. ONE solo / sync visible event) of an
-- operand becomes ONE composite step, for EVERY head shape of the moving operand — at
-- the price of `NoSil` on the operand that stands still (see the header).
-------------------------------------------------------------------------------------

-- one τ of the LEFT operand lifts (Q must not be `sil`-headed: it would take priority)
αpar-τ-lift-L : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
              → NoSil Q → P ─[ τ ]─► P′
              → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-τ-lift-L A B nsQ (sSil eqP)      = αpar-sil-L eqP
αpar-τ-lift-L A B {Q = Q} nsQ (sTau eqP bP) with Q .force in q-eq
... | ret s        = αpar-τ-retR A B eqP q-eq bP
... | react vQ τcQ = αpar-τ-L eqP q-eq bP
... | sil Q0       = ⊥-elim (nsQ refl)

-- one τ of the RIGHT operand lifts (P must not be `sil`-headed)
αpar-τ-lift-R : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                (A B : EventSet)
                {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
              → NoSil P → Q ─[ τ ]─► Q′
              → (P ⟦ A ∥ B ⟧ Q) ─[ τ ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-τ-lift-R A B nsP (sSil eqQ)      = αpar-sil-R nsP eqQ
αpar-τ-lift-R A B {P = P} nsP (sTau eqQ bQ) with P .force in p-eq
... | ret r        = αpar-τ-retL A B p-eq eqQ bQ
... | react vP τcP = αpar-τ-R p-eq eqQ bQ
... | sil P0       = ⊥-elim (nsP refl)

-- a shared (`A∩B`) event fired by BOTH operands is a composite synchronisation step
-- (no side condition: an operand that offers a visible event is `react`-headed)
αpar-sync-lift : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                 (A B : EventSet)
                 {P P′ : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
                 {X : Set ℓ} {f : E X} {a : X}
               → A .mem (X , f) a → B .mem (X , f) a
               → P ─[ ev (evl (evLabel X f a)) ]─► P′
               → Q ─[ ev (evl (evLabel X f a)) ]─► Q′
               → (P ⟦ A ∥ B ⟧ Q) ─[ ev (evl (evLabel X f a)) ]─► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-sync-lift A B mA mB (sVis eqP bP) (sVis eqQ bQ) =
  αpar-sync-step mA mB eqP bP eqQ bQ

-- an `A∖B` event of the LEFT operand is a composite solo step (Q not `sil`-headed)
αpar-soloL-lift : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  {P P′ : PTree E (ExtI I) R} {Q : PTree E (ExtI I) S}
                  {X : Set ℓ} {f : E X} {a : X}
                → A .mem (X , f) a → ¬ B .mem (X , f) a → NoSil Q
                → P ─[ ev (evl (evLabel X f a)) ]─► P′
                → (P ⟦ A ∥ B ⟧ Q) ─[ ev (evl (evLabel X f a)) ]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-soloL-lift A B {Q = Q} mA ¬mB nsQ (sVis eqP bP) with Q .force in q-eq
... | ret s        = αpar-soloL-step-retR A B mA ¬mB eqP bP q-eq
... | react vQ τcQ = αpar-soloL-step mA ¬mB eqP bP q-eq
... | sil Q0       = ⊥-elim (nsQ refl)

-- a `B∖A` event of the RIGHT operand is a composite solo step (P not `sil`-headed)
αpar-soloR-lift : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  {P : PTree E (ExtI I) R} {Q Q′ : PTree E (ExtI I) S}
                  {X : Set ℓ} {f : E X} {a : X}
                → ¬ A .mem (X , f) a → B .mem (X , f) a → NoSil P
                → Q ─[ ev (evl (evLabel X f a)) ]─► Q′
                → (P ⟦ A ∥ B ⟧ Q) ─[ ev (evl (evLabel X f a)) ]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-soloR-lift A B {P = P} ¬mA mB nsP (sVis eqQ bQ) with P .force in p-eq
... | ret r        = αpar-soloR-step-retL A B ¬mA mB p-eq eqQ bQ
... | react vP τcP = αpar-soloR-step ¬mA mB p-eq eqQ bQ
... | sil P0       = ⊥-elim (nsP refl)

-------------------------------------------------------------------------------------
-- τ*-LIFTING (the `Par-τ*-L`/`-R` analogues).  A whole silent run of ONE operand
-- replays as a silent run of the composite; the OTHER operand stands still, so it
-- must not be `sil`-headed (its head shape is invariant along the run, hence ONE
-- `NoSil` hypothesis suffices, and NOTHING is required of the run's endpoint).
-------------------------------------------------------------------------------------

-- a LEFT operand's τ*-run lifts to a τ*-run of the composite
αpar-τ*-L : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
            (A B : EventSet)
            (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {P′ : PTree E (ExtI I) R}
          → NoSil Q → P ─[τ*]─► P′
          → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q)
αpar-τ*-L A B P Q nsQ τ*-refl           = τ*-refl
αpar-τ*-L A B P Q nsQ (τ*-step Pτ rest) =
  τ*-step (αpar-τ-lift-L A B nsQ Pτ) (αpar-τ*-L A B _ Q nsQ rest)

-- a RIGHT operand's τ*-run lifts to a τ*-run of the composite
αpar-τ*-R : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
            (A B : EventSet)
            (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {Q′ : PTree E (ExtI I) S}
          → NoSil P → Q ─[τ*]─► Q′
          → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P ⟦ A ∥ B ⟧ Q′)
αpar-τ*-R A B P Q nsP τ*-refl           = τ*-refl
αpar-τ*-R A B P Q nsP (τ*-step Qτ rest) =
  τ*-step (αpar-τ-lift-R A B nsP Qτ) (αpar-τ*-R A B P _ nsP rest)

-------------------------------------------------------------------------------------
-- THE τ-FLUSH (τ* form).  BOTH operands' silent runs are replayed as ONE composite
-- silent run, INTERLEAVED in the operator's own sil-priority order.  Unlike
-- `AlphaParallel.αpar-τ-flush` (which demands `isStable` at both endpoints, so it is
-- unusable when an operand has TERMINATED) the only requirement here is that the two
-- ENDPOINTS are not `sil`-headed — satisfied by a stable AND by a `ret` endpoint,
-- which is exactly what the four named corollaries below record.
--
-- Termination: every recursive call passes a strict sub-derivation of one run and
-- leaves the other unchanged (the lexicographic measure `AlphaParallel.αpar-τ-flush`
-- also uses), driven by the matched step's own force-equality.
-------------------------------------------------------------------------------------

αpar-flush : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
             (A B : EventSet)
             (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
             {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S}
           → P ─[τ*]─► P′ → Q ─[τ*]─► Q′ → NoSil P′ → NoSil Q′
           → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q′)
-- P `sil`-headed: the composite is forced to advance P (operator clause 1)
αpar-flush A B P Q rP rQ nsP′ nsQ′ with P .force in p-eq | Q .force in q-eq
... | sil P0 | _ with rP
...   | τ*-refl                = ⊥-elim (nsP′ p-eq)
...   | τ*-step (sSil e) restP =
        τ*-step (αpar-sil-L e) (αpar-flush A B _ Q restP rQ nsP′ nsQ′)
...   | τ*-step (sTau e _) _   = case trans (sym p-eq) e of λ ()
-- P terminated, Q `sil`-headed: the composite is forced to advance Q (clause 2)
αpar-flush A B P Q rP rQ nsP′ nsQ′ | ret r | sil Q0 with rQ
...   | τ*-refl                = ⊥-elim (nsQ′ q-eq)
...   | τ*-step (sSil e) restQ =
        τ*-step (αpar-sil-R (noSil-ret {t = P} p-eq) e)
                (αpar-flush A B P _ rP restQ nsP′ nsQ′)
...   | τ*-step (sTau e _) _   = case trans (sym q-eq) e of λ ()
-- P `react`-headed, Q `sil`-headed: likewise, Q is advanced first
αpar-flush A B P Q rP rQ nsP′ nsQ′ | react vP τcP | sil Q0 with rQ
...   | τ*-refl                = ⊥-elim (nsQ′ q-eq)
...   | τ*-step (sSil e) restQ =
        τ*-step (αpar-sil-R (noSil-react {t = P} p-eq) e)
                (αpar-flush A B P _ rP restQ nsP′ nsQ′)
...   | τ*-step (sTau e _) _   = case trans (sym q-eq) e of λ ()
-- both `react`-headed: route P's leading τ first (tag 0), then Q's (tag 1)
αpar-flush A B P Q rP rQ nsP′ nsQ′ | react vP τcP | react vQ τcQ with rP
...   | τ*-step (sTau eP bp) restP =
        τ*-step (αpar-τ-L eP q-eq bp) (αpar-flush A B _ Q restP rQ nsP′ nsQ′)
...   | τ*-step (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | τ*-refl with rQ
...     | τ*-step (sTau eQ bq) restQ =
          τ*-step (αpar-τ-R p-eq eQ bq) (αpar-flush A B P _ τ*-refl restQ nsP′ nsQ′)
...     | τ*-step (sSil e) _ = case trans (sym q-eq) e of λ ()
...     | τ*-refl = τ*-refl
-- both terminated: a `ret` head has no τ at all, so both runs are empty
αpar-flush A B P Q rP rQ nsP′ nsQ′ | ret r | ret s with rP
...   | τ*-step (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | τ*-step (sTau e _) _ = case trans (sym p-eq) e of λ ()
...   | τ*-refl with rQ
...     | τ*-step (sSil e) _ = case trans (sym q-eq) e of λ ()
...     | τ*-step (sTau e _) _ = case trans (sym q-eq) e of λ ()
...     | τ*-refl = τ*-refl
-- P terminated, Q `react`-headed: P's run is empty; Q's τ's go through `αpar-hTauR`
αpar-flush A B P Q rP rQ nsP′ nsQ′ | ret r | react vQ τcQ with rP
...   | τ*-step (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | τ*-step (sTau e _) _ = case trans (sym p-eq) e of λ ()
...   | τ*-refl with rQ
...     | τ*-step (sTau eQ bq) restQ =
          τ*-step (αpar-τ-retL A B p-eq eQ bq)
                  (αpar-flush A B P _ τ*-refl restQ nsP′ nsQ′)
...     | τ*-step (sSil e) _ = case trans (sym q-eq) e of λ ()
...     | τ*-refl = τ*-refl
-- Q terminated, P `react`-headed: Q's run is empty; P's τ's go through `αpar-hTauL`
αpar-flush A B P Q rP rQ nsP′ nsQ′ | react vP τcP | ret s with rQ
...   | τ*-step (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | τ*-step (sTau e _) _ = case trans (sym q-eq) e of λ ()
...   | τ*-refl with rP
...     | τ*-step (sTau eP bp) restP =
          τ*-step (αpar-τ-retR A B eP q-eq bp)
                  (αpar-flush A B _ Q restP τ*-refl nsP′ nsQ′)
...     | τ*-step (sSil e) _ = case trans (sym p-eq) e of λ ()
...     | τ*-refl = τ*-refl

-- FLUSH corollary 1 (stable | stable): the τ*-form of `AlphaParallel.αpar-τ-flush`
αpar-flush-stable : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                    (A B : EventSet)
                    (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                    {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S}
                  → P ─[τ*]─► P′ → Q ─[τ*]─► Q′ → isStable P′ → isStable Q′
                  → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-flush-stable A B P Q {P′ = P′} {Q′ = Q′} rP rQ stP′ stQ′ =
  αpar-flush A B P Q rP rQ (noSil-stable {t = P′} stP′) (noSil-stable {t = Q′} stQ′)

-- FLUSH corollary 2 (ret | stable): the LEFT operand has TERMINATED
αpar-flush-retL : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                  {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S} {r : R}
                → P ─[τ*]─► P′ → Q ─[τ*]─► Q′
                → P′ .force ≡ ret r → isStable Q′
                → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-flush-retL A B P Q {P′ = P′} {Q′ = Q′} rP rQ eqP′ stQ′ =
  αpar-flush A B P Q rP rQ (noSil-ret {t = P′} eqP′) (noSil-stable {t = Q′} stQ′)

-- FLUSH corollary 3 (stable | ret): the RIGHT operand has TERMINATED
αpar-flush-retR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                  {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S} {s : S}
                → P ─[τ*]─► P′ → Q ─[τ*]─► Q′
                → isStable P′ → Q′ .force ≡ ret s
                → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-flush-retR A B P Q {P′ = P′} {Q′ = Q′} rP rQ stP′ eqQ′ =
  αpar-flush A B P Q rP rQ (noSil-stable {t = P′} stP′) (noSil-ret {t = Q′} eqQ′)

-- FLUSH corollary 4 (ret | ret): BOTH operands have terminated (the composite is
-- then `ret`-headed, hence NOT stable — see `αpar-stable-normal` below)
αpar-flush-retLR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                   (A B : EventSet)
                   (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                   {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S} {r : R} {s : S}
                 → P ─[τ*]─► P′ → Q ─[τ*]─► Q′
                 → P′ .force ≡ ret r → Q′ .force ≡ ret s
                 → (P ⟦ A ∥ B ⟧ Q) ─[τ*]─► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-flush-retLR A B P Q {P′ = P′} {Q′ = Q′} rP rQ eqP′ eqQ′ =
  αpar-flush A B P Q rP rQ (noSil-ret {t = P′} eqP′) (noSil-ret {t = Q′} eqQ′)

-------------------------------------------------------------------------------------
-- WEAK-STEP LIFTING (the `Par-wsolo{L,R}` / `Par-wsync-both` / `Par-w√-both`
-- analogues): the three shapes a forward simulation has to produce.
--
-- The leading and trailing silent runs of a weak step are replayed by `αpar-τ*-L`/`-R`
-- (solo cases: one operand stands still throughout, so ONE `NoSil` on it suffices) or
-- by `αpar-flush` (sync / √ cases: both operands move, so `NoSil` is needed at the two
-- ENDPOINTS — automatic for `√`, where both endpoints are `ret`-headed).
-------------------------------------------------------------------------------------

-- a weak `A∖B` solo event of the LEFT operand lifts to a weak step of the composite
αpar-wsolo-L : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
               (A B : EventSet)
               (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
               {X : Set ℓ} {f : E X} {a : X} {P′ : PTree E (ExtI I) R}
             → A .mem (X , f) a → ¬ B .mem (X , f) a → NoSil Q
             → P ═[ ev (evl (evLabel X f a)) ]═► P′
             → (P ⟦ A ∥ B ⟧ Q) ═[ ev (evl (evLabel X f a)) ]═► (P′ ⟦ A ∥ B ⟧ Q)
αpar-wsolo-L A B P Q mA ¬mB nsQ (wev p→pₛ pₛev pₘ→p′) =
  wev (αpar-τ*-L A B P Q nsQ p→pₛ)
      (αpar-soloL-lift A B mA ¬mB nsQ pₛev)
      (αpar-τ*-L A B _ Q nsQ pₘ→p′)

-- a weak `B∖A` solo event of the RIGHT operand lifts to a weak step of the composite
αpar-wsolo-R : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
               (A B : EventSet)
               (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
               {X : Set ℓ} {f : E X} {a : X} {Q′ : PTree E (ExtI I) S}
             → ¬ A .mem (X , f) a → B .mem (X , f) a → NoSil P
             → Q ═[ ev (evl (evLabel X f a)) ]═► Q′
             → (P ⟦ A ∥ B ⟧ Q) ═[ ev (evl (evLabel X f a)) ]═► (P ⟦ A ∥ B ⟧ Q′)
αpar-wsolo-R A B P Q ¬mA mB nsP (wev q→qₛ qₛev qₘ→q′) =
  wev (αpar-τ*-R A B P Q nsP q→qₛ)
      (αpar-soloR-lift A B ¬mA mB nsP qₛev)
      (αpar-τ*-R A B P _ nsP qₘ→q′)

-- BOTH operands weakly perform the same shared (`A∩B`) event ⇒ the composite weakly
-- synchronises on it.  The leading runs need nothing (both settle at `react` heads,
-- where the visible step fires); the trailing runs need the two endpoints non-`sil`.
αpar-wsync : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
             (A B : EventSet)
             (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
             {X : Set ℓ} {f : E X} {a : X}
             {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S}
           → A .mem (X , f) a → B .mem (X , f) a → NoSil P′ → NoSil Q′
           → P ═[ ev (evl (evLabel X f a)) ]═► P′
           → Q ═[ ev (evl (evLabel X f a)) ]═► Q′
           → (P ⟦ A ∥ B ⟧ Q) ═[ ev (evl (evLabel X f a)) ]═► (P′ ⟦ A ∥ B ⟧ Q′)
αpar-wsync A B P Q mA mB nsP′ nsQ′ (wev p→pₛ pₛev pₘ→p′) (wev q→qₛ qₛev qₘ→q′) =
  wev (αpar-flush A B P Q p→pₛ q→qₛ (noSil-of-ev pₛev) (noSil-of-ev qₛev))
      (αpar-sync-lift A B mA mB pₛev qₛev)
      (αpar-flush A B _ _ pₘ→p′ qₘ→q′ nsP′ nsQ′)

-- BOTH operands weakly terminate ⇒ the composite weakly performs the joint √ into
-- `deadlock`, carrying the merged pair.  NO side condition: the two silent runs end at
-- `ret` heads, which the flush accepts.
αpar-w√ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
          (A B : EventSet)
          (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
          {r : R} {s : S} {P′ : PTree E (ExtI I) R} {Q′ : PTree E (ExtI I) S}
        → P ═[ ev (√ r) ]═► P′ → Q ═[ ev (√ s) ]═► Q′
        → (P ⟦ A ∥ B ⟧ Q) ═[ ev (√ (r , s)) ]═► deadlock
αpar-w√ A B P Q (wev {p′ = Pₛ} p→pₛ pₛev _) (wev {p′ = Qₛ} q→qₛ qₛev _) =
  wev (αpar-flush A B P Q p→pₛ q→qₛ
        (noSil-ret {t = Pₛ} (√-source pₛev)) (noSil-ret {t = Qₛ} (√-source qₛev)))
      (αpar-√-step A B (√-source pₛev) (√-source qₛev))
      τ*-refl

-------------------------------------------------------------------------------------
-- STABILITY: introduction at the three stable head-pairs, and the CLASSIFICATION
-- (`Par-stable-normal` analogue) inverting composite stability into them.
-------------------------------------------------------------------------------------

-- both operands stable ⇒ the composite is stable (its fused τ-map is everywhere
-- `nothing` because each operand's own τ-map is)
αpar-stable : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
              (A B : EventSet)
              (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
            → isStable P → isStable Q → isStable (P ⟦ A ∥ B ⟧ Q)
αpar-stable A B P Q stP stQ
  with stable→react {t = P} stP | stable→react {t = Q} stQ
... | vP , τcP , eqP , hP | vQ , τcQ , eqQ , hQ =
      mk-stable {t = P ⟦ A ∥ B ⟧ Q}
                (fαpar-nn A B {P = P} {Q = Q} {vP = vP} {τcP = τcP}
                              {vQ = vQ} {τcQ = τcQ} eqP eqQ)
                pTauNothing
  where
    pTauNothing : ∀ i a → αpar-pTau A B _,_ τcP τcQ P Q i a ≡ nothing
    pTauNothing (_ , base _)            _                   = refl
    pTauNothing (_ , fin)               _                   = refl
    pTauNothing (_ , pair (base _) _)   _                   = refl
    pTauNothing (_ , pair (pair _ _) _) _                   = refl
    pTauNothing (_ , pair fin i) (lift fzero , a)            rewrite hP (_ , i) a = refl
    pTauNothing (_ , pair fin i) (lift (fsuc fzero) , a)     rewrite hQ (_ , i) a = refl
    pTauNothing (_ , pair fin i) (lift (fsuc (fsuc _)) , a)                       = refl

-- LEFT operand terminated, RIGHT stable ⇒ the composite is stable (`αpar-hTauR` node)
αpar-stable-termL : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                    (A B : EventSet)
                    (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {r : R}
                  → P .force ≡ ret r → isStable Q → isStable (P ⟦ A ∥ B ⟧ Q)
αpar-stable-termL A B P Q {r = r} eqP stQ with stable→react {t = Q} stQ
... | vQ , τcQ , eqQ , hQ =
      mk-stable {t = P ⟦ A ∥ B ⟧ Q}
                (fαpar-rn A B {P = P} {Q = Q} {r = r} {vQ = vQ} {τcQ = τcQ} eqP eqQ)
                hTauNothing
  where
    hTauNothing : ∀ i a → αpar-hTauR A B _,_ r τcQ P Q i a ≡ nothing
    hTauNothing i a rewrite hQ i a = refl

-- LEFT operand stable, RIGHT terminated ⇒ the composite is stable (`αpar-hTauL` node)
αpar-stable-termR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                    (A B : EventSet)
                    (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {s : S}
                  → isStable P → Q .force ≡ ret s → isStable (P ⟦ A ∥ B ⟧ Q)
αpar-stable-termR A B P Q {s = s} stP eqQ with stable→react {t = P} stP
... | vP , τcP , eqP , hP =
      mk-stable {t = P ⟦ A ∥ B ⟧ Q}
                (fαpar-nr A B {P = P} {Q = Q} {s = s} {vP = vP} {τcP = τcP} eqP eqQ)
                hTauNothing
  where
    hTauNothing : ∀ i a → αpar-hTauL A B _,_ s τcP P Q i a ≡ nothing
    hTauNothing i a rewrite hP i a = refl

-- which normal form each operand of a STABLE composite is in.  `ret|ret` is absent:
-- it makes the composite `ret`-headed, and a `ret` head is not stable.
αNormal : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        → (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
        → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
αNormal {R = R} {S = S} P Q =
    (isStable P × isStable Q)
  ⊎ (Σ[ r ∈ R ] ((P .force ≡ ret r) × isStable Q))
  ⊎ (isStable P × Σ[ s ∈ S ] (Q .force ≡ ret s))

-- invert composite stability into the operand normal forms (the elim of `αpar-stable`
-- / `αpar-stable-termL` / `-termR`): case on the two heads, refute every `sil` shape
-- and the `ret|ret` shape, and project the composite's everywhere-`nothing` τ-map back
-- onto the operands' own τ-maps.
αpar-stable-normal : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                     (A B : EventSet)
                     (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                   → isStable (P ⟦ A ∥ B ⟧ Q) → αNormal P Q
αpar-stable-normal {I = I} {R = R} {S = S} A B P Q st =
    go (P .force) refl (Q .force) refl
  where
  go : (nP : NodeKind E (ExtI I) R) → P .force ≡ nP
     → (nQ : NodeKind E (ExtI I) S) → Q .force ≡ nQ
     → αNormal P Q
  -- a `sil` head anywhere makes the composite `sil`-headed — not stable
  go (sil P0) eqP nQ eqQ =
    ⊥-elim (stable-not-sil {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-sl A B eqP))
  go (ret r) eqP (sil Q0) eqQ =
    ⊥-elim (stable-not-sil {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-rs A B eqP eqQ))
  go (react vP τcP) eqP (sil Q0) eqQ =
    ⊥-elim (stable-not-sil {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-ns A B eqP eqQ))
  -- `ret|ret`: the composite is `ret`-headed — not stable
  go (ret r) eqP (ret s) eqQ =
    ⊥-elim (stable-not-ret {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-rr A B eqP eqQ))
  -- `ret|react`: the composite τ-map is `αpar-hTauR`; project it back onto τcQ
  go (ret r) eqP (react vQ τcQ) eqQ =
      inj₂ (inj₁ (r , eqP , mk-stable {t = Q} eqQ τcQ-nothing))
    where
    hC : ∀ i a → αpar-hTauR A B _,_ r τcQ P Q i a ≡ nothing
    hC = stable-react-τc {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-rn A B eqP eqQ)
    τcQ-nothing : ∀ i a → τcQ i a ≡ nothing
    τcQ-nothing i a with τcQ i a in tq
    ... | nothing = refl
    ... | just Q′ =
          case trans (sym (αpar-hTauR-eq A B {P = P} {Q = Q} {Q′ = Q′} {r = r}
                                         {τcQ = τcQ} {i = i} {a = a} tq))
                     (hC i a)
          of λ ()
  -- `react|ret`: mirror, via `αpar-hTauL`
  go (react vP τcP) eqP (ret s) eqQ =
      inj₂ (inj₂ (mk-stable {t = P} eqP τcP-nothing , s , eqQ))
    where
    hC : ∀ i a → αpar-hTauL A B _,_ s τcP P Q i a ≡ nothing
    hC = stable-react-τc {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-nr A B eqP eqQ)
    τcP-nothing : ∀ i a → τcP i a ≡ nothing
    τcP-nothing i a with τcP i a in tp
    ... | nothing = refl
    ... | just P′ =
          case trans (sym (αpar-hTauL-eq A B {P = P} {P′ = P′} {Q = Q} {s = s}
                                         {τcP = τcP} {i = i} {a = a} tp))
                     (hC i a)
          of λ ()
  -- `react|react`: the composite τ-map is `αpar-pTau`; tag 0 projects onto τcP and
  -- tag 1 onto τcQ, so BOTH operands are stable
  go (react vP τcP) eqP (react vQ τcQ) eqQ =
      inj₁ (mk-stable {t = P} eqP τcP-nothing , mk-stable {t = Q} eqQ τcQ-nothing)
    where
    hC : ∀ i a → αpar-pTau A B _,_ τcP τcQ P Q i a ≡ nothing
    hC = stable-react-τc {t = P ⟦ A ∥ B ⟧ Q} st (fαpar-nn A B eqP eqQ)
    τcP-nothing : ∀ i a → τcP i a ≡ nothing
    τcP-nothing (X , ii) a with τcP (X , ii) a in tp
    ... | nothing = refl
    ... | just P′ =
          case trans (sym (αpar-pTauL-eq A B {P = P} {P′ = P′} {Q = Q}
                                         {τcP = τcP} {τcQ = τcQ}
                                         {X = X} {ii = ii} {a = a} tp))
                     (hC (_ , pair (fin {n = 2}) ii) (lift fzero , a))
          of λ ()
    τcQ-nothing : ∀ i a → τcQ i a ≡ nothing
    τcQ-nothing (X , ii) a with τcQ (X , ii) a in tq
    ... | nothing = refl
    ... | just Q′ =
          case trans (sym (αpar-pTauR-eq A B {P = P} {Q = Q} {Q′ = Q′}
                                         {τcP = τcP} {τcQ = τcQ}
                                         {X = X} {ii = ii} {a = a} tq))
                     (hC (_ , pair (fin {n = 2}) ii) (lift (fsuc fzero) , a))
          of λ ()

-- a STABLE composite's LEFT operand is not `sil`-headed (it is stable or terminated)
αpar-stable-noSil-L : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                      (A B : EventSet)
                      (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                    → isStable (P ⟦ A ∥ B ⟧ Q) → NoSil P
αpar-stable-noSil-L A B P Q st with αpar-stable-normal A B P Q st
... | inj₁ (stP , _)             = noSil-stable {t = P} stP
... | inj₂ (inj₁ (r , eqP , _))  = noSil-ret {t = P} eqP
... | inj₂ (inj₂ (stP , _))      = noSil-stable {t = P} stP

-- a STABLE composite's RIGHT operand is not `sil`-headed
αpar-stable-noSil-R : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                      (A B : EventSet)
                      (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                    → isStable (P ⟦ A ∥ B ⟧ Q) → NoSil Q
αpar-stable-noSil-R A B P Q st with αpar-stable-normal A B P Q st
... | inj₁ (_ , stQ)             = noSil-stable {t = Q} stQ
... | inj₂ (inj₁ (_ , _ , stQ))  = noSil-stable {t = Q} stQ
... | inj₂ (inj₂ (_ , s , eqQ))  = noSil-ret {t = Q} eqQ

-------------------------------------------------------------------------------------
-- OFFERS: elimination (which operand(s) an offer comes from, by alphabet),
-- introduction at every head shape, and the MONOTONICITY the `stab` field consumes.
-------------------------------------------------------------------------------------

-- a stable state offers no √ (its head is `react`, not `ret`)
αpar-stable-no-√-offer : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                         {t : PTree E (ExtI I) R} {r : R} → isStable t → ¬ Offers t (√ r)
αpar-stable-no-√-offer {t = t} st (_ , sRet eq) = stable-not-ret {t = t} st eq

-- ELIM: a visible offer of the composite is routed by alphabet membership — a shared
-- event needs BOTH operands to offer it, an `A∖B` event only P, a `B∖A` event only Q
-- (an event in NEITHER alphabet is refused, so it cannot appear).
αpar-offer-elim : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                  {X : Set ℓ} {f : E X} {a : X}
                → Offers (P ⟦ A ∥ B ⟧ Q) (evl (evLabel X f a))
                → (  A .mem (X , f) a ×   B .mem (X , f) a
                     × Offers P (evl (evLabel X f a)) × Offers Q (evl (evLabel X f a)))
                ⊎ (  A .mem (X , f) a × ¬ B .mem (X , f) a
                     × Offers P (evl (evLabel X f a)))
                ⊎ (¬ A .mem (X , f) a ×   B .mem (X , f) a
                     × Offers Q (evl (evLabel X f a)))
αpar-offer-elim A B P Q (M , sVis feq br) with αpar-vis-step-inv feq br
... | vSync  mA  mB  Pev Qev = inj₁ (mA , mB , (_ , Pev) , (_ , Qev))
... | vSoloL mA  ¬mB Pev     = inj₂ (inj₁ (mA , ¬mB , (_ , Pev)))
... | vSoloR ¬mA mB  Qev     = inj₂ (inj₂ (¬mA , mB , (_ , Qev)))

-- ELIM (√): a √-offer of the composite means BOTH operands have terminated
αpar-offer-elim-√ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                    (A B : EventSet)
                    (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {x : R × S}
                  → Offers (P ⟦ A ∥ B ⟧ Q) (√ x)
                  → Σ[ r ∈ R ] Σ[ s ∈ S ]
                      ((P .force ≡ ret r) × (Q .force ≡ ret s) × (x ≡ (r , s)))
αpar-offer-elim-√ A B P Q (M , sRet feq) with αpar-√-step-inv feq
... | v√ eqP eqQ = _ , _ , eqP , eqQ , refl

-- INTRO (sync): a shared event offered by BOTH operands is offered by the composite
-- (no side condition — an offering operand is `react`-headed)
αpar-offer-sync : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                  {X : Set ℓ} {f : E X} {a : X}
                → A .mem (X , f) a → B .mem (X , f) a
                → Offers P (evl (evLabel X f a)) → Offers Q (evl (evLabel X f a))
                → Offers (P ⟦ A ∥ B ⟧ Q) (evl (evLabel X f a))
αpar-offer-sync A B P Q mA mB (P′ , Pev) (Q′ , Qev) =
  _ , αpar-sync-lift A B mA mB Pev Qev

-- INTRO (solo-L): an `A∖B` event offered by P is offered by the composite at EVERY
-- non-`sil` head of Q — `react` (via `αpar-soloL-step`) AND `ret` (via `αpar-hVisL`)
αpar-offer-soloL : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                   (A B : EventSet)
                   (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                   {X : Set ℓ} {f : E X} {a : X}
                 → A .mem (X , f) a → ¬ B .mem (X , f) a → NoSil Q
                 → Offers P (evl (evLabel X f a))
                 → Offers (P ⟦ A ∥ B ⟧ Q) (evl (evLabel X f a))
αpar-offer-soloL A B P Q mA ¬mB nsQ (P′ , Pev) =
  _ , αpar-soloL-lift A B mA ¬mB nsQ Pev

-- INTRO (solo-R): a `B∖A` event offered by Q is offered by the composite at every
-- non-`sil` head of P
αpar-offer-soloR : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                   (A B : EventSet)
                   (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S)
                   {X : Set ℓ} {f : E X} {a : X}
                 → ¬ A .mem (X , f) a → B .mem (X , f) a → NoSil P
                 → Offers Q (evl (evLabel X f a))
                 → Offers (P ⟦ A ∥ B ⟧ Q) (evl (evLabel X f a))
αpar-offer-soloR A B P Q ¬mA mB nsP (Q′ , Qev) =
  _ , αpar-soloR-lift A B ¬mA mB nsP Qev

-- INTRO (√): two terminated operands offer the joint √
αpar-offer-√ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
               (A B : EventSet)
               (P : PTree E (ExtI I) R) (Q : PTree E (ExtI I) S) {r : R} {s : S}
             → P .force ≡ ret r → Q .force ≡ ret s
             → Offers (P ⟦ A ∥ B ⟧ Q) (√ (r , s))
αpar-offer-√ A B P Q eqP eqQ = deadlock , αpar-√-step A B eqP eqQ

-- OFFER MONOTONICITY: operand-wise offer inclusion composes to composite offer
-- inclusion.  ORIENTATION (what `FSim.stab` consumes): the offers of the SETTLED SPEC
-- composite `P₂ ⟦A∥B⟧ Q₂` are included in those of the IMPL composite `P₁ ⟦A∥B⟧ Q₁`,
-- given the operand-wise spec ⊆ impl inclusions.  The `evl` cases route through the
-- offer elim/intro above (a shared event needs both operands, a solo one exactly the
-- alphabet's owner); the √ case cannot arise because the including (spec) composite is
-- stable and a √-offer needs a `ret` head.  `NoSil` on the IMPL operands is what the
-- solo intro needs; `αpar-stable-noSil-L/R` discharges both from `isStable (P₁⟦A∥B⟧Q₁)`.
αpar-offer-mono : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                  (A B : EventSet)
                  (P₁ P₂ : PTree E (ExtI I) R) (Q₁ Q₂ : PTree E (ExtI I) S)
                → NoSil P₁ → NoSil Q₁
                → isStable (P₂ ⟦ A ∥ B ⟧ Q₂)
                → (∀ e → Offers P₂ e → Offers P₁ e)
                → (∀ e → Offers Q₂ e → Offers Q₁ e)
                → ∀ e → Offers (P₂ ⟦ A ∥ B ⟧ Q₂) e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e
αpar-offer-mono A B P₁ P₂ Q₁ Q₂ nsP₁ nsQ₁ st inclP inclQ (evl (evLabel X f a)) off
  with αpar-offer-elim A B P₂ Q₂ off
... | inj₁ (mA , mB , oP , oQ) =
      αpar-offer-sync  A B P₁ Q₁ mA mB (inclP _ oP) (inclQ _ oQ)
... | inj₂ (inj₁ (mA , ¬mB , oP)) =
      αpar-offer-soloL A B P₁ Q₁ mA ¬mB nsQ₁ (inclP _ oP)
... | inj₂ (inj₂ (¬mA , mB , oQ)) =
      αpar-offer-soloR A B P₁ Q₁ ¬mA mB nsP₁ (inclQ _ oQ)
αpar-offer-mono A B P₁ P₂ Q₁ Q₂ nsP₁ nsQ₁ st inclP inclQ (√ x) off =
  ⊥-elim (αpar-stable-no-√-offer {t = P₂ ⟦ A ∥ B ⟧ Q₂} st off)

-- the same, with the two `NoSil` hypotheses read off the IMPL composite's stability
-- (the exact shape available inside an FSim `stab` field)
αpar-offer-mono-st : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                     (A B : EventSet)
                     (P₁ P₂ : PTree E (ExtI I) R) (Q₁ Q₂ : PTree E (ExtI I) S)
                   → isStable (P₁ ⟦ A ∥ B ⟧ Q₁) → isStable (P₂ ⟦ A ∥ B ⟧ Q₂)
                   → (∀ e → Offers P₂ e → Offers P₁ e)
                   → (∀ e → Offers Q₂ e → Offers Q₁ e)
                   → ∀ e → Offers (P₂ ⟦ A ∥ B ⟧ Q₂) e → Offers (P₁ ⟦ A ∥ B ⟧ Q₁) e
αpar-offer-mono-st A B P₁ P₂ Q₁ Q₂ st₁ st₂ =
  αpar-offer-mono A B P₁ P₂ Q₁ Q₂
    (αpar-stable-noSil-L A B P₁ Q₁ st₁) (αpar-stable-noSil-R A B P₁ Q₁ st₁) st₂

-- a terminated state's ONLY offer is its own √, which an equally terminated state also
-- offers — the offer inclusion for a `ret` operand (where `FSim.stab` says nothing)
ret-offer-incl : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 {S₁ T₁ : PTree E (ExtI I) R} {r : R}
               → S₁ .force ≡ ret r → T₁ .force ≡ ret r
               → ∀ e → Offers S₁ e → Offers T₁ e
ret-offer-incl {S₁ = S₁} eqS eqT (evl _) (_ , sVis eqf _) =
  ⊥-elim (case trans (sym eqS) eqf of λ ())
ret-offer-incl {S₁ = S₁} eqS eqT (√ x)   (_ , sRet eqf) with trans (sym eqS) eqf
... | refl = deadlock , sRet eqT
