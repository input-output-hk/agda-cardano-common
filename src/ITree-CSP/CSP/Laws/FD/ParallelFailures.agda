{-# OPTIONS --guardedness #-}

-- Parallel stable-failures DECOMPOSITION (elim): a failure of Par P Q at trace s
-- refusing X decomposes into a de-interleaving — reach stable operand residuals
-- P*, Q* over sub-traces sP, sQ (related to s by ParInter), the composite Par P* Q*
-- stable, and X routed to the operands' maximal refusals by the cs-split ParRef.
-- Mirrors Par-reach-div (divergence elim) EXACTLY, threading Refuses/ParRef instead
-- of Diverges; the only structural difference is the ev√ (joint-termination) case,
-- which here is NON-vacuous — it yields the p√ leaf (both operands at deadlock).

open import Level using (Level; Lift; lift)
open import Data.Maybe using (nothing)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.ParallelFailures {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E}
  using (Offers; Refuses; deadlock-no-offer; deadlock-stable; deadlock-refuses)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (deadlock-no-τ)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim  E-≟
  using (ParτR; τL; τR; Par-τ-elim; ParevR; evSync; evL; evR; evBoth; ev√; Par-ev-elim; fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; brBoth-τ-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono  E-≟
  using (brBoth-commitL; Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.FD.ParallelRefusals          E-≟
  using (MaxRef; ParRef; Par-Refuses→ParRef; ParRef→Par-Refuses; Par-stable)
open EventSet

private
  variable
    ℓ₁ ℓ₂ ℓs ℓx : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-- a stable state has no τ-move (local copy of the ExtChoiceFD helper).
stable-no-τ : {t M : PTree E (ExtI E) R} → isStable t → t ─[ τ ]─► M → ⊥
stable-no-τ {t = t} st (sSil eq)             with PTree.force t | st
... | sil _ | lift ()
stable-no-τ {t = t} st (sTau {i = i} {a = a} eq br) with PTree.force t | st | eq
... | react _ τc | st′ | refl = case trans (sym (st′ i a)) br of λ ()

-------------------------------------------------------------------------------------
-- the decomposition output: reach stable operand residuals, ParInter-interleaved,
-- composite stable, X cs-split against the operands' maximal refusals.
-------------------------------------------------------------------------------------
ParFailOut : (A : EventSet) (merge : Mg R₁ R₂ R)
             (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
             (pre : List (Event√ R)) (X : Event√ R → Set ℓx) → Set _
ParFailOut {R₁ = R₁} {R₂ = R₂} A merge P Q pre X =
  Σ[ sP ∈ List (Event√ R₁) ] Σ[ sQ ∈ List (Event√ R₂) ]
  Σ[ P* ∈ PTree E (ExtI E) R₁ ] Σ[ Q* ∈ PTree E (ExtI E) R₂ ]
    (P ⟹⟨ sP ⟩ P*) × (Q ⟹⟨ sQ ⟩ Q*) × ParInter A merge sP sQ pre
    × isStable (Par A merge P* Q*) × ParRef A X (MaxRef P*) (MaxRef Q*)

Par-reach-fail : (A : EventSet) (merge : Mg R₁ R₂ R)
                 (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                 {pre : List (Event√ R)} {W : PTree E (ExtI E) R} {X : Event√ R → Set ℓx}
               → (Par A merge P Q) ⟹⟨ pre ⟩ W → Refuses W X → ParFailOut A merge P Q pre X
Par-ov-reach-fail : (A : EventSet) (merge : Mg R₁ R₂ R)
                    (P P' : PTree E (ExtI E) R₁) (Q Q' : PTree E (ExtI E) R₂)
                    {X : Set ℓ} {e : E X} {a : X} {pre : List (Event√ R)} {W : PTree E (ExtI E) R}
                    {Y : Event√ R → Set ℓx}
                  → ¬ A .mem (X , e) a
                  → P ─[ ev (evl (evLabel X e a)) ]─► P'
                  → Q ─[ ev (evl (evLabel X e a)) ]─► Q'
                  → (ptree (react (λ _ _ → nothing) (par-brBoth A merge P Q P' Q'))) ⟹⟨ pre ⟩ W → Refuses W Y
                  → ParFailOut A merge P Q (evl (evLabel X e a) ∷ pre) Y

Par-reach-fail A merge P Q ⟹-refl refW =
  [] , [] , P , Q , ⟹-refl , ⟹-refl , pnil , proj₁ refW , Par-Refuses→ParRef A merge P Q refW
Par-reach-fail A merge P Q (⟹-τ step rest) refW with Par-τ-elim A merge P Q step
... | τL P' Pτ refl with Par-reach-fail A merge P' Q rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr = sP , sQ , P* , Q* , ⟹-τ Pτ rP , rQ , inter , stW , pr
Par-reach-fail A merge P Q (⟹-τ step rest) refW | τR Q' Qτ refl
  with Par-reach-fail A merge P Q' rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr = sP , sQ , P* , Q* , rP , ⟹-τ Qτ rQ , inter , stW , pr
Par-reach-fail A merge P Q (⟹-ev step rest) refW with Par-ev-elim A merge P Q step
... | evSync csat Pev Qev with Par-reach-fail A merge _ _ rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        _ ∷ sP , _ ∷ sQ , P* , Q* , ⟹-ev Pev rP , ⟹-ev Qev rQ , psync csat inter , stW , pr
Par-reach-fail A merge P Q (⟹-ev step rest) refW | evL ¬cs Pev
  with Par-reach-fail A merge _ Q rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        _ ∷ sP , sQ , P* , Q* , ⟹-ev Pev rP , rQ , psoloL ¬cs inter , stW , pr
Par-reach-fail A merge P Q (⟹-ev step rest) refW | evR ¬cs Qev
  with Par-reach-fail A merge P _ rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        sP , _ ∷ sQ , P* , Q* , rP , ⟹-ev Qev rQ , psoloR ¬cs inter , stW , pr
Par-reach-fail A merge P Q (⟹-ev step rest) refW | evBoth ¬cs Pev Qev =
  Par-ov-reach-fail A merge P _ Q _ ¬cs Pev Qev rest refW
Par-reach-fail A merge P Q (⟹-ev step rest) refW | ev√ {r₁ = r₁} {r₂ = r₂} fpP fpQ with rest
...   | ⟹-refl =
        √ r₁ ∷ [] , √ r₂ ∷ [] , deadlock , deadlock ,
        ⟹-ev (sRet fpP) ⟹-refl , ⟹-ev (sRet fpQ) ⟹-refl , p√ ,
        Par-stable A merge deadlock deadlock deadlock-stable deadlock-stable ,
        ( (λ f a _ _ → inj₁ λ o → deadlock-no-offer (proj₂ o))
        , (λ f a _ _ → (λ o → deadlock-no-offer (proj₂ o)) , λ o → deadlock-no-offer (proj₂ o)) )
...   | ⟹-τ step′ _  = ⊥-elim (deadlock-no-τ step′)
...   | ⟹-ev step′ _ = ⊥-elim (deadlock-no-offer step′)

Par-ov-reach-fail A merge P P' Q Q' ¬cs Pev Qev ⟹-refl refW =
  ⊥-elim (stable-no-τ (proj₁ refW) (brBoth-commitL A merge P Q P' Q'))
Par-ov-reach-fail A merge P P' Q Q' ¬cs Pev Qev (⟹-τ step rest) refW
  with brBoth-τ-elim A merge P Q P' Q' step
... | inj₁ refl with Par-reach-fail A merge P' Q rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        _ ∷ sP , sQ , P* , Q* , ⟹-ev Pev rP , rQ , psoloL ¬cs inter , stW , pr
Par-ov-reach-fail A merge P P' Q Q' ¬cs Pev Qev (⟹-τ step rest) refW | inj₂ refl
  with Par-reach-fail A merge P Q' rest refW
...   | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        sP , _ ∷ sQ , P* , Q* , rP , ⟹-ev Qev rQ , psoloR ¬cs inter , stW , pr
Par-ov-reach-fail A merge P P' Q Q' ¬cs Pev Qev (⟹-ev (sVis refl ()) _) refW
Par-ov-reach-fail A merge P P' Q Q' ¬cs Pev Qev (⟹-ev (sRet ()) _) refW

-- top-level: a stable failure of Par P Q decomposes (the divergence is at SOME stable
-- residual reached along the trace).
Par-failures-elim : (A : EventSet) (merge : Mg R₁ R₂ R)
                    {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
                    {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                  → failures (Par A merge P Q) s X → ParFailOut A merge P Q s X
Par-failures-elim A merge {P = P} {Q = Q} (W , reach , refW) =
  Par-reach-fail A merge P Q reach refW

-------------------------------------------------------------------------------------
-- Par-failures-intro : the dual of Par-failures-elim.  Re-interleave the operand
-- residuals per the ParInter witness into a composite failure.  Mirrors Par-div-intro
-- (carrying the stable-composite + ParRef leaf certificate instead of a divergence).
-------------------------------------------------------------------------------------
-- failures is a plain Σ ⇒ the prepends just extend the reach.
fail-τ-prepend : {P P′ : PTree E (ExtI E) R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
               → P ─[ τ ]─► P′ → failures P′ s X → failures P s X
fail-τ-prepend step (W , reach , ref) = W , ⟹-τ step reach , ref

fail-ev-prepend : {P P′ : PTree E (ExtI E) R} {e : Event√ R} {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                → P ─[ ev e ]─► P′ → failures P′ s X → failures P (e ∷ s) X
fail-ev-prepend step (W , reach , ref) = W , ⟹-ev step reach , ref

Par-failures-intro : (A : EventSet) (merge : Mg R₁ R₂ R)
                     (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
                     {P* : PTree E (ExtI E) R₁} {Q* : PTree E (ExtI E) R₂}
                     {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
                     {X : Event√ R → Set ℓx}
                   → P ⟹⟨ sP ⟩ P* → Q ⟹⟨ sQ ⟩ Q* → ParInter A merge sP sQ s
                   → isStable (Par A merge P* Q*) → ParRef A X (MaxRef P*) (MaxRef Q*)
                   → failures (Par A merge P Q) s X
-- drain P's / Q's τ's
Par-failures-intro A merge P Q (⟹-τ Pτ restP) Qbs PI stPar pr =
  fail-τ-prepend (Par-τ-L A merge P Q Pτ)
                 (Par-failures-intro A merge _ Q restP Qbs PI stPar pr)
Par-failures-intro A merge P Q Pbs (⟹-τ Qτ restQ) PI stPar pr =
  fail-τ-prepend (Par-τ-R A merge P Q Qτ)
                 (Par-failures-intro A merge P _ Pbs restQ PI stPar pr)
-- base: both operands settled — the composite refuses X via the ParRef leaf
Par-failures-intro A merge P Q ⟹-refl ⟹-refl pnil stPar pr =
  Par A merge P Q , ⟹-refl , ParRef→Par-Refuses A merge P Q stPar pr
-- a shared (in `A`) event
Par-failures-intro A merge P Q (⟹-ev Pev restP) (⟹-ev Qev restQ) (psync csat PI) stPar pr =
  fail-ev-prepend (Par-sync A merge P Q csat Pev Qev)
                  (Par-failures-intro A merge _ _ restP restQ PI stPar pr)
-- a solo (outside `A`) event on the left / right (multi-step reach via the overlap)
Par-failures-intro A merge P Q (⟹-ev Pev restP) Qbs (psoloL ¬cs PI) stPar pr
  with Par-failures-intro A merge _ Q restP Qbs PI stPar pr
... | W , reach , ref = W , Par-soloL-reach A merge P Q ¬cs Pev reach , ref
Par-failures-intro A merge P Q Pbs (⟹-ev Qev restQ) (psoloR ¬cs PI) stPar pr
  with Par-failures-intro A merge P _ Pbs restQ PI stPar pr
... | W , reach , ref = W , Par-soloR-reach A merge P Q ¬cs Qev reach , ref
-- joint √ : both operands terminate ⇒ the composite emits the joint √ to deadlock,
-- which refuses everything (the leaf certificate is irrelevant here).
Par-failures-intro A merge P Q (⟹-ev (sRet eqPr) restP) (⟹-ev (sRet eqQr) restQ) p√ stPar pr =
  deadlock , ⟹-ev (sRet (fPar-rr A merge eqPr eqQr)) ⟹-refl , deadlock-refuses

-- top-level: a decomposed failure recomposes into a failure of Par P Q.
Par-failures-intro-top : (A : EventSet) (merge : Mg R₁ R₂ R)
                         {P : PTree E (ExtI E) R₁} {Q : PTree E (ExtI E) R₂}
                         {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                       → ParFailOut A merge P Q s X → failures (Par A merge P Q) s X
Par-failures-intro-top A merge {P = P} {Q = Q} (sP , sQ , P* , Q* , rP , rQ , inter , stW , pr) =
  Par-failures-intro A merge P Q rP rQ inter stW pr
