{-# OPTIONS --guardedness #-}

-- Parallel ASSOCIATIVITY at ≈FD (homogeneous R, associative merge — for Par⊤/⦀ the merge
-- is ⊤'s, trivially associative):  (P ∥ Q) ∥ R ≈FD P ∥ (Q ∥ R).
--
-- FD-DIRECT (NOT a weak/strong bisim — when P,Q,R all offer the same outside-`A` event, the two
-- bracketings commit their overlaps in a different order; see [[project_state]]).  The
-- divergence half is done in ParallelAssocDiv (div-transfer-LR/RL).  This module assembles
-- the FAILURES half (the harder one, with the termination/√ bookkeeping) and the ≈FD.
--
-- Per direction the failures transfer is: Par-failures-elim (outer) → classify the stable
-- leaf → decompose the still-bracketed operand (Par-failures-elim if stable, else
-- Par-trace-elim-eq for the terminated case) → ParInter-assoc reassociate → re-interleave
-- the other bracketing with Par-trace-reach (explicit codomain Par·R*, or deadlock on the
-- joint-√ tail) → Par-failures-intro-top.  Refusal/stability reassociation via
-- ParRef-build-R/L + Par-stable-assoc-LR/RL.

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Laws.FD.ParallelAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers; deadlock-no-offer)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; _⊑F⊥_; _⊑D_; _≈FD_)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (ParInter; Par-trace-elim-eq)
open import CSP.Laws.Traces.TraceLawsParallelInterAssoc E-≟
  using (ParInter-assoc-LR; ParInter-assoc-RL)
open import CSP.Laws.FD.ParallelFailures E-≟
  using (ParFailOut; Par-failures-elim; Par-failures-intro-top)
open import CSP.Laws.FD.ParallelRefusals E-≟
  using (MaxRef; ParRef; ParRef-build-R; ParRef-build-L
        ; Par-stable; Par-stable-termL; Par-stable-termR; ret-no-vis-offer)
open import CSP.Laws.FD.ParallelAssocFail E-≟
  using (Par-trace-reach; Par-stable-classify; bothS; termL; termR
        ; Par-stable-assoc-LR; Par-stable-assoc-RL; Par-force-ret-inv)
open import CSP.Laws.FD.ParallelAssocDiv E-≟ using (div-transfer-LR; div-transfer-RL)

private
  variable
    ℓr ℓx ℓa ℓb : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- small refusal helpers
-------------------------------------------------------------------------------------

-- a ret operand refuses every visible event (offers only √).
ret-maxref : {t : PTree E (ExtI E) R} {r : R} → PTree.force t ≡ ret r
           → ∀ {A} (f : E A) (a : A) → MaxRef t (evl (evLabel A f a))
ret-maxref eqf f a o = ret-no-vis-offer eqf o

-- weaken the right operand of a ParRef to `deadlock` (which refuses everything).
parRef→dl-R : (A : EventSet)
            → {X : Event√ R → Set ℓx} {AP : Event√ R → Set ℓa} {BP : Event√ R → Set ℓb}
            → ParRef A X AP BP → ParRef A X AP (MaxRef (deadlock {R = R}))
parRef→dl-R A {X = X} {AP = AP} (csCl , ncsCl) = csCl′ , ncsCl′
  where
    dl : ∀ {C} (f : E C) (a : C) → MaxRef (deadlock {R = R}) (evl (evLabel C f a))
    dl f a o = deadlock-no-offer (proj₂ o)
    csCl′ : ∀ {C} (f : E C) (a : C) → A .mem (C , f) a → X (evl (evLabel C f a))
          → AP (evl (evLabel C f a)) ⊎ MaxRef (deadlock {R = R}) (evl (evLabel C f a))
    csCl′ f a csat Xe with csCl f a csat Xe
    ... | inj₁ mA = inj₁ mA
    ... | inj₂ _  = inj₂ (dl f a)
    ncsCl′ : ∀ {C} (f : E C) (a : C) → ¬ A .mem (C , f) a → X (evl (evLabel C f a))
           → AP (evl (evLabel C f a)) × MaxRef (deadlock {R = R}) (evl (evLabel C f a))
    ncsCl′ f a ¬csat Xe = proj₁ (ncsCl f a ¬csat Xe) , dl f a

-- weaken the LEFT operand of a ParRef to `deadlock` (mirror of parRef→dl-R).
parRef→dl-L : (A : EventSet)
            → {X : Event√ R → Set ℓx} {AP : Event√ R → Set ℓa} {BP : Event√ R → Set ℓb}
            → ParRef A X BP AP → ParRef A X (MaxRef (deadlock {R = R})) AP
parRef→dl-L A {X = X} {AP = AP} (csCl , ncsCl) = csCl′ , ncsCl′
  where
    dl : ∀ {C} (f : E C) (a : C) → MaxRef (deadlock {R = R}) (evl (evLabel C f a))
    dl f a o = deadlock-no-offer (proj₂ o)
    csCl′ : ∀ {C} (f : E C) (a : C) → A .mem (C , f) a → X (evl (evLabel C f a))
          → MaxRef (deadlock {R = R}) (evl (evLabel C f a)) ⊎ AP (evl (evLabel C f a))
    csCl′ f a csat Xe with csCl f a csat Xe
    ... | inj₁ _  = inj₁ (dl f a)
    ... | inj₂ mA = inj₂ mA
    ncsCl′ : ∀ {C} (f : E C) (a : C) → ¬ A .mem (C , f) a → X (evl (evLabel C f a))
           → MaxRef (deadlock {R = R}) (evl (evLabel C f a)) × AP (evl (evLabel C f a))
    ncsCl′ f a ¬csat Xe = dl f a , proj₂ (ncsCl f a ¬csat Xe)

-- the trivial inner ParRef when both operands are terminated (ret ⇒ refuse all visible).
ret-inner-ParRef : (A : EventSet) {Z : Event√ R → Set ℓa}
                   {P* Q* : PTree E (ExtI E) R} {rp rq : R}
                 → PTree.force P* ≡ ret rp → PTree.force Q* ≡ ret rq
                 → ParRef A Z (MaxRef P*) (MaxRef Q*)
ret-inner-ParRef A eqP eqQ =
    (λ f a _ _ → inj₁ (ret-maxref eqP f a))
  , (λ f a _ _ → ret-maxref eqP f a , ret-maxref eqQ f a)

-------------------------------------------------------------------------------------
-- the LR failures transfer:  failures of (P∥Q)∥R  →  failures of P∥(Q∥R).
-------------------------------------------------------------------------------------
module _ (A : EventSet) (merge : Mg R R R)
         (ma : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
         (P Q R₀ : PTree E (ExtI E) R) where

  -- the common inj₁ assembly (operand reaches reach an explicit Par Q* R*).
  private
    intro-spine : (X : Event√ R → Set ℓx)
                  {s_P s_QR pre : List (Event√ R)} {P* Q* R* : PTree E (ExtI E) R}
                → P ⟹⟨ s_P ⟩ P* → (Par A merge Q R₀) ⟹⟨ s_QR ⟩ (Par A merge Q* R*)
                → ParInter A merge s_P s_QR pre
                → isStable (Par A merge (Par A merge P* Q*) R*)
                → ParRef A X (MaxRef P*) (MaxRef (Par A merge Q* R*))
                → failures (Par A merge P (Par A merge Q R₀)) pre X
    intro-spine X {P* = P*} {Q* = Q*} {R* = R*} rP rQR jP stInner parRef =
      Par-failures-intro-top A merge {X = X}
        (_ , _ , P* , Par A merge Q* R* , rP , rQR , jP
           , Par-stable-assoc-LR A merge P* Q* R* stInner , parRef)

  Par-assoc-fail-LR : {pre : List (Event√ R)} (X : Event√ R → Set ℓx)
                    → ParFailOut A merge (Par A merge P Q) R₀ pre X
                    → failures (Par A merge P (Par A merge Q R₀)) pre X
  Par-assoc-fail-LR X (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , stO , prX)
    with Par-stable-classify A merge PQ* R* stO
  -- ── PQ* stable, R* stable ───────────────────────────────────────────────────────
  ... | bothS stPQ stR
    with Par-failures-elim A merge {X = MaxRef PQ*} (PQ* , reach_PQ , (stPQ , λ e me → me))
  ...   | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , stPQ′ , inner-L
    with ParInter-assoc-LR A merge ma inter_i inter_o
  ...     | s_QR , jQR , jP
    with Par-trace-reach A merge Q R₀ reach_Q reach_R jQR
  ...       | inj₁ reach_QR =
              intro-spine X reach_P reach_QR jP
                (Par-stable A merge (Par A merge P* Q*) R* stPQ′ stR)
                (ParRef-build-R A merge P* Q* R* {X = X} (MaxRef PQ*) prX inner-L)
  ...       | inj₂ (reach_dl , refl , refl) =
              Par-failures-intro-top A merge {X = X}
                (s_P , s_QR , P* , deadlock , reach_P , reach_dl , jP , stPQ′
                   , parRef→dl-R A {X = X} {AP = MaxRef P*} {BP = MaxRef (Par A merge deadlock deadlock)}
                       (ParRef-build-R A merge P* deadlock deadlock {X = X} (MaxRef PQ*) prX inner-L))
  -- ── PQ* stable, R* terminated ───────────────────────────────────────────────────
  Par-assoc-fail-LR X (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , stO , prX)
    | termR stPQ (rR , eqR)
    with Par-failures-elim A merge {X = MaxRef PQ*} (PQ* , reach_PQ , (stPQ , λ e me → me))
  ...   | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , stPQ′ , inner-L
    with ParInter-assoc-LR A merge ma inter_i inter_o
  ...     | s_QR , jQR , jP
    with Par-trace-reach A merge Q R₀ reach_Q reach_R jQR
  ...       | inj₁ reach_QR =
              intro-spine X reach_P reach_QR jP
                (Par-stable-termR A merge (Par A merge P* Q*) R* stPQ′ eqR)
                (ParRef-build-R A merge P* Q* R* {X = X} (MaxRef PQ*) prX inner-L)
  ...       | inj₂ (reach_dl , eQ , refl) = ⊥-elim (case eqR of λ ())
  -- ── PQ* terminated, R* stable ───────────────────────────────────────────────────
  Par-assoc-fail-LR X (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , stO , prX)
    | termL (rPQ , eqPQ) stR
    with Par-trace-elim-eq A merge P Q reach_PQ
  ...   | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , inj₂ ¬ret =
          ⊥-elim (¬ret (rPQ , eqPQ))
  ...   | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , inj₁ refl
    with Par-force-ret-inv A merge eqPQ
  ...     | rp , rq , eqP , eqQ , _
    with ParInter-assoc-LR A merge ma inter_i inter_o
  ...       | s_QR , jQR , jP
    with Par-trace-reach A merge Q R₀ reach_Q reach_R jQR
  ...         | inj₁ reach_QR =
                intro-spine X reach_P reach_QR jP stO
                  (ParRef-build-R A merge P* Q* R* {X = X} (MaxRef (Par A merge P* Q*))
                    prX (ret-inner-ParRef A {Z = MaxRef (Par A merge P* Q*)} eqP eqQ))
  ...         | inj₂ (reach_dl , refl , _) = ⊥-elim (case eqQ of λ ())

  -----------------------------------------------------------------------------------
  -- the RL failures transfer:  failures of P∥(Q∥R)  →  failures of (P∥Q)∥R.
  -----------------------------------------------------------------------------------
  private
    intro-spine-R : (X : Event√ R → Set ℓx)
                    {s_PQ s_R pre : List (Event√ R)} {P* Q* R* : PTree E (ExtI E) R}
                  → (Par A merge P Q) ⟹⟨ s_PQ ⟩ (Par A merge P* Q*) → R₀ ⟹⟨ s_R ⟩ R*
                  → ParInter A merge s_PQ s_R pre
                  → isStable (Par A merge P* (Par A merge Q* R*))
                  → ParRef A X (MaxRef (Par A merge P* Q*)) (MaxRef R*)
                  → failures (Par A merge (Par A merge P Q) R₀) pre X
    intro-spine-R X {P* = P*} {Q* = Q*} {R* = R*} rPQ rR jR stInner parRef =
      Par-failures-intro-top A merge {X = X}
        (_ , _ , Par A merge P* Q* , R* , rPQ , rR , jR
           , Par-stable-assoc-RL A merge P* Q* R* stInner , parRef)

  Par-assoc-fail-RL : {pre : List (Event√ R)} (X : Event√ R → Set ℓx)
                    → ParFailOut A merge P (Par A merge Q R₀) pre X
                    → failures (Par A merge (Par A merge P Q) R₀) pre X
  Par-assoc-fail-RL X (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , stO , prX)
    with Par-stable-classify A merge P* QR* stO
  -- ── P* stable, QR* stable ───────────────────────────────────────────────────────
  ... | bothS stP stQR
    with Par-failures-elim A merge {X = MaxRef QR*} (QR* , reach_QR , (stQR , λ e me → me))
  ...   | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , stQR′ , inner-R
    with ParInter-assoc-RL A merge ma inter_i inter_o
  ...     | s_PQ , jPQ , jR
    with Par-trace-reach A merge P Q reach_P reach_Q jPQ
  ...       | inj₁ reach_PQ =
              intro-spine-R X reach_PQ reach_R jR
                (Par-stable A merge P* (Par A merge Q* R*) stP stQR′)
                (ParRef-build-L A merge P* Q* R* {X = X} (MaxRef QR*) prX inner-R)
  ...       | inj₂ (reach_dl , refl , refl) =
              Par-failures-intro-top A merge {X = X}
                (s_PQ , s_R , deadlock , R* , reach_dl , reach_R , jR , stQR′
                   , parRef→dl-L A {X = X} {AP = MaxRef R*} {BP = MaxRef (Par A merge deadlock deadlock)}
                       (ParRef-build-L A merge deadlock deadlock R* {X = X} (MaxRef QR*) prX inner-R))
  -- ── P* terminated, QR* stable ───────────────────────────────────────────────────
  Par-assoc-fail-RL X (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , stO , prX)
    | termL (rP , eqP) stQR
    with Par-failures-elim A merge {X = MaxRef QR*} (QR* , reach_QR , (stQR , λ e me → me))
  ...   | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , stQR′ , inner-R
    with ParInter-assoc-RL A merge ma inter_i inter_o
  ...     | s_PQ , jPQ , jR
    with Par-trace-reach A merge P Q reach_P reach_Q jPQ
  ...       | inj₁ reach_PQ =
              intro-spine-R X reach_PQ reach_R jR
                (Par-stable-termL A merge P* (Par A merge Q* R*) eqP stQR′)
                (ParRef-build-L A merge P* Q* R* {X = X} (MaxRef QR*) prX inner-R)
  ...       | inj₂ (reach_dl , refl , _) = ⊥-elim (case eqP of λ ())
  -- ── P* stable, QR* terminated ───────────────────────────────────────────────────
  Par-assoc-fail-RL X (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , stO , prX)
    | termR stP (rQR , eqQR)
    with Par-trace-elim-eq A merge Q R₀ reach_QR
  ...   | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , inj₂ ¬ret =
          ⊥-elim (¬ret (rQR , eqQR))
  ...   | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , inj₁ refl
    with Par-force-ret-inv A merge eqQR
  ...     | rq , rr , eqQ , eqR , _
    with ParInter-assoc-RL A merge ma inter_i inter_o
  ...       | s_PQ , jPQ , jR
    with Par-trace-reach A merge P Q reach_P reach_Q jPQ
  ...         | inj₁ reach_PQ =
                intro-spine-R X reach_PQ reach_R jR stO
                  (ParRef-build-L A merge P* Q* R* {X = X} (MaxRef (Par A merge Q* R*))
                    prX (ret-inner-ParRef A {Z = MaxRef (Par A merge Q* R*)} eqQ eqR))
  ...         | inj₂ (reach_dl , _ , refl) = ⊥-elim (case eqQ of λ ())

  -----------------------------------------------------------------------------------
  -- ≈FD assembly:  (P∥Q)∥R  ≈FD  P∥(Q∥R).
  -----------------------------------------------------------------------------------
  private
    LHS : PTree E (ExtI E) R
    LHS = Par A merge (Par A merge P Q) R₀
    RHS : PTree E (ExtI E) R
    RHS = Par A merge P (Par A merge Q R₀)

    af₁ : LHS ⊑F⊥ RHS
    af₁ {B = X} (inj₁ f) = inj₁ (Par-assoc-fail-RL X (Par-failures-elim A merge f))
    af₁ (inj₂ d) = inj₂ (div-transfer-RL A merge ma P Q R₀ d)
    ad₁ : LHS ⊑D RHS
    ad₁ d = div-transfer-RL A merge ma P Q R₀ d
    af₂ : RHS ⊑F⊥ LHS
    af₂ {B = X} (inj₁ f) = inj₁ (Par-assoc-fail-LR X (Par-failures-elim A merge f))
    af₂ (inj₂ d) = inj₂ (div-transfer-LR A merge ma P Q R₀ d)
    ad₂ : RHS ⊑D LHS
    ad₂ d = div-transfer-LR A merge ma P Q R₀ d

  Par-assoc-FD : LHS ≈FD RHS
  Par-assoc-FD = (af₁ , ad₁) , (af₂ , ad₂)

-------------------------------------------------------------------------------------
-- instances: ⊤-merge (Par⊤) and interleaving (⦀, cs = ∅)
-------------------------------------------------------------------------------------
Par⊤-assoc-FD : (A : EventSet) (P Q R₀ : PTree E (ExtI E) (⊤ {ℓr}))
              → ((P ∥⇘ A ⇙ Q) ∥⇘ A ⇙ R₀) ≈FD (P ∥⇘ A ⇙ (Q ∥⇘ A ⇙ R₀))
Par⊤-assoc-FD A P Q R₀ = Par-assoc-FD A (λ _ _ → tt) (λ a b c → refl) P Q R₀

⦀-assoc-FD : (P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})) → ((P ⦀ Q) ⦀ R₀) ≈FD (P ⦀ (Q ⦀ R₀))
⦀-assoc-FD P Q R₀ = Par⊤-assoc-FD ∅ES P Q R₀
