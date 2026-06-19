{-# OPTIONS --guardedness #-}

-- Divergence half of parallel associativity (homogeneous R, associative merge — for
-- Par⊤/⦀ the merge is ⊤'s, trivially associative).  The divergence transfer is CLEAN
-- (no joint-√ wart): a diverging operand never terminates, so its trace has no √, so
-- ParInter never produces the joint p√ — every re-interleaving reaches a clean Par
-- state.  This is captured by Par-div-reach (Par-div-intro returning the EXPLICIT reach
-- to Par Q* R* + Diverges (Par Q* R*); its p√ case is refuted by the operand divergence).

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ParallelAssocDiv {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (Diverges; deadlock-converges; deadlock-no-τ)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; IsDivergence; div-extension-closed)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono  E-≟
  using (Par-soloL-reach; Par-soloR-reach; Par-trace-intro)
open import CSP.Laws.Traces.TraceLawsParallelInterAssoc E-≟
  using (ParInter-assoc-LR; ParInter-assoc-RL)
open import CSP.Laws.FD.ParallelDivergence E-≟
  using (ParDivOut; Par-reach-div; Par-div-intro; Par-Diverges-L; Par-Diverges-R)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- Par-div-reach : re-interleave Q, R per a ParInter into the EXPLICIT composite reach
-- Par Q R ⟹ Par Q* R*, carrying the operand divergence up to Diverges (Par Q* R*).
-- (Par-div-intro restructured to expose the reached state; p√ refuted by the divergence.)
-------------------------------------------------------------------------------------
Par-div-reach : (A : EventSet) (merge : Mg R R R)
                (Q R₀ : PTree E (ExtI E) R)
                {Q* R* : PTree E (ExtI E) R}
                {sQ sR sQR : List (Event√ R)}
              → Q ⟹⟨ sQ ⟩ Q* → R₀ ⟹⟨ sR ⟩ R* → ParInter A merge sQ sR sQR
              → Diverges Q* ⊎ Diverges R*
              → ((Par A merge Q R₀) ⟹⟨ sQR ⟩ Par A merge Q* R*)
                × Diverges (Par A merge Q* R*)
Par-div-reach A merge Q R₀ (⟹-τ Qτ restQ) Rbs PI dd
  with Par-div-reach A merge _ R₀ restQ Rbs PI dd
... | reach , div = ⟹-τ (Par-τ-L A merge Q R₀ Qτ) reach , div
Par-div-reach A merge Q R₀ Qbs (⟹-τ Rτ restR) PI dd
  with Par-div-reach A merge Q _ Qbs restR PI dd
... | reach , div = ⟹-τ (Par-τ-R A merge Q R₀ Rτ) reach , div
Par-div-reach A merge Q R₀ ⟹-refl ⟹-refl pnil (inj₁ dQ) =
  ⟹-refl , Par-Diverges-L A merge R₀ dQ
Par-div-reach A merge Q R₀ ⟹-refl ⟹-refl pnil (inj₂ dR) =
  ⟹-refl , Par-Diverges-R A merge Q dR
Par-div-reach A merge Q R₀ (⟹-ev Qev restQ) (⟹-ev Rev restR) (psync csat PI) dd
  with Par-div-reach A merge _ _ restQ restR PI dd
... | reach , div = ⟹-ev (Par-sync A merge Q R₀ csat Qev Rev) reach , div
Par-div-reach A merge Q R₀ (⟹-ev Qev restQ) Rbs (psoloL ¬cs PI) dd
  with Par-div-reach A merge _ R₀ restQ Rbs PI dd
... | reach , div = Par-soloL-reach A merge Q R₀ ¬cs Qev reach , div
Par-div-reach A merge Q R₀ Qbs (⟹-ev Rev restR) (psoloR ¬cs PI) dd
  with Par-div-reach A merge Q _ Qbs restR PI dd
... | reach , div = Par-soloR-reach A merge Q R₀ ¬cs Rev reach , div
Par-div-reach A merge Q R₀ (⟹-ev (sRet _) ⟹-refl) (⟹-ev (sRet _) restR) p√ (inj₁ dQ) =
  ⊥-elim (deadlock-converges dQ)
Par-div-reach A merge Q R₀ (⟹-ev (sRet _) (⟹-τ step _)) (⟹-ev (sRet _) restR) p√ (inj₁ dQ) =
  ⊥-elim (deadlock-no-τ step)
Par-div-reach A merge Q R₀ (⟹-ev (sRet _) restQ) (⟹-ev (sRet _) ⟹-refl) p√ (inj₂ dR) =
  ⊥-elim (deadlock-converges dR)
Par-div-reach A merge Q R₀ (⟹-ev (sRet _) restQ) (⟹-ev (sRet _) (⟹-τ step _)) p√ (inj₂ dR) =
  ⊥-elim (deadlock-no-τ step)

-------------------------------------------------------------------------------------
-- the LR transfer at a prefix: a decomposed divergence of (P∥Q)∥R re-brackets to one
-- of P∥(Q∥R).  Cases on WHERE the divergence is (R / P / Q); P uses a plain re-interleave
-- (Par-trace-intro), the Q∥R-side uses Par-div-reach (carrying the divergence).
-------------------------------------------------------------------------------------
Par-assoc-div-LR : (A : EventSet) (merge : Mg R R R)
                   (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                   (P Q R₀ : PTree E (ExtI E) R) {pre : List (Event√ R)}
                 → ParDivOut A merge (Par A merge P Q) R₀ pre
                 → divergences (Par A merge P (Par A merge Q R₀)) pre
-- R diverges: decompose the (P∥Q)-reach by TRACE (no divergence on that side)
Par-assoc-div-LR A merge ma P Q R₀ (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , inj₂ dR*)
  with Par-trace-elim A merge P Q reach_PQ
... | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i
  with ParInter-assoc-LR A merge ma inter_i inter_o
...  | s_QR , jQR , jP with Par-div-reach A merge Q R₀ reach_Q reach_R jQR (inj₂ dR*)
...    | reach_QR , dQR =
         Par-div-intro A merge P (Par A merge Q R₀) reach_P reach_QR jP (inj₂ dQR)
-- (P∥Q) diverges: decompose it by DIVERGENCE — gives which of P, Q diverges
Par-assoc-div-LR A merge ma P Q R₀ (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , inj₁ dPQ*)
  with Par-reach-div A merge P Q reach_PQ dPQ*
... | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , inj₁ dP*
  with ParInter-assoc-LR A merge ma inter_i inter_o
...  | s_QR , jQR , jP with Par-trace-intro A merge Q R₀ reach_Q reach_R jQR
...    | QR* , reach_QR =
         Par-div-intro A merge P (Par A merge Q R₀) reach_P reach_QR jP (inj₁ dP*)
Par-assoc-div-LR A merge ma P Q R₀ (s_PQ , s_R , PQ* , R* , reach_PQ , reach_R , inter_o , inj₁ dPQ*)
  | s_P , s_Q , P* , Q* , reach_P , reach_Q , inter_i , inj₂ dQ*
  with ParInter-assoc-LR A merge ma inter_i inter_o
...  | s_QR , jQR , jP with Par-div-reach A merge Q R₀ reach_Q reach_R jQR (inj₁ dQ*)
...    | reach_QR , dQR =
         Par-div-intro A merge P (Par A merge Q R₀) reach_P reach_QR jP (inj₂ dQR)

-- top-level: divergences (P∥Q)∥R s → divergences P∥(Q∥R) s (extension-closed wrap).
div-transfer-LR : (A : EventSet) (merge : Mg R R R)
                  (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                  (P Q R₀ : PTree E (ExtI E) R) {s : List (Event√ R)}
                → divergences (Par A merge (Par A merge P Q) R₀) s
                → divergences (Par A merge P (Par A merge Q R₀)) s
div-transfer-LR A merge ma P Q R₀ {s} d =
  subst (divergences (Par A merge P (Par A merge Q R₀))) (sym (d .IsDivergence.split))
    (div-extension-closed {t = d .IsDivergence.suffix}
      (Par-assoc-div-LR A merge ma P Q R₀
        (Par-reach-div A merge (Par A merge P Q) R₀
          (d .IsDivergence.reach) (d .IsDivergence.divwit))))

-------------------------------------------------------------------------------------
-- the RL transfer (mirror): a decomposed divergence of P∥(Q∥R) re-brackets to (P∥Q)∥R.
-------------------------------------------------------------------------------------
Par-assoc-div-RL : (A : EventSet) (merge : Mg R R R)
                   (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                   (P Q R₀ : PTree E (ExtI E) R) {pre : List (Event√ R)}
                 → ParDivOut A merge P (Par A merge Q R₀) pre
                 → divergences (Par A merge (Par A merge P Q) R₀) pre
-- P diverges: decompose the (Q∥R)-reach by TRACE
Par-assoc-div-RL A merge ma P Q R₀ (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , inj₁ dP*)
  with Par-trace-elim A merge Q R₀ reach_QR
... | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i
  with ParInter-assoc-RL A merge ma inter_i inter_o
...  | s_PQ , jPQ , jR with Par-div-reach A merge P Q reach_P reach_Q jPQ (inj₁ dP*)
...    | reach_PQ , dPQ =
         Par-div-intro A merge (Par A merge P Q) R₀ reach_PQ reach_R jR (inj₁ dPQ)
-- (Q∥R) diverges: decompose it by DIVERGENCE — gives which of Q, R diverges
Par-assoc-div-RL A merge ma P Q R₀ (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , inj₂ dQR*)
  with Par-reach-div A merge Q R₀ reach_QR dQR*
... | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , inj₁ dQ*
  with ParInter-assoc-RL A merge ma inter_i inter_o
...  | s_PQ , jPQ , jR with Par-div-reach A merge P Q reach_P reach_Q jPQ (inj₂ dQ*)
...    | reach_PQ , dPQ =
         Par-div-intro A merge (Par A merge P Q) R₀ reach_PQ reach_R jR (inj₁ dPQ)
Par-assoc-div-RL A merge ma P Q R₀ (s_P , s_QR , P* , QR* , reach_P , reach_QR , inter_o , inj₂ dQR*)
  | s_Q , s_R , Q* , R* , reach_Q , reach_R , inter_i , inj₂ dR*
  with ParInter-assoc-RL A merge ma inter_i inter_o
...  | s_PQ , jPQ , jR with Par-trace-intro A merge P Q reach_P reach_Q jPQ
...    | PQ* , reach_PQ =
         Par-div-intro A merge (Par A merge P Q) R₀ reach_PQ reach_R jR (inj₂ dR*)

div-transfer-RL : (A : EventSet) (merge : Mg R R R)
                  (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                  (P Q R₀ : PTree E (ExtI E) R) {s : List (Event√ R)}
                → divergences (Par A merge P (Par A merge Q R₀)) s
                → divergences (Par A merge (Par A merge P Q) R₀) s
div-transfer-RL A merge ma P Q R₀ {s} d =
  subst (divergences (Par A merge (Par A merge P Q) R₀)) (sym (d .IsDivergence.split))
    (div-extension-closed {t = d .IsDivergence.suffix}
      (Par-assoc-div-RL A merge ma P Q R₀
        (Par-reach-div A merge P (Par A merge Q R₀)
          (d .IsDivergence.reach) (d .IsDivergence.divwit))))
