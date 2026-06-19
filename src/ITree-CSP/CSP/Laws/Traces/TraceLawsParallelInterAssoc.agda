{-# OPTIONS --guardedness #-}

-- Associativity of the `A`-synchronised interleaving ParInter (homogeneous R, with an
-- associative merge — for Par⊤/⦀ the merge is ⊤'s λ _ _ → tt, trivially associative).
--
--   ParInter-assoc-LR : (P,Q ⇒ s_PQ) → (s_PQ,R ⇒ s)  ⊢  ∃ s_QR. (Q,R ⇒ s_QR) × (P,s_QR ⇒ s)
--   ParInter-assoc-RL : the converse re-bracketing.
--
-- The reassociation routes each event by where it lives: a 3-way `A`-sync stays a sync;
-- a P-solo stays a P-solo; a Q-solo becomes solo-in-(Q∥R) then solo-from-the-QR-side; an
-- R-solo symmetric.  A sync-vs-solo clash (in `A` vs outside `A` on the same event) is impossible.

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsParallelInterAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators                          E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsParallel      E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- left-to-right re-bracketing of a nested interleaving.
ParInter-assoc-LR : (A : EventSet) (merge : Mg R R R)
                    (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                    {sP sQ sR sPQ s : List (Event√ R)}
                  → ParInter A merge sP sQ sPQ → ParInter A merge sPQ sR s
                  → Σ[ sQR ∈ List (Event√ R) ]
                      (ParInter A merge sQ sR sQR × ParInter A merge sP sQR s)
ParInter-assoc-LR A merge ma pnil pnil = [] , pnil , pnil
-- outer sync ⇒ event is cs ⇒ inner must also be a sync (psoloL/R would carry ¬cs)
ParInter-assoc-LR A merge ma (psync {X} {e} {a} csf i) (psync _ o)
  with ParInter-assoc-LR A merge ma i o
... | sQR , jR , jP = evl (evLabel X e a) ∷ sQR , psync csf jR , psync csf jP
ParInter-assoc-LR A merge ma (psoloL ¬csf i) (psync csf o) = ⊥-elim (¬csf csf)
ParInter-assoc-LR A merge ma (psoloR ¬csf i) (psync csf o) = ⊥-elim (¬csf csf)
-- outer solo-from-PQ ⇒ inner says it came from P (psoloL) or Q (psoloR)
ParInter-assoc-LR A merge ma (psoloL ¬csf i) (psoloL _ o)
  with ParInter-assoc-LR A merge ma i o
... | sQR , jR , jP = sQR , jR , psoloL ¬csf jP
ParInter-assoc-LR A merge ma (psoloR {X} {e} {a} ¬csf i) (psoloL _ o)
  with ParInter-assoc-LR A merge ma i o
... | sQR , jR , jP = evl (evLabel X e a) ∷ sQR , psoloL ¬csf jR , psoloR ¬csf jP
ParInter-assoc-LR A merge ma (psync csf i) (psoloL ¬csf o) = ⊥-elim (¬csf csf)
-- outer solo-from-R ⇒ inner untouched
ParInter-assoc-LR A merge ma i (psoloR {X} {e} {a} ¬csf o)
  with ParInter-assoc-LR A merge ma i o
... | sQR , jR , jP = evl (evLabel X e a) ∷ sQR , psoloR ¬csf jR , psoloR ¬csf jP
-- outer joint √ ⇒ inner joint √ ⇒ all three terminate (needs merge-assoc)
ParInter-assoc-LR A merge ma (p√ {r₁ = a} {r₂ = b}) (p√ {r₂ = c}) =
  √ (merge b c) ∷ [] , p√ ,
  subst (λ z → ParInter A merge (√ a ∷ []) (√ (merge b c) ∷ []) (√ z ∷ [])) (sym (ma a b c)) p√

-- right-to-left re-bracketing.
ParInter-assoc-RL : (A : EventSet) (merge : Mg R R R)
                    (massoc : ∀ a b c → merge (merge a b) c ≡ merge a (merge b c))
                    {sP sQ sR sQR s : List (Event√ R)}
                  → ParInter A merge sQ sR sQR → ParInter A merge sP sQR s
                  → Σ[ sPQ ∈ List (Event√ R) ]
                      (ParInter A merge sP sQ sPQ × ParInter A merge sPQ sR s)
ParInter-assoc-RL A merge ma pnil pnil = [] , pnil , pnil
-- outer sync ⇒ inner (Q,R) must be a sync
ParInter-assoc-RL A merge ma (psync {X} {e} {a} csf i) (psync _ o)
  with ParInter-assoc-RL A merge ma i o
... | sPQ , jP , jR = evl (evLabel X e a) ∷ sPQ , psync csf jP , psync csf jR
ParInter-assoc-RL A merge ma (psoloL ¬csf i) (psync csf o) = ⊥-elim (¬csf csf)
ParInter-assoc-RL A merge ma (psoloR ¬csf i) (psync csf o) = ⊥-elim (¬csf csf)
-- outer solo-from-QR ⇒ inner says from Q (psoloL) or R (psoloR)
ParInter-assoc-RL A merge ma (psoloL {X} {e} {a} ¬csf i) (psoloR _ o)
  with ParInter-assoc-RL A merge ma i o
... | sPQ , jP , jR = evl (evLabel X e a) ∷ sPQ , psoloR ¬csf jP , psoloL ¬csf jR
ParInter-assoc-RL A merge ma (psoloR ¬csf i) (psoloR _ o)
  with ParInter-assoc-RL A merge ma i o
... | sPQ , jP , jR = sPQ , jP , psoloR ¬csf jR
ParInter-assoc-RL A merge ma (psync csf i) (psoloR ¬csf o) = ⊥-elim (¬csf csf)
-- outer solo-from-P ⇒ inner (Q,R) untouched
ParInter-assoc-RL A merge ma i (psoloL {X} {e} {a} ¬csf o)
  with ParInter-assoc-RL A merge ma i o
... | sPQ , jP , jR = evl (evLabel X e a) ∷ sPQ , psoloL ¬csf jP , psoloL ¬csf jR
-- outer joint √
ParInter-assoc-RL A merge ma (p√ {r₁ = b} {r₂ = c}) (p√ {r₁ = a}) =
  √ (merge a b) ∷ [] , p√ ,
  subst (λ z → ParInter A merge (√ (merge a b) ∷ []) (√ c ∷ []) (√ z ∷ [])) (ma a b c) p√
