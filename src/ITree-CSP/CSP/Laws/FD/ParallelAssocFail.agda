{-# OPTIONS --guardedness #-}

-- Failures half of parallel associativity — FOUNDATIONS: force/stability inversions and
-- the stability reassociation isStable(Par(Par P Q)R) ↔ isStable(Par P(Par Q R)).
-- (Homogeneous R; for Par⊤/⦀ merge = ⊤'s.)  The leaf of a stable parallel composite is
-- classified (both-stable / left-terminated / right-terminated); reassociation re-pairs
-- the residuals accordingly via Par-stable / Par-stable-termL/R.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.ParallelAssocFail {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (deadlock-no-τ)
open import CSP.Laws.Traces.TraceLawsParallel E-≟
  using (Mg; Par-τ-L; Par-τ-R; Par-sync)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (fPar-rr; Par-ev-elim; ParevR; ev√)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟
  using (Par-soloL-reach; Par-soloR-reach)
open import CSP.Laws.FD.ParallelRefusals E-≟
  using (stable→react; stable-not-ret; mk-stable; Par-stable; Par-stable-termL; Par-stable-termR)
-- generic stability facts (`react-no-τ→stable` below is a thin alias)
import Semantics.Stability {E = E} {I = ExtI E} as S

private
  variable
    ℓr : Level
    R  : Set ℓr

-- a stable state has no τ-move (local copy).
stable-no-τ : {t M : PTree E (ExtI E) R} → isStable t → t ─[ τ ]─► M → ⊥
stable-no-τ {t = t} st (sSil eq)             with PTree.force t | st
... | sil _ | lift ()
stable-no-τ {t = t} st (sTau {i = i} {a = a} eq br) with PTree.force t | st | eq
... | react _ τc | st′ | refl = case trans (sym (st′ i a)) br of λ ()

-- force(Par P Q) ≡ ret r ⇒ both operands terminated.  A ret-forced Par emits √ (sRet);
-- Par-ev-elim on that √-step forces the ev√ case (both operands ret), via event unification.
Par-force-ret-inv : (A : EventSet) (merge : Mg R R R)
                    {P Q : PTree E (ExtI E) R} {r : R}
                  → PTree.force (Par A merge P Q) ≡ ret r
                  → Σ[ rp ∈ R ] Σ[ rq ∈ R ]
                      (PTree.force P ≡ ret rp × PTree.force Q ≡ ret rq × r ≡ merge rp rq)
Par-force-ret-inv A merge {P} {Q} eq with Par-ev-elim A merge P Q (sRet eq)
... | ev√ {r₁ = r₁} {r₂ = r₂} fpP fpQ = r₁ , r₂ , fpP , fpQ , refl

-- an react state with no enabled τ is stable (an alias for the generic
-- `Semantics.Stability.react-no-τ→stable`).
react-no-τ→stable : {t : PTree E (ExtI E) R}
                   {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                 → PTree.force t ≡ react v τc → (∀ {t'} → t ─[ τ ]─► t' → ⊥) → isStable t
react-no-τ→stable {t = t} = S.react-no-τ→stable {t = t}

-- the stable-leaf classification of a parallel composite.
data StableClass {ℓr} {R : Set ℓr} (A B : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) where
  bothS : isStable A → isStable B → StableClass A B
  termL : (Σ[ r ∈ R ] PTree.force A ≡ ret r) → isStable B → StableClass A B
  termR : isStable A → (Σ[ r ∈ R ] PTree.force B ≡ ret r) → StableClass A B

-- top-level go-helper: case the EXPLICIT NodeKind parameters nA, nB (so stPar's type
-- isn't abstracted by a `with PTree.force A`); the force-eqs eqA, eqB relate them back.
psc-go : (A : EventSet) (merge : Mg R R R)
         (S T : PTree E (ExtI E) R) → isStable (Par A merge S T)
       → (nA nB : NodeKind E (ExtI E) R)
       → PTree.force S ≡ nA → PTree.force T ≡ nB → StableClass S T
psc-go A merge S T stPar nA nB eqA eqB with nA | nB
... | ret rA | ret rB = ⊥-elim (stable-not-ret {t = Par A merge S T} (fPar-rr A merge eqA eqB) stPar)
... | ret rA | sil B' = ⊥-elim (stable-no-τ stPar (Par-τ-R A merge S T (sSil eqB)))
... | ret rA | react vB τcB =
        termL (rA , eqA) (react-no-τ→stable eqB (λ Bτ → stable-no-τ stPar (Par-τ-R A merge S T Bτ)))
... | sil A' | nB' = ⊥-elim (stable-no-τ stPar (Par-τ-L A merge S T (sSil eqA)))
... | react vA τcA | ret rB =
        termR (react-no-τ→stable eqA (λ Aτ → stable-no-τ stPar (Par-τ-L A merge S T Aτ))) (rB , eqB)
... | react vA τcA | sil B' = ⊥-elim (stable-no-τ stPar (Par-τ-R A merge S T (sSil eqB)))
... | react vA τcA | react vB τcB =
        bothS (react-no-τ→stable eqA (λ Aτ → stable-no-τ stPar (Par-τ-L A merge S T Aτ)))
              (react-no-τ→stable eqB (λ Bτ → stable-no-τ stPar (Par-τ-R A merge S T Bτ)))

Par-stable-classify : (A : EventSet) (merge : Mg R R R)
                      (S T : PTree E (ExtI E) R)
                    → isStable (Par A merge S T) → StableClass S T
Par-stable-classify A merge S T stPar =
  psc-go A merge S T stPar (PTree.force S) (PTree.force T) refl refl

-- stability reassociation, left-to-right.
Par-stable-assoc-LR : (A : EventSet) (merge : Mg R R R)
                      (P Q R₀ : PTree E (ExtI E) R)
                    → isStable (Par A merge (Par A merge P Q) R₀)
                    → isStable (Par A merge P (Par A merge Q R₀))
Par-stable-assoc-LR A merge P Q R₀ stO with Par-stable-classify A merge (Par A merge P Q) R₀ stO
... | bothS stPQ stR with Par-stable-classify A merge P Q stPQ
...   | bothS stP stQ =
        Par-stable A merge P (Par A merge Q R₀) stP (Par-stable A merge Q R₀ stQ stR)
...   | termL (rP , eqP) stQ =
        Par-stable-termL A merge P (Par A merge Q R₀) eqP (Par-stable A merge Q R₀ stQ stR)
...   | termR stP (rQ , eqQ) =
        Par-stable A merge P (Par A merge Q R₀) stP (Par-stable-termL A merge Q R₀ eqQ stR)
Par-stable-assoc-LR A merge P Q R₀ stO | termL (rPQ , eqPQ) stR with Par-force-ret-inv A merge eqPQ
...   | rP , rQ , eqP , eqQ , _ =
        Par-stable-termL A merge P (Par A merge Q R₀) eqP (Par-stable-termL A merge Q R₀ eqQ stR)
Par-stable-assoc-LR A merge P Q R₀ stO | termR stPQ (rR , eqR) with Par-stable-classify A merge P Q stPQ
...   | bothS stP stQ =
        Par-stable A merge P (Par A merge Q R₀) stP (Par-stable-termR A merge Q R₀ stQ eqR)
...   | termL (rP , eqP) stQ =
        Par-stable-termL A merge P (Par A merge Q R₀) eqP (Par-stable-termR A merge Q R₀ stQ eqR)
...   | termR stP (rQ , eqQ) =
        Par-stable-termR A merge P (Par A merge Q R₀) stP (fPar-rr A merge eqQ eqR)

-- stability reassociation, right-to-left.
Par-stable-assoc-RL : (A : EventSet) (merge : Mg R R R)
                      (P Q R₀ : PTree E (ExtI E) R)
                    → isStable (Par A merge P (Par A merge Q R₀))
                    → isStable (Par A merge (Par A merge P Q) R₀)
Par-stable-assoc-RL A merge P Q R₀ stO with Par-stable-classify A merge P (Par A merge Q R₀) stO
... | bothS stP stQR with Par-stable-classify A merge Q R₀ stQR
...   | bothS stQ stR =
        Par-stable A merge (Par A merge P Q) R₀ (Par-stable A merge P Q stP stQ) stR
...   | termL (rQ , eqQ) stR =
        Par-stable A merge (Par A merge P Q) R₀ (Par-stable-termR A merge P Q stP eqQ) stR
...   | termR stQ (rR , eqR) =
        Par-stable-termR A merge (Par A merge P Q) R₀ (Par-stable A merge P Q stP stQ) eqR
Par-stable-assoc-RL A merge P Q R₀ stO | termL (rP , eqP) stQR with Par-stable-classify A merge Q R₀ stQR
...   | bothS stQ stR =
        Par-stable A merge (Par A merge P Q) R₀ (Par-stable-termL A merge P Q eqP stQ) stR
...   | termL (rQ , eqQ) stR =
        -- P,Q both ret ⇒ Par P Q force ret ⇒ half-term-L at the outer level
        Par-stable-termL A merge (Par A merge P Q) R₀ (fPar-rr A merge eqP eqQ) stR
...   | termR stQ (rR , eqR) =
        Par-stable-termR A merge (Par A merge P Q) R₀ (Par-stable-termL A merge P Q eqP stQ) eqR
Par-stable-assoc-RL A merge P Q R₀ stO | termR stP (rQR , eqQR) with Par-force-ret-inv A merge eqQR
...   | rQ , rR , eqQ , eqR , _ =
        Par-stable-termR A merge (Par A merge P Q) R₀ (Par-stable-termR A merge P Q stP eqQ) eqR

-------------------------------------------------------------------------------------
-- Par-trace-reach : re-interleave the operand reaches per a ParInter into an EXPLICIT
-- composite reach.  Mirrors Par-trace-intro but fixes the codomain: the no-√ spine
-- reaches `Par Q* R*`; the joint-√ (p√) tail reaches `deadlock` and ALSO exposes that the
-- operand residuals are deadlock (Q* ≡ deadlock, R* ≡ deadlock) — the eqs let the caller
-- transport stability/refusals built for `Par Q* R*` onto the actual `deadlock` codomain.
-- (Analogue of ParallelAssocDiv.Par-div-reach, which instead refuted p√ via a divergence.)
-------------------------------------------------------------------------------------
Par-trace-reach : (A : EventSet) (merge : Mg R R R)
                  (Q R₀ : PTree E (ExtI E) R)
                  {Q* R* : PTree E (ExtI E) R} {sQ sR sQR : List (Event√ R)}
                → Q ⟹⟨ sQ ⟩ Q* → R₀ ⟹⟨ sR ⟩ R* → ParInter A merge sQ sR sQR
                → ((Par A merge Q R₀) ⟹⟨ sQR ⟩ (Par A merge Q* R*))
                ⊎ (((Par A merge Q R₀) ⟹⟨ sQR ⟩ deadlock)
                     × (Q* ≡ deadlock) × (R* ≡ deadlock))
Par-trace-reach A merge Q R₀ (⟹-τ Qτ restQ) Rbs PI =
  case Par-trace-reach A merge _ R₀ restQ Rbs PI of λ where
    (inj₁ r)              → inj₁ (⟹-τ (Par-τ-L A merge Q R₀ Qτ) r)
    (inj₂ (r , eQ , eR))  → inj₂ (⟹-τ (Par-τ-L A merge Q R₀ Qτ) r , eQ , eR)
Par-trace-reach A merge Q R₀ Qbs (⟹-τ Rτ restR) PI =
  case Par-trace-reach A merge Q _ Qbs restR PI of λ where
    (inj₁ r)              → inj₁ (⟹-τ (Par-τ-R A merge Q R₀ Rτ) r)
    (inj₂ (r , eQ , eR))  → inj₂ (⟹-τ (Par-τ-R A merge Q R₀ Rτ) r , eQ , eR)
Par-trace-reach A merge Q R₀ ⟹-refl ⟹-refl pnil = inj₁ ⟹-refl
Par-trace-reach A merge Q R₀ (⟹-ev Qev restQ) (⟹-ev Rev restR) (psync csat PI) =
  case Par-trace-reach A merge _ _ restQ restR PI of λ where
    (inj₁ r)              → inj₁ (⟹-ev (Par-sync A merge Q R₀ csat Qev Rev) r)
    (inj₂ (r , eQ , eR))  → inj₂ (⟹-ev (Par-sync A merge Q R₀ csat Qev Rev) r , eQ , eR)
Par-trace-reach A merge Q R₀ (⟹-ev Qev restQ) Rbs (psoloL ¬cs PI) =
  case Par-trace-reach A merge _ R₀ restQ Rbs PI of λ where
    (inj₁ r)              → inj₁ (Par-soloL-reach A merge Q R₀ ¬cs Qev r)
    (inj₂ (r , eQ , eR))  → inj₂ (Par-soloL-reach A merge Q R₀ ¬cs Qev r , eQ , eR)
Par-trace-reach A merge Q R₀ Qbs (⟹-ev Rev restR) (psoloR ¬cs PI) =
  case Par-trace-reach A merge Q _ Qbs restR PI of λ where
    (inj₁ r)              → inj₁ (Par-soloR-reach A merge Q R₀ ¬cs Rev r)
    (inj₂ (r , eQ , eR))  → inj₂ (Par-soloR-reach A merge Q R₀ ¬cs Rev r , eQ , eR)
Par-trace-reach A merge Q R₀ (⟹-ev (sRet eqQr) ⟹-refl) (⟹-ev (sRet eqRr) ⟹-refl) p√ =
  inj₂ (⟹-ev (sRet (fPar-rr A merge eqQr eqRr)) ⟹-refl , refl , refl)
-- after a √ the operand is `deadlock`, which has no τ ⇒ the empty-trace tails can only be
-- ⟹-refl; the ⟹-τ tails are vacuous.
Par-trace-reach A merge Q R₀ (⟹-ev (sRet eqQr) (⟹-τ step _)) _ p√ =
  ⊥-elim (deadlock-no-τ step)
Par-trace-reach A merge Q R₀ (⟹-ev (sRet eqQr) ⟹-refl) (⟹-ev (sRet eqRr) (⟹-τ step _)) p√ =
  ⊥-elim (deadlock-no-τ step)
