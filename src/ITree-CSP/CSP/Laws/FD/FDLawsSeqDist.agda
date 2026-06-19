{-# OPTIONS --guardedness #-}

-- ⊓-distribution for sequential composition (left operand):
--   (P ⊓ Q) >>= k  ≈FD  (P >>= k) ⊓ (Q >>= k).
--
-- Unlike prefix-distribution, this one is actually a STRONG bisimulation law: the
-- τ-branches of (P ⊓ Q) >>= k are `bindT k (react ∅v (br2 P Q))`, which reduces (via
-- viewT/br2) to exactly the two successors `P >>= k` and `Q >>= k` — the same two
-- successors as (P >>= k) ⊓ (Q >>= k), reached by ⊓-stepL/⊓-stepR.  So the two sides
-- match step-for-step (targets identical, related by reflexivity).  We then lift the
-- strong bisimulation to ≈FD via sbisim→drbisim ∘ drbisim→≈FD.

open import Level using (Level; Lift; lift)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees

module CSP.Laws.FD.FDLawsSeqDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.Bisim               {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.Laws            E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- The two τ-successors of (P ⊓ Q) >>= k, and the inversion that they are the only ones.
-------------------------------------------------------------------------------------

bind⊓-stepL : (P Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
            → ((P ⊓ Q) >>= k) ─[ τ ]─► (P >>= k)
bind⊓-stepL P Q k = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero} refl refl

bind⊓-stepR : (P Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
            → ((P ⊓ Q) >>= k) ─[ τ ]─► (Q >>= k)
bind⊓-stepR P Q k = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

bind⊓-τ-inv : (P Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
              {t : PTree E (ExtI E) S}
            → ((P ⊓ Q) >>= k) ─[ τ ]─► t → (t ≡ (P >>= k)) ⊎ (t ≡ (Q >>= k))
bind⊓-τ-inv P Q k (sSil ())
bind⊓-τ-inv P Q k (sTau {i = _ , base _}   refl ())
bind⊓-τ-inv P Q k (sTau {i = _ , pair _ _} refl ())
bind⊓-τ-inv P Q k (sTau {i = _ , fin} {a = lift fzero}           refl br) = inj₁ (sym (just-injective br))
bind⊓-τ-inv P Q k (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl br) = inj₂ (sym (just-injective br))
bind⊓-τ-inv P Q k (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())

-------------------------------------------------------------------------------------
-- The strong bisimulation, then the ≈FD law.
-------------------------------------------------------------------------------------

bind-⊓-distrib-∼ : (P Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                 → ((P ⊓ Q) >>= k) ∼ ((P >>= k) ⊓ (Q >>= k))
bind-⊓-distrib-∼ P Q k .Sbisim.fwd .SSimF.on-ev (sRet ())
bind-⊓-distrib-∼ P Q k .Sbisim.fwd .SSimF.on-ev (sVis refl ())
bind-⊓-distrib-∼ P Q k .Sbisim.fwd .SSimF.on-tau step with bind⊓-τ-inv P Q k step
... | inj₁ refl = (P >>= k) , ⊓-stepL (P >>= k) (Q >>= k) , sbisim-refl _
... | inj₂ refl = (Q >>= k) , ⊓-stepR (P >>= k) (Q >>= k) , sbisim-refl _
bind-⊓-distrib-∼ P Q k .Sbisim.bwd .SSimF.on-ev (sRet ())
bind-⊓-distrib-∼ P Q k .Sbisim.bwd .SSimF.on-ev (sVis refl ())
bind-⊓-distrib-∼ P Q k .Sbisim.bwd .SSimF.on-tau step with ⊓-τ-inv (P >>= k) (Q >>= k) step
... | inj₁ refl = (P >>= k) , bind⊓-stepL P Q k , sbisim-refl _
... | inj₂ refl = (Q >>= k) , bind⊓-stepR P Q k , sbisim-refl _

bind-⊓-distrib-FD : (P Q : PTree E (ExtI E) R) (k : R → PTree E (ExtI E) S)
                  → ((P ⊓ Q) >>= k) ≈FD ((P >>= k) ⊓ (Q >>= k))
bind-⊓-distrib-FD P Q k = drbisim→≈FD (sbisim→drbisim (bind-⊓-distrib-∼ P Q k))

-- the >> corollary (k a constant continuation)
seq-⊓-distrib-FD : (P Q : PTree E (ExtI E) R) (S′ : PTree E (ExtI E) S)
                 → ((P ⊓ Q) >> S′) ≈FD ((P >> S′) ⊓ (Q >> S′))
seq-⊓-distrib-FD P Q S′ = bind-⊓-distrib-FD P Q (λ _ → S′)
