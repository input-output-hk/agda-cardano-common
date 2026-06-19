{-# OPTIONS --guardedness #-}

-- Interleaving UNIT (T6.16 / U7-style):  SKIP ⦀ P ≈FD P.
--
-- For the interleaving operator `⦀` (= Par with cs = ∅) the terminated left operand
-- `Skip` (= Ret tt) is dead: it offers nothing and can only join the final √.  With cs = ∅
-- nothing is blocked, so `Par Skip P` runs P solo — every P-move is mirrored one-for-one,
-- and the joint √ (merge tt tt = tt) matches P's √.  Hence a STRONG bisimulation
-- `Par Skip P ∼ P`, lifted to ≈FD.  (The right unit `P ⦀ SKIP ≈FD P` follows by ⦀-comm-FD.)
--
-- The dead-left node uses Par's `par-hVisR`/`par-hTauR` maps; with dec ∅ ≡ `no _` these
-- offer exactly P's events into `Par Skip P′`.  The backward direction needs the REVERSED
-- relation, so we define `Par-ret-unit` / `Par-ret-unitR` mutually (as for bind-ret in
-- SeqLaws) — never `sbisim-sym`, which would project the corecursive call and unguard it.

open import Level using (Level)
open import Data.Maybe using (just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ParallelUnit {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Bisim    {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg; Par-τ-R; fPar-re)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using (ParτR; τL; τR; Par-τ-elim; par-hVisR-elim; Par-force-ret-inv; fPar-rr)
open import CSP.Laws.Traces.TraceLawsParallelMono E-≟ using (par-hVisR-eq)
open import CSP.Laws.Bisim.IterCong E-≟ using (ret-no-τ)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr : Level

-- the interleaving instance: empty cs (∅ES), ⊤-merge
tm : ⊤ {ℓr} → ⊤ {ℓr} → ⊤ {ℓr}
tm _ _ = tt

-------------------------------------------------------------------------------------
-- the strong bisimulation `Par Skip P ∼ P`, with its reverse, defined mutually.
-------------------------------------------------------------------------------------
Par-ret-unit  : (P : PTree E (ExtI E) (⊤ {ℓr})) → (Par ∅ES tm Skip P) ∼ P
Par-ret-unitR : (P : PTree E (ExtI E) (⊤ {ℓr})) → P ∼ (Par ∅ES tm Skip P)

-- forward: a move of `Par Skip P` is mirrored by P (the dead Skip never moves).
unit-fwd-ev : (P : PTree E (ExtI E) (⊤ {ℓr})) {l : Event√ (⊤ {ℓr})} {M : PTree E (ExtI E) (⊤ {ℓr})}
            → (Par ∅ES tm Skip P) ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((P ─[ ev l ]─► M′) × (M ∼ M′))
unit-fwd-ev P (sRet eqf) with Par-force-ret-inv ∅ES tm eqf
... | r₁ , r₂ , fpP , fpQ , refl = deadlock , sRet fpQ , sbisim-refl deadlock
unit-fwd-ev P (sVis {v = v} {τc = τc} {at = at} {a = a} {t′ = M} eqf br) with PTree.force P in eqP
... | ret r₂    = case eqf of λ ()
... | sil P′    = case eqf of λ ()
... | react vQ τcQ
      with par-hVisR-elim ∅ES tm Skip {vQ = vQ} {at = at} {a = a}
             (subst (λ g → g at a ≡ just M) (sym (proj₁ (react-injective eqf))) br)
...   | Q′ , ¬cs , vQeq , refl = Q′ , sVis eqP vQeq , Par-ret-unit Q′

unit-fwd-tau : (P : PTree E (ExtI E) (⊤ {ℓr})) {M : PTree E (ExtI E) (⊤ {ℓr})}
             → (Par ∅ES tm Skip P) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((P ─[ τ ]─► M′) × (M ∼ M′))
unit-fwd-tau P step with Par-τ-elim ∅ES tm Skip P step
... | τL P′ Pτ _    = ⊥-elim (ret-no-τ refl Pτ)
... | τR Q′ Qτ refl = Q′ , Qτ , Par-ret-unit Q′

-- backward: a move of P is mirrored by `Par Skip P` (Skip stays put as the dead operand).
unit-bwd-ev : (P : PTree E (ExtI E) (⊤ {ℓr})) {l : Event√ (⊤ {ℓr})} {M : PTree E (ExtI E) (⊤ {ℓr})}
            → P ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((Par ∅ES tm Skip P) ─[ ev l ]─► M′) × (M ∼ M′)
unit-bwd-ev P (sRet eqP) =
  deadlock , sRet (fPar-rr ∅ES tm refl eqP) , sbisim-refl deadlock
unit-bwd-ev P (sVis {v = vQ} {τc = τcQ} {at = at} {a = a} {t′ = M} eqP br) =
  Par ∅ES tm Skip M
  , sVis (fPar-re ∅ES tm refl eqP)
         (par-hVisR-eq ∅ES tm Skip {vQ = vQ} {at = at} {a = a} (λ z → z) br)
  , Par-ret-unitR M

unit-bwd-tau : (P : PTree E (ExtI E) (⊤ {ℓr})) {M : PTree E (ExtI E) (⊤ {ℓr})}
             → P ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) (⊤ {ℓr}) ] ((Par ∅ES tm Skip P) ─[ τ ]─► M′) × (M ∼ M′)
unit-bwd-tau P Pτ =
  Par ∅ES tm Skip _ , Par-τ-R ∅ES tm Skip P Pτ , Par-ret-unitR _

Par-ret-unit  P .Sbisim.fwd .SSimF.on-ev  = unit-fwd-ev  P
Par-ret-unit  P .Sbisim.fwd .SSimF.on-tau = unit-fwd-tau P
Par-ret-unit  P .Sbisim.bwd .SSimF.on-ev  = unit-bwd-ev  P
Par-ret-unit  P .Sbisim.bwd .SSimF.on-tau = unit-bwd-tau P
Par-ret-unitR P .Sbisim.fwd .SSimF.on-ev  = unit-bwd-ev  P
Par-ret-unitR P .Sbisim.fwd .SSimF.on-tau = unit-bwd-tau P
Par-ret-unitR P .Sbisim.bwd .SSimF.on-ev  = unit-fwd-ev  P
Par-ret-unitR P .Sbisim.bwd .SSimF.on-tau = unit-fwd-tau P

-------------------------------------------------------------------------------------
-- ⦀-unit (T6.16):  SKIP ⦀ P ≈FD P
-------------------------------------------------------------------------------------
⦀-unit-FD : (P : PTree E (ExtI E) (⊤ {ℓr})) → (Skip ⦀ P) ≈FD P
⦀-unit-FD P = drbisim→≈FD (sbisim→drbisim (Par-ret-unit P))
