{-# OPTIONS --guardedness #-}

-- □-SKIP-resolve (T6.6, U13.17):  P □ SKIP  ≈FD  P ▷ SKIP.
--
-- In CSP the √ offered by SKIP in an external choice resolves to an INTERNAL timeout.
-- In this spike that holds **as a STRONG bisimulation** and needs NO side-condition —
-- because the two operators' slide-continuations coincide:
--   • `□-slide-PR nP Skip` (the "P live, Q=ret" arm of `□`) and `▷-slide nP Skip` are
--     CLAUSE-FOR-CLAUSE identical (tag0 = a τ to the terminated `Skip`, tag1 = P's own τ
--     sliding on as `· ▷ Skip`), so every successor of `P □ Skip` is the SAME tree as the
--     matching successor of `P ▷ Skip`;
--   • when `force P = ret`, both reduce to that same `ret` (here `ret tt`).
--
-- The law is stated at `R = ⊤`: the GENERAL `P □ Ret r ≈ P ▷ Ret r` FAILS when `force P`
-- is `ret r₀` with `r₀ ≠ r` (then `P □ Ret r = P ⊓ Ret r` but `P ▷ Ret r = Ret r₀`,
-- eager-`ret`); `⊤`'s unique element rules that mismatch out.
--
-- Proof: a generic node-equality strong bisim `node-pw` (same offer map `v`, POINTWISE-equal
-- τ-map `F i a ≡ G i a`, successors discharged by `sbisim-refl`) for the live `force P`
-- cases, and the force-equality bisim `sbisim-force-eq` for the `ret` case.  Lifted to ≈FD
-- via `drbisim→≈FD ∘ sbisim→drbisim`.

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.SlideSkipResolve {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-react; force-▷-sil; force-▷-ret)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (fL-A; fL-E; fL-F)

-- ⊤'s unique element makes equality trivially decidable (needed for `□` at R = ⊤).
private instance
  DecEq-⊤ : ∀ {ℓr} → DecEq (⊤ {ℓr})
  DecEq-⊤ = record { _≟_ = λ _ _ → yes refl }

-------------------------------------------------------------------------------------
-- Generic node-equality strong bisimulation.
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr} where

  -- force-equal trees are strongly bisimilar (re-targeting each outgoing step).
  retarget : {a b : PTree E (ExtI E) R} {l : Label R} {M : PTree E (ExtI E) R}
           → PTree.force a ≡ PTree.force b → a ─[ l ]─► M → b ─[ l ]─► M
  retarget eq (sRet fe)    = sRet (trans (sym eq) fe)
  retarget eq (sSil fe)    = sSil (trans (sym eq) fe)
  retarget eq (sVis fe br) = sVis (trans (sym eq) fe) br
  retarget eq (sTau fe br) = sTau (trans (sym eq) fe) br

  sbisim-force-eq : {t u : PTree E (ExtI E) R} → PTree.force t ≡ PTree.force u → t ∼ u
  sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev  step = _ , retarget eq        step , sbisim-refl _
  sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau step = _ , retarget eq        step , sbisim-refl _
  sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev  step = _ , retarget (sym eq)  step , sbisim-refl _
  sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau step = _ , retarget (sym eq)  step , sbisim-refl _

  -- two react nodes with the SAME offer map `v` and POINTWISE-equal τ-maps are bisimilar;
  -- every matched successor is literally the same tree (⇒ sbisim-refl).
  node-sim : (t₁ t₂ : PTree E (ExtI E) R)
             (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
             (F G : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
           → PTree.force t₁ ≡ react v F → PTree.force t₂ ≡ react v G
           → (∀ i a → F i a ≡ G i a)
           → SSimF (Sbisim R) t₁ t₂
  node-sim t₁ t₂ v F G ft₁ ft₂ pw .SSimF.on-ev (sRet eqr) =
    ⊥-elim (case trans (sym ft₁) eqr of λ ())
  node-sim t₁ t₂ v F G ft₁ ft₂ pw .SSimF.on-ev (sVis {at = at} {a = a} eqf br) =
    _ , sVis ft₂ (subst (λ f → f at a ≡ just _)
                        (sym (proj₁ (react-injective (trans (sym ft₁) eqf)))) br)
      , sbisim-refl _
  node-sim t₁ t₂ v F G ft₁ ft₂ pw .SSimF.on-tau (sSil eqs) =
    ⊥-elim (case trans (sym ft₁) eqs of λ ())
  node-sim t₁ t₂ v F G ft₁ ft₂ pw .SSimF.on-tau (sTau {i = i} {a = a} eqf br) =
    _ , sTau ft₂ (trans (sym (pw i a))
                        (subst (λ f → f i a ≡ just _)
                               (sym (proj₂ (react-injective (trans (sym ft₁) eqf)))) br))
      , sbisim-refl _

  node-pw : (t₁ t₂ : PTree E (ExtI E) R)
            (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
            (F G : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
          → PTree.force t₁ ≡ react v F → PTree.force t₂ ≡ react v G
          → (∀ i a → F i a ≡ G i a)
          → t₁ ∼ t₂
  node-pw t₁ t₂ v F G ft₁ ft₂ pw .Sbisim.fwd = node-sim t₁ t₂ v F G ft₁ ft₂ pw
  node-pw t₁ t₂ v F G ft₁ ft₂ pw .Sbisim.bwd = node-sim t₂ t₁ v G F ft₂ ft₁ (λ i a → sym (pw i a))

-------------------------------------------------------------------------------------
-- □-slide-PR nP Skip  and  ▷-slide nP Skip  agree pointwise (identical clauses).
-------------------------------------------------------------------------------------

module _ {ℓr} where

  slide-pw : (nP : NodeKind E (ExtI E) (⊤ {ℓr}))
           → ∀ i a → □-slide-PR nP (Skip {ℓr}) i a ≡ ▷-slide nP (Skip {ℓr}) i a
  slide-pw nP (_ , base _)            _ = refl
  slide-pw nP (_ , fin)               _ = refl
  slide-pw nP (_ , pair (base _) _)   _ = refl
  slide-pw nP (_ , pair (pair _ _) _) _ = refl
  slide-pw nP (_ , pair fin i) (lift fzero , a)               = refl
  slide-pw nP (_ , pair fin i) (lift (fsuc fzero) , a) with viewT nP (_ , i) a
  ... | just P' = refl
  ... | nothing = refl
  slide-pw nP (_ , pair fin i) (lift (fsuc (fsuc _)) , a)     = refl

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr} where

  -- P □ SKIP  ∼  P ▷ SKIP   (strong bisimulation, no side-condition)
  □-SKIP-resolve : (P : PTree E (ExtI E) (⊤ {ℓr})) → (P □ Skip) ∼ (P ▷ Skip)
  □-SKIP-resolve P with PTree.force P in eqP
  ... | ret r     = sbisim-force-eq (trans (fL-A {P = P} {Q = Skip} {r = r} eqP refl)
                                           (sym (force-▷-ret {P = P} {Q = Skip} eqP)))
  ... | sil P'    = node-pw (P □ Skip) (P ▷ Skip) ∅v
                            (□-slide-PR (sil P') Skip) (▷-slide (sil P') Skip)
                            (fL-E {P = P} {Q = Skip} eqP refl)
                            (force-▷-sil {P = P} {Q = Skip} eqP)
                            (slide-pw (sil P'))
  ... | react vP τcP = node-pw (P □ Skip) (P ▷ Skip) vP
                            (□-slide-PR (react vP τcP) Skip) (▷-slide (react vP τcP) Skip)
                            (fL-F {P = P} {Q = Skip} eqP refl)
                            (force-▷-react {P = P} {Q = Skip} eqP)
                            (slide-pw (react vP τcP))

  -- lifted to ≈FD
  □-SKIP-resolve-FD : (P : PTree E (ExtI E) (⊤ {ℓr})) → (P □ Skip) ≈FD (P ▷ Skip)
  □-SKIP-resolve-FD P = drbisim→≈FD (sbisim→drbisim (□-SKIP-resolve P))
