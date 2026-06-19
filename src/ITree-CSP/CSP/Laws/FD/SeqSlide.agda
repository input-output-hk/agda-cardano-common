{-# OPTIONS --guardedness #-}

-- seq-slide / ;-slide (U13.8):  ((e ⟶ P) ▷ P′) ; Q  ≈FD  (e ⟶ (λ x → P x ; Q)) ▷ (P′ ; Q)
--
-- In the spike `;` is `_>>_` (a constant-continuation bind), so the Roscoe side-condition
-- `x ∉ fv(Q)` is automatic — Q is a fixed tree, not a binder.  The law holds as a STRONG
-- bisimulation and needs NO DecEq:
--   • The visible parts agree: both nodes carry a single-channel prefix offer on `e`; the
--     bind pushes `; Q` under the prefix continuation `P x`, which is exactly what the
--     prefix on the RHS already supplies (`λ x → P x ; Q`).
--   • The τ parts agree: the LHS slide-tag `fzero` timeout to `P′` gets `; Q`'d to `P′ ; Q`,
--     matching the RHS timeout to `P′ ; Q`; P's own τ-tag and all other ExtI indices give
--     `nothing` on both sides (the prefix node has an empty τ-map ∅t).
-- The matched successors are LITERALLY the same trees (`P x >> Q`, `P′ >> Q`), so each is
-- discharged by `sbisim-refl`.  Lifted to ≈FD via `drbisim→≈FD ∘ sbisim→drbisim`.

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.FD.SeqSlide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-react)
open import CSP.Laws.Traces.TraceLawsBind E-≟ using (fBind-react)

-------------------------------------------------------------------------------------
-- Generic node-equality strong bisimulation, generalised so the VISIBLE map need
-- only be POINTWISE-equal (mirrors how `node-sim` already transports the τ map).
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

  -- two react nodes whose offer maps and τ-maps are each POINTWISE-equal are bisimilar;
  -- every matched successor is literally the same tree (⇒ sbisim-refl).
  node-sim2 : (t₁ t₂ : PTree E (ExtI E) R)
              (Fv Gv : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
              (F G  : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
            → PTree.force t₁ ≡ react Fv F → PTree.force t₂ ≡ react Gv G
            → (∀ at a → Fv at a ≡ Gv at a)
            → (∀ i a  → F  i a ≡ G  i a)
            → SSimF (Sbisim R) t₁ t₂
  node-sim2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .SSimF.on-ev (sRet eqr) =
    ⊥-elim (case trans (sym ft₁) eqr of λ ())
  node-sim2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .SSimF.on-ev (sVis {at = at} {a = a} eqf br) =
    _ , sVis ft₂ (trans (sym (pwv at a))
                        (subst (λ f → f at a ≡ just _)
                               (sym (proj₁ (react-injective (trans (sym ft₁) eqf)))) br))
      , sbisim-refl _
  node-sim2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .SSimF.on-tau (sSil eqs) =
    ⊥-elim (case trans (sym ft₁) eqs of λ ())
  node-sim2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .SSimF.on-tau (sTau {i = i} {a = a} eqf br) =
    _ , sTau ft₂ (trans (sym (pw i a))
                        (subst (λ f → f i a ≡ just _)
                               (sym (proj₂ (react-injective (trans (sym ft₁) eqf)))) br))
      , sbisim-refl _

  node-pw2 : (t₁ t₂ : PTree E (ExtI E) R)
             (Fv Gv : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
             (F G  : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
           → PTree.force t₁ ≡ react Fv F → PTree.force t₂ ≡ react Gv G
           → (∀ at a → Fv at a ≡ Gv at a)
           → (∀ i a  → F  i a ≡ G  i a)
           → t₁ ∼ t₂
  node-pw2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .Sbisim.fwd =
    node-sim2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw
  node-pw2 t₁ t₂ Fv Gv F G ft₁ ft₂ pwv pw .Sbisim.bwd =
    node-sim2 t₂ t₁ Gv Fv G F ft₂ ft₁ (λ at a → sym (pwv at a)) (λ i a → sym (pw i a))

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} {A : Set ℓ}
         (e : E A) (P : A → PTree E (ExtI E) R)
         (P′ : PTree E (ExtI E) R) (Q : PTree E (ExtI E) S) where

  private
    K : R → PTree E (ExtI E) S
    K = λ _ → Q

    S₀ : PTree E (ExtI E) R
    S₀ = (e ⟶ P) ▷ P′

    -- force (e ⟶ P) ≡ react (Prefix-cont e P) ∅t   (definitional)
    force-eP : PTree.force (e ⟶ P) ≡ react (Prefix-cont e P) ∅t
    force-eP = refl

    -- force S₀ ≡ react v_e (▷-slide (react v_e ∅t) P′)
    nS : NodeKind E (ExtI E) R
    nS = react (Prefix-cont e P) (▷-slide (react (Prefix-cont e P) ∅t) P′)

    force-S₀ : PTree.force S₀ ≡ nS
    force-S₀ = force-▷-react {P = e ⟶ P} {Q = P′} force-eP

    -- LHS forces to a bind react node.
    force-LHS : PTree.force (S₀ >> Q) ≡ react (bindV K nS) (bindT K nS)
    force-LHS = fBind-react K S₀ force-S₀

    -- RHS forces to a slide react node over the pushed prefix.
    force-RHS : PTree.force ((e ⟶ (λ x → P x >> Q)) ▷ (P′ >> Q))
              ≡ react (Prefix-cont e (λ x → P x >> Q))
                      (▷-slide (react (Prefix-cont e (λ x → P x >> Q)) ∅t) (P′ >> Q))
    force-RHS = force-▷-react {P = e ⟶ (λ x → P x >> Q)} {Q = P′ >> Q} refl

    -- VISIBLE pointwise:  bindV K nS at a ≡ Prefix-cont e (λ x → P x >> Q) at a
    vis-pw : ∀ at a → bindV K nS at a ≡ Prefix-cont e (λ x → P x >> Q) at a
    vis-pw at a with E-≟ (A , e) at
    ... | yes refl = refl
    ... | no  _    = refl

    -- τ pointwise:  bindT K nS i a ≡ ▷-slide (react (Prefix-cont e (λx→P x>>Q)) ∅t) (P′>>Q) i a
    tau-pw : ∀ i a
           → bindT K nS i a
           ≡ ▷-slide (react (Prefix-cont e (λ x → P x >> Q)) ∅t) (P′ >> Q) i a
    tau-pw (_ , base _)            _ = refl
    tau-pw (_ , fin)               _ = refl
    tau-pw (_ , pair (base _) _)   _ = refl
    tau-pw (_ , pair (pair _ _) _) _ = refl
    tau-pw (_ , pair fin i) (lift fzero        , a) = refl
    tau-pw (_ , pair fin i) (lift (fsuc fzero) , a) = refl
    tau-pw (_ , pair fin i) (lift (fsuc (fsuc _)) , a) = refl

  seq-slide-∼ : (S₀ >> Q) ∼ ((e ⟶ (λ x → P x >> Q)) ▷ (P′ >> Q))
  seq-slide-∼ =
    node-pw2 (S₀ >> Q) ((e ⟶ (λ x → P x >> Q)) ▷ (P′ >> Q))
             (bindV K nS) (Prefix-cont e (λ x → P x >> Q))
             (bindT K nS) (▷-slide (react (Prefix-cont e (λ x → P x >> Q)) ∅t) (P′ >> Q))
             force-LHS force-RHS vis-pw tau-pw

  seq-slide-FD : (((e ⟶ P) ▷ P′) >> Q) ≈FD ((e ⟶ (λ x → P x >> Q)) ▷ (P′ >> Q))
  seq-slide-FD = drbisim→≈FD (sbisim→drbisim seq-slide-∼)
