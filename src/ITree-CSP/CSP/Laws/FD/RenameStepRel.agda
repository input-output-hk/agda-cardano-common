{-# OPTIONS --guardedness #-}

-- rename-step relational (T3.15, fan-in form):
--
--   (pchoice v) ⟦ R ¿ preimg ⟧  ≈FD  pchoice (renMenuG R preimg v)
--
-- For the GENERAL relational renaming `_⟦ R ¿ preimg ⟧` (same-alphabet instantiation
-- E₁ = E₂ = E) a target event `y` may have SEVERAL enabled source preimages, so the
-- renamed offer is the fan-in internal choice over those sources.  The "spec" menu
-- `renMenuG` offers, at each target, the `⨅⁺`-fold of the renamed enabled sources —
-- equal to the operator's internal `rnFan ∘ rnCollect` only up to ≈FD (the fan-in
-- node and the binary-⊓ fold reach the same stable states / divergences, via the
-- keystone bridge `fanNode-⨅⁺-FD`).
--
-- Two steps, chained by ≈FD-trans:
--   (i)  (pchoice v) ⟦ R ¿ preimg ⟧  ≈FD  pchoice (λ bt b → rnFan … (rnCollect v …))
--        — a STRONG bisimulation (force-equal up to pointwise τ), lifted to ≈FD.
--   (ii) pchoice (λ bt b → rnFan … (rnCollect v …))  ≈FD  pchoice (renMenuG R preimg v)
--        — `pchoice-cong-FD` applied pointwise via `rnFan-list-FD`.

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.RenameStepRel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (pchoice; ⨅⁺; ∅t)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (_⟦_¿_⟧; ConcEvent₁; ConcEvent₂; rnCollect; rnFan; extBranch; extBwd)
open import CSP.Laws.Traces.TraceLawsRenameGen {E = E} using (fanNode)
open import CSP.Laws.FD.RenameFanIn E-≟ using (fanNode-⨅⁺-FD)
open import CSP.Laws.FD.SeqSlide   E-≟ using (node-pw2)
open import CSP.Laws.FD.SlideCombine E-≟
  using (pchoice-ev; pchoice-stable; pchoice-ev-inv; pchoice-failures→; pchoice-div→)
open import CSP.Laws.FD.ExtChoiceFD E-≟ using (fail-ev-prepend; div-ev-prepend)
open import Semantics.LTS {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E} using (_∼_)
open import Semantics.Failures {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (failures⊥; divergences; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_;
         ≈FD-refl; ≈FD-sym; ≈FD-setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr ℓR : Level
    R-set : Set ℓr
    R : ConcEvent₁ → ConcEvent₂ → Set ℓR
    preimg : (bt : AnyTypes E) (b : proj₁ bt)
           → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b))

-------------------------------------------------------------------------------------
-- MaybeFD : FD-equivalence lifted to `Maybe` continuations (a menu cell).
-------------------------------------------------------------------------------------

MaybeFD : ∀ {ℓr} {R-set : Set ℓr}
        → Maybe (PTree E (ExtI E) R-set) → Maybe (PTree E (ExtI E) R-set)
        → Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr)
MaybeFD {ℓr = ℓr} nothing   nothing   = Lift (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) ⊤
MaybeFD          (just M₁) (just M₂)  = M₁ ≈FD M₂
MaybeFD {ℓr = ℓr} (just _)  nothing   = Lift (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) ⊥
MaybeFD {ℓr = ℓr} nothing   (just _)  = Lift (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr) ⊥
-- note: for I = ExtI E the index level ℓi = ℓe, so ≈FD : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓr).

MaybeFD-sym : {x y : Maybe (PTree E (ExtI E) R-set)} → MaybeFD x y → MaybeFD y x
MaybeFD-sym {x = nothing} {y = nothing} _ = lift tt
MaybeFD-sym {x = just M₁} {y = just M₂} p = ≈FD-sym p
MaybeFD-sym {x = just _}  {y = nothing} p = ⊥-elim (lower p)
MaybeFD-sym {x = nothing} {y = just _}  p = ⊥-elim (lower p)

-------------------------------------------------------------------------------------
-- pchoice congruence for ≈FD (reusable).  Two stable visible-offer nodes whose menus
-- are pointwise MaybeFD-related are FD-equivalent: refusals transfer (offered events
-- coincide because a `nothing` cell on one side would be `Lift ⊥` against a `just` on
-- the other), and each event-peeled failure/divergence transfers through the
-- corresponding cells' ≈FD.  Built FD-direct over `pchoice`'s decomposition.
-------------------------------------------------------------------------------------

module _ {ℓr} {R-set : Set ℓr} where

  private
    Menu : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
    Menu = (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set))

  -- a `just` cell on side a paired with `nothing` on side b is contradictory
  cell-just-nothing : (va vb : Menu) → (∀ at a → MaybeFD (va at a) (vb at a))
                    → ∀ at a {W} → va at a ≡ just W → vb at a ≡ nothing → ⊥
  cell-just-nothing va vb pw at a {W} eqA eqB =
    lower (subst (MaybeFD (just W)) eqB (subst (λ m → MaybeFD m (vb at a)) eqA (pw at a)))

  -- a `just` cell on side a yields a `just` cell on side b with an FD-equivalence
  cell-just→ : (va vb : Menu) → (∀ at a → MaybeFD (va at a) (vb at a))
             → ∀ at a {W} → va at a ≡ just W
             → Σ[ W′ ∈ PTree E (ExtI E) R-set ] (vb at a ≡ just W′ × W ≈FD W′)
  cell-just→ va vb pw at a {W} eqA with vb at a in eqB
  ... | just W′ = W′ , refl ,
                    subst (λ m → MaybeFD m (just W′)) eqA
                      (subst (MaybeFD (va at a)) eqB (pw at a))
  ... | nothing = ⊥-elim (cell-just-nothing va vb pw at a eqA eqB)

  -- transfer a refusal across pointwise-MaybeFD menus (one direction):
  -- any event pchoice va offers, pchoice vb also offers, so vb's refusal forces va's.
  pchoice-refuses-cong :
      (va vb : Menu) → (∀ at a → MaybeFD (va at a) (vb at a))
    → {ℓx : Level} {X : Event√ R-set → Set ℓx}
    → Refuses (pchoice vb) X → Refuses (pchoice va) X
  pchoice-refuses-cong va vb pw {X = X} (_ , noffB) =
    pchoice-stable va , noffA
    where
      noffA : ∀ e → X e → ¬ Offers (pchoice va) e
      noffA e xe (W , step) with pchoice-ev-inv va step
      ... | at , a , refl , brA with cell-just→ va vb pw at a brA
      ...   | W′ , brB , _ = noffB _ xe (W′ , pchoice-ev vb brB)

  -- prepend an offered event to a failures⊥ of the cell continuation
  prepend-ev⊥ : (va : Menu) {at : AnyTypes E} {a : proj₁ at}
                {M : PTree E (ExtI E) R-set} {t : List (Event√ R-set)}
                {B : Event√ R-set → Set ℓr}
              → va at a ≡ just M → failures⊥ M t B
              → failures⊥ (pchoice va) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ t) B
  prepend-ev⊥ va brA (inj₁ f) = inj₁ (fail-ev-prepend (pchoice-ev va brA) f)
  prepend-ev⊥ va brA (inj₂ d) = inj₂ (div-ev-prepend (pchoice-ev va brA) d)

  -- one ⊑F⊥ direction: pchoice va ⊑F⊥ pchoice vb
  pchoice-⊑F⊥-dir : (va vb : Menu) → (∀ at a → MaybeFD (va at a) (vb at a))
                  → pchoice va ⊑F⊥ pchoice vb
  pchoice-⊑F⊥-dir va vb pw (inj₁ f) with pchoice-failures→ vb f
  ... | inj₁ (refl , refB) =
          inj₁ (pchoice va , ⟹-refl , pchoice-refuses-cong va vb pw refB)
  ... | inj₂ (at , a , M₂ , t , brB , refl , fM₂)
          with cell-just→ vb va (λ x y → MaybeFD-sym (pw x y)) at a brB
  ...     | M₁ , brA , m21 =
            -- m21 : M₂ ≈FD M₁ ; we need M₁ ⊑F⊥ M₂ = proj₁ (proj₂ m21)
            prepend-ev⊥ va brA (proj₁ (proj₂ m21) (inj₁ fM₂))
  pchoice-⊑F⊥-dir va vb pw (inj₂ d) with pchoice-div→ vb d
  ... | at , a , M₂ , t , brB , refl , dM₂
          with cell-just→ vb va (λ x y → MaybeFD-sym (pw x y)) at a brB
  ...     | M₁ , brA , m21 =
            prepend-ev⊥ va brA (proj₁ (proj₂ m21) (inj₂ dM₂))

  -- one ⊑D direction: pchoice va ⊑D pchoice vb
  pchoice-⊑D-dir : (va vb : Menu) → (∀ at a → MaybeFD (va at a) (vb at a))
                 → pchoice va ⊑D pchoice vb
  pchoice-⊑D-dir va vb pw d with pchoice-div→ vb d
  ... | at , a , M₂ , t , brB , refl , dM₂
          with cell-just→ vb va (λ x y → MaybeFD-sym (pw x y)) at a brB
  ...     | M₁ , brA , m21 =
            -- m21 : M₂ ≈FD M₁ ; we need M₁ ⊑D M₂ = proj₂ (proj₂ m21)
            div-ev-prepend (pchoice-ev va brA) (proj₂ (proj₂ m21) dM₂)

  -- THE reusable congruence
  pchoice-cong-FD : (v₁ v₂ : Menu)
                  → (∀ at a → MaybeFD (v₁ at a) (v₂ at a))
                  → pchoice v₁ ≈FD pchoice v₂
  pchoice-cong-FD v₁ v₂ pw =
      (pchoice-⊑F⊥-dir v₁ v₂ pw , pchoice-⊑D-dir v₁ v₂ pw)
    , (pchoice-⊑F⊥-dir v₂ v₁ (λ at a → MaybeFD-sym (pw at a))
      , pchoice-⊑D-dir v₂ v₁ (λ at a → MaybeFD-sym (pw at a)))

-------------------------------------------------------------------------------------
-- The fan-in offer as a binary-⊓ fold (the "spec" form), and its pointwise MaybeFD
-- equivalence to the operator's `rnFan`.  [] → nothing ; [t] → renamed t ; ≥2 → ⨅⁺.
-------------------------------------------------------------------------------------

rnFanAs⨅ : (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
         → List (PTree E (ExtI E) R-set) → Maybe (PTree E (ExtI E) R-set)
rnFanAs⨅ R preimg []            = nothing
rnFanAs⨅ R preimg (t ∷ [])      = just (t ⟦ R ¿ preimg ⟧)
rnFanAs⨅ R preimg (t ∷ u ∷ rest) =
  just (⨅⁺ (t ⟦ R ¿ preimg ⟧) (map (_⟦ R ¿ preimg ⟧) (u ∷ rest)))

-- the explicit relational renamed menu (spec form of the rename-step law)
renMenuG : (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
           (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set)))
         → (bt : AnyTypes E) → ContinueType bt (Maybe (PTree E (ExtI E) R-set))
renMenuG R preimg v bt b = rnFanAs⨅ R preimg (rnCollect v (preimg bt b))

-- the operator's internal fan-in offer is MaybeFD-equivalent to the spec ⨅⁺ fold.
rnFan-list-FD : (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
                (ts : List (PTree E (ExtI E) R-set))
              → MaybeFD (rnFan R preimg ts) (rnFanAs⨅ R preimg ts)
rnFan-list-FD R preimg []            = lift tt
rnFan-list-FD R preimg (t ∷ [])      = ≈FD-refl (t ⟦ R ¿ preimg ⟧)
rnFan-list-FD R preimg (t ∷ u ∷ rest) = fanNode-⨅⁺-FD {R = R} {preimg = preimg} t u rest

-------------------------------------------------------------------------------------
-- THE LAW (T3.15, relational fan-in form).  Chain:
--   (i)  (pchoice v) ⟦R¿preimg⟧  ≈FD  pchoice (operator's rnFan menu)   — strong bisim
--   (ii) pchoice (rnFan menu)     ≈FD  pchoice (renMenuG R preimg v)     — pchoice-cong
-------------------------------------------------------------------------------------

module _ {ℓr} {R-set : Set ℓr}
         (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
         (preimg : (bt : AnyTypes E) (b : proj₁ bt)
                 → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set)))
         where

  -- the operator's force-level renamed visible offer map
  opMenu : (bt : AnyTypes E) → ContinueType bt (Maybe (PTree E (ExtI E) R-set))
  opMenu bt b = rnFan R preimg (rnCollect v (preimg bt b))

  -- τ-map pointwise: the renamed empty τ-map (∅t) is still empty.
  tau-pw : ∀ i a → extBranch R preimg (∅t {R = R-set}) i a ≡ ∅t {R = R-set} i a
  tau-pw (A , eι₂) a with extBwd eι₂
  ... | just eι₁ = refl
  ... | nothing  = refl

  -- (i) strong bisimulation: force ((pchoice v)⟦R¿preimg⟧) = react opMenu (extBranch R preimg ∅t),
  -- and force (pchoice opMenu) = react opMenu ∅t — same visible map, pointwise-equal τ.
  step-i-∼ : ((pchoice v) ⟦ R ¿ preimg ⟧) ∼ pchoice opMenu
  step-i-∼ =
    node-pw2
      ((pchoice v) ⟦ R ¿ preimg ⟧) (pchoice opMenu)
      opMenu opMenu
      (extBranch R preimg ∅t) ∅t
      refl refl
      (λ bt b → refl)
      tau-pw

  step-i-FD : ((pchoice v) ⟦ R ¿ preimg ⟧) ≈FD pchoice opMenu
  step-i-FD = drbisim→≈FD (sbisim→drbisim step-i-∼)

  -- (ii) pchoice congruence, cell-by-cell via rnFan-list-FD on the collected list.
  step-ii-FD : pchoice opMenu ≈FD pchoice (renMenuG R preimg v)
  step-ii-FD =
    pchoice-cong-FD opMenu (renMenuG R preimg v)
      (λ bt b → rnFan-list-FD R preimg (rnCollect v (preimg bt b)))

  -- rename-step relational (T3.15, fan-in):
  rename-step-rel-FD : ((pchoice v) ⟦ R ¿ preimg ⟧) ≈FD pchoice (renMenuG R preimg v)
  rename-step-rel-FD = begin
    (pchoice v) ⟦ R ¿ preimg ⟧    ≈⟨ step-i-FD ⟩
    pchoice opMenu                 ≈⟨ step-ii-FD ⟩
    pchoice (renMenuG R preimg v)  ∎
    where open SetoidReasoning (≈FD-setoid R-set)
