{-# OPTIONS --guardedness #-}

-- Renaming distributes over sliding for the GENERAL RELATIONAL renaming `_⟦ R ¿ preimg ⟧`
-- (same-alphabet instantiation E₁ = E₂ = E), the relational analogue of the injective
-- `CSP.Laws.FD.RenameSlide` (U13.6):
--
--   (((pchoice v) ▷ Q) ⟦ R ¿ preimg ⟧)
--     ≈FD (((pchoice v) ⟦ R ¿ preimg ⟧) ▷ (Q ⟦ R ¿ preimg ⟧)).
--
-- Faithful spike rendering of Roscoe's
--   ((?x:A→P) ▷ Q)⟦R⟧ = (?y:R(A)→⨅{P[a/x]⟦R⟧ | a R y}) ▷ (Q⟦R⟧).
--
-- WHY a NODE-PW2 (force-equality) strong bisim and NOT step-inversion:
-- the relational visible step is WEAK (fan-in: a target event reaches an internal
-- ⨅ over its enabled sources).  But here that fan-in is IDENTICAL on both sides — the
-- renamed prefix `pchoice v ⟦R¿preimg⟧` is the SAME `react rnVis …` node whether it
-- appears renamed-then-slid or slid-then-renamed — so a force-level node comparison
-- (`node-pw2` from `SeqSlide`) sidesteps the fan-in entirely.  Both forces are
-- `react rnVis τ`:  the visible maps are the LITERALLY SAME expression `rnVis`
-- (`vis-pw = refl`), and the τ-maps are POINTWISE EQUAL (`tau-pw`, the crux), with
-- LITERALLY-SAME successors (`Q ⟦R¿preimg⟧` for the timeout) ⇒ `sbisim-refl` inside
-- `node-pw2`.  Lifted to ≈FD via `drbisim→≈FD ∘ sbisim→drbisim`.
--
-- The crux `tau-pw` matches `extBranch R preimg τcS` (LHS τ-map, where
-- `τcS = ▷-slide (react v ∅t) Q`) against `▷-slide (react rnVis ∅t) (Q⟦R¿preimg⟧)`
-- (RHS τ-map), casing the `ExtI E` index.  `extBranch` pulls the target index back via
-- `extBwd`; for the IDENTITY instantiation (ι = id, ι⁻¹ = just) `extBwd` always
-- succeeds (`extBwd-just`), so the timeout index `pair fin i` is recovered and the
-- slide's `just Q` renames to `just (Q⟦R¿preimg⟧)`, matching the RHS slide's `just`.

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.RenameSlideRel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (pchoice; _▷_; ▷-slide; ∅t)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (_⟦_¿_⟧; ConcEvent₁; ConcEvent₂; rnCollect; rnFan; rnMc;
         extBranch; extBwd; extFwd; ext-linv)
open import CSP.Laws.FD.SeqSlide E-≟ using (node-pw2)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-react)
open import CSP.Laws.Traces.TraceLawsRenameGen {E = E} using (force-renG-react)
open import Semantics.Bisim {E = E} {I = ExtI E} using (_∼_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
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
-- extBwd is a total `just` for the IDENTITY instantiation (ι = id, ι⁻¹ = just):
-- extFwd is pointwise the identity, so `ext-linv` gives `extBwd i ≡ just i`.
-------------------------------------------------------------------------------------

extFwd-id : ∀ {A} (i : ExtI E A) → extFwd i ≡ i
extFwd-id (base e)   = refl
extFwd-id (pair p q) = cong₂ pair (extFwd-id p) (extFwd-id q)
  where open import Data.Product using () renaming (_,_ to _,,_)
        open import Relation.Binary.PropositionalEquality using (cong₂)
extFwd-id fin        = refl

extBwd-just : ∀ {A} (i : ExtI E A) → extBwd i ≡ just i
extBwd-just i = trans (cong extBwd (sym (extFwd-id i))) (ext-linv i)

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr} {R-set : Set ℓr}
         (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
         (preimg : (bt : AnyTypes E) (b : proj₁ bt)
                 → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set)))
         (Q : PTree E (ExtI E) R-set)
         where

  -- the renamed visible offer map shared by both nodes.
  rnVis : (bt : AnyTypes E) → ContinueType bt (Maybe (PTree E (ExtI E) R-set))
  rnVis bt b = rnFan R preimg (rnCollect v (preimg bt b))

  -- the LHS prefix's slide τ-map (the renamed-then-slid one is `extBranch … τcS`).
  τcS : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R-set))
  τcS = ▷-slide (react v ∅t) Q

  -- force LHS:  force ((pchoice v) ▷ Q) = react v τcS (force-▷-react); renaming a
  -- react node gives  react rnVis (extBranch R preimg τcS)  (force-renG-react).
  force-LHS : PTree.force ((((pchoice v) ▷ Q) ⟦ R ¿ preimg ⟧))
            ≡ react rnVis (extBranch R preimg τcS)
  force-LHS = force-renG-react {R = R} {preimg = preimg} {P = (pchoice v) ▷ Q}
                (force-▷-react {P = pchoice v} {Q = Q} refl)

  -- the renamed prefix `(pchoice v) ⟦R¿preimg⟧` is the bare react node `react rnVis ∅t′`,
  -- where the renamed empty τ-map ∅t′ = extBranch R preimg ∅t is pointwise ∅t.
  force-ren-pchoice : PTree.force ((pchoice v) ⟦ R ¿ preimg ⟧)
                    ≡ react rnVis (extBranch R preimg ∅t)
  force-ren-pchoice = force-renG-react {R = R} {preimg = preimg} {P = pchoice v} refl

  -- force RHS:  the renamed prefix is a react node (force-ren-pchoice), so sliding it
  -- gives  react rnVis (▷-slide (react rnVis (extBranch R preimg ∅t)) (Q⟦R¿preimg⟧)).
  force-RHS : PTree.force (((pchoice v) ⟦ R ¿ preimg ⟧) ▷ (Q ⟦ R ¿ preimg ⟧))
            ≡ react rnVis (▷-slide (react rnVis (extBranch R preimg ∅t)) (Q ⟦ R ¿ preimg ⟧))
  force-RHS = force-▷-react {P = (pchoice v) ⟦ R ¿ preimg ⟧} {Q = Q ⟦ R ¿ preimg ⟧}
                force-ren-pchoice

  -- visible-map pointwise: both nodes carry the LITERALLY-SAME `rnVis`.
  vis-pw : ∀ bt b → rnVis bt b ≡ rnVis bt b
  vis-pw bt b = refl

  -- THE CRUX.  τ-map pointwise:
  --   extBranch R preimg τcS  ≡  ▷-slide (react rnVis (extBranch R preimg ∅t)) (Q⟦R¿preimg⟧)
  -- casing the ExtI E index.  `extBranch … (A , eι₂)` pulls `eι₂` back via `extBwd`;
  -- for the identity instantiation `extBwd eι₂ = just eι₂` (extBwd-just), recovering
  -- the source index, so `τcS` fires:  the timeout `pair fin _` gives `just Q`, renamed
  -- to `just (Q⟦R¿preimg⟧)` = the RHS slide's timeout `just`; every other index gives
  -- `nothing` on both sides (the prefix's τ-map is ∅t).
  tau-pw : ∀ i a
         → extBranch R preimg τcS i a
         ≡ ▷-slide (react rnVis (extBranch R preimg ∅t)) (Q ⟦ R ¿ preimg ⟧) i a
  tau-pw (A , base e)   a rewrite extBwd-just {A = A} (base e) = refl
  tau-pw (A , fin)      a rewrite extBwd-just {A = A} fin      = refl
  tau-pw (A , pair p q) a rewrite extBwd-just {A = A} (pair p q) = lemma p q a
    where
      -- after extBwd recovers `pair p q`, the LHS is `rnMc R preimg (τcS (A,pair p q) a)`;
      -- match `τcS = ▷-slide (react v ∅t) Q` and the RHS slide on the `pair` index.
      lemma : ∀ p q a
            → rnMc R preimg (▷-slide (react v ∅t) Q (A , pair p q) a)
            ≡ ▷-slide (react rnVis (extBranch R preimg ∅t)) (Q ⟦ R ¿ preimg ⟧)
                      (A , pair p q) a
      lemma (base _)   q a = refl
      lemma (pair _ _) q a = refl
      lemma fin q (lift fzero            , a) = refl
      -- P's own τ (`fsuc fzero`): both sides read the prefix node's τ-map.  LHS reads
      -- `viewT (react v ∅t) = ∅t = nothing`; RHS reads `viewT (react rnVis
      -- (extBranch R preimg ∅t)) = extBranch R preimg ∅t`, which is pointwise `nothing`
      -- (force the `extBwd q` block via extBwd-just; then `rnMc … nothing = nothing`).
      lemma fin q (lift (fsuc fzero)     , a)
        rewrite extBwd-just {A = _} q = refl
      lemma fin q (lift (fsuc (fsuc _))  , a) = refl

  rename-slide-rel-∼ :
      ((((pchoice v) ▷ Q) ⟦ R ¿ preimg ⟧))
        ∼ (((pchoice v) ⟦ R ¿ preimg ⟧) ▷ (Q ⟦ R ¿ preimg ⟧))
  rename-slide-rel-∼ =
    node-pw2
      ((((pchoice v) ▷ Q) ⟦ R ¿ preimg ⟧))
      (((pchoice v) ⟦ R ¿ preimg ⟧) ▷ (Q ⟦ R ¿ preimg ⟧))
      rnVis rnVis
      (extBranch R preimg τcS)
      (▷-slide (react rnVis (extBranch R preimg ∅t)) (Q ⟦ R ¿ preimg ⟧))
      force-LHS force-RHS
      vis-pw
      tau-pw

  -- rename-slide relational (U13.6, relational):
  rename-slide-rel-FD :
      ((((pchoice v) ▷ Q) ⟦ R ¿ preimg ⟧))
        ≈FD (((pchoice v) ⟦ R ¿ preimg ⟧) ▷ (Q ⟦ R ¿ preimg ⟧))
  rename-slide-rel-FD = drbisim→≈FD (sbisim→drbisim rename-slide-rel-∼)
