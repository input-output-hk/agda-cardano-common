{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- TOPOLOGY-GENERIC single-step LTS inversion for the replicated
-- interleaving folds `⦀Fin⁺`, `⦀Fin` and `⦀⋆`, with NO pairwise-disjointness
-- (`noBoth`) hypothesis.  Parameterised exactly like
-- `CSP.Laws.Traces.TraceLawsParallelElim` (a decidable equality on
-- events), so nothing here is specialised to any concrete event type.
--
-- Findings encoded below:
--  * τ-inversion needs NO hypothesis at all and is positional
--    (index + operand step + `finUpd`-reconstructed target).
--  * ev-inversion without `noBoth` CANNOT be positional: `par-pVis`'s
--    clause `no _ | just P' | just Q' = just (ptree (react ∅v
--    (par-brBoth …)))` builds an internal-choice COLLISION node that is
--    not of the form `⦀Fin⁺ n g`.  The disjointness-free statement is
--    therefore a three-way recursive residual family `FoldEvR`.
--  * `noBoth` deletes the collision disjunct and restores the positional
--    shape — proved here as `⦀Fin⁺-ev-pos`.
------------------------------------------------------------------------

open import Level using (Level; Lift; lower; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsRepElim {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import Semantics.LTS {E = E} {I = ExtI E}
open import CSP.Laws.Traces.TraceLawsParallel     E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelElim E-≟
  using ( ParτR; τL; τR
        ; ParevR; evSync; evL; evR; evBoth
        ; Par-τ-elim; Par-ev-elim )

module _ {ℓr : Level} where

  -- the process type the CSP interleaving lives at
  Proc : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  Proc = PTree E (ExtI E) (⊤ {ℓr})

  -- the merge used by `_⦀_` (definitionally the one in `Par ∅ES (λ _ _ → tt)`)
  mrg : Mg (⊤ {ℓr}) (⊤ {ℓr}) (⊤ {ℓr})
  mrg _ _ = tt

  -- pointwise update of a `Fin`-indexed family, by Fin recursion, so that the
  -- fold reconstruction below reduces DEFINITIONALLY (no funext is needed)
  finUpd : ∀ {n} → (Fin n → Proc) → Fin n → Proc → Fin n → Proc
  finUpd f fzero    Mi fzero    = Mi
  finUpd f fzero    Mi (fsuc j) = f (fsuc j)
  finUpd f (fsuc i) Mi fzero    = f fzero
  finUpd f (fsuc i) Mi (fsuc j) = finUpd (λ k → f (fsuc k)) i Mi j

  ------------------------------------------------------------------------
  -- τ-inversion: NO hypothesis, and positional
  ------------------------------------------------------------------------

  -- a τ of `⦀Fin⁺ n f` is exactly one component's τ, the target being the
  -- fold with that position updated
  ⦀Fin⁺-τ-inv : (n : ℕ) (f : Fin (suc n) → Proc) {M : Proc}
    → ⦀Fin⁺ n f ─[ τ ]─► M
    → Σ[ i ∈ Fin (suc n) ] Σ[ Mi ∈ Proc ]
        (f i ─[ τ ]─► Mi) × (M ≡ ⦀Fin⁺ n (finUpd f i Mi))
  ⦀Fin⁺-τ-inv zero    f step = fzero , _ , step , refl
  ⦀Fin⁺-τ-inv (suc n) f step
    with Par-τ-elim ∅ES mrg (f fzero) (⦀Fin⁺ n (λ i → f (fsuc i))) step
  ... | τL P' ps refl = fzero , P' , ps , refl
  ... | τR Q' qs refl with ⦀Fin⁺-τ-inv n (λ i → f (fsuc i)) qs
  ...   | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq

  ------------------------------------------------------------------------
  -- ev-inversion WITHOUT disjointness: the three-way residual family
  ------------------------------------------------------------------------

  -- `FoldEvR n f M X e a` describes every residual `M` a visible (non-√)
  -- step on `(X , e , a)` of `⦀Fin⁺ n f` can have.  Three shapes per layer:
  --   (1) the head fired solo   → `Mi ⦀ tail`
  --   (2) the head is unchanged → `f 0 ⦀ M′`, recursively inverted
  --   (3) COLLISION: head AND tail both offer the event, so `par-pVis`
  --       emits the internal-choice node `react ∅v (par-brBoth …)`; this
  --       residual is NOT an interleaving fold, which is exactly why the
  --       disjointness-free statement cannot be positional.
  FoldEvR : (n : ℕ) → (Fin (suc n) → Proc) → Proc
          → (X : Set ℓ) → E X → X → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  FoldEvR zero    f M X e a = f fzero ─[ ev (evl (evLabel X e a)) ]─► M
  FoldEvR (suc n) f M X e a =
      (Σ[ Mi ∈ Proc ] (f fzero ─[ ev (evl (evLabel X e a)) ]─► Mi)
                    × (M ≡ Mi ⦀ ⦀Fin⁺ n (λ i → f (fsuc i))))
    ⊎ (Σ[ M′ ∈ Proc ] FoldEvR n (λ i → f (fsuc i)) M′ X e a
                    × (M ≡ f fzero ⦀ M′))
    ⊎ (Σ[ Mi ∈ Proc ] Σ[ M′ ∈ Proc ]
         (f fzero ─[ ev (evl (evLabel X e a)) ]─► Mi)
       × FoldEvR n (λ i → f (fsuc i)) M′ X e a
       × (M ≡ ptree (react (λ _ _ → nothing)
                     (par-brBoth ∅ES mrg (f fzero)
                       (⦀Fin⁺ n (λ i → f (fsuc i))) Mi M′))))

  -- THE DISJOINTNESS-FREE INVERSION: every visible step of the fold is
  -- decoded into `FoldEvR`, with no hypothesis whatsoever.  `evSync` is
  -- refuted by `∅ES .mem _ _ = ⊥`; `ev√` is index-impossible on an `evl`
  -- label; `evBoth` is KEPT (disjunct 3) rather than refuted.
  ⦀Fin⁺-ev-inv : (n : ℕ) (f : Fin (suc n) → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → ⦀Fin⁺ n f ─[ ev (evl (evLabel X e a)) ]─► M
    → FoldEvR n f M X e a
  ⦀Fin⁺-ev-inv zero    f step = step
  ⦀Fin⁺-ev-inv (suc n) f step
    with Par-ev-elim ∅ES mrg (f fzero) (⦀Fin⁺ n (λ i → f (fsuc i))) step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ ps       = inj₁ (_ , ps , refl)
  ... | evR _ qs       = inj₂ (inj₁ (_ , ⦀Fin⁺-ev-inv n (λ i → f (fsuc i)) qs , refl))
  ... | evBoth _ ps qs =
          inj₂ (inj₂ (_ , _ , ps , ⦀Fin⁺-ev-inv n (λ i → f (fsuc i)) qs , refl))

  ------------------------------------------------------------------------
  -- what the residual family still buys you with no hypothesis
  ------------------------------------------------------------------------

  -- "some component moved": the index and its step are recoverable from
  -- `FoldEvR` even through collisions (a collision reports its head)
  ⦀Fin⁺-ev-some : (n : ℕ) (f : Fin (suc n) → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → FoldEvR n f M X e a
    → Σ[ i ∈ Fin (suc n) ] Σ[ Mi ∈ Proc ] (f i ─[ ev (evl (evLabel X e a)) ]─► Mi)
  ⦀Fin⁺-ev-some zero    f st = fzero , _ , st
  ⦀Fin⁺-ev-some (suc n) f (inj₁ (Mi , ps , _)) = fzero , Mi , ps
  ⦀Fin⁺-ev-some (suc n) f (inj₂ (inj₁ (_ , rec , _)))
    with ⦀Fin⁺-ev-some n (λ i → f (fsuc i)) rec
  ... | i , Mi , istep = fsuc i , Mi , istep
  ⦀Fin⁺-ev-some (suc n) f (inj₂ (inj₂ (Mi , _ , ps , _ , _))) = fzero , Mi , ps

  ------------------------------------------------------------------------
  -- what `noBoth` actually buys: it deletes disjunct (3)
  ------------------------------------------------------------------------

  -- pairwise alphabet disjointness at one event: no two distinct components
  -- both offer `(X , e , a)`
  NoBoth : (n : ℕ) → (Fin (suc n) → Proc) → (X : Set ℓ) → E X → X → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  NoBoth n f X e a = (i j : Fin (suc n)) → i ≢ j → {Mi Mj : Proc}
    → f i ─[ ev (evl (evLabel X e a)) ]─► Mi
    → f j ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥

  -- under `NoBoth` the residual family collapses to the POSITIONAL shape
  -- (the same conclusion the bespoke `⦀Fin-ev-inv` reaches)
  ⦀Fin⁺-ev-pos : (n : ℕ) (f : Fin (suc n) → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → NoBoth n f X e a
    → FoldEvR n f M X e a
    → Σ[ i ∈ Fin (suc n) ] Σ[ Mi ∈ Proc ]
        (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin⁺ n (finUpd f i Mi))
  ⦀Fin⁺-ev-pos zero    f nb st = fzero , _ , st , refl
  ⦀Fin⁺-ev-pos (suc n) f nb (inj₁ (Mi , ps , refl)) = fzero , Mi , ps , refl
  ⦀Fin⁺-ev-pos (suc n) f nb (inj₂ (inj₁ (M′ , rec , refl)))
    with ⦀Fin⁺-ev-pos n (λ i → f (fsuc i))
           (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) rec
  ... | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq
  ⦀Fin⁺-ev-pos (suc n) f nb (inj₂ (inj₂ (Mi , M′ , ps , rec , _)))
    with ⦀Fin⁺-ev-some n (λ i → f (fsuc i)) rec
  ... | i , _ , istep = ⊥-elim (nb fzero (fsuc i) (λ ()) ps istep)

  -- end-to-end: the classical positional ev-inversion, derived from the
  -- disjointness-free one
  ⦀Fin⁺-ev-inv-noBoth : (n : ℕ) (f : Fin (suc n) → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → NoBoth n f X e a
    → ⦀Fin⁺ n f ─[ ev (evl (evLabel X e a)) ]─► M
    → Σ[ i ∈ Fin (suc n) ] Σ[ Mi ∈ Proc ]
        (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin⁺ n (finUpd f i Mi))
  ⦀Fin⁺-ev-inv-noBoth n f nb step = ⦀Fin⁺-ev-pos n f nb (⦀Fin⁺-ev-inv n f step)

  ------------------------------------------------------------------------
  -- the Skip-tailed fold `⦀Fin` (empty fold = `Skip`)
  ------------------------------------------------------------------------

  -- a τ of `⦀Fin n f` is exactly one component's τ; the empty fold is
  -- `Skip = Ret tt`, which has no τ at all, so the base case is absurd
  ⦀Fin-τ-inv : (n : ℕ) (f : Fin n → Proc) {M : Proc}
    → ⦀Fin n f ─[ τ ]─► M
    → Σ[ i ∈ Fin n ] Σ[ Mi ∈ Proc ]
        (f i ─[ τ ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
  ⦀Fin-τ-inv zero    f (sSil ())
  ⦀Fin-τ-inv zero    f (sTau () _)
  ⦀Fin-τ-inv (suc n) f step
    with Par-τ-elim ∅ES mrg (f fzero) (⦀Fin n (λ i → f (fsuc i))) step
  ... | τL P' ps refl = fzero , P' , ps , refl
  ... | τR Q' qs refl with ⦀Fin-τ-inv n (λ i → f (fsuc i)) qs
  ...   | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq

  -- the `⦀Fin` analogue of `FoldEvR`: same three shapes per layer, with the
  -- empty fold contributing NO visible step (`Skip` offers nothing)
  FoldEvRF : (n : ℕ) → (Fin n → Proc) → Proc
           → (X : Set ℓ) → E X → X → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  FoldEvRF zero    f M X e a = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓr) ⊥
  FoldEvRF (suc n) f M X e a =
      (Σ[ Mi ∈ Proc ] (f fzero ─[ ev (evl (evLabel X e a)) ]─► Mi)
                    × (M ≡ Mi ⦀ ⦀Fin n (λ i → f (fsuc i))))
    ⊎ (Σ[ M′ ∈ Proc ] FoldEvRF n (λ i → f (fsuc i)) M′ X e a
                    × (M ≡ f fzero ⦀ M′))
    ⊎ (Σ[ Mi ∈ Proc ] Σ[ M′ ∈ Proc ]
         (f fzero ─[ ev (evl (evLabel X e a)) ]─► Mi)
       × FoldEvRF n (λ i → f (fsuc i)) M′ X e a
       × (M ≡ ptree (react (λ _ _ → nothing)
                     (par-brBoth ∅ES mrg (f fzero)
                       (⦀Fin n (λ i → f (fsuc i))) Mi M′))))

  -- disjointness-free ev-inversion for `⦀Fin`; the empty fold is refuted by
  -- `force Skip ≡ ret tt` (no `react` node to offer from)
  ⦀Fin-ev-inv : (n : ℕ) (f : Fin n → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → ⦀Fin n f ─[ ev (evl (evLabel X e a)) ]─► M
    → FoldEvRF n f M X e a
  ⦀Fin-ev-inv zero    f (sVis () _)
  ⦀Fin-ev-inv (suc n) f step
    with Par-ev-elim ∅ES mrg (f fzero) (⦀Fin n (λ i → f (fsuc i))) step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ ps       = inj₁ (_ , ps , refl)
  ... | evR _ qs       = inj₂ (inj₁ (_ , ⦀Fin-ev-inv n (λ i → f (fsuc i)) qs , refl))
  ... | evBoth _ ps qs =
          inj₂ (inj₂ (_ , _ , ps , ⦀Fin-ev-inv n (λ i → f (fsuc i)) qs , refl))

  -- "some component moved", recovered from the `⦀Fin` residual family
  ⦀Fin-ev-some : (n : ℕ) (f : Fin n → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → FoldEvRF n f M X e a
    → Σ[ i ∈ Fin n ] Σ[ Mi ∈ Proc ] (f i ─[ ev (evl (evLabel X e a)) ]─► Mi)
  ⦀Fin-ev-some zero    f r = ⊥-elim (lower r)
  ⦀Fin-ev-some (suc n) f (inj₁ (Mi , ps , _)) = fzero , Mi , ps
  ⦀Fin-ev-some (suc n) f (inj₂ (inj₁ (_ , rec , _)))
    with ⦀Fin-ev-some n (λ i → f (fsuc i)) rec
  ... | i , Mi , istep = fsuc i , Mi , istep
  ⦀Fin-ev-some (suc n) f (inj₂ (inj₂ (Mi , _ , ps , _ , _))) = fzero , Mi , ps

  -- `NoBoth` at an arbitrary arity (`NoBoth n f` is `NoBothF (suc n) f`)
  NoBothF : (n : ℕ) → (Fin n → Proc) → (X : Set ℓ) → E X → X → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  NoBothF n f X e a = (i j : Fin n) → i ≢ j → {Mi Mj : Proc}
    → f i ─[ ev (evl (evLabel X e a)) ]─► Mi
    → f j ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥

  -- under `NoBothF` the `⦀Fin` residual family collapses to the positional shape
  ⦀Fin-ev-pos : (n : ℕ) (f : Fin n → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → NoBothF n f X e a
    → FoldEvRF n f M X e a
    → Σ[ i ∈ Fin n ] Σ[ Mi ∈ Proc ]
        (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
  ⦀Fin-ev-pos zero    f nb r = ⊥-elim (lower r)
  ⦀Fin-ev-pos (suc n) f nb (inj₁ (Mi , ps , refl)) = fzero , Mi , ps , refl
  ⦀Fin-ev-pos (suc n) f nb (inj₂ (inj₁ (M′ , rec , refl)))
    with ⦀Fin-ev-pos n (λ i → f (fsuc i))
           (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) rec
  ... | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq
  ⦀Fin-ev-pos (suc n) f nb (inj₂ (inj₂ (Mi , M′ , ps , rec , _)))
    with ⦀Fin-ev-some n (λ i → f (fsuc i)) rec
  ... | i , _ , istep = ⊥-elim (nb fzero (fsuc i) (λ ()) ps istep)

  -- end-to-end positional ev-inversion for `⦀Fin`
  ⦀Fin-ev-inv-noBoth : (n : ℕ) (f : Fin n → Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → NoBothF n f X e a
    → ⦀Fin n f ─[ ev (evl (evLabel X e a)) ]─► M
    → Σ[ i ∈ Fin n ] Σ[ Mi ∈ Proc ]
        (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
  ⦀Fin-ev-inv-noBoth n f nb step = ⦀Fin-ev-pos n f nb (⦀Fin-ev-inv n f step)

  ------------------------------------------------------------------------
  -- the list-indexed Skip-tailed fold `⦀⋆`
  ------------------------------------------------------------------------

  -- a τ of `⦀⋆ Ps` is exactly one element's τ, located by a list split;
  -- `⦀⋆ [] = Skip` has no τ, so the base case is absurd
  ⦀⋆-τ-inv : (Ps : List Proc) {M : Proc}
    → ⦀⋆ Ps ─[ τ ]─► M
    → Σ[ pre ∈ List Proc ] Σ[ P ∈ Proc ] Σ[ post ∈ List Proc ] Σ[ P′ ∈ Proc ]
        (Ps ≡ pre ++ P ∷ post) × (P ─[ τ ]─► P′) × (M ≡ ⦀⋆ (pre ++ P′ ∷ post))
  ⦀⋆-τ-inv []       (sSil ())
  ⦀⋆-τ-inv []       (sTau () _)
  ⦀⋆-τ-inv (P ∷ Ps) step with Par-τ-elim ∅ES mrg P (⦀⋆ Ps) step
  ... | τL P' ps refl = [] , P , Ps , P' , refl , ps , refl
  ... | τR Q' qs refl with ⦀⋆-τ-inv Ps qs
  ...   | pre , R , post , R' , peq , rs , meq =
            P ∷ pre , R , post , R' , cong (P ∷_) peq , rs , cong (P ⦀_) meq

  -- the `⦀⋆` analogue of `FoldEvR`, recursing on the list spine
  FoldEvL : List Proc → Proc → (X : Set ℓ) → E X → X → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  FoldEvL []       M X e a = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓr) ⊥
  FoldEvL (P ∷ Ps) M X e a =
      (Σ[ P′ ∈ Proc ] (P ─[ ev (evl (evLabel X e a)) ]─► P′) × (M ≡ P′ ⦀ ⦀⋆ Ps))
    ⊎ (Σ[ M′ ∈ Proc ] FoldEvL Ps M′ X e a × (M ≡ P ⦀ M′))
    ⊎ (Σ[ P′ ∈ Proc ] Σ[ M′ ∈ Proc ]
         (P ─[ ev (evl (evLabel X e a)) ]─► P′)
       × FoldEvL Ps M′ X e a
       × (M ≡ ptree (react (λ _ _ → nothing)
                     (par-brBoth ∅ES mrg P (⦀⋆ Ps) P′ M′))))

  -- disjointness-free ev-inversion for `⦀⋆`
  ⦀⋆-ev-inv : (Ps : List Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → ⦀⋆ Ps ─[ ev (evl (evLabel X e a)) ]─► M
    → FoldEvL Ps M X e a
  ⦀⋆-ev-inv []       (sVis () _)
  ⦀⋆-ev-inv (P ∷ Ps) step with Par-ev-elim ∅ES mrg P (⦀⋆ Ps) step
  ... | evSync mem _ _ = ⊥-elim mem
  ... | evL _ ps       = inj₁ (_ , ps , refl)
  ... | evR _ qs       = inj₂ (inj₁ (_ , ⦀⋆-ev-inv Ps qs , refl))
  ... | evBoth _ ps qs = inj₂ (inj₂ (_ , _ , ps , ⦀⋆-ev-inv Ps qs , refl))

  -- "some element moved", recovered from the `⦀⋆` residual family
  ⦀⋆-ev-some : (Ps : List Proc)
      {X : Set ℓ} {e : E X} {a : X} {M : Proc}
    → FoldEvL Ps M X e a
    → Σ[ pre ∈ List Proc ] Σ[ P ∈ Proc ] Σ[ post ∈ List Proc ] Σ[ P′ ∈ Proc ]
        (Ps ≡ pre ++ P ∷ post) × (P ─[ ev (evl (evLabel X e a)) ]─► P′)
  ⦀⋆-ev-some []       r = ⊥-elim (lower r)
  ⦀⋆-ev-some (P ∷ Ps) (inj₁ (P′ , ps , _)) = [] , P , Ps , P′ , refl , ps
  ⦀⋆-ev-some (P ∷ Ps) (inj₂ (inj₁ (_ , rec , _))) with ⦀⋆-ev-some Ps rec
  ... | pre , R , post , R′ , peq , rs = P ∷ pre , R , post , R′ , cong (P ∷_) peq , rs
  ⦀⋆-ev-some (P ∷ Ps) (inj₂ (inj₂ (P′ , _ , ps , _ , _))) = [] , P , Ps , P′ , refl , ps
