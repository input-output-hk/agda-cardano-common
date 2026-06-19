{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees

module CSP.Rename {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where
open PTree

-------------------------------------------------------------------------------------
-- Rename (alphabet transformation E₁ → E₂) on the pure-react PTree.
--
-- A *productive* relational renaming operator (no NON_TERMINATING pragma). It
-- relabels the visible events of `P` (a process tree over the *source* alphabet
-- E₁) onto the *target* alphabet E₂ according to a relation `R` on concrete
-- events, with a caller-supplied per-target preimage enumerator.
--
-- The react adaptation is SIMPLER than the vis/ndbr/mix version: the witness-free
-- `react v τc` node fuses the visible offers (renamed via `rnFan`/`rnCollect`,
-- fan-in/fan-out preserved) and the τ-branch function (re-tagged E₁→E₂ via
-- `extBranch`).  No non-emptiness witness ⇒ the old `rnWit`/`extNdWit` are gone.
--
-- Guardedness: every corecursive call `_ ⟦ R ¿ preimg ⟧` sits syntactically under
-- a constructor (`sil`, `just`, the react branch function), routed only through
-- *named* helpers — fan-in is built directly as one `react ∅ τc` node (an internal
-- choice over the enabled sources); a single source stays τ-free.

-- A concrete event over each alphabet: an event label together with its value.
ConcEvent₁ : Set (lsuc ℓ ⊔ ℓe₁)
ConcEvent₁ = Σ[ at ∈ AnyTypes E₁ ] proj₁ at

ConcEvent₂ : Set (lsuc ℓ ⊔ ℓe₂)
ConcEvent₂ = Σ[ at ∈ AnyTypes E₂ ] proj₁ at

-------------------------------------------------------------------------------------
-- Internal index re-tagging (ExtI E₁ ↔ ExtI E₂).  `fin`/`pair` never mention the
-- event type → translated both ways structurally; only `base e` consults ι/ι⁻¹.
-------------------------------------------------------------------------------------

extFwd   : ∀ {A} → ExtI E₁ A → ExtI E₂ A
extBwd   : ∀ {A} → ExtI E₂ A → Maybe (ExtI E₁ A)
extFwdΣ  : AnyTypes (ExtI E₁) → AnyTypes (ExtI E₂)
ext-linv : ∀ {A} (eι : ExtI E₁ A) → extBwd (extFwd eι) ≡ just eι

extFwd (base e)   = base (ι e)
extFwd (pair p q) = pair (extFwd p) (extFwd q)
extFwd fin        = fin

extBwd (base e)   with ι⁻¹ e
... | just e′     = just (base e′)
... | nothing     = nothing
extBwd (pair p q) with extBwd p | extBwd q
... | just p′ | just q′ = just (pair p′ q′)
... | just _  | nothing = nothing
... | nothing | _       = nothing
extBwd fin        = just fin

extFwdΣ (A , eι) = (A , extFwd eι)

ext-linv (base e)   rewrite ι-linv e = refl
ext-linv (pair p q) rewrite ext-linv p | ext-linv q = refl
ext-linv fin        = refl

-------------------------------------------------------------------------------------
-- Collect the enabled source continuations among a target's preimage entries.
-- Pure (no corecursion).  Generic in the proof component so it accepts any
-- `preimg bt b`.
rnCollect : ∀ {ℓr ℓP} {Rr : Set ℓr} {P : (at : AnyTypes E₁) → proj₁ at → Set ℓP}
          → (vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr)))
          → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] P at a)
          → List (PTree E₁ (ExtI E₁) Rr)
rnCollect vP []                 = []
rnCollect vP ((at , a , _) ∷ r) with vP at a
... | just t′ = t′ ∷ rnCollect vP r
... | nothing = rnCollect vP r

-------------------------------------------------------------------------------------
-- The operator and its corecursive helpers (forward declarations, then definitions).
-------------------------------------------------------------------------------------

_⟦_¿_⟧ :
    ∀ {ℓr ℓR} {Rr : Set ℓr}
  → PTree E₁ (ExtI E₁) Rr
  → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
  → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
            → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
  → PTree E₂ (ExtI E₂) Rr

-- rename a single (Maybe) source continuation (corecursion under `just`)
rnMc : ∀ {ℓr ℓR} {Rr : Set ℓr}
     → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
     → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
               → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
     → Maybe (PTree E₁ (ExtI E₁) Rr) → Maybe (PTree E₂ (ExtI E₂) Rr)

-- the k-th enabled source, renamed (`just (… ⟦…⟧)` under a constructor)
rnNth : ∀ {ℓr ℓR} {Rr : Set ℓr}
      → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
      → List (PTree E₁ (ExtI E₁) Rr) → ∀ {m} → Fin m → Maybe (PTree E₂ (ExtI E₂) Rr)

-- τ-branch function of the fan-in node: a finite internal choice over the sources
rnBranch : ∀ {ℓr ℓR} {Rr : Set ℓr}
         → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
         → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                   → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
         → List (PTree E₁ (ExtI E₁) Rr)
         → (i : AnyTypes (ExtI E₂)) → ContinueType i (Maybe (PTree E₂ (ExtI E₂) Rr))

-- renamed visible offer at a target: internal choice over the enabled sources.
-- []→nothing; [t]→ the bare renamed source (τ-free); ≥2→ one `react ∅ τc` node.
rnFan : ∀ {ℓr ℓR} {Rr : Set ℓr}
      → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
      → List (PTree E₁ (ExtI E₁) Rr) → Maybe (PTree E₂ (ExtI E₂) Rr)

-- renamed τ-branch function: pull the target index back via `extBwd` to a source
-- index feeding the source τc; an index outside the source image yields nothing.
extBranch : ∀ {ℓr ℓR} {Rr : Set ℓr}
          → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
          → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                    → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
          → (τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr)))
          → (i₂ : AnyTypes (ExtI E₂)) → ContinueType i₂ (Maybe (PTree E₂ (ExtI E₂) Rr))

rnMc R preimg nothing   = nothing
rnMc R preimg (just t′) = just (t′ ⟦ R ¿ preimg ⟧)

rnNth R preimg []        _        = nothing
rnNth R preimg (t ∷ _)   fzero    = just (t ⟦ R ¿ preimg ⟧)
rnNth R preimg (_ ∷ ts)  (fsuc k) = rnNth R preimg ts k

rnBranch R preimg ts (_ , fin)      (lift k) = rnNth R preimg ts k
rnBranch R preimg ts (_ , base _)   _        = nothing
rnBranch R preimg ts (_ , pair _ _) _        = nothing

rnFan R preimg []           = nothing
rnFan R preimg (t ∷ [])     = just (t ⟦ R ¿ preimg ⟧)
rnFan R preimg (t ∷ u ∷ ts) =
  just (ptree (react (λ _ _ → nothing) (rnBranch R preimg (t ∷ u ∷ ts))))

extBranch R preimg τcP (A , eι₂) a with extBwd eι₂
... | just eι₁ = rnMc R preimg (τcP (A , eι₁) a)
... | nothing  = nothing

force (_⟦_¿_⟧ {Rr = Rr} P R preimg) with P .force
... | ret r       = ret r
... | sil P′      = sil (P′ ⟦ R ¿ preimg ⟧)
... | react vP τcP = react (λ bt b → rnFan R preimg (rnCollect vP (preimg bt b)))
                         (extBranch R preimg τcP)

-------------------------------------------------------------------------------------
-- Inverse-based (functional / injective) visible renaming.
-------------------------------------------------------------------------------------

invRel : (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
       → ConcEvent₁ → ConcEvent₂ → Set (lsuc ℓ ⊔ ℓe₁)
invRel inv ce (bt , b) = inv bt b ≡ just ce

invPreimg : (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
          → (bt : AnyTypes E₂) (b : proj₁ bt)
          → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] invRel inv (at , a) (bt , b))
invPreimg inv bt b with inv bt b
... | nothing       = []
... | just (at , a) = (at , a , refl) ∷ []

renameInv :
    ∀ {ℓr} {Rr : Set ℓr}
  → PTree E₁ (ExtI E₁) Rr
  → (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
  → PTree E₂ (ExtI E₂) Rr
renameInv P inv = P ⟦ invRel inv ¿ invPreimg inv ⟧

-- the visible inverse induced by the module's event injection ι
ι-vis-inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁
ι-vis-inv (A , e₂) b with ι⁻¹ e₂
... | just e₁ = just ((A , e₁) , b)
... | nothing = nothing

-- functional injective alphabet renaming: relabel every event by ι (no fan-in/out)
renameMap : ∀ {ℓr} {Rr : Set ℓr}
          → PTree E₁ (ExtI E₁) Rr → PTree E₂ (ExtI E₂) Rr
renameMap P = renameInv P ι-vis-inv
