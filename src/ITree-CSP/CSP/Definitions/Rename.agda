{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any renaming (just to any-just)
open import Data.Unit.Base renaming (tt to tt₀)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; length)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Interaction_Trees

module CSP.Definitions.Rename {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where
open ITree

-------------------------------------------------------------------------------------
-- Rename (alphabet transformation E₁ → E₂)
--
-- A *productive* relational renaming operator (no NON_TERMINATING pragma). It
-- relabels the visible events of `P` (an interaction tree over the *source*
-- alphabet E₁) onto the *target* alphabet E₂ according to a relation `R` on
-- concrete events, with a caller-supplied per-target preimage enumerator.
--
-- Visible renaming stays fully relational (fan-in and fan-out preserved) via
-- `R`/`preimg`. The module-level injection `(ι, ι⁻¹, ι-linv)` re-tags ONLY the
-- internal `base` indices of `ndbr` nodes (the events that `Hide` embeds), giving
-- full post-hiding generality. `ι` is never used for visible events.
--
-- Guardedness is satisfied by keeping every corecursive call `_ ⟦ R ¿ preimg ⟧`
-- syntactically under a constructor (`sil`, `just`, the `ndbr` branch function,
-- `mix`), routed only through *named* mutual helpers — never through `_⊓_`/`foldr`/
-- `mapMaybe`/extended-lambdas/where-helpers, which the checker cannot see past.
-- Fan-in (several sources → one target) is built directly as ONE `ndbr` node
-- (an internal choice over the enabled sources); a single source stays τ-free.

-- A concrete event over each alphabet: an event label together with its value.
ConcEvent₁ : Set (lsuc ℓ ⊔ ℓe₁)
ConcEvent₁ = Σ[ at ∈ AnyTypes E₁ ] proj₁ at

ConcEvent₂ : Set (lsuc ℓ ⊔ ℓe₂)
ConcEvent₂ = Σ[ at ∈ AnyTypes E₂ ] proj₁ at

-------------------------------------------------------------------------------------
-- Internal index re-tagging (ExtI E₁ ↔ ExtI E₂).
--
-- `fin` / `pair` never mention the event type → translated both ways structurally
-- for free. Only `base e` consults `ι` / `ι⁻¹`. All cases PRESERVE the carried
-- type `A`, so the witnessed value `wa : proj₁ wi` is reused unchanged across the
-- forward re-tag.

extFwd : ∀ {A} → ExtI E₁ A → ExtI E₂ A
extBwd : ∀ {A} → ExtI E₂ A → Maybe (ExtI E₁ A)
extFwdΣ : AnyTypes (ExtI E₁) → AnyTypes (ExtI E₂)
ext-linv : ∀ {A} (eι : ExtI E₁ A) → extBwd (extFwd eι) ≡ just eι

extFwd (base e)    = base (ι e)
extFwd (pair p q)  = pair (extFwd p) (extFwd q)
extFwd fin         = fin

extBwd (base e)    with ι⁻¹ e
... | just e′      = just (base e′)
... | nothing      = nothing
extBwd (pair p q)  with extBwd p | extBwd q
... | just p′ | just q′ = just (pair p′ q′)
... | just _  | nothing = nothing
... | nothing | _       = nothing
extBwd fin         = just fin

extFwdΣ (A , eι) = (A , extFwd eι)

ext-linv (base e)   rewrite ι-linv e = refl
ext-linv (pair p q) rewrite ext-linv p | ext-linv q = refl
ext-linv fin        = refl

-------------------------------------------------------------------------------------
-- Collect the enabled source continuations among a target's preimage entries.
-- Pure (no corecursion): kept outside the mutual block. Generic in the proof
-- component `P` of the entries so it accepts any `preimg bt b`. Source tree is
-- over E₁, but the collected continuations are still source trees (renamed later).
rnCollect : ∀ {ℓr ℓP} {Rr : Set ℓr} {P : (at : AnyTypes E₁) → proj₁ at → Set ℓP}
          → (fP : (at : AnyTypes E₁) → ContinueType at (Maybe (ITree E₁ (ExtI E₁) Rr)))
          → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] P at a)
          → List (ITree E₁ (ExtI E₁) Rr)
rnCollect fP []                 = []
rnCollect fP ((at , a , _) ∷ r) with fP at a
... | just t′ = t′ ∷ rnCollect fP r
... | nothing = rnCollect fP r

-- The operator and its helpers are mutually recursive. Per project convention
-- we use FORWARD DECLARATIONS (all signatures first, then all definitions)
-- rather than a `mutual` block.

-- The renaming operator: source tree over E₁ → target tree over E₂.
_⟦_¿_⟧ :
    ∀ {ℓr ℓR} {Rr : Set ℓr}
  → ITree E₁ (ExtI E₁) Rr
  → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
  → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
            → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
  → ITree E₂ (ExtI E₂) Rr

-- Rename a single (Maybe) source continuation into a target continuation — used
-- for the `ndbr`-distribute case. Corecursion sits under `just`.
rnMc : ∀ {ℓr ℓR} {Rr : Set ℓr}
     → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
     → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
               → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
     → Maybe (ITree E₁ (ExtI E₁) Rr) → Maybe (ITree E₂ (ExtI E₂) Rr)

-- The k-th enabled source, renamed (`just (… ⟦…⟧)` under a constructor).
rnNth : ∀ {ℓr ℓR} {Rr : Set ℓr}
      → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
      → List (ITree E₁ (ExtI E₁) Rr) → ∀ {m} → Fin m → Maybe (ITree E₂ (ExtI E₂) Rr)

-- Branch function of the fan-in `ndbr`: a finite internal choice over sources.
-- The index now ranges over `ExtI E₂` (the target's internal index functor).
rnBranch : ∀ {ℓr ℓR} {Rr : Set ℓr}
         → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
         → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                   → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
         → List (ITree E₁ (ExtI E₁) Rr)
         → (i : AnyTypes (ExtI E₂)) → ContinueType i (Maybe (ITree E₂ (ExtI E₂) Rr))

-- Non-emptiness witness: a nonempty source list makes branch fzero `just (…)`.
rnWit : ∀ {ℓr ℓR} {Rr : Set ℓr}
      → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
      → (t : ITree E₁ (ExtI E₁) Rr) (ts : List (ITree E₁ (ExtI E₁) Rr))
      → Is-just (rnBranch R preimg (t ∷ ts)
                   (Lift ℓ (Fin (length (t ∷ ts))) , fin) (lift fzero))

-- Renamed visible offer at a target: internal choice over the enabled sources.
-- []→nothing (not offered); [t]→ the bare renamed source (τ-free); ≥2→ one ndbr.
rnFan : ∀ {ℓr ℓR} {Rr : Set ℓr}
      → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
      → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
      → List (ITree E₁ (ExtI E₁) Rr) → Maybe (ITree E₂ (ExtI E₂) Rr)

-- Output branch function of a re-tagged `ndbr` node. The index `i₂` ranges over
-- `ExtI E₂`; it is pulled BACKWARD via `extBwd` to a source `ExtI E₁` index that
-- feeds the source branch function `fP`. An index outside the source's image
-- (e.g. a `base` event not in `ι`'s range) yields no branch (`nothing`).
extBranch : ∀ {ℓr ℓR} {Rr : Set ℓr}
          → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
          → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                    → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
          → (fP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (ITree E₁ (ExtI E₁) Rr)))
          → (i₂ : AnyTypes (ExtI E₂)) → ContinueType i₂ (Maybe (ITree E₂ (ExtI E₂) Rr))

-- Witness preservation for the re-tagged `ndbr` node. The source witness `wi`
-- maps forward to `extFwdΣ wi`; `extBranch` there pulls back via
-- `extBwd (extFwd …)`, which `ext-linv` rewrites to `just …`, recovering
-- `fP wi wa` (known `Is-just` from `wp`); `rnMc … (just _) = just _`.
extNdWit : ∀ {ℓr ℓR} {Rr : Set ℓr}
         → (R : ConcEvent₁ → ConcEvent₂ → Set ℓR)
         → (preimg : (bt : AnyTypes E₂) (b : proj₁ bt)
                   → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b)))
         → (fP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (ITree E₁ (ExtI E₁) Rr)))
         → ∀ {wi : AnyTypes (ExtI E₁)} {wa : proj₁ wi}
         → Is-just (fP wi wa)
         → Is-just (extBranch R preimg fP (extFwdΣ wi) wa)

-- Definitions.
rnMc R preimg nothing    = nothing
rnMc R preimg (just t′)  = just (t′ ⟦ R ¿ preimg ⟧)

rnNth R preimg []        _        = nothing
rnNth R preimg (t ∷ _)   fzero    = just (t ⟦ R ¿ preimg ⟧)
rnNth R preimg (_ ∷ ts)  (fsuc k) = rnNth R preimg ts k

rnBranch R preimg ts (_ , fin)      (lift k) = rnNth R preimg ts k
rnBranch R preimg ts (_ , base _)   _        = nothing
rnBranch R preimg ts (_ , pair _ _) _        = nothing

rnWit R preimg t ts = any-just tt₀

rnFan R preimg []            = nothing
rnFan R preimg (t ∷ [])      = just (t ⟦ R ¿ preimg ⟧)
rnFan R preimg (t ∷ u ∷ ts)  =
  just (itree (ndbr (rnBranch R preimg (t ∷ u ∷ ts))
                    (Lift ℓ (Fin (length (t ∷ u ∷ ts))) , fin)
                    (lift fzero) (rnWit R preimg t (u ∷ ts))))

extBranch R preimg fP (A , eι₂) a with extBwd eι₂
... | just eι₁ = rnMc R preimg (fP (A , eι₁) a)
... | nothing  = nothing

extNdWit R preimg fP {_ , eι} {wa} p
  rewrite ext-linv eι with fP (_ , eι) wa | p
... | just _ | _ = any-just tt₀

force (_⟦_¿_⟧ {Rr = Rr} P R preimg) with P .force
... | ret r            = ret r
... | sil P′           = sil (P′ ⟦ R ¿ preimg ⟧)
... | vis fP           = vis (λ bt b → rnFan R preimg (rnCollect fP (preimg bt b)))
... | ndbr fP wi wa wp = ndbr (extBranch R preimg fP) (extFwdΣ wi) wa
                              (extNdWit R preimg fP wp)
... | mix fP Q′        = mix (λ bt b → rnFan R preimg (rnCollect fP (preimg bt b)))
                             (Q′ ⟦ R ¿ preimg ⟧)

-- Inverse-based (functional / injective) visible renaming. `inv bt b` returns the
-- unique concrete source event (over E₁) that renames to the concrete target
-- (bt , b) over E₂, or nothing. `invRel`/`invPreimg` are top-level (not
-- where-bound) so they can be named in proofs/checks. The visible `inv` and the
-- module-level `ι`/`ι⁻¹` are independent inputs (one re-labels visible events
-- possibly many-to-one; the other re-tags internal events).
invRel : (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
       → ConcEvent₁ → ConcEvent₂ → Set (lsuc ℓ ⊔ ℓe₁)
invRel inv ce (bt , b) = inv bt b ≡ just ce

invPreimg : (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
          → (bt : AnyTypes E₂) (b : proj₁ bt)
          → List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] invRel inv (at , a) (bt , b))
invPreimg inv bt b with inv bt b
... | nothing       = []
-- the with-match rewrites inv bt b to just (at , a), so invRel reduces to refl
... | just (at , a) = (at , a , refl) ∷ []

renameInv :
    ∀ {ℓr} {Rr : Set ℓr}
  → ITree E₁ (ExtI E₁) Rr
  → (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
  → ITree E₂ (ExtI E₂) Rr
renameInv P inv = P ⟦ invRel inv ¿ invPreimg inv ⟧

-- The visible inverse induced by the module's event injection: a target event
-- (bt , b) comes from the unique source event (preimage under ι) carrying the
-- same value b, when bt is in ι's image.
ι-vis-inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁
ι-vis-inv (A , e₂) b with ι⁻¹ e₂
... | just e₁ = just ((A , e₁) , b)
... | nothing = nothing

-- Functional injective alphabet renaming: relabel every visible/internal event by
-- the module's injection ι (no fan-in/out). The classic CSP f(P) with injective f.
renameMap : ∀ {ℓr} {Rr : Set ℓr}
  → ITree E₁ (ExtI E₁) Rr → ITree E₂ (ExtI E₂) Rr
renameMap P = renameInv P ι-vis-inv
