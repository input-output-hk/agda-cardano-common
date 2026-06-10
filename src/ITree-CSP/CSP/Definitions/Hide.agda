{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; Is-just; nothing) renaming (map to mapMaybe)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; _×_)
-- open import Relation.Unary
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
-- open import Class.DecEq
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Class.DecEq

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes

module CSP.Definitions.Hide  {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-------------------------------------------------------------------------------------
-- Hide
--
-- Hiding turns events in `cs` into silent (τ) transitions.  The interesting
-- case is hiding a visible choice `vis fP`:
--
--   (?x : A → P(x)) ∖ cs
--     = (?x : (A − cs) → P(x) ∖ cs)                       when A ∩ cs = ∅  (a plain vis)
--     = (?x : (A − cs) → P(x) ∖ cs) ▷ ⨅ a:A∩cs (P[a/x] ∖ cs)  otherwise   (a mix)
--
-- Whether `A ∩ cs` (restricted to the *enabled* events of `fP`) is empty is
-- NOT decidable from `fP`, `cs`, `dec` alone: it quantifies over every event
-- type and every value.  Yet the `ndbr` node used for the internal choice
-- demands a non-emptiness witness, so this case split is unavoidable.  We
-- therefore take it as a parameter `hdec`: for any visible continuation it
-- decides whether some hidden event is enabled and, in the `yes` case, hands
-- back the witnessing `(event , value)` from which the `ndbr` witness is built.
-- `hdec` is dischargeable by the caller for concrete (e.g. finite/decidable)
-- alphabets.
--
-- This operator is *productive* (no NON_TERMINATING pragma).  Guardedness is
-- satisfied by keeping every corecursive call `_ ∖ cs ¿ dec ¿ hdec`
-- syntactically under a constructor (`sil`, `just`, `mix`'s timeout tree, the
-- `ndbr` branch function), routed only through FORWARD-DECLARED, in-clique
-- named helpers (`hVis`/`hInner`/`hWit`/`hNd`/`hWitNd`/`hBr2`) — never through
-- `case_of_`/`λ where`/`_⊓_`/`where`-bound helpers, which the guardedness
-- checker cannot see past.  The merged internal choice in the `mix`-yes case
-- (`(⨅ hidden) ⊓ (Q' ∖ cs)`) is built by hand as ONE `ndbr` node rather than
-- via `_⊓_`.

-- The hiding operator.
_∖_¿_¿_ :
  ∀ {ℓr} {R : Set ℓr}
  → {{ DecEq R }}
  → ITree E (ExtI E) R
  → (cs  : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
          → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
  → ITree E (ExtI E) R

-- Hide a single (Maybe) continuation.  Corecursion sits under `just`, reached
-- by DIRECT clause matching (NOT a `with`): a `with` on the corecursive path
-- spawns an out-of-clique auxiliary the guardedness checker cannot see past, so
-- every arm that carries `_ ∖ cs ¿ dec ¿ hdec` routes through this helper.
hCont : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
      → (cs  : AnyTypes E → Set)
      → (dec : (at : AnyTypes E) → Dec (cs at))
      → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
              → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
      → Maybe (ITree E (ExtI E) R) → Maybe (ITree E (ExtI E) R)

-- Non-hidden visible offers, with hiding propagated into each continuation.
-- Hidden events are dropped here (they reappear as τ branches below).
-- Corecursion sits under `just`.
hVis : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
     → (cs  : AnyTypes E → Set)
     → (dec : (at : AnyTypes E) → Dec (cs at))
     → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
             → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
     → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
     → (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R))

-- ⨅ a : A ∩ cs @ (P[a/x] ∖ cs) : the internal choice over hidden, enabled events.
-- Corecursion sits under `just`.
hInner : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
       → (cs  : AnyTypes E → Set)
       → (dec : (at : AnyTypes E) → Dec (cs at))
       → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
               → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
       → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
       → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (ITree E (ExtI E) R))

-- The `hdec`-supplied witness (a hidden, enabled event) inhabits `hInner`.
-- The `DecEq` instance is named (`deq`) and passed explicitly to `hInner` in
-- the result type, since instance resolution does not fire inside a signature.
hWit : ∀ {ℓr} {R : Set ℓr} → {{ deq : DecEq R }}
     → (cs  : AnyTypes E → Set)
     → (dec : (at : AnyTypes E) → Dec (cs at))
     → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
             → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
     → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
     → ∀ {A} {e : E A} {a : A}
     → cs (A , e) → Is-just (fP (A , e) a)
     → Is-just (hInner {{ deq }} cs dec hdec fP (A , base e) a)

-- Hiding distributes through an internal choice: each branch is hidden.
-- Corecursion sits under `just`.
hNd : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
    → (cs  : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
            → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
    → (fP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (ITree E (ExtI E) R)))
    → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (ITree E (ExtI E) R))

-- Witness preservation for the `ndbr`-distribute case.
hWitNd : ∀ {ℓr} {R : Set ℓr} → {{ deq : DecEq R }}
       → (cs  : AnyTypes E → Set)
       → (dec : (at : AnyTypes E) → Dec (cs at))
       → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
               → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
       → (fP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (ITree E (ExtI E) R)))
       → ∀ {wi wa} → Is-just (fP wi wa) → Is-just (hNd {{ deq }} cs dec hdec fP wi wa)

-- The binary internal-choice branch function for the `mix`-yes case: a hand-made
-- `br2` (an inlined `_⊓_`) whose two branches are (0) the internal choice over
-- the hidden, enabled events and (1) the hidden timeout continuation `Q'`.
--
-- CRUCIAL for guardedness: the corecursive calls must appear *syntactically
-- under `just` inside this branch function's own clauses*.  Passing an
-- already-built `Q' ∖ …` (or a pre-built inner tree containing `_ ∖ …`) as an
-- ARGUMENT to the branch function defeats the checker — it cannot see that the
-- argument ends up under a constructor.  So `hBr2` takes the RAW ingredients
-- (`fP`, the witnessing `e`/`a`, the proofs, and `Q'`) and reconstructs both
-- branches here, each under `just`.
hBr2 : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
     → (cs  : AnyTypes E → Set)
     → (dec : (at : AnyTypes E) → Dec (cs at))
     → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
             → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
     → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
     → ∀ {A} (e : E A) (a : A) → cs (A , e) → Is-just (fP (A , e) a)
     → (Q' : ITree E (ExtI E) R)
     → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (ITree E (ExtI E) R))

-- The `vis fP` node of the hidden process: a pure `vis` when no hidden event is
-- enabled, otherwise a `mix` whose timeout is the internal choice over the
-- hidden, enabled events.  Lifted to a top-level in-clique helper so the
-- recursive `force` body does NOT nest a `with hdec fP` under `with P .force`
-- (a nested `with` generates an out-of-clique auxiliary the guardedness checker
-- cannot see past).
hStepVis : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
         → (cs  : AnyTypes E → Set)
         → (dec : (at : AnyTypes E) → Dec (cs at))
         → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
                 → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
         → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
         → NodeKind E (ExtI E) R

-- The `mix fP Q'` node of the hidden process: a `mix` whose timeout is `Q'`
-- hidden, merged (via a hand-built binary `ndbr`, i.e. an inlined `_⊓_`) with
-- the internal choice over hidden, enabled events when one is present.
hStepMix : ∀ {ℓr} {R : Set ℓr} → {{ DecEq R }}
         → (cs  : AnyTypes E → Set)
         → (dec : (at : AnyTypes E) → Dec (cs at))
         → (hdec : (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
                 → Dec (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] (cs at × Is-just (fP at a))))
         → (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI E) R)))
         → (Q' : ITree E (ExtI E) R)
         → NodeKind E (ExtI E) R

-- Definitions ----------------------------------------------------------------

hCont cs dec hdec nothing    = nothing
hCont cs dec hdec (just P')   = just (P' ∖ cs ¿ dec ¿ hdec)

hVis cs dec hdec fP at a with dec at
... | yes _ = nothing                       -- hidden: removed from vis
... | no  _ = hCont cs dec hdec (fP at a)

hInner cs dec hdec fP (A , base e) a with dec (A , e)
... | no  _ = nothing                       -- not hidden: not an internal branch
... | yes _ = hCont cs dec hdec (fP (A , e) a)
hInner cs dec hdec fP (A , pair _ _) a = nothing
hInner cs dec hdec fP (A , fin)      a = nothing

hWit cs dec hdec fP {A} {e} {a} csp isj with dec (A , e)
... | no ¬p = ⊥-elim (¬p csp)
... | yes _ with fP (A , e) a | isj
...   | just _  | _  = any-just tt₀

hNd cs dec hdec fP i a = hCont cs dec hdec (fP i a)

hWitNd cs dec hdec fP {wi} {wa} p with fP wi wa | p
... | just _  | _  = any-just tt₀

hBr2 cs dec hdec fP e a csp isj Q' (_ , fin) (lift fzero) =
  just (itree (ndbr (hInner cs dec hdec fP) (_ , base e) a (hWit cs dec hdec fP csp isj)))
hBr2 cs dec hdec fP e a csp isj Q' (_ , fin) (lift (fsuc fzero))    = just (Q' ∖ cs ¿ dec ¿ hdec)
hBr2 cs dec hdec fP e a csp isj Q' (_ , fin) (lift (fsuc (fsuc _))) = nothing
hBr2 cs dec hdec fP e a csp isj Q' (_ , base _)   _ = nothing
hBr2 cs dec hdec fP e a csp isj Q' (_ , pair _ _) _ = nothing

-- visible choice: pure vis when nothing hidden is enabled, else a mix.
hStepVis cs dec hdec fP with hdec fP
... | no  _ = vis (hVis cs dec hdec fP)
... | yes ((A , e) , a , csp , isj) =
        mix (hVis cs dec hdec fP)
            (itree (ndbr (hInner cs dec hdec fP) (A , base e) a
                         (hWit cs dec hdec fP csp isj)))

-- mix: the existing τ-timeout to Q' is always a witness, so the internal choice
-- over hidden events (when present) is merged in via a hand-built `ndbr` (the
-- inlined `_⊓_`) instead of calling `_⊓_` on the corecursive `Q'`.
hStepMix cs dec hdec fP Q' with hdec fP
... | no  _ = mix (hVis cs dec hdec fP) (Q' ∖ cs ¿ dec ¿ hdec)
... | yes ((A , e) , a , csp , isj) =
        mix (hVis cs dec hdec fP)
            (itree (ndbr (hBr2 cs dec hdec fP e a csp isj Q')
                         (Lift ℓ (Fin 2) , fin) (lift fzero) (any-just tt₀)))

force (_∖_¿_¿_ {ℓr = ℓr} {R = R} P cs dec hdec) with P .force
... | sil P'           = sil (P' ∖ cs ¿ dec ¿ hdec)
... | ret r            = ret r
... | vis fP           = hStepVis cs dec hdec fP
... | ndbr fP wi wa wp = ndbr (hNd cs dec hdec fP) wi wa (hWitNd cs dec hdec fP wp)
... | mix fP Q'        = hStepMix cs dec hdec fP Q'
