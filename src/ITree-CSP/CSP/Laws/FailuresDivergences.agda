{-
  This module proves failures and divergences laws for CSP processes,
  mirroring the structure of `CSP.Laws.Traces`. The underlying definitions
  of `_ref_`, `failures`, `_⊑F_`, `divergences`, `failures⊥`, `_⊑D_`,
  and `_⊑FD_` live in `ITree_Relations.FailuresDivergences`.
-}

{-# OPTIONS --guardedness #-}

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤′; tt to tt′)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.List.Membership.Propositional as ListMem
open ListMem using (_∈_; _∉_)
open import Class.DecEq using (DecEq)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open import Data.Maybe.Properties using (just-injective)

module CSP.Laws.FailuresDivergences
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces
open Failures

-- Trace helpers from CSP.Laws.Traces (Stop-no-τ, Stop-no-ev, Stop-no-steps, Ret-trace, …).
import CSP.Laws.Traces {ℓ} {ℓe} {E} E-≟ as TR
open TR

-- CSP operators (Prefix, _□_, _⊓_, _▷_, _>>=_, …) parameterised by E-≟.
import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟



-----------------------------------------------------------------------------------------
-- External choice  P □ Q
-- The FD theory of `_□_` lives in `CSP.Laws.ExternalChoice_FD`: refusal
-- iff for `P □ P`, lift/project of failures/divergences/failures⊥ between
-- `P` and `P □ P`, and the FD-only idempotence law `□-idem-FD`.  We
-- re-export the public names here.

import CSP.Laws.ExternalChoice_FD {ℓ} {ℓe} {E} as □-FD
open □-FD E-≟ public using
  ( □-comm-FD
  ; □P-ref-iff
  ; failures-lift-PP
  ; failures-project-PP
  ; divergences-lift-PP
  ; divergences-project-PP
  ; failures⊥-lift-PP
  ; failures⊥-project-PP
  ; □-idem-FD
  )

-----------------------------------------------------------------------------------------
-- Internal choice  P ⊓ Q
-- The bulk of the FD theory of `_⊓_` lives in `CSP.Laws.InternalChoice_FD`:
-- step lemmas, sum decomposition of failures/divergences/failures⊥, and
-- the FD-only associativity law `⊓-assoc-FD` (which fails under DRWbisim).
-- We re-export the public names here.

import CSP.Laws.InternalChoice_FD {ℓ} {ℓe} {E} as ⊓-FD
open ⊓-FD E-≟ public using
  ( ⊓-step-L
  ; ⊓-step-R
  ; ⊓-failures-introL
  ; ⊓-failures-introR
  ; ⊓-failures-elim
  ; ⊓-divergences-introL
  ; ⊓-divergences-introR
  ; ⊓-divergences-elim
  ; ⊓-failures⊥-introL
  ; ⊓-failures⊥-introR
  ; ⊓-failures⊥-elim
  ; ⊓-assoc-FD
  ; ⊓-comm-FD
  ; ⊓-idem-FD
  )

-----------------------------------------------------------------------------------------
-- Sliding  P ▷ Q
-- The FD theory of `_▷_` lives in `CSP.Laws.Sliding`: step lemmas
-- (under the `Q-not-ndbr` precondition exposing the P-shape clauses),
-- the Q-ndbr distribution step, big-step decomposition, and the full
-- failures/divergences/failures⊥ elim+intro families.  The sole
-- postulate touching `_▷_` (`divergent-▷-asymm-project`, a König-style
-- step in the divergence base case) lives in `CSP.Laws.Sliding`.  We
-- re-export the public names here.

import CSP.Laws.Sliding {ℓ} {ℓe} {E} as ▷-FD
open ▷-FD E-≟ public using
  ( ▷-step-sil-τ
  ; ▷-step-ret-√
  ; ▷-step-vis-τ-R
  ; ▷-step-ndbr-τ-L
  ; ▷-step-Q-ndbr
  ; ▷-never-stable
  ; ▷-force-never-vis
  ; ▷BigStepSplit
  ; ▷-bigstep-decomp
  ; ▷-failures-elim
  ; ▷-failures-introP-vis
  ; ▷-failures-introP-sRet
  ; ▷-failures-introQ-slide
  ; ▷-divergences-elim
  ; ▷-divergences-introP
  ; ▷-divergences-introQ-slide
  ; divergent-▷-asymm-project
  ; ▷-failures⊥-elim
  ; ▷-failures⊥-introP-vis
  ; ▷-failures⊥-introP-sRet
  ; ▷-failures⊥-introQ-slide
  ; ▷-failures⊥-introP-Divergent
  ; ▷-failures⊥-introQ-Divergent-slide
  )

-----------------------------------------------------------------------------------------
-- Iterate  loop / loop0 / loopc / while
-- The FD theory of the iterators lives in `CSP.Laws.Iterate`: trace
-- characterization (`*-trace`, `*-trace-intro`), algebraic identities
-- (`*-unfold-T`, `loopc≡loop0`), failures/divergences/failures⊥
-- elim+intros, and ⊑ᵀ / ⊑F⊥ / ⊑FD monotonicity.  We re-export the
-- public names here.

import CSP.Laws.Iterate {ℓ} {ℓe} {E} as Iter-Laws
open Iter-Laws E-≟ public using
  -- characterization data types
  ( LoopSplit ; WhileSplit ; Loop0Split ; LoopcSplit
  ; LoopFailureSplit ; WhileFailureSplit
  ; Loop0FailureSplit ; LoopcFailureSplit
  ; LoopDivergenceSplit ; WhileDivergenceSplit
  ; Loop0DivergenceSplit ; LoopcDivergenceSplit
  -- trace elim/intro
  ; loop-trace  ; loop-trace-intro
  ; loop0-trace ; loop0-trace-intro
  ; loopc-trace ; loopc-trace-intro
  ; while-trace ; while-trace-intro
  -- algebraic identities
  ; loop-unfold-T-fwd ; loop-unfold-T-bwd
  ; loop0-unfold-T-fwd ; loop0-unfold-T-bwd
  ; loopc-unfold-T-fwd ; loopc-unfold-T-bwd
  ; while-unfold-T-fwd ; while-unfold-T-bwd
  ; loopc≡loop0
  -- failures elim/intro
  ; loop-failures-elim  ; loop-failures-intro
  ; loop0-failures-elim ; loop0-failures-intro
  ; loopc-failures-elim ; loopc-failures-intro
  ; while-failures-elim ; while-failures-intro
  -- divergences elim/intro
  ; loop-divergences-elim  ; loop-divergences-intro
  ; loop0-divergences-elim ; loop0-divergences-intro
  ; loopc-divergences-elim ; loopc-divergences-intro
  ; while-divergences-elim ; while-divergences-intro
  -- failures⊥ elim/intros
  ; loop-failures⊥-elim  ; loop-failures⊥-intro-failures
  ; loop-failures⊥-intro-divergent
  ; loop0-failures⊥-elim ; loop0-failures⊥-intro-failures
  ; loop0-failures⊥-intro-divergent
  ; loopc-failures⊥-elim ; loopc-failures⊥-intro-failures
  ; loopc-failures⊥-intro-divergent
  ; while-failures⊥-elim ; while-failures⊥-intro-failures
  ; while-failures⊥-intro-divergent
  -- monotonicity (⊑ᵀ family stays here; the loop-/loop0-/loopc-/while-
  -- F⊥/D/FD names are re-exported from `CSP.Laws.Iterate_FD` below,
  -- which assembles them atop the bisim-based `*-mono-*-via-bisim`.)
  ; loop-mono-⊑ᵀ
  ; loop0-mono-⊑ᵀ
  ; loopc-mono-⊑ᵀ
  ; while-mono-⊑ᵀ
  )

import CSP.Laws.Iterate_FD {ℓ} {ℓe} {E} as Iter-FD-Laws
open Iter-FD-Laws E-≟ public using
  ( loop-mono-⊑F⊥  ; loop-mono-⊑D ; loop-mono-⊑FD
  ; loop0-mono-⊑F⊥ ; loop0-mono-⊑FD
  ; loopc-mono-⊑F⊥ ; loopc-mono-⊑FD
  ; while-mono-⊑F⊥ ; while-mono-⊑D ; while-mono-⊑FD
  )

