{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Constructive accessibility under τ-steps.
--
-- `τ-Acc t` is the (inductive) accessibility predicate for the *backwards*
-- τ-transition relation: `t` is τ-accessible iff every τ-successor is.  It is
-- the well-foundedness certificate that τ-normalisation of a process
-- TERMINATES; unlike a postulated divergence-freedom hypothesis it REDUCES, so
-- it can drive well-founded recursion (this is Layer 3's whole point).
--
-- MOVED: the definitions now live in `Semantics.DivergenceFree`, the single home
-- of the divergence-freedom calculus, next to the leaf certificates
-- (`stable→τ-Acc`, `ret→τ-Acc`, `sil→τ-Acc`) and `DivergenceFree` itself.  This
-- module re-exports them verbatim so any existing importer keeps working.
--
-- The `--safe` pragma this module used to carry has been dropped: `--safe` is
-- CO-infective, and `Process_Trees` / `Semantics.LTS` do not carry it, so the
-- pragma made this module fail to typecheck under a plain `agda` invocation.
-- The content is still `--safe`-clean — check it with
-- `agda --safe Semantics/TauAcc.agda`, which puts every dependency under
-- `--safe` too.
------------------------------------------------------------------------

open import Process_Trees

module Semantics.TauAcc {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Semantics.DivergenceFree {ℓ} {ℓe} {ℓi} {E} {I}
  using (τ-Acc; acc; accSub; τ-Acc→¬Div) public
