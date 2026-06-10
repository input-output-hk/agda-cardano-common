{-
  Aggregator module re-exporting trace lemmas from per-operator files.

  Historical clients that `open import CSP.Laws.Traces …` continue to
  work via the `open … public` chain below.  Each per-operator module
  bundles trace + FD + DRBisim lemmas; opening them here makes the
  full surface accessible from this module.  See
  docs/superpowers/specs/2026-05-15-csp-laws-per-operator-split-design.md
  for the trade-off this entails.
-}

{-# OPTIONS --guardedness #-}

open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Interaction_Trees

module CSP.Laws.Traces
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open import CSP.Laws.BasicProcesses {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.Prefix         {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.InternalChoice {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.ExternalChoice {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.Sliding        {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.Bind           {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.Parallel       {ℓ} {ℓe} {E} E-≟ public
open import CSP.Laws.Iterate        {ℓ} {ℓe} {E} E-≟ public
