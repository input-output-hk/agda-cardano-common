{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- SANITY INSTANCE (Task 6).  Instantiate the GENERAL, payload-parametric
-- refinement `NetworkRefinementGenExp` at `Data := ⊤`, recovering the
-- original `Data = ⊤` headline result `Network ≈FD CopySpec`.
--
-- This certifies the generalisation is conservative: the abstract `Data`
-- module, fed the unit payload, reproduces the concrete `NetworkRefinement`
-- result.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.NetworkVerification.NetworkRefinementGenSanity where

open import Data.Unit using (⊤; tt)
open import Class.DecEq using (DecEq)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (refl)

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

open import CSP.Examples.Cardano_network.NetworkVerification.NetworkRefinementGenExp ⊤

-- Re-export the headline result at `Data := ⊤` as a sanity check.  The
-- general results take an arbitrary payload `(d : Data)`; here `Data = ⊤`,
-- so we feed the unique inhabitant `tt`.
_ = net≈FD tt
