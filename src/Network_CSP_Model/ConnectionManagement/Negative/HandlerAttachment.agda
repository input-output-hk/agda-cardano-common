{-# OPTIONS --guardedness #-}

-- Each previously demonstrated malformed attachment violates an explicit
-- creation premise. Successful attachment alone cannot discharge that premise.
module ConnectionManagement.Negative.HandlerAttachment where

open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerAttachment
open import ConnectionManagement.Negative.HandlerReferences using (wrongKey; missingEntry; missingSocket)
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀; key₁)

wrong-key-no-premises : ¬ CreationPremises child₀ (world wrongKey) (inboundGovernor wrongKey)
wrong-key-no-premises premises = different (coherent premises _ _ _ _ _ refl refl refl refl)
  where
  different : ¬ (key₁ ≡ key₀)
  different ()

missing-entry-no-premises : ¬ CreationPremises child₀ (world missingEntry) (inboundGovernor missingEntry)
missing-entry-no-premises premises with resources premises _ refl
... | (_ , ()) , _

missing-socket-no-premises : ¬ CreationPremises child₀ (world missingSocket) (inboundGovernor missingSocket)
missing-socket-no-premises premises with resources premises _ refl
... | _ , (_ , ())
