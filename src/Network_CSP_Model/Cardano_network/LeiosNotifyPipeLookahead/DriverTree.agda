{-# OPTIONS --guardedness #-}

-- Exact finite-prefix PTree for the generic paired driver-record product.
-- Infinite callback input domains are retained; this is not a finite search algorithm.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.DriverTree
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Maybe using (nothing)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
open import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification Return notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.OperationalTree

-- Paired prefix semantics has no global return rule; endpoint results remain in state.
module Native (contract : S.Contract) =
  Cardano_network.LeiosNotifyPipeLookahead.OperationalTree
    State Event Exec.Choice ⊥ (Step contract) (Tau contract)
    (λ s e → Exec.lookup contract e s) (Exec.hidden contract)
    Exec.next-complete Exec.hidden-complete
    (λ _ → nothing) (λ _ → refl) (λ _ → refl)

-- Fresh paired entry point before either endpoint acts or any channel packet exists.
driverTree : (contract : S.Contract) → Native.Proc contract
driverTree contract = Native.tree contract initial
