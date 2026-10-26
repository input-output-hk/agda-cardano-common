{-# OPTIONS --guardedness #-}

-- Existing prepared/published reference chains through every combined action.
-- These are historical table lookups, not source object-lifetime claims.
module ConnectionManagement.Properties.SubsystemReferences where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerReferences using (Chain)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Inbound
import ConnectionManagement.Properties.HandlerStateRetention as StateChain
import ConnectionManagement.Properties.HandlerTableRetention as Tables
import ConnectionManagement.Properties.StateRetention as State
import ConnectionManagement.Properties.IGTableRetention as Table
open import ConnectionManagement.Properties.SharedStateEffects using (to-retains; identity)
import ConnectionManagement.Properties.OutboundWorldInvariant as Runtime
import ConnectionManagement.Properties.SubsystemWorldInvariant as Combined

-- Recover the nested state and IG observations without changing the machine.
shared : Sub.Configuration → S.State
shared c = I.world (O.core (J.cm (Sub.world c)))
governor : Sub.Configuration → IG.Runtime
governor c = I.inboundGovernor (O.core (J.cm (Sub.world c)))

-- Preparation has no publication premise; it retains the original handle
-- descriptor and permits dynamic changes to a mux with the same connection key.
module PreparedFor (w : WorkerId) (hid : HandleId) (mid : MuxId) where
  Predicate : S.State → IG.Runtime → Set
  Predicate = Prepared w hid mid
  stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Table.Retains ig ig′ →
    Predicate s ig → Predicate s′ ig′
  stable = Inbound.prepared-retained
  ig-stable : ∀ {s ig ig′} → Table.Retains ig ig′ → Predicate s ig → Predicate s ig′
  ig-stable {s} eff p = stable (to-retains {s = s} {s′ = s} (identity s)) eff p
  module Outbound = Runtime.Lift Predicate stable
  open Combined.Lift Predicate Outbound.advance-preserves ig-stable public

-- Published chains also retain the exact stored promise result, independently
-- of current map membership, IG registration, or handler lifecycle phase.
module ChainFor (w : WorkerId) (mid : MuxId) where
  Predicate : S.State → IG.Runtime → Set
  Predicate = Chain w mid
  stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Table.Retains ig ig′ →
    Predicate s ig → Predicate s′ ig′
  stable state tables chain = Tables.retains-chain tables (StateChain.retains-chain state chain)
  ig-stable : ∀ {s ig ig′} → Table.Retains ig ig′ → Predicate s ig → Predicate s ig′
  ig-stable = Tables.retains-chain
  module Outbound = Runtime.Lift Predicate stable
  open Combined.Lift Predicate Outbound.advance-preserves ig-stable public

-- The public APIs retain the old predicates with no added structural premise.
prepared-step : ∀ a c {c′ w hid mid} → Sub.advance a c ≡ just c′ →
  Prepared w hid mid (shared c) (governor c) → Prepared w hid mid (shared c′) (governor c′)
prepared-step a c {w = w} {hid} {mid} = PreparedFor.advance-preserves w hid mid a c
chain-step : ∀ a c {c′ w mid} → Sub.advance a c ≡ just c′ →
  Chain w mid (shared c) (governor c) → Chain w mid (shared c′) (governor c′)
chain-step a c {w = w} {mid} = ChainFor.advance-preserves w mid a c
prepared-exec : ∀ {c actions c′ w hid mid} → Sub.Executes c actions c′ →
  Prepared w hid mid (shared c) (governor c) → Prepared w hid mid (shared c′) (governor c′)
prepared-exec {w = w} {hid} {mid} path p = PreparedFor.exec-preserves w hid mid p path
chain-exec : ∀ {c actions c′ w mid} → Sub.Executes c actions c′ →
  Chain w mid (shared c) (governor c) → Chain w mid (shared c′) (governor c′)
chain-exec {w = w} {mid} path chain = ChainFor.exec-preserves w mid chain path
