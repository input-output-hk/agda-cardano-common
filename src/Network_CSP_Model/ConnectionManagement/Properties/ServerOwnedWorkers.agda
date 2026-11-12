{-# OPTIONS --guardedness #-}

-- Every variant outer run erases to a source run (join labels stutter), so SI5
-- applies without changing its premises or certificate. Global live-handler
-- coverage is not a consequence: see Negative/ServerOwnedWorkersCounterexample.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerOwnedWorkers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Nat using (ℕ)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (HandleId)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Variants.ServerOwnedWorkers as Variant
import ConnectionManagement.Properties.ServerShutdownCoordinator as SI5

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open Variant.Protocols isBearerClosed isIOManagerError canInitiate using
    (module T; Runtime; runtime; source; Outer; outer; Executes; eraseOuter; eraseActions; outer-erasure)
  open SI5.Protocols isBearerClosed isIOManagerError canInitiate using (Complete; complete)

  -- SI5 transports along erasure; the extra labels need no new source axiom.
  si5 : ∀ {c₀ g start scheduled as final handles t} →
    T.initialize (O.initial c₀) g ≡ just start →
    Executes (outer (runtime start []) (RR.initial scheduled)) as
      (outer (runtime final handles) (RR.relaysState t RR.finished)) →
    Complete scheduled final t
  si5 initialized path = complete initialized (outer-erasure path)
