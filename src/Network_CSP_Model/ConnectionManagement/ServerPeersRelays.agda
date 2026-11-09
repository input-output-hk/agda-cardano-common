{-# OPTIONS --guardedness #-}

-- The pool relays scope around the Server/PSA/governor composition. The inner
-- callback has returned when the Server scope reaches serverReturned. Socket
-- closing between that return and the relays cancellation is not modelled.
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import Data.Bool using (Bool)
module ConnectionManagement.ServerPeersRelays
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Rules.PoolRelays as R
private
  module K = Combined isBearerClosed isIOManagerError
  module S = Server isBearerClosed
  module E = Exit isBearerClosed

returned : K.State → Bool
returned s with S.stage (E.base (K.server s))
... | S.serverReturned = true
... | _ = false

returned-of : ∀ s → S.stage (E.base (K.server s)) ≡ S.serverReturned → returned s ≡ true
returned-of s eq rewrite eq = refl

-- The physical-protocol runtime used by the accepted endpoint.
module Protocols (canInitiate : HandleId → ℕ → Bool) where
  module V = K.Protocols canInitiate
  runtimeReturned : V.Runtime → Bool
  runtimeReturned t = returned (V.base t)
  open R.Outer V.advance runtimeReturned public
