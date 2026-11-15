{-# OPTIONS --guardedness #-}

-- Full initialized stage-2 candidates, rather than their reached local windows.
module ConnectionManagement.Exploration.MinimiseCandidates where
open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just; nothing; is-just)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain using (DecEq-Id)
import ConnectionManagement.Exploration.Minimise as Minimise
import ConnectionManagement.OutboundMachine as Outbound
import ConnectionManagement.Negative.ServerLateAdmission as Late
import ConnectionManagement.Negative.ServerAdmission as Prefix
import ConnectionManagement.Negative.ServerOwnedWorkersSelfPurge as Purge
import ConnectionManagement.Negative.ForeignCallerResidue as Foreign
import ConnectionManagement.Negative.ServerAdmissionPrefixSupport as Support
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.CMShutdown as CM
import ConnectionManagement.Rules.PoolRelays as RR

-- Instantiate only the actual dispatchers; search proofs are not runtime inputs.
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerPeersRelays as Outer
import ConnectionManagement.Variants.ServerOwnedWorkers as Workers
import ConnectionManagement.Variants.ServerOwnedHandlers as Handlers
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as P
import ConnectionManagement.Negative.PoolRelays as R
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
module L where
  module S = Server I.bearerClosed
module S where
  module W = Workers.Protocols I.bearerClosed Purge.classify Purge.capability
  module V = Handlers.Protocols I.bearerClosed Purge.classify Purge.capability
module F where
  module O = Outer.Protocols I.bearerClosed P.classify Protocols.capability
  module B where
    module T = O.V
  start : O.Outer
  start = O.outer Protocols.initial (RR.initial true)
  actions : List O.OuterAction
  actions = map O.innerAct Foreign.innerActions ++ R.Initialized.closeActions

indices : ℕ → ℕ → List ℕ
indices from zero = []
indices from (suc n) = from ∷ indices (suc from) n

module LateCase where
  actions : List L.S.Action
  actions = Prefix.allActions ++ Late.lateActions
  violation : L.S.State → Bool
  violation s with L.S.stage s | CM.phase (Late.coordinator s)
    | CM.snapshot (Late.coordinator s) | CM.collected (Late.coordinator s)
  ... | L.S.serverReturned | CM.closed | [] | [] = is-just (lookup A.child₁ (Support.physicalThreads s))
  ... | _ | _ | _ | _ = false
  module M = Minimise L.S.State L.S.Action L.S.step actions Prefix.start violation
  original : List ℕ
  original = indices 0 (length actions)
  reduced : List ℕ
  reduced = M.coarse 12 (length original) original

module PurgeCase where
  actions : List S.W.OuterAction
  actions = Purge.actions
  violation : S.W.Outer → Bool
  violation s with CM.phase (Purge.coord s) | RR.owner (S.W.relays s)
  ... | CM.closed | RR.finished = is-just (lookup A.child₀ (S.V.threads (S.W.inner s))) ∧
    not (S.V.ready (S.W.inner s) A.child₀)
  ... | _ | _ = false
  module M = Minimise S.W.Outer S.W.OuterAction S.W.outerStep actions Purge.start violation
  original : List ℕ
  original = indices 0 (length actions)
  reduced : List ℕ
  reduced = M.coarse 12 (length original) original

module ForeignCase where
  actions : List F.O.OuterAction
  actions = F.actions
  violation : F.O.Outer → Bool
  violation s with RR.owner (F.O.relays s)
  ... | RR.finished = is-just (lookup Foreign.foreignWorker (Outbound.acquiring (F.B.T.sourceOf (F.O.inner s))))
  ... | _ = false
  module M = Minimise F.O.Outer F.O.OuterAction F.O.outerStep actions F.start violation
  original : List ℕ
  original = indices 0 (length actions)
  reduced : List ℕ
  reduced = M.coarse 12 (length original) original

-- Executable bounded examples only. Shrunk* certifies the separately retained
-- external-loop results; no compilation backend is needed or used.
results : List (List ℕ)
results = (length LateCase.original ∷ LateCase.reduced) ∷
  (length PurgeCase.original ∷ PurgeCase.reduced) ∷
  (length ForeignCase.original ∷ ForeignCase.reduced) ∷ []
