{-# OPTIONS --guardedness #-}

-- The actual supervised outer dispatcher, with finite identifier carriers and a
-- maximum-allocation cutoff. This module does not import any witness schedules.
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
module ConnectionManagement.Exploration.Supervised
  (isBearerClosed isIOManagerError : ErrorId → Bool)
  (canInitiate : HandleId → ℕ → Bool) where

open import Data.Nat using (zero; suc; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m)
open import Data.List using (List; []; _∷_; _++_; map; length; foldr)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import ConnectionManagement.Domain using (IdKind; Id; WorkerId; PeerConnectionId; SocketId; PromiseId)
open import ConnectionManagement.Exploration.Finite
open import ConnectionManagement.Exploration.Identities
import ConnectionManagement.CSP.Supervised as Bridge
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as Jobs
import ConnectionManagement.Rules.PoolRelays as Relays
import ConnectionManagement.Exploration.Alphabet as Alphabet
import ConnectionManagement.Exploration.Bounded as Bounded
module B = Bridge isBearerClosed isIOManagerError canInitiate
module O = B.O
module V = B.T
module K = Combined isBearerClosed isIOManagerError
module PS = Supervision isIOManagerError
module S = Server isBearerClosed
module E = Exit isBearerClosed
module A = Alphabet O.Outer O.OuterAction O.outerStep

core : O.Outer → CM.Configuration
core s = V.sourceOf (O.inner s)
shared : O.Outer → Shared.State
shared s = Machine.world (CM.core (core s))
subsystem : O.Outer → Sub.Configuration
subsystem s = PS.machine (K.peers (V.base (O.inner s)))

-- Retain allocated worker keys, plus captures before their stores are installed.
workers : O.Outer → List WorkerId
workers s = map proj₁ (Shared.admissions (shared s)) ++
  map proj₁ (Shared.handlers (shared s)) ++ map proj₁ (Shared.cleanups (shared s)) ++
  map proj₁ (CM.acquiring (core s)) ++ map proj₁ (CM.releasing (core s)) ++
  map proj₁ (S.workers (E.base (K.server (V.base (O.inner s))))) ++
  map proj₁ (V.commands (V.front (O.inner s))) ++
  map proj₁ (V.cursors (V.front (O.inner s))) ++
  map (λ j → Jobs.caller (Sub.execution (proj₂ j))) (Sub.jobs (subsystem s)) ++
  map (λ j → Jobs.child (Sub.execution (proj₂ j))) (Sub.jobs (subsystem s)) ++
  map (λ c → V.owner (proj₂ c)) (V.calls (V.front (O.inner s)))
peers : O.Outer → List PeerConnectionId
peers s = map proj₁ (Jobs.peers (Sub.world (subsystem s))) ++
  map (λ j → Jobs.connectionRef (Sub.execution (proj₂ j))) (Sub.jobs (subsystem s)) ++
  map (λ c → V.peerRef (proj₂ c)) (V.calls (V.front (O.inner s)))
sockets : O.Outer → List SocketId
sockets s = map proj₁ (Shared.sockets (shared s))
promises : O.Outer → List PromiseId
promises s = Shared.promises (shared s)

-- One bound controls typed ID ranges, fresh supplies, and retained store sizes.
-- The final 1 reserves the supervisor slot. Additional limits can be supplied
-- through Bounded without altering the model.
footprint : O.Outer → List ℕ
footprint s = maxIds (workers s) ∷ maxIds (peers s) ∷ maxIds (sockets s) ∷ maxIds (promises s) ∷
  Shared.nextEntry (Shared.cm (shared s)) ∷ Shared.nextPromise (shared s) ∷
  Sub.nextPeer (subsystem s) ∷ Sub.nextJob (subsystem s) ∷
  length (Shared.entries (Shared.cm (shared s))) ∷ length (Shared.sockets (shared s)) ∷
  length (Shared.promises (shared s)) ∷ length (Shared.handlers (shared s)) ∷
  length (Sub.jobs (subsystem s)) ∷ length (V.calls (V.front (O.inner s))) ∷ 1 ∷ []
maximum : List ℕ → ℕ
maximum = foldr _⊔_ 0
allocated : O.Outer → ℕ
allocated s = maximum (footprint s)

-- Finite ID sets are executable declarations, not claims about all small-ID
-- Event constructors. The separately declared event alphabet is the search scope.
workerCarrier : ℕ → List WorkerId
workerCarrier = ids
peerCarrier : ℕ → List PeerConnectionId
peerCarrier = ids
socketCarrier : ℕ → List SocketId
socketCarrier = ids
promiseCarrier : ℕ → List PromiseId
promiseCarrier = ids

maximum-member : ∀ {x xs n} → x ∈ xs → maximum xs ≤ n → x ≤ n
maximum-member {xs = x ∷ xs} here bound = ≤-trans (m≤m⊔n _ _) bound
maximum-member {xs = x ∷ xs} (there member) bound =
  maximum-member member (≤-trans (m≤n⊔m _ _) bound)
worker-bounded : ∀ {s b w} → allocated s ≤ b → w ∈ workers s → w ∈ workerCarrier b
worker-bounded {s} bound member = maxIds-member {xs = workers s} member (maximum-member {xs = footprint s} here bound)
peer-bounded : ∀ {s b p} → allocated s ≤ b → p ∈ peers s → p ∈ peerCarrier b
peer-bounded {s} bound member = maxIds-member {xs = peers s} member (maximum-member {xs = footprint s} (there here) bound)
socket-bounded : ∀ {s b k} → allocated s ≤ b → k ∈ sockets s → k ∈ socketCarrier b
socket-bounded {s} bound member = maxIds-member {xs = sockets s} member (maximum-member {xs = footprint s} (there (there here)) bound)
promise-bounded : ∀ {s b p} → allocated s ≤ b → p ∈ promises s → p ∈ promiseCarrier b
promise-bounded {s} bound member = maxIds-member {xs = promises s} member (maximum-member {xs = footprint s} (there (there (there here))) bound)

-- A declared finite action alphabet is encoded and decoded through G4. All
-- permutations/repetitions over it are explored, including raw relays events.
module Search (candidates : List O.OuterAction) where
  candidateEvents = map B.label candidates
  decodedCandidates = A.decodeAlphabet candidateEvents
  module Engine = Bounded O.Outer O.OuterAction O.outerStep decodedCandidates allocated
  open Engine public

-- Reusable membership certificate for a whole committed native run. The carrier
-- forgets schedule order; all relays branches are added, even when refused.
open import Data.Bool using (true)
open import Data.Maybe using (just)
open import Data.List.Properties using (length-map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
module Witness (initial final : V.Runtime) (schedule : List V.Event) where
  start = O.outer initial (Relays.initial true)
  end = O.outer final (Relays.initial true)
  actions = map O.innerAct schedule
  relaysActions : List O.OuterAction
  relaysActions = map O.relaysAct
    (Relays.requestCancel ∷ Relays.finish ∷
     Relays.threadAct Relays.beginFailure ∷ Relays.threadAct Relays.bodyExit ∷
     Relays.threadAct Relays.publishResult ∷ Relays.threadAct Relays.deliverCancel ∷
     Relays.threadAct Relays.join ∷ [])
  candidates = actions ++ relaysActions
  module Find = Search candidates
  budget = Find.budgetFor start actions
  covered : Covered actions Find.decodedCandidates
  covered rewrite A.encoded-alphabet candidates = covered-left actions relaysActions
  abstract
    found : V.Runs initial schedule final →
      (actions , end) ∈ Find.reach (length actions) budget start
    found run = Find.witness-membership {s = start} {as = actions} {t = end} (B.to-raw (B.lift-run (just Relays.running) run)) covered
    within-length : ∀ n → length schedule ≡ n → V.Runs initial schedule final →
      (actions , end) ∈ Find.reach n budget start
    within-length n count run = subst (λ depth → (actions , end) ∈ Find.reach depth budget start)
      (trans (length-map O.innerAct schedule) count) (found run)
