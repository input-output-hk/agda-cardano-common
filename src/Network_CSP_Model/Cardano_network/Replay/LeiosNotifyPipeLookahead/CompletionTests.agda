{-# OPTIONS --safe #-}

-- Universal flush counts, occupied-source corrections, finite-prefix controls and low-occupancy growth.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CompletionTests where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Function using (_$_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.Properties Bool as Old
import Cardano_network.LeiosNotifyPipeLookahead.CompletionAccounting Bool as Count
import Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver Bool Bool as Paired
import Cardano_network.LeiosNotifyPipeLookahead.SequentialCompletion Bool true as Family
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Bool as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Bool as Projection
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as Driver
import Cardano_network.LeiosNotifyPipeLookahead.CompletionDriver Bool ⊤ as NodeCount
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Bool ⊤ as Steps
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingTests as Sent
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainTests as PairedExample

-- Already completed idle jobs need exactly that many flushes in every successful schedule.
idle-universal : ∀ {p actions n} (run : S.Run p (S.state S.flushing 0 S.idle n true) actions
  (S.state S.closed 0 S.idle 0 true)) → Count.flushes run ≡ n
idle-universal run = Count.shutdown-flushes run refl

-- The pre-existing constructed witness inhabits this universal exact-count result.
idle-example : Count.flushes (Old.drain-completed {S.nodeNext} 3) ≡ 3
idle-example = idle-universal (Old.drain-completed {S.nodeNext} 3)

-- A sent response still needs a retirement and one flush, despite zero completed/owed at start.
sent-drain : S.Run S.nodeNext Sent.unretired (S.sendDone ∷ []) (S.state S.closed 0 S.idle 0 true)
sent-drain = S.internal (S.retire refl) (Old.drain-completed 1)

-- The naive zero-owed/zero-completed resource test misses this real flush obligation.
sent-work : Count.work Sent.unretired ≡ 1
sent-work = refl

-- Every successful continuation from the freshly reachable unretired state has one flush.
sent-universal : ∀ {p actions} (run : S.Run p Sent.unretired actions (S.state S.closed 0 S.idle 0 true)) →
  Count.flushes run ≡ 1
sent-universal run = Count.shutdown-flushes run refl

-- That obligation has an actual finite closing witness and an exact retirement count.
sent-example : Count.flushes sent-drain ≡ 1
sent-example = sent-universal sent-drain

-- Reply Send itself did not publish this completion token; retirement does so once.
sent-retirement : Count.retirements sent-drain ≡ 1
sent-retirement = refl

-- Two unanswered jobs coexist with three older completed tokens in this source state.
mixed : S.State
mixed = S.state S.flushing 1 S.claimed 3 true

-- The mixed state is reachable from a fresh server, with the last two callbacks canceled by Quit.
mixed-prefix : Σ[ actions ∈ List S.Action ] S.Run S.nodeNext S.initial actions mixed
mixed-prefix with Old.completed-reachable true 2
... | actions , run = _ , S.append run (
  S.visible (S.receiveRequest S.atNext) $
  S.internal S.admitted $
  S.internal S.registered $
  S.internal (S.claim refl) $
  S.visible (S.receiveRequest S.atNext) $
  S.internal S.admitted $
  S.internal S.registered $
  S.visible (S.receiveQuit S.atNext) $
  S.internal S.setQuit S.stop)

-- The two active obligations retire before the five resulting completions are flushed.
mixed-drain : S.Run S.nodeNext mixed (S.sendReply S.canceled ∷ S.sendReply S.canceled ∷ S.sendDone ∷ [])
  (S.state S.closed 0 S.idle 0 true)
mixed-drain =
  S.internal (S.cancel refl) $
  S.visible (S.send refl) $
  S.internal (S.retire refl) $
  S.internal (S.claim refl) $
  S.internal (S.cancel refl) $
  S.visible (S.send refl) $
  S.internal (S.retire refl) (Old.drain-completed 5)

-- Every successful schedule at this mixed boundary flushes three historical plus two pending jobs.
mixed-universal : ∀ {p actions} (run : S.Run p mixed actions (S.state S.closed 0 S.idle 0 true)) →
  Count.flushes run ≡ 5
mixed-universal run = Count.shutdown-flushes run refl

-- The actual witness has five flushes and two new retirements, preserving the token equation.
mixed-count : Count.flushes mixed-drain ≡ 5
mixed-count = mixed-universal mixed-drain

-- Initial three tokens plus two retirements equal five consumed tokens.
mixed-tokens : 3 Data.Nat.+ Count.retirements mixed-drain ≡ Count.flushes mixed-drain
mixed-tokens = refl

-- Closing fourteen source operations include the five mandatory flush transitions.
mixed-steps : Count.steps mixed-drain ≡ 14
mixed-steps = refl

-- A finite EOF prefix with seven retained tokens may perform no flush at all.
prefix-only : S.Run S.nodeNext (S.state S.flushing 0 S.idle 7 true) [] (S.state S.flushing 0 S.idle 7 true)
prefix-only = S.stop

-- The closure premise cannot be replaced by merely accepting a finite prefix.
prefix-count : Count.flushes prefix-only ≡ 0
prefix-count = refl

-- The paired cancellation example flushes one server job while the client is still draining.
paired-count : Paired.flushes PairedExample.drain ≡ 1
paired-count = Paired.shutdown-flushes PairedExample.drain refl refl

-- Every intermediate state of the concrete production-policy family has eight actual inequalities.
all-prefix-bounds : ∀ n → Family.AllBounds (Family.prefix n)
all-prefix-bounds = Family.prefix-bounds

-- The occupancy-one guarantee also holds during the unbounded flush phase and full closure.
all-full-bounds : ∀ n → Family.AllBounds (Family.full n)
all-full-bounds = Family.full-bounds

-- Each chosen finite history has exactly n completed tokens and a successful n-flush shutdown.
family-count : ∀ n → NodeCount.flushes (Projection.driver (Family.shutdown (Family.reading n) n)) ≡ n
family-count n = Family.shutdown-count (Family.reading n) n

-- The full selected paired shutdown has an exact fixed overhead beyond its n flushes.
family-steps : ∀ n → Steps.steps (Projection.driver (Family.shutdown (Family.reading n) n)) ≡ n Data.Nat.+ 12
family-steps n = Family.shutdown-steps (Family.reading n) n

-- A three-token instance has three flushes and fifteen total paired operations.
three-steps : Steps.steps (Projection.driver (Family.shutdown (Family.reading 3) 3)) ≡ 15
three-steps = family-steps 3

-- Pipeline occupancy one cannot supply any constant bound on retained completion history.
unbounded : ∀ bound → Family.AllSmall (Family.prefix (Data.Nat.suc bound)) ×
  bound < S.completed (Driver.serverState (Node.driverState (Family.ready S.awaitNext (Data.Nat.suc bound))))
unbounded bound with Family.unbounded-completions bound
... | small , empty-client , empty-owed , larger = small , larger
