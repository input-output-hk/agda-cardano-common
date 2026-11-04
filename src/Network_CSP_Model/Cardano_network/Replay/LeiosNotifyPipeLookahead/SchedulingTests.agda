{-# OPTIONS --safe #-}

-- Fresh shutdown runs exercise the operation bound and distinct bookkeeping resources.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Induction.WellFounded using (Acc)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.Properties Bool as Server
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Bool Bool as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Bool Bool as Rank
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Bool Bool as Shutdown
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownTests as Fixture

-- Fresh paired control has constructive hidden accessibility, not an assumed no-livelock premise.
initial-accessible : Acc (λ t s → D.Tau S.nodeNext s t) D.initial
initial-accessible = Rank.tau-accessible S.nodeNext D.initial

-- The earlier fresh server-Done-first witness leaves exactly this reachable client drain.
closed : D.State
closed = D.pair (C.client C.closed C.idle [] [] 0 (+ 1) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- Client processing consumes the queued cancellation, marker and final Done.
finish-client : D.Run S.nodeNext Fixture.server-done-first
  (D.clientRecv (D.reply S.canceled) ∷ D.clientRecv D.done ∷ []) closed
finish-client =
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) $
  D.internal (D.clientInternal (C.discardReply refl)) $
  D.internal (D.clientInternal (C.countArrival refl)) $
  D.internal (D.clientInternal (C.publishResponse refl)) $
  D.internal (D.clientInternal C.drainResult) $
  D.internal (D.clientInternal (C.startMarker refl)) $
  D.internal (D.clientInternal (C.publishMarker refl)) $
  D.internal (D.clientInternal C.drainResult) $
  D.internal (D.clientInternal C.drained) $
  D.internal (D.decodeClient C.receivedDone) $
  D.visible (D.clientReceived C.receivedDone) D.stop

-- The theorem counts internal work as well as the two remaining wire records.
client-drain-bounded : Shutdown.steps finish-client ≤ Cost.rank Fixture.server-done-first
client-drain-bounded = Shutdown.bounded finish-client (refl , refl)

-- Twelve actual model operations occur in this continuation.
client-drain-count : Shutdown.steps finish-client ≡ 12
client-drain-count = refl

-- The initial potential is a conservative bound, rather than an exact operation count.
client-drain-budget : Cost.rank Fixture.server-done-first ≡ 37
client-drain-budget = refl

-- Unused empty-Send-slot credits remain even when both peers and transports have completed.
completed-budget : Cost.rank closed ≡ 11
completed-budget = refl

-- An already-sent reply still has retirement work before a completion token exists.
unretired : S.State
unretired = S.state S.flushing 0 S.sent 0 true

-- This counterexample state is reached from a fresh server, not posited as an arbitrary state.
unretired-reachable : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.recvQuit ∷ S.sendReply S.canceled ∷ []) unretired
unretired-reachable =
  S.visible (S.receiveRequest S.atFirst) $
  S.internal S.admitted $
  S.internal S.registered $
  S.visible (S.receiveQuit S.atNext) $
  S.internal S.setQuit $
  S.internal (S.claim refl) $
  S.internal (S.cancel refl) $
  S.visible (S.send refl) S.stop

-- Zero owed and zero completion tokens do not imply that shutdown work has finished.
unretired-counters : (S.owed unretired ≡ 0) × (S.completed unretired ≡ 0) ×
  (Shutdown.unretired (S.sender unretired) ≡ 1) × (Cost.serverCost unretired ≡ 13)
unretired-counters = refl , refl , refl , refl

-- Reuse the original sequential exchanges to reach arbitrary completion bookkeeping after Quit.
post-flag-reachable : (n : ℕ) → Σ[ actions ∈ List S.Action ]
  S.Run S.nodeNext S.initial actions (S.state S.flushing 0 S.idle (suc n) true)
post-flag-reachable n with Server.completed-reachable true n
... | actions , source = actions ++ (S.recvQuit ∷ []) ,
  S.append source (S.visible (S.receiveQuit S.atNext) (S.internal S.setQuit S.stop))

-- Completion history remains a separate additive cost even with no unanswered replies.
completion-cost : (n : ℕ) →
  (S.owed (S.state S.flushing 0 S.idle n true) ≡ 0) ×
  (Cost.serverCost (S.state S.flushing 0 S.idle n true) ≡ 11 Data.Nat.+ n)
completion-cost n = refl , refl
