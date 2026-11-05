{-# OPTIONS --safe #-}

-- All-prefix transport preserves delayed hooks and rejects orders whose final counts alone are valid.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransportTests where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as D
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransport Bool ⊥ as Prefix

-- These record orders permit one Receive ahead of each Send, independently in both directions.
late-hooks : List D.Event
late-hooks = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷
  D.clientSend D.request ∷ D.serverSend (D.reply (S.normal false)) ∷ []

-- Every visible prefix passes; no strict Send-before-Receive order was imposed.
late-hooks-pass : Prefix.Bounded Prefix.History.empty late-hooks
late-hooks-pass = toWitness {a? = Prefix.decide Prefix.History.empty late-hooks} tt

-- A cut can retain just the two Receive records while both Send hooks remain pending.
cut-before-sends : Prefix.Bounded Prefix.History.empty
  (D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ [])
cut-before-sends = Prefix.cut
  (D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ []) late-hooks-pass

-- Final recorded counts allow three Requests received against two recorded client Sends.
invalid-order : List D.Event
invalid-order = D.serverRecv D.request ∷ D.serverRecv D.request ∷ D.serverRecv D.request ∷
  D.clientSend D.request ∷ D.clientSend D.request ∷ []

-- The final endpoint counts alone miss the earlier receive-lead violation.
final-counts-pass : Prefix.Bounds (Prefix.History.observe invalid-order Prefix.History.empty)
final-counts-pass = toWitness {a? = Prefix.bounds? (Prefix.History.observe invalid-order Prefix.History.empty)} tt

-- The second server Receive already exceeds the one pending client Send, before later Sends can help.
invalid-prefix : Prefix.Bounded Prefix.History.empty invalid-order → ⊥
invalid-prefix = toWitnessFalse {a? = Prefix.decide Prefix.History.empty invalid-order} tt

-- The response direction has the same prefix constraint, including repeated identical packet values.
invalid-reply-order : List D.Event
invalid-reply-order = D.clientRecv (D.reply (S.normal false)) ∷
  D.clientRecv (D.reply (S.normal false)) ∷ D.serverSend (D.reply (S.normal false)) ∷ []

-- Its final counts satisfy Receive≤Send+1 despite the impossible second early Receive.
final-reply-counts-pass : Prefix.Bounds (Prefix.History.observe invalid-reply-order Prefix.History.empty)
final-reply-counts-pass = toWitness
  {a? = Prefix.bounds? (Prefix.History.observe invalid-reply-order Prefix.History.empty)} tt

-- Earlier prefix failure cannot be repaired by appending the later Send record.
invalid-reply-prefix : Prefix.Bounded Prefix.History.empty invalid-reply-order → ⊥
invalid-reply-prefix = toWitnessFalse {a? = Prefix.decide Prefix.History.empty invalid-reply-order} tt

-- Several queued client Sends are allowed while the receiver has produced no record yet.
send-excess : List D.Event
send-excess = D.clientSend D.request ∷ D.clientSend D.request ∷
  D.clientSend D.request ∷ D.clientSend D.request ∷ []

-- The abstraction contains no finite FIFO-capacity or symmetric send-lead bound.
send-excess-pass : Prefix.Bounded Prefix.History.empty send-excess
send-excess-pass = toWitness {a? = Prefix.decide Prefix.History.empty send-excess} tt

-- A fresh no-operation source witnesses transport even for an empty Return carrier.
empty-return : Prefix.Bounded Prefix.History.empty []
empty-return = Prefix.necessary {contract = S.nodeNext} D.stop

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as Actual
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as Basis
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransport Bool ⊤ as ActualPrefix
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests as Fixture

-- This is an independently inhabited source run, not an acceptance assumption about the abstraction.
actual-both-pending : ActualPrefix.Bounded ActualPrefix.History.empty
  (Actual.serverRecv Actual.request ∷ Actual.clientRecv (Actual.reply (S.normal false)) ∷ [])
actual-both-pending = ActualPrefix.necessary (Basis.sound Fixture.both-delayed)

-- The source prefix theorem exposes the real first server Receive before either Send hook.
actual-first-prefix : ActualPrefix.Bounds
  (ActualPrefix.History.observe (Actual.serverRecv Actual.request ∷ []) ActualPrefix.History.empty)
actual-first-prefix = ActualPrefix.source-prefix-bounds
  (Actual.serverRecv Actual.request ∷ []) (Basis.sound Fixture.both-delayed)
