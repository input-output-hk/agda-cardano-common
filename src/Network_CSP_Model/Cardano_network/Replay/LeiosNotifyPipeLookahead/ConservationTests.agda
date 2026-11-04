{-# OPTIONS --safe #-}

-- Reachable races/faults and malformed histories exercise the conservation endpoints.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ConservationTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_+_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Bool Bool as Transport
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Bool as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Tests as ServerTests
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverTests as DriverTests

-- An excessive-request fault retains its one unanswered request instead of losing it.
fault-accounted : Server.requests (S.recvRequest ∷ []) ≡
  Server.replies (S.recvRequest ∷ []) + S.owed (S.state S.failed 0 S.idle 0 false)
fault-accounted = Server.initial-balance ServerTests.excessive-request

-- Cancellation discharges the request, while Done does not count as another reply.
cancellation-accounted : Server.requests (S.recvRequest ∷ S.recvQuit ∷ S.sendReply S.canceled ∷ S.sendDone ∷ []) ≡
  Server.replies (S.recvRequest ∷ S.recvQuit ∷ S.sendReply S.canceled ∷ S.sendDone ∷ [])
cancellation-accounted = Server.closed-balance ServerTests.canceled-drain

-- The global accounting theorem excludes a reply with no preceding wire request.
no-phantom-reply : ∀ {p t} → S.Run p S.initial (S.sendReply (S.normal true) ∷ []) t → ⊥
no-phantom-reply run with Server.no-extra-replies run
... | ()

-- This reachable state has a recorded Receive and a still-pending client Send hook.
race-state : D.State
race-state = D.pair (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.admit 0 S.idle 0 false) [] [] (just D.request) nothing nothing nothing

-- The original channel/record ordering permits this fresh one-record history.
receive-before-send : D.Run S.nodeNext D.initial (D.serverRecv D.request ∷ []) race-state
receive-before-send =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) D.stop

-- Pending-slot accounting accepts that concrete race without inventing a Send record.
race-balanced : Transport.Balanced (Transport.observe (D.serverRecv D.request ∷ []) Transport.empty) race-state
race-balanced = Transport.initial-conservation receive-before-send

-- Equality of only the recorded histories would falsely reject the reachable prefix.
naive-race-equality-false :
  Transport.clientSends (Transport.observe (D.serverRecv D.request ∷ []) Transport.empty) ≢
  Transport.serverReceives (Transport.observe (D.serverRecv D.request ∷ []) Transport.empty)
naive-race-equality-false ()

-- When its delayed hooks finish, the known concrete schedule has identical command histories.
delayed-commands-settled : D.request ∷ [] ≡ D.request ∷ []
delayed-commands-settled = Transport.commands-settled DriverTests.delayed-send-records refl refl refl

-- The response direction preserves the original exact normal payload too.
delayed-responses-settled : D.reply (S.normal false) ∷ [] ≡ D.reply (S.normal false) ∷ []
delayed-responses-settled = Transport.responses-settled DriverTests.delayed-send-records refl refl refl

-- Reversing two different response payloads contradicts conservation even in a prefix.
no-swapped-responses : ∀ {p t} → D.Run p D.initial
  (D.clientSend D.request ∷ D.serverRecv D.request ∷
   D.clientSend D.request ∷ D.serverRecv D.request ∷
   D.serverSend (D.reply (S.normal true)) ∷ D.serverSend (D.reply (S.normal false)) ∷
   D.clientRecv (D.reply (S.normal false)) ∷ D.clientRecv (D.reply (S.normal true)) ∷ []) t → ⊥
no-swapped-responses run with Transport.to-client (Transport.initial-conservation run)
... | ()

-- An extra Receive is excluded once all command packets and hooks have settled.
no-duplicated-command : ∀ {p t} → D.Run p D.initial
  (D.clientSend D.request ∷ D.serverRecv D.request ∷ D.serverRecv D.request ∷ []) t →
  D.pendingClientSend t ≡ nothing → D.pendingServerRecv t ≡ nothing → D.clientToServer t ≡ [] → ⊥
no-duplicated-command run send-clear receive-clear queue-clear
  with Transport.commands-settled run send-clear receive-clear queue-clear
... | ()
