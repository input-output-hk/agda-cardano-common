{-# OPTIONS --safe #-}

-- Fresh driver witnesses show why prefix bounds retain a pending Send correction in both directions.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverPrefixBoundsTests where

open import Data.Bool using (Bool; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (_≤_; _+_; s≤s; z≤n)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
open import Cardano_network.LeiosNotifyPipeLookahead.DriverPrefixBounds Bool Bool
open import Cardano_network.LeiosNotifyPipeLookahead.DriverPrefixBoundsQueues Bool Bool

-- An EOF before any visible row may still contain one physically committed request.
committed-state : D.State
committed-state = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  S.initial (D.request ∷ []) [] (just D.request) nothing nothing nothing

-- The source registration and actual commit precede the delayed client Send hook.
committed-prefix : D.Run S.nodeNext D.initial [] committed-state
committed-prefix =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) D.stop

-- Exact tally computes one physical operation despite having zero input rows.
empty-prefix-count : ClientSend.operations committed-prefix ≡ 1
empty-prefix-count = refl

-- The command FIFO attains the additive-one envelope already at an empty visible prefix.
empty-prefix-queue : occupied (D.pendingServerRecv committed-state) +
  length (D.clientToServer committed-state) ≤ ClientSend.rows [] + 1
empty-prefix-queue = commands-bound committed-prefix

-- Removing the pending-Send allowance would rule out this genuinely reachable prefix.
zero-allowance-impossible : ClientSend.operations committed-prefix ≤ ClientSend.rows [] → ⊥
zero-allowance-impossible ()

-- Both receivers can publish records before either sender publishes its own Send row.
delayed-rows : List D.Event
delayed-rows = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ []

-- Both independent Send slots remain occupied at this valid EOF prefix.
delayed-state : D.State
delayed-state = D.pair
  (C.client C.writingRequest (C.inspect (S.normal false)) [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 (S.selected (S.normal false)) 0 false)
  [] [] (just D.request) (just (D.reply (S.normal false))) nothing nothing

-- Every hidden/visible rule is an actual DriverModel operation from the fresh state.
both-delayed-prefix : D.Run S.nodeNext D.initial delayed-rows delayed-state
both-delayed-prefix =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose refl refl)) $
  D.internal (D.commitServer (S.send refl)) $
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) D.stop

-- The client direction needs exactly the one-slot correction for this concrete trace.
client-delayed-exact : ClientSend.operations both-delayed-prefix ≡
  ClientSend.rows delayed-rows + occupied (D.pendingClientSend delayed-state)
client-delayed-exact = clientSend-exact both-delayed-prefix

-- The server direction independently needs its own pending trace-hook correction.
server-delayed-exact : ServerSend.operations both-delayed-prefix ≡
  ServerSend.rows delayed-rows + occupied (D.pendingServerSend delayed-state)
server-delayed-exact = serverSend-exact both-delayed-prefix

-- The one-slot client bound is attained, rather than merely an unused upper limit.
client-delayed-count : ClientSend.operations both-delayed-prefix ≡ 1
client-delayed-count = refl

-- The reverse direction also commits a real normal reply with no visible Send record.
server-delayed-count : ServerSend.operations both-delayed-prefix ≡ 1
server-delayed-count = refl

-- Both transport FIFOs have been decoded without waiting for the two Send records.
client-decode-accounted : ClientSend.operations both-delayed-prefix ≡
  ServerRecv.operations both-delayed-prefix + length (D.clientToServer delayed-state)
client-decode-accounted = client-commits-exact both-delayed-prefix

-- Reverse transport accounting retains the same receive-before-send behavior.
server-decode-accounted : ServerSend.operations both-delayed-prefix ≡
  ClientRecv.operations both-delayed-prefix + length (D.serverToClient delayed-state)
server-decode-accounted = server-commits-exact both-delayed-prefix

-- A zero-correction server bound would reject the inhabited delayed-reply prefix too.
server-zero-allowance-impossible : ServerSend.operations both-delayed-prefix ≤ ServerSend.rows delayed-rows → ⊥
server-zero-allowance-impossible ()
