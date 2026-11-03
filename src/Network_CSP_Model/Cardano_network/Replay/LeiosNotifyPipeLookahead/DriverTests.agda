{-# OPTIONS --safe #-}

-- Constructive paired schedules at the actual pinned driver-record boundary.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverTests where

open import Data.Bool using (Bool; false)
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
open import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool

-- Both endpoint record orders participate in a valid paired run despite delayed sends.
delayed-send-records : Run S.nodeNext initial
  (serverRecv request ∷ clientRecv (reply (S.normal false)) ∷
   clientSend request ∷ serverSend (reply (S.normal false)) ∷ [])
  (pair
    (C.client C.poll (C.inspect (S.normal false)) [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false)
    [] [] nothing nothing nothing nothing)
delayed-send-records =
  internal (clientCallback (continue {k = + 1}) C.continueZero) $
  internal (clientInternal C.registerResponse) $
  internal (clientInternal (C.startResponse refl)) $
  internal (commitClient C.sentRequest) $
  internal (decodeServer (S.receiveRequest S.atFirst)) $
  visible (serverReceived (S.receiveRequest S.atFirst)) $
  internal (serverInternal S.admitted) $
  internal (serverInternal S.registered) $
  internal (serverInternal (S.claim refl)) $
  internal (serverCallback (S.choose refl refl)) $
  internal (commitServer (S.send refl)) $
  internal (decodeClient (C.receivedReply refl)) $
  visible (clientReceived (C.receivedReply refl)) $
  visible (clientSent C.sentRequest) $
  visible (serverSent (S.send refl)) stop

-- Send records require an earlier commit of that exact message.
client-send-has-commit : ∀ {p s m t} → Step p s (clientSend m) t →
  pendingClientSend s ≡ just m
client-send-has-commit (clientSent _) = refl

-- Responder send records obey the same exact-value commitment rule.
server-send-has-commit : ∀ {p s m t} → Step p s (serverSend m) t →
  pendingServerSend s ≡ just m
server-send-has-commit (serverSent _) = refl

-- Receives record the exact packet already decoded from the transport.
client-receive-has-packet : ∀ {p s m t} → Step p s (clientRecv m) t →
  pendingClientRecv s ≡ just m
client-receive-has-packet (clientReceived _) = refl

-- Command receive records cannot invent requests absent from transport decoding.
server-receive-has-packet : ∀ {p s m t} → Step p s (serverRecv m) t →
  pendingServerRecv s ≡ just m
server-receive-has-packet (serverReceived _) = refl

-- Record emission never enqueues or dequeues a packet a second time.
record-preserves-transport : ∀ {p s e t} → Step p s e t →
  clientToServer s ≡ clientToServer t × serverToClient s ≡ serverToClient t
record-preserves-transport (clientSent _) = refl , refl
record-preserves-transport (serverSent _) = refl , refl
record-preserves-transport (clientReceived _) = refl , refl
record-preserves-transport (serverReceived _) = refl , refl

-- A fresh connection has no pending records that could justify a receive.
no-initial-receive : ∀ {p m t} → Step p initial (serverRecv m) t → ⊥
no-initial-receive ()

-- An uncommitted Send record is equally impossible in the fresh state.
no-initial-send : ∀ {p m t} → Step p initial (clientSend m) t → ⊥
no-initial-send ()
