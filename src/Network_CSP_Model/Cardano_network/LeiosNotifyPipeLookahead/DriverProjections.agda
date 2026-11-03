{-# OPTIONS --safe #-}

-- Endpoint control executions extracted from the independent paired driver product.
module Cardano_network.LeiosNotifyPipeLookahead.DriverProjections (Notification Return : Set) where

open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- Retain precisely the client's wire records from its source action history.
clientWire : C.Action → Maybe D.Event
clientWire C.sendRequest = just (D.clientSend D.request)
clientWire C.sendQuit = just (D.clientSend D.quit)
clientWire (C.recvReply msg) = just (D.clientRecv (D.reply msg))
clientWire C.recvDone = just (D.clientRecv D.done)
clientWire _ = nothing

-- Retain the corresponding server wire records, excluding application readiness.
serverWire : S.Action → Maybe D.Event
serverWire S.recvRequest = just (D.serverRecv D.request)
serverWire S.recvQuit = just (D.serverRecv D.quit)
serverWire (S.sendReply msg) = just (D.serverSend (D.reply msg))
serverWire S.sendDone = just (D.serverSend D.done)
serverWire _ = nothing

-- Extract only client records while preserving their supplied order.
clientRows : List D.Event → List D.Event
clientRows [] = []
clientRows (row@(D.clientSend _) ∷ rows) = row ∷ clientRows rows
clientRows (row@(D.clientRecv _) ∷ rows) = row ∷ clientRows rows
clientRows (_ ∷ rows) = clientRows rows

-- Extract server records with the same order-preserving convention.
serverRows : List D.Event → List D.Event
serverRows [] = []
serverRows (row@(D.serverSend _) ∷ rows) = row ∷ serverRows rows
serverRows (row@(D.serverRecv _) ∷ rows) = row ∷ serverRows rows
serverRows (_ ∷ rows) = serverRows rows

-- Declared client callbacks contribute control steps but no driver wire row.
callback-erased : ∀ {a} → D.ClientCallback a → clientWire a ≡ nothing
callback-erased D.continue = refl
callback-erased D.terminate = refl
callback-erased D.handled = refl

-- Abstract client commands preserve their concrete record identity.
client-send-wire : ∀ msg → clientWire (D.clientSendAction msg) ≡ just (D.clientSend msg)
client-send-wire D.request = refl
client-send-wire D.quit = refl

-- Client receives likewise retain the distinction between a reply and Done.
client-receive-wire : ∀ msg → clientWire (D.clientRecvAction msg) ≡ just (D.clientRecv msg)
client-receive-wire (D.reply _) = refl
client-receive-wire D.done = refl

-- Server sends preserve their original reply or final Done record.
server-send-wire : ∀ msg → serverWire (D.serverSendAction msg) ≡ just (D.serverSend msg)
server-send-wire (D.reply _) = refl
server-send-wire D.done = refl

-- Server receives preserve the initiating command they consumed.
server-receive-wire : ∀ msg → serverWire (D.serverRecvAction msg) ≡ just (D.serverRecv msg)
server-receive-wire D.request = refl
server-receive-wire D.quit = refl

-- Erasing one declared non-wire action preserves the remaining record sequence.
erased-cons : ∀ {A : Set} (project : A → Maybe D.Event) (a : A) actions → project a ≡ nothing →
  mapMaybe project (a ∷ actions) ≡ mapMaybe project actions
erased-cons project a actions eq rewrite eq = refl

-- Keeping one action adds precisely its original record ahead of the remaining sequence.
kept-cons : ∀ {A : Set} (project : A → Maybe D.Event) (a : A) actions row → project a ≡ just row →
  mapMaybe project (a ∷ actions) ≡ row ∷ mapMaybe project actions
kept-cons project a actions row eq rewrite eq = refl

-- Extraction is valid at every fixed responder callback contract.
module For (contract : S.Contract) where
  -- Every product execution projects to an exact client source run with matching wire order.
  client : ∀ {s rows t} → D.Run contract s rows t →
    Σ[ actions ∈ List C.Action ]
      (C.Run (D.clientState s) actions (D.clientState t) × mapMaybe clientWire actions ≡ clientRows rows)
  client D.stop = [] , C.stop , refl
  client (D.internal (D.clientInternal pr) run) with client run
  ... | actions , source , wire = actions , C.internal pr source , wire
  client (D.internal (D.serverInternal _) run) = client run
  client (D.internal (D.clientCallback {a = a} callback pr) run) with client run
  ... | actions , source , wire = a ∷ actions , C.visible pr source ,
    trans (erased-cons clientWire a actions (callback-erased callback)) wire
  client (D.internal (D.serverCallback _) run) = client run
  client (D.internal (D.commitClient _) run) = client run
  client (D.internal (D.commitServer _) run) = client run
  client (D.internal (D.decodeClient _) run) = client run
  client (D.internal (D.decodeServer _) run) = client run
  client (D.visible (D.clientSent {m = msg} pr) run) with client run
  ... | actions , source , wire = D.clientSendAction msg ∷ actions , C.visible pr source ,
    trans (kept-cons clientWire (D.clientSendAction msg) actions (D.clientSend msg) (client-send-wire msg))
      (cong (D.clientSend msg ∷_) wire)
  client (D.visible (D.clientReceived {m = msg} pr) run) with client run
  ... | actions , source , wire = D.clientRecvAction msg ∷ actions , C.visible pr source ,
    trans (kept-cons clientWire (D.clientRecvAction msg) actions (D.clientRecv msg) (client-receive-wire msg))
      (cong (D.clientRecv msg ∷_) wire)
  client (D.visible (D.serverSent _) run) = client run
  client (D.visible (D.serverReceived _) run) = client run

  -- The same product execution independently projects to its exact server source run.
  server : ∀ {s rows t} → D.Run contract s rows t →
    Σ[ actions ∈ List S.Action ]
      (S.Run contract (D.serverState s) actions (D.serverState t) × mapMaybe serverWire actions ≡ serverRows rows)
  server D.stop = [] , S.stop , refl
  server (D.internal (D.serverInternal pr) run) with server run
  ... | actions , source , wire = actions , S.internal pr source , wire
  server (D.internal (D.clientInternal _) run) = server run
  server (D.internal (D.clientCallback _ _) run) = server run
  server (D.internal (D.serverCallback {m = msg} pr) run) with server run
  ... | actions , source , wire = S.nextReply msg ∷ actions , S.visible pr source , wire
  server (D.internal (D.commitClient _) run) = server run
  server (D.internal (D.commitServer _) run) = server run
  server (D.internal (D.decodeClient _) run) = server run
  server (D.internal (D.decodeServer _) run) = server run
  server (D.visible (D.serverSent {m = msg} pr) run) with server run
  ... | actions , source , wire = D.serverSendAction msg ∷ actions , S.visible pr source ,
    trans (kept-cons serverWire (D.serverSendAction msg) actions (D.serverSend msg) (server-send-wire msg))
      (cong (D.serverSend msg ∷_) wire)
  server (D.visible (D.serverReceived {m = msg} pr) run) with server run
  ... | actions , source , wire = D.serverRecvAction msg ∷ actions , S.visible pr source ,
    trans (kept-cons serverWire (D.serverRecvAction msg) actions (D.serverRecv msg) (server-receive-wire msg))
      (cong (D.serverRecv msg ∷_) wire)
  server (D.visible (D.clientSent _) run) = server run
  server (D.visible (D.clientReceived _) run) = server run
