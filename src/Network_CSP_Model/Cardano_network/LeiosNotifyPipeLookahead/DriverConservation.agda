{-# OPTIONS --safe #-}

-- Exact FIFO conservation includes packets whose Send/Recv trace hooks are pending.
module Cardano_network.LeiosNotifyPipeLookahead.DriverConservation
  (Notification Return : Set) where

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_; _∷ʳ_)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- The list argument preserves exact payloads and multiplicity, at any packet universe.
module Packet {ℓ : Level} (A : Set ℓ) where
  -- One pending hook refers to exactly one already committed or decoded packet.
  pending : Maybe A → List A
  pending nothing = []
  pending (just m) = m ∷ []

  -- Committed sends equal recorded receives, the pending Receive, then the FIFO.
  Balance : List A → List A → Maybe A → Maybe A → List A → Set ℓ
  Balance sent received ps pr queue = sent ++ pending ps ≡ received ++ (pending pr ++ queue)

  -- Channel commit appends the same packet to the FIFO and pending Send slot.
  enqueue : ∀ {sent received pr queue m} → Balance sent received nothing pr queue →
    Balance sent received (just m) pr (queue ∷ʳ m)
  enqueue {sent} {received} {pr} {queue} {m} equal =
    trans (cong (_++ (m ∷ [])) (sym (++-identityʳ sent)))
      (trans (cong (_++ (m ∷ [])) equal)
        (trans (++-assoc received (pending pr ++ queue) (m ∷ []))
          (cong (received ++_) (++-assoc (pending pr) queue (m ∷ [])))))

  -- The delayed Send record moves its packet into history without committing twice.
  record-send : ∀ {sent received pr queue m} → Balance sent received (just m) pr queue →
    Balance (sent ∷ʳ m) received nothing pr queue
  record-send {sent} {m = m} equal = trans (++-identityʳ (sent ∷ʳ m)) equal

  -- Decode removes the head into its pending Receive slot without changing order.
  decode : ∀ {sent received ps queue m} → Balance sent received ps nothing (m ∷ queue) →
    Balance sent received ps (just m) queue
  decode equal = equal

  -- The Receive record moves that same head into history exactly once.
  record-receive : ∀ {sent received ps queue m} → Balance sent received ps (just m) queue →
    Balance sent (received ∷ʳ m) ps nothing queue
  record-receive {received = received} {queue = queue} {m = m} equal =
    trans equal (sym (++-assoc received (m ∷ []) queue))

  -- Only empty buffers and both discharged hooks justify equality of recorded histories.
  settled : ∀ {sent received ps pr queue} → Balance sent received ps pr queue →
    ps ≡ nothing → pr ≡ nothing → queue ≡ [] → sent ≡ received
  settled {sent} {received} equal refl refl refl =
    trans (sym (++-identityʳ sent)) (trans equal (++-identityʳ received))

-- Independent directions retain their own command/reply packet types.
module ToServer = Packet D.ClientMessage
-- Reply payloads, Canceled and Done remain distinct in the reverse direction.
module ToClient = Packet D.ServerMessage

-- Histories remember each endpoint's observed packet order without sorting records.
record History : Set where
  constructor history
  field
    clientSends serverReceives : List D.ClientMessage
    serverSends clientReceives : List D.ServerMessage
open History public

-- Fresh captures have no invented historical packets.
empty : History
empty = history [] [] [] []

-- Append one original record to precisely its endpoint's history.
advance : D.Event → History → History
advance (D.clientSend m) (history cs sr ss cr) = history (cs ∷ʳ m) sr ss cr
advance (D.serverRecv m) (history cs sr ss cr) = history cs (sr ∷ʳ m) ss cr
advance (D.serverSend m) (history cs sr ss cr) = history cs sr (ss ∷ʳ m) cr
advance (D.clientRecv m) (history cs sr ss cr) = history cs sr ss (cr ∷ʳ m)

-- Fold the supplied sequence in file order, preserving every repeated occurrence.
observe : List D.Event → History → History
observe [] past = past
observe (row ∷ rows) past = observe rows (advance row past)

-- Both directions satisfy exact packet-list conservation, including unfinished hooks.
record Balanced (past : History) (raw : D.State) : Set where
  constructor balanced
  field
    to-server : ToServer.Balance (clientSends past) (serverReceives past)
      (D.pendingClientSend raw) (D.pendingServerRecv raw) (D.clientToServer raw)
    to-client : ToClient.Balance (serverSends past) (clientReceives past)
      (D.pendingServerSend raw) (D.pendingClientRecv raw) (D.serverToClient raw)
open Balanced public

-- Each visible driver hook preserves both directional equations exactly.
step-balance : ∀ {p s row t past} → D.Step p s row t → Balanced past s → Balanced (advance row past) t
step-balance {past = history cs sr ss cr} (D.clientSent {cs = queue} {m = m} {rs = pr} _) (balanced there back) =
  balanced (ToServer.record-send {sent = cs} {received = sr} {pr = pr} {queue = queue} {m = m} there) back
step-balance {past = history cs sr ss cr} (D.serverReceived {cs = queue} {pc = ps} {m = m} _) (balanced there back) =
  balanced (ToServer.record-receive {sent = cs} {received = sr} {ps = ps} {queue = queue} {m = m} there) back
step-balance {past = history cs sr ss cr} (D.serverSent {sc = queue} {m = m} {rc = pr} _) (balanced there back) =
  balanced there (ToClient.record-send {sent = ss} {received = cr} {pr = pr} {queue = queue} {m = m} back)
step-balance {past = history cs sr ss cr} (D.clientReceived {sc = queue} {ps = ps} {m = m} _) (balanced there back) =
  balanced there (ToClient.record-receive {sent = ss} {received = cr} {ps = ps} {queue = queue} {m = m} back)

-- Source control/callbacks move no packets; commit and decode preserve their exact lists.
tau-balance : ∀ {p s t past} → D.Tau p s t → Balanced past s → Balanced past t
tau-balance (D.clientInternal _) (balanced there back) = balanced there back
tau-balance (D.serverInternal _) (balanced there back) = balanced there back
tau-balance (D.clientCallback _ _) (balanced there back) = balanced there back
tau-balance (D.serverCallback _) (balanced there back) = balanced there back
tau-balance {past = history cs sr ss cr} (D.commitClient {cs = queue} {rs = pr} {m = m} _) (balanced there back) =
  balanced (ToServer.enqueue {sent = cs} {received = sr} {pr = pr} {queue = queue} {m = m} there) back
tau-balance {past = history cs sr ss cr} (D.commitServer {sc = queue} {rc = pr} {m = m} _) (balanced there back) =
  balanced there (ToClient.enqueue {sent = ss} {received = cr} {pr = pr} {queue = queue} {m = m} back)
tau-balance {past = history cs sr ss cr} (D.decodeClient {sc = queue} {ps = ps} {m = m} _) (balanced there back) =
  balanced there (ToClient.decode {sent = ss} {received = cr} {ps = ps} {queue = queue} {m = m} back)
tau-balance {past = history cs sr ss cr} (D.decodeServer {cs = queue} {pc = ps} {m = m} _) (balanced there back) =
  balanced (ToServer.decode {sent = cs} {received = sr} {ps = ps} {queue = queue} {m = m} there) back

-- Every finite run preserves conservation from any already balanced starting history.
run-balance : ∀ {p s rows t past} → D.Run p s rows t → Balanced past s → Balanced (observe rows past) t
run-balance D.stop accounted = accounted
run-balance (D.internal step run) accounted = run-balance run (tau-balance step accounted)
run-balance (D.visible step run) accounted = run-balance run (step-balance step accounted)

-- The empty product and histories satisfy both equations constructively.
initial-balanced : Balanced empty D.initial
initial-balanced = balanced refl refl

-- Every fresh finite product execution preserves payloads, FIFO order and multiplicity.
initial-conservation : ∀ {p rows t} → D.Run p D.initial rows t → Balanced (observe rows empty) t
initial-conservation run = run-balance run initial-balanced

-- Once the command direction is settled, its two endpoint histories are identical.
commands-settled : ∀ {p rows t} → D.Run p D.initial rows t →
  D.pendingClientSend t ≡ nothing → D.pendingServerRecv t ≡ nothing → D.clientToServer t ≡ [] →
  clientSends (observe rows empty) ≡ serverReceives (observe rows empty)
commands-settled run = ToServer.settled (to-server (initial-conservation run))

-- The same statement retains exact normal/Canceled payloads and final Done occurrences.
responses-settled : ∀ {p rows t} → D.Run p D.initial rows t →
  D.pendingServerSend t ≡ nothing → D.pendingClientRecv t ≡ nothing → D.serverToClient t ≡ [] →
  serverSends (observe rows empty) ≡ clientReceives (observe rows empty)
responses-settled run = ToClient.settled (to-client (initial-conservation run))
