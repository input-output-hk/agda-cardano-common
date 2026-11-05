{-# OPTIONS --safe #-}

-- Every received normal/Canceled reply needs an actually recorded server Request, even before its Send hook.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheck
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_; map; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≤_; _≤?_; z≤n)
open import Data.Nat.Properties using (m≤m+n; m≤n+m; ≤-refl; ≤-trans; +-mono-≤)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Nullary using (Dec)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification Return as Conservation
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.ServerSendSlot Notification Return as Slot
import Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger Notification Return as Ledger
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Notification as Wire
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Notification Return as Local
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Notification Return as Packet

-- Only RequestNext creates reply credit; recorded Quit contributes no unit.
wire-requests : List Wire.Wire → ℕ
wire-requests [] = 0
wire-requests (Wire.request ∷ rows) = suc (wire-requests rows)
wire-requests (Wire.quit ∷ rows) = wire-requests rows
wire-requests (Wire.reply _ ∷ rows) = wire-requests rows
wire-requests (Wire.done ∷ rows) = wire-requests rows

-- Normal and Canceled consume credit; final Done is an independent acknowledgment.
wire-replies : List Wire.Wire → ℕ
wire-replies [] = 0
wire-replies (Wire.request ∷ rows) = wire-replies rows
wire-replies (Wire.quit ∷ rows) = wire-replies rows
wire-replies (Wire.reply _ ∷ rows) = suc (wire-replies rows)
wire-replies (Wire.done ∷ rows) = wire-replies rows

-- Server source observation preserves the exact request count while hiding callback selections.
source-requests : ∀ actions → Server.requests actions ≡ wire-requests (Wire.wire actions)
source-requests [] = refl
source-requests (S.recvRequest ∷ actions) = cong suc (source-requests actions)
source-requests (S.recvQuit ∷ actions) = source-requests actions
source-requests (S.sendReply _ ∷ actions) = source-requests actions
source-requests (S.sendDone ∷ actions) = source-requests actions
source-requests (S.nextReply _ ∷ actions) = source-requests actions

-- Reply selections are hidden, but each actual server Send remains a counted occurrence.
source-replies : ∀ actions → Server.replies actions ≡ wire-replies (Wire.wire actions)
source-replies [] = refl
source-replies (S.recvRequest ∷ actions) = source-replies actions
source-replies (S.recvQuit ∷ actions) = source-replies actions
source-replies (S.sendReply _ ∷ actions) = cong suc (source-replies actions)
source-replies (S.sendDone ∷ actions) = source-replies actions
source-replies (S.nextReply _ ∷ actions) = source-replies actions

-- The local wire map counts precisely the typed server Request receives, without counting Quit.
typed-requests : ∀ rows → wire-requests (map Local.serverWire rows) ≡ Ledger.requests (Packet.serverReceives rows)
typed-requests [] = refl
typed-requests (Rows.receiveCommand D.request ∷ rows) = cong suc (typed-requests rows)
typed-requests (Rows.receiveCommand D.quit ∷ rows) = typed-requests rows
typed-requests (Rows.sendResponse (D.reply _) ∷ rows) = typed-requests rows
typed-requests (Rows.sendResponse D.done ∷ rows) = typed-requests rows

-- Typed normal/Canceled Send records preserve their count and keep Done outside it.
typed-replies : ∀ rows → wire-replies (map Local.serverWire rows) ≡ Ledger.replies (Packet.serverSends rows)
typed-replies [] = refl
typed-replies (Rows.receiveCommand D.request ∷ rows) = typed-replies rows
typed-replies (Rows.receiveCommand D.quit ∷ rows) = typed-replies rows
typed-replies (Rows.sendResponse (D.reply _) ∷ rows) = cong suc (typed-replies rows)
typed-replies (Rows.sendResponse D.done ∷ rows) = typed-replies rows

-- Existing endpoint projections give the exact server accounting at every paired initial prefix.
server-accounting : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Ledger.requests (Packet.serverReceives server) ≡
    Ledger.replies (Packet.serverSends server) + S.owed (D.serverState target)
server-accounting {contract} {server = server} {target = target} merged run
  with Projection.For.server contract run
... | actions , source , matching = trans (sym requests-same)
  (trans (Server.initial-balance source) (cong (_+ S.owed (D.serverState target)) replies-same))
  where
  -- This is the same exact wire equation used by the independent local precheck.
  same : Wire.wire actions ≡ map Local.serverWire server
  same = trans (sym (Local.server-observation actions))
    (trans (cong (mapMaybe Local.serverDecode) matching) (Local.server-merged merged))

  -- Source counts are transported to the supplied typed server rows, independently of merge order.
  requests-same : Server.requests actions ≡ Ledger.requests (Packet.serverReceives server)
  requests-same = trans (source-requests actions) (trans (cong wire-requests same) (typed-requests server))

  -- The corresponding response count retains all repeated normal/Canceled values and excludes Done.
  replies-same : Server.replies actions ≡ Ledger.replies (Packet.serverSends server)
  replies-same = trans (source-replies actions) (trans (cong wire-replies same) (typed-replies server))

-- Counting normal/Canceled packets is additive over exact queue concatenation.
replies-++ : (before after : List D.ServerMessage) →
  Ledger.replies (before ++ after) ≡ Ledger.replies before + Ledger.replies after
replies-++ [] after = refl
replies-++ (D.reply _ ∷ before) after = cong suc (replies-++ before after)
replies-++ (D.done ∷ before) after = replies-++ before after

-- One pending slot contributes one credit only when it contains a Reply rather than Done.
pending-replies : ∀ pending → Ledger.replies (Conservation.ToClient.pending pending) ≡ Ledger.reply pending
pending-replies nothing = refl
pending-replies (just (D.reply _)) = refl
pending-replies (just D.done) = refl

-- Exact committed packet histories retain the pending server Send's reply contribution.
committed-replies : (sent : List D.ServerMessage) (pending : Maybe D.ServerMessage) →
  Ledger.replies (sent ++ Conservation.ToClient.pending pending) ≡ Ledger.replies sent + Ledger.reply pending
committed-replies sent pending = trans (replies-++ sent (Conservation.ToClient.pending pending))
  (cong (Ledger.replies sent +_) (pending-replies pending))

-- Conservation bounds received replies by committed replies, retaining decoded/FIFO suffixes.
received-committed : (sent received : List D.ServerMessage)
  {ps pr : Maybe D.ServerMessage} {queue : List D.ServerMessage} →
  Conservation.ToClient.Balance sent received ps pr queue →
  Ledger.replies received ≤ Ledger.replies sent + Ledger.reply ps
received-committed sent received {ps} {pr} {queue} balance =
  subst (Ledger.replies received ≤_)
    (trans (sym (cong Ledger.replies balance)) (committed-replies sent ps))
    (subst (Ledger.replies received ≤_)
      (sym (replies-++ received (Conservation.ToClient.pending pr ++ queue)))
      (m≤m+n (Ledger.replies received) (Ledger.replies (Conservation.ToClient.pending pr ++ queue))))

-- A committed Reply Send still has selected source control and therefore one actual owed job.
pending-credit : ∀ {server pending} → Slot.Slot server pending → Ledger.reply pending ≤ S.owed server
pending-credit Slot.vacant = z≤n
pending-credit (Slot.reply {r} {w}) = ≤-trans (m≤n+m 1 w) (m≤n+m (w + 1) (S.unregistered r))
pending-credit Slot.done = z≤n

-- This cross-endpoint necessary condition excludes unsolicited replies; it deliberately does not count Done.
Pass : List Rows.ClientRow → List Rows.ServerRow → Set
Pass client server = Ledger.replies (Packet.clientReceives client) ≤ Ledger.requests (Packet.serverReceives server)

-- Pure numerical checking requires no payload equality or inhabited Return type.
decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (Pass client server)
decide client server = Ledger.replies (Packet.clientReceives client) ≤? Ledger.requests (Packet.serverReceives server)

-- Every original source run supplies enough recorded Request credit even when Reply Send hooks are pending.
necessary : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Pass client server
necessary {client = client} {server} {target = target} merged run = ≤-trans
  (received-committed (Packet.serverSends server) (Packet.clientReceives client)
    {ps = D.pendingServerSend target} {pr = D.pendingClientRecv target} {queue = D.serverToClient target}
    (Conservation.to-client balanced))
  (subst (Ledger.replies (Packet.serverSends server) + Ledger.reply (D.pendingServerSend target) ≤_)
    (sym (server-accounting merged run))
    (+-mono-≤ ≤-refl (pending-credit (Slot.initial-consistent run))))
  where
  -- The independent packet-history lemma preserves the complete supplied endpoint row lists.
  balanced : Conservation.Balanced (Packet.extend Conservation.empty client server) target
  balanced = subst (λ history → Conservation.Balanced history target)
    (Packet.merge-history merged Conservation.empty) (Conservation.initial-conservation run)
