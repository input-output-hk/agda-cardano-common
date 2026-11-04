{-# OPTIONS --safe #-}

-- A committed server packet retains the corresponding source send control.
module Cardano_network.LeiosNotifyPipeLookahead.ServerSendSlot
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- This is structural consistency, including a reply committed before reader shutdown.
data Slot : S.State → Maybe D.ServerMessage → Set where
  vacant : ∀ {s} → Slot s nothing
  reply : ∀ {r w c q m} → Slot (S.state r w (S.selected m) c q) (just (D.reply m))
  done : Slot (S.state S.doneReady 0 S.idle 0 true) (just D.done)

-- The invariant refers to the actual pending server hook in the driver state.
Consistent : D.State → Set
Consistent raw = Slot (D.serverState raw) (D.pendingServerSend raw)

-- Reader/sender scheduling cannot overwrite a committed selected payload.
server-tau : ∀ {s t ps} → S.Tau s t → Slot s ps → Slot t ps
server-tau pr vacant = vacant
server-tau S.admitted reply = reply
server-tau S.excessive reply = reply
server-tau S.registered reply = reply
server-tau S.setQuit reply = reply
server-tau S.flush reply = reply
server-tau S.abort reply = reply
server-tau () done

-- A next callback starts from claimed control, which cannot already hold a send hook.
server-callback : ∀ {p s msg t ps} → S.Step p s (S.nextReply msg) t → Slot s ps → Slot t ps
server-callback (S.choose _ _) vacant = vacant

-- Receiving either command can change the reader without changing the pending reply.
server-receive : ∀ {p s t ps} (m : D.ClientMessage) →
  S.Step p s (D.serverRecvAction m) t → Slot s ps → Slot t ps
server-receive D.request (S.receiveRequest S.atFirst) vacant = vacant
server-receive D.request (S.receiveRequest S.atFirst) reply = reply
server-receive D.request (S.receiveRequest S.atNext) vacant = vacant
server-receive D.request (S.receiveRequest S.atNext) reply = reply
server-receive D.quit (S.receiveQuit S.atFirst) vacant = vacant
server-receive D.quit (S.receiveQuit S.atFirst) reply = reply
server-receive D.quit (S.receiveQuit S.atNext) vacant = vacant
server-receive D.quit (S.receiveQuit S.atNext) reply = reply

-- Publishing the server Send discharges its slot; other records preserve it.
step-consistent : ∀ {p s row t} → D.Step p s row t → Consistent s → Consistent t
step-consistent (D.clientSent _) slot = slot
step-consistent (D.serverSent _) slot = vacant
step-consistent (D.clientReceived _) slot = slot
step-consistent (D.serverReceived {m = m} pr) slot = server-receive m pr slot

-- Commit creates the exact slot; all other operations retain or preserve it.
tau-consistent : ∀ {p s t} → D.Tau p s t → Consistent s → Consistent t
tau-consistent (D.clientInternal _) slot = slot
tau-consistent (D.serverInternal pr) slot = server-tau pr slot
tau-consistent (D.clientCallback _ _) slot = slot
tau-consistent (D.serverCallback pr) slot = server-callback pr slot
tau-consistent (D.commitClient _) slot = slot
tau-consistent (D.commitServer {m = D.reply _} (S.send _)) slot = reply
tau-consistent (D.commitServer {m = D.done} S.finish) slot = done
tau-consistent (D.decodeClient _) slot = slot
tau-consistent (D.decodeServer _) slot = slot

-- Consistency survives arbitrary finite interleavings, not only a chosen drain schedule.
run-consistent : ∀ {p s rows t} → D.Run p s rows t → Consistent s → Consistent t
run-consistent D.stop slot = slot
run-consistent (D.internal pr run) slot = run-consistent run (tau-consistent pr slot)
run-consistent (D.visible pr run) slot = run-consistent run (step-consistent pr slot)

-- Every fresh paired execution has a structurally consistent pending server hook.
initial-consistent : ∀ {p rows t} → D.Run p D.initial rows t → Consistent t
initial-consistent run = run-consistent run vacant

-- A closed server has already discharged its Send-Done record.
closed-empty : ∀ {raw} → Consistent raw → D.serverState raw ≡ S.state S.closed 0 S.idle 0 true →
  D.pendingServerSend raw ≡ nothing
closed-empty vacant closed = refl
closed-empty reply ()
closed-empty done ()
