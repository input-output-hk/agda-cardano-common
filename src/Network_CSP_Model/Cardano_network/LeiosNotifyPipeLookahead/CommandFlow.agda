{-# OPTIONS --safe #-}

-- Physical Quit seals the initiator FIFO before the server observes that command.
module Cardano_network.LeiosNotifyPipeLookahead.CommandFlow
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Server

-- After the client Quit record only draining and final control remain.
data AfterQuit : C.Main → Set where
  drain : AfterQuit C.draining
  await : AfterQuit C.awaitDone
  closed : AfterQuit C.closed

-- A physical Quit is either awaiting its Send hook or has advanced client control.
data Seal : C.Main → Maybe D.ClientMessage → Set where
  pending : ∀ {b} → Seal (C.writingQuit b) (just D.quit)
  recorded : ∀ {m} → AfterQuit m → Seal m nothing

-- Receiver scheduling cannot reopen command issuance after physical Quit.
seal-tau : ∀ {s t pc} → C.Tau s t → Seal (C.main s) pc → Seal (C.main t) pc
seal-tau C.registerResponse (recorded ())
seal-tau C.setStopIdle (recorded ())
seal-tau C.setStopBusy (recorded ())
seal-tau C.registerMarker (recorded ())
seal-tau C.optionalEmpty (recorded ())
seal-tau C.optionalResult (recorded ())
seal-tau C.blockingResult (recorded ())
seal-tau C.adjustArrival (recorded ())
seal-tau C.drainResult (recorded drain) = recorded drain
seal-tau C.drained (recorded drain) = recorded await
seal-tau (C.startResponse _) seal = seal
seal-tau (C.startMarker _) seal = seal
seal-tau (C.keepReply _) seal = seal
seal-tau (C.discardReply _) seal = seal
seal-tau (C.countArrival _) seal = seal
seal-tau (C.publishResponse _) seal = seal
seal-tau (C.publishMarker _) seal = seal

-- The erased application actions cannot reopen the sealed main thread.
seal-callback : ∀ {s a t pc} → D.ClientCallback a → C.Step s a t →
  Seal (C.main s) pc → Seal (C.main t) pc
seal-callback D.continue C.continueZero (recorded ())
seal-callback D.continue (C.continueBelow _) (recorded ())
seal-callback D.continue (C.continueFull _ _) (recorded ())
seal-callback D.terminate C.stopRequested (recorded ())
seal-callback D.handled (C.delivered _) seal = seal

-- Actual responder receives only advance sealed draining/final control.
seal-receive : ∀ {s t pc} (m : D.ServerMessage) → C.Step s (D.clientRecvAction m) t →
  Seal (C.main s) pc → Seal (C.main t) pc
seal-receive (D.reply _) (C.receivedReply _) seal = seal
seal-receive D.done C.receivedDone (recorded await) = recorded closed

-- The Quit Send record discharges the sole pending command hook.
seal-send : ∀ {s t} (m : D.ClientMessage) → C.Step s (D.clientSendAction m) t →
  Seal (C.main s) (just m) → Seal (C.main t) nothing
seal-send D.request C.sentRequest ()
seal-send D.quit C.sentQuitIdle pending = recorded await
seal-send D.quit C.sentQuitBusy pending = recorded drain

-- No later physical command can be committed after a sealed Send slot is discharged.
no-new-command : ∀ {s t} (m : D.ClientMessage) → C.Step s (D.clientSendAction m) t →
  Seal (C.main s) nothing → ⊥
no-new-command D.request C.sentRequest (recorded ())
no-new-command D.quit C.sentQuitIdle (recorded ())
no-new-command D.quit C.sentQuitBusy (recorded ())

-- Before physical Quit, command queues contain requests only.
data Requests : List D.ClientMessage → Set where
  nil : Requests []
  request : ∀ {xs} → Requests xs → Requests (D.request ∷ xs)

-- The corresponding pending Send/Receive slots also exclude Quit.
data RequestSlot : Maybe D.ClientMessage → Set where
  vacant : RequestSlot nothing
  request : RequestSlot (just D.request)

-- Appending one request preserves the open command language.
snoc-request : ∀ {xs} → Requests xs → Requests (xs ∷ʳ D.request)
snoc-request nil = request nil
snoc-request (request rest) = request (snoc-request rest)

-- The sealed queue has one final Quit preceded by zero or more requests.
data QuitQueue : List D.ClientMessage → Set where
  lastQuit : QuitQueue (D.quit ∷ [])
  request : ∀ {xs} → QuitQueue xs → QuitQueue (D.request ∷ xs)

-- Physical Quit closes an ordinary request queue without permitting a later suffix.
snoc-quit : ∀ {xs} → Requests xs → QuitQueue (xs ∷ʳ D.quit)
snoc-quit nil = lastQuit
snoc-quit (request rest) = request (snoc-quit rest)

-- Before-Quit server scheduling retains its ordinary reader tag, including faults.
before-tau : ∀ {s t} → S.Tau s t → Phase.Before (S.reader s) → Phase.Before (S.reader t)
before-tau S.admitted _ = Phase.register
before-tau S.excessive _ = Phase.raising
before-tau S.registered _ = Phase.awaitNext
before-tau S.setQuit ()
before-tau (S.claim _) pre = pre
before-tau (S.cancel _) pre = pre
before-tau (S.retire _) pre = pre
before-tau S.flush ()
before-tau S.drained ()
before-tau S.abort _ = Phase.failed

-- Callback selection never changes reader control.
before-next : ∀ {p s m t} → S.Step p s (S.nextReply m) t →
  Phase.Before (S.reader s) → Phase.Before (S.reader t)
before-next (S.choose _ _) pre = pre

-- A source cannot send Done while its reader still precedes Quit.
before-send : ∀ {p s t} (m : D.ServerMessage) → S.Step p s (D.serverSendAction m) t →
  Phase.Before (S.reader s) → Phase.Before (S.reader t)
before-send (D.reply _) (S.send _) pre = pre
before-send D.done S.finish ()

-- These four stages retain the physical Quit position and both endpoint control phases.
data Flow (c : C.State) (s : S.State) : List D.ClientMessage → Maybe D.ClientMessage → Maybe D.ClientMessage → Set where
  openFlow : ∀ {cs pc rs} → RequestSlot pc → Requests cs → RequestSlot rs → Phase.Before (S.reader s) → Flow c s cs pc rs
  queued : ∀ {cs pc rs} → QuitQueue cs → Seal (C.main c) pc → RequestSlot rs → Phase.Before (S.reader s) →
    Flow c s cs pc rs
  decoded : ∀ {pc} → Seal (C.main c) pc → Phase.Before (S.reader s) → Flow c s [] pc (just D.quit)
  received : ∀ {pc} → Seal (C.main c) pc → Server.Stopping s → Flow c s [] pc nothing

-- Receiver/callback activity only changes the client field and preserves an existing seal.
map-client : ∀ {c c′ s cs pc rs} → (Seal (C.main c) pc → Seal (C.main c′) pc) →
  Flow c s cs pc rs → Flow c′ s cs pc rs
map-client keep (openFlow pc cs rs pre) = openFlow pc cs rs pre
map-client keep (queued xs seal rs pre) = queued xs (keep seal) rs pre
map-client keep (decoded seal pre) = decoded (keep seal) pre
map-client keep (received seal stopping) = received (keep seal) stopping

-- Independent server work preserves its appropriate ordinary/shutdown region.
map-server : ∀ {c s s′ cs pc rs} →
  (Phase.Before (S.reader s) → Phase.Before (S.reader s′)) →
  (Server.Stopping s → Server.Stopping s′) → Flow c s cs pc rs → Flow c s′ cs pc rs
map-server preKeep stopKeep (openFlow pc cs rs pre) = openFlow pc cs rs (preKeep pre)
map-server preKeep stopKeep (queued xs seal rs pre) = queued xs seal rs (preKeep pre)
map-server preKeep stopKeep (decoded seal pre) = decoded seal (preKeep pre)
map-server preKeep stopKeep (received seal stopping) = received seal (stopKeep stopping)

-- A client Send changes the slot and control but never appends the physical command twice.
client-record : ∀ {c c′ s cs rs} (m : D.ClientMessage) → C.Step c (D.clientSendAction m) c′ →
  Flow c s cs (just m) rs → Flow c′ s cs nothing rs
client-record D.request C.sentRequest (openFlow request cs rs pre) = openFlow vacant cs rs pre
client-record D.quit pr (openFlow () cs rs pre)
client-record m pr (queued xs seal rs pre) = queued xs (seal-send m pr seal) rs pre
client-record m pr (decoded seal pre) = decoded (seal-send m pr seal) pre
client-record m pr (received seal stopping) = received (seal-send m pr seal) stopping

-- The server consumes the unique physical Quit only after all earlier commands.
server-record : ∀ {p c s s′ cs pc} (m : D.ClientMessage) → S.Step p s (D.serverRecvAction m) s′ →
  Flow c s cs pc (just m) → Flow c s′ cs pc nothing
server-record D.request (S.receiveRequest _) (openFlow pc cs request pre) = openFlow pc cs vacant Phase.admit
server-record D.request (S.receiveRequest _) (queued xs seal request pre) = queued xs seal vacant Phase.admit
server-record D.quit pr (openFlow pc cs () pre)
server-record D.quit pr (queued xs seal () pre)
server-record D.quit (S.receiveQuit _) (decoded seal pre) = received seal Server.publishing

-- Commit appends a request or the unique final Quit, before either corresponding trace hook.
commit : ∀ {c c′ s cs rs} (m : D.ClientMessage) → C.Step c (D.clientSendAction m) c′ →
  Flow c s cs nothing rs → Flow c s (cs ∷ʳ m) (just m) rs
commit D.request C.sentRequest (openFlow vacant cs rs pre) = openFlow request (snoc-request cs) rs pre
commit D.quit C.sentQuitIdle (openFlow vacant cs rs pre) = queued (snoc-quit cs) pending rs pre
commit D.quit C.sentQuitBusy (openFlow vacant cs rs pre) = queued (snoc-quit cs) pending rs pre
commit m pr (queued xs seal rs pre) = ⊥-elim (no-new-command m pr seal)
commit m pr (decoded seal pre) = ⊥-elim (no-new-command m pr seal)
commit m pr (received seal stopping) = ⊥-elim (no-new-command m pr seal)

-- Decode respects the exact head, exposing Quit only when its request prefix is empty.
decode : ∀ {c s cs pc} (m : D.ClientMessage) → Flow c s (m ∷ cs) pc nothing → Flow c s cs pc (just m)
decode D.request (openFlow pc (request cs) vacant pre) = openFlow pc cs request pre
decode D.request (queued (request xs) seal vacant pre) = queued xs seal request pre
decode D.quit (openFlow pc () vacant pre)
decode D.quit (queued lastQuit seal vacant pre) = decoded seal pre

-- The actual driver state supplies all fields of this command-flow invariant.
Consistent : D.State → Set
Consistent raw = Flow (D.clientState raw) (D.serverState raw) (D.clientToServer raw)
  (D.pendingClientSend raw) (D.pendingServerRecv raw)

-- Every wire record preserves the sealed initiator language and endpoint agency.
step-consistent : ∀ {p s row t} → D.Step p s row t → Consistent s → Consistent t
step-consistent (D.clientSent {m = m} pr) flow = client-record m pr flow
step-consistent (D.serverSent {m = m} pr) flow = map-server (before-send m pr) (Server.step-stays pr) flow
step-consistent (D.clientReceived {m = m} pr) flow = map-client (seal-receive m pr) flow
step-consistent (D.serverReceived {m = m} pr) flow = server-record m pr flow

-- Commit/decode and independent scheduling preserve the same structural command phases.
tau-consistent : ∀ {p s t} → D.Tau p s t → Consistent s → Consistent t
tau-consistent (D.clientInternal pr) flow = map-client (seal-tau pr) flow
tau-consistent (D.serverInternal pr) flow = map-server (before-tau pr) (Server.tau-stays pr) flow
tau-consistent (D.clientCallback tag pr) flow = map-client (seal-callback tag pr) flow
tau-consistent (D.serverCallback pr) flow = map-server (before-next pr) (Server.step-stays pr) flow
tau-consistent (D.commitClient {m = m} pr) flow = commit m pr flow
tau-consistent (D.commitServer _) flow = flow
tau-consistent (D.decodeClient _) flow = flow
tau-consistent (D.decodeServer {m = m} _) flow = decode m flow

-- Fresh captures begin with no Quit in the queues, slots or endpoint control.
run-consistent : ∀ {p s rows t} → D.Run p s rows t → Consistent s → Consistent t
run-consistent D.stop flow = flow
run-consistent (D.internal pr run) flow = run-consistent run (tau-consistent pr flow)
run-consistent (D.visible pr run) flow = run-consistent run (step-consistent pr flow)

-- Every fresh paired run satisfies physical Quit sealing, including delayed Send records.
initial-consistent : ∀ {p rows t} → D.Run p D.initial rows t → Consistent t
initial-consistent run = run-consistent run (openFlow vacant nil vacant Phase.first)

-- An ordinary reader tag excludes closed control without a hidden reachability premise.
before-not-closed : ∀ {r} → Phase.Before r → r ≡ S.closed → ⊥
before-not-closed Phase.first ()
before-not-closed Phase.admit ()
before-not-closed Phase.register ()
before-not-closed Phase.awaitNext ()
before-not-closed Phase.raising ()
before-not-closed Phase.failed ()

-- Once the server is closed, the initiator direction is empty and the client is sealed.
closed-commands : ∀ {raw} → Consistent raw → S.reader (D.serverState raw) ≡ S.closed →
  (Seal (C.main (D.clientState raw)) (D.pendingClientSend raw) ×
   D.clientToServer raw ≡ [] × D.pendingServerRecv raw ≡ nothing)
closed-commands (openFlow pc cs rs pre) finished = ⊥-elim (before-not-closed pre finished)
closed-commands (queued xs seal rs pre) finished = ⊥-elim (before-not-closed pre finished)
closed-commands (decoded seal pre) finished = ⊥-elim (before-not-closed pre finished)
closed-commands (received seal stopping) finished = seal , refl , refl
