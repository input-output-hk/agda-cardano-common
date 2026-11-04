{-# OPTIONS --safe #-}

-- Physical Done is the unique final responder packet, independent of trace-hook order.
module Cardano_network.LeiosNotifyPipeLookahead.ResponseFlow
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- Before Done, each responder packet is an actual reply.
data Replies : List D.ServerMessage → Set where
  nil : Replies []
  reply : ∀ {m xs} → Replies xs → Replies (D.reply m ∷ xs)

-- Pending Send/Receive slots in this phase cannot contain Done.
data ReplySlot : Maybe D.ServerMessage → Set where
  vacant : ReplySlot nothing
  reply : ∀ {m} → ReplySlot (just (D.reply m))

-- A sealed responder FIFO ends in one Done after its remaining reply prefix.
data DoneQueue : List D.ServerMessage → Set where
  lastDone : DoneQueue (D.done ∷ [])
  reply : ∀ {m xs} → DoneQueue xs → DoneQueue (D.reply m ∷ xs)

-- The physical Done commit retains either its pending Send or its closed source control.
data Publication : S.State → Maybe D.ServerMessage → Set where
  pending : Publication (S.state S.doneReady 0 S.idle 0 true) (just D.done)
  recorded : Publication (S.state S.closed 0 S.idle 0 true) nothing

-- Appending a reply keeps the ordinary reply language.
snoc-reply : ∀ {xs} (m : S.Reply) → Replies xs → Replies (xs ∷ʳ D.reply m)
snoc-reply m nil = reply nil
snoc-reply m (reply rest) = reply (snoc-reply m rest)

-- Appending Done seals the exact current reply queue.
snoc-done : ∀ {xs} → Replies xs → DoneQueue (xs ∷ʳ D.done)
snoc-done nil = lastDone
snoc-done (reply rest) = reply (snoc-done rest)

-- Client hidden scheduling never enters closed control from a different phase.
tau-closed-source : ∀ {s t} → C.Tau s t → C.main t ≡ C.closed → C.main s ≡ C.closed
tau-closed-source C.registerResponse ()
tau-closed-source C.setStopIdle ()
tau-closed-source C.setStopBusy ()
tau-closed-source C.registerMarker ()
tau-closed-source C.optionalEmpty ()
tau-closed-source C.optionalResult ()
tau-closed-source C.blockingResult ()
tau-closed-source C.adjustArrival ()
tau-closed-source C.drainResult ()
tau-closed-source C.drained ()
tau-closed-source (C.startResponse _) eq = eq
tau-closed-source (C.startMarker _) eq = eq
tau-closed-source (C.keepReply _) eq = eq
tau-closed-source (C.discardReply _) eq = eq
tau-closed-source (C.countArrival _) eq = eq
tau-closed-source (C.publishResponse _) eq = eq
tau-closed-source (C.publishMarker _) eq = eq

-- A closed client stays closed through any hidden rule that has such a source.
tau-closed-target : ∀ {s t} → C.Tau s t → C.main s ≡ C.closed → C.main t ≡ C.closed
tau-closed-target C.registerResponse ()
tau-closed-target C.setStopIdle ()
tau-closed-target C.setStopBusy ()
tau-closed-target C.registerMarker ()
tau-closed-target C.optionalEmpty ()
tau-closed-target C.optionalResult ()
tau-closed-target C.blockingResult ()
tau-closed-target C.adjustArrival ()
tau-closed-target C.drainResult ()
tau-closed-target C.drained ()
tau-closed-target (C.startResponse _) eq = eq
tau-closed-target (C.startMarker _) eq = eq
tau-closed-target (C.keepReply _) eq = eq
tau-closed-target (C.discardReply _) eq = eq
tau-closed-target (C.countArrival _) eq = eq
tau-closed-target (C.publishResponse _) eq = eq
tau-closed-target (C.publishMarker _) eq = eq

-- Application callbacks cannot close an open client.
callback-open : ∀ {s a t} → D.ClientCallback a → C.Step s a t → C.main s ≢ C.closed → C.main t ≢ C.closed
callback-open D.continue C.continueZero ne = λ ()
callback-open D.continue (C.continueBelow _) ne = λ ()
callback-open D.continue (C.continueFull _ _) ne = λ ()
callback-open D.terminate C.stopRequested ne = λ ()
callback-open D.handled (C.delivered _) ne = ne

-- A callback from closed control retains that control if its premise is inhabited.
callback-closed : ∀ {s a t} → D.ClientCallback a → C.Step s a t → C.main s ≡ C.closed → C.main t ≡ C.closed
callback-closed D.continue C.continueZero ()
callback-closed D.continue (C.continueBelow _) ()
callback-closed D.continue (C.continueFull _ _) ()
callback-closed D.terminate C.stopRequested ()
callback-closed D.handled (C.delivered _) eq = eq

-- Client command Sends lead to ordinary, draining or Await-Done control, never closed.
send-open : ∀ {s t} (m : D.ClientMessage) → C.Step s (D.clientSendAction m) t → C.main t ≢ C.closed
send-open D.request C.sentRequest = λ ()
send-open D.quit C.sentQuitIdle = λ ()
send-open D.quit C.sentQuitBusy = λ ()

-- Those command Sends cannot start from an already closed main thread.
send-closed : ∀ {s t} (m : D.ClientMessage) → C.Step s (D.clientSendAction m) t →
  C.main s ≡ C.closed → C.main t ≡ C.closed
send-closed D.request C.sentRequest ()
send-closed D.quit C.sentQuitIdle ()
send-closed D.quit C.sentQuitBusy ()

-- Hidden server scheduling never closes the reader.
server-tau-open : ∀ {s t} → S.Tau s t → S.reader s ≢ S.closed → S.reader t ≢ S.closed
server-tau-open S.admitted ne = λ ()
server-tau-open S.excessive ne = λ ()
server-tau-open S.registered ne = λ ()
server-tau-open S.setQuit ne = λ ()
server-tau-open (S.claim _) ne = ne
server-tau-open (S.cancel _) ne = ne
server-tau-open (S.retire _) ne = ne
server-tau-open S.flush ne = λ ()
server-tau-open S.drained ne = λ ()
server-tau-open S.abort ne = λ ()

-- No server scheduling remains enabled in either physical-Done publication phase.
publication-no-tau : ∀ {s ps t} → Publication s ps → S.Tau s t → ⊥
publication-no-tau pending ()
publication-no-tau recorded ()

-- Both publication phases have idle sender control, excluding another next result.
publication-no-next : ∀ {p s ps m t} → Publication s ps → S.Step p s (S.nextReply m) t → ⊥
publication-no-next pending ()
publication-no-next recorded ()

-- The final publication phases cannot consume another initiator command.
publication-no-receive : ∀ {p s ps t} (m : D.ClientMessage) →
  S.Step p s (D.serverRecvAction m) t → Publication s ps → ⊥
publication-no-receive D.request (S.receiveRequest _) ()
publication-no-receive D.quit (S.receiveQuit _) ()

-- A discharged Done Send belongs to a closed server, which cannot commit again.
publication-no-send : ∀ {p s t} (m : D.ServerMessage) →
  S.Step p s (D.serverSendAction m) t → Publication s nothing → ⊥
publication-no-send m () recorded

-- Packet/control phases include both possible orders of the independent Done trace hooks.
data Flow (c : C.State) (s : S.State) : List D.ServerMessage → Maybe D.ServerMessage → Maybe D.ServerMessage → Set where
  openFlow : ∀ {sc ps rc} → Replies sc → ReplySlot ps → ReplySlot rc →
    S.reader s ≢ S.closed → C.main c ≢ C.closed → Flow c s sc ps rc
  queued : ∀ {sc ps rc} → DoneQueue sc → Publication s ps → ReplySlot rc → C.main c ≢ C.closed → Flow c s sc ps rc
  decoded : ∀ {ps} → Publication s ps → C.main c ≢ C.closed → Flow c s [] ps (just D.done)
  received : ∀ {ps} → Publication s ps → C.main c ≡ C.closed → Flow c s [] ps nothing

-- Ordinary receiver scheduling preserves the packet position and open/closed control relation.
client-tau : ∀ {c c′ s sc ps rc} → C.Tau c c′ → Flow c s sc ps rc → Flow c′ s sc ps rc
client-tau pr (openFlow sc ps rc sn cn) = openFlow sc ps rc sn (λ eq → cn (tau-closed-source pr eq))
client-tau pr (queued sc pub rc cn) = queued sc pub rc (λ eq → cn (tau-closed-source pr eq))
client-tau pr (decoded pub cn) = decoded pub (λ eq → cn (tau-closed-source pr eq))
client-tau pr (received pub eq) = received pub (tau-closed-target pr eq)

-- Successful application callbacks preserve the same physical-packet phase.
client-callback : ∀ {c c′ s sc ps rc a} → D.ClientCallback a → C.Step c a c′ →
  Flow c s sc ps rc → Flow c′ s sc ps rc
client-callback tag pr (openFlow sc ps rc sn cn) = openFlow sc ps rc sn (callback-open tag pr cn)
client-callback tag pr (queued sc pub rc cn) = queued sc pub rc (callback-open tag pr cn)
client-callback tag pr (decoded pub cn) = decoded pub (callback-open tag pr cn)
client-callback tag pr (received pub eq) = received pub (callback-closed tag pr eq)

-- Initiator command records do not move responder packets or consume Done.
client-send : ∀ {c c′ s sc ps rc} (m : D.ClientMessage) → C.Step c (D.clientSendAction m) c′ →
  Flow c s sc ps rc → Flow c′ s sc ps rc
client-send m pr (openFlow sc ps rc sn cn) = openFlow sc ps rc sn (send-open m pr)
client-send m pr (queued sc pub rc cn) = queued sc pub rc (send-open m pr)
client-send m pr (decoded pub cn) = decoded pub (send-open m pr)
client-send m pr (received pub eq) = received pub (send-closed m pr eq)

-- No server scheduling can append new work after Done is physically committed.
server-tau : ∀ {c s s′ sc ps rc} → S.Tau s s′ → Flow c s sc ps rc → Flow c s′ sc ps rc
server-tau pr (openFlow sc ps rc sn cn) = openFlow sc ps rc (server-tau-open pr sn) cn
server-tau pr (queued sc pub rc cn) = ⊥-elim (publication-no-tau pub pr)
server-tau pr (decoded pub cn) = ⊥-elim (publication-no-tau pub pr)
server-tau pr (received pub eq) = ⊥-elim (publication-no-tau pub pr)

-- Before publication, next selection retains the same reader and queue position.
server-next : ∀ {p c s s′ sc ps rc m} → S.Step p s (S.nextReply m) s′ →
  Flow c s sc ps rc → Flow c s′ sc ps rc
server-next (S.choose _ _) (openFlow sc ps rc sn cn) = openFlow sc ps rc sn cn
server-next pr (queued sc pub rc cn) = ⊥-elim (publication-no-next pub pr)
server-next pr (decoded pub cn) = ⊥-elim (publication-no-next pub pr)
server-next pr (received pub eq) = ⊥-elim (publication-no-next pub pr)

-- Command receives occur before Done publication and cannot close either endpoint.
server-receive : ∀ {p c s s′ sc ps rc} (m : D.ClientMessage) → S.Step p s (D.serverRecvAction m) s′ →
  Flow c s sc ps rc → Flow c s′ sc ps rc
server-receive D.request (S.receiveRequest _) (openFlow sc ps rc sn cn) = openFlow sc ps rc (λ ()) cn
server-receive D.quit (S.receiveQuit _) (openFlow sc ps rc sn cn) = openFlow sc ps rc (λ ()) cn
server-receive m pr (queued sc pub rc cn) = ⊥-elim (publication-no-receive m pr pub)
server-receive m pr (decoded pub cn) = ⊥-elim (publication-no-receive m pr pub)
server-receive m pr (received pub eq) = ⊥-elim (publication-no-receive m pr pub)

-- Physical responder commit either appends a reply or uniquely seals the queue with Done.
commit : ∀ {p c s s′ sc rc} (m : D.ServerMessage) → S.Step p s (D.serverSendAction m) s′ →
  Flow c s sc nothing rc → Flow c s (sc ∷ʳ m) (just m) rc
commit (D.reply m) (S.send _) (openFlow sc vacant rc sn cn) = openFlow (snoc-reply m sc) reply rc sn cn
commit D.done S.finish (openFlow sc vacant rc sn cn) = queued (snoc-done sc) pending rc cn
commit m pr (queued sc pub rc cn) = ⊥-elim (publication-no-send m pr pub)
commit m pr (decoded pub cn) = ⊥-elim (publication-no-send m pr pub)
commit m pr (received pub eq) = ⊥-elim (publication-no-send m pr pub)

-- Recording the server Send closes publication without modifying the queued physical packet.
server-record : ∀ {p c s s′ sc rc} (m : D.ServerMessage) → S.Step p s (D.serverSendAction m) s′ →
  Flow c s sc (just m) rc → Flow c s′ sc nothing rc
server-record (D.reply m) (S.send _) (openFlow sc reply rc sn cn) = openFlow sc vacant rc sn cn
server-record (D.reply m) pr (queued sc () rc cn)
server-record (D.reply m) pr (decoded () cn)
server-record (D.reply m) pr (received () eq)
server-record D.done pr (openFlow sc () rc sn cn)
server-record D.done S.finish (queued sc pending rc cn) = queued sc recorded rc cn
server-record D.done S.finish (decoded pending cn) = decoded recorded cn
server-record D.done S.finish (received pending eq) = received recorded eq

-- Decode moves the exact head to its Receive hook, preserving the unique final Done.
decode : ∀ {c s sc ps} (m : D.ServerMessage) → Flow c s (m ∷ sc) ps nothing → Flow c s sc ps (just m)
decode (D.reply m) (openFlow (reply sc) ps vacant sn cn) = openFlow sc ps reply sn cn
decode (D.reply m) (queued (reply sc) pub vacant cn) = queued sc pub reply cn
decode D.done (openFlow () ps vacant sn cn)
decode D.done (queued lastDone pub vacant cn) = decoded pub cn

-- Receive-Done closes the client only after that exact packet has been decoded.
client-record : ∀ {c c′ s sc ps} (m : D.ServerMessage) → C.Step c (D.clientRecvAction m) c′ →
  Flow c s sc ps (just m) → Flow c′ s sc ps nothing
client-record (D.reply m) (C.receivedReply _) (openFlow sc ps reply sn cn) = openFlow sc ps vacant sn cn
client-record (D.reply m) (C.receivedReply _) (queued sc pub reply cn) = queued sc pub vacant cn
client-record D.done pr (openFlow sc ps () sn cn)
client-record D.done pr (queued sc pub () cn)
client-record D.done C.receivedDone (decoded pub cn) = received pub refl

-- The driver supplies responder FIFO and pending hook fields without a ghost history.
Consistent : D.State → Set
Consistent raw = Flow (D.clientState raw) (D.serverState raw) (D.serverToClient raw)
  (D.pendingServerSend raw) (D.pendingClientRecv raw)

-- All four kinds of visible record preserve this responder language.
step-consistent : ∀ {p s row t} → D.Step p s row t → Consistent s → Consistent t
step-consistent (D.clientSent {m = m} pr) flow = client-send m pr flow
step-consistent (D.serverSent {m = m} pr) flow = server-record m pr flow
step-consistent (D.clientReceived {m = m} pr) flow = client-record m pr flow
step-consistent (D.serverReceived {m = m} pr) flow = server-receive m pr flow

-- Hidden operations preserve exact packet placement, including Receive-before-Send schedules.
tau-consistent : ∀ {p s t} → D.Tau p s t → Consistent s → Consistent t
tau-consistent (D.clientInternal pr) flow = client-tau pr flow
tau-consistent (D.serverInternal pr) flow = server-tau pr flow
tau-consistent (D.clientCallback tag pr) flow = client-callback tag pr flow
tau-consistent (D.serverCallback pr) flow = server-next pr flow
tau-consistent (D.commitClient _) flow = flow
tau-consistent (D.commitServer {m = m} pr) flow = commit m pr flow
tau-consistent (D.decodeClient {m = m} _) flow = decode m flow
tau-consistent (D.decodeServer _) flow = flow

-- Any finite continuation preserves the same publication and delivery phase.
run-consistent : ∀ {p s rows t} → D.Run p s rows t → Consistent s → Consistent t
run-consistent D.stop flow = flow
run-consistent (D.internal pr run) flow = run-consistent run (tau-consistent pr flow)
run-consistent (D.visible pr run) flow = run-consistent run (step-consistent pr flow)

-- Fresh runs start with no packets and neither endpoint closed.
initial-consistent : ∀ {p rows t} → D.Run p D.initial rows t → Consistent t
initial-consistent run = run-consistent run (openFlow nil vacant vacant (λ ()) (λ ()))

-- Fresh closed client control implies there is no residual responder packet or Receive hook.
client-closed : ∀ {raw} → Consistent raw → C.main (D.clientState raw) ≡ C.closed →
  (D.serverToClient raw ≡ [] × D.pendingClientRecv raw ≡ nothing)
client-closed (openFlow sc ps rc sn cn) eq = ⊥-elim (cn eq)
client-closed (queued sc pub rc cn) eq = ⊥-elim (cn eq)
client-closed (decoded pub cn) eq = ⊥-elim (cn eq)
client-closed (received pub ce) eq = refl , refl

-- A closed server has discharged the final Done Send slot in every publication phase.
server-closed : ∀ {raw} → Consistent raw → S.reader (D.serverState raw) ≡ S.closed →
  D.pendingServerSend raw ≡ nothing
server-closed (openFlow sc ps rc sn cn) eq = ⊥-elim (sn eq)
server-closed (queued sc pending rc cn) ()
server-closed (queued sc recorded rc cn) eq = refl
server-closed (decoded pending cn) ()
server-closed (decoded recorded cn) eq = refl
server-closed (received pending ce) ()
server-closed (received recorded ce) eq = refl
