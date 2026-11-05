{-# OPTIONS --safe #-}

-- Client Done records require the server's Quit Receive record, not its possibly delayed Done Send hook.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownPrecheck
  (Notification Return : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.DoneOrigin Notification Return as Origin

-- Source scheduling cannot enter shutdown from the ordinary reader phases without a Quit Receive.
before-tau : ∀ {s t} → S.Tau s t → Phase.Before (S.reader s) → Phase.Before (S.reader t)
before-tau S.admitted before = Phase.register
before-tau S.excessive before = Phase.raising
before-tau S.registered before = Phase.awaitNext
before-tau S.setQuit ()
before-tau (S.claim _) before = before
before-tau (S.cancel _) before = before
before-tau (S.retire _) before = before
before-tau S.flush ()
before-tau S.drained ()
before-tau S.abort before = Phase.failed

-- Quit is the only visible source operation leaving the ordinary reader region.
before-step : ∀ {p s action t} → S.Step p s action t → (action ≡ S.recvQuit → ⊥) →
  Phase.Before (S.reader s) → Phase.Before (S.reader t)
before-step (S.receiveRequest _) absent before = Phase.admit
before-step (S.receiveQuit _) absent before = ⊥-elim (absent refl)
before-step (S.choose _ _) absent before = before
before-step (S.send _) absent before = before
before-step S.finish absent ()

-- Neither drained final source phase belongs to the pre-Quit reader region.
before-final : ∀ {s} → Phase.Before (S.reader s) → Server.Final s → ⊥
before-final () Server.ready-final
before-final () Server.closed-final

-- Transport commits/decodes retain server control; only explicit server source scheduling changes it.
driver-tau-before : ∀ {p s t} → D.Tau p s t →
  Phase.Before (S.reader (D.serverState s)) → Phase.Before (S.reader (D.serverState t))
driver-tau-before (D.clientInternal _) before = before
driver-tau-before (D.serverInternal step) before = before-tau step before
driver-tau-before (D.clientCallback _ _) before = before
driver-tau-before (D.serverCallback step) before = before-step step (λ ()) before
driver-tau-before (D.commitClient _) before = before
driver-tau-before (D.commitServer _) before = before
driver-tau-before (D.decodeClient _) before = before
driver-tau-before (D.decodeServer _) before = before

-- A hidden Quit decode does not substitute for the actual server Quit Receive record.
driver-step-before : ∀ {p s event t} → D.Step p s event t →
  (event ≡ D.serverRecv D.quit → ⊥) →
  Phase.Before (S.reader (D.serverState s)) → Phase.Before (S.reader (D.serverState t))
driver-step-before (D.clientSent _) absent before = before
driver-step-before (D.clientReceived _) absent before = before
driver-step-before (D.serverSent {m = D.reply _} step) absent before = before-step step (λ ()) before
driver-step-before (D.serverSent {m = D.done} step) absent before = before-step step (λ ()) before
driver-step-before (D.serverReceived {m = D.request} step) absent before = before-step step (λ ()) before
driver-step-before (D.serverReceived {m = D.quit} _) absent before = ⊥-elim (absent refl)

-- DoneOrigin handles both packet hooks and the FIFO, including a pending server Done Send.
before-no-client-done : ∀ {p s t} → D.Step p s (D.clientRecv D.done) t →
  Phase.Before (S.reader (D.serverState s)) → Origin.Origin s → ⊥
before-no-client-done (D.clientReceived _) before origin =
  before-final before (Origin.receiving origin refl)

-- Every continuation without a server Quit record remains unable to record a client Done.
without-quit : ∀ {p s events t} → D.Run p s events t →
  Phase.Before (S.reader (D.serverState s)) → Origin.Origin s →
  (D.serverRecv D.quit ∈ events → ⊥) → D.clientRecv D.done ∈ events → ⊥
without-quit D.stop before origin absent ()
without-quit (D.internal step rest) before origin absent present =
  without-quit rest (driver-tau-before step before) (Origin.tau-origin step origin) absent present
without-quit (D.visible step rest) before origin absent (here refl) = before-no-client-done step before origin
without-quit (D.visible step rest) before origin absent (there present) =
  without-quit rest (driver-step-before step (λ { refl → absent (here refl) }) before)
    (Origin.step-origin step origin) (λ member → absent (there member)) present

-- Membership in this one command constructor is decidable without equality on Notification values.
event-quit? : (events : List D.Event) → Dec (D.serverRecv D.quit ∈ events)
event-quit? [] = no λ ()
event-quit? (D.serverRecv D.quit ∷ events) = yes (here refl)
event-quit? (D.serverRecv D.request ∷ events) with event-quit? events
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }
event-quit? (D.clientSend _ ∷ events) with event-quit? events
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }
event-quit? (D.clientRecv _ ∷ events) with event-quit? events
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }
event-quit? (D.serverSend _ ∷ events) with event-quit? events
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }

-- Fresh packet origins and the initial ordinary phase discharge all auxiliary invariant premises.
recorded-origin : ∀ {p events t} → D.Run p D.initial events t →
  D.clientRecv D.done ∈ events → D.serverRecv D.quit ∈ events
recorded-origin {p} {events} source present with event-quit? events
... | yes received = received
... | no absent = ⊥-elim (without-quit source Phase.first (Origin.initial-origin {p = p} D.stop) absent present)

-- A typed client Done occurrence embeds as that exact endpoint-tagged driver record.
client-into-merge : ∀ {client server events} → Rows.Merge client server events →
  Rows.receiveResponse D.done ∈ client → D.clientRecv D.done ∈ events
client-into-merge Rows.empty ()
client-into-merge (Rows.client merged) (here refl) = here refl
client-into-merge (Rows.client merged) (there present) = there (client-into-merge merged present)
client-into-merge (Rows.server merged) present = there (client-into-merge merged present)

-- The exact server endpoint of a witnessed Quit record is retained in its original input list.
server-from-merge : ∀ {client server events} → Rows.Merge client server events →
  D.serverRecv D.quit ∈ events → Rows.receiveCommand D.quit ∈ server
server-from-merge Rows.empty ()
server-from-merge (Rows.client {row = Rows.sendCommand _} merged) (here ())
server-from-merge (Rows.client {row = Rows.receiveResponse _} merged) (here ())
server-from-merge (Rows.client merged) (there present) = server-from-merge merged present
server-from-merge (Rows.server {row = Rows.receiveCommand D.request} merged) (here ())
server-from-merge (Rows.server {row = Rows.receiveCommand D.quit} merged) (here refl) = here refl
server-from-merge (Rows.server {row = Rows.sendResponse _} merged) (here ())
server-from-merge (Rows.server merged) (there present) = there (server-from-merge merged present)

-- Constructor-only client Done membership retains the occurrence position and exact endpoint role.
client-done? : (client : List Rows.ClientRow) → Dec (Rows.receiveResponse D.done ∈ client)
client-done? [] = no λ ()
client-done? (Rows.receiveResponse D.done ∷ client) = yes (here refl)
client-done? (Rows.sendCommand _ ∷ client) with client-done? client
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }
client-done? (Rows.receiveResponse (D.reply _) ∷ client) with client-done? client
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }

-- Only a recorded Receive-Quit is evidence; a client Send or server Send cannot replace it.
server-quit? : (server : List Rows.ServerRow) → Dec (Rows.receiveCommand D.quit ∈ server)
server-quit? [] = no λ ()
server-quit? (Rows.receiveCommand D.quit ∷ server) = yes (here refl)
server-quit? (Rows.receiveCommand D.request ∷ server) with server-quit? server
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }
server-quit? (Rows.sendResponse _ ∷ server) with server-quit? server
... | yes present = yes (there present)
... | no absent = no λ { (here ()) ; (there present) → absent present }

-- This implication is necessary only; server Done publication and successful completion are not asserted.
Pass : List Rows.ClientRow → List Rows.ServerRow → Set
Pass client server = Rows.receiveResponse D.done ∈ client → Rows.receiveCommand D.quit ∈ server

-- The cheap finite-prefix decision uses no payload equality, callback contract or Return inhabitance.
decide : (client : List Rows.ClientRow) (server : List Rows.ServerRow) → Dec (Pass client server)
decide client server with client-done? client
... | no absent = yes λ present → ⊥-elim (absent present)
... | yes done with server-quit? server
...   | yes quit = yes λ _ → quit
...   | no absent = no λ implication → absent (implication done)

-- Every original fresh source run and every exact merge has the required recorded shutdown origin.
necessary : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Pass client server
necessary merged source present = server-from-merge merged (recorded-origin source (client-into-merge merged present))
