{-# OPTIONS --safe #-}

-- Role-specific shutdown guarantees retain the actual channel/trace boundary.
module Cardano_network.LeiosNotifyPipeLookahead.DriverShutdown
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as Accounting
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification Return as Client
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.DoneOrigin Notification Return as Origin

-- New client RequestNext records are forbidden on the entire termination path.
no-client-request : ∀ {p s t} → Client.stopping (C.main (D.clientState s)) ≡ true →
  D.Step p s (D.clientSend D.request) t → ⊥
no-client-request stopping (D.clientSent pr) = Client.no-request stopping pr

-- A new physical RequestNext commit is forbidden as well, before its Send trace hook.
no-request-commit : ∀ {p s t} → D.Tau p s t →
  Client.stopping (C.main (D.clientState s)) ≡ true →
  D.pendingClientSend s ≡ nothing → D.pendingClientSend t ≡ just D.request → ⊥
no-request-commit (D.clientInternal _) _ refl ()
no-request-commit (D.serverInternal _) _ refl ()
no-request-commit (D.clientCallback _ _) _ refl ()
no-request-commit (D.serverCallback _) _ refl ()
no-request-commit (D.commitClient {m = D.request} pr) stopping _ _ = Client.no-request stopping pr
no-request-commit (D.commitClient {m = D.quit} _) _ _ ()
no-request-commit (D.commitServer _) _ refl ()
no-request-commit (D.decodeClient _) _ refl ()
no-request-commit (D.decodeServer _) _ refl ()

-- After the flag, a hidden transition can newly select only Canceled, never a normal.
new-selection-after-flag : ∀ {p s t msg} → D.Tau p s t → S.quitFlag (D.serverState s) ≡ true →
  S.sender (D.serverState s) ≡ S.claimed → S.sender (D.serverState t) ≡ S.selected msg → msg ≡ S.canceled
new-selection-after-flag (D.clientInternal _) _ refl ()
new-selection-after-flag (D.serverInternal pr) flag before after = Server.tau-new-selection pr flag before after
new-selection-after-flag (D.clientCallback _ _) _ refl ()
new-selection-after-flag (D.serverCallback (S.choose _ _)) () _ _
new-selection-after-flag (D.commitClient _) _ refl ()
new-selection-after-flag (D.commitServer _) _ refl ()
new-selection-after-flag (D.decodeClient _) _ refl ()
new-selection-after-flag (D.decodeServer _) _ refl ()

-- Server Send-Done observes the exact drained source state and clears only its own hook.
server-done : ∀ {p s t} → D.Step p s (D.serverSend D.done) t →
  (D.serverState s ≡ S.state S.doneReady 0 S.idle 0 true) ×
  (D.serverState t ≡ S.state S.closed 0 S.idle 0 true) ×
  (D.pendingServerSend s ≡ just D.done) × (D.pendingServerSend t ≡ nothing)
server-done (D.serverSent S.finish) = refl , refl , refl , refl

-- Both sides of the server Done trace hook have zero actual server work.
server-done-final : ∀ {p s t} → D.Step p s (D.serverSend D.done) t →
  Server.Final (D.serverState s) × Server.Final (D.serverState t)
server-done-final (D.serverSent S.finish) = Server.ready-final , Server.closed-final

-- Creating the Done packet itself already requires the same drained server state.
commit-done : ∀ {p s t} → D.Tau p s t →
  D.pendingServerSend s ≡ nothing → D.pendingServerSend t ≡ just D.done →
  Server.Final (D.serverState s) × Server.Final (D.serverState t)
commit-done (D.clientInternal _) refl ()
commit-done (D.serverInternal _) refl ()
commit-done (D.clientCallback _ _) refl ()
commit-done (D.serverCallback _) refl ()
commit-done (D.commitClient _) refl ()
commit-done (D.commitServer {m = D.reply _} _) _ ()
commit-done (D.commitServer {m = D.done} S.finish) _ _ = Server.ready-final , Server.ready-final
commit-done (D.decodeClient _) refl ()
commit-done (D.decodeServer _) refl ()

-- Client Done retains the selected return value and cannot finish with outstanding count.
record ClientDone (raw : D.State) : Set where
  constructor client-done
  field
    closed : C.main (D.clientState raw) ≡ C.closed
    zero-count : C.inFlight (D.clientState raw) ≡ 0
    stopped : C.stopFlag (D.clientState raw) ≡ true
    returned : Σ[ x ∈ Return ] C.returnValue (D.clientState raw) ≡ just x
open ClientDone public

-- The local Done receive rule supplies these guards even before reachability is used.
client-done-control : ∀ {p s t} → D.Step p s (D.clientRecv D.done) t → ClientDone t
client-done-control (D.clientReceived (C.receivedDone {x = x})) = client-done refl refl refl (x , refl)

-- Completion concerns both peers' source work and permits a delayed server Done trace hook.
record Completed (raw : D.State) : Set where
  constructor completed
  field
    client-control : ClientDone raw
    client-empty : Accounting.Empty (D.clientState raw)
    server-final : Server.Final (D.serverState raw)
open Completed public

-- Generic source projections keep the same callback contract throughout a run.
module For (contract : S.Contract) where
  -- Actual client source runs account for every registration, marker and result.
  module Endpoint = Projection.For contract

  -- Driver transport and remote work do not disturb the client inventory invariant.
  client-accounted : ∀ {rows t} → D.Run contract D.initial rows t → Accounting.Accounted (D.clientState t)
  client-accounted run with Endpoint.client run
  ... | actions , source , matching = Accounting.initial-accounted source

  -- Once shutdown has started, arbitrary paired continuations cannot reopen the client.
  client-stays-stopping : ∀ {s rows t} → D.Run contract s rows t →
    Client.stopping (C.main (D.clientState s)) ≡ true → Client.stopping (C.main (D.clientState t)) ≡ true
  client-stays-stopping run stopping with Endpoint.client run
  ... | actions , source , matching = Client.run-stopping source stopping

  -- Flushed server status also survives arbitrary client/transport interleavings.
  server-stays-final : ∀ {s rows t} → D.Run contract s rows t →
    Server.Final (D.serverState s) → Server.Final (D.serverState t)
  server-stays-final run final with Endpoint.server run
  ... | actions , source , matching = Server.run-final source final

  -- The responder's true flag persists through both peers' intervening operations.
  server-stays-flagged : ∀ {s rows t} → D.Run contract s rows t →
    S.quitFlag (D.serverState s) ≡ true → S.quitFlag (D.serverState t) ≡ true
  server-stays-flagged run published with Endpoint.server run
  ... | actions , source , matching = Server.run-flag source published

  -- Every later new selection is cancellation, rather than only the immediately next step.
  new-selection-after-publication : ∀ {s rows t u msg} → D.Run contract s rows t →
    S.quitFlag (D.serverState s) ≡ true → D.Tau contract t u →
    S.sender (D.serverState t) ≡ S.claimed → S.sender (D.serverState u) ≡ S.selected msg → msg ≡ S.canceled
  new-selection-after-publication run published next =
    new-selection-after-flag next (server-stays-flagged run published)

  -- In fresh paired runs, Done really follows empty jobs, idle receiver and empty results.
  client-done-drained : ∀ {rows s t} → D.Run contract D.initial rows s →
    D.Step contract s (D.clientRecv D.done) t →
    Accounting.Empty (D.clientState s) × Accounting.Empty (D.clientState t)
  client-done-drained {s = s} prefix (D.clientReceived C.receivedDone)
    with Accounting.empty-at-zero {c = D.clientState s} (client-accounted prefix) refl refl
  ... | Accounting.empty js r rs = Accounting.empty js r rs , Accounting.empty js r rs

  -- The received physical Done also proves that the actual responder has drained its work.
  client-done-server : ∀ {rows s t} → D.Run contract D.initial rows s →
    D.Step contract s (D.clientRecv D.done) t →
    Server.Final (D.serverState s) × Server.Final (D.serverState t)
  client-done-server prefix (D.clientReceived C.receivedDone)
    with Origin.receiving (Origin.initial-origin prefix) refl
  ... | final = final , final

  -- A fresh Done receive certifies both peers' completed work, not all trace-hook publication.
  client-done-completed : ∀ {rows s t} → D.Run contract D.initial rows s →
    D.Step contract s (D.clientRecv D.done) t → Completed t
  client-done-completed prefix step with client-done-drained prefix step | client-done-server prefix step
  ... | before , after | final-before , final-after = completed (client-done-control step) after final-after
