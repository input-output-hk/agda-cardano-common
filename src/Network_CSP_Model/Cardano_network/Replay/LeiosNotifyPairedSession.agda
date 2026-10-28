{-# OPTIONS --safe #-}

-- LeiosNotifyP: bounded request credits and exact retained-message FIFOs.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.LeiosNotifyPairedSession (k : ℕ) where
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.LeiosNotifyPipeline as N

-- Payloads are matched by the queues; local agency uses the existing kind abstraction.
next : N.Role → N.St → N.E → Maybe N.St
next = λ role s e → N.nextKind k role s (N.forget e)
open import Cardano_network.Replay.Paired N.St N.Msg N.msgEq next public
open import Cardano_network.Replay.PairedDecide N.St N.Msg N.msgEq next public
module Client = N.Spec k client
module Server = N.Spec k server

-- The pair accepts only fresh local sessions and empty initial channels.
initial : State
initial = fresh N.idle N.idle

-- Every paired run projects to a legal local client run.
client-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Client._⇒⟨_⟩_ (clientState s) (project client es) (clientState t)
client-trace done = Client.done
client-trace (tau () _)
client-trace (vis (clientSend pr) run) = Client.vis pr (client-trace run)
client-trace (vis (clientRecv pr) run) = Client.vis pr (client-trace run)
client-trace (vis (serverSend pr) run) = client-trace run
client-trace (vis (serverRecv pr) run) = client-trace run

-- Every paired run also projects to a legal server run.
server-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Server._⇒⟨_⟩_ (serverState s) (project server es) (serverState t)
server-trace done = Server.done
server-trace (tau () _)
server-trace (vis (clientSend pr) run) = server-trace run
server-trace (vis (clientRecv pr) run) = server-trace run
server-trace (vis (serverSend pr) run) = Server.vis pr (server-trace run)
server-trace (vis (serverRecv pr) run) = Server.vis pr (server-trace run)

-- Paired acceptance implies local client membership for the complete input.
compatible-client : ∀ {cs ss} → Compatible initial cs ss → Client.HasTrace N.idle cs
compatible-client run with merge-run run
... | t , pr = clientState t , subst
  (λ es → Client._⇒⟨_⟩_ N.idle es (clientState t)) (client-projection run) (client-trace pr)

-- Paired acceptance implies local server membership at the same configured bound.
compatible-server : ∀ {cs ss} → Compatible initial cs ss → Server.HasTrace N.idle ss
compatible-server run with merge-run run
... | t , pr = serverState t , subst
  (λ es → Server._⇒⟨_⟩_ N.idle es (serverState t)) (server-projection run) (server-trace pr)
