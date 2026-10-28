{-# OPTIONS --safe #-}

-- ChainSync pilot: a bounded requester and sequential producer with two FIFOs.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.ChainSyncPairedSession (k : ℕ) where
open import Relation.Binary.PropositionalEquality using (subst)
open import Data.List using (List; [])
open import Data.Product using (Σ-syntax; _,_)
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.ChainSyncSession as CS
open import Cardano_network.Replay.Paired CS.St CS.Kind CS.kindEq (CS.next k) public
open import Cardano_network.Replay.PairedDecide CS.St CS.Kind CS.kindEq (CS.next k) public
module Client = CS.Spec k client
module Server = CS.Spec k server

-- The pilot accepts only fresh local sessions and empty initial channels.
initial : State
initial = fresh CS.initial CS.initial

-- Every paired run projects to a legal local client run.
client-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Client._⇒⟨_⟩_ (clientState s) (project client es) (clientState t)
client-trace done = Client.done
client-trace (tau () _)
client-trace (vis (clientSend pr) run) = Client.vis pr (client-trace run)
client-trace (vis (clientRecv pr) run) = Client.vis pr (client-trace run)
client-trace (vis (serverSend pr) run) = client-trace run
client-trace (vis (serverRecv pr) run) = client-trace run

-- Every paired run also projects to a legal sequential server run.
server-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Server._⇒⟨_⟩_ (serverState s) (project server es) (serverState t)
server-trace done = Server.done
server-trace (tau () _)
server-trace (vis (clientSend pr) run) = server-trace run
server-trace (vis (clientRecv pr) run) = server-trace run
server-trace (vis (serverSend pr) run) = Server.vis pr (server-trace run)
server-trace (vis (serverRecv pr) run) = Server.vis pr (server-trace run)

-- Paired acceptance implies local client membership for the complete input.
compatible-client : ∀ {cs ss} → Compatible initial cs ss → Client.HasTrace CS.initial cs
compatible-client run with merge-run run
... | t , pr = clientState t , subst
  (λ es → Client._⇒⟨_⟩_ CS.initial es (clientState t)) (client-projection run) (client-trace pr)

-- Paired acceptance implies local server membership independently of the bound.
compatible-server : ∀ {cs ss} → Compatible initial cs ss → Server.HasTrace CS.initial ss
compatible-server run with merge-run run
... | t , pr = serverState t , subst
  (λ es → Server._⇒⟨_⟩_ CS.initial es (serverState t)) (server-projection run) (server-trace pr)
