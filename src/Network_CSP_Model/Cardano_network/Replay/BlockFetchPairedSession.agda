{-# OPTIONS --safe #-}

-- Bounded BlockFetch client and sequential server joined by two control FIFOs.
open import Data.Nat using (ℕ)
module Cardano_network.Replay.BlockFetchPairedSession (k : ℕ) where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (subst)
open import Cardano_network.Replay.Common using (client; server)
import Cardano_network.Replay.BlockFetchClientSession as C
import Cardano_network.Replay.BlockFetchServerSession as S
open import Cardano_network.Replay.BlockFetchPairedLocal k public
open import Cardano_network.Replay.Paired St C.Kind C.kindEq next public
open import Cardano_network.Replay.PairedDecide St C.Kind C.kindEq next public
module Client = C.Spec k
module Server = S

-- Both local machines and both directional channels start empty.
initial : State
initial = fresh (clientS C.initial) (serverS S.idle)

-- Projecting a paired run gives a genuine run of the existing client model.
client-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Client._⇒⟨_⟩_ (clientView (clientState s)) (project client es) (clientView (clientState t))
client-trace done = Client.done
client-trace (tau () _)
client-trace (vis (clientSend {c = c} pr) run) = Client.vis (client-sound {s = c} pr) (client-trace run)
client-trace (vis (clientRecv {c = c} pr) run) = Client.vis (client-sound {s = c} pr) (client-trace run)
client-trace (vis (serverSend pr) run) = client-trace run
client-trace (vis (serverRecv pr) run) = client-trace run

-- Server projection preserves sequential batch processing exactly.
server-trace : ∀ {s es t} → s ⇒⟨ es ⟩ t →
  Server._⇒⟨_⟩_ (serverView (serverState s)) (project server es) (serverView (serverState t))
server-trace done = Server.done
server-trace (tau () _)
server-trace (vis (clientSend pr) run) = server-trace run
server-trace (vis (clientRecv pr) run) = server-trace run
server-trace (vis (serverSend {s = s} pr) run) = Server.vis (server-sound {s = s} pr) (server-trace run)
server-trace (vis (serverRecv {s = s} pr) run) = Server.vis (server-sound {s = s} pr) (server-trace run)

-- Acceptance entails legality of every row in the complete client input.
compatible-client : ∀ {cs ss} → Compatible initial cs ss → Client.HasTrace C.initial cs
compatible-client run with merge-run run
... | t , pr = clientView (clientState t) , subst
  (λ es → Client._⇒⟨_⟩_ C.initial es (clientView (clientState t)))
  (client-projection run) (client-trace pr)

-- Acceptance also entails legality of every row in the complete server input.
compatible-server : ∀ {cs ss} → Compatible initial cs ss → Server.HasTrace S.idle ss
compatible-server run with merge-run run
... | t , pr = serverView (serverState t) , subst
  (λ es → Server._⇒⟨_⟩_ S.idle es (serverView (serverState t)))
  (server-projection run) (server-trace pr)
