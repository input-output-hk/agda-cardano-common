{-# OPTIONS --guardedness #-}

-- At depth one, the new peers preserve the old peers' observed wire-control language.
-- This is finite kind/direction trace equivalence, not a payload-level bisimulation.
module Cardano_network.Replay.LeiosNotifyPipeDepthOne where
open import Data.Fin using (zero)
open import Data.List using (List)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Function.Bundles using (_⇔_; mk⇔; module Equivalence)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (header)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; stIdle)
open import Cardano_network.LeiosNotifyPipe replayParams using (Peer; consumer; producer; client; server)
import Cardano_network.Replay.LeiosNotifyPipeBridge replayParams 1 zero hi as New
import Cardano_network.Replay.LeiosNotifyBridge as Old
import Cardano_network.Replay.LeiosNotifyPipeline as N
open import Process_Trees using (ExtI)
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} using (_⟹∖√⟨_⟩_)

-- The concrete replay domains supply all stated native completeness witnesses.
witnesses : New.Payloads
witnesses = New.payloads (header tt) (0 , 0) tt

-- The old process selects the original depth-one peer for each agency.
oldPeer : Peer → Old.Proc
oldPeer r = Old.It (New.role r) (Old.step (New.role r) stIdle)

-- The new process selects the explicit bounded extension at capacity one.
newPeer : Peer → Old.Proc
newPeer consumer = client 1 zero hi
newPeer producer = server 1 zero hi

-- A concrete witness on the new peer transports to a concrete witness on the old peer.
new-to-old : ∀ r {es} →
  (∃[ t ] ∃[ T ] (newPeer r ⟹∖√⟨ t ⟩ T × New.Obs t es)) →
  (∃[ t ] ∃[ T ] (oldPeer r ⟹∖√⟨ t ⟩ T × Old.Obs t es))
new-to-old consumer {es} (t , T , run , obs) = Old.complete N.client
  (Equivalence.from (N.depth-one-traces N.client es) (New.sound consumer run obs))
new-to-old producer {es} (t , T , run , obs) = Old.complete N.server
  (Equivalence.from (N.depth-one-traces N.server es) (New.sound producer run obs))

-- Conversely every original observed control trace occurs on the new depth-one peer.
old-to-new : ∀ r {es} →
  (∃[ t ] ∃[ T ] (oldPeer r ⟹∖√⟨ t ⟩ T × Old.Obs t es)) →
  (∃[ t ] ∃[ T ] (newPeer r ⟹∖√⟨ t ⟩ T × New.Obs t es))
old-to-new consumer {es} (t , T , run , obs) = New.complete witnesses consumer
  (Equivalence.to (N.depth-one-traces N.client es) (Old.sound N.client run obs))
old-to-new producer {es} (t , T , run , obs) = New.complete witnesses producer
  (Equivalence.to (N.depth-one-traces N.server es) (Old.sound N.server run obs))

-- Both depth-one native peers have exactly the original finite wire-control traces.
depth-one : ∀ r {es} →
  (∃[ t ] ∃[ T ] (newPeer r ⟹∖√⟨ t ⟩ T × New.Obs t es)) ⇔
  (∃[ t ] ∃[ T ] (oldPeer r ⟹∖√⟨ t ⟩ T × Old.Obs t es))
depth-one r = mk⇔ (new-to-old r) (old-to-new r)
