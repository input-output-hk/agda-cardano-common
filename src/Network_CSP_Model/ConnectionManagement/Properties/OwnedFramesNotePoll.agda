{-# OPTIONS --guardedness #-}

-- notePoll's diagnostic peer restoration and exact monitor-PC update.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesNotePoll
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (UniqueKeys)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesThreads as ThreadRows
import ConnectionManagement.Properties.OwnedFramesThreadUpdate as ThreadFacts
import ConnectionManagement.Properties.OwnedFramesMonitorLifecycle as Lifecycle
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module Rows = ThreadRows isIOManagerError
  module T = ThreadFacts isBearerClosed isIOManagerError
  module M = Lifecycle isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError

-- A computed post-poll PC stays observing whenever this handle has a followup.
poll-keep : ∀ k ref tid t → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just t →
  PS.peerRef t ≡ ref → PS.pc t ≡ PS.observing →
  T.KeepObserving k tid (record t { pc = PS.afterPoll (lookup ref (C.SubContext.monitors (C.subsystem k))) }) (C.monitorPool k)
poll-keep k ref tid t unique saved peer observing with lookup ref (C.SubContext.monitors (C.subsystem k)) in active
... | nothing = T.keep-detached k tid t (record t { pc = PS.normalFinishing }) (C.monitorPool k) unique saved
  (trans (cong (λ q → lookup q (C.SubContext.monitors (C.subsystem k))) peer) active)
... | just f = T.keep-stable k tid t (record t { pc = PS.observing }) (C.monitorPool k) unique saved (sym observing) refl

-- An observing before-thread remains the exact same looked-up row after the
-- governor poll. A missing followup permits exit; an active one stays observing.
note-poll : ∀ ref before after tid t → PS.byPeer ref (PS.monitors before) ≡ just (tid , t) →
  PS.pc t ≡ PS.observing → lookup tid (PS.monitors after) ≡ just t → D.Held after → D.Held (PS.notePoll ref before after)
note-poll ref before after tid t chosen observing saved held with PS.byPeer ref (PS.monitors before) in selected
... | nothing = case chosen of λ ()
... | just (uid , u) with just-injective chosen
...   | refl with lookup ref (J.peers (Sub.world (PS.machine before))) | lookup ref (J.peers (Sub.world (PS.machine after)))
...     | nothing | next-peer = held
...     | just old-peer | nothing = held
...     | just old-peer | just next-peer with Peer.monitorStarted next-peer
...       | true = held
...       | false = M.thread-write before-thread tid t next-thread (PS.monitorPool after) saved refl refl
  (λ uid apart → refl)
  (poll-keep (C.capture before-thread) ref tid t (X.Aux.monitorKeys (proj₂ (proj₂ before-held))) saved
    (Rows.byPeer-ref ref (PS.monitors before) tid t selected) observing) before-held
  where
  rows = put ref (record next-peer { monitorStarted = true; promotedAt = Peer.promotedAt old-peer }) (J.peers (Sub.world (PS.machine after)))
  before-thread = PS.setMachine (record (PS.machine after) { world = record (Sub.world (PS.machine after)) { peers = rows } }) after
  before-held = M.peer-rows-held after rows held
  next-thread = record t { pc = PS.afterPoll (lookup ref (Sub.monitors (PS.machine after))) }
