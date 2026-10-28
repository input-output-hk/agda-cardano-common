{-# OPTIONS --guardedness #-}

-- Inhabited composed PTree witnesses and FIFO negative controls for the same model.
module Cardano_network.Replay.ChainSyncPairedBridgeTests where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi; FromInitiator)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams
open import Cardano_network.Params using (Params)
open Params replayParams using (time₀; length₀)
open import Cardano_network.ChainSync replayParams using (CSEv; sendCS; receiveCS)
import Cardano_network.Replay.ChainSyncPairedSession as R
import Cardano_network.Replay.ChainSyncPairedTests as T
import Cardano_network.Replay.ChainSyncPairedBridge replayParams as B
import Cardano_network.Replay.ChainSyncPairedModel replayParams as Model
import Cardano_network.Replay.ChainSyncPairedPackets replayParams as Packets
open import Process_Trees using (ExtI)
import Semantics.LTS {E = CSEv} {I = ExtI CSEv} as Local
open import Cardano_network.Replay.ChainSyncSession

-- The checker witness now gives one composed execution of both original peers.
paired-system : B.Inputs 2 zero zero lo hi tt T.clientRows T.serverRows
paired-system = B.inputs-complete 2 zero zero lo hi tt (R.fromWitness 2 T.paired-run)

-- Soundness of the actual composed witness reconstructs a checker certificate.
roundtrip : R.Compatible 2 (R.initial 2) T.clientRows T.serverRows
roundtrip = B.inputs-sound 2 zero zero lo hi tt paired-system

-- An accepted unfinished send queue is inhabited in the actual PTree product.
inflight-system : B.Inputs 2 zero zero hi lo tt
  ((Send , requestNext) ∷ (Send , requestNext) ∷ []) []
inflight-system = B.inputs-complete 2 zero zero hi lo tt (R.fromWitness 2 T.inflight)

-- Zero pipeline credit still permits a synchronous intersection and wire Done.
zero-system : B.Inputs 0 zero zero lo hi tt
  ((Send , findIntersect) ∷ (Recv , intersectNotFound) ∷ (Send , doneK) ∷ [])
  ((Recv , findIntersect) ∷ (Send , intersectNotFound) ∷ (Recv , doneK) ∷ [])
zero-system = B.inputs-complete 0 zero zero lo hi tt (R.fromWitness 0 T.zero-pair)

-- Two locally legal but incompatible captures have no composed PTree witness.
mismatch-impossible : ¬ B.Inputs 2 zero zero lo hi tt T.mismatchedClient T.mismatchedServer
mismatch-impossible input = T.pair-mismatch
  (R.toWitness 2 (B.inputs-sound 2 zero zero lo hi tt input))

-- Reply-family agreement alone does not permit FIFO reordering.
fifo-impossible : ¬ B.Inputs 2 zero zero lo hi tt
  ((Send , requestNext) ∷ (Send , requestNext) ∷ (Recv , rollForward) ∷ (Recv , rollBackward) ∷ [])
  ((Recv , requestNext) ∷ (Send , rollBackward) ∷ (Recv , requestNext) ∷ (Send , rollForward) ∷ [])
fifo-impossible input = T.fifo-order (B.inputs-sound 2 zero zero lo hi tt input)

-- Distinct concrete payloads can have the same observed control kind.
empty-points : Payload
empty-points = time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect [])

-- The receive below changes the transmitted intersection list.
other-points : Payload
other-points = time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect (point tt ∷ []))

-- This information is intentionally erased by control-only replay.
same-control : Packets.payloadKind empty-points ≡ Packets.payloadKind other-points
same-control = refl

-- The concrete medium enqueues the full payload rather than just its kind.
full-enqueue : Model.clientGate (Local.evLabel _ (sendCS zero lo) empty-points) Model.empty ≡
  just (Model.queues (empty-points ∷ []) [])
full-enqueue = refl

-- Receiving the wrong payload is disabled even when its control kind matches.
wrong-payload : Model.serverGate (Local.evLabel _ (receiveCS zero hi) other-points)
  (Model.queues (empty-points ∷ []) []) ≡ nothing
wrong-payload = refl
