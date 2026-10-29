{-# OPTIONS --guardedness #-}

-- Inhabited joint BlockFetch executions and exclusions for the same peer model.
module Cardano_network.Replay.BlockFetchPairedBridgeTests where

open import Data.Fin using (zero)
open import Data.Bool using (Bool; false; true)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams
open import Cardano_network.Params using (Params)
import Class.DecEq.Instances as DecEqI
open Params replayParams using (time₀; length₀)
open import Cardano_network.BlockFetch replayParams using (BFEv; sendBF; receiveBF)
open import Cardano_network.Replay.BlockFetchClientSession
import Cardano_network.Replay.BlockFetchPairedSession as R
import Cardano_network.Replay.BlockFetchPairedTests as T
import Cardano_network.Replay.BlockFetchPairedBridge replayParams as B
import Cardano_network.Replay.BlockFetchPairedModel replayParams as Model
import Cardano_network.Replay.BlockFetchPairedPackets replayParams as Packets
open import Process_Trees using (ExtI)
import Semantics.LTS {E = BFEv} {I = ExtI BFEv} as Local

-- Both original peers jointly realise the depth-two two-block batch witness.
paired-system : B.Inputs 2 zero zero lo hi tt T.clientRows T.serverRows
paired-system = B.checker-sound 2 zero zero lo hi tt T.paired-run

-- This reverse endpoint takes no block or transaction-ID witness argument.
unconditional-certificate : R.Witness 2 (R.initial 2) T.clientRows T.serverRows
unconditional-certificate with paired-system
... | t , tree , es , run , obs , co , so = B.model-certificate 2 zero zero lo hi run obs co so

-- The joint witness returns to a certificate for the exact endpoint inputs.
roundtrip : R.Witness 2 (R.initial 2) T.clientRows T.serverRows
roundtrip = B.checker-complete 2 zero zero lo hi tt paired-system

-- Transmitted requests may remain unconsumed in the actual composed model.
inflight-system : B.Inputs 2 zero zero hi lo tt
  ((Send , request) ∷ (Send , request) ∷ []) []
inflight-system = B.checker-sound 2 zero zero hi lo tt T.inflight

-- Zero pipeline capacity still permits idle ClientDone at both peers.
zero-system : B.Inputs 0 zero zero lo hi tt ((Send , clientDone) ∷ []) ((Recv , clientDone) ∷ [])
zero-system = B.checker-sound 0 zero zero lo hi tt T.zero-close

-- Conflicting locally legal batch outcomes cannot arise in a joint execution.
mismatch-impossible : ¬ B.Inputs 2 zero zero lo hi tt
  ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , noBlocks) ∷ [])
mismatch-impossible input = T.pair-mismatch (B.inputs-sound 2 zero zero lo hi tt input)

-- A merged PTree execution cannot undo the client's own capacity violation.
shallow-impossible : ¬ B.Inputs 1 zero zero lo hi tt T.clientRows T.serverRows
shallow-impossible input = T.too-shallow (B.inputs-sound 1 zero zero lo hi tt input)

-- Different batch outcomes cannot be reordered across the concrete FIFO.
fifo-impossible : ¬ B.Inputs 2 zero zero lo hi tt
  ((Send , request) ∷ (Send , request) ∷ (Recv , noBlocks) ∷
   (Recv , startBatch) ∷ (Recv , batchDone) ∷ [])
  ((Recv , request) ∷ (Send , startBatch) ∷ (Send , batchDone) ∷
   (Recv , request) ∷ (Send , noBlocks) ∷ [])
fifo-impossible input = T.fifo-order (B.inputs-sound 2 zero zero lo hi tt input)

-- Fresh queues cannot supply an uncaptured request to the actual server.
missing-send-impossible : ¬ B.Inputs 2 zero zero lo hi tt [] ((Recv , request) ∷ [])
missing-send-impossible input = T.missing-send (B.inputs-sound 2 zero zero lo hi tt input)

-- A concrete request includes the sender's transport mode.
request-payload : Payload
request-payload = time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange (chainRange (point tt) (point tt)))

-- This deliberately changes an envelope field erased by the replay observation.
other-payload : Payload
other-payload = time₀ , FromResponder , length₀ , blockFetch (MsgRequestRange (chainRange (point tt) (point tt)))

-- Control observation alone cannot distinguish those packets.
same-control : Packets.payloadKind request-payload ≡ Packets.payloadKind other-payload
same-control = refl

-- The concrete composition retains the entire packet sent by the client.
full-enqueue : Model.clientGate (Local.evLabel _ (sendBF zero lo) request-payload) Model.empty ≡
  just (Model.queues (request-payload ∷ []) [])
full-enqueue = refl

-- Equal control kinds do not permit substitution of a different concrete packet.
wrong-payload : Model.serverGate (Local.evLabel _ (receiveBF zero hi) other-payload)
  (Model.queues (request-payload ∷ []) []) ≡ nothing
wrong-payload = refl

-- A second parameter instance gives the erased block carrier distinct values.
twoBlocks : Params
twoBlocks = record replayParams
  { Block = Bool ; rbHash = λ _ → tt ; slotOf = λ _ → 0
  ; announcedEB = λ _ → nothing ; decBlock = DecEqI.DecEq-Bool }

module DistinctBlocks where
  import Cardano_network.Data twoBlocks as D
  import Cardano_network.BlockFetch twoBlocks as BF
  import Cardano_network.Replay.BlockFetchPairedModel twoBlocks as M
  import Cardano_network.Replay.BlockFetchPairedPackets twoBlocks as P
  import Cardano_network.Replay.BlockFetchPairedBridge twoBlocks as Bridge
  import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as L

  -- The same accepted control logs are realised with a non-unit Block carrier.
  inhabited : Bridge.Inputs 2 zero zero lo hi false T.clientRows T.serverRows
  inhabited = Bridge.checker-sound 2 zero zero lo hi false T.paired-run

  -- Both requests have legal initiator envelopes but different range contents.
  first : D.Payload
  first = tt , FromInitiator , tt , D.blockFetch (D.MsgRequestRange (D.chainRange (D.point false) (D.point false)))

  -- This changes only the requested endpoint, which control replay erases.
  second : D.Payload
  second = tt , FromInitiator , tt , D.blockFetch (D.MsgRequestRange (D.chainRange (D.point false) (D.point true)))

  -- Control equality cannot distinguish the range payloads.
  same-kind : P.payloadKind first ≡ P.payloadKind second
  same-kind = refl

  -- The full-payload FIFO still refuses their substitution at the receive gate.
  wrong-range : M.serverGate (L.evLabel _ (BF.receiveBF zero hi) second)
    (M.queues (first ∷ []) []) ≡ nothing
  wrong-range = refl
