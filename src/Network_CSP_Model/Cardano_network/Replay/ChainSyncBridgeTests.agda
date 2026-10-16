{-# OPTIONS --guardedness #-}

-- Inhabited original PTree runs and negative controls through both bridges.
module Cardano_network.Replay.ChainSyncBridgeTests where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (lo; hi)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Replay.ChainSyncSession
import Cardano_network.Replay.ChainSyncTests as T
import Cardano_network.ChainSyncPipe replayParams as P
import Cardano_network.Replay.ChainSyncClientBridge replayParams as C
import Cardano_network.Replay.ChainSyncServerBridge replayParams as S
open import Cardano_network.ChainSync replayParams using (CSEv)
open import Process_Trees using (ExtI)
open import Semantics.Deadlock {E = CSEv} {I = ExtI CSEv} using (_⟹∖√⟨_⟩_)

-- Overlapping requests exercise AwaitReply, both roll replies, and intersection.
client-run : ∃[ t ] ∃[ M ] (P.client 2 zero lo ⟹∖√⟨ t ⟩ M × C.Obs t T.rounds)
client-run = C.complete 2 zero lo tt T.rounds-run

-- The constructive witness satisfies soundness in the opposite direction.
client-roundtrip : Spec.HasTrace 2 client initial T.rounds
client-roundtrip with client-run
... | t , M , run , obs = C.sound 2 zero lo run obs

-- Server witnesses use the other endpoint direction and ignore client capacity.
server-run : ∃[ t ] ∃[ M ] (P.server zero hi ⟹∖√⟨ t ⟩ M × S.Obs t T.server-rounds)
server-run = S.complete 0 zero hi tt T.server-run

-- The existing sequential server is covered, not a copied replay tree.
server-roundtrip : Spec.HasTrace 0 server initial T.server-rounds
server-roundtrip with server-run
... | t , M , run , obs = S.sound 0 zero hi run obs

-- Zero capacity still admits intersection, its negative result, and Done.
zero-events : List E
zero-events = (Send , findIntersect) ∷ (Recv , intersectNotFound) ∷ (Send , doneK) ∷ []

-- A concrete zero-capacity original client trace is inhabited.
zero-run : ∃[ t ] ∃[ M ] (P.client 0 zero hi ⟹∖√⟨ t ⟩ M × C.Obs t zero-events)
zero-run = C.complete 0 zero hi tt (toWitness {a? = Spec.check 0 client zero-events} tt)

-- EOF can leave the pipeline full without asserting eventual replies.
open-events : List E
open-events = (Send , requestNext) ∷ (Send , requestNext) ∷ (Send , requestNext) ∷ []

-- Completeness includes finite prefixes with several pending operations.
open-run : ∃[ t ] ∃[ M ] (P.client 3 zero lo ⟹∖√⟨ t ⟩ M × C.Obs t open-events)
open-run = C.complete 3 zero lo tt (toWitness {a? = Spec.check 3 client open-events} tt)

-- Rejection plus soundness excludes the same projected trace in the PTree.
shallow-impossible : ¬ (∃[ t ] ∃[ M ] (P.client 1 zero lo ⟹∖√⟨ t ⟩ M × C.Obs t T.rounds))
shallow-impossible (t , M , run , obs) =
  toWitnessFalse {a? = Spec.check 1 client T.rounds} tt (C.sound 1 zero lo run obs)
