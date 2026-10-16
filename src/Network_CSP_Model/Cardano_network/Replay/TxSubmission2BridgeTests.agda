{-# OPTIONS --guardedness #-}

-- Concrete original-peer witnesses, including pipelining and blocking replies.
module Cardano_network.Replay.TxSubmission2BridgeTests where

open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (lo; hi)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Replay.TxSubmission2Session
import Cardano_network.Replay.TxSubmission2Tests as T
import Cardano_network.TxSubmission2Pipe replayParams as P
import Cardano_network.Replay.TxSubmission2ClientBridge replayParams as C
import Cardano_network.Replay.TxSubmission2ServerBridge replayParams as S
open import Cardano_network.TxSubmission replayParams using (TSEv)
open import Process_Trees using (ExtI)
open import Semantics.Deadlock {E = TSEv} {I = ExtI TSEv} using (_⟹∖√⟨_⟩_)

-- Two asynchronous request families coexist before blocking shutdown.
server-run : ∃[ t ] ∃[ M ] (P.server 2 zero lo ⟹∖√⟨ t ⟩ M × S.Obs t T.rounds)
server-run = S.complete 2 zero lo tt T.server-run

-- Soundness returns the constructed original-peer run to the replay model.
server-roundtrip : Spec.HasTrace 2 server initial T.rounds
server-roundtrip with server-run
... | t , M , run , obs = S.sound 2 zero lo run obs

-- The strict submitter is sequential even at requester capacity zero.
client-run : ∃[ t ] ∃[ M ] (P.client zero hi ⟹∖√⟨ t ⟩ M × C.Obs t T.client-rounds)
client-run = C.complete 0 zero hi tt T.client-run

-- Both bridge directions apply to an inhabited client execution.
client-roundtrip : Spec.HasTrace 0 client initial T.client-rounds
client-roundtrip with client-run
... | t , M , run , obs = C.sound 0 zero hi run obs

-- Refill behind an ID request, drain, unblock with IDs, and close.
refill-events : List E
refill-events = (Recv , init) ∷ (Send , requestTxs) ∷ (Send , requestNonBlocking) ∷
  (Recv , replyTxs) ∷ (Send , requestTxs) ∷ (Recv , replyIdsNonEmpty) ∷
  (Recv , replyTxs) ∷ (Send , requestBlocking) ∷ (Recv , replyIdsNonEmpty) ∷
  (Send , requestBlocking) ∷ (Recv , doneK) ∷ []

-- Completeness witnesses both FIFO tag orders and nonempty reply branches.
refill-run : ∃[ t ] ∃[ M ] (P.server 2 zero hi ⟹∖√⟨ t ⟩ M × S.Obs t refill-events)
refill-run = S.complete 2 zero hi tt (toWitness {a? = Spec.check 2 server refill-events} tt)

-- A synchronous request can remain unfinished even with no pipeline credit.
zero-prefix-run : ∃[ t ] ∃[ M ]
  (P.server 0 zero lo ⟹∖√⟨ t ⟩ M × S.Obs t ((Recv , init) ∷ (Send , requestBlocking) ∷ []))
zero-prefix-run = S.complete 0 zero lo tt T.blocking-prefix

-- A reply cannot skip the oldest queued response family.
wrong-fifo : List E
wrong-fifo = (Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷ (Recv , replyTxs) ∷ []

-- The checker negative control excludes a projected PTree execution too.
fifo-impossible : ¬ (∃[ t ] ∃[ M ] (P.server 2 zero lo ⟹∖√⟨ t ⟩ M × S.Obs t wrong-fifo))
fifo-impossible (t , M , run , obs) =
  toWitnessFalse {a? = Spec.check 2 server wrong-fifo} tt (S.sound 2 zero lo run obs)

-- Empty blocking replies remain forbidden by the targeted strict client.
empty-blocking-events : List E
empty-blocking-events = (Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsEmpty) ∷ []

-- Soundness transfers the strict blocking rule back to the actual PTree.
empty-blocking-impossible : ¬ (∃[ t ] ∃[ M ]
  (P.client zero hi ⟹∖√⟨ t ⟩ M × C.Obs t empty-blocking-events))
empty-blocking-impossible (t , M , run , obs) =
  toWitnessFalse {a? = Spec.check 0 client empty-blocking-events} tt (C.sound 0 zero hi run obs)
