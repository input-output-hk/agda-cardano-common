{-# OPTIONS --guardedness #-}

-- Inhabited server PTree traces, certified refutations and parser diagnostics.
module Cardano_network.Replay.BlockFetchServerTests where

open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Data.Fin using (zero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Replay.BlockFetchServerSession
open import Cardano_network.Replay.BlockFetchServerReport using (report)
open import Cardano_network.Base using (lo)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.BlockFetch replayParams using (BFEv; BFserverStClient)
import Cardano_network.Replay.BlockFetchServerBridge replayParams as B
import Cardano_network.Replay.BlockFetchClientSession as C
open import Semantics.Deadlock {E = BFEv} {I = ExtI BFEv} using (_⟹∖√⟨_⟩_)

-- A streaming batch, NoBlocks, an empty batch, then wire closure.
rounds : List E
rounds = (Recv , request) ∷ (Send , startBatch) ∷ (Send , block) ∷
  (Send , block) ∷ (Send , batchDone) ∷ (Recv , request) ∷
  (Send , noBlocks) ∷ (Recv , request) ∷ (Send , startBatch) ∷
  (Send , batchDone) ∷ (Recv , clientDone) ∷ []

-- Acceptance constructs a specification run.
rounds-run : HasTrace idle rounds
rounds-run = toWitness {a? = check rounds} tt

-- The accepted trace is witnessed in the original sequential server PTree.
ptree-run : ∃[ t ] ∃[ M ] (BFserverStClient zero lo ⟹∖√⟨ t ⟩ M × B.Obs t rounds)
ptree-run = B.complete zero lo tt rounds-run

-- Soundness maps that inhabited execution back to the control language.
roundtrip : HasTrace idle rounds
roundtrip with ptree-run
... | t , M , run , obs = B.sound zero lo run obs

-- The server must respond before consuming the next range.
pipelined-receives : ¬ HasTrace idle ((Recv , request) ∷ (Recv , request) ∷ [])
pipelined-receives = toWitnessFalse {a? = check ((Recv , request) ∷ (Recv , request) ∷ [])} tt

-- The client can emit two requests; the server need not consume them together.
client-pipeline : True (C.Spec.check 2 ((Send , request) ∷ (Send , request) ∷ []))
client-pipeline = tt

-- Transport receipt is not silently promoted to a protocol receive during a batch.
request-during-batch : False (check ((Recv , request) ∷ (Send , startBatch) ∷ (Recv , request) ∷ []))
request-during-batch = tt

-- A server cannot begin a response without a request.
unsolicited : False (check ((Send , startBatch) ∷ []))
unsolicited = tt

-- Blocks require StartBatch first.
early-block : False (check ((Recv , request) ∷ (Send , block) ∷ []))
early-block = tt

-- BatchDone also requires StartBatch first.
early-end : False (check ((Recv , request) ∷ (Send , batchDone) ∷ []))
early-end = tt

-- Once streaming, NoBlocks is no longer available.
wrong-phase : False (check ((Recv , request) ∷ (Send , startBatch) ∷ (Send , noBlocks) ∷ []))
wrong-phase = tt

-- Starting the same batch twice is not permitted.
double-start : False (check ((Recv , request) ∷ (Send , startBatch) ∷ (Send , startBatch) ∷ []))
double-start = tt

-- The server cannot receive ClientDone while a response remains active.
early-done : False (check ((Recv , request) ∷ (Recv , clientDone) ∷ []))
early-done = tt

-- Control direction is relative to the server, not the client.
wrong-agency : False (check ((Send , request) ∷ []))
wrong-agency = tt

-- No event is legal after wire ClientDone.
closed-request : False (check ((Recv , clientDone) ∷ (Recv , request) ∷ []))
closed-request = tt

-- Idle EOF is a valid prefix.
empty-prefix : True (check [])
empty-prefix = tt

-- EOF may occur before the response decision.
busy-prefix : True (check ((Recv , request) ∷ []))
busy-prefix = tt

-- EOF may occur while streaming, without proving batch completion.
streaming-prefix : True (check ((Recv , request) ∷ (Send , startBatch) ∷ (Send , block) ∷ []))
streaming-prefix = tt

-- Diagnostic state is the server's state before the failing event.
diagnostic : report "role server\nRecv RequestRange\nRecv RequestRange\n" ≡
  "rejected at index 2: Recv RequestRange\nmodel state after 1 events: busy (must send StartBatch or NoBlocks)"
diagnostic = refl

-- Both directions retain exact original namespaces on input.
namespace-round : report "role server\nBlockFetch.Remote.Receive.RequestRange\nBlockFetch.Remote.Send.NoBlocks\nBlockFetch.Remote.Receive.ClientDone\n" ≡
  "accepted (3 events; BlockFetch server control only)"
namespace-round = refl

-- Client input is rejected rather than silently reinterpreted.
wrong-header : report "role client\n" ≡ "parse error at line 1: role client"
wrong-header = refl

-- Extra fields cannot imply unsupported payload validation.
extra-fields : report "role server\nSend Block ab\n" ≡ "parse error at line 2: Send Block ab"
extra-fields = refl

-- Cross-protocol namespaces are rejected even when message names overlap.
wrong-namespace : report "role server\nLeiosFetch.Remote.Send.Block\n" ≡
  "parse error at line 2: LeiosFetch.Remote.Send.Block"
wrong-namespace = refl
