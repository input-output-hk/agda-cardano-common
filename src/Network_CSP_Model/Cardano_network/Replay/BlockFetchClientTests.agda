{-# OPTIONS --guardedness #-}

-- Certified positive/negative traces and an inhabited original PTree witness.
module Cardano_network.Replay.BlockFetchClientTests where

open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Data.Fin using (zero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Replay.BlockFetchClientSession
open import Cardano_network.Replay.BlockFetchReport using (report)
open import Cardano_network.Base using (lo)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.BlockFetch replayParams using (BFEv)
import Cardano_network.BlockFetchPipe replayParams as P
import Cardano_network.Replay.BlockFetchClientBridge replayParams as B
open import Semantics.Deadlock {E = BFEv} {I = ExtI BFEv} using (_⟹∖√⟨_⟩_)

-- Overlap ranges during a batch, refill, drain and close.
rounds : List E
rounds = (Send , request) ∷ (Recv , startBatch) ∷ (Send , request) ∷
  (Recv , block) ∷ (Recv , batchDone) ∷ (Send , request) ∷
  (Recv , noBlocks) ∷ (Recv , startBatch) ∷ (Recv , batchDone) ∷
  (Send , clientDone) ∷ []

-- A decision certificate contains an actual run of the control specification.
rounds-run : Spec.HasTrace 2 initial rounds
rounds-run = toWitness {a? = Spec.check 2 rounds} tt

-- The very same trace cannot run with only one credit.
rounds-too-deep : ¬ Spec.HasTrace 1 initial rounds
rounds-too-deep = toWitnessFalse {a? = Spec.check 1 rounds} tt

-- Completeness produces a run of the pre-existing pipelined PTree, not a copy.
ptree-run : ∃[ t ] ∃[ M ] (P.client 2 zero lo ⟹∖√⟨ t ⟩ M × B.Obs t rounds)
ptree-run = B.complete 2 zero lo tt rounds-run

-- Soundness maps that inhabited witness back to a certified control trace.
roundtrip : Spec.HasTrace 2 initial rounds
roundtrip with ptree-run
... | t , M , run , obs = B.sound 2 zero lo run obs

-- EOF accepts a prefix with two outstanding responses.
full-prefix : True (Spec.check 2 ((Send , request) ∷ (Send , request) ∷ []))
full-prefix = tt

-- A third request exceeds the bound.
overflow : False (Spec.check 2 ((Send , request) ∷ (Send , request) ∷ (Send , request) ∷ []))
overflow = tt

-- NoBlocks is only allowed before StartBatch.
wrong-phase : False (Spec.check 2 ((Send , request) ∷ (Recv , startBatch) ∷ (Recv , noBlocks) ∷ []))
wrong-phase = tt

-- A batch cannot start without a request.
unsolicited : False (Spec.check 2 ((Recv , startBatch) ∷ []))
unsolicited = tt

-- Block data cannot arrive before StartBatch.
early-block : False (Spec.check 2 ((Send , request) ∷ (Recv , block) ∷ []))
early-block = tt

-- Done is illegal while a response is outstanding.
early-done : False (Spec.check 2 ((Send , request) ∷ (Send , clientDone) ∷ []))
early-done = tt

-- The client cannot receive its own request kind.
wrong-agency : False (Spec.check 2 ((Recv , request) ∷ []))
wrong-agency = tt

-- Closure is final.
closed-request : False (Spec.check 2 ((Send , clientDone) ∷ (Send , request) ∷ []))
closed-request = tt

-- Zero permits closure but no requests.
zero-close : True (Spec.check 0 ((Send , clientDone) ∷ []))
zero-close = tt

-- Zero is a bound, not a special unlimited mode.
zero-request : False (Spec.check 0 ((Send , request) ∷ []))
zero-request = tt

-- Normalized CLI diagnostics identify the first rejected event and prior state.
diagnostic : report 1 "role client\nSend RequestRange\nSend RequestRange\n" ≡
  "rejected at index 2: Send RequestRange\nmodel state after 1 events: outstanding 1, waiting for batch"
diagnostic = refl

-- Never silently reinterpret a server trace as a pipelined client trace.
server-header : report 2 "role server\n" ≡ "parse error at line 1: role server"
server-header = refl

-- Kind-only input cannot imply that extra payload fields were validated.
extra-fields : report 2 "role client\nSend RequestRange aa bb\n" ≡
  "parse error at line 2: Send RequestRange aa bb"
extra-fields = refl

-- Original protocol namespaces can identify rows without changing the grammar.
namespace-round : report 1 "role client\nBlockFetch.Remote.Send.RequestRange\nBlockFetch.Remote.Receive.NoBlocks\nBlockFetch.Remote.Send.ClientDone\n" ≡
  "accepted (3 events; BlockFetch client control only)"
namespace-round = refl

-- A similarly named message from another protocol is not a BlockFetch event.
wrong-namespace : report 1 "role client\nLeiosFetch.Remote.Receive.Block\n" ≡
  "parse error at line 2: LeiosFetch.Remote.Receive.Block"
wrong-namespace = refl
