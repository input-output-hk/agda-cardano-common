{-# OPTIONS --guardedness #-}

-- Inhabited bounded native executions, depth-one transport and paired FIFO witnesses.
module Cardano_network.Replay.LeiosNotifyPipeBridgeTests where
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (hi; FromInitiator)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (header; Payload; leiosNotifyP; MsgLNPRequestNext)
open import Cardano_network.Net replayParams using (lnpSendRequestNext; lnpSendDone; lnpRecvBlockOffer)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; apiLPev; sendLNP; receiveLNP)
import Cardano_network.LeiosNotifyPipe replayParams as Pipe
import Cardano_network.Replay.LeiosNotifyPipeBridge replayParams as B
import Cardano_network.Replay.LeiosNotifyPipeDepthOne as One
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyTests as OldTests
import Cardano_network.Replay.LeiosNotifyBridge as Old
import Cardano_network.Replay.LeiosNotifyPairedModel replayParams as M
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Native
import Semantics.LTS {E = M.PairEv} {I = M.PairI} as Pair
import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} as NT
open import Semantics.Deadlock {E = M.PairEv} {I = M.PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; ∖√-τ)

-- Opaque-domain completeness premises are inhabited in the concrete replay parameters.
witnesses : ∀ depth → B.Payloads depth zero hi
witnesses depth = B.payloads (header tt) (0 , 0) tt

-- Fill two credits, consume and refill, then drain and close with different kinds.
pipelined : List N.E
pipelined = (N.Send , Log.RequestNext) ∷ (N.Send , Log.RequestNext) ∷
  (N.Recv , Log.Votes []) ∷ (N.Send , Log.RequestNext) ∷
  (N.Recv , Log.BlockOffer 8 3 20) ∷ (N.Recv , Log.BlockTxsOffer 9 4) ∷
  (N.Send , Log.Done) ∷ []

-- Every log field may vary independently at this intentionally kind-only boundary.
client-spec : N.Spec.HasTrace 2 N.client N.idle pipelined
client-spec = toWitness {a? = N.Spec.check 2 N.client pipelined} tt

-- General completeness produces an actual native bounded client execution.
client-native : ∃[ events ] ∃[ T ]
  (Pipe.client 2 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 2 zero hi events pipelined)
client-native = B.complete 2 zero hi (witnesses 2) Pipe.consumer client-spec

-- Soundness returns a valid certificate from the inhabited native execution.
client-roundtrip : N.Spec.HasTrace 2 N.client N.idle pipelined
client-roundtrip with client-native
... | events , T , run , obs = B.sound 2 zero hi Pipe.consumer run obs

-- Reverse directions while preserving the order of all notification data.
reverse : N.E → N.E
reverse (N.Send , m) = N.Recv , m
reverse (N.Recv , m) = N.Send , m

-- The new producer independently supports more than one pending request credit.
server-native : ∃[ events ] ∃[ T ]
  (Pipe.server 2 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 2 zero hi events (map reverse pipelined))
server-native = B.complete 2 zero hi (witnesses 2) Pipe.producer
  (toWitness {a? = N.Spec.check 2 N.server (map reverse pipelined)} tt)

-- All four notification carriers have inhabited native realizations.
all-notifications : ∃[ events ] ∃[ T ]
  (Pipe.client 2 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 2 zero hi events OldTests.rounds)
all-notifications = B.complete 2 zero hi (witnesses 2) Pipe.consumer
  (toWitness {a? = N.Spec.check 2 N.client OldTests.rounds} tt)

-- Zero capacity still admits the legal Done wire event at the native client.
zero-client : ∃[ events ] ∃[ T ]
  (Pipe.client 0 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 0 zero hi events ((N.Send , Log.Done) ∷ []))
zero-client = B.complete 0 zero hi (witnesses 0) Pipe.consumer
  (toWitness {a? = N.Spec.check 0 N.client ((N.Send , Log.Done) ∷ [])} tt)

-- The original depth-one trace witnesses transport to the new native extension.
depth-one-client : ∃[ events ] ∃[ T ]
  (Pipe.client 1 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 1 zero hi events OldTests.rounds)
depth-one-client = B.complete 1 zero hi (witnesses 1) Pipe.consumer
  (toWitness {a? = N.Spec.check 1 N.client OldTests.rounds} tt)

-- The checked depth-one equivalence recovers an actual original-peer execution.
original-client : ∃[ events ] ∃[ T ]
  (One.oldPeer Pipe.consumer NT.⟹∖√⟨ events ⟩ T ×
   Old.Obs events OldTests.rounds)
original-client = One.new-to-old Pipe.consumer {es = OldTests.rounds} depth-one-client

-- Three unanswered requests have no observed execution at client capacity two.
capacity-refuted : ¬ (∃[ events ] ∃[ T ]
  (Pipe.client 2 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 2 zero hi events
    ((N.Send , Log.RequestNext) ∷ (N.Send , Log.RequestNext) ∷ (N.Send , Log.RequestNext) ∷ [])))
capacity-refuted (events , T , run , obs) =
  toWitnessFalse {a? = N.Spec.check 2 N.client
    ((N.Send , Log.RequestNext) ∷ (N.Send , Log.RequestNext) ∷ (N.Send , Log.RequestNext) ∷ [])} tt
    (B.sound 2 zero hi Pipe.consumer run obs)

-- A pending wire output blocks another application request until the send occurs.
output-blocks-api : Pipe.Machine.next 2 zero hi Pipe.consumer
  (Pipe.sending FromInitiator MsgLNPRequestNext (Pipe.openN 1))
  (Native.evLabel _ (apiLPev zero hi lnpSendRequestNext) tt) ≡ nothing
output-blocks-api = refl

-- An outstanding credit prevents premature Done at the native menu.
busy-done : Pipe.Machine.next 2 zero hi Pipe.consumer (Pipe.head (Pipe.openN 1))
  (Native.evLabel _ (apiLPev zero hi lnpSendDone) tt) ≡ nothing
busy-done = refl

-- Native delivery cannot alter a received offer's point before passing it to the API.
delivery-exact : Pipe.Machine.next 2 zero hi Pipe.consumer
  (Pipe.delivering (Pipe.offer (1 , 3) tt) (Pipe.openN 0))
  (Native.evLabel _ (apiLPev zero hi lnpRecvBlockOffer) ((2 , 3) , tt)) ≡ nothing
delivery-exact = refl

-- The actual packet remains unchanged across the two-FIFO composition.
request : Payload
request = tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext

-- Both clients' sends precede both server receives, preserving each endpoint's order.
paired-events : List Pair.Event
paired-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lnpSendRequestNext)) tt ∷
  Pair.evLabel _ (M.atClient (sendLNP zero hi)) request ∷
  Pair.evLabel _ (M.atClient (apiLPev zero hi lnpSendRequestNext)) tt ∷
  Pair.evLabel _ (M.atClient (sendLNP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLNP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLNP zero hi)) request ∷ []

-- The new depth-two client and producer jointly realize pipelining through real FIFOs.
paired-pipeline : ∃[ end ] M.pipelined-system 2 zero zero hi hi ⟹∖√⟨ paired-events ⟩ end
paired-pipeline = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.clientI M.silence} {a = lift tt} refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.serverI M.silence} {a = lift tt} refl refl)
  (∖√-ev (Pair.sVis refl refl) ∖√-refl)))))))

-- Producer capacity is enforced at the actual receive menu as well.
server-full : Pipe.Machine.next 2 zero hi Pipe.producer (Pipe.head (Pipe.openN 2))
  (Native.evLabel _ (receiveLNP zero hi) request) ≡ nothing
server-full = refl

-- Zero credit blocks even the first native request at the producer.
server-zero : Pipe.Machine.next 0 zero hi Pipe.producer (Pipe.head (Pipe.openN 0))
  (Native.evLabel _ (receiveLNP zero hi) request) ≡ nothing
server-zero = refl

-- The producer also has an inhabited depth-one witness for every notification kind.
depth-one-server : ∃[ events ] ∃[ T ]
  (Pipe.server 1 zero hi NT.⟹∖√⟨ events ⟩ T × B.Obs 1 zero hi events (map reverse OldTests.rounds))
depth-one-server = B.complete 1 zero hi (witnesses 1) Pipe.producer
  (toWitness {a? = N.Spec.check 1 N.server (map reverse OldTests.rounds)} tt)

-- Depth-one compatibility covers the original producer, not just the consumer.
original-server : ∃[ events ] ∃[ T ]
  (One.oldPeer Pipe.producer NT.⟹∖√⟨ events ⟩ T × Old.Obs events (map reverse OldTests.rounds))
original-server = One.new-to-old Pipe.producer {es = map reverse OldTests.rounds} depth-one-server
