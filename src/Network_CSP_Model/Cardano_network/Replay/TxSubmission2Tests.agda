{-# OPTIONS --safe #-}

-- Positive first-order runs and negative controls for both TxSubmission2 roles.
module Cardano_network.Replay.TxSubmission2Tests where

open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.TxSubmission2Session
open import Cardano_network.Replay.SessionReport using (reportTxSubmission2; reportWithProtocolDepths)

-- Different asynchronous request families coexist before synchronous shutdown.
rounds : List E
rounds = (Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷
  (Recv , replyIdsEmpty) ∷ (Recv , replyTxs) ∷ (Send , requestBlocking) ∷ (Recv , doneK) ∷ []

-- Acceptance constructs an inhabited run of the requester specification.
server-run : Spec.HasTrace 2 server initial rounds
server-run = toWitness {a? = Spec.check 2 server rounds} tt

-- Capacity counts messages, including both response families.
too-shallow : False (Spec.check 1 server rounds)
too-shallow = tt

-- A sequential submitter cannot receive two requests before replying.
client-sequential : False (Spec.check 100 client (map reverse rounds))
client-sequential = tt

-- Sequential submitter exchanges, independent of the requester bound.
client-rounds : List E
client-rounds = (Send , init) ∷ (Recv , requestBlocking) ∷ (Send , replyIdsNonEmpty) ∷
  (Recv , requestNonBlocking) ∷ (Send , replyIdsEmpty) ∷
  (Recv , requestTxs) ∷ (Send , replyTxs) ∷
  (Recv , requestBlocking) ∷ (Send , doneK) ∷ []

-- Zero requester capacity does not disable the independent submitter.
client-run : Spec.HasTrace 0 client initial client-rounds
client-run = toWitness {a? = Spec.check 0 client client-rounds} tt

-- Requester must receive Init first.
missing-init : False (Spec.check 2 server ((Send , requestBlocking) ∷ []))
missing-init = tt

-- Repeated Init cannot reset an active generation.
repeated-init : False (Spec.check 2 server ((Recv , init) ∷ (Recv , init) ∷ []))
repeated-init = tt

-- Reply family must match the FIFO head, not any outstanding request.
fifo : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Send , requestTxs) ∷ (Recv , replyTxs) ∷ []))
fifo = tt

-- Blocking calls require a drained pipeline.
blocking-drain : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestTxs) ∷ (Send , requestBlocking) ∷ []))
blocking-drain = tt

-- No asynchronous request overlaps a synchronous blocking call.
blocking-exclusive : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestBlocking) ∷ (Send , requestTxs) ∷ []))
blocking-exclusive = tt

-- Empty ID replies are forbidden specifically in the blocking state.
empty-blocking : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestBlocking) ∷ (Recv , replyIdsEmpty) ∷ []))
empty-blocking = tt

-- Done is not legal for a nonblocking request.
nonblocking-done : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestNonBlocking) ∷ (Recv , doneK) ∷ []))
nonblocking-done = tt

-- The requester cannot terminate by sending Done itself.
wrong-agency : False (Spec.check 2 server ((Recv , init) ∷ (Send , requestBlocking) ∷ (Send , doneK) ∷ []))
wrong-agency = tt

-- EOF after a blocking request is a valid unfinished prefix.
blocking-prefix : Spec.HasTrace 0 server initial ((Recv , init) ∷ (Send , requestBlocking) ∷ [])
blocking-prefix = toWitness {a? = Spec.check 0 server ((Recv , init) ∷ (Send , requestBlocking) ∷ [])} tt

-- Namespace rows preserve the prototype's exceptional MsgInit spelling.
parsed : reportTxSubmission2 0 "role client\nTxSubmission.Remote.Send.MsgInit\nTxSubmission.Remote.Receive.RequestTxIds Blocking\nTxSubmission.Remote.Send.Done\n" ≡ "accepted (3 events, 1 sessions)"
parsed = refl

-- Missing blocking evidence is rejected, not interpreted nondeterministically.
missing-blocking : reportTxSubmission2 4 "role client\nSend Init\nRecv RequestTxIds\n" ≡ "parse error at line 3: Recv RequestTxIds"
missing-blocking = refl

-- Replies cannot consume a request from another session.
isolation : reportWithProtocolDepths 1 1 1 1 2 "sessions txsubmission2:server txsubmission2:server\n0 Recv Init\n1 Recv Init\n0 Send RequestTxs\n1 Recv ReplyTxs\n" ≡
  "rejected at index 4 (session 1): Recv ReplyTxs\nmodel session state after 3 events: txsubmission2 server pending []"
isolation = refl

-- Mixed dispatch applies only the fifth bound to TxSubmission2 requesters.
mixed : reportWithProtocolDepths 0 0 0 0 2 "sessions fetch:client notify:client blockfetch:client chainsync:client txsubmission2:server\n4 Recv Init\n4 Send RequestTxIds NonBlocking\n4 Send RequestTxs\n4 Recv ReplyTxIds NonEmpty\n4 Recv ReplyTxs\n" ≡ "accepted (5 events, 5 sessions)"
mixed = refl
