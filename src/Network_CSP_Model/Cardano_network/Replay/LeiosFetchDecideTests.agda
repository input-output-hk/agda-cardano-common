{-# OPTIONS --safe #-}

-- Computation tests for the positional reply, decoder caps, and silent
-- draining/throw branches, pinned to upstream e6511527 (stage 1).
module Cardano_network.Replay.LeiosFetchDecideTests where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_; applyUpTo)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (does; toWitnessFalse)
open import Data.Unit using (tt)
open import Semantics.Replay using (module Traces)

open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.LeiosFetchWire using (Bitmap)
open import Cardano_network.Replay.LeiosFetchDecide

open Spec 150 using (whyRejected; after; taus; leiosFetch)
open Traces leiosFetch using (HasTrace)
open Cert 150 using (hasTrace?; client-cert; server-cert; rejectionReason)

-- Two requested offsets, represented by the low two bits of word zero.
bm : Bitmap
bm = (0 , 3) ∷ []

-- A valid 17143-offset request exceeds the client decoder count limit.
replyCapBitmap : Bitmap
replyCapBitmap = applyUpTo (λ i → i , 18446744073709551615) 267 ++
  ((267 , 36028797018963967) ∷ [])

-- Server encoding permits both an over-cap count and an over-cap byte size.
server-over-cap-reply-accepted : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockTxsRequest 1 10 17143 replyCapBitmap)
   ∷ (Send , MsgLeiosBlockTxs 17143 550001) ∷ [])) ≡ true
server-over-cap-reply-accepted = refl

-- Server encoding permits a Block larger than the receive-side byte cap.
server-oversized-block-accepted : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockRequest 1 10) ∷ (Send , MsgLeiosBlock 1 700000) ∷ [])) ≡ true
server-oversized-block-accepted = refl

-- Client receives still reject an oversized Block, including while draining.
client-oversized-block-rejected : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockRequest 1 10) ∷ (Recv , MsgLeiosBlock 1 700000) ∷ [])) ≡ false
client-oversized-block-rejected = refl

-- The oversized client Block is diagnosed at the wire layer.
client-oversized-block-reason : whyRejected (cOpen (blockReq 1 10 ∷ []))
  (Recv , MsgLeiosBlock 1 700000) ≡ "wire: block byte cap exceeded"
client-oversized-block-reason = refl

-- Client receives still reject the over-cap reply even on the drain path.
client-over-cap-reply-rejected : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
   ∷ (Recv , MsgLeiosBlockTxs 17143 550001) ∷ [])) ≡ false
client-over-cap-reply-rejected = refl

-- The client count cap is diagnosed before the reply byte cap.
client-over-cap-reply-reason : whyRejected (cOpen (blockTxsReq 1 10 2 ∷ []))
  (Recv , MsgLeiosBlockTxs 17143 550001) ≡ "wire: transaction count cap exceeded"
client-over-cap-reply-reason = refl

-- All 268 indices are valid; 267 full words plus 62 bits request 17150 transactions.
overCapBitmap : Bitmap
overCapBitmap = applyUpTo (λ i → i , 18446744073709551615) 267 ++
  ((267 , 4611686018427387903) ∷ [])

-- The oversized count comes from a valid bitmap, rather than malformed input.
over-cap-bitmap-valid : Cardano_network.Replay.LeiosFetchWire.validᵇ overCapBitmap ≡ true
over-cap-bitmap-valid = refl

-- Its popcount is above the decoder's 17142-transaction limit.
over-cap-bitmap-count : Cardano_network.Replay.LeiosFetchWire.popcount overCapBitmap ≡ 17150
over-cap-bitmap-count = refl

-- Client sends reject the final decoder padding bit despite its small count.
client-padding-rejected : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 1) ∷ [])) ∷ [])) ≡ false
client-padding-rejected = refl

-- Padding is diagnosed as an offset violation rather than a count violation.
client-padding-reason : rejectionReason client₀ client₀
  ((Send , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 1) ∷ [])) ∷ []) ≡
  "client: request offset exceeds maxTxs at index 1"
client-padding-reason = refl

-- The last honest offset remains a legal client request.
client-last-offset-accepted : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 1024) ∷ [])) ∷ [])) ≡ true
client-last-offset-accepted = refl

-- The first padding offset is already outside the client send domain.
client-first-padding-rejected : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 512) ∷ [])) ∷ [])) ≡ false
client-first-padding-rejected = refl

-- Server decoding still permits the final padding offset 17151.
server-padding-accepted : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 1) ∷ [])) ∷ [])) ≡ true
server-padding-accepted = refl

-- Honest clients cannot request more than maxTxs, even with a valid bitmap.
client-request-over-cap : does (hasTrace? client-cert
  ((Send , MsgLeiosBlockTxsRequest 1 10 17150 overCapBitmap) ∷ [])) ≡ false
client-request-over-cap = refl

-- Oversized requests fail at the client layer rather than bitmap decoding.
client-request-over-cap-reason : rejectionReason client₀ client₀
  ((Send , MsgLeiosBlockTxsRequest 1 10 17150 overCapBitmap) ∷ []) ≡
  "client: request offset exceeds maxTxs at index 1"
client-request-over-cap-reason = refl

-- Servers may receive every valid request and then serve it or throw.
server-request-over-cap-accepted : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockTxsRequest 1 10 17150 overCapBitmap) ∷ [])) ≡ true
server-request-over-cap-accepted = refl

-- Even a 17150-count reply is permitted on a server send.
server-count-cap : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockTxsRequest 1 10 17150 overCapBitmap)
   ∷ (Send , MsgLeiosBlockTxs 17150 100) ∷ [])) ≡ true
server-count-cap = refl

-- Server diagnostics retain count matching even above both decoder caps.
server-count-cap-reason : whyRejected (sReady (blockTxsReq 1 10 2))
  (Send , MsgLeiosBlockTxs 17143 550001) ≡ "client: reply count mismatch"
server-count-cap-reason = refl

-- Oversized server sends have no cap failure to report after matching.
server-oversized-block-reason : whyRejected (sReady (blockReq 1 10))
  (Send , MsgLeiosBlock 1 700000) ≡ "none: no failed check"
server-oversized-block-reason = refl

-- Both decoder limits are ignored for a matching server transaction reply.
server-over-cap-reply-reason : whyRejected (sReady (blockTxsReq 1 10 17143))
  (Send , MsgLeiosBlockTxs 17143 550001) ≡ "none: no failed check"
server-over-cap-reply-reason = refl

-- A wrong server hash remains diagnosed even above the receive byte cap.
server-oversized-wrong-hash-reason : whyRejected (sReady (blockReq 1 10))
  (Send , MsgLeiosBlock 2 700000) ≡ "client: block hash mismatch"
server-oversized-wrong-hash-reason = refl

-- A server cannot send a different block hash for the outstanding request.
server-wrong-hash : does (hasTrace? server-cert
  ((Recv , MsgLeiosBlockRequest 1 10) ∷ (Send , MsgLeiosBlock 2 100) ∷ [])) ≡ false
server-wrong-hash = refl

-- Client session: client-ok.
client-ok : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 2 300)
    ∷ [])) ≡ true
client-ok = refl

-- Client session: client-count.
client-count : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 3 300)
    ∷ (Send , MsgLeiosBlockRequest 2 11)
    ∷ [])) ≡ false
client-count = refl

-- Client session: drain-ok.
drain-ok : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 3 300)
    ∷ (Send , MsgLeiosDone)
    ∷ [])) ≡ true
drain-ok = refl

-- Client session: numtxs-popcount.
numtxs-popcount : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 3 bm)
    ∷ [])) ≡ false
numtxs-popcount = refl

-- Client session: bad-bitmap.
bad-bitmap : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 0 ((0 , 0) ∷ []))
    ∷ [])) ≡ false
bad-bitmap = refl

-- Client session: too-many.
too-many : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 17143 300)
    ∷ (Send , MsgLeiosDone)
    ∷ [])) ≡ false
too-many = refl

-- Client session: too-big.
too-big : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 2 550001)
    ∷ [])) ≡ false
too-big = refl

-- Client session: block-hash.
block-hash : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlock 2 100)
    ∷ (Send , MsgLeiosBlockRequest 3 11)
    ∷ [])) ≡ false
block-hash = refl

-- Client session: block-hash-drain.
block-hash-drain : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlock 2 100)
    ∷ (Send , MsgLeiosDone)
    ∷ [])) ≡ true
block-hash-drain = refl

-- Client session: fifo.
fifo : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Send , MsgLeiosBlockTxsRequest 2 11 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 2 300)
    ∷ [])) ≡ false
fifo = refl

-- Server session: server-ok.
server-ok : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Send , MsgLeiosBlockTxs 2 300)
    ∷ [])) ≡ true
server-ok = refl

-- Server session: server-count.
server-count : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Send , MsgLeiosBlockTxs 1 300)
    ∷ [])) ≡ false
server-count = refl

-- Server session: throw-eof.
throw-eof : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ [])) ≡ true
throw-eof = refl

-- Server session: throw-block-eof.
throw-block-eof : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockRequest 1 10)
    ∷ [])) ≡ true
throw-block-eof = refl

-- Server session: server-popcount.
server-popcount : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 3 bm)
    ∷ [])) ≡ false
server-popcount = refl

-- Server session: server-bad-bitmap.
server-bad-bitmap : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 0 ((0 , 0) ∷ []))
    ∷ [])) ≡ false
server-bad-bitmap = refl

-- Client session: zero-count.
zero-count : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 0 300)
    ∷ (Send , MsgLeiosBlockRequest 2 11)
    ∷ [])) ≡ false
zero-count = refl

-- Client session: block-too-big.
block-too-big : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlock 1 660001)
    ∷ (Send , MsgLeiosDone)
    ∷ [])) ≡ false
block-too-big = refl

-- Server session: server-txs-too-big.
server-txs-too-big : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Send , MsgLeiosBlockTxs 2 550001)
    ∷ [])) ≡ true
server-txs-too-big = refl

-- Server session: server-block-too-big.
server-block-too-big : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockRequest 1 10)
    ∷ (Send , MsgLeiosBlock 1 660001)
    ∷ [])) ≡ true
server-block-too-big = refl

-- Client session: client-unsolicited.
client-unsolicited : does (hasTrace? client-cert
    ((Recv , MsgLeiosBlock 1 100)
    ∷ [])) ≡ false
client-unsolicited = refl

-- Server session: server-unsolicited.
server-unsolicited : does (hasTrace? server-cert
    ((Send , MsgLeiosBlock 1 100)
    ∷ [])) ≡ false
server-unsolicited = refl

-- Client session: client-duplicate.
client-duplicate : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlock 1 100)
    ∷ (Recv , MsgLeiosBlock 1 100)
    ∷ [])) ≡ false
client-duplicate = refl

-- Server session: server-duplicate.
server-duplicate : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockRequest 1 10)
    ∷ (Send , MsgLeiosBlock 1 100)
    ∷ (Send , MsgLeiosBlock 1 100)
    ∷ [])) ≡ false
server-duplicate = refl

-- Client session: client-done-pending.
client-done-pending : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Send , MsgLeiosDone)
    ∷ [])) ≡ false
client-done-pending = refl

-- Server session: server-done-pending.
server-done-pending : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosDone)
    ∷ [])) ≡ false
server-done-pending = refl

-- Server session: server-overlap.
server-overlap : does (hasTrace? server-cert
    ((Recv , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlockRequest 2 11)
    ∷ [])) ≡ false
server-overlap = refl

-- Client session: block-cap-boundary.
block-cap-boundary : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockRequest 1 10)
    ∷ (Recv , MsgLeiosBlock 1 660000)
    ∷ [])) ≡ true
block-cap-boundary = refl

-- Client session: txs-cap-boundary.
txs-cap-boundary : does (hasTrace? client-cert
    ((Send , MsgLeiosBlockTxsRequest 1 10 2 bm)
    ∷ (Recv , MsgLeiosBlockTxs 2 550000)
    ∷ [])) ≡ true
txs-cap-boundary = refl

-- Construct exactly n client requests, with the index as the requested hash.
requests : ℕ → List E
requests n = applyUpTo (λ i → Send , MsgLeiosBlockRequest i 0) n

-- The upstream pipeline accepts all 150 requests.
depth : does (hasTrace? client-cert (requests 150)) ≡ true
depth = refl

-- Request 151 exceeds the upstream pipeline bound.
depth-over : does (hasTrace? client-cert (requests 151)) ≡ false
depth-over = refl

-- A bad count can only have been consumed by draining, forbidding a new request.
client-count-diagnostic :
  whyRejected (cDrain []) (Send , MsgLeiosBlockRequest 2 11) ≡
    "client: draining forbids new requests"
client-count-diagnostic = refl

-- Invalid bitmap encoding is diagnosed before the logged popcount is checked.
bad-bitmap-diagnostic :
  whyRejected client₀ (Send , MsgLeiosBlockTxsRequest 1 10 0 ((0 , 0) ∷ [])) ≡
    "wire: invalid bitmap"
bad-bitmap-diagnostic = refl

-- Both application outcomes are enumerated, including the terminal throw.
throw-successors : taus (sBusy (blockReq 1 10)) ≡
  sReady (blockReq 1 10) ∷ sThrown ∷ []
throw-successors = refl

-- A thrown server has no visible continuation, in either direction.
throw-terminal-send : after sThrown (Send , MsgLeiosBlock 1 100) ≡ []
throw-terminal-send = refl

-- A thrown server cannot receive a new request either.
throw-terminal-recv : after sThrown (Recv , MsgLeiosBlockRequest 2 11) ≡ []
throw-terminal-recv = refl

-- A thrown server has no further silent step.
throw-terminal-tau : taus sThrown ≡ []
throw-terminal-tau = refl

-- A mismatched reply count is a client-layer failure on the checked reading.
count-diagnostic : whyRejected (cOpen (blockTxsReq 1 10 2 ∷ []))
  (Recv , MsgLeiosBlockTxs 3 300) ≡ "client: reply count mismatch"
count-diagnostic = refl

-- The count wire cap is checked before byte size or client matching.
count-cap-diagnostic : whyRejected (cOpen (blockTxsReq 1 10 2 ∷ []))
  (Recv , MsgLeiosBlockTxs 17143 550001) ≡ "wire: transaction count cap exceeded"
count-cap-diagnostic = refl

-- An impossible event kind is diagnosed using the current state.
kind-diagnostic : whyRejected client₀ (Recv , MsgLeiosBlock 1 100) ≡
  "wire: no step from client open"
kind-diagnostic = refl

-- Historical FIFO-skip log, now admitted as an unobservable drain on stop.
-- Its former non-membership claim is replaced below with a later-request case.
fifoSkip : List E
fifoSkip =
    (Send , MsgLeiosBlockRequest
       0x203b94b7bc9ec85d9c41f64fcb1bfc4ae81f52251359b64bbd1e5e0b8f111592 1781013)
  ∷ (Send , MsgLeiosBlockRequest
       0x322074c685b9aa591cfc461d269faf8bfa05889020b55c05a7e2bc61470d2f34 1781049)
  ∷ (Recv , MsgLeiosBlock
       0x322074c685b9aa591cfc461d269faf8bfa05889020b55c05a7e2bc61470d2f34 99975)
  ∷ []

-- With no later request, the mismatched hash may be drained.
fifoSkip-drained : does (hasTrace? client-cert fifoSkip) ≡ true
fifoSkip-drained = refl

-- Sending another request after the skip rules out the draining reading.
fifoSkip-continued : List E
fifoSkip-continued = fifoSkip ++ ((Send , MsgLeiosBlockRequest 3 11) ∷ [])

-- The continued historical counterexample still computes to rejection.
fifoSkip-continued-result : does (hasTrace? client-cert fifoSkip-continued) ≡ false
fifoSkip-continued-result = refl

-- The negative decision carries a proof of weak-trace non-membership.
fifoSkip-continued-rejected : ¬ HasTrace client₀ fifoSkip-continued
fifoSkip-continued-rejected =
  toWitnessFalse {a? = hasTrace? client-cert fifoSkip-continued} tt

-- A successful check has a neutral sentinel, never a wire-failure prefix.
no-failure-diagnostic : whyRejected client₀ (Send , MsgLeiosDone) ≡
  "none: no failed check"
no-failure-diagnostic = refl

-- The review's exact count mismatch is drainable until a later request.
drained-count-continuation : List E
drained-count-continuation =
    (Send , MsgLeiosBlockTxsRequest 1 10 2 ((0 , 0xc000000000000000) ∷ []))
  ∷ (Recv , MsgLeiosBlockTxs 3 300)
  ∷ (Send , MsgLeiosBlockRequest 2 11)
  ∷ []

-- The reproduction really rejects, rather than merely failing the checked path.
drained-count-rejected : does (hasTrace? client-cert drained-count-continuation) ≡ false
drained-count-rejected = refl

-- Diagnose the earlier checked failure even though the witness queue is empty.
drained-count-reason : rejectionReason client₀ (cDrain []) drained-count-continuation ≡
  "client: reply count mismatch at index 2 (accepted only by a draining client; a later event rules that out)"
drained-count-reason = refl

-- The same whole-history reading recovers the earlier hash mismatch.
drained-hash-reason : rejectionReason client₀ (cDrain [])
  ((Send , MsgLeiosBlockRequest 1 10) ∷ (Recv , MsgLeiosBlock 2 100)
   ∷ (Send , MsgLeiosBlockRequest 3 11) ∷ []) ≡
  "client: block hash mismatch at index 2 (accepted only by a draining client; a later event rules that out)"
drained-hash-reason = refl

-- A thrown server witness must not hide the checked service reply-count failure.
thrown-server-reason : rejectionReason server₀ sThrown
  ((Recv , MsgLeiosBlockTxsRequest 1 10 2 bm) ∷ (Send , MsgLeiosBlockTxs 3 300) ∷ []) ≡
  "client: reply count mismatch at index 2"
thrown-server-reason = refl

-- After a throw-capable prefix, checked service diagnoses a second request.
thrown-overlap-reason : rejectionReason server₀ sThrown
  ((Recv , MsgLeiosBlockRequest 1 10) ∷ (Recv , MsgLeiosBlockRequest 2 11) ∷ []) ≡
  "wire: request while one is outstanding at index 2"
thrown-overlap-reason = refl

-- A draining depth-overflow witness still reports the checked wire depth limit.
drained-depth-reason : Cert.rejectionReason 1 client₀ (cDrain (blockReq 1 10 ∷ []))
  ((Send , MsgLeiosBlockRequest 1 10) ∷ (Send , MsgLeiosBlockRequest 2 11) ∷ []) ≡
  "wire: pipeline depth exceeded at index 2"
drained-depth-reason = refl


-- An unsolicited later reply also rules out the earlier draining interpretation.
drained-unsolicited-reason : rejectionReason client₀ (cDrain [])
  ((Send , MsgLeiosBlockRequest 1 10) ∷ (Recv , MsgLeiosBlock 2 100)
   ∷ (Recv , MsgLeiosBlock 3 100) ∷ []) ≡
  "client: block hash mismatch at index 2 (accepted only by a draining client; a later event rules that out)"
drained-unsolicited-reason = refl
