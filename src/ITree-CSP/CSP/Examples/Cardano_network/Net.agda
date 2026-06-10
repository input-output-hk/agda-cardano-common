{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the shared network event type `Net`.
--
-- This module is parametrised by `(p : Params)` and `open Params p`,
-- which supplies the abstract data domains (+ their `DecEq` instances)
-- and the connection-count assignment `numConns : IDs → ℕ`
-- (instantiated to concrete values by a scenario module). From it we
-- derive the dependent connection type `Conn id = Fin (numConns id)`,
-- the per-protocol API/handler datatypes `ApiKA … ApiLF`, the shared
-- ⊤-carried network event type `Net : Set → Set`, and its decidable
-- equality `Net-≟` over `AnyTypes Net`.
--
-- Every constructor of `Net` yields `Net ⊤`, so the carried `Set` in an
-- `AnyTypes Net = Σ Set Net` is always `⊤`. Each network data payload is
-- led by `(id : IDs)` and its dependent connection `Conn id`, followed
-- by `Time = ℕ`, `Mode`, `Length = ℕ`, `Messages`; the API folds fix
-- `id` to a single protocol and carry only `Conn N2N_P`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.Unit using (⊤)
open import Data.List using (List)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Interaction_Trees using (AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.Net (p : Params) where

-- abstract data domains (+ their DecEq) and `numConns` from the params
open Params p
-- derived structured types + messages (+ their DecEq) over those domains
open import CSP.Examples.Cardano_network.Data p

------------------------------------------------------------------------
-- Step 1: dependent connection.
------------------------------------------------------------------------

Conn : IDs → Set
Conn id = Fin (numConns id)

------------------------------------------------------------------------
-- The six per-protocol API/handler datatypes.
--
-- Each `ApiP` enumerates that protocol's `Send*`/`Receive*Handler`/
-- `recvMsg*`/`errorCookie*` channels from the reference `.csp`. The
-- leading `Connection` of every such channel is supplied separately by
-- the `apiP : Conn N2N_P → ApiP → Net ⊤` constructor, so `ApiP` carries
-- only the remaining payload.
------------------------------------------------------------------------

-- KeepAlive: SendKAMsgKeepAlive.Cookie / SendKAMsgDone /
--            errorCookieMismatchKeepAlive.Cookie.Cookie
data ApiKA : Set where
  sendKAMsg  : Cookie → ApiKA
  sendKADone : ApiKA
  errCookie  : Cookie → Cookie → ApiKA

-- BlockFetch: SendBFMsgRequestRange.ChainRange / SendBFMsgClientDone /
--   SendBFMsgStartBatch / SendBFMsgNoBlocks / SendBFMsgBlock.Block /
--   SendBFMsgBatchDone / ReceiveBlockHandler.Block /
--   requestBFRangeHandler.ChainRange
data ApiBF : Set where
  sendBFRequestRange : ChainRange → ApiBF
  sendBFClientDone   : ApiBF
  sendBFStartBatch   : ApiBF
  sendBFNoBlocks     : ApiBF
  sendBFBlock        : Block → ApiBF
  sendBFBatchDone    : ApiBF
  recvBFBlock        : Block → ApiBF
  reqBFRange         : ChainRange → ApiBF

-- ChainSync: SendCSMsgRequestNext / SendCSMsgFindIntersect.[Point] /
--   SendCSMsgDone / SendCSMsgAwaitReply / SendCSMsgRollForward.Header.Tip /
--   SendCSMsgRollBackward.Point.Tip / SendCSMsgIntersectFound.Point.Tip /
--   SendCSMsgIntersectNotFound.Tip / ReceiveRollforwardHandler.Header.Tip /
--   ReceiveRollbackHandler.Point.Tip
data ApiCS : Set where
  sendCSRequestNext       : ApiCS
  sendCSFindIntersect     : List Point → ApiCS
  sendCSDone              : ApiCS
  sendCSAwaitReply        : ApiCS
  sendCSRollForward       : Header → Tip → ApiCS
  sendCSRollBackward      : Point → Tip → ApiCS
  sendCSIntersectFound    : Point → Tip → ApiCS
  sendCSIntersectNotFound : Tip → ApiCS
  recvCSRollforward       : Header → Tip → ApiCS
  recvCSRollback          : Point → Tip → ApiCS

-- TxSubmission: SendTSMsgReplyTxIds.[Txid] / SendTSMsgReplyTxs.[Tx] /
--   SendTSMsgDone / SendTSMsgRequestTxIdsBlocking.ℕ.ℕ /
--   SendTSMsgRequestTxIdsPipelined.ℕ.ℕ / SendTSMsgRequestTxsPipelined.[Txid] /
--   recvMsgRequestTxIds.BlockingStyle.ℕ.ℕ / recvMsgRequestTxs.[Txid]
data ApiTS : Set where
  sendTSReplyTxIds            : List Txid → ApiTS
  sendTSReplyTxs             : List Tx → ApiTS
  sendTSDone                 : ApiTS
  sendTSRequestTxIdsBlocking  : ℕ → ℕ → ApiTS
  sendTSRequestTxIdsPipelined : ℕ → ℕ → ApiTS
  sendTSRequestTxsPipelined   : List Txid → ApiTS
  recvTSRequestTxIds          : BlockingStyle → ℕ → ℕ → ApiTS
  recvTSRequestTxs            : List Txid → ApiTS

-- LeiosNotify: SendLNMsgRequestNext / SendLNMsgDone /
--   SendLNMsgBlockAnnouncement.Header / SendLNMsgBlockOffer.Point /
--   SendLNMsgBlockTxsOffer.Point / SendLNMsgVotesOffer.[Vote] /
--   ReceiveLNBlockAnnouncementHandler.Header / ReceiveLNBlockOfferHandler.Point /
--   ReceiveLNBlockTxsOfferHandler.Point / ReceiveLNVotesOfferHandler.[Vote]
data ApiLN : Set where
  sendLNRequestNext         : ApiLN
  sendLNDone                : ApiLN
  sendLNBlockAnnouncement   : Header → ApiLN
  sendLNBlockOffer          : Point → ApiLN
  sendLNBlockTxsOffer       : Point → ApiLN
  sendLNVotesOffer          : List Vote → ApiLN
  recvLNBlockAnnouncement   : Header → ApiLN
  recvLNBlockOffer          : Point → ApiLN
  recvLNBlockTxsOffer       : Point → ApiLN
  recvLNVotesOffer          : List Vote → ApiLN

-- LeiosFetch: SendLFMsgBlockRequest.Point / SendLFMsgBlockTxsRequest.Point.LFBitmap /
--   SendLFMsgVotesRequest.[Vote] / SendLFMsgBlockRangeRequest.ChainRange /
--   SendLFMsgDone / SendLFMsgBlock.Block / SendLFMsgBlockTxs.[Tx] /
--   SendLFMsgVoteDelivery.[VoteBlob] / SendLFMsgNextBlockAndTxsInRange.Block.[Tx] /
--   SendLFMsgLastBlockAndTxsInRange.Block.[Tx] / ReceiveLFBlockHandler.Block /
--   ReceiveLFBlockTxsHandler.[Tx] / ReceiveLFVoteDeliveryHandler.[VoteBlob] /
--   ReceiveLFRangeBlockHandler.Block.[Tx]
data ApiLF : Set where
  sendLFBlockRequest          : Point → ApiLF
  sendLFBlockTxsRequest       : Point → LFBitmap → ApiLF
  sendLFVotesRequest          : List Vote → ApiLF
  sendLFBlockRangeRequest     : ChainRange → ApiLF
  sendLFDone                  : ApiLF
  sendLFBlock                 : Block → ApiLF
  sendLFBlockTxs              : List Tx → ApiLF
  sendLFVoteDelivery          : List VoteBlob → ApiLF
  sendLFNextBlockAndTxsInRange : Block → List Tx → ApiLF
  sendLFLastBlockAndTxsInRange : Block → List Tx → ApiLF
  recvLFBlock                 : Block → ApiLF
  recvLFBlockTxs              : List Tx → ApiLF
  recvLFVoteDelivery          : List VoteBlob → ApiLF
  recvLFRangeBlock            : Block → List Tx → ApiLF

------------------------------------------------------------------------
-- DecEq instances for the six ApiP datatypes (hand-written, small).
------------------------------------------------------------------------

instance
  DecEq-ApiKA : DecEq ApiKA
  DecEq-ApiKA ._≟_ = go
    where
    go : (x y : ApiKA) → Dec (x ≡ y)
    go (sendKAMsg a)    (sendKAMsg b)    with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendKADone       sendKADone       = yes refl
    go (errCookie a b)  (errCookie c d)  with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendKAMsg _)    sendKADone       = no λ ()
    go (sendKAMsg _)    (errCookie _ _)  = no λ ()
    go sendKADone       (sendKAMsg _)    = no λ ()
    go sendKADone       (errCookie _ _)  = no λ ()
    go (errCookie _ _)  (sendKAMsg _)    = no λ ()
    go (errCookie _ _)  sendKADone       = no λ ()

  DecEq-ApiBF : DecEq ApiBF
  DecEq-ApiBF ._≟_ = go
    where
    go : (x y : ApiBF) → Dec (x ≡ y)
    go (sendBFRequestRange a) (sendBFRequestRange b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendBFClientDone sendBFClientDone = yes refl
    go sendBFStartBatch sendBFStartBatch = yes refl
    go sendBFNoBlocks   sendBFNoBlocks   = yes refl
    go (sendBFBlock a)  (sendBFBlock b)  with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendBFBatchDone  sendBFBatchDone  = yes refl
    go (recvBFBlock a)  (recvBFBlock b)  with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (reqBFRange a)   (reqBFRange b)   with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendBFRequestRange _) sendBFClientDone   = no λ ()
    go (sendBFRequestRange _) sendBFStartBatch   = no λ ()
    go (sendBFRequestRange _) sendBFNoBlocks     = no λ ()
    go (sendBFRequestRange _) (sendBFBlock _)    = no λ ()
    go (sendBFRequestRange _) sendBFBatchDone    = no λ ()
    go (sendBFRequestRange _) (recvBFBlock _)    = no λ ()
    go (sendBFRequestRange _) (reqBFRange _)     = no λ ()
    go sendBFClientDone (sendBFRequestRange _)   = no λ ()
    go sendBFClientDone sendBFStartBatch         = no λ ()
    go sendBFClientDone sendBFNoBlocks           = no λ ()
    go sendBFClientDone (sendBFBlock _)          = no λ ()
    go sendBFClientDone sendBFBatchDone          = no λ ()
    go sendBFClientDone (recvBFBlock _)          = no λ ()
    go sendBFClientDone (reqBFRange _)           = no λ ()
    go sendBFStartBatch (sendBFRequestRange _)   = no λ ()
    go sendBFStartBatch sendBFClientDone         = no λ ()
    go sendBFStartBatch sendBFNoBlocks           = no λ ()
    go sendBFStartBatch (sendBFBlock _)          = no λ ()
    go sendBFStartBatch sendBFBatchDone          = no λ ()
    go sendBFStartBatch (recvBFBlock _)          = no λ ()
    go sendBFStartBatch (reqBFRange _)           = no λ ()
    go sendBFNoBlocks   (sendBFRequestRange _)   = no λ ()
    go sendBFNoBlocks   sendBFClientDone         = no λ ()
    go sendBFNoBlocks   sendBFStartBatch         = no λ ()
    go sendBFNoBlocks   (sendBFBlock _)          = no λ ()
    go sendBFNoBlocks   sendBFBatchDone          = no λ ()
    go sendBFNoBlocks   (recvBFBlock _)          = no λ ()
    go sendBFNoBlocks   (reqBFRange _)           = no λ ()
    go (sendBFBlock _)  (sendBFRequestRange _)   = no λ ()
    go (sendBFBlock _)  sendBFClientDone         = no λ ()
    go (sendBFBlock _)  sendBFStartBatch         = no λ ()
    go (sendBFBlock _)  sendBFNoBlocks           = no λ ()
    go (sendBFBlock _)  sendBFBatchDone          = no λ ()
    go (sendBFBlock _)  (recvBFBlock _)          = no λ ()
    go (sendBFBlock _)  (reqBFRange _)           = no λ ()
    go sendBFBatchDone  (sendBFRequestRange _)   = no λ ()
    go sendBFBatchDone  sendBFClientDone         = no λ ()
    go sendBFBatchDone  sendBFStartBatch         = no λ ()
    go sendBFBatchDone  sendBFNoBlocks           = no λ ()
    go sendBFBatchDone  (sendBFBlock _)          = no λ ()
    go sendBFBatchDone  (recvBFBlock _)          = no λ ()
    go sendBFBatchDone  (reqBFRange _)           = no λ ()
    go (recvBFBlock _)  (sendBFRequestRange _)   = no λ ()
    go (recvBFBlock _)  sendBFClientDone         = no λ ()
    go (recvBFBlock _)  sendBFStartBatch         = no λ ()
    go (recvBFBlock _)  sendBFNoBlocks           = no λ ()
    go (recvBFBlock _)  (sendBFBlock _)          = no λ ()
    go (recvBFBlock _)  sendBFBatchDone          = no λ ()
    go (recvBFBlock _)  (reqBFRange _)           = no λ ()
    go (reqBFRange _)   (sendBFRequestRange _)   = no λ ()
    go (reqBFRange _)   sendBFClientDone         = no λ ()
    go (reqBFRange _)   sendBFStartBatch         = no λ ()
    go (reqBFRange _)   sendBFNoBlocks           = no λ ()
    go (reqBFRange _)   (sendBFBlock _)          = no λ ()
    go (reqBFRange _)   sendBFBatchDone          = no λ ()
    go (reqBFRange _)   (recvBFBlock _)          = no λ ()

  DecEq-ApiCS : DecEq ApiCS
  DecEq-ApiCS ._≟_ = go
    where
    go : (x y : ApiCS) → Dec (x ≡ y)
    go sendCSRequestNext sendCSRequestNext = yes refl
    go (sendCSFindIntersect a) (sendCSFindIntersect b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendCSDone sendCSDone = yes refl
    go sendCSAwaitReply sendCSAwaitReply = yes refl
    go (sendCSRollForward a b) (sendCSRollForward c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendCSRollBackward a b) (sendCSRollBackward c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendCSIntersectFound a b) (sendCSIntersectFound c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendCSIntersectNotFound a) (sendCSIntersectNotFound b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvCSRollforward a b) (recvCSRollforward c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (recvCSRollback a b) (recvCSRollback c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go sendCSRequestNext            (sendCSFindIntersect _)      = no λ ()
    go sendCSRequestNext            sendCSDone                   = no λ ()
    go sendCSRequestNext            sendCSAwaitReply             = no λ ()
    go sendCSRequestNext            (sendCSRollForward _ _)      = no λ ()
    go sendCSRequestNext            (sendCSRollBackward _ _)     = no λ ()
    go sendCSRequestNext            (sendCSIntersectFound _ _)   = no λ ()
    go sendCSRequestNext            (sendCSIntersectNotFound _)  = no λ ()
    go sendCSRequestNext            (recvCSRollforward _ _)      = no λ ()
    go sendCSRequestNext            (recvCSRollback _ _)         = no λ ()
    go (sendCSFindIntersect _)      sendCSRequestNext            = no λ ()
    go (sendCSFindIntersect _)      sendCSDone                   = no λ ()
    go (sendCSFindIntersect _)      sendCSAwaitReply             = no λ ()
    go (sendCSFindIntersect _)      (sendCSRollForward _ _)      = no λ ()
    go (sendCSFindIntersect _)      (sendCSRollBackward _ _)     = no λ ()
    go (sendCSFindIntersect _)      (sendCSIntersectFound _ _)   = no λ ()
    go (sendCSFindIntersect _)      (sendCSIntersectNotFound _)  = no λ ()
    go (sendCSFindIntersect _)      (recvCSRollforward _ _)      = no λ ()
    go (sendCSFindIntersect _)      (recvCSRollback _ _)         = no λ ()
    go sendCSDone                   sendCSRequestNext            = no λ ()
    go sendCSDone                   (sendCSFindIntersect _)      = no λ ()
    go sendCSDone                   sendCSAwaitReply             = no λ ()
    go sendCSDone                   (sendCSRollForward _ _)      = no λ ()
    go sendCSDone                   (sendCSRollBackward _ _)     = no λ ()
    go sendCSDone                   (sendCSIntersectFound _ _)   = no λ ()
    go sendCSDone                   (sendCSIntersectNotFound _)  = no λ ()
    go sendCSDone                   (recvCSRollforward _ _)      = no λ ()
    go sendCSDone                   (recvCSRollback _ _)         = no λ ()
    go sendCSAwaitReply             sendCSRequestNext            = no λ ()
    go sendCSAwaitReply             (sendCSFindIntersect _)      = no λ ()
    go sendCSAwaitReply             sendCSDone                   = no λ ()
    go sendCSAwaitReply             (sendCSRollForward _ _)      = no λ ()
    go sendCSAwaitReply             (sendCSRollBackward _ _)     = no λ ()
    go sendCSAwaitReply             (sendCSIntersectFound _ _)   = no λ ()
    go sendCSAwaitReply             (sendCSIntersectNotFound _)  = no λ ()
    go sendCSAwaitReply             (recvCSRollforward _ _)      = no λ ()
    go sendCSAwaitReply             (recvCSRollback _ _)         = no λ ()
    go (sendCSRollForward _ _)      sendCSRequestNext            = no λ ()
    go (sendCSRollForward _ _)      (sendCSFindIntersect _)      = no λ ()
    go (sendCSRollForward _ _)      sendCSDone                   = no λ ()
    go (sendCSRollForward _ _)      sendCSAwaitReply             = no λ ()
    go (sendCSRollForward _ _)      (sendCSRollBackward _ _)     = no λ ()
    go (sendCSRollForward _ _)      (sendCSIntersectFound _ _)   = no λ ()
    go (sendCSRollForward _ _)      (sendCSIntersectNotFound _)  = no λ ()
    go (sendCSRollForward _ _)      (recvCSRollforward _ _)      = no λ ()
    go (sendCSRollForward _ _)      (recvCSRollback _ _)         = no λ ()
    go (sendCSRollBackward _ _)     sendCSRequestNext            = no λ ()
    go (sendCSRollBackward _ _)     (sendCSFindIntersect _)      = no λ ()
    go (sendCSRollBackward _ _)     sendCSDone                   = no λ ()
    go (sendCSRollBackward _ _)     sendCSAwaitReply             = no λ ()
    go (sendCSRollBackward _ _)     (sendCSRollForward _ _)      = no λ ()
    go (sendCSRollBackward _ _)     (sendCSIntersectFound _ _)   = no λ ()
    go (sendCSRollBackward _ _)     (sendCSIntersectNotFound _)  = no λ ()
    go (sendCSRollBackward _ _)     (recvCSRollforward _ _)      = no λ ()
    go (sendCSRollBackward _ _)     (recvCSRollback _ _)         = no λ ()
    go (sendCSIntersectFound _ _)   sendCSRequestNext            = no λ ()
    go (sendCSIntersectFound _ _)   (sendCSFindIntersect _)      = no λ ()
    go (sendCSIntersectFound _ _)   sendCSDone                   = no λ ()
    go (sendCSIntersectFound _ _)   sendCSAwaitReply             = no λ ()
    go (sendCSIntersectFound _ _)   (sendCSRollForward _ _)      = no λ ()
    go (sendCSIntersectFound _ _)   (sendCSRollBackward _ _)     = no λ ()
    go (sendCSIntersectFound _ _)   (sendCSIntersectNotFound _)  = no λ ()
    go (sendCSIntersectFound _ _)   (recvCSRollforward _ _)      = no λ ()
    go (sendCSIntersectFound _ _)   (recvCSRollback _ _)         = no λ ()
    go (sendCSIntersectNotFound _)  sendCSRequestNext            = no λ ()
    go (sendCSIntersectNotFound _)  (sendCSFindIntersect _)      = no λ ()
    go (sendCSIntersectNotFound _)  sendCSDone                   = no λ ()
    go (sendCSIntersectNotFound _)  sendCSAwaitReply             = no λ ()
    go (sendCSIntersectNotFound _)  (sendCSRollForward _ _)      = no λ ()
    go (sendCSIntersectNotFound _)  (sendCSRollBackward _ _)     = no λ ()
    go (sendCSIntersectNotFound _)  (sendCSIntersectFound _ _)   = no λ ()
    go (sendCSIntersectNotFound _)  (recvCSRollforward _ _)      = no λ ()
    go (sendCSIntersectNotFound _)  (recvCSRollback _ _)         = no λ ()
    go (recvCSRollforward _ _)      sendCSRequestNext            = no λ ()
    go (recvCSRollforward _ _)      (sendCSFindIntersect _)      = no λ ()
    go (recvCSRollforward _ _)      sendCSDone                   = no λ ()
    go (recvCSRollforward _ _)      sendCSAwaitReply             = no λ ()
    go (recvCSRollforward _ _)      (sendCSRollForward _ _)      = no λ ()
    go (recvCSRollforward _ _)      (sendCSRollBackward _ _)     = no λ ()
    go (recvCSRollforward _ _)      (sendCSIntersectFound _ _)   = no λ ()
    go (recvCSRollforward _ _)      (sendCSIntersectNotFound _)  = no λ ()
    go (recvCSRollforward _ _)      (recvCSRollback _ _)         = no λ ()
    go (recvCSRollback _ _)         sendCSRequestNext            = no λ ()
    go (recvCSRollback _ _)         (sendCSFindIntersect _)      = no λ ()
    go (recvCSRollback _ _)         sendCSDone                   = no λ ()
    go (recvCSRollback _ _)         sendCSAwaitReply             = no λ ()
    go (recvCSRollback _ _)         (sendCSRollForward _ _)      = no λ ()
    go (recvCSRollback _ _)         (sendCSRollBackward _ _)     = no λ ()
    go (recvCSRollback _ _)         (sendCSIntersectFound _ _)   = no λ ()
    go (recvCSRollback _ _)         (sendCSIntersectNotFound _)  = no λ ()
    go (recvCSRollback _ _)         (recvCSRollforward _ _)      = no λ ()

  DecEq-ApiTS : DecEq ApiTS
  DecEq-ApiTS ._≟_ = go
    where
    go : (x y : ApiTS) → Dec (x ≡ y)
    go (sendTSReplyTxIds a) (sendTSReplyTxIds b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendTSReplyTxs a) (sendTSReplyTxs b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendTSDone sendTSDone = yes refl
    go (sendTSRequestTxIdsBlocking a b) (sendTSRequestTxIdsBlocking c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendTSRequestTxIdsPipelined a b) (sendTSRequestTxIdsPipelined c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendTSRequestTxsPipelined a) (sendTSRequestTxsPipelined b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvTSRequestTxIds a b c) (recvTSRequestTxIds d e f) with a ≟ d | b ≟ e | c ≟ f
    ... | yes refl | yes refl | yes refl = yes refl
    ... | no ¬p    | _        | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | _        | no ¬p    = no λ where refl → ¬p refl
    go (recvTSRequestTxs a) (recvTSRequestTxs b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendTSReplyTxIds _)            (sendTSReplyTxs _)                = no λ ()
    go (sendTSReplyTxIds _)            sendTSDone                        = no λ ()
    go (sendTSReplyTxIds _)            (sendTSRequestTxIdsBlocking _ _)  = no λ ()
    go (sendTSReplyTxIds _)            (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (sendTSReplyTxIds _)            (sendTSRequestTxsPipelined _)     = no λ ()
    go (sendTSReplyTxIds _)            (recvTSRequestTxIds _ _ _)        = no λ ()
    go (sendTSReplyTxIds _)            (recvTSRequestTxs _)              = no λ ()
    go (sendTSReplyTxs _)              (sendTSReplyTxIds _)              = no λ ()
    go (sendTSReplyTxs _)              sendTSDone                        = no λ ()
    go (sendTSReplyTxs _)              (sendTSRequestTxIdsBlocking _ _)  = no λ ()
    go (sendTSReplyTxs _)              (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (sendTSReplyTxs _)              (sendTSRequestTxsPipelined _)     = no λ ()
    go (sendTSReplyTxs _)              (recvTSRequestTxIds _ _ _)        = no λ ()
    go (sendTSReplyTxs _)              (recvTSRequestTxs _)              = no λ ()
    go sendTSDone                      (sendTSReplyTxIds _)              = no λ ()
    go sendTSDone                      (sendTSReplyTxs _)                = no λ ()
    go sendTSDone                      (sendTSRequestTxIdsBlocking _ _)  = no λ ()
    go sendTSDone                      (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go sendTSDone                      (sendTSRequestTxsPipelined _)     = no λ ()
    go sendTSDone                      (recvTSRequestTxIds _ _ _)        = no λ ()
    go sendTSDone                      (recvTSRequestTxs _)              = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (sendTSReplyTxIds _)            = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (sendTSReplyTxs _)             = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  sendTSDone                     = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (sendTSRequestTxsPipelined _)  = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (recvTSRequestTxIds _ _ _)     = no λ ()
    go (sendTSRequestTxIdsBlocking _ _)  (recvTSRequestTxs _)           = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (sendTSReplyTxIds _)           = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (sendTSReplyTxs _)            = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) sendTSDone                    = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (sendTSRequestTxIdsBlocking _ _) = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (sendTSRequestTxsPipelined _) = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (recvTSRequestTxIds _ _ _)    = no λ ()
    go (sendTSRequestTxIdsPipelined _ _) (recvTSRequestTxs _)          = no λ ()
    go (sendTSRequestTxsPipelined _)   (sendTSReplyTxIds _)            = no λ ()
    go (sendTSRequestTxsPipelined _)   (sendTSReplyTxs _)             = no λ ()
    go (sendTSRequestTxsPipelined _)   sendTSDone                     = no λ ()
    go (sendTSRequestTxsPipelined _)   (sendTSRequestTxIdsBlocking _ _) = no λ ()
    go (sendTSRequestTxsPipelined _)   (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (sendTSRequestTxsPipelined _)   (recvTSRequestTxIds _ _ _)     = no λ ()
    go (sendTSRequestTxsPipelined _)   (recvTSRequestTxs _)           = no λ ()
    go (recvTSRequestTxIds _ _ _)      (sendTSReplyTxIds _)           = no λ ()
    go (recvTSRequestTxIds _ _ _)      (sendTSReplyTxs _)            = no λ ()
    go (recvTSRequestTxIds _ _ _)      sendTSDone                    = no λ ()
    go (recvTSRequestTxIds _ _ _)      (sendTSRequestTxIdsBlocking _ _) = no λ ()
    go (recvTSRequestTxIds _ _ _)      (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (recvTSRequestTxIds _ _ _)      (sendTSRequestTxsPipelined _)  = no λ ()
    go (recvTSRequestTxIds _ _ _)      (recvTSRequestTxs _)           = no λ ()
    go (recvTSRequestTxs _)            (sendTSReplyTxIds _)           = no λ ()
    go (recvTSRequestTxs _)            (sendTSReplyTxs _)            = no λ ()
    go (recvTSRequestTxs _)            sendTSDone                    = no λ ()
    go (recvTSRequestTxs _)            (sendTSRequestTxIdsBlocking _ _) = no λ ()
    go (recvTSRequestTxs _)            (sendTSRequestTxIdsPipelined _ _) = no λ ()
    go (recvTSRequestTxs _)            (sendTSRequestTxsPipelined _)  = no λ ()
    go (recvTSRequestTxs _)            (recvTSRequestTxIds _ _ _)     = no λ ()

  DecEq-ApiLN : DecEq ApiLN
  DecEq-ApiLN ._≟_ = go
    where
    go : (x y : ApiLN) → Dec (x ≡ y)
    go sendLNRequestNext sendLNRequestNext = yes refl
    go sendLNDone sendLNDone = yes refl
    go (sendLNBlockAnnouncement a) (sendLNBlockAnnouncement b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLNBlockOffer a) (sendLNBlockOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLNBlockTxsOffer a) (sendLNBlockTxsOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLNVotesOffer a) (sendLNVotesOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLNBlockAnnouncement a) (recvLNBlockAnnouncement b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLNBlockOffer a) (recvLNBlockOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLNBlockTxsOffer a) (recvLNBlockTxsOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLNVotesOffer a) (recvLNVotesOffer b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendLNRequestNext          sendLNDone                   = no λ ()
    go sendLNRequestNext          (sendLNBlockAnnouncement _)  = no λ ()
    go sendLNRequestNext          (sendLNBlockOffer _)         = no λ ()
    go sendLNRequestNext          (sendLNBlockTxsOffer _)      = no λ ()
    go sendLNRequestNext          (sendLNVotesOffer _)         = no λ ()
    go sendLNRequestNext          (recvLNBlockAnnouncement _)  = no λ ()
    go sendLNRequestNext          (recvLNBlockOffer _)         = no λ ()
    go sendLNRequestNext          (recvLNBlockTxsOffer _)      = no λ ()
    go sendLNRequestNext          (recvLNVotesOffer _)         = no λ ()
    go sendLNDone                 sendLNRequestNext            = no λ ()
    go sendLNDone                 (sendLNBlockAnnouncement _)  = no λ ()
    go sendLNDone                 (sendLNBlockOffer _)         = no λ ()
    go sendLNDone                 (sendLNBlockTxsOffer _)      = no λ ()
    go sendLNDone                 (sendLNVotesOffer _)         = no λ ()
    go sendLNDone                 (recvLNBlockAnnouncement _)  = no λ ()
    go sendLNDone                 (recvLNBlockOffer _)         = no λ ()
    go sendLNDone                 (recvLNBlockTxsOffer _)      = no λ ()
    go sendLNDone                 (recvLNVotesOffer _)         = no λ ()
    go (sendLNBlockAnnouncement _) sendLNRequestNext           = no λ ()
    go (sendLNBlockAnnouncement _) sendLNDone                  = no λ ()
    go (sendLNBlockAnnouncement _) (sendLNBlockOffer _)        = no λ ()
    go (sendLNBlockAnnouncement _) (sendLNBlockTxsOffer _)     = no λ ()
    go (sendLNBlockAnnouncement _) (sendLNVotesOffer _)        = no λ ()
    go (sendLNBlockAnnouncement _) (recvLNBlockAnnouncement _) = no λ ()
    go (sendLNBlockAnnouncement _) (recvLNBlockOffer _)        = no λ ()
    go (sendLNBlockAnnouncement _) (recvLNBlockTxsOffer _)     = no λ ()
    go (sendLNBlockAnnouncement _) (recvLNVotesOffer _)        = no λ ()
    go (sendLNBlockOffer _)       sendLNRequestNext            = no λ ()
    go (sendLNBlockOffer _)       sendLNDone                   = no λ ()
    go (sendLNBlockOffer _)       (sendLNBlockAnnouncement _)  = no λ ()
    go (sendLNBlockOffer _)       (sendLNBlockTxsOffer _)      = no λ ()
    go (sendLNBlockOffer _)       (sendLNVotesOffer _)         = no λ ()
    go (sendLNBlockOffer _)       (recvLNBlockAnnouncement _)  = no λ ()
    go (sendLNBlockOffer _)       (recvLNBlockOffer _)         = no λ ()
    go (sendLNBlockOffer _)       (recvLNBlockTxsOffer _)      = no λ ()
    go (sendLNBlockOffer _)       (recvLNVotesOffer _)         = no λ ()
    go (sendLNBlockTxsOffer _)    sendLNRequestNext            = no λ ()
    go (sendLNBlockTxsOffer _)    sendLNDone                   = no λ ()
    go (sendLNBlockTxsOffer _)    (sendLNBlockAnnouncement _)  = no λ ()
    go (sendLNBlockTxsOffer _)    (sendLNBlockOffer _)         = no λ ()
    go (sendLNBlockTxsOffer _)    (sendLNVotesOffer _)         = no λ ()
    go (sendLNBlockTxsOffer _)    (recvLNBlockAnnouncement _)  = no λ ()
    go (sendLNBlockTxsOffer _)    (recvLNBlockOffer _)         = no λ ()
    go (sendLNBlockTxsOffer _)    (recvLNBlockTxsOffer _)      = no λ ()
    go (sendLNBlockTxsOffer _)    (recvLNVotesOffer _)         = no λ ()
    go (sendLNVotesOffer _)       sendLNRequestNext            = no λ ()
    go (sendLNVotesOffer _)       sendLNDone                   = no λ ()
    go (sendLNVotesOffer _)       (sendLNBlockAnnouncement _)  = no λ ()
    go (sendLNVotesOffer _)       (sendLNBlockOffer _)         = no λ ()
    go (sendLNVotesOffer _)       (sendLNBlockTxsOffer _)      = no λ ()
    go (sendLNVotesOffer _)       (recvLNBlockAnnouncement _)  = no λ ()
    go (sendLNVotesOffer _)       (recvLNBlockOffer _)         = no λ ()
    go (sendLNVotesOffer _)       (recvLNBlockTxsOffer _)      = no λ ()
    go (sendLNVotesOffer _)       (recvLNVotesOffer _)         = no λ ()
    go (recvLNBlockAnnouncement _) sendLNRequestNext           = no λ ()
    go (recvLNBlockAnnouncement _) sendLNDone                  = no λ ()
    go (recvLNBlockAnnouncement _) (sendLNBlockAnnouncement _) = no λ ()
    go (recvLNBlockAnnouncement _) (sendLNBlockOffer _)        = no λ ()
    go (recvLNBlockAnnouncement _) (sendLNBlockTxsOffer _)     = no λ ()
    go (recvLNBlockAnnouncement _) (sendLNVotesOffer _)        = no λ ()
    go (recvLNBlockAnnouncement _) (recvLNBlockOffer _)        = no λ ()
    go (recvLNBlockAnnouncement _) (recvLNBlockTxsOffer _)     = no λ ()
    go (recvLNBlockAnnouncement _) (recvLNVotesOffer _)        = no λ ()
    go (recvLNBlockOffer _)       sendLNRequestNext            = no λ ()
    go (recvLNBlockOffer _)       sendLNDone                   = no λ ()
    go (recvLNBlockOffer _)       (sendLNBlockAnnouncement _)  = no λ ()
    go (recvLNBlockOffer _)       (sendLNBlockOffer _)         = no λ ()
    go (recvLNBlockOffer _)       (sendLNBlockTxsOffer _)      = no λ ()
    go (recvLNBlockOffer _)       (sendLNVotesOffer _)         = no λ ()
    go (recvLNBlockOffer _)       (recvLNBlockAnnouncement _)  = no λ ()
    go (recvLNBlockOffer _)       (recvLNBlockTxsOffer _)      = no λ ()
    go (recvLNBlockOffer _)       (recvLNVotesOffer _)         = no λ ()
    go (recvLNBlockTxsOffer _)    sendLNRequestNext            = no λ ()
    go (recvLNBlockTxsOffer _)    sendLNDone                   = no λ ()
    go (recvLNBlockTxsOffer _)    (sendLNBlockAnnouncement _)  = no λ ()
    go (recvLNBlockTxsOffer _)    (sendLNBlockOffer _)         = no λ ()
    go (recvLNBlockTxsOffer _)    (sendLNBlockTxsOffer _)      = no λ ()
    go (recvLNBlockTxsOffer _)    (sendLNVotesOffer _)         = no λ ()
    go (recvLNBlockTxsOffer _)    (recvLNBlockAnnouncement _)  = no λ ()
    go (recvLNBlockTxsOffer _)    (recvLNBlockOffer _)         = no λ ()
    go (recvLNBlockTxsOffer _)    (recvLNVotesOffer _)         = no λ ()
    go (recvLNVotesOffer _)       sendLNRequestNext            = no λ ()
    go (recvLNVotesOffer _)       sendLNDone                   = no λ ()
    go (recvLNVotesOffer _)       (sendLNBlockAnnouncement _)  = no λ ()
    go (recvLNVotesOffer _)       (sendLNBlockOffer _)         = no λ ()
    go (recvLNVotesOffer _)       (sendLNBlockTxsOffer _)      = no λ ()
    go (recvLNVotesOffer _)       (sendLNVotesOffer _)         = no λ ()
    go (recvLNVotesOffer _)       (recvLNBlockAnnouncement _)  = no λ ()
    go (recvLNVotesOffer _)       (recvLNBlockOffer _)         = no λ ()
    go (recvLNVotesOffer _)       (recvLNBlockTxsOffer _)      = no λ ()

  DecEq-ApiLF : DecEq ApiLF
  DecEq-ApiLF ._≟_ = go
    where
    go : (x y : ApiLF) → Dec (x ≡ y)
    go (sendLFBlockRequest a) (sendLFBlockRequest b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLFBlockTxsRequest a b) (sendLFBlockTxsRequest c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendLFVotesRequest a) (sendLFVotesRequest b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLFBlockRangeRequest a) (sendLFBlockRangeRequest b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go sendLFDone sendLFDone = yes refl
    go (sendLFBlock a) (sendLFBlock b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLFBlockTxs a) (sendLFBlockTxs b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLFVoteDelivery a) (sendLFVoteDelivery b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (sendLFNextBlockAndTxsInRange a b) (sendLFNextBlockAndTxsInRange c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendLFLastBlockAndTxsInRange a b) (sendLFLastBlockAndTxsInRange c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (recvLFBlock a) (recvLFBlock b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLFBlockTxs a) (recvLFBlockTxs b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLFVoteDelivery a) (recvLFVoteDelivery b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (recvLFRangeBlock a b) (recvLFRangeBlock c d) with a ≟ c | b ≟ d
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (sendLFBlockRequest _)            (sendLFBlockTxsRequest _ _)         = no λ ()
    go (sendLFBlockRequest _)            (sendLFVotesRequest _)              = no λ ()
    go (sendLFBlockRequest _)            (sendLFBlockRangeRequest _)         = no λ ()
    go (sendLFBlockRequest _)            sendLFDone                          = no λ ()
    go (sendLFBlockRequest _)            (sendLFBlock _)                     = no λ ()
    go (sendLFBlockRequest _)            (sendLFBlockTxs _)                  = no λ ()
    go (sendLFBlockRequest _)            (sendLFVoteDelivery _)              = no λ ()
    go (sendLFBlockRequest _)            (sendLFNextBlockAndTxsInRange _ _)  = no λ ()
    go (sendLFBlockRequest _)            (sendLFLastBlockAndTxsInRange _ _)  = no λ ()
    go (sendLFBlockRequest _)            (recvLFBlock _)                     = no λ ()
    go (sendLFBlockRequest _)            (recvLFBlockTxs _)                  = no λ ()
    go (sendLFBlockRequest _)            (recvLFVoteDelivery _)              = no λ ()
    go (sendLFBlockRequest _)            (recvLFRangeBlock _ _)              = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFBlockRequest _)             = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFVotesRequest _)             = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFBlockRangeRequest _)        = no λ ()
    go (sendLFBlockTxsRequest _ _)       sendLFDone                         = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFBlock _)                    = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFBlockTxs _)                 = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFVoteDelivery _)             = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockTxsRequest _ _)       (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockTxsRequest _ _)       (recvLFBlock _)                    = no λ ()
    go (sendLFBlockTxsRequest _ _)       (recvLFBlockTxs _)                 = no λ ()
    go (sendLFBlockTxsRequest _ _)       (recvLFVoteDelivery _)             = no λ ()
    go (sendLFBlockTxsRequest _ _)       (recvLFRangeBlock _ _)             = no λ ()
    go (sendLFVotesRequest _)            (sendLFBlockRequest _)             = no λ ()
    go (sendLFVotesRequest _)            (sendLFBlockTxsRequest _ _)        = no λ ()
    go (sendLFVotesRequest _)            (sendLFBlockRangeRequest _)        = no λ ()
    go (sendLFVotesRequest _)            sendLFDone                         = no λ ()
    go (sendLFVotesRequest _)            (sendLFBlock _)                    = no λ ()
    go (sendLFVotesRequest _)            (sendLFBlockTxs _)                 = no λ ()
    go (sendLFVotesRequest _)            (sendLFVoteDelivery _)             = no λ ()
    go (sendLFVotesRequest _)            (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFVotesRequest _)            (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFVotesRequest _)            (recvLFBlock _)                    = no λ ()
    go (sendLFVotesRequest _)            (recvLFBlockTxs _)                 = no λ ()
    go (sendLFVotesRequest _)            (recvLFVoteDelivery _)             = no λ ()
    go (sendLFVotesRequest _)            (recvLFRangeBlock _ _)             = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFBlockRequest _)            = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFBlockTxsRequest _ _)       = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFVotesRequest _)            = no λ ()
    go (sendLFBlockRangeRequest _)       sendLFDone                        = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFBlock _)                   = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFBlockTxs _)                = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFVoteDelivery _)            = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockRangeRequest _)       (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockRangeRequest _)       (recvLFBlock _)                   = no λ ()
    go (sendLFBlockRangeRequest _)       (recvLFBlockTxs _)                = no λ ()
    go (sendLFBlockRangeRequest _)       (recvLFVoteDelivery _)            = no λ ()
    go (sendLFBlockRangeRequest _)       (recvLFRangeBlock _ _)            = no λ ()
    go sendLFDone                        (sendLFBlockRequest _)            = no λ ()
    go sendLFDone                        (sendLFBlockTxsRequest _ _)       = no λ ()
    go sendLFDone                        (sendLFVotesRequest _)            = no λ ()
    go sendLFDone                        (sendLFBlockRangeRequest _)       = no λ ()
    go sendLFDone                        (sendLFBlock _)                   = no λ ()
    go sendLFDone                        (sendLFBlockTxs _)                = no λ ()
    go sendLFDone                        (sendLFVoteDelivery _)            = no λ ()
    go sendLFDone                        (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go sendLFDone                        (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go sendLFDone                        (recvLFBlock _)                   = no λ ()
    go sendLFDone                        (recvLFBlockTxs _)                = no λ ()
    go sendLFDone                        (recvLFVoteDelivery _)            = no λ ()
    go sendLFDone                        (recvLFRangeBlock _ _)            = no λ ()
    go (sendLFBlock _)                   (sendLFBlockRequest _)            = no λ ()
    go (sendLFBlock _)                   (sendLFBlockTxsRequest _ _)       = no λ ()
    go (sendLFBlock _)                   (sendLFVotesRequest _)            = no λ ()
    go (sendLFBlock _)                   (sendLFBlockRangeRequest _)       = no λ ()
    go (sendLFBlock _)                   sendLFDone                        = no λ ()
    go (sendLFBlock _)                   (sendLFBlockTxs _)                = no λ ()
    go (sendLFBlock _)                   (sendLFVoteDelivery _)            = no λ ()
    go (sendLFBlock _)                   (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlock _)                   (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlock _)                   (recvLFBlock _)                   = no λ ()
    go (sendLFBlock _)                   (recvLFBlockTxs _)                = no λ ()
    go (sendLFBlock _)                   (recvLFVoteDelivery _)            = no λ ()
    go (sendLFBlock _)                   (recvLFRangeBlock _ _)            = no λ ()
    go (sendLFBlockTxs _)                (sendLFBlockRequest _)            = no λ ()
    go (sendLFBlockTxs _)                (sendLFBlockTxsRequest _ _)       = no λ ()
    go (sendLFBlockTxs _)                (sendLFVotesRequest _)            = no λ ()
    go (sendLFBlockTxs _)                (sendLFBlockRangeRequest _)       = no λ ()
    go (sendLFBlockTxs _)                sendLFDone                        = no λ ()
    go (sendLFBlockTxs _)                (sendLFBlock _)                   = no λ ()
    go (sendLFBlockTxs _)                (sendLFVoteDelivery _)            = no λ ()
    go (sendLFBlockTxs _)                (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockTxs _)                (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFBlockTxs _)                (recvLFBlock _)                   = no λ ()
    go (sendLFBlockTxs _)                (recvLFBlockTxs _)                = no λ ()
    go (sendLFBlockTxs _)                (recvLFVoteDelivery _)            = no λ ()
    go (sendLFBlockTxs _)                (recvLFRangeBlock _ _)            = no λ ()
    go (sendLFVoteDelivery _)            (sendLFBlockRequest _)            = no λ ()
    go (sendLFVoteDelivery _)            (sendLFBlockTxsRequest _ _)       = no λ ()
    go (sendLFVoteDelivery _)            (sendLFVotesRequest _)            = no λ ()
    go (sendLFVoteDelivery _)            (sendLFBlockRangeRequest _)       = no λ ()
    go (sendLFVoteDelivery _)            sendLFDone                        = no λ ()
    go (sendLFVoteDelivery _)            (sendLFBlock _)                   = no λ ()
    go (sendLFVoteDelivery _)            (sendLFBlockTxs _)                = no λ ()
    go (sendLFVoteDelivery _)            (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFVoteDelivery _)            (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFVoteDelivery _)            (recvLFBlock _)                   = no λ ()
    go (sendLFVoteDelivery _)            (recvLFBlockTxs _)                = no λ ()
    go (sendLFVoteDelivery _)            (recvLFVoteDelivery _)            = no λ ()
    go (sendLFVoteDelivery _)            (recvLFRangeBlock _ _)            = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFBlockRequest _)           = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFBlockTxsRequest _ _)      = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFVotesRequest _)           = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFBlockRangeRequest _)      = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) sendLFDone                       = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFBlock _)                  = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFBlockTxs _)               = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFVoteDelivery _)           = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (recvLFBlock _)                  = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (recvLFBlockTxs _)               = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (recvLFVoteDelivery _)           = no λ ()
    go (sendLFNextBlockAndTxsInRange _ _) (recvLFRangeBlock _ _)           = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFBlockRequest _)           = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFBlockTxsRequest _ _)      = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFVotesRequest _)           = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFBlockRangeRequest _)      = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) sendLFDone                       = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFBlock _)                  = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFBlockTxs _)               = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFVoteDelivery _)           = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (recvLFBlock _)                  = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (recvLFBlockTxs _)               = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (recvLFVoteDelivery _)           = no λ ()
    go (sendLFLastBlockAndTxsInRange _ _) (recvLFRangeBlock _ _)           = no λ ()
    go (recvLFBlock _)                   (sendLFBlockRequest _)            = no λ ()
    go (recvLFBlock _)                   (sendLFBlockTxsRequest _ _)       = no λ ()
    go (recvLFBlock _)                   (sendLFVotesRequest _)            = no λ ()
    go (recvLFBlock _)                   (sendLFBlockRangeRequest _)       = no λ ()
    go (recvLFBlock _)                   sendLFDone                        = no λ ()
    go (recvLFBlock _)                   (sendLFBlock _)                   = no λ ()
    go (recvLFBlock _)                   (sendLFBlockTxs _)                = no λ ()
    go (recvLFBlock _)                   (sendLFVoteDelivery _)            = no λ ()
    go (recvLFBlock _)                   (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (recvLFBlock _)                   (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (recvLFBlock _)                   (recvLFBlockTxs _)                = no λ ()
    go (recvLFBlock _)                   (recvLFVoteDelivery _)            = no λ ()
    go (recvLFBlock _)                   (recvLFRangeBlock _ _)            = no λ ()
    go (recvLFBlockTxs _)                (sendLFBlockRequest _)            = no λ ()
    go (recvLFBlockTxs _)                (sendLFBlockTxsRequest _ _)       = no λ ()
    go (recvLFBlockTxs _)                (sendLFVotesRequest _)            = no λ ()
    go (recvLFBlockTxs _)                (sendLFBlockRangeRequest _)       = no λ ()
    go (recvLFBlockTxs _)                sendLFDone                        = no λ ()
    go (recvLFBlockTxs _)                (sendLFBlock _)                   = no λ ()
    go (recvLFBlockTxs _)                (sendLFBlockTxs _)                = no λ ()
    go (recvLFBlockTxs _)                (sendLFVoteDelivery _)            = no λ ()
    go (recvLFBlockTxs _)                (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (recvLFBlockTxs _)                (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (recvLFBlockTxs _)                (recvLFBlock _)                   = no λ ()
    go (recvLFBlockTxs _)                (recvLFVoteDelivery _)            = no λ ()
    go (recvLFBlockTxs _)                (recvLFRangeBlock _ _)            = no λ ()
    go (recvLFVoteDelivery _)            (sendLFBlockRequest _)            = no λ ()
    go (recvLFVoteDelivery _)            (sendLFBlockTxsRequest _ _)       = no λ ()
    go (recvLFVoteDelivery _)            (sendLFVotesRequest _)            = no λ ()
    go (recvLFVoteDelivery _)            (sendLFBlockRangeRequest _)       = no λ ()
    go (recvLFVoteDelivery _)            sendLFDone                        = no λ ()
    go (recvLFVoteDelivery _)            (sendLFBlock _)                   = no λ ()
    go (recvLFVoteDelivery _)            (sendLFBlockTxs _)                = no λ ()
    go (recvLFVoteDelivery _)            (sendLFVoteDelivery _)            = no λ ()
    go (recvLFVoteDelivery _)            (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (recvLFVoteDelivery _)            (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (recvLFVoteDelivery _)            (recvLFBlock _)                   = no λ ()
    go (recvLFVoteDelivery _)            (recvLFBlockTxs _)                = no λ ()
    go (recvLFVoteDelivery _)            (recvLFRangeBlock _ _)            = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFBlockRequest _)            = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFBlockTxsRequest _ _)       = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFVotesRequest _)            = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFBlockRangeRequest _)       = no λ ()
    go (recvLFRangeBlock _ _)            sendLFDone                        = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFBlock _)                   = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFBlockTxs _)                = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFVoteDelivery _)            = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFNextBlockAndTxsInRange _ _) = no λ ()
    go (recvLFRangeBlock _ _)            (sendLFLastBlockAndTxsInRange _ _) = no λ ()
    go (recvLFRangeBlock _ _)            (recvLFBlock _)                   = no λ ()
    go (recvLFRangeBlock _ _)            (recvLFBlockTxs _)                = no λ ()
    go (recvLFRangeBlock _ _)            (recvLFVoteDelivery _)            = no λ ()

------------------------------------------------------------------------
-- Step 2: the shared network event type `Net`.
--
-- Every constructor yields `Net ⊤`. The protocol id `(id : IDs)` and its
-- dependent connection `Conn id` lead every network data payload. The
-- API folds fix `id` to a single protocol, carrying only `Conn N2N_P`.
------------------------------------------------------------------------

data Net : Set → Set where
  input output sndmsg rcvmsg tx : (id : IDs) → Conn id → ℕ → Mode → ℕ → Messages → Net ⊤
  sndack rcvack ack             : (id : IDs) → Conn id → ℕ → Net ⊤
  done                          : (id : IDs) → Conn id → Net ⊤
  apiKA : Conn N2N_KeepAlive    → ApiKA → Net ⊤
  apiBF : Conn N2N_BlockFetch   → ApiBF → Net ⊤
  apiCS : Conn N2N_ChainSync    → ApiCS → Net ⊤
  apiTS : Conn N2N_TxSubmission → ApiTS → Net ⊤
  apiLN : Conn N2N_LeiosNotify  → ApiLN → Net ⊤
  apiLF : Conn N2N_LeiosFetch   → ApiLF → Net ⊤

------------------------------------------------------------------------
-- Step 3: decidable equality on `AnyTypes Net`.
--
-- Since every constructor yields `Net ⊤`, the carried `Set` is always
-- `⊤`; we destructure each `AnyTypes Net` as `(⊤ , ctor …)` and decide
-- on the underlying `Net ⊤` values via the helper `go`.
--
-- The leading `(id , c)` of the network data/ack/done channels is a
-- dependent pair: we first decide `id₁ ≟ id₂` (IDs DecEq); on `refl` the
-- connections `c₁ c₂ : Conn id` share a type and are compared by the Fin
-- DecEq instance; mismatched ids ⇒ `no λ ()`.
------------------------------------------------------------------------

Net-≟ : (x y : AnyTypes Net) → Dec (x ≡ y)
Net-≟ = go
  where
  go : (x y : AnyTypes Net) → Dec (x ≡ y)
  -- input / input
  go (_ , input i₁ c₁ t₁ m₁ l₁ d₁) (_ , input i₂ c₂ t₂ m₂ l₂ d₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ...   | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ...   | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  -- output / output
  go (_ , (output i₁ c₁ t₁ m₁ l₁ d₁)) (_ , (output i₂ c₂ t₂ m₂ l₂ d₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ...   | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ...   | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  -- sndmsg / sndmsg
  go (_ , (sndmsg i₁ c₁ t₁ m₁ l₁ d₁)) (_ , (sndmsg i₂ c₂ t₂ m₂ l₂ d₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ...   | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ...   | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  -- rcvmsg / rcvmsg
  go (_ , (rcvmsg i₁ c₁ t₁ m₁ l₁ d₁)) (_ , (rcvmsg i₂ c₂ t₂ m₂ l₂ d₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ...   | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ...   | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  -- tx / tx
  go (_ , (tx i₁ c₁ t₁ m₁ l₁ d₁)) (_ , (tx i₂ c₂ t₂ m₂ l₂ d₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ...   | yes refl | yes refl | yes refl | yes refl | yes refl = yes refl
  ...   | no ¬p | _ | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
  -- sndack / sndack
  go (_ , (sndack i₁ c₁ t₁)) (_ , (sndack i₂ c₂ t₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂
  ...   | yes refl | yes refl = yes refl
  ...   | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p = no λ where refl → ¬p refl
  -- rcvack / rcvack
  go (_ , (rcvack i₁ c₁ t₁)) (_ , (rcvack i₂ c₂ t₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂
  ...   | yes refl | yes refl = yes refl
  ...   | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p = no λ where refl → ¬p refl
  -- ack / ack
  go (_ , (ack i₁ c₁ t₁)) (_ , (ack i₂ c₂ t₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂ | t₁ ≟ t₂
  ...   | yes refl | yes refl = yes refl
  ...   | no ¬p | _ = no λ where refl → ¬p refl
  ...   | _ | no ¬p = no λ where refl → ¬p refl
  -- done / done
  go (_ , (done i₁ c₁)) (_ , (done i₂ c₂)) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- api channels (id fixed; only Conn + ApiP to compare)
  go (_ , (apiKA c₁ a₁)) (_ , (apiKA c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , (apiBF c₁ a₁)) (_ , (apiBF c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , (apiCS c₁ a₁)) (_ , (apiCS c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , (apiTS c₁ a₁)) (_ , (apiTS c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , (apiLN c₁ a₁)) (_ , (apiLN c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  go (_ , (apiLF c₁ a₁)) (_ , (apiLF c₂ a₂)) with c₁ ≟ c₂ | a₁ ≟ a₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p = no λ where refl → ¬p refl
  -- cross-constructor: heads differ
  go (_ , (input _ _ _ _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (input _ _ _ _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (output _ _ _ _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (sndmsg _ _ _ _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (rcvmsg _ _ _ _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (tx _ _ _ _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (sndack _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (sndack _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (sndack _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (sndack _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (sndack _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (sndack _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (sndack _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (rcvack _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (ack _ _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (ack _ _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (ack _ _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (ack _ _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (ack _ _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (ack _ _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (ack _ _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (ack _ _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (done _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (done _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (done _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (done _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (done _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (done _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (done _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (done _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiKA _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiKA _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiKA _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiKA _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiKA _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiKA _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiKA _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiKA _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (apiKA _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiBF _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiBF _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiBF _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiBF _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiBF _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiBF _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiBF _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiBF _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (apiBF _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiCS _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiCS _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiCS _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiCS _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiCS _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiCS _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiCS _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiCS _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (apiCS _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiTS _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiTS _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiTS _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiTS _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiTS _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiTS _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiTS _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiTS _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (apiLN _ _))          = no λ ()
  go (_ , (apiTS _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiLN _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLN _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLN _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLN _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiLN _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiLN _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiLN _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiLN _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (apiLN _ _)) (_ , (apiLF _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (input _ _ _ _ _ _))  = no λ ()
  go (_ , (apiLF _ _)) (_ , (output _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLF _ _)) (_ , (sndmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLF _ _)) (_ , (rcvmsg _ _ _ _ _ _)) = no λ ()
  go (_ , (apiLF _ _)) (_ , (tx _ _ _ _ _ _))     = no λ ()
  go (_ , (apiLF _ _)) (_ , (sndack _ _ _))       = no λ ()
  go (_ , (apiLF _ _)) (_ , (rcvack _ _ _))       = no λ ()
  go (_ , (apiLF _ _)) (_ , (ack _ _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (done _ _))           = no λ ()
  go (_ , (apiLF _ _)) (_ , (apiKA _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (apiBF _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (apiCS _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (apiTS _ _))          = no λ ()
  go (_ , (apiLF _ _)) (_ , (apiLN _ _))          = no λ ()
