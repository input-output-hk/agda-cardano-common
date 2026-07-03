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
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (AnyTypes)
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
-- Each protocol's `Send*`/`Receive*Handler`/`recvMsg*`/`errorCookie*`
-- channels from the reference `.csp` are modelled as a *tag enum*
-- `ApiPTag` paired with a *carrier function* `ApiPCar : ApiPTag → Set`.
-- The channel's payload is the event's **carrier value** (the `?`/`!`
-- datum), NOT a constructor argument: a request like `SendKAMsg?cookie`
-- is an application *input*, so the cookie must be bindable as the value
-- (`ApiKACar sendKAMsg = Cookie`); payload-free tags carry `⊤`; multi-
-- field payloads carry a product (`errCookie ↦ Cookie × Cookie`).
--
-- The leading `Connection` and the tag are supplied by the `Net_Api`
-- constructor `apiP : (c : Conn N2N_P) (m : ApiPTag) → Net_Api Data (ApiPCar m)`;
-- the carrier `ApiPCar m` is computed from the *value* `m`, so the index
-- is small — no `--large-indices` (which Agda 2.8 deems unsafe). Event
-- identity (and hence `Net_Api-≟`) is `Connection` + tag only; the
-- payload lives in the carrier, not the identity. See
-- `docs/superpowers/specs/2026-06-24-carrier-indexed-api-design.md`.
------------------------------------------------------------------------

-- KeepAlive: SendKAMsgKeepAlive.Cookie / SendKAMsgDone /
--            errorCookieMismatchKeepAlive.Cookie.Cookie
data ApiKATag : Set where
  sendKAMsg sendKADone errCookie : ApiKATag

ApiKACar : ApiKATag → Set
ApiKACar sendKAMsg  = Cookie
ApiKACar sendKADone = ⊤
ApiKACar errCookie  = Cookie × Cookie

-- BlockFetch: SendBFMsgRequestRange.ChainRange / SendBFMsgClientDone /
--   SendBFMsgStartBatch / SendBFMsgNoBlocks / SendBFMsgBlock.Block /
--   SendBFMsgBatchDone / ReceiveBlockHandler.Block /
--   requestBFRangeHandler.ChainRange
data ApiBFTag : Set where
  sendBFRequestRange sendBFClientDone sendBFStartBatch sendBFNoBlocks
    sendBFBlock sendBFBatchDone recvBFBlock reqBFRange : ApiBFTag

-- Carrier of each API
ApiBFCar : ApiBFTag → Set
ApiBFCar sendBFRequestRange = ChainRange
ApiBFCar sendBFClientDone   = ⊤
ApiBFCar sendBFStartBatch   = ⊤
ApiBFCar sendBFNoBlocks     = ⊤
ApiBFCar sendBFBlock        = Block
ApiBFCar sendBFBatchDone    = ⊤
ApiBFCar recvBFBlock        = Block
ApiBFCar reqBFRange         = ChainRange

-- ChainSync: SendCSMsgRequestNext / SendCSMsgFindIntersect.[Point] /
--   SendCSMsgDone / SendCSMsgAwaitReply / SendCSMsgRollForward.Header.Tip /
--   SendCSMsgRollBackward.Point.Tip / SendCSMsgIntersectFound.Point.Tip /
--   SendCSMsgIntersectNotFound.Tip / ReceiveRollforwardHandler.Header.Tip /
--   ReceiveRollbackHandler.Point.Tip
data ApiCSTag : Set where
  sendCSRequestNext sendCSFindIntersect sendCSDone sendCSAwaitReply
    sendCSRollForward sendCSRollBackward sendCSIntersectFound
    sendCSIntersectNotFound recvCSRollforward recvCSRollback
    recvCSIntersectFound recvCSIntersectNotFound
    reqCSRequestNext reqCSFindIntersect : ApiCSTag

ApiCSCar : ApiCSTag → Set
ApiCSCar sendCSRequestNext       = ⊤
ApiCSCar sendCSFindIntersect     = List Point
ApiCSCar sendCSDone              = ⊤
ApiCSCar sendCSAwaitReply        = ⊤
ApiCSCar sendCSRollForward       = Header × Tip
ApiCSCar sendCSRollBackward      = Point × Tip
ApiCSCar sendCSIntersectFound    = Point × Tip
ApiCSCar sendCSIntersectNotFound = Tip
ApiCSCar recvCSRollforward       = Header × Tip
ApiCSCar recvCSRollback          = Point × Tip
ApiCSCar recvCSIntersectFound    = Point × Tip
ApiCSCar recvCSIntersectNotFound = Tip
ApiCSCar reqCSRequestNext        = ⊤
ApiCSCar reqCSFindIntersect      = List Point

-- TxSubmission: SendTSMsgReplyTxIds.[Txid] / SendTSMsgReplyTxs.[Tx] /
--   SendTSMsgDone / SendTSMsgRequestTxIdsBlocking.ℕ.ℕ /
--   SendTSMsgRequestTxIdsPipelined.ℕ.ℕ / SendTSMsgRequestTxsPipelined.[Txid] /
--   recvMsgRequestTxIds.BlockingStyle.ℕ.ℕ / recvMsgRequestTxs.[Txid]
data ApiTSTag : Set where
  sendTSReplyTxIds sendTSReplyTxs sendTSDone sendTSRequestTxIdsBlocking
    sendTSRequestTxIdsPipelined sendTSRequestTxsPipelined recvTSRequestTxIds
    recvTSRequestTxs : ApiTSTag

ApiTSCar : ApiTSTag → Set
ApiTSCar sendTSReplyTxIds            = List Txid
ApiTSCar sendTSReplyTxs              = List Tx
ApiTSCar sendTSDone                  = ⊤
ApiTSCar sendTSRequestTxIdsBlocking  = ℕ × ℕ
ApiTSCar sendTSRequestTxIdsPipelined = ℕ × ℕ
ApiTSCar sendTSRequestTxsPipelined   = List Txid
ApiTSCar recvTSRequestTxIds          = BlockingStyle × ℕ × ℕ
ApiTSCar recvTSRequestTxs            = List Txid

-- LeiosNotify: SendLNMsgRequestNext / SendLNMsgDone /
--   SendLNMsgBlockAnnouncement.Header / SendLNMsgBlockOffer.Point /
--   SendLNMsgBlockTxsOffer.Point / SendLNMsgVotesOffer.[Vote] /
--   ReceiveLNBlockAnnouncementHandler.Header / ReceiveLNBlockOfferHandler.Point /
--   ReceiveLNBlockTxsOfferHandler.Point / ReceiveLNVotesOfferHandler.[Vote]
data ApiLNTag : Set where
  sendLNRequestNext sendLNDone sendLNBlockAnnouncement sendLNBlockOffer
    sendLNBlockTxsOffer sendLNVotesOffer recvLNBlockAnnouncement
    recvLNBlockOffer recvLNBlockTxsOffer recvLNVotesOffer : ApiLNTag

ApiLNCar : ApiLNTag → Set
ApiLNCar sendLNRequestNext       = ⊤
ApiLNCar sendLNDone              = ⊤
ApiLNCar sendLNBlockAnnouncement = Header
ApiLNCar sendLNBlockOffer        = Point
ApiLNCar sendLNBlockTxsOffer     = Point
ApiLNCar sendLNVotesOffer        = List Vote
ApiLNCar recvLNBlockAnnouncement = Header
ApiLNCar recvLNBlockOffer        = Point
ApiLNCar recvLNBlockTxsOffer     = Point
ApiLNCar recvLNVotesOffer        = List Vote

-- LeiosFetch: SendLFMsgBlockRequest.Point / SendLFMsgBlockTxsRequest.Point.LFBitmap /
--   SendLFMsgVotesRequest.[Vote] / SendLFMsgBlockRangeRequest.ChainRange /
--   SendLFMsgDone / SendLFMsgBlock.Block / SendLFMsgBlockTxs.[Tx] /
--   SendLFMsgVoteDelivery.[VoteBlob] / SendLFMsgNextBlockAndTxsInRange.Block.[Tx] /
--   SendLFMsgLastBlockAndTxsInRange.Block.[Tx] / ReceiveLFBlockHandler.Block /
--   ReceiveLFBlockTxsHandler.[Tx] / ReceiveLFVoteDeliveryHandler.[VoteBlob] /
--   ReceiveLFRangeBlockHandler.Block.[Tx]
data ApiLFTag : Set where
  sendLFBlockRequest sendLFBlockTxsRequest sendLFVotesRequest
    sendLFBlockRangeRequest sendLFDone sendLFBlock sendLFBlockTxs
    sendLFVoteDelivery sendLFNextBlockAndTxsInRange sendLFLastBlockAndTxsInRange
    recvLFBlock recvLFBlockTxs recvLFVoteDelivery recvLFRangeBlock : ApiLFTag

ApiLFCar : ApiLFTag → Set
ApiLFCar sendLFBlockRequest           = Point
ApiLFCar sendLFBlockTxsRequest        = Point × LFBitmap
ApiLFCar sendLFVotesRequest           = List Vote
ApiLFCar sendLFBlockRangeRequest      = ChainRange
ApiLFCar sendLFDone                   = ⊤
ApiLFCar sendLFBlock                  = Block
ApiLFCar sendLFBlockTxs               = List Tx
ApiLFCar sendLFVoteDelivery           = List VoteBlob
ApiLFCar sendLFNextBlockAndTxsInRange = Block × List Tx
ApiLFCar sendLFLastBlockAndTxsInRange = Block × List Tx
ApiLFCar recvLFBlock                  = Block
ApiLFCar recvLFBlockTxs               = List Tx
ApiLFCar recvLFVoteDelivery           = List VoteBlob
ApiLFCar recvLFRangeBlock             = Block × List Tx

------------------------------------------------------------------------
-- DecEq instances for the six finite api tag enums (payload-free).
------------------------------------------------------------------------

instance
  DecEq-ApiKATag : DecEq ApiKATag
  DecEq-ApiKATag ._≟_ = go
    where
    go : (x y : ApiKATag) → Dec (x ≡ y)
    go sendKAMsg sendKAMsg = yes refl
    go sendKADone sendKADone = yes refl
    go errCookie errCookie = yes refl
    go sendKAMsg sendKADone = no λ ()
    go sendKAMsg errCookie = no λ ()
    go sendKADone sendKAMsg = no λ ()
    go sendKADone errCookie = no λ ()
    go errCookie sendKAMsg = no λ ()
    go errCookie sendKADone = no λ ()

  DecEq-ApiBFTag : DecEq ApiBFTag
  DecEq-ApiBFTag ._≟_ = go
    where
    go : (x y : ApiBFTag) → Dec (x ≡ y)
    go sendBFRequestRange sendBFRequestRange = yes refl
    go sendBFClientDone sendBFClientDone = yes refl
    go sendBFStartBatch sendBFStartBatch = yes refl
    go sendBFNoBlocks sendBFNoBlocks = yes refl
    go sendBFBlock sendBFBlock = yes refl
    go sendBFBatchDone sendBFBatchDone = yes refl
    go recvBFBlock recvBFBlock = yes refl
    go reqBFRange reqBFRange = yes refl
    go sendBFRequestRange sendBFClientDone = no λ ()
    go sendBFRequestRange sendBFStartBatch = no λ ()
    go sendBFRequestRange sendBFNoBlocks = no λ ()
    go sendBFRequestRange sendBFBlock = no λ ()
    go sendBFRequestRange sendBFBatchDone = no λ ()
    go sendBFRequestRange recvBFBlock = no λ ()
    go sendBFRequestRange reqBFRange = no λ ()
    go sendBFClientDone sendBFRequestRange = no λ ()
    go sendBFClientDone sendBFStartBatch = no λ ()
    go sendBFClientDone sendBFNoBlocks = no λ ()
    go sendBFClientDone sendBFBlock = no λ ()
    go sendBFClientDone sendBFBatchDone = no λ ()
    go sendBFClientDone recvBFBlock = no λ ()
    go sendBFClientDone reqBFRange = no λ ()
    go sendBFStartBatch sendBFRequestRange = no λ ()
    go sendBFStartBatch sendBFClientDone = no λ ()
    go sendBFStartBatch sendBFNoBlocks = no λ ()
    go sendBFStartBatch sendBFBlock = no λ ()
    go sendBFStartBatch sendBFBatchDone = no λ ()
    go sendBFStartBatch recvBFBlock = no λ ()
    go sendBFStartBatch reqBFRange = no λ ()
    go sendBFNoBlocks sendBFRequestRange = no λ ()
    go sendBFNoBlocks sendBFClientDone = no λ ()
    go sendBFNoBlocks sendBFStartBatch = no λ ()
    go sendBFNoBlocks sendBFBlock = no λ ()
    go sendBFNoBlocks sendBFBatchDone = no λ ()
    go sendBFNoBlocks recvBFBlock = no λ ()
    go sendBFNoBlocks reqBFRange = no λ ()
    go sendBFBlock sendBFRequestRange = no λ ()
    go sendBFBlock sendBFClientDone = no λ ()
    go sendBFBlock sendBFStartBatch = no λ ()
    go sendBFBlock sendBFNoBlocks = no λ ()
    go sendBFBlock sendBFBatchDone = no λ ()
    go sendBFBlock recvBFBlock = no λ ()
    go sendBFBlock reqBFRange = no λ ()
    go sendBFBatchDone sendBFRequestRange = no λ ()
    go sendBFBatchDone sendBFClientDone = no λ ()
    go sendBFBatchDone sendBFStartBatch = no λ ()
    go sendBFBatchDone sendBFNoBlocks = no λ ()
    go sendBFBatchDone sendBFBlock = no λ ()
    go sendBFBatchDone recvBFBlock = no λ ()
    go sendBFBatchDone reqBFRange = no λ ()
    go recvBFBlock sendBFRequestRange = no λ ()
    go recvBFBlock sendBFClientDone = no λ ()
    go recvBFBlock sendBFStartBatch = no λ ()
    go recvBFBlock sendBFNoBlocks = no λ ()
    go recvBFBlock sendBFBlock = no λ ()
    go recvBFBlock sendBFBatchDone = no λ ()
    go recvBFBlock reqBFRange = no λ ()
    go reqBFRange sendBFRequestRange = no λ ()
    go reqBFRange sendBFClientDone = no λ ()
    go reqBFRange sendBFStartBatch = no λ ()
    go reqBFRange sendBFNoBlocks = no λ ()
    go reqBFRange sendBFBlock = no λ ()
    go reqBFRange sendBFBatchDone = no λ ()
    go reqBFRange recvBFBlock = no λ ()

  DecEq-ApiCSTag : DecEq ApiCSTag
  DecEq-ApiCSTag ._≟_ = go
    where
    go : (x y : ApiCSTag) → Dec (x ≡ y)
    go sendCSRequestNext       sendCSRequestNext       = yes refl
    go sendCSFindIntersect     sendCSFindIntersect     = yes refl
    go sendCSDone              sendCSDone              = yes refl
    go sendCSAwaitReply        sendCSAwaitReply        = yes refl
    go sendCSRollForward       sendCSRollForward       = yes refl
    go sendCSRollBackward      sendCSRollBackward      = yes refl
    go sendCSIntersectFound    sendCSIntersectFound    = yes refl
    go sendCSIntersectNotFound sendCSIntersectNotFound = yes refl
    go recvCSRollforward       recvCSRollforward       = yes refl
    go recvCSRollback          recvCSRollback          = yes refl
    go recvCSIntersectFound    recvCSIntersectFound    = yes refl
    go recvCSIntersectNotFound recvCSIntersectNotFound = yes refl
    go reqCSRequestNext        reqCSRequestNext        = yes refl
    go reqCSFindIntersect      reqCSFindIntersect      = yes refl
    go sendCSRequestNext       sendCSFindIntersect     = no λ ()
    go sendCSRequestNext       sendCSDone              = no λ ()
    go sendCSRequestNext       sendCSAwaitReply        = no λ ()
    go sendCSRequestNext       sendCSRollForward       = no λ ()
    go sendCSRequestNext       sendCSRollBackward      = no λ ()
    go sendCSRequestNext       sendCSIntersectFound    = no λ ()
    go sendCSRequestNext       sendCSIntersectNotFound = no λ ()
    go sendCSRequestNext       recvCSRollforward       = no λ ()
    go sendCSRequestNext       recvCSRollback          = no λ ()
    go sendCSRequestNext       recvCSIntersectFound    = no λ ()
    go sendCSRequestNext       recvCSIntersectNotFound = no λ ()
    go sendCSRequestNext       reqCSRequestNext        = no λ ()
    go sendCSRequestNext       reqCSFindIntersect      = no λ ()
    go sendCSFindIntersect     sendCSRequestNext       = no λ ()
    go sendCSFindIntersect     sendCSDone              = no λ ()
    go sendCSFindIntersect     sendCSAwaitReply        = no λ ()
    go sendCSFindIntersect     sendCSRollForward       = no λ ()
    go sendCSFindIntersect     sendCSRollBackward      = no λ ()
    go sendCSFindIntersect     sendCSIntersectFound    = no λ ()
    go sendCSFindIntersect     sendCSIntersectNotFound = no λ ()
    go sendCSFindIntersect     recvCSRollforward       = no λ ()
    go sendCSFindIntersect     recvCSRollback          = no λ ()
    go sendCSFindIntersect     recvCSIntersectFound    = no λ ()
    go sendCSFindIntersect     recvCSIntersectNotFound = no λ ()
    go sendCSFindIntersect     reqCSRequestNext        = no λ ()
    go sendCSFindIntersect     reqCSFindIntersect      = no λ ()
    go sendCSDone              sendCSRequestNext       = no λ ()
    go sendCSDone              sendCSFindIntersect     = no λ ()
    go sendCSDone              sendCSAwaitReply        = no λ ()
    go sendCSDone              sendCSRollForward       = no λ ()
    go sendCSDone              sendCSRollBackward      = no λ ()
    go sendCSDone              sendCSIntersectFound    = no λ ()
    go sendCSDone              sendCSIntersectNotFound = no λ ()
    go sendCSDone              recvCSRollforward       = no λ ()
    go sendCSDone              recvCSRollback          = no λ ()
    go sendCSDone              recvCSIntersectFound    = no λ ()
    go sendCSDone              recvCSIntersectNotFound = no λ ()
    go sendCSDone              reqCSRequestNext        = no λ ()
    go sendCSDone              reqCSFindIntersect      = no λ ()
    go sendCSAwaitReply        sendCSRequestNext       = no λ ()
    go sendCSAwaitReply        sendCSFindIntersect     = no λ ()
    go sendCSAwaitReply        sendCSDone              = no λ ()
    go sendCSAwaitReply        sendCSRollForward       = no λ ()
    go sendCSAwaitReply        sendCSRollBackward      = no λ ()
    go sendCSAwaitReply        sendCSIntersectFound    = no λ ()
    go sendCSAwaitReply        sendCSIntersectNotFound = no λ ()
    go sendCSAwaitReply        recvCSRollforward       = no λ ()
    go sendCSAwaitReply        recvCSRollback          = no λ ()
    go sendCSAwaitReply        recvCSIntersectFound    = no λ ()
    go sendCSAwaitReply        recvCSIntersectNotFound = no λ ()
    go sendCSAwaitReply        reqCSRequestNext        = no λ ()
    go sendCSAwaitReply        reqCSFindIntersect      = no λ ()
    go sendCSRollForward       sendCSRequestNext       = no λ ()
    go sendCSRollForward       sendCSFindIntersect     = no λ ()
    go sendCSRollForward       sendCSDone              = no λ ()
    go sendCSRollForward       sendCSAwaitReply        = no λ ()
    go sendCSRollForward       sendCSRollBackward      = no λ ()
    go sendCSRollForward       sendCSIntersectFound    = no λ ()
    go sendCSRollForward       sendCSIntersectNotFound = no λ ()
    go sendCSRollForward       recvCSRollforward       = no λ ()
    go sendCSRollForward       recvCSRollback          = no λ ()
    go sendCSRollForward       recvCSIntersectFound    = no λ ()
    go sendCSRollForward       recvCSIntersectNotFound = no λ ()
    go sendCSRollForward       reqCSRequestNext        = no λ ()
    go sendCSRollForward       reqCSFindIntersect      = no λ ()
    go sendCSRollBackward      sendCSRequestNext       = no λ ()
    go sendCSRollBackward      sendCSFindIntersect     = no λ ()
    go sendCSRollBackward      sendCSDone              = no λ ()
    go sendCSRollBackward      sendCSAwaitReply        = no λ ()
    go sendCSRollBackward      sendCSRollForward       = no λ ()
    go sendCSRollBackward      sendCSIntersectFound    = no λ ()
    go sendCSRollBackward      sendCSIntersectNotFound = no λ ()
    go sendCSRollBackward      recvCSRollforward       = no λ ()
    go sendCSRollBackward      recvCSRollback          = no λ ()
    go sendCSRollBackward      recvCSIntersectFound    = no λ ()
    go sendCSRollBackward      recvCSIntersectNotFound = no λ ()
    go sendCSRollBackward      reqCSRequestNext        = no λ ()
    go sendCSRollBackward      reqCSFindIntersect      = no λ ()
    go sendCSIntersectFound    sendCSRequestNext       = no λ ()
    go sendCSIntersectFound    sendCSFindIntersect     = no λ ()
    go sendCSIntersectFound    sendCSDone              = no λ ()
    go sendCSIntersectFound    sendCSAwaitReply        = no λ ()
    go sendCSIntersectFound    sendCSRollForward       = no λ ()
    go sendCSIntersectFound    sendCSRollBackward      = no λ ()
    go sendCSIntersectFound    sendCSIntersectNotFound = no λ ()
    go sendCSIntersectFound    recvCSRollforward       = no λ ()
    go sendCSIntersectFound    recvCSRollback          = no λ ()
    go sendCSIntersectFound    recvCSIntersectFound    = no λ ()
    go sendCSIntersectFound    recvCSIntersectNotFound = no λ ()
    go sendCSIntersectFound    reqCSRequestNext        = no λ ()
    go sendCSIntersectFound    reqCSFindIntersect      = no λ ()
    go sendCSIntersectNotFound sendCSRequestNext       = no λ ()
    go sendCSIntersectNotFound sendCSFindIntersect     = no λ ()
    go sendCSIntersectNotFound sendCSDone              = no λ ()
    go sendCSIntersectNotFound sendCSAwaitReply        = no λ ()
    go sendCSIntersectNotFound sendCSRollForward       = no λ ()
    go sendCSIntersectNotFound sendCSRollBackward      = no λ ()
    go sendCSIntersectNotFound sendCSIntersectFound    = no λ ()
    go sendCSIntersectNotFound recvCSRollforward       = no λ ()
    go sendCSIntersectNotFound recvCSRollback          = no λ ()
    go sendCSIntersectNotFound recvCSIntersectFound    = no λ ()
    go sendCSIntersectNotFound recvCSIntersectNotFound = no λ ()
    go sendCSIntersectNotFound reqCSRequestNext        = no λ ()
    go sendCSIntersectNotFound reqCSFindIntersect      = no λ ()
    go recvCSRollforward       sendCSRequestNext       = no λ ()
    go recvCSRollforward       sendCSFindIntersect     = no λ ()
    go recvCSRollforward       sendCSDone              = no λ ()
    go recvCSRollforward       sendCSAwaitReply        = no λ ()
    go recvCSRollforward       sendCSRollForward       = no λ ()
    go recvCSRollforward       sendCSRollBackward      = no λ ()
    go recvCSRollforward       sendCSIntersectFound    = no λ ()
    go recvCSRollforward       sendCSIntersectNotFound = no λ ()
    go recvCSRollforward       recvCSRollback          = no λ ()
    go recvCSRollforward       recvCSIntersectFound    = no λ ()
    go recvCSRollforward       recvCSIntersectNotFound = no λ ()
    go recvCSRollforward       reqCSRequestNext        = no λ ()
    go recvCSRollforward       reqCSFindIntersect      = no λ ()
    go recvCSRollback          sendCSRequestNext       = no λ ()
    go recvCSRollback          sendCSFindIntersect     = no λ ()
    go recvCSRollback          sendCSDone              = no λ ()
    go recvCSRollback          sendCSAwaitReply        = no λ ()
    go recvCSRollback          sendCSRollForward       = no λ ()
    go recvCSRollback          sendCSRollBackward      = no λ ()
    go recvCSRollback          sendCSIntersectFound    = no λ ()
    go recvCSRollback          sendCSIntersectNotFound = no λ ()
    go recvCSRollback          recvCSRollforward       = no λ ()
    go recvCSRollback          recvCSIntersectFound    = no λ ()
    go recvCSRollback          recvCSIntersectNotFound = no λ ()
    go recvCSRollback          reqCSRequestNext        = no λ ()
    go recvCSRollback          reqCSFindIntersect      = no λ ()
    go recvCSIntersectFound    sendCSRequestNext       = no λ ()
    go recvCSIntersectFound    sendCSFindIntersect     = no λ ()
    go recvCSIntersectFound    sendCSDone              = no λ ()
    go recvCSIntersectFound    sendCSAwaitReply        = no λ ()
    go recvCSIntersectFound    sendCSRollForward       = no λ ()
    go recvCSIntersectFound    sendCSRollBackward      = no λ ()
    go recvCSIntersectFound    sendCSIntersectFound    = no λ ()
    go recvCSIntersectFound    sendCSIntersectNotFound = no λ ()
    go recvCSIntersectFound    recvCSRollforward       = no λ ()
    go recvCSIntersectFound    recvCSRollback          = no λ ()
    go recvCSIntersectFound    recvCSIntersectNotFound = no λ ()
    go recvCSIntersectFound    reqCSRequestNext        = no λ ()
    go recvCSIntersectFound    reqCSFindIntersect      = no λ ()
    go recvCSIntersectNotFound sendCSRequestNext       = no λ ()
    go recvCSIntersectNotFound sendCSFindIntersect     = no λ ()
    go recvCSIntersectNotFound sendCSDone              = no λ ()
    go recvCSIntersectNotFound sendCSAwaitReply        = no λ ()
    go recvCSIntersectNotFound sendCSRollForward       = no λ ()
    go recvCSIntersectNotFound sendCSRollBackward      = no λ ()
    go recvCSIntersectNotFound sendCSIntersectFound    = no λ ()
    go recvCSIntersectNotFound sendCSIntersectNotFound = no λ ()
    go recvCSIntersectNotFound recvCSRollforward       = no λ ()
    go recvCSIntersectNotFound recvCSRollback          = no λ ()
    go recvCSIntersectNotFound recvCSIntersectFound    = no λ ()
    go recvCSIntersectNotFound reqCSRequestNext        = no λ ()
    go recvCSIntersectNotFound reqCSFindIntersect      = no λ ()
    go reqCSRequestNext        sendCSRequestNext       = no λ ()
    go reqCSRequestNext        sendCSFindIntersect     = no λ ()
    go reqCSRequestNext        sendCSDone              = no λ ()
    go reqCSRequestNext        sendCSAwaitReply        = no λ ()
    go reqCSRequestNext        sendCSRollForward       = no λ ()
    go reqCSRequestNext        sendCSRollBackward      = no λ ()
    go reqCSRequestNext        sendCSIntersectFound    = no λ ()
    go reqCSRequestNext        sendCSIntersectNotFound = no λ ()
    go reqCSRequestNext        recvCSRollforward       = no λ ()
    go reqCSRequestNext        recvCSRollback          = no λ ()
    go reqCSRequestNext        recvCSIntersectFound    = no λ ()
    go reqCSRequestNext        recvCSIntersectNotFound = no λ ()
    go reqCSRequestNext        reqCSFindIntersect      = no λ ()
    go reqCSFindIntersect      sendCSRequestNext       = no λ ()
    go reqCSFindIntersect      sendCSFindIntersect     = no λ ()
    go reqCSFindIntersect      sendCSDone              = no λ ()
    go reqCSFindIntersect      sendCSAwaitReply        = no λ ()
    go reqCSFindIntersect      sendCSRollForward       = no λ ()
    go reqCSFindIntersect      sendCSRollBackward      = no λ ()
    go reqCSFindIntersect      sendCSIntersectFound    = no λ ()
    go reqCSFindIntersect      sendCSIntersectNotFound = no λ ()
    go reqCSFindIntersect      recvCSRollforward       = no λ ()
    go reqCSFindIntersect      recvCSRollback          = no λ ()
    go reqCSFindIntersect      recvCSIntersectFound    = no λ ()
    go reqCSFindIntersect      recvCSIntersectNotFound = no λ ()
    go reqCSFindIntersect      reqCSRequestNext        = no λ ()

  DecEq-ApiTSTag : DecEq ApiTSTag
  DecEq-ApiTSTag ._≟_ = go
    where
    go : (x y : ApiTSTag) → Dec (x ≡ y)
    go sendTSReplyTxIds sendTSReplyTxIds = yes refl
    go sendTSReplyTxs sendTSReplyTxs = yes refl
    go sendTSDone sendTSDone = yes refl
    go sendTSRequestTxIdsBlocking sendTSRequestTxIdsBlocking = yes refl
    go sendTSRequestTxIdsPipelined sendTSRequestTxIdsPipelined = yes refl
    go sendTSRequestTxsPipelined sendTSRequestTxsPipelined = yes refl
    go recvTSRequestTxIds recvTSRequestTxIds = yes refl
    go recvTSRequestTxs recvTSRequestTxs = yes refl
    go sendTSReplyTxIds sendTSReplyTxs = no λ ()
    go sendTSReplyTxIds sendTSDone = no λ ()
    go sendTSReplyTxIds sendTSRequestTxIdsBlocking = no λ ()
    go sendTSReplyTxIds sendTSRequestTxIdsPipelined = no λ ()
    go sendTSReplyTxIds sendTSRequestTxsPipelined = no λ ()
    go sendTSReplyTxIds recvTSRequestTxIds = no λ ()
    go sendTSReplyTxIds recvTSRequestTxs = no λ ()
    go sendTSReplyTxs sendTSReplyTxIds = no λ ()
    go sendTSReplyTxs sendTSDone = no λ ()
    go sendTSReplyTxs sendTSRequestTxIdsBlocking = no λ ()
    go sendTSReplyTxs sendTSRequestTxIdsPipelined = no λ ()
    go sendTSReplyTxs sendTSRequestTxsPipelined = no λ ()
    go sendTSReplyTxs recvTSRequestTxIds = no λ ()
    go sendTSReplyTxs recvTSRequestTxs = no λ ()
    go sendTSDone sendTSReplyTxIds = no λ ()
    go sendTSDone sendTSReplyTxs = no λ ()
    go sendTSDone sendTSRequestTxIdsBlocking = no λ ()
    go sendTSDone sendTSRequestTxIdsPipelined = no λ ()
    go sendTSDone sendTSRequestTxsPipelined = no λ ()
    go sendTSDone recvTSRequestTxIds = no λ ()
    go sendTSDone recvTSRequestTxs = no λ ()
    go sendTSRequestTxIdsBlocking sendTSReplyTxIds = no λ ()
    go sendTSRequestTxIdsBlocking sendTSReplyTxs = no λ ()
    go sendTSRequestTxIdsBlocking sendTSDone = no λ ()
    go sendTSRequestTxIdsBlocking sendTSRequestTxIdsPipelined = no λ ()
    go sendTSRequestTxIdsBlocking sendTSRequestTxsPipelined = no λ ()
    go sendTSRequestTxIdsBlocking recvTSRequestTxIds = no λ ()
    go sendTSRequestTxIdsBlocking recvTSRequestTxs = no λ ()
    go sendTSRequestTxIdsPipelined sendTSReplyTxIds = no λ ()
    go sendTSRequestTxIdsPipelined sendTSReplyTxs = no λ ()
    go sendTSRequestTxIdsPipelined sendTSDone = no λ ()
    go sendTSRequestTxIdsPipelined sendTSRequestTxIdsBlocking = no λ ()
    go sendTSRequestTxIdsPipelined sendTSRequestTxsPipelined = no λ ()
    go sendTSRequestTxIdsPipelined recvTSRequestTxIds = no λ ()
    go sendTSRequestTxIdsPipelined recvTSRequestTxs = no λ ()
    go sendTSRequestTxsPipelined sendTSReplyTxIds = no λ ()
    go sendTSRequestTxsPipelined sendTSReplyTxs = no λ ()
    go sendTSRequestTxsPipelined sendTSDone = no λ ()
    go sendTSRequestTxsPipelined sendTSRequestTxIdsBlocking = no λ ()
    go sendTSRequestTxsPipelined sendTSRequestTxIdsPipelined = no λ ()
    go sendTSRequestTxsPipelined recvTSRequestTxIds = no λ ()
    go sendTSRequestTxsPipelined recvTSRequestTxs = no λ ()
    go recvTSRequestTxIds sendTSReplyTxIds = no λ ()
    go recvTSRequestTxIds sendTSReplyTxs = no λ ()
    go recvTSRequestTxIds sendTSDone = no λ ()
    go recvTSRequestTxIds sendTSRequestTxIdsBlocking = no λ ()
    go recvTSRequestTxIds sendTSRequestTxIdsPipelined = no λ ()
    go recvTSRequestTxIds sendTSRequestTxsPipelined = no λ ()
    go recvTSRequestTxIds recvTSRequestTxs = no λ ()
    go recvTSRequestTxs sendTSReplyTxIds = no λ ()
    go recvTSRequestTxs sendTSReplyTxs = no λ ()
    go recvTSRequestTxs sendTSDone = no λ ()
    go recvTSRequestTxs sendTSRequestTxIdsBlocking = no λ ()
    go recvTSRequestTxs sendTSRequestTxIdsPipelined = no λ ()
    go recvTSRequestTxs sendTSRequestTxsPipelined = no λ ()
    go recvTSRequestTxs recvTSRequestTxIds = no λ ()

  DecEq-ApiLNTag : DecEq ApiLNTag
  DecEq-ApiLNTag ._≟_ = go
    where
    go : (x y : ApiLNTag) → Dec (x ≡ y)
    go sendLNRequestNext sendLNRequestNext = yes refl
    go sendLNDone sendLNDone = yes refl
    go sendLNBlockAnnouncement sendLNBlockAnnouncement = yes refl
    go sendLNBlockOffer sendLNBlockOffer = yes refl
    go sendLNBlockTxsOffer sendLNBlockTxsOffer = yes refl
    go sendLNVotesOffer sendLNVotesOffer = yes refl
    go recvLNBlockAnnouncement recvLNBlockAnnouncement = yes refl
    go recvLNBlockOffer recvLNBlockOffer = yes refl
    go recvLNBlockTxsOffer recvLNBlockTxsOffer = yes refl
    go recvLNVotesOffer recvLNVotesOffer = yes refl
    go sendLNRequestNext sendLNDone = no λ ()
    go sendLNRequestNext sendLNBlockAnnouncement = no λ ()
    go sendLNRequestNext sendLNBlockOffer = no λ ()
    go sendLNRequestNext sendLNBlockTxsOffer = no λ ()
    go sendLNRequestNext sendLNVotesOffer = no λ ()
    go sendLNRequestNext recvLNBlockAnnouncement = no λ ()
    go sendLNRequestNext recvLNBlockOffer = no λ ()
    go sendLNRequestNext recvLNBlockTxsOffer = no λ ()
    go sendLNRequestNext recvLNVotesOffer = no λ ()
    go sendLNDone sendLNRequestNext = no λ ()
    go sendLNDone sendLNBlockAnnouncement = no λ ()
    go sendLNDone sendLNBlockOffer = no λ ()
    go sendLNDone sendLNBlockTxsOffer = no λ ()
    go sendLNDone sendLNVotesOffer = no λ ()
    go sendLNDone recvLNBlockAnnouncement = no λ ()
    go sendLNDone recvLNBlockOffer = no λ ()
    go sendLNDone recvLNBlockTxsOffer = no λ ()
    go sendLNDone recvLNVotesOffer = no λ ()
    go sendLNBlockAnnouncement sendLNRequestNext = no λ ()
    go sendLNBlockAnnouncement sendLNDone = no λ ()
    go sendLNBlockAnnouncement sendLNBlockOffer = no λ ()
    go sendLNBlockAnnouncement sendLNBlockTxsOffer = no λ ()
    go sendLNBlockAnnouncement sendLNVotesOffer = no λ ()
    go sendLNBlockAnnouncement recvLNBlockAnnouncement = no λ ()
    go sendLNBlockAnnouncement recvLNBlockOffer = no λ ()
    go sendLNBlockAnnouncement recvLNBlockTxsOffer = no λ ()
    go sendLNBlockAnnouncement recvLNVotesOffer = no λ ()
    go sendLNBlockOffer sendLNRequestNext = no λ ()
    go sendLNBlockOffer sendLNDone = no λ ()
    go sendLNBlockOffer sendLNBlockAnnouncement = no λ ()
    go sendLNBlockOffer sendLNBlockTxsOffer = no λ ()
    go sendLNBlockOffer sendLNVotesOffer = no λ ()
    go sendLNBlockOffer recvLNBlockAnnouncement = no λ ()
    go sendLNBlockOffer recvLNBlockOffer = no λ ()
    go sendLNBlockOffer recvLNBlockTxsOffer = no λ ()
    go sendLNBlockOffer recvLNVotesOffer = no λ ()
    go sendLNBlockTxsOffer sendLNRequestNext = no λ ()
    go sendLNBlockTxsOffer sendLNDone = no λ ()
    go sendLNBlockTxsOffer sendLNBlockAnnouncement = no λ ()
    go sendLNBlockTxsOffer sendLNBlockOffer = no λ ()
    go sendLNBlockTxsOffer sendLNVotesOffer = no λ ()
    go sendLNBlockTxsOffer recvLNBlockAnnouncement = no λ ()
    go sendLNBlockTxsOffer recvLNBlockOffer = no λ ()
    go sendLNBlockTxsOffer recvLNBlockTxsOffer = no λ ()
    go sendLNBlockTxsOffer recvLNVotesOffer = no λ ()
    go sendLNVotesOffer sendLNRequestNext = no λ ()
    go sendLNVotesOffer sendLNDone = no λ ()
    go sendLNVotesOffer sendLNBlockAnnouncement = no λ ()
    go sendLNVotesOffer sendLNBlockOffer = no λ ()
    go sendLNVotesOffer sendLNBlockTxsOffer = no λ ()
    go sendLNVotesOffer recvLNBlockAnnouncement = no λ ()
    go sendLNVotesOffer recvLNBlockOffer = no λ ()
    go sendLNVotesOffer recvLNBlockTxsOffer = no λ ()
    go sendLNVotesOffer recvLNVotesOffer = no λ ()
    go recvLNBlockAnnouncement sendLNRequestNext = no λ ()
    go recvLNBlockAnnouncement sendLNDone = no λ ()
    go recvLNBlockAnnouncement sendLNBlockAnnouncement = no λ ()
    go recvLNBlockAnnouncement sendLNBlockOffer = no λ ()
    go recvLNBlockAnnouncement sendLNBlockTxsOffer = no λ ()
    go recvLNBlockAnnouncement sendLNVotesOffer = no λ ()
    go recvLNBlockAnnouncement recvLNBlockOffer = no λ ()
    go recvLNBlockAnnouncement recvLNBlockTxsOffer = no λ ()
    go recvLNBlockAnnouncement recvLNVotesOffer = no λ ()
    go recvLNBlockOffer sendLNRequestNext = no λ ()
    go recvLNBlockOffer sendLNDone = no λ ()
    go recvLNBlockOffer sendLNBlockAnnouncement = no λ ()
    go recvLNBlockOffer sendLNBlockOffer = no λ ()
    go recvLNBlockOffer sendLNBlockTxsOffer = no λ ()
    go recvLNBlockOffer sendLNVotesOffer = no λ ()
    go recvLNBlockOffer recvLNBlockAnnouncement = no λ ()
    go recvLNBlockOffer recvLNBlockTxsOffer = no λ ()
    go recvLNBlockOffer recvLNVotesOffer = no λ ()
    go recvLNBlockTxsOffer sendLNRequestNext = no λ ()
    go recvLNBlockTxsOffer sendLNDone = no λ ()
    go recvLNBlockTxsOffer sendLNBlockAnnouncement = no λ ()
    go recvLNBlockTxsOffer sendLNBlockOffer = no λ ()
    go recvLNBlockTxsOffer sendLNBlockTxsOffer = no λ ()
    go recvLNBlockTxsOffer sendLNVotesOffer = no λ ()
    go recvLNBlockTxsOffer recvLNBlockAnnouncement = no λ ()
    go recvLNBlockTxsOffer recvLNBlockOffer = no λ ()
    go recvLNBlockTxsOffer recvLNVotesOffer = no λ ()
    go recvLNVotesOffer sendLNRequestNext = no λ ()
    go recvLNVotesOffer sendLNDone = no λ ()
    go recvLNVotesOffer sendLNBlockAnnouncement = no λ ()
    go recvLNVotesOffer sendLNBlockOffer = no λ ()
    go recvLNVotesOffer sendLNBlockTxsOffer = no λ ()
    go recvLNVotesOffer sendLNVotesOffer = no λ ()
    go recvLNVotesOffer recvLNBlockAnnouncement = no λ ()
    go recvLNVotesOffer recvLNBlockOffer = no λ ()
    go recvLNVotesOffer recvLNBlockTxsOffer = no λ ()

  DecEq-ApiLFTag : DecEq ApiLFTag
  DecEq-ApiLFTag ._≟_ = go
    where
    go : (x y : ApiLFTag) → Dec (x ≡ y)
    go sendLFBlockRequest sendLFBlockRequest = yes refl
    go sendLFBlockTxsRequest sendLFBlockTxsRequest = yes refl
    go sendLFVotesRequest sendLFVotesRequest = yes refl
    go sendLFBlockRangeRequest sendLFBlockRangeRequest = yes refl
    go sendLFDone sendLFDone = yes refl
    go sendLFBlock sendLFBlock = yes refl
    go sendLFBlockTxs sendLFBlockTxs = yes refl
    go sendLFVoteDelivery sendLFVoteDelivery = yes refl
    go sendLFNextBlockAndTxsInRange sendLFNextBlockAndTxsInRange = yes refl
    go sendLFLastBlockAndTxsInRange sendLFLastBlockAndTxsInRange = yes refl
    go recvLFBlock recvLFBlock = yes refl
    go recvLFBlockTxs recvLFBlockTxs = yes refl
    go recvLFVoteDelivery recvLFVoteDelivery = yes refl
    go recvLFRangeBlock recvLFRangeBlock = yes refl
    go sendLFBlockRequest sendLFBlockTxsRequest = no λ ()
    go sendLFBlockRequest sendLFVotesRequest = no λ ()
    go sendLFBlockRequest sendLFBlockRangeRequest = no λ ()
    go sendLFBlockRequest sendLFDone = no λ ()
    go sendLFBlockRequest sendLFBlock = no λ ()
    go sendLFBlockRequest sendLFBlockTxs = no λ ()
    go sendLFBlockRequest sendLFVoteDelivery = no λ ()
    go sendLFBlockRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockRequest recvLFBlock = no λ ()
    go sendLFBlockRequest recvLFBlockTxs = no λ ()
    go sendLFBlockRequest recvLFVoteDelivery = no λ ()
    go sendLFBlockRequest recvLFRangeBlock = no λ ()
    go sendLFBlockTxsRequest sendLFBlockRequest = no λ ()
    go sendLFBlockTxsRequest sendLFVotesRequest = no λ ()
    go sendLFBlockTxsRequest sendLFBlockRangeRequest = no λ ()
    go sendLFBlockTxsRequest sendLFDone = no λ ()
    go sendLFBlockTxsRequest sendLFBlock = no λ ()
    go sendLFBlockTxsRequest sendLFBlockTxs = no λ ()
    go sendLFBlockTxsRequest sendLFVoteDelivery = no λ ()
    go sendLFBlockTxsRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockTxsRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockTxsRequest recvLFBlock = no λ ()
    go sendLFBlockTxsRequest recvLFBlockTxs = no λ ()
    go sendLFBlockTxsRequest recvLFVoteDelivery = no λ ()
    go sendLFBlockTxsRequest recvLFRangeBlock = no λ ()
    go sendLFVotesRequest sendLFBlockRequest = no λ ()
    go sendLFVotesRequest sendLFBlockTxsRequest = no λ ()
    go sendLFVotesRequest sendLFBlockRangeRequest = no λ ()
    go sendLFVotesRequest sendLFDone = no λ ()
    go sendLFVotesRequest sendLFBlock = no λ ()
    go sendLFVotesRequest sendLFBlockTxs = no λ ()
    go sendLFVotesRequest sendLFVoteDelivery = no λ ()
    go sendLFVotesRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFVotesRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFVotesRequest recvLFBlock = no λ ()
    go sendLFVotesRequest recvLFBlockTxs = no λ ()
    go sendLFVotesRequest recvLFVoteDelivery = no λ ()
    go sendLFVotesRequest recvLFRangeBlock = no λ ()
    go sendLFBlockRangeRequest sendLFBlockRequest = no λ ()
    go sendLFBlockRangeRequest sendLFBlockTxsRequest = no λ ()
    go sendLFBlockRangeRequest sendLFVotesRequest = no λ ()
    go sendLFBlockRangeRequest sendLFDone = no λ ()
    go sendLFBlockRangeRequest sendLFBlock = no λ ()
    go sendLFBlockRangeRequest sendLFBlockTxs = no λ ()
    go sendLFBlockRangeRequest sendLFVoteDelivery = no λ ()
    go sendLFBlockRangeRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockRangeRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockRangeRequest recvLFBlock = no λ ()
    go sendLFBlockRangeRequest recvLFBlockTxs = no λ ()
    go sendLFBlockRangeRequest recvLFVoteDelivery = no λ ()
    go sendLFBlockRangeRequest recvLFRangeBlock = no λ ()
    go sendLFDone sendLFBlockRequest = no λ ()
    go sendLFDone sendLFBlockTxsRequest = no λ ()
    go sendLFDone sendLFVotesRequest = no λ ()
    go sendLFDone sendLFBlockRangeRequest = no λ ()
    go sendLFDone sendLFBlock = no λ ()
    go sendLFDone sendLFBlockTxs = no λ ()
    go sendLFDone sendLFVoteDelivery = no λ ()
    go sendLFDone sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFDone sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFDone recvLFBlock = no λ ()
    go sendLFDone recvLFBlockTxs = no λ ()
    go sendLFDone recvLFVoteDelivery = no λ ()
    go sendLFDone recvLFRangeBlock = no λ ()
    go sendLFBlock sendLFBlockRequest = no λ ()
    go sendLFBlock sendLFBlockTxsRequest = no λ ()
    go sendLFBlock sendLFVotesRequest = no λ ()
    go sendLFBlock sendLFBlockRangeRequest = no λ ()
    go sendLFBlock sendLFDone = no λ ()
    go sendLFBlock sendLFBlockTxs = no λ ()
    go sendLFBlock sendLFVoteDelivery = no λ ()
    go sendLFBlock sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlock sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlock recvLFBlock = no λ ()
    go sendLFBlock recvLFBlockTxs = no λ ()
    go sendLFBlock recvLFVoteDelivery = no λ ()
    go sendLFBlock recvLFRangeBlock = no λ ()
    go sendLFBlockTxs sendLFBlockRequest = no λ ()
    go sendLFBlockTxs sendLFBlockTxsRequest = no λ ()
    go sendLFBlockTxs sendLFVotesRequest = no λ ()
    go sendLFBlockTxs sendLFBlockRangeRequest = no λ ()
    go sendLFBlockTxs sendLFDone = no λ ()
    go sendLFBlockTxs sendLFBlock = no λ ()
    go sendLFBlockTxs sendLFVoteDelivery = no λ ()
    go sendLFBlockTxs sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockTxs sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockTxs recvLFBlock = no λ ()
    go sendLFBlockTxs recvLFBlockTxs = no λ ()
    go sendLFBlockTxs recvLFVoteDelivery = no λ ()
    go sendLFBlockTxs recvLFRangeBlock = no λ ()
    go sendLFVoteDelivery sendLFBlockRequest = no λ ()
    go sendLFVoteDelivery sendLFBlockTxsRequest = no λ ()
    go sendLFVoteDelivery sendLFVotesRequest = no λ ()
    go sendLFVoteDelivery sendLFBlockRangeRequest = no λ ()
    go sendLFVoteDelivery sendLFDone = no λ ()
    go sendLFVoteDelivery sendLFBlock = no λ ()
    go sendLFVoteDelivery sendLFBlockTxs = no λ ()
    go sendLFVoteDelivery sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFVoteDelivery sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFVoteDelivery recvLFBlock = no λ ()
    go sendLFVoteDelivery recvLFBlockTxs = no λ ()
    go sendLFVoteDelivery recvLFVoteDelivery = no λ ()
    go sendLFVoteDelivery recvLFRangeBlock = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockTxsRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFVotesRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockRangeRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFDone = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlock = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockTxs = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFVoteDelivery = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFBlock = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFBlockTxs = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFVoteDelivery = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFRangeBlock = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockTxsRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFVotesRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockRangeRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFDone = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlock = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockTxs = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFVoteDelivery = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFBlock = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFBlockTxs = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFVoteDelivery = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFRangeBlock = no λ ()
    go recvLFBlock sendLFBlockRequest = no λ ()
    go recvLFBlock sendLFBlockTxsRequest = no λ ()
    go recvLFBlock sendLFVotesRequest = no λ ()
    go recvLFBlock sendLFBlockRangeRequest = no λ ()
    go recvLFBlock sendLFDone = no λ ()
    go recvLFBlock sendLFBlock = no λ ()
    go recvLFBlock sendLFBlockTxs = no λ ()
    go recvLFBlock sendLFVoteDelivery = no λ ()
    go recvLFBlock sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFBlock sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFBlock recvLFBlockTxs = no λ ()
    go recvLFBlock recvLFVoteDelivery = no λ ()
    go recvLFBlock recvLFRangeBlock = no λ ()
    go recvLFBlockTxs sendLFBlockRequest = no λ ()
    go recvLFBlockTxs sendLFBlockTxsRequest = no λ ()
    go recvLFBlockTxs sendLFVotesRequest = no λ ()
    go recvLFBlockTxs sendLFBlockRangeRequest = no λ ()
    go recvLFBlockTxs sendLFDone = no λ ()
    go recvLFBlockTxs sendLFBlock = no λ ()
    go recvLFBlockTxs sendLFBlockTxs = no λ ()
    go recvLFBlockTxs sendLFVoteDelivery = no λ ()
    go recvLFBlockTxs sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFBlockTxs sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFBlockTxs recvLFBlock = no λ ()
    go recvLFBlockTxs recvLFVoteDelivery = no λ ()
    go recvLFBlockTxs recvLFRangeBlock = no λ ()
    go recvLFVoteDelivery sendLFBlockRequest = no λ ()
    go recvLFVoteDelivery sendLFBlockTxsRequest = no λ ()
    go recvLFVoteDelivery sendLFVotesRequest = no λ ()
    go recvLFVoteDelivery sendLFBlockRangeRequest = no λ ()
    go recvLFVoteDelivery sendLFDone = no λ ()
    go recvLFVoteDelivery sendLFBlock = no λ ()
    go recvLFVoteDelivery sendLFBlockTxs = no λ ()
    go recvLFVoteDelivery sendLFVoteDelivery = no λ ()
    go recvLFVoteDelivery sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFVoteDelivery sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFVoteDelivery recvLFBlock = no λ ()
    go recvLFVoteDelivery recvLFBlockTxs = no λ ()
    go recvLFVoteDelivery recvLFRangeBlock = no λ ()
    go recvLFRangeBlock sendLFBlockRequest = no λ ()
    go recvLFRangeBlock sendLFBlockTxsRequest = no λ ()
    go recvLFRangeBlock sendLFVotesRequest = no λ ()
    go recvLFRangeBlock sendLFBlockRangeRequest = no λ ()
    go recvLFRangeBlock sendLFDone = no λ ()
    go recvLFRangeBlock sendLFBlock = no λ ()
    go recvLFRangeBlock sendLFBlockTxs = no λ ()
    go recvLFRangeBlock sendLFVoteDelivery = no λ ()
    go recvLFRangeBlock sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFRangeBlock sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFRangeBlock recvLFBlock = no λ ()
    go recvLFRangeBlock recvLFBlockTxs = no λ ()
    go recvLFRangeBlock recvLFVoteDelivery = no λ ()


------------------------------------------------------------------------
-- Step 2: the shared network event type `Net`.
--
-- `Net` is parametrised by an abstract payload type `Data`: at the
-- network level the carried data is opaque — its contents are a
-- mini-protocol concern, supplied concretely downstream as `Net <D>`.
-- The protocol id `(id : IDs)` and its dependent connection `Conn id`
-- lead every channel; the five message channels have carried type
-- `Data` (the ITrees-style `E A` value type, negotiated by `?`/`!`),
-- while the three acknowledgement channels have carried type `⊤`.
------------------------------------------------------------------------

data Net (Data : Set) : Set → Set where
  input output sndmsg rcvmsg tx : (id : IDs) → Conn id → Net Data Data
  sndack rcvack ack             : (id : IDs) → Conn id → Net Data ⊤

------------------------------------------------------------------------
-- Step 3: decidable equality on `AnyTypes (Net Data)`.
--
-- `Net-≟` identifies an event by `(constructor, id, Conn id)` only — the
-- carried `Data` is negotiated by `?`/`!`, not part of the event
-- identity, so no `DecEq Data` is needed. We destructure each
-- `AnyTypes (Net Data)` as `(_ , ctor …)` and decide via the helper `go`.
--
-- The leading `(id , c)` of every channel is a dependent pair: we first
-- decide `id₁ ≟ id₂` (IDs DecEq); on `refl` the connections `c₁ c₂ :
-- Conn id` share a type and are compared by the Fin DecEq instance;
-- mismatched ids ⇒ `no λ ()`.
------------------------------------------------------------------------

Net-≟ : {Data : Set} → (x y : AnyTypes (Net Data)) → Dec (x ≡ y)
Net-≟ {Data} = go
  where
  go : (x y : AnyTypes (Net Data)) → Dec (x ≡ y)
  -- input / input
  go (_ , input i₁ c₁) (_ , input i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- output / output
  go (_ , output i₁ c₁) (_ , output i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- sndmsg / sndmsg
  go (_ , sndmsg i₁ c₁) (_ , sndmsg i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- rcvmsg / rcvmsg
  go (_ , rcvmsg i₁ c₁) (_ , rcvmsg i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- tx / tx
  go (_ , tx i₁ c₁) (_ , tx i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- sndack / sndack
  go (_ , sndack i₁ c₁) (_ , sndack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- rcvack / rcvack
  go (_ , rcvack i₁ c₁) (_ , rcvack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- ack / ack
  go (_ , ack i₁ c₁) (_ , ack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  -- off-diagonal: distinct constructors are never equal
  go (_ , input _ _)  (_ , output _ _) = no λ ()
  go (_ , input _ _)  (_ , sndmsg _ _) = no λ ()
  go (_ , input _ _)  (_ , rcvmsg _ _) = no λ ()
  go (_ , input _ _)  (_ , tx _ _)     = no λ ()
  go (_ , input _ _)  (_ , sndack _ _)   = no λ ()
  go (_ , input _ _)  (_ , rcvack _ _)   = no λ ()
  go (_ , input _ _)  (_ , ack _ _)      = no λ ()
  go (_ , output _ _) (_ , input _ _)  = no λ ()
  go (_ , output _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , output _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , output _ _) (_ , tx _ _)     = no λ ()
  go (_ , output _ _) (_ , sndack _ _)   = no λ ()
  go (_ , output _ _) (_ , rcvack _ _)   = no λ ()
  go (_ , output _ _) (_ , ack _ _)      = no λ ()
  go (_ , sndmsg _ _) (_ , input _ _)  = no λ ()
  go (_ , sndmsg _ _) (_ , output _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , tx _ _)     = no λ ()
  go (_ , sndmsg _ _) (_ , sndack _ _)   = no λ ()
  go (_ , sndmsg _ _) (_ , rcvack _ _)   = no λ ()
  go (_ , sndmsg _ _) (_ , ack _ _)      = no λ ()
  go (_ , rcvmsg _ _) (_ , input _ _)  = no λ ()
  go (_ , rcvmsg _ _) (_ , output _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , tx _ _)     = no λ ()
  go (_ , rcvmsg _ _) (_ , sndack _ _)   = no λ ()
  go (_ , rcvmsg _ _) (_ , rcvack _ _)   = no λ ()
  go (_ , rcvmsg _ _) (_ , ack _ _)      = no λ ()
  go (_ , tx _ _)     (_ , input _ _)  = no λ ()
  go (_ , tx _ _)     (_ , output _ _) = no λ ()
  go (_ , tx _ _)     (_ , sndmsg _ _) = no λ ()
  go (_ , tx _ _)     (_ , rcvmsg _ _) = no λ ()
  go (_ , tx _ _)     (_ , sndack _ _)   = no λ ()
  go (_ , tx _ _)     (_ , rcvack _ _)   = no λ ()
  go (_ , tx _ _)     (_ , ack _ _)      = no λ ()
  go (_ , sndack _ _)   (_ , input _ _)  = no λ ()
  go (_ , sndack _ _)   (_ , output _ _) = no λ ()
  go (_ , sndack _ _)   (_ , sndmsg _ _) = no λ ()
  go (_ , sndack _ _)   (_ , rcvmsg _ _) = no λ ()
  go (_ , sndack _ _)   (_ , tx _ _)     = no λ ()
  go (_ , sndack _ _)   (_ , rcvack _ _)   = no λ ()
  go (_ , sndack _ _)   (_ , ack _ _)      = no λ ()
  go (_ , rcvack _ _)   (_ , input _ _)  = no λ ()
  go (_ , rcvack _ _)   (_ , output _ _) = no λ ()
  go (_ , rcvack _ _)   (_ , sndmsg _ _) = no λ ()
  go (_ , rcvack _ _)   (_ , rcvmsg _ _) = no λ ()
  go (_ , rcvack _ _)   (_ , tx _ _)     = no λ ()
  go (_ , rcvack _ _)   (_ , sndack _ _)   = no λ ()
  go (_ , rcvack _ _)   (_ , ack _ _)      = no λ ()
  go (_ , ack _ _)      (_ , input _ _)  = no λ ()
  go (_ , ack _ _)      (_ , output _ _) = no λ ()
  go (_ , ack _ _)      (_ , sndmsg _ _) = no λ ()
  go (_ , ack _ _)      (_ , rcvmsg _ _) = no λ ()
  go (_ , ack _ _)      (_ , tx _ _)     = no λ ()
  go (_ , ack _ _)      (_ , sndack _ _)   = no λ ()
  go (_ , ack _ _)      (_ , rcvack _ _)   = no λ ()

------------------------------------------------------------------------
-- Step 4: an api-carrying *superset* network event type `Net_Api`.
--
-- A second shared alphabet that keeps every channel of `Net`
-- (`input output sndmsg rcvmsg tx` + `sndack rcvack ack`), adds a
-- protocol-level `done`, and adds one api constructor per mini-protocol
-- -- the same six `ApiP` folds as the per-protocol events (cf. `KAEv`'s
-- `apiKAev`/`doneKA` in `KeepAlive.agda`), lifted to the shared level.
--
-- Being a superset of `Net` is what lets the *real* `Network` (whose
-- hidden channels survive as the tau at index `pair fin (base e)`) be
-- renamed into `Net_Api` via `CSP.Rename`: the injection `Net` into
-- `Net_Api` is total and injective, so the inverse can still recover the
-- hidden events and fire their tau-steps.  The six message/ack channels
-- remain inert plumbing after composition (still hidden); only
-- `input`/`output` (and the client-local `apiKA`/`done`) are observable.
--
-- Each `apiP` fixes `id` to its protocol and carries `Conn N2N_P` with
-- the full `ApiP` value, so every api event is `top`-carried; the
-- channels keep the `(id : IDs) -> Conn id` prefix and `Net`'s carrier.
------------------------------------------------------------------------

data Net_Api (Data : Set) : Set → Set where
  input output sndmsg rcvmsg tx : (id : IDs) → Conn id → Net_Api Data Data
  sndack rcvack ack done        : (id : IDs) → Conn id → Net_Api Data ⊤
  apiCS : (c : Conn N2N_ChainSync)    (m : ApiCSTag) → Net_Api Data (ApiCSCar m)
  apiBF : (c : Conn N2N_BlockFetch)   (m : ApiBFTag) → Net_Api Data (ApiBFCar m)
  apiTS : (c : Conn N2N_TxSubmission) (m : ApiTSTag) → Net_Api Data (ApiTSCar m)
  apiKA : (c : Conn N2N_KeepAlive)    (m : ApiKATag) → Net_Api Data (ApiKACar m)
  apiLN : (c : Conn N2N_LeiosNotify)  (m : ApiLNTag) → Net_Api Data (ApiLNCar m)
  apiLF : (c : Conn N2N_LeiosFetch)   (m : ApiLFTag) → Net_Api Data (ApiLFCar m)

------------------------------------------------------------------------
-- Step 5: decidable equality on `AnyTypes (Net_Api Data)`.
--
-- Channels are identified by `(constructor, id, Conn id)` -- the carried
-- `Data` is negotiated by the value, not part of the identity.  Each
-- `apiP` is identified by its (fixed-type) `Conn N2N_P` and the api
-- sub-constructor tag only; the `ApiP` payload now lives in the carrier
-- value, not the event identity, so there is nothing further to compare.
------------------------------------------------------------------------

Net_Api-≟ : {Data : Set} → (x y : AnyTypes (Net_Api Data)) → Dec (x ≡ y)
Net_Api-≟ {Data} = go
  where
  go : (x y : AnyTypes (Net_Api Data)) → Dec (x ≡ y)
  go (_ , input i₁ c₁) (_ , input i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , output i₁ c₁) (_ , output i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , sndmsg i₁ c₁) (_ , sndmsg i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , rcvmsg i₁ c₁) (_ , rcvmsg i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , tx i₁ c₁) (_ , tx i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , sndack i₁ c₁) (_ , sndack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , rcvack i₁ c₁) (_ , rcvack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , ack i₁ c₁) (_ , ack i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , done i₁ c₁) (_ , done i₂ c₂) with i₁ ≟ i₂
  ... | no ¬p = no λ where refl → ¬p refl
  ... | yes refl with c₁ ≟ c₂
  ...   | yes refl = yes refl
  ...   | no ¬p = no λ where refl → ¬p refl
  go (_ , apiCS c₁ m₁) (_ , apiCS c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiBF c₁ m₁) (_ , apiBF c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiTS c₁ m₁) (_ , apiTS c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiKA c₁ m₁) (_ , apiKA c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLN c₁ m₁) (_ , apiLN c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  go (_ , apiLF c₁ m₁) (_ , apiLF c₂ m₂) with c₁ ≟ c₂ | m₁ ≟ m₂
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl
  -- off-diagonal: distinct constructors are never equal
  go (_ , input _ _) (_ , output _ _) = no λ ()
  go (_ , input _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , input _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , input _ _) (_ , tx _ _) = no λ ()
  go (_ , input _ _) (_ , sndack _ _) = no λ ()
  go (_ , input _ _) (_ , rcvack _ _) = no λ ()
  go (_ , input _ _) (_ , ack _ _) = no λ ()
  go (_ , input _ _) (_ , done _ _) = no λ ()
  go (_ , input _ _) (_ , apiCS _ _) = no λ ()
  go (_ , input _ _) (_ , apiBF _ _) = no λ ()
  go (_ , input _ _) (_ , apiTS _ _) = no λ ()
  go (_ , input _ _) (_ , apiKA _ _) = no λ ()
  go (_ , input _ _) (_ , apiLN _ _) = no λ ()
  go (_ , input _ _) (_ , apiLF _ _) = no λ ()
  go (_ , output _ _) (_ , input _ _) = no λ ()
  go (_ , output _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , output _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , output _ _) (_ , tx _ _) = no λ ()
  go (_ , output _ _) (_ , sndack _ _) = no λ ()
  go (_ , output _ _) (_ , rcvack _ _) = no λ ()
  go (_ , output _ _) (_ , ack _ _) = no λ ()
  go (_ , output _ _) (_ , done _ _) = no λ ()
  go (_ , output _ _) (_ , apiCS _ _) = no λ ()
  go (_ , output _ _) (_ , apiBF _ _) = no λ ()
  go (_ , output _ _) (_ , apiTS _ _) = no λ ()
  go (_ , output _ _) (_ , apiKA _ _) = no λ ()
  go (_ , output _ _) (_ , apiLN _ _) = no λ ()
  go (_ , output _ _) (_ , apiLF _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , input _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , output _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , tx _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , sndack _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , rcvack _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , ack _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , done _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiCS _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiBF _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiTS _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiKA _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiLN _ _) = no λ ()
  go (_ , sndmsg _ _) (_ , apiLF _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , input _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , output _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , tx _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , sndack _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , rcvack _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , ack _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , done _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiCS _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiBF _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiTS _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiKA _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiLN _ _) = no λ ()
  go (_ , rcvmsg _ _) (_ , apiLF _ _) = no λ ()
  go (_ , tx _ _) (_ , input _ _) = no λ ()
  go (_ , tx _ _) (_ , output _ _) = no λ ()
  go (_ , tx _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , tx _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , tx _ _) (_ , sndack _ _) = no λ ()
  go (_ , tx _ _) (_ , rcvack _ _) = no λ ()
  go (_ , tx _ _) (_ , ack _ _) = no λ ()
  go (_ , tx _ _) (_ , done _ _) = no λ ()
  go (_ , tx _ _) (_ , apiCS _ _) = no λ ()
  go (_ , tx _ _) (_ , apiBF _ _) = no λ ()
  go (_ , tx _ _) (_ , apiTS _ _) = no λ ()
  go (_ , tx _ _) (_ , apiKA _ _) = no λ ()
  go (_ , tx _ _) (_ , apiLN _ _) = no λ ()
  go (_ , tx _ _) (_ , apiLF _ _) = no λ ()
  go (_ , sndack _ _) (_ , input _ _) = no λ ()
  go (_ , sndack _ _) (_ , output _ _) = no λ ()
  go (_ , sndack _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , sndack _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , sndack _ _) (_ , tx _ _) = no λ ()
  go (_ , sndack _ _) (_ , rcvack _ _) = no λ ()
  go (_ , sndack _ _) (_ , ack _ _) = no λ ()
  go (_ , sndack _ _) (_ , done _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiCS _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiBF _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiTS _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiKA _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiLN _ _) = no λ ()
  go (_ , sndack _ _) (_ , apiLF _ _) = no λ ()
  go (_ , rcvack _ _) (_ , input _ _) = no λ ()
  go (_ , rcvack _ _) (_ , output _ _) = no λ ()
  go (_ , rcvack _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , rcvack _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , rcvack _ _) (_ , tx _ _) = no λ ()
  go (_ , rcvack _ _) (_ , sndack _ _) = no λ ()
  go (_ , rcvack _ _) (_ , ack _ _) = no λ ()
  go (_ , rcvack _ _) (_ , done _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiCS _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiBF _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiTS _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiKA _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiLN _ _) = no λ ()
  go (_ , rcvack _ _) (_ , apiLF _ _) = no λ ()
  go (_ , ack _ _) (_ , input _ _) = no λ ()
  go (_ , ack _ _) (_ , output _ _) = no λ ()
  go (_ , ack _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , ack _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , ack _ _) (_ , tx _ _) = no λ ()
  go (_ , ack _ _) (_ , sndack _ _) = no λ ()
  go (_ , ack _ _) (_ , rcvack _ _) = no λ ()
  go (_ , ack _ _) (_ , done _ _) = no λ ()
  go (_ , ack _ _) (_ , apiCS _ _) = no λ ()
  go (_ , ack _ _) (_ , apiBF _ _) = no λ ()
  go (_ , ack _ _) (_ , apiTS _ _) = no λ ()
  go (_ , ack _ _) (_ , apiKA _ _) = no λ ()
  go (_ , ack _ _) (_ , apiLN _ _) = no λ ()
  go (_ , ack _ _) (_ , apiLF _ _) = no λ ()
  go (_ , done _ _) (_ , input _ _) = no λ ()
  go (_ , done _ _) (_ , output _ _) = no λ ()
  go (_ , done _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , done _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , done _ _) (_ , tx _ _) = no λ ()
  go (_ , done _ _) (_ , sndack _ _) = no λ ()
  go (_ , done _ _) (_ , rcvack _ _) = no λ ()
  go (_ , done _ _) (_ , ack _ _) = no λ ()
  go (_ , done _ _) (_ , apiCS _ _) = no λ ()
  go (_ , done _ _) (_ , apiBF _ _) = no λ ()
  go (_ , done _ _) (_ , apiTS _ _) = no λ ()
  go (_ , done _ _) (_ , apiKA _ _) = no λ ()
  go (_ , done _ _) (_ , apiLN _ _) = no λ ()
  go (_ , done _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiCS _ _) (_ , input _ _) = no λ ()
  go (_ , apiCS _ _) (_ , output _ _) = no λ ()
  go (_ , apiCS _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiCS _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiCS _ _) (_ , tx _ _) = no λ ()
  go (_ , apiCS _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiCS _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiCS _ _) (_ , ack _ _) = no λ ()
  go (_ , apiCS _ _) (_ , done _ _) = no λ ()
  go (_ , apiCS _ _) (_ , apiBF _ _) = no λ ()
  go (_ , apiCS _ _) (_ , apiTS _ _) = no λ ()
  go (_ , apiCS _ _) (_ , apiKA _ _) = no λ ()
  go (_ , apiCS _ _) (_ , apiLN _ _) = no λ ()
  go (_ , apiCS _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiBF _ _) (_ , input _ _) = no λ ()
  go (_ , apiBF _ _) (_ , output _ _) = no λ ()
  go (_ , apiBF _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiBF _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiBF _ _) (_ , tx _ _) = no λ ()
  go (_ , apiBF _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiBF _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiBF _ _) (_ , ack _ _) = no λ ()
  go (_ , apiBF _ _) (_ , done _ _) = no λ ()
  go (_ , apiBF _ _) (_ , apiCS _ _) = no λ ()
  go (_ , apiBF _ _) (_ , apiTS _ _) = no λ ()
  go (_ , apiBF _ _) (_ , apiKA _ _) = no λ ()
  go (_ , apiBF _ _) (_ , apiLN _ _) = no λ ()
  go (_ , apiBF _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiTS _ _) (_ , input _ _) = no λ ()
  go (_ , apiTS _ _) (_ , output _ _) = no λ ()
  go (_ , apiTS _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiTS _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiTS _ _) (_ , tx _ _) = no λ ()
  go (_ , apiTS _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiTS _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiTS _ _) (_ , ack _ _) = no λ ()
  go (_ , apiTS _ _) (_ , done _ _) = no λ ()
  go (_ , apiTS _ _) (_ , apiCS _ _) = no λ ()
  go (_ , apiTS _ _) (_ , apiBF _ _) = no λ ()
  go (_ , apiTS _ _) (_ , apiKA _ _) = no λ ()
  go (_ , apiTS _ _) (_ , apiLN _ _) = no λ ()
  go (_ , apiTS _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiKA _ _) (_ , input _ _) = no λ ()
  go (_ , apiKA _ _) (_ , output _ _) = no λ ()
  go (_ , apiKA _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiKA _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiKA _ _) (_ , tx _ _) = no λ ()
  go (_ , apiKA _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiKA _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiKA _ _) (_ , ack _ _) = no λ ()
  go (_ , apiKA _ _) (_ , done _ _) = no λ ()
  go (_ , apiKA _ _) (_ , apiCS _ _) = no λ ()
  go (_ , apiKA _ _) (_ , apiBF _ _) = no λ ()
  go (_ , apiKA _ _) (_ , apiTS _ _) = no λ ()
  go (_ , apiKA _ _) (_ , apiLN _ _) = no λ ()
  go (_ , apiKA _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiLN _ _) (_ , input _ _) = no λ ()
  go (_ , apiLN _ _) (_ , output _ _) = no λ ()
  go (_ , apiLN _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiLN _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiLN _ _) (_ , tx _ _) = no λ ()
  go (_ , apiLN _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiLN _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiLN _ _) (_ , ack _ _) = no λ ()
  go (_ , apiLN _ _) (_ , done _ _) = no λ ()
  go (_ , apiLN _ _) (_ , apiCS _ _) = no λ ()
  go (_ , apiLN _ _) (_ , apiBF _ _) = no λ ()
  go (_ , apiLN _ _) (_ , apiTS _ _) = no λ ()
  go (_ , apiLN _ _) (_ , apiKA _ _) = no λ ()
  go (_ , apiLN _ _) (_ , apiLF _ _) = no λ ()
  go (_ , apiLF _ _) (_ , input _ _) = no λ ()
  go (_ , apiLF _ _) (_ , output _ _) = no λ ()
  go (_ , apiLF _ _) (_ , sndmsg _ _) = no λ ()
  go (_ , apiLF _ _) (_ , rcvmsg _ _) = no λ ()
  go (_ , apiLF _ _) (_ , tx _ _) = no λ ()
  go (_ , apiLF _ _) (_ , sndack _ _) = no λ ()
  go (_ , apiLF _ _) (_ , rcvack _ _) = no λ ()
  go (_ , apiLF _ _) (_ , ack _ _) = no λ ()
  go (_ , apiLF _ _) (_ , done _ _) = no λ ()
  go (_ , apiLF _ _) (_ , apiCS _ _) = no λ ()
  go (_ , apiLF _ _) (_ , apiBF _ _) = no λ ()
  go (_ , apiLF _ _) (_ , apiTS _ _) = no λ ()
  go (_ , apiLF _ _) (_ , apiKA _ _) = no λ ()
  go (_ , apiLF _ _) (_ , apiLN _ _) = no λ ()
