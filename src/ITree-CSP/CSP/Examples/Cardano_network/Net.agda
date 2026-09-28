{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the shared network event type `Net`.
--
-- This module is parametrised by `(p : Params)` and `open Params p`,
-- which supplies the abstract data domains (+ their `DecEq` instances)
-- and the link-count assignment `numLinks : ℕ`
-- (instantiated to concrete values by a scenario module). From it we
-- derive the protocol-independent link type `Link = Fin numLinks`,
-- the per-protocol API/handler datatypes `ApiKA … ApiLF`, the shared
-- ⊤-carried network event type `Net : Set → Set`, and its decidable
-- equality `Net-≟` over `AnyTypes Net`.
--
-- Every constructor of `Net` yields `Net ⊤`, so the carried `Set` in an
-- `AnyTypes Net = Σ Set Net` is always `⊤`. Each network data payload is
-- led by `(l : Link) (d : Dir)`, then the protocol `id : IDs`, followed
-- by `Time = ℕ`, `Mode`, `Length = ℕ`, `Messages`; the API folds fix
-- `id` to a single protocol and carry the same `Link`/`Dir` pair.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Fin using (Fin)
open import Data.Unit using (⊤)
open import Data.Maybe using (Maybe)
open import Data.List using (List)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees using (AnyTypes)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.Net (p : Params) where

-- abstract data domains (+ their DecEq) and `numLinks` from the params
open Params p
-- derived structured types + messages (+ their DecEq) over those domains
open import CSP.Examples.Cardano_network.Data p

------------------------------------------------------------------------
-- Step 1: protocol-independent link.
------------------------------------------------------------------------

-- A link (TCP connection) index, shared across all mini-protocols.
Link : Set
Link = Fin numLinks

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
-- The leading `Link`/`Dir` and the tag are supplied by the `Net_Api`
-- constructor `apiP : (l : Link) (d : Dir) (m : ApiPTag) → Net_Api Data (ApiPCar m)`;
-- the carrier `ApiPCar m` is computed from the *value* `m`, so the index
-- is small — no `--large-indices` (which Agda 2.8 deems unsafe). Event
-- identity (and hence `Net_Api-≟`) is `Link`/`Dir` + tag only; the
-- payload lives in the carrier, not the identity. See
-- `docs/superpowers/specs/2026-06-24-carrier-indexed-api-design.md`.
------------------------------------------------------------------------

-- KeepAlive: SendKAMsgKeepAlive.Cookie / SendKAMsgDone /
--            errorCookieMismatchKeepAlive.Cookie.Cookie
data ApiKATag : Set where
  sendKAMsg sendKADone errCookie : ApiKATag
  recvKACookie : ApiKATag   -- server-side api emitted after receiving a keepalive: reports the received cookie

ApiKACar : ApiKATag → Set
ApiKACar sendKAMsg    = Cookie
ApiKACar sendKADone   = ⊤
ApiKACar errCookie    = Cookie × Cookie
ApiKACar recvKACookie = Cookie

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
  -- the REQUESTER peer reports the reply it received off the wire, so the application
  -- can act on it (mirrors BlockFetch's `reqBFRange`)
  recvTSReplyTxIds recvTSReplyTxs : ApiTSTag

ApiTSCar : ApiTSTag → Set
ApiTSCar sendTSReplyTxIds            = List TxHash
ApiTSCar sendTSReplyTxs              = List Tx
ApiTSCar sendTSDone                  = ⊤
ApiTSCar sendTSRequestTxIdsBlocking  = ℕ × ℕ
ApiTSCar sendTSRequestTxIdsPipelined = ℕ × ℕ
ApiTSCar sendTSRequestTxsPipelined   = List TxHash
ApiTSCar recvTSRequestTxIds          = BlockingStyle × ℕ × ℕ
ApiTSCar recvTSRequestTxs            = List TxHash
ApiTSCar recvTSReplyTxIds            = List TxHash
ApiTSCar recvTSReplyTxs              = List Tx

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

-- LeiosFetch: SendLFMsgBlockRequest.Point /
--   SendLFMsgVotesRequest.[Vote] / SendLFMsgBlockRangeRequest.ChainRange /
--   SendLFMsgDone / SendLFMsgBlock.Block /
--   SendLFMsgVoteDelivery.[VoteBlob] / SendLFMsgNextBlockAndTxsInRange.Block.[Tx] /
--   SendLFMsgLastBlockAndTxsInRange.Block.[Tx] / ReceiveLFBlockHandler.Block /
--   ReceiveLFVoteDeliveryHandler.[VoteBlob] /
--   ReceiveLFRangeBlockHandler.Block.[Tx]
-- The tx-closure branch of the July-2026 CIP draft is GONE from this (old) protocol: the
-- prototype's closure lives in `ApiLPTag`'s `lfp…BlockTxs…` family.
-- see ADR 2026-09-21 (leios-tx-closure-and-object-identities) §6
data ApiLFTag : Set where
  sendLFBlockRequest sendLFVotesRequest
    sendLFBlockRangeRequest sendLFDone sendLFBlock
    sendLFVoteDelivery sendLFNextBlockAndTxsInRange sendLFLastBlockAndTxsInRange
    recvLFBlock recvLFVoteDelivery recvLFRangeBlock : ApiLFTag
  -- the PRODUCER peer reports the request it received off the wire, so the application
  -- can serve exactly what was asked for (mirrors BlockFetch's `reqBFRange`)
  reqLFBlockRequest reqLFVotesRequest : ApiLFTag

ApiLFCar : ApiLFTag → Set
ApiLFCar sendLFBlockRequest           = EBHash
ApiLFCar sendLFVotesRequest           = List Vote
ApiLFCar sendLFBlockRangeRequest      = ChainRange
ApiLFCar sendLFDone                   = ⊤
ApiLFCar sendLFBlock                  = EB
ApiLFCar sendLFVoteDelivery           = List VoteBlob
ApiLFCar sendLFNextBlockAndTxsInRange = Block × List Tx
ApiLFCar sendLFLastBlockAndTxsInRange = Block × List Tx
ApiLFCar recvLFBlock                  = EB
ApiLFCar recvLFVoteDelivery           = List VoteBlob
ApiLFCar recvLFRangeBlock             = Block × List Tx
ApiLFCar reqLFBlockRequest            = EBHash
ApiLFCar reqLFVotesRequest            = List Vote

-- the api tags of the leios-prototype peers — BOTH protocols in ONE family, because every
-- exhaustive `Net_Api` dispatch in the live closure costs one wildcard arm per CONSTRUCTOR
-- (110 measured), and two constructors would cost 220 for no modelling gain.  Layout mirrors
-- `ApiLNTag`/`ApiLFTag`: the consumer's `…Send…`, the consumer's `…Recv…`, and — for Fetch —
-- the producer's `…Req…` reports of the request it received off the wire.
-- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
data ApiLPTag : Set where
  lnpSendRequestNext lnpSendDone
    lnpSendBlockAnnouncement lnpSendBlockOffer lnpSendBlockTxsOffer lnpSendVotes
    lnpRecvBlockAnnouncement lnpRecvBlockOffer lnpRecvBlockTxsOffer lnpRecvVotes
    lfpSendBlockRequest lfpSendBlockTxsRequest lfpSendDone
    lfpSendBlock lfpSendBlockTxs lfpRecvBlock lfpRecvBlockTxs
    lfpReqBlockRequest lfpReqBlockTxsRequest : ApiLPTag

-- what each prototype api channel hands over
-- LeiosNotify has three type parameters: point, announcement, vote, seen from LeiosDemoOnlyTestNotify.hs
-- They are instantiated to LeiosPoint, (Header blk), LeiosVote in NodeToNode.hs
ApiLPCar : ApiLPTag → Set
ApiLPCar lnpSendRequestNext       = ⊤
ApiLPCar lnpSendDone              = ⊤
ApiLPCar lnpSendBlockAnnouncement = Header
ApiLPCar lnpSendBlockOffer        = (EBHash × LSlot) × Size
ApiLPCar lnpSendBlockTxsOffer     = EBHash × LSlot
ApiLPCar lnpSendVotes             = List VoteBlob
ApiLPCar lnpRecvBlockAnnouncement = Header
ApiLPCar lnpRecvBlockOffer        = (EBHash × LSlot) × Size
ApiLPCar lnpRecvBlockTxsOffer     = EBHash × LSlot
ApiLPCar lnpRecvVotes             = List VoteBlob
ApiLPCar lfpSendBlockRequest      = EBHash × LSlot
ApiLPCar lfpSendBlockTxsRequest   = (EBHash × LSlot) × TxBitmap
ApiLPCar lfpSendDone              = ⊤
ApiLPCar lfpSendBlock             = EB
ApiLPCar lfpSendBlockTxs          = (EBHash × LSlot) × List (ℕ × Tx)
ApiLPCar lfpRecvBlock             = EB
ApiLPCar lfpRecvBlockTxs          = (EBHash × LSlot) × List (ℕ × Tx)
ApiLPCar lfpReqBlockRequest       = EBHash × LSlot
ApiLPCar lfpReqBlockTxsRequest    = (EBHash × LSlot) × TxBitmap

------------------------------------------------------------------------
-- The two NODE-LOCAL channel families (not mini-protocol apis, not wire
-- channels): a node's block STORE and the ENVIRONMENT that forges blocks.
-- They are their own `Net_Api` constructors rather than a reuse of the
-- mux-internal `tx` channel, which `Network` hides.
------------------------------------------------------------------------

-- the node-local store channels: the two original directions, plus the read-pointer
-- reads and the four Leios stores of the Linear-Leios node logic (design law L)
data StoreTag : Set where
  stPut stGet : StoreTag
  stGetAt     : ℕ → StoreTag        -- the k-th OLDEST held ranking block
  stPutEB     : StoreTag            -- deposit an (EB hash , announcing slot) entry
  stGetEBAt   : ℕ → StoreTag        -- the k-th OLDEST such entry
  stPutBody   : StoreTag            -- deposit an endorser-block body
  stGetBody   : EBHash → StoreTag   -- the body with that hash, offered iff held
  stPutTx     : StoreTag            -- deposit a transaction in the mempool
  stGetTxAt   : ℕ → StoreTag        -- the k-th OLDEST mempool transaction
  stPutVote   : StoreTag            -- deposit a vote blob
  stGetVoteAt : ℕ → StoreTag        -- the k-th OLDEST vote blob
  stCert      : StoreTag            -- the node-local certificate event for a ranking block
  stGetTx     : TxHash → StoreTag   -- the mempool transaction with that hash, offered iff held
  stHasCert   : RbHash → StoreTag   -- offered iff that RB is already certified here

-- what each store channel hands over
StoreCar : StoreTag → Set
StoreCar stPut           = Block
StoreCar stGet           = Block
StoreCar (stGetAt _)     = Block
StoreCar stPutEB         = EBHash × LSlot
StoreCar (stGetEBAt _)   = EBHash × LSlot
StoreCar stPutBody       = EB
StoreCar (stGetBody _)   = EB
StoreCar stPutTx         = Tx
StoreCar (stGetTxAt _)   = Tx
StoreCar stPutVote       = VoteBlob
StoreCar (stGetVoteAt _) = VoteBlob
StoreCar stCert          = RbHash    -- CHANGED from EBHash: a vote names the RB it certifies
StoreCar (stGetTx _)     = Tx
StoreCar (stHasCert _)   = ⊤

-- the environment's channels into a node: the block forge, a transaction submission, and the
-- forge of a CERTIFICATE-carrying ranking block (whose body certifies some earlier RB)
data EnvTag : Set where envForge envSubmit envForgeCert : EnvTag

-- a forge delivers an optional EB forged together with its announcing RB; a submission
-- delivers one transaction; a certificate forge delivers the certificate-carrying RB
EnvCar : EnvTag → Set
EnvCar envForge     = Maybe EB × Block
EnvCar envSubmit    = Tx
EnvCar envForgeCert = Block

------------------------------------------------------------------------
-- DecEq instances for the six finite api tag enums (payload-free) and
-- the two node-local tag enums.
------------------------------------------------------------------------

instance
  DecEq-ApiKATag : DecEq ApiKATag
  DecEq-ApiKATag ._≟_ = go
    where
    go : (x y : ApiKATag) → Dec (x ≡ y)
    go sendKAMsg sendKAMsg = yes refl
    go sendKADone sendKADone = yes refl
    go errCookie errCookie = yes refl
    go recvKACookie recvKACookie = yes refl
    go sendKAMsg sendKADone = no λ ()
    go sendKAMsg errCookie = no λ ()
    go sendKAMsg recvKACookie = no λ ()
    go sendKADone sendKAMsg = no λ ()
    go sendKADone errCookie = no λ ()
    go sendKADone recvKACookie = no λ ()
    go errCookie sendKAMsg = no λ ()
    go errCookie sendKADone = no λ ()
    go errCookie recvKACookie = no λ ()
    go recvKACookie sendKAMsg = no λ ()
    go recvKACookie sendKADone = no λ ()
    go recvKACookie errCookie = no λ ()

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
    go recvTSReplyTxIds recvTSReplyTxIds = yes refl
    go recvTSReplyTxs   recvTSReplyTxs   = yes refl
    go sendTSReplyTxIds recvTSReplyTxIds = no λ ()
    go sendTSReplyTxIds recvTSReplyTxs = no λ ()
    go sendTSReplyTxs recvTSReplyTxIds = no λ ()
    go sendTSReplyTxs recvTSReplyTxs = no λ ()
    go sendTSDone recvTSReplyTxIds = no λ ()
    go sendTSDone recvTSReplyTxs = no λ ()
    go sendTSRequestTxIdsBlocking recvTSReplyTxIds = no λ ()
    go sendTSRequestTxIdsBlocking recvTSReplyTxs = no λ ()
    go sendTSRequestTxIdsPipelined recvTSReplyTxIds = no λ ()
    go sendTSRequestTxIdsPipelined recvTSReplyTxs = no λ ()
    go sendTSRequestTxsPipelined recvTSReplyTxIds = no λ ()
    go sendTSRequestTxsPipelined recvTSReplyTxs = no λ ()
    go recvTSRequestTxIds recvTSReplyTxIds = no λ ()
    go recvTSRequestTxIds recvTSReplyTxs = no λ ()
    go recvTSRequestTxs recvTSReplyTxIds = no λ ()
    go recvTSRequestTxs recvTSReplyTxs = no λ ()
    go recvTSReplyTxIds sendTSReplyTxIds = no λ ()
    go recvTSReplyTxIds sendTSReplyTxs = no λ ()
    go recvTSReplyTxIds sendTSDone = no λ ()
    go recvTSReplyTxIds sendTSRequestTxIdsBlocking = no λ ()
    go recvTSReplyTxIds sendTSRequestTxIdsPipelined = no λ ()
    go recvTSReplyTxIds sendTSRequestTxsPipelined = no λ ()
    go recvTSReplyTxIds recvTSRequestTxIds = no λ ()
    go recvTSReplyTxIds recvTSRequestTxs = no λ ()
    go recvTSReplyTxIds recvTSReplyTxs = no λ ()
    go recvTSReplyTxs sendTSReplyTxIds = no λ ()
    go recvTSReplyTxs sendTSReplyTxs = no λ ()
    go recvTSReplyTxs sendTSDone = no λ ()
    go recvTSReplyTxs sendTSRequestTxIdsBlocking = no λ ()
    go recvTSReplyTxs sendTSRequestTxIdsPipelined = no λ ()
    go recvTSReplyTxs sendTSRequestTxsPipelined = no λ ()
    go recvTSReplyTxs recvTSRequestTxIds = no λ ()
    go recvTSReplyTxs recvTSRequestTxs = no λ ()
    go recvTSReplyTxs recvTSReplyTxIds = no λ ()

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
    go sendLFVotesRequest sendLFVotesRequest = yes refl
    go sendLFBlockRangeRequest sendLFBlockRangeRequest = yes refl
    go sendLFDone sendLFDone = yes refl
    go sendLFBlock sendLFBlock = yes refl
    go sendLFVoteDelivery sendLFVoteDelivery = yes refl
    go sendLFNextBlockAndTxsInRange sendLFNextBlockAndTxsInRange = yes refl
    go sendLFLastBlockAndTxsInRange sendLFLastBlockAndTxsInRange = yes refl
    go recvLFBlock recvLFBlock = yes refl
    go recvLFVoteDelivery recvLFVoteDelivery = yes refl
    go recvLFRangeBlock recvLFRangeBlock = yes refl
    go sendLFBlockRequest sendLFVotesRequest = no λ ()
    go sendLFBlockRequest sendLFBlockRangeRequest = no λ ()
    go sendLFBlockRequest sendLFDone = no λ ()
    go sendLFBlockRequest sendLFBlock = no λ ()
    go sendLFBlockRequest sendLFVoteDelivery = no λ ()
    go sendLFBlockRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockRequest recvLFBlock = no λ ()
    go sendLFBlockRequest recvLFVoteDelivery = no λ ()
    go sendLFBlockRequest recvLFRangeBlock = no λ ()
    go sendLFVotesRequest sendLFBlockRequest = no λ ()
    go sendLFVotesRequest sendLFBlockRangeRequest = no λ ()
    go sendLFVotesRequest sendLFDone = no λ ()
    go sendLFVotesRequest sendLFBlock = no λ ()
    go sendLFVotesRequest sendLFVoteDelivery = no λ ()
    go sendLFVotesRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFVotesRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFVotesRequest recvLFBlock = no λ ()
    go sendLFVotesRequest recvLFVoteDelivery = no λ ()
    go sendLFVotesRequest recvLFRangeBlock = no λ ()
    go sendLFBlockRangeRequest sendLFBlockRequest = no λ ()
    go sendLFBlockRangeRequest sendLFVotesRequest = no λ ()
    go sendLFBlockRangeRequest sendLFDone = no λ ()
    go sendLFBlockRangeRequest sendLFBlock = no λ ()
    go sendLFBlockRangeRequest sendLFVoteDelivery = no λ ()
    go sendLFBlockRangeRequest sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlockRangeRequest sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlockRangeRequest recvLFBlock = no λ ()
    go sendLFBlockRangeRequest recvLFVoteDelivery = no λ ()
    go sendLFBlockRangeRequest recvLFRangeBlock = no λ ()
    go sendLFDone sendLFBlockRequest = no λ ()
    go sendLFDone sendLFVotesRequest = no λ ()
    go sendLFDone sendLFBlockRangeRequest = no λ ()
    go sendLFDone sendLFBlock = no λ ()
    go sendLFDone sendLFVoteDelivery = no λ ()
    go sendLFDone sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFDone sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFDone recvLFBlock = no λ ()
    go sendLFDone recvLFVoteDelivery = no λ ()
    go sendLFDone recvLFRangeBlock = no λ ()
    go sendLFBlock sendLFBlockRequest = no λ ()
    go sendLFBlock sendLFVotesRequest = no λ ()
    go sendLFBlock sendLFBlockRangeRequest = no λ ()
    go sendLFBlock sendLFDone = no λ ()
    go sendLFBlock sendLFVoteDelivery = no λ ()
    go sendLFBlock sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFBlock sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFBlock recvLFBlock = no λ ()
    go sendLFBlock recvLFVoteDelivery = no λ ()
    go sendLFBlock recvLFRangeBlock = no λ ()
    go sendLFVoteDelivery sendLFBlockRequest = no λ ()
    go sendLFVoteDelivery sendLFVotesRequest = no λ ()
    go sendLFVoteDelivery sendLFBlockRangeRequest = no λ ()
    go sendLFVoteDelivery sendLFDone = no λ ()
    go sendLFVoteDelivery sendLFBlock = no λ ()
    go sendLFVoteDelivery sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFVoteDelivery sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFVoteDelivery recvLFBlock = no λ ()
    go sendLFVoteDelivery recvLFVoteDelivery = no λ ()
    go sendLFVoteDelivery recvLFRangeBlock = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFVotesRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlockRangeRequest = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFDone = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFBlock = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFVoteDelivery = no λ ()
    go sendLFNextBlockAndTxsInRange sendLFLastBlockAndTxsInRange = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFBlock = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFVoteDelivery = no λ ()
    go sendLFNextBlockAndTxsInRange recvLFRangeBlock = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFVotesRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlockRangeRequest = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFDone = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFBlock = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFVoteDelivery = no λ ()
    go sendLFLastBlockAndTxsInRange sendLFNextBlockAndTxsInRange = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFBlock = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFVoteDelivery = no λ ()
    go sendLFLastBlockAndTxsInRange recvLFRangeBlock = no λ ()
    go recvLFBlock sendLFBlockRequest = no λ ()
    go recvLFBlock sendLFVotesRequest = no λ ()
    go recvLFBlock sendLFBlockRangeRequest = no λ ()
    go recvLFBlock sendLFDone = no λ ()
    go recvLFBlock sendLFBlock = no λ ()
    go recvLFBlock sendLFVoteDelivery = no λ ()
    go recvLFBlock sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFBlock sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFBlock recvLFVoteDelivery = no λ ()
    go recvLFBlock recvLFRangeBlock = no λ ()
    go recvLFVoteDelivery sendLFBlockRequest = no λ ()
    go recvLFVoteDelivery sendLFVotesRequest = no λ ()
    go recvLFVoteDelivery sendLFBlockRangeRequest = no λ ()
    go recvLFVoteDelivery sendLFDone = no λ ()
    go recvLFVoteDelivery sendLFBlock = no λ ()
    go recvLFVoteDelivery sendLFVoteDelivery = no λ ()
    go recvLFVoteDelivery sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFVoteDelivery sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFVoteDelivery recvLFBlock = no λ ()
    go recvLFVoteDelivery recvLFRangeBlock = no λ ()
    go recvLFRangeBlock sendLFBlockRequest = no λ ()
    go recvLFRangeBlock sendLFVotesRequest = no λ ()
    go recvLFRangeBlock sendLFBlockRangeRequest = no λ ()
    go recvLFRangeBlock sendLFDone = no λ ()
    go recvLFRangeBlock sendLFBlock = no λ ()
    go recvLFRangeBlock sendLFVoteDelivery = no λ ()
    go recvLFRangeBlock sendLFNextBlockAndTxsInRange = no λ ()
    go recvLFRangeBlock sendLFLastBlockAndTxsInRange = no λ ()
    go recvLFRangeBlock recvLFBlock = no λ ()
    go recvLFRangeBlock recvLFVoteDelivery = no λ ()
    go reqLFBlockRequest reqLFBlockRequest = yes refl
    go reqLFVotesRequest reqLFVotesRequest = yes refl
    go sendLFBlockRequest reqLFBlockRequest = no λ ()
    go sendLFBlockRequest reqLFVotesRequest = no λ ()
    go sendLFVotesRequest reqLFBlockRequest = no λ ()
    go sendLFVotesRequest reqLFVotesRequest = no λ ()
    go sendLFBlockRangeRequest reqLFBlockRequest = no λ ()
    go sendLFBlockRangeRequest reqLFVotesRequest = no λ ()
    go sendLFDone reqLFBlockRequest = no λ ()
    go sendLFDone reqLFVotesRequest = no λ ()
    go sendLFBlock reqLFBlockRequest = no λ ()
    go sendLFBlock reqLFVotesRequest = no λ ()
    go sendLFVoteDelivery reqLFBlockRequest = no λ ()
    go sendLFVoteDelivery reqLFVotesRequest = no λ ()
    go sendLFNextBlockAndTxsInRange reqLFBlockRequest = no λ ()
    go sendLFNextBlockAndTxsInRange reqLFVotesRequest = no λ ()
    go sendLFLastBlockAndTxsInRange reqLFBlockRequest = no λ ()
    go sendLFLastBlockAndTxsInRange reqLFVotesRequest = no λ ()
    go recvLFBlock reqLFBlockRequest = no λ ()
    go recvLFBlock reqLFVotesRequest = no λ ()
    go recvLFVoteDelivery reqLFBlockRequest = no λ ()
    go recvLFVoteDelivery reqLFVotesRequest = no λ ()
    go recvLFRangeBlock reqLFBlockRequest = no λ ()
    go recvLFRangeBlock reqLFVotesRequest = no λ ()
    go reqLFBlockRequest sendLFBlockRequest = no λ ()
    go reqLFBlockRequest sendLFVotesRequest = no λ ()
    go reqLFBlockRequest sendLFBlockRangeRequest = no λ ()
    go reqLFBlockRequest sendLFDone = no λ ()
    go reqLFBlockRequest sendLFBlock = no λ ()
    go reqLFBlockRequest sendLFVoteDelivery = no λ ()
    go reqLFBlockRequest sendLFNextBlockAndTxsInRange = no λ ()
    go reqLFBlockRequest sendLFLastBlockAndTxsInRange = no λ ()
    go reqLFBlockRequest recvLFBlock = no λ ()
    go reqLFBlockRequest recvLFVoteDelivery = no λ ()
    go reqLFBlockRequest recvLFRangeBlock = no λ ()
    go reqLFBlockRequest reqLFVotesRequest = no λ ()
    go reqLFVotesRequest sendLFBlockRequest = no λ ()
    go reqLFVotesRequest sendLFVotesRequest = no λ ()
    go reqLFVotesRequest sendLFBlockRangeRequest = no λ ()
    go reqLFVotesRequest sendLFDone = no λ ()
    go reqLFVotesRequest sendLFBlock = no λ ()
    go reqLFVotesRequest sendLFVoteDelivery = no λ ()
    go reqLFVotesRequest sendLFNextBlockAndTxsInRange = no λ ()
    go reqLFVotesRequest sendLFLastBlockAndTxsInRange = no λ ()
    go reqLFVotesRequest recvLFBlock = no λ ()
    go reqLFVotesRequest recvLFVoteDelivery = no λ ()
    go reqLFVotesRequest recvLFRangeBlock = no λ ()
    go reqLFVotesRequest reqLFBlockRequest = no λ ()

  -- the nineteen prototype api channels are distinguishable
  DecEq-ApiLPTag : DecEq ApiLPTag
  DecEq-ApiLPTag ._≟_ = go
    where
    go : (x y : ApiLPTag) → Dec (x ≡ y)
    go lnpSendRequestNext lnpSendRequestNext = yes refl
    go lnpSendDone lnpSendDone = yes refl
    go lnpSendBlockAnnouncement lnpSendBlockAnnouncement = yes refl
    go lnpSendBlockOffer lnpSendBlockOffer = yes refl
    go lnpSendBlockTxsOffer lnpSendBlockTxsOffer = yes refl
    go lnpSendVotes lnpSendVotes = yes refl
    go lnpRecvBlockAnnouncement lnpRecvBlockAnnouncement = yes refl
    go lnpRecvBlockOffer lnpRecvBlockOffer = yes refl
    go lnpRecvBlockTxsOffer lnpRecvBlockTxsOffer = yes refl
    go lnpRecvVotes lnpRecvVotes = yes refl
    go lfpSendBlockRequest lfpSendBlockRequest = yes refl
    go lfpSendBlockTxsRequest lfpSendBlockTxsRequest = yes refl
    go lfpSendDone lfpSendDone = yes refl
    go lfpSendBlock lfpSendBlock = yes refl
    go lfpSendBlockTxs lfpSendBlockTxs = yes refl
    go lfpRecvBlock lfpRecvBlock = yes refl
    go lfpRecvBlockTxs lfpRecvBlockTxs = yes refl
    go lfpReqBlockRequest lfpReqBlockRequest = yes refl
    go lfpReqBlockTxsRequest lfpReqBlockTxsRequest = yes refl
    go lnpSendRequestNext lnpSendDone = no λ ()
    go lnpSendRequestNext lnpSendBlockAnnouncement = no λ ()
    go lnpSendRequestNext lnpSendBlockOffer = no λ ()
    go lnpSendRequestNext lnpSendBlockTxsOffer = no λ ()
    go lnpSendRequestNext lnpSendVotes = no λ ()
    go lnpSendRequestNext lnpRecvBlockAnnouncement = no λ ()
    go lnpSendRequestNext lnpRecvBlockOffer = no λ ()
    go lnpSendRequestNext lnpRecvBlockTxsOffer = no λ ()
    go lnpSendRequestNext lnpRecvVotes = no λ ()
    go lnpSendRequestNext lfpSendBlockRequest = no λ ()
    go lnpSendRequestNext lfpSendBlockTxsRequest = no λ ()
    go lnpSendRequestNext lfpSendDone = no λ ()
    go lnpSendRequestNext lfpSendBlock = no λ ()
    go lnpSendRequestNext lfpSendBlockTxs = no λ ()
    go lnpSendRequestNext lfpRecvBlock = no λ ()
    go lnpSendRequestNext lfpRecvBlockTxs = no λ ()
    go lnpSendRequestNext lfpReqBlockRequest = no λ ()
    go lnpSendRequestNext lfpReqBlockTxsRequest = no λ ()
    go lnpSendDone lnpSendRequestNext = no λ ()
    go lnpSendDone lnpSendBlockAnnouncement = no λ ()
    go lnpSendDone lnpSendBlockOffer = no λ ()
    go lnpSendDone lnpSendBlockTxsOffer = no λ ()
    go lnpSendDone lnpSendVotes = no λ ()
    go lnpSendDone lnpRecvBlockAnnouncement = no λ ()
    go lnpSendDone lnpRecvBlockOffer = no λ ()
    go lnpSendDone lnpRecvBlockTxsOffer = no λ ()
    go lnpSendDone lnpRecvVotes = no λ ()
    go lnpSendDone lfpSendBlockRequest = no λ ()
    go lnpSendDone lfpSendBlockTxsRequest = no λ ()
    go lnpSendDone lfpSendDone = no λ ()
    go lnpSendDone lfpSendBlock = no λ ()
    go lnpSendDone lfpSendBlockTxs = no λ ()
    go lnpSendDone lfpRecvBlock = no λ ()
    go lnpSendDone lfpRecvBlockTxs = no λ ()
    go lnpSendDone lfpReqBlockRequest = no λ ()
    go lnpSendDone lfpReqBlockTxsRequest = no λ ()
    go lnpSendBlockAnnouncement lnpSendRequestNext = no λ ()
    go lnpSendBlockAnnouncement lnpSendDone = no λ ()
    go lnpSendBlockAnnouncement lnpSendBlockOffer = no λ ()
    go lnpSendBlockAnnouncement lnpSendBlockTxsOffer = no λ ()
    go lnpSendBlockAnnouncement lnpSendVotes = no λ ()
    go lnpSendBlockAnnouncement lnpRecvBlockAnnouncement = no λ ()
    go lnpSendBlockAnnouncement lnpRecvBlockOffer = no λ ()
    go lnpSendBlockAnnouncement lnpRecvBlockTxsOffer = no λ ()
    go lnpSendBlockAnnouncement lnpRecvVotes = no λ ()
    go lnpSendBlockAnnouncement lfpSendBlockRequest = no λ ()
    go lnpSendBlockAnnouncement lfpSendBlockTxsRequest = no λ ()
    go lnpSendBlockAnnouncement lfpSendDone = no λ ()
    go lnpSendBlockAnnouncement lfpSendBlock = no λ ()
    go lnpSendBlockAnnouncement lfpSendBlockTxs = no λ ()
    go lnpSendBlockAnnouncement lfpRecvBlock = no λ ()
    go lnpSendBlockAnnouncement lfpRecvBlockTxs = no λ ()
    go lnpSendBlockAnnouncement lfpReqBlockRequest = no λ ()
    go lnpSendBlockAnnouncement lfpReqBlockTxsRequest = no λ ()
    go lnpSendBlockOffer lnpSendRequestNext = no λ ()
    go lnpSendBlockOffer lnpSendDone = no λ ()
    go lnpSendBlockOffer lnpSendBlockAnnouncement = no λ ()
    go lnpSendBlockOffer lnpSendBlockTxsOffer = no λ ()
    go lnpSendBlockOffer lnpSendVotes = no λ ()
    go lnpSendBlockOffer lnpRecvBlockAnnouncement = no λ ()
    go lnpSendBlockOffer lnpRecvBlockOffer = no λ ()
    go lnpSendBlockOffer lnpRecvBlockTxsOffer = no λ ()
    go lnpSendBlockOffer lnpRecvVotes = no λ ()
    go lnpSendBlockOffer lfpSendBlockRequest = no λ ()
    go lnpSendBlockOffer lfpSendBlockTxsRequest = no λ ()
    go lnpSendBlockOffer lfpSendDone = no λ ()
    go lnpSendBlockOffer lfpSendBlock = no λ ()
    go lnpSendBlockOffer lfpSendBlockTxs = no λ ()
    go lnpSendBlockOffer lfpRecvBlock = no λ ()
    go lnpSendBlockOffer lfpRecvBlockTxs = no λ ()
    go lnpSendBlockOffer lfpReqBlockRequest = no λ ()
    go lnpSendBlockOffer lfpReqBlockTxsRequest = no λ ()
    go lnpSendBlockTxsOffer lnpSendRequestNext = no λ ()
    go lnpSendBlockTxsOffer lnpSendDone = no λ ()
    go lnpSendBlockTxsOffer lnpSendBlockAnnouncement = no λ ()
    go lnpSendBlockTxsOffer lnpSendBlockOffer = no λ ()
    go lnpSendBlockTxsOffer lnpSendVotes = no λ ()
    go lnpSendBlockTxsOffer lnpRecvBlockAnnouncement = no λ ()
    go lnpSendBlockTxsOffer lnpRecvBlockOffer = no λ ()
    go lnpSendBlockTxsOffer lnpRecvBlockTxsOffer = no λ ()
    go lnpSendBlockTxsOffer lnpRecvVotes = no λ ()
    go lnpSendBlockTxsOffer lfpSendBlockRequest = no λ ()
    go lnpSendBlockTxsOffer lfpSendBlockTxsRequest = no λ ()
    go lnpSendBlockTxsOffer lfpSendDone = no λ ()
    go lnpSendBlockTxsOffer lfpSendBlock = no λ ()
    go lnpSendBlockTxsOffer lfpSendBlockTxs = no λ ()
    go lnpSendBlockTxsOffer lfpRecvBlock = no λ ()
    go lnpSendBlockTxsOffer lfpRecvBlockTxs = no λ ()
    go lnpSendBlockTxsOffer lfpReqBlockRequest = no λ ()
    go lnpSendBlockTxsOffer lfpReqBlockTxsRequest = no λ ()
    go lnpSendVotes lnpSendRequestNext = no λ ()
    go lnpSendVotes lnpSendDone = no λ ()
    go lnpSendVotes lnpSendBlockAnnouncement = no λ ()
    go lnpSendVotes lnpSendBlockOffer = no λ ()
    go lnpSendVotes lnpSendBlockTxsOffer = no λ ()
    go lnpSendVotes lnpRecvBlockAnnouncement = no λ ()
    go lnpSendVotes lnpRecvBlockOffer = no λ ()
    go lnpSendVotes lnpRecvBlockTxsOffer = no λ ()
    go lnpSendVotes lnpRecvVotes = no λ ()
    go lnpSendVotes lfpSendBlockRequest = no λ ()
    go lnpSendVotes lfpSendBlockTxsRequest = no λ ()
    go lnpSendVotes lfpSendDone = no λ ()
    go lnpSendVotes lfpSendBlock = no λ ()
    go lnpSendVotes lfpSendBlockTxs = no λ ()
    go lnpSendVotes lfpRecvBlock = no λ ()
    go lnpSendVotes lfpRecvBlockTxs = no λ ()
    go lnpSendVotes lfpReqBlockRequest = no λ ()
    go lnpSendVotes lfpReqBlockTxsRequest = no λ ()
    go lnpRecvBlockAnnouncement lnpSendRequestNext = no λ ()
    go lnpRecvBlockAnnouncement lnpSendDone = no λ ()
    go lnpRecvBlockAnnouncement lnpSendBlockAnnouncement = no λ ()
    go lnpRecvBlockAnnouncement lnpSendBlockOffer = no λ ()
    go lnpRecvBlockAnnouncement lnpSendBlockTxsOffer = no λ ()
    go lnpRecvBlockAnnouncement lnpSendVotes = no λ ()
    go lnpRecvBlockAnnouncement lnpRecvBlockOffer = no λ ()
    go lnpRecvBlockAnnouncement lnpRecvBlockTxsOffer = no λ ()
    go lnpRecvBlockAnnouncement lnpRecvVotes = no λ ()
    go lnpRecvBlockAnnouncement lfpSendBlockRequest = no λ ()
    go lnpRecvBlockAnnouncement lfpSendBlockTxsRequest = no λ ()
    go lnpRecvBlockAnnouncement lfpSendDone = no λ ()
    go lnpRecvBlockAnnouncement lfpSendBlock = no λ ()
    go lnpRecvBlockAnnouncement lfpSendBlockTxs = no λ ()
    go lnpRecvBlockAnnouncement lfpRecvBlock = no λ ()
    go lnpRecvBlockAnnouncement lfpRecvBlockTxs = no λ ()
    go lnpRecvBlockAnnouncement lfpReqBlockRequest = no λ ()
    go lnpRecvBlockAnnouncement lfpReqBlockTxsRequest = no λ ()
    go lnpRecvBlockOffer lnpSendRequestNext = no λ ()
    go lnpRecvBlockOffer lnpSendDone = no λ ()
    go lnpRecvBlockOffer lnpSendBlockAnnouncement = no λ ()
    go lnpRecvBlockOffer lnpSendBlockOffer = no λ ()
    go lnpRecvBlockOffer lnpSendBlockTxsOffer = no λ ()
    go lnpRecvBlockOffer lnpSendVotes = no λ ()
    go lnpRecvBlockOffer lnpRecvBlockAnnouncement = no λ ()
    go lnpRecvBlockOffer lnpRecvBlockTxsOffer = no λ ()
    go lnpRecvBlockOffer lnpRecvVotes = no λ ()
    go lnpRecvBlockOffer lfpSendBlockRequest = no λ ()
    go lnpRecvBlockOffer lfpSendBlockTxsRequest = no λ ()
    go lnpRecvBlockOffer lfpSendDone = no λ ()
    go lnpRecvBlockOffer lfpSendBlock = no λ ()
    go lnpRecvBlockOffer lfpSendBlockTxs = no λ ()
    go lnpRecvBlockOffer lfpRecvBlock = no λ ()
    go lnpRecvBlockOffer lfpRecvBlockTxs = no λ ()
    go lnpRecvBlockOffer lfpReqBlockRequest = no λ ()
    go lnpRecvBlockOffer lfpReqBlockTxsRequest = no λ ()
    go lnpRecvBlockTxsOffer lnpSendRequestNext = no λ ()
    go lnpRecvBlockTxsOffer lnpSendDone = no λ ()
    go lnpRecvBlockTxsOffer lnpSendBlockAnnouncement = no λ ()
    go lnpRecvBlockTxsOffer lnpSendBlockOffer = no λ ()
    go lnpRecvBlockTxsOffer lnpSendBlockTxsOffer = no λ ()
    go lnpRecvBlockTxsOffer lnpSendVotes = no λ ()
    go lnpRecvBlockTxsOffer lnpRecvBlockAnnouncement = no λ ()
    go lnpRecvBlockTxsOffer lnpRecvBlockOffer = no λ ()
    go lnpRecvBlockTxsOffer lnpRecvVotes = no λ ()
    go lnpRecvBlockTxsOffer lfpSendBlockRequest = no λ ()
    go lnpRecvBlockTxsOffer lfpSendBlockTxsRequest = no λ ()
    go lnpRecvBlockTxsOffer lfpSendDone = no λ ()
    go lnpRecvBlockTxsOffer lfpSendBlock = no λ ()
    go lnpRecvBlockTxsOffer lfpSendBlockTxs = no λ ()
    go lnpRecvBlockTxsOffer lfpRecvBlock = no λ ()
    go lnpRecvBlockTxsOffer lfpRecvBlockTxs = no λ ()
    go lnpRecvBlockTxsOffer lfpReqBlockRequest = no λ ()
    go lnpRecvBlockTxsOffer lfpReqBlockTxsRequest = no λ ()
    go lnpRecvVotes lnpSendRequestNext = no λ ()
    go lnpRecvVotes lnpSendDone = no λ ()
    go lnpRecvVotes lnpSendBlockAnnouncement = no λ ()
    go lnpRecvVotes lnpSendBlockOffer = no λ ()
    go lnpRecvVotes lnpSendBlockTxsOffer = no λ ()
    go lnpRecvVotes lnpSendVotes = no λ ()
    go lnpRecvVotes lnpRecvBlockAnnouncement = no λ ()
    go lnpRecvVotes lnpRecvBlockOffer = no λ ()
    go lnpRecvVotes lnpRecvBlockTxsOffer = no λ ()
    go lnpRecvVotes lfpSendBlockRequest = no λ ()
    go lnpRecvVotes lfpSendBlockTxsRequest = no λ ()
    go lnpRecvVotes lfpSendDone = no λ ()
    go lnpRecvVotes lfpSendBlock = no λ ()
    go lnpRecvVotes lfpSendBlockTxs = no λ ()
    go lnpRecvVotes lfpRecvBlock = no λ ()
    go lnpRecvVotes lfpRecvBlockTxs = no λ ()
    go lnpRecvVotes lfpReqBlockRequest = no λ ()
    go lnpRecvVotes lfpReqBlockTxsRequest = no λ ()
    go lfpSendBlockRequest lnpSendRequestNext = no λ ()
    go lfpSendBlockRequest lnpSendDone = no λ ()
    go lfpSendBlockRequest lnpSendBlockAnnouncement = no λ ()
    go lfpSendBlockRequest lnpSendBlockOffer = no λ ()
    go lfpSendBlockRequest lnpSendBlockTxsOffer = no λ ()
    go lfpSendBlockRequest lnpSendVotes = no λ ()
    go lfpSendBlockRequest lnpRecvBlockAnnouncement = no λ ()
    go lfpSendBlockRequest lnpRecvBlockOffer = no λ ()
    go lfpSendBlockRequest lnpRecvBlockTxsOffer = no λ ()
    go lfpSendBlockRequest lnpRecvVotes = no λ ()
    go lfpSendBlockRequest lfpSendBlockTxsRequest = no λ ()
    go lfpSendBlockRequest lfpSendDone = no λ ()
    go lfpSendBlockRequest lfpSendBlock = no λ ()
    go lfpSendBlockRequest lfpSendBlockTxs = no λ ()
    go lfpSendBlockRequest lfpRecvBlock = no λ ()
    go lfpSendBlockRequest lfpRecvBlockTxs = no λ ()
    go lfpSendBlockRequest lfpReqBlockRequest = no λ ()
    go lfpSendBlockRequest lfpReqBlockTxsRequest = no λ ()
    go lfpSendBlockTxsRequest lnpSendRequestNext = no λ ()
    go lfpSendBlockTxsRequest lnpSendDone = no λ ()
    go lfpSendBlockTxsRequest lnpSendBlockAnnouncement = no λ ()
    go lfpSendBlockTxsRequest lnpSendBlockOffer = no λ ()
    go lfpSendBlockTxsRequest lnpSendBlockTxsOffer = no λ ()
    go lfpSendBlockTxsRequest lnpSendVotes = no λ ()
    go lfpSendBlockTxsRequest lnpRecvBlockAnnouncement = no λ ()
    go lfpSendBlockTxsRequest lnpRecvBlockOffer = no λ ()
    go lfpSendBlockTxsRequest lnpRecvBlockTxsOffer = no λ ()
    go lfpSendBlockTxsRequest lnpRecvVotes = no λ ()
    go lfpSendBlockTxsRequest lfpSendBlockRequest = no λ ()
    go lfpSendBlockTxsRequest lfpSendDone = no λ ()
    go lfpSendBlockTxsRequest lfpSendBlock = no λ ()
    go lfpSendBlockTxsRequest lfpSendBlockTxs = no λ ()
    go lfpSendBlockTxsRequest lfpRecvBlock = no λ ()
    go lfpSendBlockTxsRequest lfpRecvBlockTxs = no λ ()
    go lfpSendBlockTxsRequest lfpReqBlockRequest = no λ ()
    go lfpSendBlockTxsRequest lfpReqBlockTxsRequest = no λ ()
    go lfpSendDone lnpSendRequestNext = no λ ()
    go lfpSendDone lnpSendDone = no λ ()
    go lfpSendDone lnpSendBlockAnnouncement = no λ ()
    go lfpSendDone lnpSendBlockOffer = no λ ()
    go lfpSendDone lnpSendBlockTxsOffer = no λ ()
    go lfpSendDone lnpSendVotes = no λ ()
    go lfpSendDone lnpRecvBlockAnnouncement = no λ ()
    go lfpSendDone lnpRecvBlockOffer = no λ ()
    go lfpSendDone lnpRecvBlockTxsOffer = no λ ()
    go lfpSendDone lnpRecvVotes = no λ ()
    go lfpSendDone lfpSendBlockRequest = no λ ()
    go lfpSendDone lfpSendBlockTxsRequest = no λ ()
    go lfpSendDone lfpSendBlock = no λ ()
    go lfpSendDone lfpSendBlockTxs = no λ ()
    go lfpSendDone lfpRecvBlock = no λ ()
    go lfpSendDone lfpRecvBlockTxs = no λ ()
    go lfpSendDone lfpReqBlockRequest = no λ ()
    go lfpSendDone lfpReqBlockTxsRequest = no λ ()
    go lfpSendBlock lnpSendRequestNext = no λ ()
    go lfpSendBlock lnpSendDone = no λ ()
    go lfpSendBlock lnpSendBlockAnnouncement = no λ ()
    go lfpSendBlock lnpSendBlockOffer = no λ ()
    go lfpSendBlock lnpSendBlockTxsOffer = no λ ()
    go lfpSendBlock lnpSendVotes = no λ ()
    go lfpSendBlock lnpRecvBlockAnnouncement = no λ ()
    go lfpSendBlock lnpRecvBlockOffer = no λ ()
    go lfpSendBlock lnpRecvBlockTxsOffer = no λ ()
    go lfpSendBlock lnpRecvVotes = no λ ()
    go lfpSendBlock lfpSendBlockRequest = no λ ()
    go lfpSendBlock lfpSendBlockTxsRequest = no λ ()
    go lfpSendBlock lfpSendDone = no λ ()
    go lfpSendBlock lfpSendBlockTxs = no λ ()
    go lfpSendBlock lfpRecvBlock = no λ ()
    go lfpSendBlock lfpRecvBlockTxs = no λ ()
    go lfpSendBlock lfpReqBlockRequest = no λ ()
    go lfpSendBlock lfpReqBlockTxsRequest = no λ ()
    go lfpSendBlockTxs lnpSendRequestNext = no λ ()
    go lfpSendBlockTxs lnpSendDone = no λ ()
    go lfpSendBlockTxs lnpSendBlockAnnouncement = no λ ()
    go lfpSendBlockTxs lnpSendBlockOffer = no λ ()
    go lfpSendBlockTxs lnpSendBlockTxsOffer = no λ ()
    go lfpSendBlockTxs lnpSendVotes = no λ ()
    go lfpSendBlockTxs lnpRecvBlockAnnouncement = no λ ()
    go lfpSendBlockTxs lnpRecvBlockOffer = no λ ()
    go lfpSendBlockTxs lnpRecvBlockTxsOffer = no λ ()
    go lfpSendBlockTxs lnpRecvVotes = no λ ()
    go lfpSendBlockTxs lfpSendBlockRequest = no λ ()
    go lfpSendBlockTxs lfpSendBlockTxsRequest = no λ ()
    go lfpSendBlockTxs lfpSendDone = no λ ()
    go lfpSendBlockTxs lfpSendBlock = no λ ()
    go lfpSendBlockTxs lfpRecvBlock = no λ ()
    go lfpSendBlockTxs lfpRecvBlockTxs = no λ ()
    go lfpSendBlockTxs lfpReqBlockRequest = no λ ()
    go lfpSendBlockTxs lfpReqBlockTxsRequest = no λ ()
    go lfpRecvBlock lnpSendRequestNext = no λ ()
    go lfpRecvBlock lnpSendDone = no λ ()
    go lfpRecvBlock lnpSendBlockAnnouncement = no λ ()
    go lfpRecvBlock lnpSendBlockOffer = no λ ()
    go lfpRecvBlock lnpSendBlockTxsOffer = no λ ()
    go lfpRecvBlock lnpSendVotes = no λ ()
    go lfpRecvBlock lnpRecvBlockAnnouncement = no λ ()
    go lfpRecvBlock lnpRecvBlockOffer = no λ ()
    go lfpRecvBlock lnpRecvBlockTxsOffer = no λ ()
    go lfpRecvBlock lnpRecvVotes = no λ ()
    go lfpRecvBlock lfpSendBlockRequest = no λ ()
    go lfpRecvBlock lfpSendBlockTxsRequest = no λ ()
    go lfpRecvBlock lfpSendDone = no λ ()
    go lfpRecvBlock lfpSendBlock = no λ ()
    go lfpRecvBlock lfpSendBlockTxs = no λ ()
    go lfpRecvBlock lfpRecvBlockTxs = no λ ()
    go lfpRecvBlock lfpReqBlockRequest = no λ ()
    go lfpRecvBlock lfpReqBlockTxsRequest = no λ ()
    go lfpRecvBlockTxs lnpSendRequestNext = no λ ()
    go lfpRecvBlockTxs lnpSendDone = no λ ()
    go lfpRecvBlockTxs lnpSendBlockAnnouncement = no λ ()
    go lfpRecvBlockTxs lnpSendBlockOffer = no λ ()
    go lfpRecvBlockTxs lnpSendBlockTxsOffer = no λ ()
    go lfpRecvBlockTxs lnpSendVotes = no λ ()
    go lfpRecvBlockTxs lnpRecvBlockAnnouncement = no λ ()
    go lfpRecvBlockTxs lnpRecvBlockOffer = no λ ()
    go lfpRecvBlockTxs lnpRecvBlockTxsOffer = no λ ()
    go lfpRecvBlockTxs lnpRecvVotes = no λ ()
    go lfpRecvBlockTxs lfpSendBlockRequest = no λ ()
    go lfpRecvBlockTxs lfpSendBlockTxsRequest = no λ ()
    go lfpRecvBlockTxs lfpSendDone = no λ ()
    go lfpRecvBlockTxs lfpSendBlock = no λ ()
    go lfpRecvBlockTxs lfpSendBlockTxs = no λ ()
    go lfpRecvBlockTxs lfpRecvBlock = no λ ()
    go lfpRecvBlockTxs lfpReqBlockRequest = no λ ()
    go lfpRecvBlockTxs lfpReqBlockTxsRequest = no λ ()
    go lfpReqBlockRequest lnpSendRequestNext = no λ ()
    go lfpReqBlockRequest lnpSendDone = no λ ()
    go lfpReqBlockRequest lnpSendBlockAnnouncement = no λ ()
    go lfpReqBlockRequest lnpSendBlockOffer = no λ ()
    go lfpReqBlockRequest lnpSendBlockTxsOffer = no λ ()
    go lfpReqBlockRequest lnpSendVotes = no λ ()
    go lfpReqBlockRequest lnpRecvBlockAnnouncement = no λ ()
    go lfpReqBlockRequest lnpRecvBlockOffer = no λ ()
    go lfpReqBlockRequest lnpRecvBlockTxsOffer = no λ ()
    go lfpReqBlockRequest lnpRecvVotes = no λ ()
    go lfpReqBlockRequest lfpSendBlockRequest = no λ ()
    go lfpReqBlockRequest lfpSendBlockTxsRequest = no λ ()
    go lfpReqBlockRequest lfpSendDone = no λ ()
    go lfpReqBlockRequest lfpSendBlock = no λ ()
    go lfpReqBlockRequest lfpSendBlockTxs = no λ ()
    go lfpReqBlockRequest lfpRecvBlock = no λ ()
    go lfpReqBlockRequest lfpRecvBlockTxs = no λ ()
    go lfpReqBlockRequest lfpReqBlockTxsRequest = no λ ()
    go lfpReqBlockTxsRequest lnpSendRequestNext = no λ ()
    go lfpReqBlockTxsRequest lnpSendDone = no λ ()
    go lfpReqBlockTxsRequest lnpSendBlockAnnouncement = no λ ()
    go lfpReqBlockTxsRequest lnpSendBlockOffer = no λ ()
    go lfpReqBlockTxsRequest lnpSendBlockTxsOffer = no λ ()
    go lfpReqBlockTxsRequest lnpSendVotes = no λ ()
    go lfpReqBlockTxsRequest lnpRecvBlockAnnouncement = no λ ()
    go lfpReqBlockTxsRequest lnpRecvBlockOffer = no λ ()
    go lfpReqBlockTxsRequest lnpRecvBlockTxsOffer = no λ ()
    go lfpReqBlockTxsRequest lnpRecvVotes = no λ ()
    go lfpReqBlockTxsRequest lfpSendBlockRequest = no λ ()
    go lfpReqBlockTxsRequest lfpSendBlockTxsRequest = no λ ()
    go lfpReqBlockTxsRequest lfpSendDone = no λ ()
    go lfpReqBlockTxsRequest lfpSendBlock = no λ ()
    go lfpReqBlockTxsRequest lfpSendBlockTxs = no λ ()
    go lfpReqBlockTxsRequest lfpRecvBlock = no λ ()
    go lfpReqBlockTxsRequest lfpRecvBlockTxs = no λ ()
    go lfpReqBlockTxsRequest lfpReqBlockRequest = no λ ()

  -- the twelve store channels are distinguishable; the four indexed families compare
  -- their index, `stGetBody` its hash
  DecEq-StoreTag : DecEq StoreTag
  DecEq-StoreTag ._≟_ = go
    where
    go : (x y : StoreTag) → Dec (x ≡ y)
    go stPut stPut = yes refl
    go stGet stGet = yes refl
    go (stGetAt j) (stGetAt k) with j Nat.≟ k
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stPutEB stPutEB = yes refl
    go (stGetEBAt j) (stGetEBAt k) with j Nat.≟ k
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stPutBody stPutBody = yes refl
    go (stGetBody h) (stGetBody h′) with h ≟ h′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stPutTx stPutTx = yes refl
    go (stGetTxAt j) (stGetTxAt k) with j Nat.≟ k
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stPutVote stPutVote = yes refl
    go (stGetVoteAt j) (stGetVoteAt k) with j Nat.≟ k
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stCert stCert = yes refl
    go (stGetTx h) (stGetTx h′) with h ≟ h′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go (stHasCert r) (stHasCert r′) with r ≟ r′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ { refl → ¬p refl }
    go stPut stGet = no λ ()
    go stPut (stGetAt _) = no λ ()
    go stPut stPutEB = no λ ()
    go stPut (stGetEBAt _) = no λ ()
    go stPut stPutBody = no λ ()
    go stPut (stGetBody _) = no λ ()
    go stPut stPutTx = no λ ()
    go stPut (stGetTxAt _) = no λ ()
    go stPut stPutVote = no λ ()
    go stPut (stGetVoteAt _) = no λ ()
    go stPut stCert = no λ ()
    go stGet stPut = no λ ()
    go stGet (stGetAt _) = no λ ()
    go stGet stPutEB = no λ ()
    go stGet (stGetEBAt _) = no λ ()
    go stGet stPutBody = no λ ()
    go stGet (stGetBody _) = no λ ()
    go stGet stPutTx = no λ ()
    go stGet (stGetTxAt _) = no λ ()
    go stGet stPutVote = no λ ()
    go stGet (stGetVoteAt _) = no λ ()
    go stGet stCert = no λ ()
    go (stGetAt _) stPut = no λ ()
    go (stGetAt _) stGet = no λ ()
    go (stGetAt _) stPutEB = no λ ()
    go (stGetAt _) (stGetEBAt _) = no λ ()
    go (stGetAt _) stPutBody = no λ ()
    go (stGetAt _) (stGetBody _) = no λ ()
    go (stGetAt _) stPutTx = no λ ()
    go (stGetAt _) (stGetTxAt _) = no λ ()
    go (stGetAt _) stPutVote = no λ ()
    go (stGetAt _) (stGetVoteAt _) = no λ ()
    go (stGetAt _) stCert = no λ ()
    go stPutEB stPut = no λ ()
    go stPutEB stGet = no λ ()
    go stPutEB (stGetAt _) = no λ ()
    go stPutEB (stGetEBAt _) = no λ ()
    go stPutEB stPutBody = no λ ()
    go stPutEB (stGetBody _) = no λ ()
    go stPutEB stPutTx = no λ ()
    go stPutEB (stGetTxAt _) = no λ ()
    go stPutEB stPutVote = no λ ()
    go stPutEB (stGetVoteAt _) = no λ ()
    go stPutEB stCert = no λ ()
    go (stGetEBAt _) stPut = no λ ()
    go (stGetEBAt _) stGet = no λ ()
    go (stGetEBAt _) (stGetAt _) = no λ ()
    go (stGetEBAt _) stPutEB = no λ ()
    go (stGetEBAt _) stPutBody = no λ ()
    go (stGetEBAt _) (stGetBody _) = no λ ()
    go (stGetEBAt _) stPutTx = no λ ()
    go (stGetEBAt _) (stGetTxAt _) = no λ ()
    go (stGetEBAt _) stPutVote = no λ ()
    go (stGetEBAt _) (stGetVoteAt _) = no λ ()
    go (stGetEBAt _) stCert = no λ ()
    go stPutBody stPut = no λ ()
    go stPutBody stGet = no λ ()
    go stPutBody (stGetAt _) = no λ ()
    go stPutBody stPutEB = no λ ()
    go stPutBody (stGetEBAt _) = no λ ()
    go stPutBody (stGetBody _) = no λ ()
    go stPutBody stPutTx = no λ ()
    go stPutBody (stGetTxAt _) = no λ ()
    go stPutBody stPutVote = no λ ()
    go stPutBody (stGetVoteAt _) = no λ ()
    go stPutBody stCert = no λ ()
    go (stGetBody _) stPut = no λ ()
    go (stGetBody _) stGet = no λ ()
    go (stGetBody _) (stGetAt _) = no λ ()
    go (stGetBody _) stPutEB = no λ ()
    go (stGetBody _) (stGetEBAt _) = no λ ()
    go (stGetBody _) stPutBody = no λ ()
    go (stGetBody _) stPutTx = no λ ()
    go (stGetBody _) (stGetTxAt _) = no λ ()
    go (stGetBody _) stPutVote = no λ ()
    go (stGetBody _) (stGetVoteAt _) = no λ ()
    go (stGetBody _) stCert = no λ ()
    go stPutTx stPut = no λ ()
    go stPutTx stGet = no λ ()
    go stPutTx (stGetAt _) = no λ ()
    go stPutTx stPutEB = no λ ()
    go stPutTx (stGetEBAt _) = no λ ()
    go stPutTx stPutBody = no λ ()
    go stPutTx (stGetBody _) = no λ ()
    go stPutTx (stGetTxAt _) = no λ ()
    go stPutTx stPutVote = no λ ()
    go stPutTx (stGetVoteAt _) = no λ ()
    go stPutTx stCert = no λ ()
    go (stGetTxAt _) stPut = no λ ()
    go (stGetTxAt _) stGet = no λ ()
    go (stGetTxAt _) (stGetAt _) = no λ ()
    go (stGetTxAt _) stPutEB = no λ ()
    go (stGetTxAt _) (stGetEBAt _) = no λ ()
    go (stGetTxAt _) stPutBody = no λ ()
    go (stGetTxAt _) (stGetBody _) = no λ ()
    go (stGetTxAt _) stPutTx = no λ ()
    go (stGetTxAt _) stPutVote = no λ ()
    go (stGetTxAt _) (stGetVoteAt _) = no λ ()
    go (stGetTxAt _) stCert = no λ ()
    go stPutVote stPut = no λ ()
    go stPutVote stGet = no λ ()
    go stPutVote (stGetAt _) = no λ ()
    go stPutVote stPutEB = no λ ()
    go stPutVote (stGetEBAt _) = no λ ()
    go stPutVote stPutBody = no λ ()
    go stPutVote (stGetBody _) = no λ ()
    go stPutVote stPutTx = no λ ()
    go stPutVote (stGetTxAt _) = no λ ()
    go stPutVote (stGetVoteAt _) = no λ ()
    go stPutVote stCert = no λ ()
    go (stGetVoteAt _) stPut = no λ ()
    go (stGetVoteAt _) stGet = no λ ()
    go (stGetVoteAt _) (stGetAt _) = no λ ()
    go (stGetVoteAt _) stPutEB = no λ ()
    go (stGetVoteAt _) (stGetEBAt _) = no λ ()
    go (stGetVoteAt _) stPutBody = no λ ()
    go (stGetVoteAt _) (stGetBody _) = no λ ()
    go (stGetVoteAt _) stPutTx = no λ ()
    go (stGetVoteAt _) (stGetTxAt _) = no λ ()
    go (stGetVoteAt _) stPutVote = no λ ()
    go (stGetVoteAt _) stCert = no λ ()
    go stCert stPut = no λ ()
    go stCert stGet = no λ ()
    go stCert (stGetAt _) = no λ ()
    go stCert stPutEB = no λ ()
    go stCert (stGetEBAt _) = no λ ()
    go stCert stPutBody = no λ ()
    go stCert (stGetBody _) = no λ ()
    go stCert stPutTx = no λ ()
    go stCert (stGetTxAt _) = no λ ()
    go stCert stPutVote = no λ ()
    go stCert (stGetVoteAt _) = no λ ()
    go stPut (stGetTx _) = no λ ()
    go stPut (stHasCert _) = no λ ()
    go stGet (stGetTx _) = no λ ()
    go stGet (stHasCert _) = no λ ()
    go (stGetAt _) (stGetTx _) = no λ ()
    go (stGetAt _) (stHasCert _) = no λ ()
    go stPutEB (stGetTx _) = no λ ()
    go stPutEB (stHasCert _) = no λ ()
    go (stGetEBAt _) (stGetTx _) = no λ ()
    go (stGetEBAt _) (stHasCert _) = no λ ()
    go stPutBody (stGetTx _) = no λ ()
    go stPutBody (stHasCert _) = no λ ()
    go (stGetBody _) (stGetTx _) = no λ ()
    go (stGetBody _) (stHasCert _) = no λ ()
    go stPutTx (stGetTx _) = no λ ()
    go stPutTx (stHasCert _) = no λ ()
    go (stGetTxAt _) (stGetTx _) = no λ ()
    go (stGetTxAt _) (stHasCert _) = no λ ()
    go (stGetTx _) stPut = no λ ()
    go (stGetTx _) stGet = no λ ()
    go (stGetTx _) (stGetAt _) = no λ ()
    go (stGetTx _) stPutEB = no λ ()
    go (stGetTx _) (stGetEBAt _) = no λ ()
    go (stGetTx _) stPutBody = no λ ()
    go (stGetTx _) (stGetBody _) = no λ ()
    go (stGetTx _) stPutTx = no λ ()
    go (stGetTx _) (stGetTxAt _) = no λ ()
    go (stGetTx _) stPutVote = no λ ()
    go (stGetTx _) (stGetVoteAt _) = no λ ()
    go (stGetTx _) stCert = no λ ()
    go (stGetTx _) (stHasCert _) = no λ ()
    go stPutVote (stGetTx _) = no λ ()
    go stPutVote (stHasCert _) = no λ ()
    go (stGetVoteAt _) (stGetTx _) = no λ ()
    go (stGetVoteAt _) (stHasCert _) = no λ ()
    go stCert (stGetTx _) = no λ ()
    go stCert (stHasCert _) = no λ ()
    go (stHasCert _) stPut = no λ ()
    go (stHasCert _) stGet = no λ ()
    go (stHasCert _) (stGetAt _) = no λ ()
    go (stHasCert _) stPutEB = no λ ()
    go (stHasCert _) (stGetEBAt _) = no λ ()
    go (stHasCert _) stPutBody = no λ ()
    go (stHasCert _) (stGetBody _) = no λ ()
    go (stHasCert _) stPutTx = no λ ()
    go (stHasCert _) (stGetTxAt _) = no λ ()
    go (stHasCert _) (stGetTx _) = no λ ()
    go (stHasCert _) stPutVote = no λ ()
    go (stHasCert _) (stGetVoteAt _) = no λ ()
    go (stHasCert _) stCert = no λ ()

  -- the two environment channels are distinguishable
  DecEq-EnvTag : DecEq EnvTag
  DecEq-EnvTag ._≟_ = go
    where
    go : (x y : EnvTag) → Dec (x ≡ y)
    go envForge  envForge  = yes refl
    go envSubmit envSubmit = yes refl
    go envForgeCert envForgeCert = yes refl
    go envForge  envSubmit = no λ ()
    go envSubmit envForge  = no λ ()
    go envForge envForgeCert = no λ ()
    go envSubmit envForgeCert = no λ ()
    go envForgeCert envForge = no λ ()
    go envForgeCert envSubmit = no λ ()


------------------------------------------------------------------------
-- Step 2: the shared network event type `Net`.
--
-- `Net` is parametrised by an abstract payload type `Data`: at the
-- network level the carried data is opaque — its contents are a
-- mini-protocol concern, supplied concretely downstream as `Net <D>`.
-- The link `(l : Link)`, its direction `(d : Dir)`, and the protocol id
-- `IDs` lead every channel; the five message channels have carried type
-- `Data` (the ITrees-style `E A` value type, negotiated by `?`/`!`),
-- while the three acknowledgement channels have carried type `⊤`.
------------------------------------------------------------------------

data Net (Data : Set) : Set → Set where
  input output sndmsg rcvmsg tx : (l : Link) (d : Dir) → IDs → Net Data Data
  sndack rcvack ack             : (l : Link) (d : Dir) → IDs → Net Data ⊤

------------------------------------------------------------------------
-- Step 3: decidable equality on `AnyTypes (Net Data)`.
--
-- `Net-≟` identifies an event by `(constructor, l, d, id)` only — the
-- carried `Data` is negotiated by `?`/`!`, not part of the event
-- identity, so no `DecEq Data` is needed. We destructure each
-- `AnyTypes (Net Data)` as `(_ , ctor …)` and decide via the helper `go`.
--
-- The leading `l d id` of every channel are compared pointwise: first
-- `l₁ ≟ l₂` (Fin DecEq), then `d₁ ≟ d₂` (Dir DecEq), then `id₁ ≟ id₂`
-- (IDs DecEq); any mismatch ⇒ `no λ { refl → ¬p refl }`.
------------------------------------------------------------------------

Net-≟ : {Data : Set} → (x y : AnyTypes (Net Data)) → Dec (x ≡ y)
Net-≟ {Data} = go
  where
  go : (x y : AnyTypes (Net Data)) → Dec (x ≡ y)
  -- input / input
  go (_ , input l₁ d₁ i₁) (_ , input l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- output / output
  go (_ , output l₁ d₁ i₁) (_ , output l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- sndmsg / sndmsg
  go (_ , sndmsg l₁ d₁ i₁) (_ , sndmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- rcvmsg / rcvmsg
  go (_ , rcvmsg l₁ d₁ i₁) (_ , rcvmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- tx / tx
  go (_ , tx l₁ d₁ i₁) (_ , tx l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- sndack / sndack
  go (_ , sndack l₁ d₁ i₁) (_ , sndack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- rcvack / rcvack
  go (_ , rcvack l₁ d₁ i₁) (_ , rcvack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- ack / ack
  go (_ , ack l₁ d₁ i₁) (_ , ack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  -- off-diagonal: distinct constructors are never equal
  go (_ , input _ _ _)  (_ , output _ _ _) = no λ ()
  go (_ , input _ _ _)  (_ , sndmsg _ _ _) = no λ ()
  go (_ , input _ _ _)  (_ , rcvmsg _ _ _) = no λ ()
  go (_ , input _ _ _)  (_ , tx _ _ _)     = no λ ()
  go (_ , input _ _ _)  (_ , sndack _ _ _)   = no λ ()
  go (_ , input _ _ _)  (_ , rcvack _ _ _)   = no λ ()
  go (_ , input _ _ _)  (_ , ack _ _ _)      = no λ ()
  go (_ , output _ _ _) (_ , input _ _ _)  = no λ ()
  go (_ , output _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , tx _ _ _)     = no λ ()
  go (_ , output _ _ _) (_ , sndack _ _ _)   = no λ ()
  go (_ , output _ _ _) (_ , rcvack _ _ _)   = no λ ()
  go (_ , output _ _ _) (_ , ack _ _ _)      = no λ ()
  go (_ , sndmsg _ _ _) (_ , input _ _ _)  = no λ ()
  go (_ , sndmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , tx _ _ _)     = no λ ()
  go (_ , sndmsg _ _ _) (_ , sndack _ _ _)   = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvack _ _ _)   = no λ ()
  go (_ , sndmsg _ _ _) (_ , ack _ _ _)      = no λ ()
  go (_ , rcvmsg _ _ _) (_ , input _ _ _)  = no λ ()
  go (_ , rcvmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , tx _ _ _)     = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndack _ _ _)   = no λ ()
  go (_ , rcvmsg _ _ _) (_ , rcvack _ _ _)   = no λ ()
  go (_ , rcvmsg _ _ _) (_ , ack _ _ _)      = no λ ()
  go (_ , tx _ _ _)     (_ , input _ _ _)  = no λ ()
  go (_ , tx _ _ _)     (_ , output _ _ _) = no λ ()
  go (_ , tx _ _ _)     (_ , sndmsg _ _ _) = no λ ()
  go (_ , tx _ _ _)     (_ , rcvmsg _ _ _) = no λ ()
  go (_ , tx _ _ _)     (_ , sndack _ _ _)   = no λ ()
  go (_ , tx _ _ _)     (_ , rcvack _ _ _)   = no λ ()
  go (_ , tx _ _ _)     (_ , ack _ _ _)      = no λ ()
  go (_ , sndack _ _ _)   (_ , input _ _ _)  = no λ ()
  go (_ , sndack _ _ _)   (_ , output _ _ _) = no λ ()
  go (_ , sndack _ _ _)   (_ , sndmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _)   (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _)   (_ , tx _ _ _)     = no λ ()
  go (_ , sndack _ _ _)   (_ , rcvack _ _ _)   = no λ ()
  go (_ , sndack _ _ _)   (_ , ack _ _ _)      = no λ ()
  go (_ , rcvack _ _ _)   (_ , input _ _ _)  = no λ ()
  go (_ , rcvack _ _ _)   (_ , output _ _ _) = no λ ()
  go (_ , rcvack _ _ _)   (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _)   (_ , rcvmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _)   (_ , tx _ _ _)     = no λ ()
  go (_ , rcvack _ _ _)   (_ , sndack _ _ _)   = no λ ()
  go (_ , rcvack _ _ _)   (_ , ack _ _ _)      = no λ ()
  go (_ , ack _ _ _)      (_ , input _ _ _)  = no λ ()
  go (_ , ack _ _ _)      (_ , output _ _ _) = no λ ()
  go (_ , ack _ _ _)      (_ , sndmsg _ _ _) = no λ ()
  go (_ , ack _ _ _)      (_ , rcvmsg _ _ _) = no λ ()
  go (_ , ack _ _ _)      (_ , tx _ _ _)     = no λ ()
  go (_ , ack _ _ _)      (_ , sndack _ _ _)   = no λ ()
  go (_ , ack _ _ _)      (_ , rcvack _ _ _)   = no λ ()

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
-- Each `apiP` carries the same `(l : Link) (d : Dir)` pair as the wire
-- channels together with the full `ApiP` value, so every api event is
-- `top`-carried; the channels keep the `(l : Link) (d : Dir) -> IDs`
-- prefix and `Net`'s carrier.
------------------------------------------------------------------------

data Net_Api (Data : Set) : Set → Set where
  input output sndmsg rcvmsg tx : (l : Link) (d : Dir) → IDs → Net_Api Data Data
  sndack rcvack ack done        : (l : Link) (d : Dir) → IDs → Net_Api Data ⊤
  apiCS : (l : Link) (d : Dir) (m : ApiCSTag) → Net_Api Data (ApiCSCar m)
  apiBF : (l : Link) (d : Dir) (m : ApiBFTag) → Net_Api Data (ApiBFCar m)
  apiTS : (l : Link) (d : Dir) (m : ApiTSTag) → Net_Api Data (ApiTSCar m)
  apiKA : (l : Link) (d : Dir) (m : ApiKATag) → Net_Api Data (ApiKACar m)
  apiLN : (l : Link) (d : Dir) (m : ApiLNTag) → Net_Api Data (ApiLNCar m)
  apiLF : (l : Link) (d : Dir) (m : ApiLFTag) → Net_Api Data (ApiLFCar m)
  -- the leios-prototype peers' api channel (both prototype mini-protocols)
  apiLP : (l : Link) (d : Dir) (m : ApiLPTag) → Net_Api Data (ApiLPCar m)
  -- node-local: a node's block store, named by the node's head endpoint (l , d)
  store : (l : Link) (d : Dir) (m : StoreTag) → Net_Api Data (StoreCar m)
  -- node-local: the environment forging into the node at endpoint (l , d)
  env   : (l : Link) (d : Dir) (m : EnvTag)   → Net_Api Data (EnvCar m)
  -- fault injection: sever the whole (duplex) TCP link l (interrupt trigger)
  break : (l : Link) → Net_Api Data ⊤

------------------------------------------------------------------------
-- Step 5: decidable equality on `AnyTypes (Net_Api Data)`.
--
-- Channels are identified by `(constructor, l, d, id)` -- the carried
-- `Data` is negotiated by the value, not part of the identity.  Each
-- `apiP` is identified by its `(l, d)` link/direction pair and the api
-- sub-constructor tag only; the `ApiP` payload now lives in the carrier
-- value, not the event identity, so there is nothing further to compare.
------------------------------------------------------------------------

Net_Api-≟ : {Data : Set} → (x y : AnyTypes (Net_Api Data)) → Dec (x ≡ y)
Net_Api-≟ {Data} = go
  where
  go : (x y : AnyTypes (Net_Api Data)) → Dec (x ≡ y)
  go (_ , input l₁ d₁ i₁) (_ , input l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , output l₁ d₁ i₁) (_ , output l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , sndmsg l₁ d₁ i₁) (_ , sndmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , rcvmsg l₁ d₁ i₁) (_ , rcvmsg l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , tx l₁ d₁ i₁) (_ , tx l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , sndack l₁ d₁ i₁) (_ , sndack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , rcvack l₁ d₁ i₁) (_ , rcvack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , ack l₁ d₁ i₁) (_ , ack l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , done l₁ d₁ i₁) (_ , done l₂ d₂ i₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | i₁ ≟ i₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬i    = no λ { refl → ¬i refl }
  go (_ , apiCS l₁ d₁ m₁) (_ , apiCS l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiBF l₁ d₁ m₁) (_ , apiBF l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiTS l₁ d₁ m₁) (_ , apiTS l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiKA l₁ d₁ m₁) (_ , apiKA l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiLN l₁ d₁ m₁) (_ , apiLN l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiLF l₁ d₁ m₁) (_ , apiLF l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , apiLP l₁ d₁ m₁) (_ , apiLP l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , break l₁) (_ , break l₂) with l₁ ≟ l₂
  ... | yes refl = yes refl
  ... | no ¬l    = no λ { refl → ¬l refl }
  -- off-diagonal: distinct constructors are never equal
  go (_ , input _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , break _) = no λ ()
  -- break / other constructors (both orders)
  go (_ , break _) (_ , input _ _ _) = no λ ()
  go (_ , break _) (_ , output _ _ _) = no λ ()
  go (_ , break _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , break _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , break _) (_ , tx _ _ _) = no λ ()
  go (_ , break _) (_ , sndack _ _ _) = no λ ()
  go (_ , break _) (_ , rcvack _ _ _) = no λ ()
  go (_ , break _) (_ , ack _ _ _) = no λ ()
  go (_ , break _) (_ , done _ _ _) = no λ ()
  go (_ , break _) (_ , apiCS _ _ _) = no λ ()
  go (_ , break _) (_ , apiBF _ _ _) = no λ ()
  go (_ , break _) (_ , apiTS _ _ _) = no λ ()
  go (_ , break _) (_ , apiKA _ _ _) = no λ ()
  go (_ , break _) (_ , apiLN _ _ _) = no λ ()
  go (_ , break _) (_ , apiLF _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , break _) = no λ ()
  go (_ , output _ _ _) (_ , break _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , break _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , break _) = no λ ()
  go (_ , tx _ _ _) (_ , break _) = no λ ()
  go (_ , sndack _ _ _) (_ , break _) = no λ ()
  go (_ , rcvack _ _ _) (_ , break _) = no λ ()
  go (_ , ack _ _ _) (_ , break _) = no λ ()
  go (_ , done _ _ _) (_ , break _) = no λ ()
  go (_ , apiCS _ _ _) (_ , break _) = no λ ()
  go (_ , apiBF _ _ _) (_ , break _) = no λ ()
  go (_ , apiTS _ _ _) (_ , break _) = no λ ()
  go (_ , apiKA _ _ _) (_ , break _) = no λ ()
  go (_ , apiLN _ _ _) (_ , break _) = no λ ()
  -- the two node-local channels: identity is constructor + link + dir + tag
  go (_ , store l₁ d₁ m₁) (_ , store l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  go (_ , env l₁ d₁ m₁) (_ , env l₂ d₂ m₂) with l₁ ≟ l₂ | d₁ ≟ d₂ | m₁ ≟ m₂
  ... | yes refl | yes refl | yes refl = yes refl
  ... | no ¬l    | _        | _        = no λ { refl → ¬l refl }
  ... | _        | no ¬d    | _        = no λ { refl → ¬d refl }
  ... | _        | _        | no ¬m    = no λ { refl → ¬m refl }
  -- off-diagonal: store / env against every other constructor (both orders)
  go (_ , store _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , store _ _ _) (_ , break _) = no λ ()
  go (_ , break _) (_ , store _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , input _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , break _) = no λ ()
  go (_ , break _) (_ , env _ _ _) = no λ ()
  -- off-diagonal: the prototype api channel against every other constructor (both orders)
  go (_ , input _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , output _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , sndmsg _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , rcvmsg _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , tx _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , sndack _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , rcvack _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , ack _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , done _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiCS _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiBF _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiTS _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiKA _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiLN _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiLF _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , input _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , output _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , sndmsg _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , rcvmsg _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , tx _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , sndack _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , rcvack _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , ack _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , done _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiCS _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiBF _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiTS _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiKA _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiLN _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , apiLF _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , store _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , env _ _ _) = no λ ()
  go (_ , apiLP _ _ _) (_ , break _) = no λ ()
  go (_ , store _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , env _ _ _) (_ , apiLP _ _ _) = no λ ()
  go (_ , break _) (_ , apiLP _ _ _) = no λ ()
