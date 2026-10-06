{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C: the LABEL WEIGHTS every peer summary is
-- stated in (on `Net_Api Payload` labels).  Each is defined by one clause
-- per channel (and per message / tag), so on a concrete label it REDUCES.
--   * `cIn`, `cOut`, `cApi`   — 1 on a wire `input` / `output` / an api-or-`done`
--   * `wIn k`, `wOut k`       — 1 on a wire input / output carrying a message of kind `k`
--   * `ℓIn k`, `ℓOut k`       — the length of the list such a message carries
--   * `cRep t`, `cCmd t`      — 1 on an api label of tag `t` (a report / a command)
--   * `ℓRep t`, `ℓCmd t`      — the length of the list that api label carries
-- One `refl` sanity lemma per weight (the reduction check).
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.NoLivelock.Weights (p : Params) where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; length)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base
open import Cardano_network.Net p
open import Cardano_network.Data p
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (Event; evLabel)

------------------------------------------------------------------------
-- channel counts
------------------------------------------------------------------------

-- 1 on a wire `input` label
cIn : Event → ℕ
cIn (evLabel _ (input _ _ _) _) = 1
cIn _                           = 0

-- 1 on a wire `output` label
cOut : Event → ℕ
cOut (evLabel _ (output _ _ _) _) = 1
cOut _                            = 0

-- 1 on an api label (any mini-protocol) or a `done`
cApi : Event → ℕ
cApi (evLabel _ (done _ _ _) _)  = 1
cApi (evLabel _ (apiCS _ _ _) _) = 1
cApi (evLabel _ (apiBF _ _ _) _) = 1
cApi (evLabel _ (apiTS _ _ _) _) = 1
cApi (evLabel _ (apiKA _ _ _) _) = 1
cApi (evLabel _ (apiLN _ _ _) _) = 1
cApi (evLabel _ (apiLF _ _ _) _) = 1
cApi (evLabel _ (apiLP _ _ _) _) = 1
cApi _                           = 0

------------------------------------------------------------------------
-- message kinds
------------------------------------------------------------------------

-- the message kinds the relays count
data Kind : Set where
  RF notif votes BlockReq TxsReq BlockTxs ReplyTxIds ReplyTxs : Kind

-- 1 on a message of kind `k` (notifications: the LNP announcement and both offers)
isK : Kind → Messages → ℕ
isK RF         (chainSync (MsgCSRollForward _ _))           = 1
isK notif      (leiosNotifyP (MsgLNPBlockAnnouncement _))  = 1
isK notif      (leiosNotifyP (MsgLNPBlockOffer _ _))       = 1
isK notif      (leiosNotifyP (MsgLNPBlockTxsOffer _))      = 1
isK votes      (leiosNotifyP (MsgLNPVotes _))              = 1
isK BlockReq   (leiosFetchP (MsgLFPBlockRequest _))        = 1
isK TxsReq     (leiosFetchP (MsgLFPBlockTxsRequest _ _))   = 1
isK BlockTxs   (leiosFetchP (MsgLFPBlockTxs _ _))          = 1
isK ReplyTxIds (txSubmission (MsgTSReplyTxIds _))          = 1
isK ReplyTxs   (txSubmission (MsgTSReplyTxs _))            = 1
isK _          _                                           = 0

-- the length of the list a message of kind `k` carries (0 for every other message)
ℓK : Kind → Messages → ℕ
ℓK votes      (leiosNotifyP (MsgLNPVotes vs))             = length vs
ℓK TxsReq     (leiosFetchP (MsgLFPBlockTxsRequest _ bm))  = length bm
ℓK BlockTxs   (leiosFetchP (MsgLFPBlockTxs _ es))         = length es
ℓK ReplyTxIds (txSubmission (MsgTSReplyTxIds ids))        = length ids
ℓK ReplyTxs   (txSubmission (MsgTSReplyTxs txs))          = length txs
ℓK _          _                                           = 0

-- 1 on a wire input carrying a message of kind `k`
wIn : Kind → Event → ℕ
wIn k (evLabel _ (input _ _ _) (_ , _ , _ , m)) = isK k m
wIn k _                                         = 0

-- 1 on a wire output carrying a message of kind `k`
wOut : Kind → Event → ℕ
wOut k (evLabel _ (output _ _ _) (_ , _ , _ , m)) = isK k m
wOut k _                                          = 0

-- the list length a wire input of kind `k` carries
ℓIn : Kind → Event → ℕ
ℓIn k (evLabel _ (input _ _ _) (_ , _ , _ , m)) = ℓK k m
ℓIn k _                                         = 0

-- the list length a wire output of kind `k` carries
ℓOut : Kind → Event → ℕ
ℓOut k (evLabel _ (output _ _ _) (_ , _ , _ , m)) = ℓK k m
ℓOut k _                                          = 0

------------------------------------------------------------------------
-- api tags (of every mini-protocol family)
------------------------------------------------------------------------

-- the api families of `Net_Api`
data Api : Set where
  KA CS BF TS LN LF LP : Api

-- the tag type of a family (constructor-headed, so the family is inferred from a tag)
Tag : Api → Set
Tag KA = ApiKATag
Tag CS = ApiCSTag
Tag BF = ApiBFTag
Tag TS = ApiTSTag
Tag LN = ApiLNTag
Tag LF = ApiLFTag
Tag LP = ApiLPTag

-- 1 when the two tags agree
eqT : {A : Set} ⦃ _ : Class.DecEq.DecEq A ⦄ → A → A → ℕ
eqT t t′ = if ⌊ t ≟ t′ ⌋ then 1 else 0

-- 1 on an api label of tag `t`
cTag : {a : Api} → Tag a → Event → ℕ
cTag {KA} t (evLabel _ (apiKA _ _ t′) _) = eqT t t′
cTag {CS} t (evLabel _ (apiCS _ _ t′) _) = eqT t t′
cTag {BF} t (evLabel _ (apiBF _ _ t′) _) = eqT t t′
cTag {TS} t (evLabel _ (apiTS _ _ t′) _) = eqT t t′
cTag {LN} t (evLabel _ (apiLN _ _ t′) _) = eqT t t′
cTag {LF} t (evLabel _ (apiLF _ _ t′) _) = eqT t t′
cTag {LP} t (evLabel _ (apiLP _ _ t′) _) = eqT t t′
cTag      _ _                            = 0

-- the list a TxSubmission api carrier holds (0 for list-free carriers)
ℓTS : (t : ApiTSTag) → ApiTSCar t → ℕ
ℓTS sendTSReplyTxIds ids = length ids
ℓTS sendTSReplyTxs   txs = length txs
ℓTS recvTSReplyTxIds ids = length ids
ℓTS recvTSReplyTxs   txs = length txs
ℓTS _                _   = 0

-- the list a prototype (LNP/LFP) api carrier holds (0 for list-free carriers)
ℓLP : (t : ApiLPTag) → ApiLPCar t → ℕ
ℓLP lnpSendVotes           vs        = length vs
ℓLP lnpRecvVotes           vs        = length vs
ℓLP lfpSendBlockTxsRequest (_ , bm)  = length bm
ℓLP lfpReqBlockTxsRequest  (_ , bm)  = length bm
ℓLP lfpSendBlockTxs        (_ , es)  = length es
ℓLP lfpRecvBlockTxs        (_ , es)  = length es
ℓLP _                      _         = 0

-- the list length an api label of tag `t` carries (TxSubmission and prototype families)
ℓTag : {a : Api} → Tag a → Event → ℕ
ℓTag {TS} t (evLabel _ (apiTS _ _ t′) c) = if ⌊ t ≟ t′ ⌋ then ℓTS t′ c else 0
ℓTag {LP} t (evLabel _ (apiLP _ _ t′) c) = if ⌊ t ≟ t′ ⌋ then ℓLP t′ c else 0
ℓTag      _ _                            = 0

-- a REPORT (the peer tells its thread what came off the wire) of tag `t`
cRep : {a : Api} → Tag a → Event → ℕ
cRep = cTag

-- a COMMAND (the thread tells its peer what to put on the wire) of tag `t`
cCmd : {a : Api} → Tag a → Event → ℕ
cCmd = cTag

-- the list length a report of tag `t` carries
ℓRep : {a : Api} → Tag a → Event → ℕ
ℓRep = ℓTag

-- the list length a command of tag `t` carries
ℓCmd : {a : Api} → Tag a → Event → ℕ
ℓCmd = ℓTag

------------------------------------------------------------------------
-- sanity: every weight reduces on a concrete label
------------------------------------------------------------------------

-- `cIn` counts a wire input
cIn-ok : ∀ {l d i pl} → cIn (evLabel _ (input l d i) pl) ≡ 1
cIn-ok = refl

-- `cOut` counts a wire output
cOut-ok : ∀ {l d i pl} → cOut (evLabel _ (output l d i) pl) ≡ 1
cOut-ok = refl

-- `cApi` counts an api label and a `done`
cApi-ok : ∀ {l d i c} → cApi (evLabel _ (apiBF l d recvBFBlock) c) ≡ 1 × cApi (evLabel _ (done l d i) _) ≡ 1
cApi-ok = refl , refl

-- `wIn` / `wOut` count a RollForward, not a RollBackward
wIn-ok : ∀ {l d i t m n h tp pt} → wIn RF (evLabel _ (input l d i) (t , m , n , chainSync (MsgCSRollForward h tp))) ≡ 1
       × wOut RF (evLabel _ (output l d i) (t , m , n , chainSync (MsgCSRollBackward pt tp))) ≡ 0
wIn-ok = refl , refl

-- `ℓIn` / `ℓOut` measure the carried list
ℓIn-ok : ∀ {l d i t m n vs} → ℓIn votes (evLabel _ (input l d i) (t , m , n , leiosNotifyP (MsgLNPVotes vs))) ≡ length vs
       × ℓOut votes (evLabel _ (output l d i) (t , m , n , leiosNotifyP (MsgLNPVotes vs))) ≡ length vs
ℓIn-ok = refl , refl

-- `cRep` / `cCmd` count their own tag only (the family is inferred from the tag)
cRep-ok : ∀ {l d ht pt} → cRep recvCSRollforward (evLabel _ (apiCS l d recvCSRollforward) ht) ≡ 1
        × cRep recvCSRollforward (evLabel _ (apiCS l d recvCSRollback) pt) ≡ 0
        × cCmd sendCSRollForward (evLabel _ (apiCS l d sendCSRollForward) ht) ≡ 1
cRep-ok = refl , refl , refl

-- `ℓRep` / `ℓCmd` measure the carried list
ℓRep-ok : ∀ {l d vs txs} → ℓRep lnpRecvVotes (evLabel _ (apiLP l d lnpRecvVotes) vs) ≡ length vs
        × ℓCmd sendTSReplyTxs (evLabel _ (apiTS l d sendTSReplyTxs) txs) ≡ length txs
ℓRep-ok = refl , refl

------------------------------------------------------------------------
-- Task 9a: the REPORT weights each peer OWNS (the triggers the far-driven
-- threads count).  A peer of the same api family that does not own them
-- must never emit them (`…-noRep` in the peer modules).
------------------------------------------------------------------------

open import Data.Nat using (_+_)

-- the LNP client's reports: the four Notify report counts and the vote-list lengths
repLNP : Event → ℕ
repLNP e = cRep lnpRecvBlockAnnouncement e + (cRep lnpRecvBlockOffer e + (cRep lnpRecvBlockTxsOffer e
         + (cRep lnpRecvVotes e + ℓRep lnpRecvVotes e)))

-- the LFP client's reports: the tx-closure entries
repLFc : Event → ℕ
repLFc e = ℓRep lfpRecvBlockTxs e

-- the LFP server's reports: body and closure requests, and the requested offsets
repLFs : Event → ℕ
repLFs e = cRep lfpReqBlockRequest e + (cRep lfpReqBlockTxsRequest e + ℓRep lfpReqBlockTxsRequest e)

-- the TxSubmission requester's reports: txid replies and the tx-list lengths
repTS : Event → ℕ
repTS e = cRep recvTSReplyTxIds e + ℓRep recvTSReplyTxs e
