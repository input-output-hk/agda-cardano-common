{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — derived structured types and protocol
-- messages, over **abstract** data domains.
--
-- This module is parametrised by `(p : Params)` and `open Params p`,
-- bringing the abstract opaque domains (`Cookie Block Txid LSlot
-- VoterId LFBitmap VoteBlob`) and their `Class.DecEq` instances into
-- scope. The concrete control enums (`IDs`/`Mode`/`BlockingStyle`) come
-- from `Base`, and the numeric domains `Length`/`Time` are simply `ℕ`.
--
-- Over the abstract bases we build the concrete *derived* structured
-- types (`Point`/`ChainRange`/`Header`/`Tip`/`Tx`/`Vote`) and the six
-- mini-protocol message datatypes of the reference CSP model
--   (Study/Networks/Mini-protocols/mini_protocols.csp),
-- providing a `DecEq` instance for every one so that downstream modules
-- (`Net-≟` and the per-protocol `□` choices) resolve decidable equality
-- compositionally.
--
-- The derived `DecEq`s see `DecEq Block` etc. directly from `open
-- Params p` (the record's instance fields enter instance scope), so no
-- explicit `instance _ = decBlock` rebindings are needed.
--
-- Bounded sequences in the `.csp` (BoundedSeq(a, 2)) are modelled as
-- plain `List` (the length bound is left informal); `List` already has a
-- `DecEq` instance derived from the element instance.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.Data (p : Params) where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Class.DecEq using (DecEq; _≟_)

open import CSP.Examples.Cardano_network.Base
  using ( BlockingStyle; Blocking; NonBlocking; Mode; DecEq-Mode )

-- Abstract opaque domains + their DecEq instances, in scope here.
open Params p

------------------------------------------------------------------------
-- Step 1: derived structured types (concrete, over the abstract bases)
------------------------------------------------------------------------

data Point : Set where
  point : Block → Point

data ChainRange : Set where
  chainRange : Point → Point → ChainRange

data Header : Set where
  header : Block → Header

data Tip : Set where
  tip : Block → Tip

data Tx : Set where
  txData : Txid → Tx

data Vote : Set where
  vote : LSlot → VoterId → Vote

------------------------------------------------------------------------
-- Step 2: the six message datatypes (constructors verbatim from the plan)
------------------------------------------------------------------------

data MessageKeepAlive : Set where
  MsgKeepAlive         : Cookie → MessageKeepAlive
  MsgKeepAliveResponse : Cookie → MessageKeepAlive
  MsgKADone            : MessageKeepAlive

data MessageBlockFetch : Set where
  MsgRequestRange : ChainRange → MessageBlockFetch
  MsgStartBatch   : MessageBlockFetch
  MsgNoBlocks     : MessageBlockFetch
  MsgBlock        : Block → MessageBlockFetch
  MsgBatchDone    : MessageBlockFetch
  MsgClientDone   : MessageBlockFetch

data MessageChainSync : Set where
  MsgCSRequestNext       : MessageChainSync
  MsgCSAwaitReply        : MessageChainSync
  MsgCSRollForward       : Header → Tip → MessageChainSync
  MsgCSRollBackward      : Point → Tip → MessageChainSync
  MsgCSFindIntersect     : List Point → MessageChainSync
  MsgCSIntersectFound    : Point → Tip → MessageChainSync
  MsgCSIntersectNotFound : Tip → MessageChainSync
  MsgCSDone              : MessageChainSync

data MessageTxSubmission2 : Set where
  MsgTSInit         : MessageTxSubmission2
  MsgTSRequestTxIds : BlockingStyle → ℕ → ℕ → MessageTxSubmission2
  MsgTSReplyTxIds   : List Txid → MessageTxSubmission2
  MsgTSRequestTxs   : List Txid → MessageTxSubmission2
  MsgTSReplyTxs     : List Tx → MessageTxSubmission2
  MsgTSDone         : MessageTxSubmission2

data MessageLeiosNotify : Set where
  MsgLNRequestNext       : MessageLeiosNotify
  MsgLNBlockAnnouncement : Header → MessageLeiosNotify
  MsgLNBlockOffer        : Point → MessageLeiosNotify
  MsgLNBlockTxsOffer     : Point → MessageLeiosNotify
  MsgLNVotesOffer        : List Vote → MessageLeiosNotify
  MsgLNDone              : MessageLeiosNotify

data MessageLeiosFetch : Set where
  MsgLFBlockRequest             : Point → MessageLeiosFetch
  MsgLFBlock                    : Block → MessageLeiosFetch
  MsgLFBlockTxsRequest          : Point → LFBitmap → MessageLeiosFetch
  MsgLFBlockTxs                 : List Tx → MessageLeiosFetch
  MsgLFVotesRequest             : List Vote → MessageLeiosFetch
  MsgLFVoteDelivery             : List VoteBlob → MessageLeiosFetch
  MsgLFBlockRangeRequest        : ChainRange → MessageLeiosFetch
  MsgLFNextBlockAndTxsInRange   : Block → List Tx → MessageLeiosFetch
  MsgLFLastBlockAndTxsInRange   : Block → List Tx → MessageLeiosFetch
  MsgLFDone                     : MessageLeiosFetch

data Messages : Set where
  keepAlive    : MessageKeepAlive     → Messages
  blockFetch   : MessageBlockFetch    → Messages
  chainSync    : MessageChainSync     → Messages
  txSubmission : MessageTxSubmission2 → Messages
  leiosNotify  : MessageLeiosNotify   → Messages
  leiosFetch   : MessageLeiosFetch    → Messages

------------------------------------------------------------------------
-- Step 3: DecEq instances
--
-- The abstract domains' instances come from `open Params p`; the
-- concrete control enums' instances come from `Base`. Here we only need
-- the derived structured types, the six message datatypes, and
-- `Messages`, assembling their `_≟_` from the component instances via
-- nested `with`; `List` reuses its stdlib-classes instance.
------------------------------------------------------------------------

instance
  -- structured (single-/multi-field) types over the abstract bases

  DecEq-Point : DecEq Point
  DecEq-Point ._≟_ (point x) (point y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl

  DecEq-ChainRange : DecEq ChainRange
  DecEq-ChainRange ._≟_ (chainRange a b) (chainRange c d) with a ≟ c | b ≟ d
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl

  DecEq-Header : DecEq Header
  DecEq-Header ._≟_ (header x) (header y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl

  DecEq-Tip : DecEq Tip
  DecEq-Tip ._≟_ (tip x) (tip y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl

  DecEq-Tx : DecEq Tx
  DecEq-Tx ._≟_ (txData x) (txData y) with x ≟ y
  ... | yes refl = yes refl
  ... | no ¬p    = no λ where refl → ¬p refl

  DecEq-Vote : DecEq Vote
  DecEq-Vote ._≟_ (vote s u) (vote s′ u′) with s ≟ s′ | u ≟ u′
  ... | yes refl | yes refl = yes refl
  ... | no ¬p    | _        = no λ where refl → ¬p refl
  ... | _        | no ¬p    = no λ where refl → ¬p refl

------------------------------------------------------------------------
-- The six message datatypes
------------------------------------------------------------------------

instance
  DecEq-MessageKeepAlive : DecEq MessageKeepAlive
  DecEq-MessageKeepAlive ._≟_ = go
    where
    go : (x y : MessageKeepAlive) → Dec (x ≡ y)
    go (MsgKeepAlive a)         (MsgKeepAlive b)         with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgKeepAliveResponse a) (MsgKeepAliveResponse b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgKADone                MsgKADone                = yes refl
    go (MsgKeepAlive _)         (MsgKeepAliveResponse _) = no λ ()
    go (MsgKeepAlive _)         MsgKADone                = no λ ()
    go (MsgKeepAliveResponse _) (MsgKeepAlive _)         = no λ ()
    go (MsgKeepAliveResponse _) MsgKADone                = no λ ()
    go MsgKADone                (MsgKeepAlive _)         = no λ ()
    go MsgKADone                (MsgKeepAliveResponse _) = no λ ()

  DecEq-MessageBlockFetch : DecEq MessageBlockFetch
  DecEq-MessageBlockFetch ._≟_ = go
    where
    go : (x y : MessageBlockFetch) → Dec (x ≡ y)
    go (MsgRequestRange a) (MsgRequestRange b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgStartBatch  MsgStartBatch  = yes refl
    go MsgNoBlocks    MsgNoBlocks    = yes refl
    go (MsgBlock a)   (MsgBlock b)   with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgBatchDone   MsgBatchDone   = yes refl
    go MsgClientDone  MsgClientDone  = yes refl
    go (MsgRequestRange _) MsgStartBatch   = no λ ()
    go (MsgRequestRange _) MsgNoBlocks     = no λ ()
    go (MsgRequestRange _) (MsgBlock _)    = no λ ()
    go (MsgRequestRange _) MsgBatchDone    = no λ ()
    go (MsgRequestRange _) MsgClientDone   = no λ ()
    go MsgStartBatch  (MsgRequestRange _)  = no λ ()
    go MsgStartBatch  MsgNoBlocks          = no λ ()
    go MsgStartBatch  (MsgBlock _)         = no λ ()
    go MsgStartBatch  MsgBatchDone         = no λ ()
    go MsgStartBatch  MsgClientDone        = no λ ()
    go MsgNoBlocks    (MsgRequestRange _)  = no λ ()
    go MsgNoBlocks    MsgStartBatch        = no λ ()
    go MsgNoBlocks    (MsgBlock _)         = no λ ()
    go MsgNoBlocks    MsgBatchDone         = no λ ()
    go MsgNoBlocks    MsgClientDone        = no λ ()
    go (MsgBlock _)   (MsgRequestRange _)  = no λ ()
    go (MsgBlock _)   MsgStartBatch        = no λ ()
    go (MsgBlock _)   MsgNoBlocks          = no λ ()
    go (MsgBlock _)   MsgBatchDone         = no λ ()
    go (MsgBlock _)   MsgClientDone        = no λ ()
    go MsgBatchDone   (MsgRequestRange _)  = no λ ()
    go MsgBatchDone   MsgStartBatch        = no λ ()
    go MsgBatchDone   MsgNoBlocks          = no λ ()
    go MsgBatchDone   (MsgBlock _)         = no λ ()
    go MsgBatchDone   MsgClientDone        = no λ ()
    go MsgClientDone  (MsgRequestRange _)  = no λ ()
    go MsgClientDone  MsgStartBatch        = no λ ()
    go MsgClientDone  MsgNoBlocks          = no λ ()
    go MsgClientDone  (MsgBlock _)         = no λ ()
    go MsgClientDone  MsgBatchDone         = no λ ()

  DecEq-MessageChainSync : DecEq MessageChainSync
  DecEq-MessageChainSync ._≟_ = go
    where
    go : (x y : MessageChainSync) → Dec (x ≡ y)
    go MsgCSRequestNext MsgCSRequestNext = yes refl
    go MsgCSAwaitReply  MsgCSAwaitReply  = yes refl
    go (MsgCSRollForward h t) (MsgCSRollForward h′ t′) with h ≟ h′ | t ≟ t′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgCSRollBackward p t) (MsgCSRollBackward p′ t′) with p ≟ p′ | t ≟ t′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgCSFindIntersect ps) (MsgCSFindIntersect ps′) with ps ≟ ps′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgCSIntersectFound p t) (MsgCSIntersectFound p′ t′) with p ≟ p′ | t ≟ t′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgCSIntersectNotFound t) (MsgCSIntersectNotFound t′) with t ≟ t′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgCSDone MsgCSDone = yes refl
    go MsgCSRequestNext            MsgCSAwaitReply              = no λ ()
    go MsgCSRequestNext            (MsgCSRollForward _ _)       = no λ ()
    go MsgCSRequestNext            (MsgCSRollBackward _ _)      = no λ ()
    go MsgCSRequestNext            (MsgCSFindIntersect _)       = no λ ()
    go MsgCSRequestNext            (MsgCSIntersectFound _ _)    = no λ ()
    go MsgCSRequestNext            (MsgCSIntersectNotFound _)   = no λ ()
    go MsgCSRequestNext            MsgCSDone                    = no λ ()
    go MsgCSAwaitReply             MsgCSRequestNext             = no λ ()
    go MsgCSAwaitReply             (MsgCSRollForward _ _)       = no λ ()
    go MsgCSAwaitReply             (MsgCSRollBackward _ _)      = no λ ()
    go MsgCSAwaitReply             (MsgCSFindIntersect _)       = no λ ()
    go MsgCSAwaitReply             (MsgCSIntersectFound _ _)    = no λ ()
    go MsgCSAwaitReply             (MsgCSIntersectNotFound _)   = no λ ()
    go MsgCSAwaitReply             MsgCSDone                    = no λ ()
    go (MsgCSRollForward _ _)      MsgCSRequestNext             = no λ ()
    go (MsgCSRollForward _ _)      MsgCSAwaitReply              = no λ ()
    go (MsgCSRollForward _ _)      (MsgCSRollBackward _ _)      = no λ ()
    go (MsgCSRollForward _ _)      (MsgCSFindIntersect _)       = no λ ()
    go (MsgCSRollForward _ _)      (MsgCSIntersectFound _ _)    = no λ ()
    go (MsgCSRollForward _ _)      (MsgCSIntersectNotFound _)   = no λ ()
    go (MsgCSRollForward _ _)      MsgCSDone                    = no λ ()
    go (MsgCSRollBackward _ _)     MsgCSRequestNext             = no λ ()
    go (MsgCSRollBackward _ _)     MsgCSAwaitReply              = no λ ()
    go (MsgCSRollBackward _ _)     (MsgCSRollForward _ _)       = no λ ()
    go (MsgCSRollBackward _ _)     (MsgCSFindIntersect _)       = no λ ()
    go (MsgCSRollBackward _ _)     (MsgCSIntersectFound _ _)    = no λ ()
    go (MsgCSRollBackward _ _)     (MsgCSIntersectNotFound _)   = no λ ()
    go (MsgCSRollBackward _ _)     MsgCSDone                    = no λ ()
    go (MsgCSFindIntersect _)      MsgCSRequestNext             = no λ ()
    go (MsgCSFindIntersect _)      MsgCSAwaitReply              = no λ ()
    go (MsgCSFindIntersect _)      (MsgCSRollForward _ _)       = no λ ()
    go (MsgCSFindIntersect _)      (MsgCSRollBackward _ _)      = no λ ()
    go (MsgCSFindIntersect _)      (MsgCSIntersectFound _ _)    = no λ ()
    go (MsgCSFindIntersect _)      (MsgCSIntersectNotFound _)   = no λ ()
    go (MsgCSFindIntersect _)      MsgCSDone                    = no λ ()
    go (MsgCSIntersectFound _ _)   MsgCSRequestNext             = no λ ()
    go (MsgCSIntersectFound _ _)   MsgCSAwaitReply              = no λ ()
    go (MsgCSIntersectFound _ _)   (MsgCSRollForward _ _)       = no λ ()
    go (MsgCSIntersectFound _ _)   (MsgCSRollBackward _ _)      = no λ ()
    go (MsgCSIntersectFound _ _)   (MsgCSFindIntersect _)       = no λ ()
    go (MsgCSIntersectFound _ _)   (MsgCSIntersectNotFound _)   = no λ ()
    go (MsgCSIntersectFound _ _)   MsgCSDone                    = no λ ()
    go (MsgCSIntersectNotFound _)  MsgCSRequestNext             = no λ ()
    go (MsgCSIntersectNotFound _)  MsgCSAwaitReply              = no λ ()
    go (MsgCSIntersectNotFound _)  (MsgCSRollForward _ _)       = no λ ()
    go (MsgCSIntersectNotFound _)  (MsgCSRollBackward _ _)      = no λ ()
    go (MsgCSIntersectNotFound _)  (MsgCSFindIntersect _)       = no λ ()
    go (MsgCSIntersectNotFound _)  (MsgCSIntersectFound _ _)    = no λ ()
    go (MsgCSIntersectNotFound _)  MsgCSDone                    = no λ ()
    go MsgCSDone                   MsgCSRequestNext             = no λ ()
    go MsgCSDone                   MsgCSAwaitReply              = no λ ()
    go MsgCSDone                   (MsgCSRollForward _ _)       = no λ ()
    go MsgCSDone                   (MsgCSRollBackward _ _)      = no λ ()
    go MsgCSDone                   (MsgCSFindIntersect _)       = no λ ()
    go MsgCSDone                   (MsgCSIntersectFound _ _)    = no λ ()
    go MsgCSDone                   (MsgCSIntersectNotFound _)   = no λ ()

  DecEq-MessageTxSubmission2 : DecEq MessageTxSubmission2
  DecEq-MessageTxSubmission2 ._≟_ = go
    where
    go : (x y : MessageTxSubmission2) → Dec (x ≡ y)
    go MsgTSInit MsgTSInit = yes refl
    go (MsgTSRequestTxIds b a r) (MsgTSRequestTxIds b′ a′ r′)
      with b ≟ b′ | a ≟ a′ | r ≟ r′
    ... | yes refl | yes refl | yes refl = yes refl
    ... | no ¬p    | _        | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgTSReplyTxIds xs) (MsgTSReplyTxIds ys) with xs ≟ ys
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgTSRequestTxs xs) (MsgTSRequestTxs ys) with xs ≟ ys
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgTSReplyTxs xs) (MsgTSReplyTxs ys) with xs ≟ ys
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgTSDone MsgTSDone = yes refl
    go MsgTSInit               (MsgTSRequestTxIds _ _ _) = no λ ()
    go MsgTSInit               (MsgTSReplyTxIds _)       = no λ ()
    go MsgTSInit               (MsgTSRequestTxs _)       = no λ ()
    go MsgTSInit               (MsgTSReplyTxs _)         = no λ ()
    go MsgTSInit               MsgTSDone                 = no λ ()
    go (MsgTSRequestTxIds _ _ _) MsgTSInit              = no λ ()
    go (MsgTSRequestTxIds _ _ _) (MsgTSReplyTxIds _)    = no λ ()
    go (MsgTSRequestTxIds _ _ _) (MsgTSRequestTxs _)    = no λ ()
    go (MsgTSRequestTxIds _ _ _) (MsgTSReplyTxs _)      = no λ ()
    go (MsgTSRequestTxIds _ _ _) MsgTSDone              = no λ ()
    go (MsgTSReplyTxIds _)     MsgTSInit                = no λ ()
    go (MsgTSReplyTxIds _)     (MsgTSRequestTxIds _ _ _) = no λ ()
    go (MsgTSReplyTxIds _)     (MsgTSRequestTxs _)      = no λ ()
    go (MsgTSReplyTxIds _)     (MsgTSReplyTxs _)        = no λ ()
    go (MsgTSReplyTxIds _)     MsgTSDone                = no λ ()
    go (MsgTSRequestTxs _)     MsgTSInit                = no λ ()
    go (MsgTSRequestTxs _)     (MsgTSRequestTxIds _ _ _) = no λ ()
    go (MsgTSRequestTxs _)     (MsgTSReplyTxIds _)      = no λ ()
    go (MsgTSRequestTxs _)     (MsgTSReplyTxs _)        = no λ ()
    go (MsgTSRequestTxs _)     MsgTSDone                = no λ ()
    go (MsgTSReplyTxs _)       MsgTSInit                = no λ ()
    go (MsgTSReplyTxs _)       (MsgTSRequestTxIds _ _ _) = no λ ()
    go (MsgTSReplyTxs _)       (MsgTSReplyTxIds _)      = no λ ()
    go (MsgTSReplyTxs _)       (MsgTSRequestTxs _)      = no λ ()
    go (MsgTSReplyTxs _)       MsgTSDone                = no λ ()
    go MsgTSDone               MsgTSInit                = no λ ()
    go MsgTSDone               (MsgTSRequestTxIds _ _ _) = no λ ()
    go MsgTSDone               (MsgTSReplyTxIds _)      = no λ ()
    go MsgTSDone               (MsgTSRequestTxs _)      = no λ ()
    go MsgTSDone               (MsgTSReplyTxs _)        = no λ ()

  DecEq-MessageLeiosNotify : DecEq MessageLeiosNotify
  DecEq-MessageLeiosNotify ._≟_ = go
    where
    go : (x y : MessageLeiosNotify) → Dec (x ≡ y)
    go MsgLNRequestNext MsgLNRequestNext = yes refl
    go (MsgLNBlockAnnouncement h) (MsgLNBlockAnnouncement h′) with h ≟ h′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLNBlockOffer p) (MsgLNBlockOffer p′) with p ≟ p′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLNBlockTxsOffer p) (MsgLNBlockTxsOffer p′) with p ≟ p′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLNVotesOffer vs) (MsgLNVotesOffer vs′) with vs ≟ vs′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go MsgLNDone MsgLNDone = yes refl
    go MsgLNRequestNext            (MsgLNBlockAnnouncement _) = no λ ()
    go MsgLNRequestNext            (MsgLNBlockOffer _)        = no λ ()
    go MsgLNRequestNext            (MsgLNBlockTxsOffer _)     = no λ ()
    go MsgLNRequestNext            (MsgLNVotesOffer _)        = no λ ()
    go MsgLNRequestNext            MsgLNDone                  = no λ ()
    go (MsgLNBlockAnnouncement _)  MsgLNRequestNext           = no λ ()
    go (MsgLNBlockAnnouncement _)  (MsgLNBlockOffer _)        = no λ ()
    go (MsgLNBlockAnnouncement _)  (MsgLNBlockTxsOffer _)     = no λ ()
    go (MsgLNBlockAnnouncement _)  (MsgLNVotesOffer _)        = no λ ()
    go (MsgLNBlockAnnouncement _)  MsgLNDone                  = no λ ()
    go (MsgLNBlockOffer _)         MsgLNRequestNext           = no λ ()
    go (MsgLNBlockOffer _)         (MsgLNBlockAnnouncement _) = no λ ()
    go (MsgLNBlockOffer _)         (MsgLNBlockTxsOffer _)     = no λ ()
    go (MsgLNBlockOffer _)         (MsgLNVotesOffer _)        = no λ ()
    go (MsgLNBlockOffer _)         MsgLNDone                  = no λ ()
    go (MsgLNBlockTxsOffer _)      MsgLNRequestNext           = no λ ()
    go (MsgLNBlockTxsOffer _)      (MsgLNBlockAnnouncement _) = no λ ()
    go (MsgLNBlockTxsOffer _)      (MsgLNBlockOffer _)        = no λ ()
    go (MsgLNBlockTxsOffer _)      (MsgLNVotesOffer _)        = no λ ()
    go (MsgLNBlockTxsOffer _)      MsgLNDone                  = no λ ()
    go (MsgLNVotesOffer _)         MsgLNRequestNext           = no λ ()
    go (MsgLNVotesOffer _)         (MsgLNBlockAnnouncement _) = no λ ()
    go (MsgLNVotesOffer _)         (MsgLNBlockOffer _)        = no λ ()
    go (MsgLNVotesOffer _)         (MsgLNBlockTxsOffer _)     = no λ ()
    go (MsgLNVotesOffer _)         MsgLNDone                  = no λ ()
    go MsgLNDone                   MsgLNRequestNext           = no λ ()
    go MsgLNDone                   (MsgLNBlockAnnouncement _) = no λ ()
    go MsgLNDone                   (MsgLNBlockOffer _)        = no λ ()
    go MsgLNDone                   (MsgLNBlockTxsOffer _)     = no λ ()
    go MsgLNDone                   (MsgLNVotesOffer _)        = no λ ()

  DecEq-MessageLeiosFetch : DecEq MessageLeiosFetch
  DecEq-MessageLeiosFetch ._≟_ = go
    where
    go : (x y : MessageLeiosFetch) → Dec (x ≡ y)
    go (MsgLFBlockRequest p) (MsgLFBlockRequest p′) with p ≟ p′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFBlock b) (MsgLFBlock b′) with b ≟ b′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFBlockTxsRequest p m) (MsgLFBlockTxsRequest p′ m′) with p ≟ p′ | m ≟ m′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFBlockTxs ts) (MsgLFBlockTxs ts′) with ts ≟ ts′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFVotesRequest vs) (MsgLFVotesRequest vs′) with vs ≟ vs′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFVoteDelivery vs) (MsgLFVoteDelivery vs′) with vs ≟ vs′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFBlockRangeRequest r) (MsgLFBlockRangeRequest r′) with r ≟ r′
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFNextBlockAndTxsInRange b ts) (MsgLFNextBlockAndTxsInRange b′ ts′)
      with b ≟ b′ | ts ≟ ts′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go (MsgLFLastBlockAndTxsInRange b ts) (MsgLFLastBlockAndTxsInRange b′ ts′)
      with b ≟ b′ | ts ≟ ts′
    ... | yes refl | yes refl = yes refl
    ... | no ¬p    | _        = no λ where refl → ¬p refl
    ... | _        | no ¬p    = no λ where refl → ¬p refl
    go MsgLFDone MsgLFDone = yes refl
    go (MsgLFBlockRequest _)              (MsgLFBlock _)                      = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockRequest _)              (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockRequest _)              MsgLFDone                           = no λ ()
    go (MsgLFBlock _)                     (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFBlock _)                     (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFBlock _)                     (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFBlock _)                     (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFBlock _)                     (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFBlock _)                     (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFBlock _)                     (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlock _)                     (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlock _)                     MsgLFDone                           = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFBlock _)                      = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockTxsRequest _ _)         (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockTxsRequest _ _)         MsgLFDone                           = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFBlock _)                      = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockTxs _)                  (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockTxs _)                  MsgLFDone                           = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFBlock _)                      = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFVotesRequest _)              (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFVotesRequest _)              MsgLFDone                           = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFBlock _)                      = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFVoteDelivery _)              (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFVoteDelivery _)              MsgLFDone                           = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFBlock _)                      = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockRangeRequest _)         (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFBlockRangeRequest _)         MsgLFDone                           = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFBlock _)                      = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFNextBlockAndTxsInRange _ _)  MsgLFDone                           = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFBlockRequest _)               = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFBlock _)                      = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFBlockTxsRequest _ _)          = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFBlockTxs _)                   = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFVotesRequest _)               = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFVoteDelivery _)               = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFBlockRangeRequest _)          = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go (MsgLFLastBlockAndTxsInRange _ _)  MsgLFDone                           = no λ ()
    go MsgLFDone                          (MsgLFBlockRequest _)               = no λ ()
    go MsgLFDone                          (MsgLFBlock _)                      = no λ ()
    go MsgLFDone                          (MsgLFBlockTxsRequest _ _)          = no λ ()
    go MsgLFDone                          (MsgLFBlockTxs _)                   = no λ ()
    go MsgLFDone                          (MsgLFVotesRequest _)               = no λ ()
    go MsgLFDone                          (MsgLFVoteDelivery _)               = no λ ()
    go MsgLFDone                          (MsgLFBlockRangeRequest _)          = no λ ()
    go MsgLFDone                          (MsgLFNextBlockAndTxsInRange _ _)   = no λ ()
    go MsgLFDone                          (MsgLFLastBlockAndTxsInRange _ _)   = no λ ()

------------------------------------------------------------------------
-- The `Messages` union
------------------------------------------------------------------------

instance
  DecEq-Messages : DecEq Messages
  DecEq-Messages ._≟_ = go
    where
    go : (x y : Messages) → Dec (x ≡ y)
    go (keepAlive a)    (keepAlive b)    with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (blockFetch a)   (blockFetch b)   with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (chainSync a)    (chainSync b)    with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (txSubmission a) (txSubmission b) with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (leiosNotify a)  (leiosNotify b)  with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (leiosFetch a)   (leiosFetch b)   with a ≟ b
    ... | yes refl = yes refl
    ... | no ¬p    = no λ where refl → ¬p refl
    go (keepAlive _)    (blockFetch _)   = no λ ()
    go (keepAlive _)    (chainSync _)    = no λ ()
    go (keepAlive _)    (txSubmission _) = no λ ()
    go (keepAlive _)    (leiosNotify _)  = no λ ()
    go (keepAlive _)    (leiosFetch _)   = no λ ()
    go (blockFetch _)   (keepAlive _)    = no λ ()
    go (blockFetch _)   (chainSync _)    = no λ ()
    go (blockFetch _)   (txSubmission _) = no λ ()
    go (blockFetch _)   (leiosNotify _)  = no λ ()
    go (blockFetch _)   (leiosFetch _)   = no λ ()
    go (chainSync _)    (keepAlive _)    = no λ ()
    go (chainSync _)    (blockFetch _)   = no λ ()
    go (chainSync _)    (txSubmission _) = no λ ()
    go (chainSync _)    (leiosNotify _)  = no λ ()
    go (chainSync _)    (leiosFetch _)   = no λ ()
    go (txSubmission _) (keepAlive _)    = no λ ()
    go (txSubmission _) (blockFetch _)   = no λ ()
    go (txSubmission _) (chainSync _)    = no λ ()
    go (txSubmission _) (leiosNotify _)  = no λ ()
    go (txSubmission _) (leiosFetch _)   = no λ ()
    go (leiosNotify _)  (keepAlive _)    = no λ ()
    go (leiosNotify _)  (blockFetch _)   = no λ ()
    go (leiosNotify _)  (chainSync _)    = no λ ()
    go (leiosNotify _)  (txSubmission _) = no λ ()
    go (leiosNotify _)  (leiosFetch _)   = no λ ()
    go (leiosFetch _)   (keepAlive _)    = no λ ()
    go (leiosFetch _)   (blockFetch _)   = no λ ()
    go (leiosFetch _)   (chainSync _)    = no λ ()
    go (leiosFetch _)   (txSubmission _) = no λ ()
    go (leiosFetch _)   (leiosNotify _)  = no λ ()

------------------------------------------------------------------------
-- Step 4: the negotiated payload `t.m.l.msg` (shared by every peer).
--
-- Each mini-protocol peer negotiates this 4-tuple as the `?`/`!` value of
-- its wire `send`/`receive` events.  It lives here (not in any one peer
-- module) so all peers share ONE `Payload` type and can compose over a
-- single `Net_Api Payload` alphabet.  `Time`/`Length` + their `DecEq`s come
-- from `open Params p`; `Mode`/`DecEq-Mode` from `Base`; `Messages` is local.
------------------------------------------------------------------------

-- the negotiated `Time × Mode × Length × Messages` tuple
Payload : Set
Payload = Time × Mode × Length × Messages

instance
  -- componentwise decidable equality on the payload tuple
  DecEq-Payload : DecEq Payload
  DecEq-Payload ._≟_ (t₁ , m₁ , l₁ , d₁) (t₂ , m₂ , l₂ , d₂)
    with t₁ ≟ t₂ | m₁ ≟ m₂ | l₁ ≟ l₂ | d₁ ≟ d₂
  ... | yes refl | yes refl | yes refl | yes refl = yes refl
  ... | no ¬p | _ | _ | _ = no λ where refl → ¬p refl
  ... | _ | no ¬p | _ | _ = no λ where refl → ¬p refl
  ... | _ | _ | no ¬p | _ = no λ where refl → ¬p refl
  ... | _ | _ | _ | no ¬p = no λ where refl → ¬p refl
