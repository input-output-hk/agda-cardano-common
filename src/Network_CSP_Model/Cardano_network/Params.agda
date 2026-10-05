{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — abstract data domains bundle (`Params`).
--
-- The opaque data domains that CSPm had to *enumerate* for FDR
-- model-checking are kept **abstract** here (we don't model-check). They
-- are bundled — together with their `Class.DecEq` instances and the
-- link-count and per-link protocol config (`numLinks : ℕ`,
-- `linkConfig : Fin numLinks → List (Dir × IDs)`) — into a single
-- record so that every downstream module threads one parameter
-- `(p : Params)` and `open Params p` brings the abstract types *and*
-- their `DecEq` instances into scope (so `Net-≟` / the `□`s / `Parallel`
-- can resolve decidable equality on event payloads).
--
-- A `Scenario` module supplies one concrete `Params` (abstract domains
-- ↦ concrete `Set`s, `numLinks`/`linkConfig` ↦ concrete values).
------------------------------------------------------------------------

module Cardano_network.Params where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Class.DecEq using (DecEq)

open import Cardano_network.Base using (IDs; Dir)

record Params : Set₁ where
  field
    ------------------------------------------------------------------
    -- Praos domains
    ------------------------------------------------------------------
    Cookie Block LSlot VoterId VoteBlob : Set
    Time Length : Set
    time₀   : Time
    length₀ : Length
    -- number of TCP links (the Link index is `Fin numLinks`)
    numLinks : ℕ
    -- per-link active mini-protocol instances: which (direction, protocol)
    -- pairs actually run on each link (unlisted ⇒ that instance is absent)
    linkConfig : Fin numLinks → List (Dir × IDs)

    ------------------------------------------------------------------
    -- THE THREE HASH-IDENTIFIED OBJECTS.  Every object the protocols move is
    -- modelled the same way: an opaque domain, an opaque identity type, and an
    -- injective-BY-INTENT hash projection (no theorem below needs injectivity).
    -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
    ------------------------------------------------------------------
    -- the hash of a RANKING block's HEADER — the identity of an RB, and what a vote names
    RbHash : Set
    rbHash : Block → RbHash
    -- an endorser block (it travels on the wire) and its identity
    EB EBHash : Set
    ebHash : EB → EBHash
    -- a transaction and its identity.  `Tx` is OPAQUE: the old wrapper
    -- `Data.Tx = txData Txid` made a transaction identical to its id, so a fetched
    -- body was a semantic no-op.  `Txid` is gone; `TxHash` is the identifier.
    Tx TxHash : Set
    txHash : Tx → TxHash

    ------------------------------------------------------------------
    -- header attributes and sizes
    ------------------------------------------------------------------
    -- the slot a ranking block was forged in (an attribute, never a key: slot battles
    -- mean a slot identifies neither an RB nor an EB uniquely).  MOVED IN from
    -- `LeiosParams`: `Data.agda`/`Net.agda` see only `Params`.
    slotOf : Block → LSlot
    -- the EB hash announced by a ranking block, if it announces one
    announcedEB : Block → Maybe EBHash
    -- a byte size on the wire (the prototype's `Word32`): the EB size on `MsgLeiosBlockOffer`
    -- and the size column of every tx table.  Opaque, like every other domain.
    Size : Set
    -- the size of a transaction
    txSize : Tx → Size

    ------------------------------------------------------------------
    -- decidable equality
    ------------------------------------------------------------------
    ⦃ decCookie ⦄   : DecEq Cookie
    ⦃ decBlock ⦄    : DecEq Block
    ⦃ decLSlot ⦄    : DecEq LSlot
    ⦃ decVoterId ⦄  : DecEq VoterId
    ⦃ decVoteBlob ⦄ : DecEq VoteBlob
    ⦃ decTime ⦄     : DecEq Time
    ⦃ decLength ⦄   : DecEq Length
    ⦃ decEB ⦄       : DecEq EB
    ⦃ decEBHash ⦄   : DecEq EBHash
    ⦃ decRbHash ⦄   : DecEq RbHash
    ⦃ decTx ⦄       : DecEq Tx
    ⦃ decTxHash ⦄   : DecEq TxHash
    ⦃ decSize ⦄     : DecEq Size

  -- BACK-COMPATIBILITY ALIAS, for the OLD estate only (TxSubmission's `R2_Bisim` and
  -- `PipePair*` modules name `Txid` in their `open Params p using (…)` lists).  New code
  -- writes `TxHash`.  `Txid` REDUCES to `TxHash`, so the `decTxHash` instance field still
  -- answers every `DecEq Txid` search in a module that opens `Params` unqualified.
  -- see ADR 2026-09-21 (leios-tx-closure-and-object-identities)
  Txid : Set
  Txid = TxHash
