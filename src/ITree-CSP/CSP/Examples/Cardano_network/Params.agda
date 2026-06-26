{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — abstract data domains bundle (`Params`).
--
-- The opaque data domains that CSPm had to *enumerate* for FDR
-- model-checking are kept **abstract** here (we don't model-check). They
-- are bundled — together with their `Class.DecEq` instances and the
-- connection-count assignment `numConns : IDs → ℕ` — into a single
-- record so that every downstream module threads one parameter
-- `(p : Params)` and `open Params p` brings the abstract types *and*
-- their `DecEq` instances into scope (so `Net-≟` / the `□`s / `Parallel`
-- can resolve decidable equality on event payloads).
--
-- A `Scenario` module supplies one concrete `Params` (abstract domains
-- ↦ concrete `Set`s, `numConns` ↦ concrete values).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Params where

open import Data.Nat using (ℕ)
open import Class.DecEq using (DecEq)

open import CSP.Examples.Cardano_network.Base using (IDs)

record Params : Set₁ where
  field
    Cookie Block Txid LSlot VoterId LFBitmap VoteBlob : Set
    Time Length : Set
    time₀   : Time
    length₀ : Length
    numConns : IDs → ℕ
    ⦃ decCookie ⦄   : DecEq Cookie
    ⦃ decBlock ⦄    : DecEq Block
    ⦃ decTxid ⦄     : DecEq Txid
    ⦃ decLSlot ⦄    : DecEq LSlot
    ⦃ decVoterId ⦄  : DecEq VoterId
    ⦃ decLFBitmap ⦄ : DecEq LFBitmap
    ⦃ decVoteBlob ⦄ : DecEq VoteBlob
    ⦃ decTime ⦄     : DecEq Time
    ⦃ decLength ⦄   : DecEq Length
