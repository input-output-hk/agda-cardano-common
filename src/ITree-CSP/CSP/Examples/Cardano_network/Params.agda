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

module CSP.Examples.Cardano_network.Params where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Product using (_×_)
open import Class.DecEq using (DecEq)

open import CSP.Examples.Cardano_network.Base using (IDs; Dir)

record Params : Set₁ where
  field
    Cookie Block Txid LSlot VoterId LFBitmap VoteBlob : Set
    Time Length : Set
    time₀   : Time
    length₀ : Length
    -- number of TCP links (the Link index is `Fin numLinks`)
    numLinks : ℕ
    -- per-link active mini-protocol instances: which (direction, protocol)
    -- pairs actually run on each link (unlisted ⇒ that instance is absent)
    linkConfig : Fin numLinks → List (Dir × IDs)
    ⦃ decCookie ⦄   : DecEq Cookie
    ⦃ decBlock ⦄    : DecEq Block
    ⦃ decTxid ⦄     : DecEq Txid
    ⦃ decLSlot ⦄    : DecEq LSlot
    ⦃ decVoterId ⦄  : DecEq VoterId
    ⦃ decLFBitmap ⦄ : DecEq LFBitmap
    ⦃ decVoteBlob ⦄ : DecEq VoteBlob
    ⦃ decTime ⦄     : DecEq Time
    ⦃ decLength ⦄   : DecEq Length
