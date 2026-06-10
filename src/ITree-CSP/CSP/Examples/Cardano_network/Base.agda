{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — concrete control enums (`Base`).
--
-- This module is *parameter-free*. It collects the genuine finite
-- *control* choices of the reference CSP model — these are real
-- enumerations, not opaque data domains, so they stay concrete:
--   `IDs`           — the six N2N mini-protocol identifiers,
--   `Mode`          — message direction (FromInitiator / FromResponder),
--   `BlockingStyle` — TxSubmission blocking flag.
--
-- The numeric domains `Length` and `Time` are *not* defined here: they
-- are simply `ℕ` and used directly downstream.
--
-- Each enum is given a hand-written `Class.DecEq` instance so that the
-- abstract data domains (`Params`) and the message datatypes (`Data`)
-- can compose decidable equality.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Base where

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

------------------------------------------------------------------------
-- The concrete control enums.
------------------------------------------------------------------------

-- Mini-protocol identifiers (the N2N protocol ids actually modelled).
data IDs : Set where
  N2N_ChainSync N2N_BlockFetch N2N_TxSubmission
    N2N_KeepAlive N2N_LeiosNotify N2N_LeiosFetch : IDs

data Mode : Set where
  FromInitiator FromResponder : Mode

data BlockingStyle : Set where
  Blocking NonBlocking : BlockingStyle

------------------------------------------------------------------------
-- DecEq instances (hand-written).
------------------------------------------------------------------------

instance
  DecEq-IDs : DecEq IDs
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_ChainSync    = yes refl
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_BlockFetch   = yes refl
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_TxSubmission = yes refl
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_KeepAlive    = yes refl
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_LeiosNotify  = yes refl
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_LeiosFetch   = yes refl
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_BlockFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_TxSubmission = no λ ()
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_KeepAlive    = no λ ()
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_LeiosNotify  = no λ ()
  DecEq-IDs ._≟_ N2N_ChainSync    N2N_LeiosFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_ChainSync    = no λ ()
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_TxSubmission = no λ ()
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_KeepAlive    = no λ ()
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_LeiosNotify  = no λ ()
  DecEq-IDs ._≟_ N2N_BlockFetch   N2N_LeiosFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_ChainSync    = no λ ()
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_BlockFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_KeepAlive    = no λ ()
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_LeiosNotify  = no λ ()
  DecEq-IDs ._≟_ N2N_TxSubmission N2N_LeiosFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_ChainSync    = no λ ()
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_BlockFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_TxSubmission = no λ ()
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_LeiosNotify  = no λ ()
  DecEq-IDs ._≟_ N2N_KeepAlive    N2N_LeiosFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_ChainSync    = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_BlockFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_TxSubmission = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_KeepAlive    = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosNotify  N2N_LeiosFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_ChainSync    = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_BlockFetch   = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_TxSubmission = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_KeepAlive    = no λ ()
  DecEq-IDs ._≟_ N2N_LeiosFetch   N2N_LeiosNotify  = no λ ()

  DecEq-Mode : DecEq Mode
  DecEq-Mode ._≟_ FromInitiator FromInitiator = yes refl
  DecEq-Mode ._≟_ FromResponder FromResponder = yes refl
  DecEq-Mode ._≟_ FromInitiator FromResponder = no λ ()
  DecEq-Mode ._≟_ FromResponder FromInitiator = no λ ()

  DecEq-BlockingStyle : DecEq BlockingStyle
  DecEq-BlockingStyle ._≟_ Blocking    Blocking    = yes refl
  DecEq-BlockingStyle ._≟_ NonBlocking NonBlocking = yes refl
  DecEq-BlockingStyle ._≟_ Blocking    NonBlocking = no λ ()
  DecEq-BlockingStyle ._≟_ NonBlocking Blocking    = no λ ()
