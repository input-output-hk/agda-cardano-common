{-# OPTIONS --guardedness #-}

-- Core.hs:1273-1832 at network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Exhaustive source-state branches, before IO/STM continuation interpretation.
module ConnectionManagement.Rules.OutboundCases where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import ConnectionManagement.Domain
open import ConnectionManagement.State

data Fault : Set where
  connectionExists forbiddenOperation forbiddenConnection inboundNotFound impossibleState : Fault
  ioFailure : ErrorId → Fault

data Result : Set where
  connected : ConnectionKey → DataFlow → HandleId → Result
  disconnected : ConnectionKey → DisconnectReason → Result
  raised : Fault → Result

data Choice : Set where
  retry : Choice
  waitInbound : ConnectionKey → Choice
  reuse : ConnectionState → Result → Choice
  refuse : Fault → Choice
  gone : Result → Choice

-- Initial selection retries on terminal entries until the map changes.
acquireCase : ConnectionState → Choice
acquireCase reservedOutbound = refuse connectionExists
acquireCase (unnegotiated outbound _ _) = refuse connectionExists
acquireCase (unnegotiated inbound k _) = waitInbound k
acquireCase (outboundUni _ _ _) = refuse connectionExists
acquireCase (outboundDup _ _ _ _) = refuse connectionExists
acquireCase (outboundIdle _ _ _ _) = refuse forbiddenOperation
acquireCase (inboundIdle _ _ _ unidirectional) = refuse forbiddenConnection
acquireCase (inboundIdle k w h duplex) = reuse (outboundDup k w h ticking) (connected k duplex h)
acquireCase (inboundActive _ _ _ unidirectional) = refuse forbiddenConnection
acquireCase (inboundActive k w h duplex) = reuse (duplexActive k w h) (connected k duplex h)
acquireCase (duplexActive _ _ _) = refuse connectionExists
acquireCase (terminating _ _ _) = retry
acquireCase (terminated _) = retry

-- Waiting reads a captured entry, not a new lookup by remote address.
waitCase : ConnectionKey → ConnectionState → Choice
waitCase k reservedOutbound = refuse impossibleState
waitCase k (unnegotiated inbound _ _) = retry
waitCase k (inboundIdle _ w h duplex) = reuse (outboundDup k w h ticking) (connected k duplex h)
waitCase k (inboundActive _ w h duplex) = reuse (duplexActive k w h) (connected k duplex h)
waitCase k (terminating _ _ err) = gone (disconnected k (inTerminating err))
waitCase k (terminated err) = gone (disconnected k (inTerminated err))
waitCase k st = acquireCase st

record Negotiated : Set where
  constructor decision
  field replacement : Maybe ConnectionState
        notify : Bool
        result : Result
open Negotiated public

-- The returned handle is the negotiated result even in the self-connection
-- branch that preserves the inbound entry's thread/handle in the heap.
successCase : ConnectionKey → WorkerId → HandleId → DataFlow → ConnectionState → Negotiated
successCase k w h unidirectional (unnegotiated _ _ _) =
  decision (just (outboundUni k w h)) false (connected k unidirectional h)
successCase k w h duplex (unnegotiated outbound _ _) =
  decision (just (outboundDup k w h ticking)) true (connected k duplex h)
successCase k w h duplex (unnegotiated inbound _ _) =
  decision (just (outboundDup k w h ticking)) false (connected k duplex h)
successCase k w h f (inboundIdle k′ w′ h′ unidirectional) =
  decision (just (outboundUni k′ w′ h′)) false (connected k f h)
successCase k w h f (inboundIdle k′ w′ h′ duplex) =
  decision (just (outboundDup k′ w′ h′ ticking)) false (connected k f h)
successCase k w h f (terminated err) = decision nothing false (disconnected k (inTerminated err))
successCase k w h f _ = decision nothing false (raised forbiddenOperation)
