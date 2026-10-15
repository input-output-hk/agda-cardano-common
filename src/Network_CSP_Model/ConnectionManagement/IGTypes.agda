{-# OPTIONS --guardedness #-}

-- Source Event/Terminated payloads and responder descriptors, at network
-- 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d. Payload execution remains abstract.
module ConnectionManagement.IGTypes where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store)

record NewConnectionInfo : Set where
  constructor newConnectionInfo
  field origin : Provenance
        connectionKey : ConnectionKey
        negotiatedFlow : DataFlow
        negotiatedHandle : HandleId
open NewConnectionInfo public

data Temperature : Set where
  hot warm established : Temperature

data StartMode : Set where
  onDemand onDemandAny eagerly : StartMode

record Protocol : Set where
  constructor protocol
  field number : ℕ
        temperature : Temperature
        startMode : StartMode
open Protocol public

data RunResult : Set where
  clean : RunResult
  errored : ErrorId → RunResult

record FreshPeer : Set where
  constructor freshPeer
  field observedAt : ℕ
        versionFromHandle : HandleId
open FreshPeer public

record Terminated : Set where
  constructor terminatedProtocol
  field peer : ConnectionKey
        capturedMux : MuxId
        descriptor : Protocol
        dataFlow : DataFlow
        result : RunResult
open Terminated public

-- Maturity carries BOTH the newly mature map and the remaining fresh queue.
-- Handle references identify opaque version data; protocol descriptors retain
-- the captured number/temperature/start policy, rather than relooking them up.
data IGEvent : Set where
  newConnection : NewConnectionInfo → IGEvent
  muxFinished : ConnectionKey → IGEvent
  miniProtocolTerminated : Terminated → IGEvent
  waitIdleRemote remotePromotedToHot remoteDemotedToWarm commitRemote
    awakeRemote : ConnectionKey → IGEvent
  maturedDuplexPeers : Store PeerAddr HandleId → Store PeerAddr FreshPeer → IGEvent
  inactivityTimeout : IGEvent
