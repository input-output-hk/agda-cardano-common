{-# OPTIONS --guardedness #-}

-- Prefix operations that can retry before a start tracer forces its descriptor.
-- Pin 96ee6e0e: InboundGovernor.hs:647-676. This helper is pure: successful
-- capacity probes do not publish a partial AwakeRemote or counter update.
module ConnectionManagement.Rules.TracerReadiness where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Nat using (zero)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (IGEvent; awakeRemote)
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InformationChannel as Channel

-- The initial AwakeRemote write precedes descriptor evaluation only when both
-- source counters are zero. Probe one message, not the eventual complete burst.
awakeReady : ConnectionKey → M.Counters → List IGEvent → Bool
awakeReady k (M.counters (+ zero) (+ zero)) queue with Channel.writeMessage (awakeRemote k) queue
... | nothing = false
... | just _ = true
awakeReady k rc queue = true

-- Apply only before descriptor classification in an active tracer callback.
-- Started traces first inspect RemoteIdle expiry and then the AwakeRemote prefix.
-- Completed traces have neither prefix: InformationChannel's strict argument
-- forces Terminated's strict descriptor before capacity retry (source
-- InboundGovernor.hs:689-695,930-937; InformationChannel.hs:47).
prefixReady : ConnectionKey → M.Trace → Maybe M.View → Maybe M.Counters → List IGEvent → Bool
prefixReady k (M.started n) (just v) (just rc) queue with M.idleExpired v
... | true = false
... | false = awakeReady k rc queue
prefixReady k tr view counters queue = true
