{-# OPTIONS --guardedness #-}

-- Explicit inhabited traces for both original peer correspondence endpoints.
module Cardano_network.Replay.LeiosNotifyBridgeTests where

open import Data.List using (List; map)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Cardano_network.Replay.LeiosNotifySession
open import Cardano_network.Replay.LeiosNotifyTests using (rounds; rounds-run)
open import Cardano_network.Replay.LeiosNotifyBridge using (It; step; Obs; complete)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; stIdle)
open import Process_Trees using (ExtI)
open import Semantics.Deadlock {E = LNPEv} {I = ExtI LNPEv} using (_⟹∖√⟨_⟩_)

-- The client witness visits every notification kind, then closes.
client-run : ∃[ t ] ∃[ M ] (It client (step client stIdle) ⟹∖√⟨ t ⟩ M × Obs t rounds)
client-run = complete client rounds-run

-- Reverse wire directions to obtain the corresponding responder trace.
reverse : E → E
reverse (Send , m) = Recv , m
reverse (Recv , m) = Send , m

-- The responder accepts the same sequence of protocol rounds.
server-ok : True (Spec.check server (map reverse rounds))
server-ok = tt

-- Completeness constructs an actual original-server trace, not an empty premise.
server-run : ∃[ t ] ∃[ M ] (It server (step server stIdle) ⟹∖√⟨ t ⟩ M × Obs t (map reverse rounds))
server-run = complete server (toWitness {a? = Spec.check server (map reverse rounds)} server-ok)
