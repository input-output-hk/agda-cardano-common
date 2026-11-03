{-# OPTIONS --guardedness #-}

-- Computation and actual PTree moves for the new native lookahead producer.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NativeTests where

open import Data.Nat using (zero)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.Bool using (false; true)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI; fin; PTree; ret)
open import Cardano_network.Base using (hi; FromInitiator)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams using (leiosNotifyP; MsgLNPQuit; MsgLNPVotes)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; receiveLNP; sendLNP)
import Cardano_network.LeiosNotifyPipe replayParams as Old
import Cardano_network.LeiosNotifyPipeLookahead replayParams as Native
open Native.Reference
open Native.Machine nodeNext fzero hi
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.Tests
  using (selected-before-quit; two-normal-after-quit; canceled-drain; excessive-request)

-- A concrete selected native payload remains unchanged across reader Quit.
pending : State
pending = state awaitNext 0 (selected (normal (Old.votes []))) 0 false

-- The received Quit record enables a reader flag-update phase independently.
quitEvent : LTS.Event
quitEvent = LTS.evLabel _ (receiveLNP fzero hi)
  (tt , FromInitiator , tt , leiosNotifyP MsgLNPQuit)

-- This is an actual visible PTree move, not only an interpreter equality.
pending-quit : tree pending LTS.─[ LTS.ev (LTS.evl quitEvent) ]─►
  tree (state signalQuit 0 (selected (normal (Old.votes []))) 0 false)
pending-quit = LTS.sVis refl refl

-- The first finite internal choice publishes the shared quit flag.
publish-quit : tree (state signalQuit 0 (selected (normal (Old.votes []))) 0 false)
  LTS.─[ LTS.τ ]─► tree (state flushing 0 (selected (normal (Old.votes []))) 0 true)
publish-quit = LTS.sTau {i = (_ , fin {n = 1})} {a = lift fzero} refl refl

-- A preselected native reply can still be sent with the flag now true.
lateEvent : LTS.Event
lateEvent = LTS.evLabel _ (sendLNP fzero hi) (packet (MsgLNPVotes []))

-- The native tree exhibits the formerly rejected post-Quit ordinary send.
late-send : tree (state flushing 0 (selected (normal (Old.votes []))) 0 true)
  LTS.─[ LTS.ev (LTS.evl lateEvent) ]─► tree (state flushing 0 sent 0 true)
late-send = LTS.sVis refl refl

-- Failure and successful protocol completion have distinct return values.
failed-result : PTree.force (tree (state failed 0 idle 0 false)) ≡ ret Native.excessiveRequests
failed-result = refl
