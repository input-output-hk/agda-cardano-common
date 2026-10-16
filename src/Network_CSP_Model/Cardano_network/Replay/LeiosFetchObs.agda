{-# OPTIONS --guardedness #-}

-- What the log observes of a model event (trace-replay Phase 5, amendment B3).
-- `E♭` keeps message kind, hash and slot (Block keeps the hash only) and
-- forgets sizes, numTxs and bitmaps; `forget` maps a spec event onto it.
-- Two classifiers: `clsS` on the renamed server alphabet (`Net_Api`, where
-- `input` = the peer sends, `output` = it receives) and `clsC` on the
-- client's `LFPEv`.  Everything else (`apiLP`, `store`, `env`, `done`, …) is
-- unlogged: `nothing`.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchObs where

open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import Process_Trees using (ExtI)
open import Cardano_network.Base using (N2N_LeiosFetch)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams using (Net_Api; input; output)
open import Cardano_network.Data replayParams
  using ( Payload; Messages; leiosFetchP; MessageLeiosFetchP
        ; MsgLFPBlockRequest; MsgLFPBlock; MsgLFPBlockTxsRequest; MsgLFPBlockTxs; MsgLFPDone )
import Cardano_network.LeiosFetchP replayParams as LFP
import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as LTSS
import Semantics.LTS {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as LTSC
import Semantics.Replay.Bridge {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as BrS
import Semantics.Replay.Bridge {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as BrC
open import Cardano_network.Replay.LeiosFetchSession
  using (Direction; Send; Recv; Msg; E
        ; MsgLeiosBlockRequest; MsgLeiosBlock; MsgLeiosBlockTxsRequest; MsgLeiosBlockTxs
        ; MsgLeiosDone)

-- a LeiosFetch message as far as the replay can compare it
data Msg♭ : Set where
  -- BlockRequest (ebHash, ebSlot)
  blockReq♭ : (h s : ℕ) → Msg♭
  -- Block ebHash
  block♭    : (h : ℕ) → Msg♭
  -- BlockTxsRequest (ebHash, ebSlot)
  txsReq♭   : (h s : ℕ) → Msg♭
  -- BlockTxs (ebHash, ebSlot)
  txs♭      : (h s : ℕ) → Msg♭
  -- Done
  done♭     : Msg♭

-- an observed event: direction and abstract message
E♭ : Set
E♭ = Direction × Msg♭

-- the observable part of a spec (log-level) event
forget : E → E♭
forget (d , MsgLeiosBlockRequest h s)        = d , blockReq♭ h s
forget (d , MsgLeiosBlock h _)               = d , block♭ h
forget (d , MsgLeiosBlockTxsRequest h s _ _) = d , txsReq♭ h s
forget (d , MsgLeiosBlockTxs h s _ _ _)      = d , txs♭ h s
forget (d , MsgLeiosDone)                    = d , done♭

-- the observable part of a model wire message (`ebHash = id` at `replayParams`)
msg♭ : MessageLeiosFetchP → Msg♭
msg♭ (MsgLFPBlockRequest (h , s))      = blockReq♭ h s
msg♭ (MsgLFPBlock eb)                  = block♭ eb
msg♭ (MsgLFPBlockTxsRequest (h , s) _) = txsReq♭ h s
msg♭ (MsgLFPBlockTxs (h , s) _)        = txs♭ h s
msg♭ MsgLFPDone                        = done♭

-- the observable part of a LeiosFetch payload, if it is one
pay♭ : Direction → Payload → Maybe E♭
pay♭ d (_ , _ , _ , leiosFetchP m) = just (d , msg♭ m)
pay♭ d _                           = nothing

-- classify a renamed-server event: LeiosFetch wire I/O is logged, all else is silent
clsS : LTSS.Event → Maybe E♭
clsS (LTSS.evLabel _ (input  _ _ N2N_LeiosFetch) a) = pay♭ Send a
clsS (LTSS.evLabel _ (output _ _ N2N_LeiosFetch) a) = pay♭ Recv a
clsS _                                              = nothing

-- classify a client (`LFPEv`) event: wire I/O is logged, api/done are silent
clsC : LTSC.Event → Maybe E♭
clsC (LTSC.evLabel _ (LFP.sendLFP    _ _) a) = pay♭ Send a
clsC (LTSC.evLabel _ (LFP.receiveLFP _ _) a) = pay♭ Recv a
clsC _                                       = nothing

-- B3's `Obs` on the server side: the log sees exactly `es` (up to `forget`)
ObsS : List LTSS.Event → List E → Set
ObsS = BrS.Obs clsS forget

-- B3's `Obs` on the client side
ObsC : List LTSC.Event → List E → Set
ObsC = BrC.Obs clsC forget
