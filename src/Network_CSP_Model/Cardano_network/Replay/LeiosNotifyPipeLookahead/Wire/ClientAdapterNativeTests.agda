{-# OPTIONS --guardedness #-}

-- Summary-native equivalence preserves genuine fresh client EOF and shutdown witnesses.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapterNativeTests where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapterNative as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapterTests as Fixture

-- Arbitrary selected endpoint coordinates retain the same exact normalized-summary language.
module For (l : Link) (d : Dir) where
  module Native = Bridge.For l d

  -- Optional empty announcement realizes a true native Receive before the pending Request Send.
  early-native : Native.Accepted Log.client (A.present ((Log.Recv , Log.BlockAnnouncement nothing) ∷ []))
  early-native = Native.realize Fixture.receive-ahead-eof

  -- A native witness transports back to the independent source without changing its normalized rows.
  early-source : A.Accepted Log.client (A.present ((Log.Recv , Log.BlockAnnouncement nothing) ∷ []))
  early-source = Native.sound early-native

  -- Unit-return idle shutdown realizes the actual client Done path, rather than treating EOF as Done.
  idle-native : Native.Accepted Log.client (A.present ((Log.Send , Log.Quit) ∷ (Log.Recv , Log.Done) ∷ []))
  idle-native = Native.realize Fixture.idle-close

  -- Rejection covers every matching native path, not only canonical source realizations.
  lead-cannot-quit : Native.Accepted Log.client (A.present
    ((Log.Recv , Log.Canceled) ∷ (Log.Send , Log.Quit) ∷ [])) → ⊥
  lead-cannot-quit native = Fixture.lead-cannot-quit (Native.sound native)
