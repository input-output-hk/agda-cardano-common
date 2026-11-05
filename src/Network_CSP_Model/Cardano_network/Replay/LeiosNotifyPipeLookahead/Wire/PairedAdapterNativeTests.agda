{-# OPTIONS --guardedness #-}

-- Paired native witnesses preserve exact normalized payloads and both endpoint EOF orders.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapterNativeTests where

open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as P
import Cardano_network.LeiosNotifyPipeLookahead.Model P.Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapterNative as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapterTests as Fixture

-- Fixed links/directions are carried by the actual paired native product rather than inferred from timestamps.
module For (cl sl : Link) (cd sd : Dir) where
  module Native = Bridge.For S.genericNext cl sl cd sd
  module Node = Bridge.For S.nodeNext cl sl cd sd

  -- Empty server EOF remains valid after the client records one Request Send.
  request-native : Node.Accepted Log.client (A.present ((Log.Send , Log.RequestNext) ∷ [])) Log.server []
  request-native = Node.realize Fixture.request-server-eof

  -- The reverse race likewise has a native witness with its client Send hook pending.
  receive-native : Node.Accepted Log.client [] Log.server (A.present ((Log.Recv , Log.RequestNext) ∷ []))
  receive-native = Node.realize Fixture.receive-client-eof

  -- Exact offer fields survive typed normalization and the actual paired PTree realization.
  payload-native : Native.Accepted Log.client
    (A.present ((Log.Recv , Log.BlockOffer 17 23 31) ∷ [])) Log.server
    (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ []))
  payload-native = Native.realize Fixture.exact-payload

  -- Native soundness reconstructs an exact complete-summary source witness.
  payload-source : A.Accepted S.genericNext Log.client
    (A.present ((Log.Recv , Log.BlockOffer 17 23 31) ∷ [])) Log.server
    (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ []))
  payload-source = Native.sound payload-native

  -- Mismatching retained hash fields exclude every matching paired native execution.
  payload-mismatch : Native.Accepted Log.client
    (A.present ((Log.Recv , Log.BlockOffer 19 23 31) ∷ [])) Log.server
    (A.present ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.BlockOffer 17 23 31) ∷ [])) → ⊥
  payload-mismatch native = Fixture.payload-mismatch (Native.sound native)
