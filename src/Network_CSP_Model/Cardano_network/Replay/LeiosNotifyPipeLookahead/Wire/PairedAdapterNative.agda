{-# OPTIONS --guardedness #-}

-- Exact normalized summary acceptance is equivalent to a fresh paired native driver prefix.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapterNative where

open import Data.List using (List)
open import Data.Unit using (⊤)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Payloads.Notification ⊤ as R
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative exactParams as Bridge

-- Link/direction coordinates and successful server callback contract stay explicit and fixed.
module For (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  module Native = Bridge.At contract cl sl cd sd

  -- Every summary outcome has an exact typed row and a genuine initial paired PTree witness.
  Accepted : Log.Role → A.Input → Log.Role → A.Input → Set₁
  Accepted cr ci sr si = Σ[ client ∈ List R.ClientRow ] Σ[ server ∈ List R.ServerRow ]
    (A.Valid cr ci sr si client server × Native.NativeTrace client server)

  -- The unrestricted source witness gives a concrete native event list and an exact merge.
  realize : ∀ {cr ci sr si} → A.Accepted contract cr ci sr si → Accepted cr ci sr si
  realize (client , server , valid , source) = client , server , valid , Native.realize source

  -- Every matching actual native trace reconstructs the same lossless normalized input language.
  sound : ∀ {cr ci sr si} → Accepted cr ci sr si → A.Accepted contract cr ci sr si
  sound (client , server , valid , native) = client , server , valid , Native.sound native

  -- Equality concerns normalized-summary carriers, not full runtime blocks, signatures or timestamps.
  equivalence : ∀ cr ci sr si →
    (A.Accepted contract cr ci sr si → Accepted cr ci sr si) ×
    (Accepted cr ci sr si → A.Accepted contract cr ci sr si)
  equivalence cr ci sr si = realize , sound

  -- Invalid input and exhaustive source rejection both refute every matching native realization.
  decide : (cr : Log.Role) (ci : A.Input) (sr : Log.Role) (si : A.Input) → Dec (Accepted cr ci sr si)
  decide cr ci sr si with A.decide contract cr ci sr si
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)
