{-# OPTIONS --guardedness #-}

-- Native realizations of validated summary rows, at a fixed fresh standalone endpoint.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapterNative where

open import Data.List using (List; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as A
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireServerNative exactParams as Bridge

-- These parameters represent logger summaries, not full block bodies, signatures or timestamps.
module For (contract : S.Contract) (l : Link) (d : Dir) where
  module Native = Bridge.For contract l d

  -- Actual API-inclusive native traces retain every validated normalized wire row in order.
  Accepted : Log.Role → A.Input → Set₁
  Accepted role input = Σ[ rows ∈ List W.Wire ] (A.Valid role input rows × Native.NativeTrace rows)

  -- Realization still has exactly one observed wire row for each supplied input outcome.
  no-row-loss : ∀ {role input rows} → A.Valid role input rows → length rows ≡ length input
  no-row-loss (_ , mapping) = A.no-row-loss mapping

  -- Canonical native realization preserves exact summary fields, optional announcements and duplicate votes.
  realize : ∀ {role input} → A.Accepted contract role input → Accepted role input
  realize (rows , valid , source) = rows , valid , Native.realize source

  -- Native evidence implies a matching detailed server-source witness with the same lossless input mapping.
  sound : ∀ {role input} → Accepted role input → A.Accepted contract role input
  sound (rows , valid , native) = rows , valid , Native.sound native

  -- This equivalence concerns existential fresh-endpoint realizations, not decoding arbitrary raw native events.
  equivalence : ∀ role input →
    (A.Accepted contract role input → Accepted role input) ×
    (Accepted role input → A.Accepted contract role input)
  equivalence role input = realize , sound

  -- Total rejection refutes every matching native realization; EOF remains prefix acceptance.
  decide : (role : Log.Role) (input : A.Input) → Dec (Accepted role input)
  decide role input with A.decide contract role input
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)
