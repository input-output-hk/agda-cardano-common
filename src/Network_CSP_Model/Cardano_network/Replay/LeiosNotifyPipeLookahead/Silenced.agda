{-# OPTIONS --guardedness #-}

-- The silenced observation profile: the deployed logger hides RequestNext and Votes rows in both directions.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Silenced (p : Params) where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_,_)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe p as Payloads

-- Normal replies hidden by the profile: exactly the vote notifications.
isVotes : Payloads.Notification → Bool
isVotes (Payloads.votes _) = true
isVotes _ = false

-- Normalized log kinds that must be absent under the profile, whatever their direction.
hiddenKind : Log.E → Bool
hiddenKind (_ , Log.RequestNext) = true
hiddenKind (_ , Log.Votes _) = true
hiddenKind _ = false
