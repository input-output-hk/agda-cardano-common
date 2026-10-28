{-# OPTIONS --guardedness #-}

-- Native Notify parameters retaining every normalized logger summary field.
module Cardano_network.Replay.LeiosNotifyExactParams where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Cardano_network.Params using (Params)
open import Cardano_network.Base using (lo; hi; N2N_LeiosNotify)
open import Cardano_network.Replay.ReplayParams using (replayParams)
import Cardano_network.Replay.LeiosNotifySession as Log
import Class.DecEq.Instances as DecEqI
open DecEqI using (DecEq-ℕ; DecEq-×; DecEq-Maybe)

-- A ranking-header representative stores precisely its optional announced EB summary.
announcedHash : Log.Announcement → Maybe ℕ
announcedHash nothing = nothing
announcedHash (just (h , s , z)) = just h

-- This separate instance changes opaque carriers, not native peer transition rules.
exactParams : Params
exactParams = record replayParams
  { Block = Log.Announcement
  ; VoteBlob = ℕ × ℕ
  ; Size = ℕ
  ; rbHash = λ _ → tt
  ; slotOf = λ _ → 0
  ; announcedEB = announcedHash
  ; txSize = λ _ → 0
  ; linkConfig = λ _ → (lo , N2N_LeiosNotify) ∷ (hi , N2N_LeiosNotify) ∷ []
  ; decBlock = DecEqI.DecEq-Maybe
      ⦃ DecEqI.DecEq-× ⦃ DecEqI.DecEq-ℕ ⦄
        ⦃ DecEqI.DecEq-× ⦃ DecEqI.DecEq-ℕ ⦄ ⦃ DecEqI.DecEq-ℕ ⦄ ⦄ ⦄
  ; decVoteBlob = DecEqI.DecEq-× ⦃ DecEqI.DecEq-ℕ ⦄ ⦃ DecEqI.DecEq-ℕ ⦄
  ; decSize = DecEqI.DecEq-ℕ }
