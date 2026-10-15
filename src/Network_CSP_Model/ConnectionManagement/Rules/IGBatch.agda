{-# OPTIONS --guardedness #-}

-- InboundGovernor.hs:242-278 at the fixed network pin. Pure batch-choice kernel,
-- not yet an IG worker or Machine action. Inputs must be computed by source
-- maturity/ordered peer-commit/timer guards in the same STM snapshot.
module ConnectionManagement.Rules.IGBatch where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (proj₁; proj₂)
import ConnectionManagement.Rules.InformationChannel as Channel

data Branch : Set where
  maturity peerCommit queued inactivity : Branch

record Selection (Event : Set) : Set where
  constructor selected
  field
    branch : Branch
    batch : List Event
    remaining : List Event
open Selection public

-- Preserve source FirstToFinish/STM alternative order. No arbitrary ready-peer
-- choice: firstCommit must already be the result of the source ordered fold.
selectBatch : ∀ {Event : Set} → Maybe Event → Maybe Event → Bool → Event → List Event → Maybe (Selection Event)
selectBatch (just event) firstCommit ready timeout queue =
  just (selected maturity (event ∷ proj₁ (Channel.readMessages queue)) (proj₂ (Channel.readMessages queue)))
selectBatch nothing (just event) ready timeout queue =
  just (selected peerCommit (event ∷ proj₁ (Channel.readMessages queue)) (proj₂ (Channel.readMessages queue)))
selectBatch nothing nothing ready timeout queue@(_ ∷ _) =
  just (selected queued (proj₁ (Channel.readMessages queue)) (proj₂ (Channel.readMessages queue)))
selectBatch nothing nothing true timeout [] = just (selected inactivity (timeout ∷ []) [])
selectBatch nothing nothing false timeout [] = nothing
