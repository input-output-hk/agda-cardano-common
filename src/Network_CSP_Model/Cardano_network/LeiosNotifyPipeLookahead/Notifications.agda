{-# OPTIONS --guardedness #-}

-- Shared exact native payloads and equality, independent of peers and replay.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.Notifications (p : Params) where

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Cardano_network.Data p
import Cardano_network.LeiosNotifyPipe p as Payloads
open Payloads using (Notification; announcement; offer; txsOffer; votes; message) public

-- The existing native-message injection distinguishes every notification value.
message-injective : ∀ {a b} → message a ≡ message b → a ≡ b
message-injective {announcement _} {announcement _} refl = refl
message-injective {offer _ _} {offer _ _} refl = refl
message-injective {txsOffer _} {txsOffer _} refl = refl
message-injective {votes _} {votes _} refl = refl
message-injective {announcement _} {offer _ _} ()
message-injective {announcement _} {txsOffer _} ()
message-injective {announcement _} {votes _} ()
message-injective {offer _ _} {announcement _} ()
message-injective {offer _ _} {txsOffer _} ()
message-injective {offer _ _} {votes _} ()
message-injective {txsOffer _} {announcement _} ()
message-injective {txsOffer _} {offer _ _} ()
message-injective {txsOffer _} {votes _} ()
message-injective {votes _} {announcement _} ()
message-injective {votes _} {offer _ _} ()
message-injective {votes _} {txsOffer _} ()

-- Selected payload equality reuses the existing native message instances.
notificationEq : DecidableEquality Notification
notificationEq a b with message a ≟ message b
... | yes eq = yes (message-injective eq)
... | no neq = no λ eq → neq (cong message eq)
