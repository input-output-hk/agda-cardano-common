{-# OPTIONS --safe #-}

-- Concrete decisions of the client language with silenced RequestNext and Votes rows.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientSilencedTests where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (True; False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Bool as W
open W using (request; quit; done; reply; normal; canceled)
open import Cardano_network.LeiosNotifyPipeLookahead.Wire.ClientSilenced Bool (λ b → b)

-- A visible reply is accepted first, although its RequestNext was silenced.
reply-first : True (decide-silenced (reply (normal false) ∷ []))
reply-first = tt

-- Graceful client shutdown: a normal reply, Quit, a cancellation and Done.
graceful : True (decide-silenced (reply (normal false) ∷ quit ∷ reply canceled ∷ done ∷ []))
graceful = tt

-- Done requires a preceding Quit.
done-before-quit-rejected : False (decide-silenced (done ∷ []))
done-before-quit-rejected = tt

-- Quit is sent at most once.
quit-twice-rejected : False (decide-silenced (quit ∷ quit ∷ []))
quit-twice-rejected = tt

-- A post-Quit drain may end at EOF as a prefix.
drain-eof-prefix : True (decide-silenced (quit ∷ reply canceled ∷ []))
drain-eof-prefix = tt

-- A hidden Votes row in the input is outside the silenced language.
hidden-reply-rejected : False (decide-silenced (reply (normal true) ∷ []))
hidden-reply-rejected = tt

-- An early reply followed by its delayed Request Send erases through Lead to the open phase.
lead-abstracted : SHasTrace opened (reply (normal false) ∷ [])
lead-abstracted = erase-complete (_ , W.step (W.earlyReply {m = normal false}) (W.step W.finishRequest W.stop))

-- The abstracted run of that Lead execution ends in the open phase.
lead-abstracted-target : proj₁ lead-abstracted ≡ opened
lead-abstracted-target = refl
