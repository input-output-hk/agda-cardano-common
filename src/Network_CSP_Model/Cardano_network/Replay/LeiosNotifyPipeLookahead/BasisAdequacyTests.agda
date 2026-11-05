{-# OPTIONS --safe #-}

-- Actual fresh runs exercise both hidden fallback replacement and exact observed payload fixing.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacyTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacy Bool Bool as Adequacy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverTests as Existing

-- This input exposes no normal value, so the sole explicitly chosen fallback is enough.
reference : List D.Event
reference = D.serverRecv D.request ∷ []

module Hidden = Adequacy.ForInput Bool._≟_ false reference

-- The finite basis contains an actual representative even when all payload choices are hidden.
one-fallback : Hidden.basis ≡ false ∷ []
one-fallback = refl

-- An unobserved normal value can collapse to the representative without changing the input.
unobserved-replacement : Hidden.retract true ≡ false
unobserved-replacement = refl

-- The original source may have chosen an entirely unobserved exact normal at EOF.
original : D.State
original = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false)
  [] [] (just D.request) nothing nothing nothing

-- This is an inhabited fresh source run, including registration, commit, decode and callback.
hidden-source : D.Run S.nodeNext D.initial reference original
hidden-source =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose refl refl)) D.stop

-- Every non-payload field and pending hook survives the transformed full run exactly.
replacement-target : Hidden.M.state original ≡ D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 (S.selected (S.normal false)) 0 false)
  [] [] (just D.request) nothing nothing nothing
replacement-target = refl

-- Adequacy constructs a real restricted run with the identical input and a renamed hidden choice.
hidden-restricted : Hidden.B.Run S.nodeNext D.initial reference (Hidden.M.state original)
hidden-restricted = Hidden.adequate hidden-source

-- Erasing membership recovers a second actual unrestricted fresh run of that same input.
hidden-original-language : D.Run S.nodeNext D.initial reference (Hidden.M.state original)
hidden-original-language = Hidden.B.sound hidden-restricted

-- The reference inventory may list records in a different order from an actual merged run.
visible-reference : List D.Event
visible-reference = D.clientSend D.request ∷ D.serverSend (D.reply (S.normal false)) ∷
  D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ []

module Visible = Adequacy.ForInput Bool._≟_ true visible-reference

-- An observed normal distinct from the fallback remains exact rather than being collapsed.
observed-fixed : Visible.retract false ≡ false
observed-fixed = refl

-- The delayed-record source list interleaves the fixed reference inventory in a different order.
delayed : List D.Event
delayed = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷
  D.clientSend D.request ∷ D.serverSend (D.reply (S.normal false)) ∷ []

-- Every row in the source merge belongs to the inventory, independently of its merge position.
covered : ∀ {row} → row ∈ delayed → row ∈ visible-reference
covered (here refl) = there (there (here refl))
covered (there (here refl)) = there (there (there (here refl)))
covered (there (there (here refl))) = here refl
covered (there (there (there (here refl)))) = there (here refl)
covered (there (there (there (there ()))))

-- The exact original endpoint preserves receive-before-send ordering under the fixed input basis.
visible-restricted : Visible.B.Run S.nodeNext D.initial delayed (Visible.M.state
  (D.pair
    (C.client C.poll (C.inspect (S.normal false)) [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing))
visible-restricted = Visible.adequate-covered covered Existing.delayed-send-records

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as EmptyDriver
import Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacy Bool ⊥ as EmptyAdequacy
module EmptyReturn = EmptyAdequacy.ForInput Bool._≟_ false []

-- Unlike new terminating source synthesis, renaming existing runs needs no inhabited Return carrier.
empty-return-prefix : EmptyReturn.B.Run S.genericNext EmptyDriver.initial [] EmptyDriver.initial
empty-return-prefix = EmptyReturn.adequate EmptyDriver.stop
