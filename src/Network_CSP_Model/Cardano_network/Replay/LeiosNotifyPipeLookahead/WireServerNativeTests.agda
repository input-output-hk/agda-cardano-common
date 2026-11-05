{-# OPTIONS --guardedness #-}

-- Inhabited exact native payloads and explicit callback erasure for the new local server wire observation.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireServerNativeTests where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as W
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents exactParams as Events
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerEventsBridge exactParams as Encoding
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerBridgeTests as Examples
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireServerNative exactParams as Bridge
module B = Bridge.For S.nodeNext fzero hi
module G = Bridge.For S.genericNext fzero hi
module E = Encoding.For S.nodeNext fzero hi

-- Exact source observations keep an arbitrary selected notification across Quit.
selected-rows : Payloads.Notification → List W.Wire
selected-rows value = W.request ∷ W.quit ∷ W.reply (S.normal value) ∷ W.done ∷ []

-- Actual baseline source schedules inhabit the abstract fresh wire proposition.
selected-source : ∀ value → B.SourceTrace (selected-rows value)
selected-source value = _ , _ , Examples.selected-shutdown-source value , refl

-- No next/readiness event is forged away in the path: only its observation is erased.
selected-native : ∀ value → B.NativeTrace (selected-rows value)
selected-native value = B.realize (selected-source value)

-- All four concrete normal kinds retain nontrivial values, including duplicate ordered votes.
all-normal-kinds : All (λ value → B.NativeTrace (selected-rows value)) Examples.notifications
all-normal-kinds = selected-native _ ∷ selected-native _ ∷ selected-native _ ∷ selected-native _ ∷ []

-- Canonical native callback API events are explicitly unobserved by the wire profile.
next-erased : ∀ value → B.Observation.observe (Events.encode fzero hi (S.nextReply (S.normal value))) ≡ nothing
next-erased value = B.Observation.observe-decoded
  {event = Events.encode fzero hi (S.nextReply (S.normal value))}
  {action = S.nextReply (S.normal value)} (E.decode-encode (S.nextReply (S.normal value)))

-- Exact wire reply values are retained rather than collapsed to a message kind.
reply-retained : ∀ value → B.Observation.observe (Events.encode fzero hi (S.sendReply (S.normal value))) ≡
  just (W.reply (S.normal value))
reply-retained value = B.Observation.observe-decoded
  {event = Events.encode fzero hi (S.sendReply (S.normal value))}
  {action = S.sendReply (S.normal value)} (E.decode-encode (S.sendReply (S.normal value)))

-- Quit and Canceled followed by Done have an inhabited native observation too.
cancellation-native : B.NativeTrace (W.request ∷ W.quit ∷ W.reply S.canceled ∷ W.done ∷ [])
cancellation-native = B.realize (_ , _ , Examples.canceled-shutdown-source , refl)

-- Observed native traces invert to independent source witnesses at the exact profile.
roundtrip-source : ∀ value → B.SourceTrace (selected-rows value)
roundtrip-source value = B.sound (selected-native value)

-- A rejected admission can still share the same unfinished wire prefix; EOF is not a return result.
rejected-prefix-native : B.NativeTrace (W.request ∷ [])
rejected-prefix-native = B.realize (_ , _ , Examples.failure-source , refl)

-- The certified decider constructs native prefix evidence while a request is still unanswered.
pending-prefix-native : B.NativeTrace (W.request ∷ [])
pending-prefix-native = toWitness {a? = B.decide (W.request ∷ [])} _

-- Generic next can return Canceled before any Quit, with its callback erased only in observation.
generic-canceled-native : G.NativeTrace (W.request ∷ W.reply S.canceled ∷ [])
generic-canceled-native = toWitness {a? = G.decide (W.request ∷ W.reply S.canceled ∷ [])} _

-- The node-next profile rejects that entire native wire language, not merely one proposed schedule.
node-canceled-before-quit-impossible : B.NativeTrace (W.request ∷ W.reply S.canceled ∷ []) → ⊥
node-canceled-before-quit-impossible =
  toWitnessFalse {a? = B.decide (W.request ∷ W.reply S.canceled ∷ [])} _
