{-# OPTIONS --guardedness #-}

-- Inhabited exact native client observations with API deletion and receive-before-send prefixes.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.WireClientNativeTests where

open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; mapMaybe)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
open import Cardano_network.LeiosNotifyP exactParams using (apiLPev)
open import Cardano_network.Net exactParams using (lnpRecvBlockOffer)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ℕ as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork exactParams ℕ as N
import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents exactParams ℕ N.Branches as E
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientEventsBridge exactParams ℕ as Encoding
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientNetworkTests as Existing
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.WireClientNative exactParams ℕ as Bridge
module B = Bridge.At fzero hi
module Canonical = Encoding.At fzero hi
module Native = N.At fzero hi
module Events = E.At fzero hi

-- All four data constructors retain nontrivial exact fields, including ordered duplicate votes.
notifications : List Notification
notifications =
  announcement (header (just (31 , 37 , 41))) ∷
  offer (43 , 47) 53 ∷
  txsOffer (59 , 61) ∷
  votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []) ∷ []

-- The exact old source fixture contains a visible normal delivery API action.
early-actions : List C.Action
early-actions = C.continue (+ 1) ∷ C.recvReply (S.normal Existing.sample) ∷
  C.handled (S.normal Existing.sample) ∷ C.sendRequest ∷ []

-- An actual pre-existing native path retains the API event while deleting it from wire observation.
early-native : B.NativeTrace (W.reply (S.normal Existing.sample) ∷ W.request ∷ [])
early-native = Native.project early-actions , _ , Existing.reply-before-send-native ,
  trans (B.Observation.canonical-observation early-actions) (sym (Bridge.wire-mapMaybe early-actions))

-- Soundness inverts this actual API-inclusive native execution into exact source evidence.
early-path-source : B.SourceTrace (W.reply (S.normal Existing.sample) ∷ W.request ∷ [])
early-path-source = B.sound early-native

-- Every exact supplied normal kind has a concrete native receive-ahead and graceful shutdown witness.
normal-round : (value : Notification) → B.NativeTrace
  (W.reply (S.normal value) ∷ W.request ∷ W.quit ∷ W.done ∷ [])
normal-round value = toWitness {a? = B.decide 73 _} _

-- Notification kinds are never replaced by a single representative in native observation transport.
all-normal-kinds : All (λ value → B.NativeTrace
  (W.reply (S.normal value) ∷ W.request ∷ W.quit ∷ W.done ∷ [])) notifications
all-normal-kinds = normal-round _ ∷ normal-round _ ∷ normal-round _ ∷ normal-round _ ∷ []

-- A canonical visible native event has the exact source observation declared by the wire profile.
observe-canonical : ∀ {action event} → Events.observe action ≡ just event →
  B.Observation.observe event ≡ Bridge.Wire.observe action
observe-canonical {action} {event} observed = B.Observation.observe-decoded
  {event = event} {action = action} (Canonical.decode-observe {a = action} {e = event} observed)

-- Visible successful normal handler APIs are erased only in the final wire projection.
normal-handler-erased : ∀ {value event} → Events.observe (C.handled (S.normal value)) ≡ just event →
  B.Observation.observe event ≡ nothing
normal-handler-erased {value} {event} observed = observe-canonical
  {action = C.handled (S.normal value)} {event = event} observed

-- The concrete offer-handler API event is present in early-native and has an inhabited erasure proof.
sample-handler-erased : B.Observation.observe
  (N.LTS.evLabel _ (apiLPev fzero hi lnpRecvBlockOffer) ((43 , 47) , 53)) ≡ nothing
sample-handler-erased = normal-handler-erased {value = Existing.sample} refl

-- All exact native incoming reply fields survive the final wire observation.
reply-retained : ∀ {value event} → Events.observe (C.recvReply value) ≡ just event →
  B.Observation.observe event ≡ just (W.reply value)
reply-retained {value} {event} observed = observe-canonical {action = C.recvReply value} {event = event} observed

-- This real source schedule keeps a normal handler selected before Quit and invokes it afterward.
late-actions : List C.Action
late-actions = C.continue (+ 1) ∷ C.sendRequest ∷ C.recvReply (S.normal Existing.sample) ∷
  C.terminate 73 ∷ C.sendQuit ∷ C.handled (S.normal Existing.sample) ∷ C.recvDone ∷ []

-- The native path includes the late API event while the wire history retains only protocol messages.
late-handler-native : B.NativeTrace
  (W.request ∷ W.reply (S.normal Existing.sample) ∷ W.quit ∷ W.done ∷ [])
late-handler-native = Native.project late-actions , _ , Existing.handler-after-quit-native ,
  trans (B.Observation.canonical-observation late-actions) (sym (Bridge.wire-mapMaybe late-actions))

-- Canceled before Quit is allowed by the generic successful handler profile, including its quiet callback.
generic-canceled-native : B.NativeTrace
  (W.reply S.canceled ∷ W.request ∷ W.quit ∷ W.done ∷ [])
generic-canceled-native = toWitness {a? = B.decide 73 _} _

-- Busy shutdown may receive a normal and cancellation with exact independent source realizations.
pipeline-native : B.NativeTrace
  (W.request ∷ W.request ∷ W.quit ∷ W.reply (S.normal Existing.sample) ∷ W.reply S.canceled ∷ W.done ∷ [])
pipeline-native = toWitness {a? = B.decide 73 _} _

-- EOF immediately after a reply is a native Lead prefix, not a returned client.
early-eof-native : B.NativeTrace (W.reply (S.normal Existing.sample) ∷ [])
early-eof-native = toWitness {a? = B.decide 73 _} _

-- Rejection excludes every matching native path, not just a chosen source schedule.
two-leading-impossible : B.NativeTrace (W.reply S.canceled ∷ W.reply (S.normal Existing.sample) ∷ []) → ⊥
two-leading-impossible = toWitnessFalse {a? = B.decide 73 _} _

-- The main thread cannot send Quit before the pending Request Send hook returns.
quit-before-delayed-send-impossible : B.NativeTrace (W.reply (S.normal Existing.sample) ∷ W.quit ∷ []) → ⊥
quit-before-delayed-send-impossible = toWitnessFalse {a? = B.decide 73 _} _

-- No native Done observation can bypass the unreceived outstanding reply.
premature-done-impossible : B.NativeTrace (W.request ∷ W.quit ∷ W.done ∷ []) → ⊥
premature-done-impossible = toWitnessFalse {a? = B.decide 73 _} _

-- An initial native Done lacks the actual graceful shutdown source control.
initial-done-impossible : B.NativeTrace (W.done ∷ []) → ⊥
initial-done-impossible = toWitnessFalse {a? = B.decide 73 _} _
