{-# OPTIONS --guardedness #-}

-- Exact full node-policy product. Native wire records and explicit policy inputs
-- remain distinct. Input readiness/eligibility values are model witnesses,
-- not observations certified by wire logs or proofs of deployed STM/ledger state.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverNetwork (p : Params) where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing; map; _>>=_)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (⊤)
open import Process_Trees using (PTree; AnyTypes; ContinueType; react)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p using (Notification; notificationEq)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverExecution Notification notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p ⊤ as Wire
import Semantics.LTS
import Semantics.Deadlock

-- Application/environment inputs cannot masquerade as a native wire record.
data Input : Set where
  forecast termination : Bool → Input
  eligible handledNormal : Notification → Input
  rejectedCancel : Input

-- The full unchanged source action is retained by each non-wire input.
action : Input → Node.Action
action (forecast ready) = Node.setForecast ready
action (termination requested) = Node.setTerminate requested
action (eligible notification) = Node.eligible notification
action (handledNormal notification) = Node.handledNormal notification
action rejectedCancel = Node.rejectedCancel

-- Existing endpoint-tagged native LNPEv channels are reused without payload erasure.
data Events : Set → Set₁ where
  wire : ∀ {A} → Wire.Events A → Events A
  policyInput : Events Input

-- Scheduler selectors carry operation data rather than externally supplied proofs.
data Branches : Set → Set₁ where
  schedule : Branches Exec.Choice

-- A local client fault is held in Node.State; it does not terminate the server.
Proc : Set₁
Proc = PTree Events Branches ⊥

-- Native event/transition semantics belongs to this distinct policy alphabet.
module LTS = Semantics.LTS {E = Events} {I = Branches}

-- Finite prefixes exclude a global termination tick, matching Node.Run.
module Traces = Semantics.Deadlock {E = Events} {I = Branches}

-- Wire-only observation hides precisely the explicit environment/application inputs.
wireAction : Node.Action → Maybe D.Event
wireAction (Node.wire row) = just row
wireAction _ = nothing

-- Coordinates remain fixed across the entire paired policy run.
module At (cl sl : Link) (cd sd : Dir) where
  module W = Wire.At S.nodeNext cl sl cd sd

  -- Wrapping a native event preserves its original carrier, channel and value.
  wireEvent : Wire.LTS.Event → LTS.Event
  wireEvent (Wire.LTS.evLabel A channel value) = LTS.evLabel A (wire channel) value

  -- The policy channel has one explicit input value per source action.
  inputEvent : Input → LTS.Event
  inputEvent value = LTS.evLabel Input policyInput value

  -- Only existing canonical wire decoding and the independent policy channel are accepted.
  decode : LTS.Event → Maybe Node.Action
  decode (LTS.evLabel A (wire channel) value) = map Node.wire (W.decode (Wire.LTS.evLabel A channel value))
  decode (LTS.evLabel _ policyInput value) = just (action value)

  -- All full source actions have native realizations, including abnormal Cancel handling.
  encode : Node.Action → LTS.Event
  encode (Node.wire row) = wireEvent (W.encode row)
  encode (Node.setForecast ready) = inputEvent (forecast ready)
  encode (Node.setTerminate requested) = inputEvent (termination requested)
  encode (Node.eligible notification) = inputEvent (eligible notification)
  encode (Node.handledNormal notification) = inputEvent (handledNormal notification)
  encode Node.rejectedCancel = inputEvent rejectedCancel

  -- Wire replay sees the original driver rows while policy witnesses remain explicit in full traces.
  observe : LTS.Event → Maybe D.Event
  observe event = decode event >>= wireAction

  -- Full state, including queue, forecast, termination and failed-client flag, is preserved.
  next : Node.State → LTS.Event → Maybe Node.State
  next state event with decode event
  ... | nothing = nothing
  ... | just input = map proj₁ (Exec.visible-step state input)

  -- Forward declarations keep actual wire offers and hidden progress concurrent.
  tree : Node.State → Proc
  offers : (state : Node.State) (at : AnyTypes Events) → ContinueType at (Maybe Proc)
  branches : (state : Node.State) (at : AnyTypes Branches) → ContinueType at (Maybe Proc)

  -- Node.Run has no global return rule, even after local close or client failure.
  PTree.force (tree state) = react (offers state) (branches state)

  -- Every offered event is justified by one complete executable source selector.
  offers state (A , channel) value with next state (LTS.evLabel A channel value)
  ... | nothing = nothing
  ... | just target = just (tree target)

  -- All hidden node transactions retain their full queue and policy guards.
  branches state (_ , schedule) choice with Exec.hidden-step state choice
  ... | nothing = nothing
  ... | just (target , proof) = just (tree target)

  -- Fresh policy execution begins with blocked forecast and no requested termination.
  node : Proc
  node = tree Node.initial
