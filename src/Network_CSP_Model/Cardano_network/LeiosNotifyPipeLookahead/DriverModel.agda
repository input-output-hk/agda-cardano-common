{-# OPTIONS --safe #-}

-- Message-level product of the pinned peers and the actual driver trace boundary.
-- Channel commits and decoded packets precede their corresponding visible records.
module Cardano_network.LeiosNotifyPipeLookahead.DriverModel
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C

-- Only the two initiator messages have client-to-server agency.
data ClientMessage : Set where
  request quit : ClientMessage

-- Responder messages are owed replies or the final Done acknowledgment.
data ServerMessage : Set where
  reply : S.Reply → ServerMessage
  done : ServerMessage

-- Driver records preserve endpoint identity and exact message payloads.
data Event : Set where
  clientSend serverRecv : ClientMessage → Event
  serverSend clientRecv : ServerMessage → Event

-- Callback actions are hidden by the driver-record observation.
data ClientCallback : C.Action → Set where
  continue : ∀ {k} → ClientCallback (C.continue k)
  terminate : ∀ {x} → ClientCallback (C.terminate x)
  handled : ∀ {m} → ClientCallback (C.handled m)

-- Each driver call can have a packet committed or decoded before its trace hook.
record State : Set where
  constructor pair
  field
    clientState : C.State
    serverState : S.State
    clientToServer : List ClientMessage
    serverToClient : List ServerMessage
    pendingClientSend : Maybe ClientMessage
    pendingServerSend : Maybe ServerMessage
    pendingClientRecv : Maybe ServerMessage
    pendingServerRecv : Maybe ClientMessage
open State public

-- Fresh paired captures start before either peer has acted.
initial : State
initial = pair C.initial S.initial [] [] nothing nothing nothing nothing

-- Message operations map back to the appropriate endpoint's source action.
clientSendAction : ClientMessage → C.Action
clientSendAction request = C.sendRequest
clientSendAction quit = C.sendQuit

-- The reader continuation consumes its command only after the Receive trace hook.
serverRecvAction : ClientMessage → S.Action
serverRecvAction request = S.recvRequest
serverRecvAction quit = S.recvQuit

-- Reply and Done use different receiver paths in the pipelined client.
clientRecvAction : ServerMessage → C.Action
clientRecvAction (reply m) = C.recvReply m
clientRecvAction done = C.recvDone

-- The server finishes a selected reply or its final main-thread Done send.
serverSendAction : ServerMessage → S.Action
serverSendAction (reply m) = S.sendReply m
serverSendAction done = S.sendDone

-- A record completes the corresponding driver operation; it moves no packet twice.
data Step (contract : S.Contract) : State → Event → State → Set where
  clientSent : ∀ {c c′ s cs sc m ps rc rs} → C.Step c (clientSendAction m) c′ →
    Step contract (pair c s cs sc (just m) ps rc rs) (clientSend m)
      (pair c′ s cs sc nothing ps rc rs)
  serverSent : ∀ {c s s′ cs sc pc m rc rs} → S.Step contract s (serverSendAction m) s′ →
    Step contract (pair c s cs sc pc (just m) rc rs) (serverSend m)
      (pair c s′ cs sc pc nothing rc rs)
  clientReceived : ∀ {c c′ s cs sc pc ps m rs} → C.Step c (clientRecvAction m) c′ →
    Step contract (pair c s cs sc pc ps (just m) rs) (clientRecv m)
      (pair c′ s cs sc pc ps nothing rs)
  serverReceived : ∀ {c s s′ cs sc pc ps rc m} → S.Step contract s (serverRecvAction m) s′ →
    Step contract (pair c s cs sc pc ps rc (just m)) (serverRecv m)
      (pair c s′ cs sc pc ps rc nothing)

-- Internal scheduling includes source callbacks and independent transport progress.
data Tau (contract : S.Contract) : State → State → Set where
  clientInternal : ∀ {c c′ s cs sc pc ps rc rs} → C.Tau c c′ →
    Tau contract (pair c s cs sc pc ps rc rs) (pair c′ s cs sc pc ps rc rs)
  serverInternal : ∀ {c s s′ cs sc pc ps rc rs} → S.Tau s s′ →
    Tau contract (pair c s cs sc pc ps rc rs) (pair c s′ cs sc pc ps rc rs)
  clientCallback : ∀ {c c′ s cs sc pc ps rc rs a} → ClientCallback a → C.Step c a c′ →
    Tau contract (pair c s cs sc pc ps rc rs) (pair c′ s cs sc pc ps rc rs)
  serverCallback : ∀ {c s s′ cs sc pc ps rc rs m} → S.Step contract s (S.nextReply m) s′ →
    Tau contract (pair c s cs sc pc ps rc rs) (pair c s′ cs sc pc ps rc rs)
  commitClient : ∀ {c c′ s cs sc ps rc rs m} → C.Step c (clientSendAction m) c′ →
    Tau contract (pair c s cs sc nothing ps rc rs)
      (pair c s (cs ∷ʳ m) sc (just m) ps rc rs)
  commitServer : ∀ {c s s′ cs sc pc rc rs m} → S.Step contract s (serverSendAction m) s′ →
    Tau contract (pair c s cs sc pc nothing rc rs)
      (pair c s cs (sc ∷ʳ m) pc (just m) rc rs)
  decodeClient : ∀ {c c′ s cs sc pc ps rs m} → C.Step c (clientRecvAction m) c′ →
    Tau contract (pair c s cs (m ∷ sc) pc ps nothing rs)
      (pair c s cs sc pc ps (just m) rs)
  decodeServer : ∀ {c s s′ cs sc pc ps rc m} → S.Step contract s (serverRecvAction m) s′ →
    Tau contract (pair c s (m ∷ cs) sc pc ps rc nothing)
      (pair c s cs sc pc ps rc (just m))

-- Finite driver executions retain exactly the supplied visible record order.
data Run (contract : S.Contract) : State → List Event → State → Set where
  stop : ∀ {s} → Run contract s [] s
  internal : ∀ {s t u es} → Tau contract s t → Run contract t es u → Run contract s es u
  visible : ∀ {s t u e es} → Step contract s e t → Run contract t es u →
    Run contract s (e ∷ es) u
