{-# OPTIONS --safe #-}

-- Restrict only new normal callback selections to a declared finite payload list.
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.DriverBasis
  (Notification Return : Set) (basis : List Notification) where

open import Data.List using ([]; _∷_; _++_; _∷ʳ_)
open import Data.Maybe using (nothing; just)
open import Data.List.Membership.Propositional using (_∈_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- Cancellation remains a control reply; a normal selection needs actual basis membership.
data AllowedReply : S.Reply → Set where
  allowNormal : ∀ {value} → value ∈ basis → AllowedReply (S.normal value)
  allowCanceled : AllowedReply S.canceled

-- Visible driver records retain the independent original rules and every exact field.
Step : S.Contract → D.State → D.Event → D.State → Set
Step = D.Step

-- All source scheduling/transport operations remain, with one explicit callback restriction.
data Tau (contract : S.Contract) : D.State → D.State → Set where
  clientInternal : ∀ {c c′ s cs sc pc ps rc rs} → C.Tau c c′ →
    Tau contract (D.pair c s cs sc pc ps rc rs) (D.pair c′ s cs sc pc ps rc rs)
  serverInternal : ∀ {c s s′ cs sc pc ps rc rs} → S.Tau s s′ →
    Tau contract (D.pair c s cs sc pc ps rc rs) (D.pair c s′ cs sc pc ps rc rs)
  clientCallback : ∀ {c c′ s cs sc pc ps rc rs action} →
    D.ClientCallback action → C.Step c action c′ →
    Tau contract (D.pair c s cs sc pc ps rc rs) (D.pair c′ s cs sc pc ps rc rs)
  serverCallback : ∀ {c s s′ cs sc pc ps rc rs reply} →
    AllowedReply reply → S.Step contract s (S.nextReply reply) s′ →
    Tau contract (D.pair c s cs sc pc ps rc rs) (D.pair c s′ cs sc pc ps rc rs)
  commitClient : ∀ {c c′ s cs sc ps rc rs message} →
    C.Step c (D.clientSendAction message) c′ →
    Tau contract (D.pair c s cs sc nothing ps rc rs)
      (D.pair c s (cs ∷ʳ message) sc (just message) ps rc rs)
  commitServer : ∀ {c s s′ cs sc pc rc rs message} →
    S.Step contract s (D.serverSendAction message) s′ →
    Tau contract (D.pair c s cs sc pc nothing rc rs)
      (D.pair c s cs (sc ∷ʳ message) pc (just message) rc rs)
  decodeClient : ∀ {c c′ s cs sc pc ps rs message} →
    C.Step c (D.clientRecvAction message) c′ →
    Tau contract (D.pair c s cs (message ∷ sc) pc ps nothing rs)
      (D.pair c s cs sc pc ps (just message) rs)
  decodeServer : ∀ {c s s′ cs sc pc ps rc message} →
    S.Step contract s (D.serverRecvAction message) s′ →
    Tau contract (D.pair c s (message ∷ cs) sc pc ps rc nothing)
      (D.pair c s cs sc pc ps rc (just message))

-- Every restricted hidden move is the same actual source move after erasing membership evidence.
sound-tau : ∀ {contract s t} → Tau contract s t → D.Tau contract s t
sound-tau (clientInternal step) = D.clientInternal step
sound-tau (serverInternal step) = D.serverInternal step
sound-tau (clientCallback classification step) = D.clientCallback classification step
sound-tau (serverCallback _ step) = D.serverCallback step
sound-tau (commitClient step) = D.commitClient step
sound-tau (commitServer step) = D.commitServer step
sound-tau (decodeClient step) = D.decodeClient step
sound-tau (decodeServer step) = D.decodeServer step

-- Restricted finite prefixes preserve the exact original visible event list.
data Run (contract : S.Contract) : D.State → List D.Event → D.State → Set where
  stop : ∀ {s} → Run contract s [] s
  internal : ∀ {s t u events} → Tau contract s t → Run contract t events u →
    Run contract s events u
  visible : ∀ {s t u event events} → Step contract s event t → Run contract t events u →
    Run contract s (event ∷ events) u

-- Acceptance in the basis model always supplies a genuine unrestricted source prefix.
sound : ∀ {contract s events t} → Run contract s events t → D.Run contract s events t
sound stop = D.stop
sound (internal step run) = D.internal (sound-tau step) (sound run)
sound (visible step run) = D.visible step (sound run)

-- Basis runs compose without altering the selected payloads or visible order.
append : ∀ {contract s t u events later} → Run contract s events t →
  Run contract t later u → Run contract s (events ++ later) u
append stop rest = rest
append (internal step run) rest = internal step (append run rest)
append (visible step run) rest = visible step (append run rest)
