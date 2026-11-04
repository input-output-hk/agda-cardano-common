{-# OPTIONS --safe #-}

-- Structural progress of the final Done handoff, including every delayed-hook interleaving.
module Cardano_network.LeiosNotifyPipeLookahead.DoneProgress
  (Notification Return : Set) where

open import Data.Bool using (true)
open import Data.Integer using (ℤ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
open import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return

-- The client has drained all receiver work and retains its original return value.
awaiting : ℤ → Return → C.State
awaiting a x = C.client C.awaitDone C.idle [] [] 0 a true (just x)

-- Completion changes only the client control phase, not its arrival count or return.
returned : ℤ → Return → C.State
returned a x = C.client C.closed C.idle [] [] 0 a true (just x)

-- This constructor fixes the already-settled initiator direction and receiver work.
pair : C.State → S.State → Data.List.List D.ServerMessage →
  Data.Maybe.Maybe D.ServerMessage → Data.Maybe.Maybe D.ServerMessage → D.State
pair c s sc ps rc = D.pair c s [] sc nothing ps rc nothing

-- Seven structural states cover the physical Done packet and its two independent hooks.
data Handoff : D.State → Set where
  before : ∀ {a x} → Handoff
    (pair (awaiting a x) (S.state S.doneReady 0 S.idle 0 true) [] nothing nothing)
  queued-pending : ∀ {a x} → Handoff
    (pair (awaiting a x) (S.state S.doneReady 0 S.idle 0 true) (D.done ∷ []) (just D.done) nothing)
  queued-recorded : ∀ {a x} → Handoff
    (pair (awaiting a x) (S.state S.closed 0 S.idle 0 true) (D.done ∷ []) nothing nothing)
  decoded-pending : ∀ {a x} → Handoff
    (pair (awaiting a x) (S.state S.doneReady 0 S.idle 0 true) [] (just D.done) (just D.done))
  decoded-recorded : ∀ {a x} → Handoff
    (pair (awaiting a x) (S.state S.closed 0 S.idle 0 true) [] nothing (just D.done))
  received-pending : ∀ {a x} → Handoff
    (pair (returned a x) (S.state S.doneReady 0 S.idle 0 true) [] (just D.done) nothing)
  completed : ∀ {a x} → Handoff
    (pair (returned a x) (S.state S.closed 0 S.idle 0 true) [] nothing nothing)

-- Every state in the handoff is already in both peers' shutdown regions.
both-stopping : ∀ {s} → Handoff s → Work.BothStopping s
both-stopping before = refl , refl
both-stopping queued-pending = refl , refl
both-stopping queued-recorded = refl , refl
both-stopping decoded-pending = refl , refl
both-stopping decoded-recorded = refl , refl
both-stopping received-pending = refl , refl
both-stopping completed = refl , refl

-- All possible actual operations preserve the seven-state structural invariant.
preserved : ∀ {p s t} → Move p s t → Handoff s → Handoff t
preserved (wire (D.clientSent _)) ()
preserved (wire (D.serverReceived _)) ()
preserved (wire (D.serverSent {m = D.reply _} (S.send _))) ()
preserved (wire (D.serverSent {m = D.done} S.finish)) queued-pending = queued-recorded
preserved (wire (D.serverSent {m = D.done} S.finish)) decoded-pending = decoded-recorded
preserved (wire (D.serverSent {m = D.done} S.finish)) received-pending = completed
preserved (wire (D.clientReceived {m = D.reply _} (C.receivedReply _))) ()
preserved (wire (D.clientReceived {m = D.done} C.receivedDone)) decoded-pending = received-pending
preserved (wire (D.clientReceived {m = D.done} C.receivedDone)) decoded-recorded = completed
preserved (internal (D.clientInternal (C.registerResponse))) ()
preserved (internal (D.clientInternal (C.setStopIdle))) ()
preserved (internal (D.clientInternal (C.setStopBusy))) ()
preserved (internal (D.clientInternal (C.registerMarker))) ()
preserved (internal (D.clientInternal (C.optionalEmpty))) ()
preserved (internal (D.clientInternal (C.optionalResult))) ()
preserved (internal (D.clientInternal (C.blockingResult))) ()
preserved (internal (D.clientInternal (C.adjustArrival))) ()
preserved (internal (D.clientInternal (C.drainResult))) ()
preserved (internal (D.clientInternal (C.drained))) ()
preserved (internal (D.clientInternal (C.startResponse _))) ()
preserved (internal (D.clientInternal (C.startMarker _))) ()
preserved (internal (D.clientInternal (C.keepReply _))) ()
preserved (internal (D.clientInternal (C.discardReply _))) ()
preserved (internal (D.clientInternal (C.countArrival _))) ()
preserved (internal (D.clientInternal (C.publishResponse _))) ()
preserved (internal (D.clientInternal (C.publishMarker _))) ()
preserved (internal (D.serverInternal (S.admitted))) ()
preserved (internal (D.serverInternal (S.excessive))) ()
preserved (internal (D.serverInternal (S.registered))) ()
preserved (internal (D.serverInternal (S.setQuit))) ()
preserved (internal (D.serverInternal (S.claim _))) ()
preserved (internal (D.serverInternal (S.cancel _))) ()
preserved (internal (D.serverInternal (S.retire _))) ()
preserved (internal (D.serverInternal (S.flush))) ()
preserved (internal (D.serverInternal (S.drained))) ()
preserved (internal (D.serverInternal (S.abort))) ()
preserved (internal (D.clientCallback _ (C.continueZero))) ()
preserved (internal (D.clientCallback _ (C.continueBelow _))) ()
preserved (internal (D.clientCallback _ (C.continueFull _ _))) ()
preserved (internal (D.clientCallback _ (C.stopRequested))) ()
preserved (internal (D.clientCallback _ (C.delivered _))) ()
preserved (internal (D.serverCallback (S.choose _ _))) ()
preserved (internal (D.commitClient {m = D.request} C.sentRequest)) ()
preserved (internal (D.commitClient {m = D.quit} C.sentQuitIdle)) ()
preserved (internal (D.commitClient {m = D.quit} C.sentQuitBusy)) ()
preserved (internal (D.commitServer {m = D.reply _} (S.send _))) ()
preserved (internal (D.commitServer {m = D.done} S.finish)) before = queued-pending
preserved (internal (D.decodeClient {m = D.reply _} (C.receivedReply _))) ()
preserved (internal (D.decodeClient {m = D.done} C.receivedDone)) queued-pending = decoded-pending
preserved (internal (D.decodeClient {m = D.done} C.receivedDone)) queued-recorded = decoded-recorded
preserved (internal (D.decodeServer {m = D.request} (S.receiveRequest S.atFirst))) ()
preserved (internal (D.decodeServer {m = D.request} (S.receiveRequest S.atNext))) ()
preserved (internal (D.decodeServer {m = D.quit} (S.receiveQuit S.atFirst))) ()
preserved (internal (D.decodeServer {m = D.quit} (S.receiveQuit S.atNext))) ()

-- No unfinished state relies on an opaque enabledness or eventual-completion premise.
progress : ∀ {p s} → Handoff s → Clean s ⊎
  (¬ Clean s × Σ[ t ∈ D.State ] Move p s t)
progress before = inj₂ ((λ ()) , _ , internal (D.commitServer S.finish))
progress queued-pending = inj₂ ((λ ()) , _ , wire (D.serverSent S.finish))
progress queued-recorded = inj₂ ((λ ()) , _ , internal (D.decodeClient C.receivedDone))
progress decoded-pending = inj₂ ((λ ()) , _ , wire (D.serverSent S.finish))
progress decoded-recorded = inj₂ ((λ ()) , _ , wire (D.clientReceived C.receivedDone))
progress received-pending = inj₂ ((λ ()) , _ , wire (D.serverSent S.finish))
progress completed = inj₁ clean

-- The concrete handoff supplies both fields of the generic local-progress contract.
local-progress : ∀ p → LocalProgress p Clean Handoff
LocalProgress.preserve (local-progress p) = preserved
LocalProgress.ready (local-progress p) invariant _ = progress invariant

-- Model-level reachability and maximal-completion theorems are now fully instantiated here.
module HandoffCompletion (p : S.Contract) = With p Clean Handoff (local-progress p)
