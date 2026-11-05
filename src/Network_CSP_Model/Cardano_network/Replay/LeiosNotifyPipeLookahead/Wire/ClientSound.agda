{-# OPTIONS --safe #-}

-- Soundness for arbitrary return carriers and every initial generic client schedule.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientSound
  (Notification Return : Set) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as A
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Notification Return as R
import Cardano_network.LeiosNotifyPipeLookahead.ClientPhase Notification Return as P
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as Q
open Q.Observation Return

-- Before the Quit Send hook, the sender can already have accepted/published termination.
data Early : C.Main → Set where
  poll : Early C.poll
  issue : Early C.issue
  writing : Early C.writingRequest
  maybeCollect : Early C.collectingMaybe
  waitCollect : Early C.collectingWait
  adjust : Early C.adjustCollected
  stopPending : Early C.stopPending
  registerQuit : Early C.registerQuit
  writeQuit : ∀ {b} → Early (C.writingQuit b)

-- After the hook only the draining and AwaitDone controls remain.
data Late : C.Main → Set where
  draining : Late C.draining
  awaitDone : Late C.awaitDone

-- Ghost stages distinguish the observed Quit from its earlier local publication.
data Stage : Set where
  ordinary quitting ended : Stage

-- Control is independent of receiver resources and preserves their arbitrary schedules.
data Control : Stage → C.Main → Set where
  before : ∀ {m} → Early m → Control ordinary m
  after : ∀ {m} → Late m → Control quitting m
  finished : Control ended C.closed

-- A pending Request Send subtracts one registered reply credit, possibly yielding Lead.
balance : C.Main → ℕ → Q.State
balance C.writingRequest zero = Q.Lead
balance C.writingRequest (suc n) = Q.Open n
balance _ n = Q.Open n

-- The quotient observes exact owed replies corrected for the one unrecorded Request Send.
view : Stage → C.State → Q.State
view ordinary s = balance (C.main s) (R.owed s)
view quitting s = Q.QuitSeen (R.owed s)
view ended s = Q.Closed

-- Only the two graceful wire hooks change the ghost observation stage.
advance : Stage → C.Action → Stage
advance _ C.sendQuit = quitting
advance _ C.recvDone = ended
advance stage _ = stage

-- Every hidden main transition preserves the observation stage.
control-tau : ∀ {stage s t} → C.Tau s t → Control stage (C.main s) → Control stage (C.main t)
control-tau C.registerResponse (before _) = before writing
control-tau C.setStopIdle (before _) = before writeQuit
control-tau C.setStopBusy (before _) = before registerQuit
control-tau C.registerMarker (before _) = before writeQuit
control-tau C.optionalEmpty (before _) = before issue
control-tau C.optionalResult (before _) = before adjust
control-tau C.blockingResult (before _) = before adjust
control-tau C.adjustArrival (before _) = before poll
control-tau C.drainResult (after _) = after draining
control-tau C.drained (after _) = after awaitDone
control-tau (C.startResponse _) ctl = ctl
control-tau (C.startMarker _) ctl = ctl
control-tau (C.keepReply _) ctl = ctl
control-tau (C.discardReply _) ctl = ctl
control-tau (C.countArrival _) ctl = ctl
control-tau (C.publishResponse _) ctl = ctl
control-tau (C.publishMarker _) ctl = ctl

-- Callbacks retain the stage while successful Quit and Done hooks move it forward.
control-step : ∀ {stage s a t} → C.Step s a t → Control stage (C.main s) →
  Control (advance stage a) (C.main t)
control-step C.continueZero (before _) = before issue
control-step (C.continueBelow _) (before _) = before maybeCollect
control-step (C.continueFull _ _) (before _) = before waitCollect
control-step C.stopRequested (before _) = before stopPending
control-step C.sentRequest (before _) = before poll
control-step C.sentQuitIdle (before _) = after awaitDone
control-step C.sentQuitBusy (before _) = after draining
control-step (C.receivedReply _) ctl = ctl
control-step (C.delivered _) ctl = ctl
control-step C.receivedDone (after _) = finished

-- A response registration adds precisely one corrected credit, with no emitted packet.
register-view : ∀ js r → balance C.writingRequest (R.responses (js ∷ʳ C.responseJob) + R.awaitingReply r)
  ≡ Q.Open (R.responses js + R.awaitingReply r)
register-view js r rewrite R.snoc-response js = refl

-- Hidden scheduling preserves the quotient observation even when it moves the receiver.
tau-view : ∀ {stage s t} → C.Tau s t → Control stage (C.main s) → view stage s ≡ view stage t
tau-view (C.registerResponse {r = r} {js = js}) (before _) = sym (register-view js r)
tau-view C.setStopIdle (before _) = refl
tau-view C.setStopBusy (before _) = refl
tau-view (C.registerMarker {js = js}) (before _) rewrite R.snoc-marker js = refl
tau-view C.optionalEmpty (before _) = refl
tau-view C.optionalResult (before _) = refl
tau-view C.blockingResult (before _) = refl
tau-view C.adjustArrival (before _) = refl
tau-view C.drainResult (after _) = refl
tau-view C.drained (after _) = refl
tau-view {stage = ordinary} (C.startResponse {js = js} _) ctl rewrite +-suc (R.responses js) 0 = refl
tau-view {stage = quitting} (C.startResponse {js = js} _) ctl rewrite +-suc (R.responses js) 0 = refl
tau-view {stage = ended} (C.startResponse _) ctl = refl
tau-view {stage = ordinary} (C.startMarker _) ctl = refl
tau-view {stage = quitting} (C.startMarker _) ctl = refl
tau-view {stage = ended} (C.startMarker _) ctl = refl
tau-view {stage = ordinary} (C.keepReply _) ctl = refl
tau-view {stage = quitting} (C.keepReply _) ctl = refl
tau-view {stage = ended} (C.keepReply _) ctl = refl
tau-view {stage = ordinary} (C.discardReply _) ctl = refl
tau-view {stage = quitting} (C.discardReply _) ctl = refl
tau-view {stage = ended} (C.discardReply _) ctl = refl
tau-view {stage = ordinary} (C.countArrival _) ctl = refl
tau-view {stage = quitting} (C.countArrival _) ctl = refl
tau-view {stage = ended} (C.countArrival _) ctl = refl
tau-view {stage = ordinary} (C.publishResponse _) ctl = refl
tau-view {stage = quitting} (C.publishResponse _) ctl = refl
tau-view {stage = ended} (C.publishResponse _) ctl = refl
tau-view {stage = ordinary} (C.publishMarker _) ctl = refl
tau-view {stage = quitting} (C.publishMarker _) ctl = refl
tau-view {stage = ended} (C.publishMarker _) ctl = refl

-- A single received-ahead reply consumes the correction before its delayed Request Send.
early-reply : ∀ n m → Q.Step (Q.Open n) (Q.reply m) (balance C.writingRequest n)
early-reply zero m = Q.earlyReply
early-reply (suc n) m = Q.receiveReply

-- Recording a pending Request Send either restores zero or adds ordinary positive credit.
request-step : ∀ n → Q.Step (balance C.writingRequest n) Q.request (Q.Open n)
request-step zero = Q.finishRequest
request-step (suc n) = Q.sendRequest

-- Reply hooks consume exact credit, including the writingRequest correction case.
reply-early : ∀ {m} → Early m → ∀ n value →
  Q.Step (balance m (suc n)) (Q.reply value) (balance m n)
reply-early poll n value = Q.receiveReply
reply-early issue n value = Q.receiveReply
reply-early writing n value = early-reply n value
reply-early maybeCollect n value = Q.receiveReply
reply-early waitCollect n value = Q.receiveReply
reply-early adjust n value = Q.receiveReply
reply-early stopPending n value = Q.receiveReply
reply-early registerQuit n value = Q.receiveReply
reply-early writeQuit n value = Q.receiveReply

-- Empty accounting at AwaitDone leaves no pending response job or awaiting receiver.
await-owed : ∀ {s} → A.Accounted s → P.Phase s → C.main s ≡ C.awaitDone → R.owed s ≡ 0
await-owed {s} acc phase waiting with A.empty-at-zero {c = s} acc (P.await-zero phase waiting) (cong A.registered waiting)
... | inventory = cong₂ _+_ (cong R.responses (A.Empty.jobs-empty inventory))
  (cong R.awaitingReply (A.Empty.receiver-idle inventory))

-- One source visible action gives zero or one exact quotient transition.
step-view : ∀ {stage s a t} → C.Step s a t → Control stage (C.main s) →
  A.Accounted s → P.Phase s → Q.Run (view stage s) (wire (a ∷ [])) (view (advance stage a) t)
step-view C.continueZero (before _) acc phase = Q.stop
step-view (C.continueBelow _) (before _) acc phase = Q.stop
step-view (C.continueFull _ _) (before _) acc phase = Q.stop
step-view C.stopRequested (before _) acc phase = Q.stop
step-view (C.sentRequest {r = r} {js = js}) (before _) acc phase = Q.step (request-step (R.responses js + R.awaitingReply r)) Q.stop
step-view C.sentQuitIdle (before _) acc phase = Q.step Q.sendQuit Q.stop
step-view C.sentQuitBusy (before _) acc phase = Q.step Q.sendQuit Q.stop
step-view {stage = ordinary} (C.receivedReply {js = js} {reply = value} _) (before early) acc phase
  rewrite +-suc (R.responses js) 0 = Q.step (reply-early early (R.responses js + 0) value) Q.stop
step-view {stage = quitting} (C.receivedReply {js = js} _) (after _) acc phase
  rewrite +-suc (R.responses js) 0 = Q.step Q.drainReply Q.stop
step-view {stage = ended} (C.receivedReply ()) finished acc phase
step-view {stage = ordinary} (C.delivered _) ctl acc phase = Q.stop
step-view {stage = quitting} (C.delivered _) ctl acc phase = Q.stop
step-view {stage = ended} (C.delivered _) ctl acc phase = Q.stop
step-view C.receivedDone (after _) acc phase rewrite await-owed acc phase refl = Q.step Q.receiveDone Q.stop

-- Quotient runs concatenate without changing event order or intermediate obligations.
append : ∀ {s t u xs ys} → Q.Run s xs t → Q.Run t ys u → Q.Run s (xs ++ ys) u
append Q.stop suffix = suffix
append (Q.step pr rest) suffix = Q.step pr (append rest suffix)

-- Induction erases callbacks, preserves arbitrary hidden scheduling, and retains a final witness.
sound : ∀ {stage s actions t} → C.Run s actions t → Control stage (C.main s) →
  A.Accounted s → P.Phase s → Σ[ last ∈ Q.State ] Q.Run (view stage s) (wire actions) last
sound C.stop ctl acc phase = _ , Q.stop
sound {stage} (C.internal pr run) ctl acc phase with sound run (control-tau pr ctl) (A.tau-accounted pr acc) (P.tau-phase pr phase)
... | last , rest = last , subst (λ start → Q.Run start _ last) (sym (tau-view pr ctl)) rest
sound {stage} {actions = a ∷ actions} (C.visible pr run) ctl acc phase
  with sound run (control-step pr ctl) (A.step-accounted pr acc) (P.step-phase pr phase)
... | last , rest = last , subst (λ rows → Q.Run _ rows last) (sym (wire-append (a ∷ []) actions))
  (append (step-view pr ctl acc phase) rest)

-- Every initial detailed client execution is an accepted exact local driver-hook prefix.
initial-sound : ∀ {actions t} → C.Run C.initial actions t → Q.HasTrace Q.initial (wire actions)
initial-sound run = sound run (before poll) refl (P.before P.poll)
