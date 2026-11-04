{-# OPTIONS --safe #-}

-- Actual fresh paired node histories witness early hits, guarded misses, hook reordering and closure.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.NodeResourceTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Bool ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Bool 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeModel Bool 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeDriverModel Bool as N
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeForward Bool as F
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeBounds Bool as Bounds
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting Bool as Count
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety Bool as Safety

-- A sequentially drained client coexists with the server's retained completed inventory.
ready : S.Reader → ℕ → N.State
ready r n = N.nodeDriver (D.pair C.initial (S.state r 0 S.idle n false)
  [] [] nothing nothing nothing nothing) Q.initial true true false

-- Admission precedes poll/registration while the one response receiver is already awaiting.
admission : S.Reader → ℕ → N.State
admission r n = N.nodeDriver
  (D.pair (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing)
    (S.state r 0 S.idle n false) [] [] nothing nothing nothing nothing)
  (Q.credits 1 []) true true false

-- The environment opens the forecast once before any repeated exchanges.
begin : N.Run N.initial (N.setForecast true ∷ []) (ready S.first 0)
begin = N.visible N.forecastInput N.stop

-- Commands are physically sent, traced and received before credit admission.
start : ∀ {r} → S.Reading r → ∀ n → N.Run (ready r n)
  (N.wire (D.clientSend D.request) ∷ N.wire (D.serverRecv D.request) ∷ []) (admission S.inspect n)
start canRead n = N.internal (N.continueReady (Client.continueAtDepth C.continueZero)) $
  N.internal (N.clientSchedule (Client.schedule C.registerResponse)) $
  N.internal (N.clientSchedule (Client.schedule (C.startResponse refl))) $
  N.internal (N.transport (D.commitClient C.sentRequest) refl) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) $
  N.internal (N.transport (D.decodeServer (S.receiveRequest canRead)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveRequest canRead))) $
  N.internal (N.serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) N.stop

-- First registration has zero old jobs; subsequent sequential registrations have one old token.
oldCount : Bool → ℕ
oldCount false = 0
oldCount true = 1

-- Both actual guarded inspection paths reserve the current registration slot.
prepare : ∀ old → N.Run (admission S.inspect (oldCount old)) [] (admission S.register 0)
prepare false = N.internal (N.serverSchedule (Server.schedule (S.inspectZero refl) refl)) N.stop
prepare true = N.internal (N.serverSchedule (Server.schedule (S.inspectPositive (s≤s z≤n)) refl)) $
  N.internal (N.serverSchedule (Server.schedule S.pollHit refl)) N.stop

-- Exact payload, eligible offer and successful normal handler remain explicit policy actions.
replyActions : List N.Action
replyActions = N.eligible true ∷ N.wire (D.serverSend (D.reply (S.normal true))) ∷
  N.wire (D.clientRecv (D.reply (S.normal true))) ∷ N.handledNormal true ∷ []

-- Response handling and collection return the fixed-depth client to its actual empty state.
respond : N.Run (admission S.register 0) replyActions (ready S.awaitNext 1)
respond = N.internal (N.serverSchedule (Server.schedule S.registered refl)) $
  N.visible (N.applicationInput (Server.applicationOffer refl Q.enqueued)) $
  N.internal (N.serverSchedule (Server.schedule (S.claim refl) refl)) $
  N.internal (N.serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl))) $
  N.internal (N.transport (D.commitServer (S.send refl)) refl) $
  N.visible (N.serverRecord N.sent (D.serverSent (S.send refl))) $
  N.internal (N.serverSchedule (Server.schedule (S.retire refl) refl)) $
  N.internal (N.transport (D.decodeClient (C.receivedReply refl)) refl) $
  N.visible (N.clientRecord N.received (D.clientReceived (C.receivedReply refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.keepReply refl))) $
  N.visible (N.normalHandler (Client.handled (C.delivered refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.countArrival refl))) $
  N.internal (N.clientSchedule (Client.schedule (C.publishResponse refl))) $
  N.internal (N.continueReady (Client.continueAtDepth (C.continueBelow refl))) $
  N.internal (N.clientSchedule (Client.schedule C.optionalResult)) $
  N.internal (N.clientSchedule (Client.schedule C.adjustArrival)) N.stop

-- One full paired round retains all endpoint wire records and policy inputs.
roundActions : List N.Action
roundActions = N.wire (D.clientSend D.request) ∷ N.wire (D.serverRecv D.request) ∷ replyActions

-- The first zero skip and every later hit use the same unchanged client and node callbacks.
round : ∀ {r} → S.Reading r → ∀ old →
  N.Run (ready r (oldCount old)) roundActions (ready S.awaitNext 1)
round canRead old = N.append (start canRead (oldCount old)) (N.append (prepare old) respond)

-- Repeated finite normal histories have no bound on the number of source or wire events.
historyActions : ℕ → List N.Action
historyActions zero = (N.setForecast true ∷ []) ++ roundActions
historyActions (suc n) = historyActions n ++ roundActions

-- Every n+1-round member is a fresh, honest paired-policy execution with one retained token.
history : ∀ n → N.Run N.initial (historyActions n) (ready S.awaitNext 1)
history zero = N.append begin (round S.atFirst false)
history (suc n) = N.append (history n) (round S.atNext true)

-- The general production theorem applies without supplying its formerly open resource premise.
history-bound : ∀ n → S.registeredJobs (Bounds.peer (ready S.awaitNext 1)) ≤ 1005
history-bound n = Bounds.initial-registered (history n)

-- Two real paired rounds move one old token into the baseline simulation's ghost inventory.
one-ghost : proj₁ (F.from-initial (history 1)) ≡ 1
one-ghost = refl

-- One response receiver can await while two requests are registered and the sender is unscheduled.
waiting : ℕ → N.State
waiting n = N.nodeDriver
  (D.pair (C.client C.poll C.awaiting (C.responseJob ∷ []) [] 2 (+ 0) false nothing)
    (S.state S.awaitNext n S.idle 0 false) [] [] nothing nothing nothing nothing)
  (Q.credits n []) true true false

-- A first unscheduled sender state is reached through the same real admission callback.
firstWaiting : N.State
firstWaiting = N.nodeDriver
  (D.pair (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 1 S.idle 0 false) [] [] nothing nothing nothing nothing)
  (Q.credits 1 []) true true false

-- The first request registers normally but has no eligible result or completed token.
first-waiting : N.Run N.initial
  (N.setForecast true ∷ N.wire (D.clientSend D.request) ∷ N.wire (D.serverRecv D.request) ∷ []) firstWaiting
first-waiting = N.append begin (N.append (start S.atFirst 0) (N.append (prepare false)
  (N.internal (N.serverSchedule (Server.schedule S.registered refl)) N.stop)))

-- The second request must miss at zero completions while the old waiting job remains unfinished.
miss : N.Run firstWaiting (N.wire (D.clientSend D.request) ∷ N.wire (D.serverRecv D.request) ∷ []) (waiting 2)
miss = N.internal (N.continueReady (Client.continueAtDepth (C.continueBelow refl))) $
  N.internal (N.clientSchedule (Client.schedule C.optionalEmpty)) $
  N.internal (N.clientSchedule (Client.schedule C.registerResponse)) $
  N.internal (N.transport (D.commitClient C.sentRequest) refl) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) $
  N.internal (N.transport (D.decodeServer (S.receiveRequest S.atNext)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveRequest S.atNext))) $
  N.internal (N.serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  N.internal (N.serverSchedule (Server.schedule (S.inspectPositive (s≤s z≤n)) refl)) $
  N.internal (N.serverSchedule (Server.schedule (S.pollMiss (s≤s z≤n)) refl)) $
  N.internal (N.serverSchedule (Server.schedule S.registered refl)) N.stop

-- That actual miss prefix receives a discharged Budgeted certificate through the production theorem.
fresh-miss : Σ[ actions ∈ List N.Action ] N.Run N.initial actions (waiting 2)
fresh-miss = _ , N.append first-waiting miss

-- A valid miss leaves both old and newly registered obligations retained, not falsely collected.
miss-inventory : S.registeredJobs (Bounds.peer (waiting 2)) ≡ 2 × Q.free (N.queueState (waiting 2)) ≡ 2
miss-inventory = refl , refl

-- Delayed Send records remain pending even after a physically delivered reply was received.
delayedState : N.State
delayedState = N.nodeDriver
  (D.pair (C.client C.poll (C.inspect (S.normal false)) [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing)
  Q.initial true true false

-- Both Receive records precede the matching Send records under the same queue/callback policy.
delayed : N.Run N.initial
  (N.setForecast true ∷ N.wire (D.serverRecv D.request) ∷ N.eligible false ∷
   N.wire (D.clientRecv (D.reply (S.normal false))) ∷ N.wire (D.clientSend D.request) ∷
   N.wire (D.serverSend (D.reply (S.normal false))) ∷ []) delayedState
delayed = N.visible N.forecastInput $
  N.internal (N.continueReady (Client.continueAtDepth C.continueZero)) $
  N.internal (N.clientSchedule (Client.schedule C.registerResponse)) $
  N.internal (N.clientSchedule (Client.schedule (C.startResponse refl))) $
  N.internal (N.transport (D.commitClient C.sentRequest) refl) $
  N.internal (N.transport (D.decodeServer (S.receiveRequest S.atFirst)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveRequest S.atFirst))) $
  N.internal (N.serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  N.internal (N.serverSchedule (Server.schedule (S.inspectZero refl) refl)) $
  N.internal (N.serverSchedule (Server.schedule S.registered refl)) $
  N.visible (N.applicationInput (Server.applicationOffer refl Q.enqueued)) $
  N.internal (N.serverSchedule (Server.schedule (S.claim refl) refl)) $
  N.internal (N.serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl))) $
  N.internal (N.transport (D.commitServer (S.send refl)) refl) $
  N.internal (N.transport (D.decodeClient (C.receivedReply refl)) refl) $
  N.visible (N.clientRecord N.received (D.clientReceived (C.receivedReply refl))) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) $
  N.visible (N.serverRecord N.sent (D.serverSent (S.send refl))) N.stop

-- Its sent-but-unretired sender is bounded as active work despite owing no wire reply.
delayed-unfinished : Count.unfinished (Bounds.peer delayedState) ≤ 1004
delayed-unfinished = Bounds.initial-unfinished delayed

-- Quit publishes the shared flag with no remaining client receiver work.
flushing : N.State
flushing = N.nodeDriver
  (D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.flushing 0 S.idle 1 true) [] [] nothing nothing nothing nothing)
  Q.initial true true true

-- The fresh history really receives Quit before the universal shutdown bound is instantiated.
quit-before : N.Run (ready S.awaitNext 1)
  (N.setTerminate true ∷ N.wire (D.clientSend D.quit) ∷ N.wire (D.serverRecv D.quit) ∷ []) flushing
quit-before = N.visible N.terminateInput $
  N.internal (N.terminateReady (Client.terminate C.stopRequested)) $
  N.internal (N.clientSchedule (Client.schedule C.setStopIdle)) $
  N.internal (N.transport (D.commitClient C.sentQuitIdle) refl) $
  N.visible (N.clientRecord N.sent (D.clientSent C.sentQuitIdle)) $
  N.internal (N.transport (D.decodeServer (S.receiveQuit S.atNext)) refl) $
  N.visible (N.serverRecord N.received (D.serverReceived (S.receiveQuit S.atNext))) $
  N.internal (N.serverSchedule (Server.schedule S.setQuit refl)) N.stop

-- One final collection closes the same actual server control, independently of earlier history length.
source-close : S.Run S.nodeNext (Bounds.peer flushing) (S.sendDone ∷ []) (S.state S.closed 0 S.idle 0 true)
source-close = S.internal S.flush $ S.internal S.drained $ S.visible S.finish S.stop

-- Production-specific shutdown bounds are inhabited for every repeated paired history.
shutdown-bound : ∀ n → Count.final source-close ≤ 1005
shutdown-bound n = Bounds.shutdown-flushes (N.append (history n) quit-before) Safety.flushing source-close

-- The original bound is conservative: this constructed family's exact final count remains one.
one-final : Count.final source-close ≡ 1
one-final = refl

-- Both physical peers can finish with the same empty FIFOs and pending hook slots.
closed : N.State
closed = N.nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  Q.initial true true true

-- The one-token source close has a real paired Done commit and client Receive realization.
paired-close : N.Run flushing (N.wire (D.serverSend D.done) ∷ N.wire (D.clientRecv D.done) ∷ []) closed
paired-close = N.internal (N.serverSchedule (Server.schedule S.flush refl)) $
  N.internal (N.serverSchedule (Server.schedule S.drained refl)) $
  N.internal (N.transport (D.commitServer S.finish) refl) $
  N.visible (N.serverRecord N.sent (D.serverSent S.finish)) $
  N.internal (N.transport (D.decodeClient C.receivedDone) refl) $
  N.visible (N.clientRecord N.received (D.clientReceived C.receivedDone)) N.stop

-- Arbitrary finite normal histories followed by Quit and Done close both modeled endpoints.
full : ∀ n → Σ[ actions ∈ List N.Action ] N.Run N.initial actions closed
full n = _ , N.append (N.append (history n) quit-before) paired-close
