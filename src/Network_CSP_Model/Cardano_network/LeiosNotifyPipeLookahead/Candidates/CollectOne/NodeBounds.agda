{-# OPTIONS --safe #-}

-- The unchanged production client/packet policy discharges CollectOne's resource premise.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeBounds
  (Notification : Set) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat using (ℕ; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl; +-mono-≤)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as BD
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as BN
import Cardano_network.LeiosNotifyPipeLookahead.ResourceBounds Notification as Resources
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeModel Notification 1000 as S
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeForward Notification as F
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Accounting Notification as A
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Bounds Notification as Bounds
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Safety Notification as Safety
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Progress Notification as Progress

-- The source server control belongs to the actual candidate paired endpoint.
peer : N.State → C.State
peer state = D.serverState (N.driverState state)

-- Ghost completions never change the number of waiting sender jobs.
waiting-lift : ∀ extra state → B.waiting (BD.serverState (BN.driverState (F.lift extra state))) ≡ C.waiting (peer state)
waiting-lift extra (N.nodeDriver (D.pair _ (C.state _ _ _ _ _) _ _ _ _ _ _) _ _ _ _) = refl

-- A baseline resource theorem is reused only after constructing an actual fresh policy history.
initial-waiting : ∀ {actions t} → N.Run N.initial actions t → C.waiting (peer t) ≤ 1003
initial-waiting {t = t} execution with F.from-initial execution
... | extra , good , baseline = subst (_≤ 1003) (waiting-lift extra t)
  (Resources.server-waiting (Resources.initial-bounds baseline))

-- Claimed, selected and sent-but-unretired all occupy the same single active sender slot.
active-bound : ∀ sender → C.activeJob sender ≤ 1
active-bound C.idle = z≤n
active-bound C.claimed = ≤-refl
active-bound (C.selected _) = ≤-refl
active-bound C.sent = ≤-refl

-- All fresh candidate states, and therefore all actual poll misses, satisfy B=1004.
initial-unfinished : ∀ {actions t} → N.Run N.initial actions t → A.unfinished (peer t) ≤ 1004
initial-unfinished {t = t} execution = +-mono-≤ (initial-waiting execution) (active-bound (C.sender (peer t)))

-- Instantiate the exact earlier premise without changing its type or its candidate rules.
miss-premise : ∀ {s t} (pr : C.Tau s t) → A.unfinished s ≤ 1004 → Bounds.MissBound 1004 pr
miss-premise C.admitted _ = tt
miss-premise C.excessive _ = tt
miss-premise (C.inspectZero _) _ = tt
miss-premise (C.inspectPositive _) _ = tt
miss-premise C.pollHit _ = tt
miss-premise (C.pollMiss _) bound = bound
miss-premise C.registered _ = tt
miss-premise C.setQuit _ = tt
miss-premise (C.claim _) _ = tt
miss-premise (C.cancel _) _ = tt
miss-premise (C.retire _) _ = tt
miss-premise C.flush _ = tt
miss-premise C.drained _ = tt
miss-premise C.abort _ = tt

-- Physical commits and decodes retain server source control even while hooks are delayed.
transport-server : ∀ {raw raw′ live} (pr : D.Tau C.nodeNext raw raw′) →
  N.transportAllowed live pr ≡ true → D.serverState raw ≡ D.serverState raw′
transport-server (D.clientInternal _) ()
transport-server (D.serverInternal _) ()
transport-server (D.clientCallback _ _) ()
transport-server (D.serverCallback _) ()
transport-server (D.commitClient _) _ = refl
transport-server (D.commitServer _) _ = refl
transport-server (D.decodeClient _) _ = refl
transport-server (D.decodeServer _) _ = refl

-- A projected source fragment retains both its real operations and every required miss certificate.
Fragment : N.State → N.State → Set
Fragment s t = Σ[ actions ∈ List C.Action ]
  (Σ[ execution ∈ C.Run C.nodeNext (peer s) actions (peer t) ] Bounds.Budgeted 1004 execution)

-- Node callback and scheduling operations are projected without inventing callback readiness.
server-tau : ∀ {s t} → N.Tau s t → A.unfinished (peer s) ≤ 1004 → Fragment s t
server-tau (N.clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} _) _ = [] , C.stop , tt
server-tau (N.continueReady {raw = D.pair _ _ _ _ _ _ _ _} _) _ = [] , C.stop , tt
server-tau (N.terminateReady {raw = D.pair _ _ _ _ _ _ _ _} _) _ = [] , C.stop , tt
server-tau (N.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (S.schedule pr _)) bound =
  [] , C.internal pr C.stop , miss-premise pr bound , tt
server-tau (N.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (S.admitAccepted _)) _ =
  [] , C.internal C.admitted C.stop , tt , tt
server-tau (N.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (S.admitExcessive _)) _ =
  [] , C.internal C.excessive C.stop , tt , tt
server-tau (N.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (S.nextQueued {m = msg} _ pr)) _ =
  C.nextReply (C.normal msg) ∷ [] , C.visible pr C.stop , tt
server-tau (N.transport pr allowed) _ rewrite transport-server pr allowed = [] , C.stop , tt

-- Only real server wire records survive; every other visible node input leaves its source control fixed.
server-step : ∀ {s a t} → N.Step s a t → Fragment s t
server-step (N.clientRecord N.sent (D.clientSent _)) = [] , C.stop , tt
server-step (N.clientRecord N.received (D.clientReceived _)) = [] , C.stop , tt
server-step (N.serverRecord N.sent (D.serverSent {m = msg} pr)) =
  D.serverSendAction msg ∷ [] , C.visible pr C.stop , tt
server-step (N.serverRecord N.received (D.serverReceived {m = msg} pr)) =
  D.serverRecvAction msg ∷ [] , C.visible pr C.stop , tt
server-step N.forecastInput = [] , C.stop , tt
server-step N.terminateInput = [] , C.stop , tt
server-step (N.applicationInput _) = [] , C.stop , tt
server-step (N.normalHandler {raw = D.pair _ _ _ _ _ _ _ _} _) = [] , C.stop , tt
server-step (N.canceledHandlerExit _) = [] , C.stop , tt

-- Every recursive suffix has a fresh paired prefix, discharging the premise where it is actually used.
project : ∀ {prefix s actions t} → N.Run N.initial prefix s → N.Run s actions t → Fragment s t
project before N.stop = [] , C.stop , tt
project before (N.internal pr rest) with server-tau pr (initial-unfinished before)
... | actions , source , budget with project (N.append before (N.internal pr N.stop)) rest
...   | more , suffix , later = actions ++ more , C.append source suffix , Bounds.budget-append source suffix budget later
project before (N.visible pr rest) with server-step pr
... | actions , source , budget with project (N.append before (N.visible pr N.stop)) rest
...   | more , suffix , later = actions ++ more , C.append source suffix , Bounds.budget-append source suffix budget later

-- The original local Budgeted premise is now inhabited for every actual fresh candidate paired run.
server : ∀ {actions t} → N.Run N.initial actions t →
  Σ[ sourceActions ∈ List C.Action ]
  (Σ[ execution ∈ C.Run C.nodeNext C.initial sourceActions (peer t) ] Bounds.Budgeted 1004 execution)
server execution = project N.stop execution

-- No caller-supplied unfinished, queue, fairness or range premise is added to this mathematical bound.
initial-registered : ∀ {actions t} → N.Run N.initial actions t → C.registeredJobs (peer t) ≤ 1005
initial-registered execution with server execution
... | sourceActions , source , budget = Bounds.initial-bound source budget

-- Completed bookkeeping is bounded independently of visible connection history length.
initial-completed : ∀ {actions t} → N.Run N.initial actions t → C.completed (peer t) ≤ 1005
initial-completed execution with server execution
... | sourceActions , source , budget = Bounds.completed-bound source budget

-- Every later successful source shutdown flushes at most this production-policy envelope.
shutdown-flushes : ∀ {prefix s actions} → N.Run N.initial prefix s → Safety.Stopping (peer s) →
  (after : C.Run C.nodeNext (peer s) actions (C.state C.closed 0 C.idle 0 true)) → A.final after ≤ 1005
shutdown-flushes before stopping after with server before
... | sourceActions , source , budget = Progress.fresh-shutdown-flushes source budget stopping after

-- This counts server source operations after its actual Quit, not driver/RTS time or whole-node work.
shutdown-steps : ∀ {prefix s actions t} → N.Run N.initial prefix s → Safety.Stopping (peer s) →
  (after : C.Run C.nodeNext (peer s) actions t) → Progress.steps after ≤ 5028
shutdown-steps before stopping after with server before
... | sourceActions , source , budget = Progress.fresh-shutdown-steps source budget stopping after
