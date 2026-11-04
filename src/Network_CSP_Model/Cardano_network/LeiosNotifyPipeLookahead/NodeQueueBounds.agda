{-# OPTIONS --safe #-}

-- Bind the exact notification budget to the fresh fixed-depth paired policy.
module Cardano_network.LeiosNotifyPipeLookahead.NodeQueueBounds (Notification : Set) where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-trans; m≤n+m)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification ⊤ as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.QueueBudget Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ResourceBounds Notification as Resources
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as P

-- Source projection fixes the original normal-only next callback contract.
module Source = Projection.For S.nodeNext

-- The combined state retains the same physical per-peer credit/notification store.
Budget : N.State → Set
Budget s = B.Budget (D.serverState (N.driverState s)) (N.queueState s)

-- Concatenate concrete node histories to retain freshness at intermediate points.
append : ∀ {s t u xs ys} → N.Run s xs t → N.Run t ys u → N.Run s (xs ++ ys) u
append N.stop rest = rest
append (N.internal pr run) rest = N.internal pr (append run rest)
append (N.visible pr run) rest = N.visible pr (append run rest)

-- Every policy input and wire record preserves the same queue budget.
step : ∀ {s a t} → N.Step s a t → Budget s → Budget t
step (N.clientRecord N.sent (D.clientSent _)) budget = budget
step (N.clientRecord N.received (D.clientReceived _)) budget = budget
step (N.serverRecord N.sent (D.serverSent {m = D.reply _} pr)) budget =
  B.step (Server.peerRecord Server.reply pr) budget
step (N.serverRecord N.sent (D.serverSent {m = D.done} pr)) budget =
  B.step (Server.peerRecord Server.done pr) budget
step (N.serverRecord N.received (D.serverReceived {m = D.request} pr)) budget =
  B.step (Server.peerRecord Server.request pr) budget
step (N.serverRecord N.received (D.serverReceived {m = D.quit} pr)) budget =
  B.step (Server.peerRecord Server.quit pr) budget
step N.forecastInput budget = budget
step N.terminateInput budget = budget
step (N.applicationInput pr) budget = B.step pr budget
step (N.normalHandler {raw = D.pair _ _ _ _ _ _ _ _} _) budget = budget
step (N.canceledHandlerExit _) budget = budget

-- Fresh server control supplies the exclusion of post-Quit admission.
phase : ∀ {actions t} → N.Run N.initial actions t → Phase.Phase (D.serverState (N.driverState t))
phase trace with Source.server (P.driver trace)
... | inputs , source , matching = Phase.initial-phase source

-- Only server scheduling can change its queue budget; transport keeps its peer control.
tau : ∀ {actions s t} → N.Run N.initial actions s → N.Tau s t → Budget s → Budget t
tau prefix (N.clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} _) budget = budget
tau prefix (N.continueReady {raw = D.pair _ _ _ _ _ _ _ _} _) budget = budget
tau prefix (N.terminateReady {raw = D.pair _ _ _ _ _ _ _ _} _) budget = budget
tau prefix (N.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} pr) budget =
  B.tau pr (phase prefix) (Resources.server-owed (Resources.initial-bounds prefix)) budget
tau prefix (N.transport pr allowed) budget rewrite P.server-transport pr allowed = budget

-- Follow a continuation while retaining an actual fresh prefix for every intermediate bound.
run : ∀ {before s actions t} → N.Run N.initial before s → N.Run s actions t → Budget s → Budget t
run prefix N.stop budget = budget
run prefix (N.internal pr rest) budget = run (append prefix (N.internal pr N.stop)) rest (tau prefix pr budget)
run prefix (N.visible pr rest) budget = run (append prefix (N.visible pr N.stop)) rest (step pr budget)

-- The initial budget is exact zero, so every production-policy prefix inherits it.
initial-budget : ∀ {actions t} → N.Run N.initial actions t → Budget t
initial-budget trace = run N.stop trace refl

-- Unused credits and queued notifications together fit in the live-work envelope.
initial-total : ∀ {actions t} → N.Run N.initial actions t → B.total (N.queueState t) ≤ 1003
initial-total {t = t} trace = B.queue-bound {s = D.serverState (N.driverState t)} {q = N.queueState t}
  (Resources.server-owed (Resources.initial-bounds trace)) (initial-budget trace)

-- In particular the actual eligible-notification FIFO has a uniform length bound.
initial-queue : ∀ {actions t} → N.Run N.initial actions t → length (Q.queued (N.queueState t)) ≤ 1003
initial-queue {t = t} trace = ≤-trans (m≤n+m (length (Q.queued (N.queueState t)))
  (Q.free (N.queueState t))) (initial-total trace)
