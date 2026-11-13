{-# OPTIONS --guardedness #-}

-- Joint content and retained observers through startup-unwind plans.
-- Pool writes carry their exact current frame and actual primitive step.
module ConnectionManagement.Properties.LiveTrackerAuxCoverageUnwind where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.HandlerAuxBacking as Presence

import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Properties.LiveTrackerAuxCoverageExit as ExitFacts
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
module Exit = ExitFacts.Exit
module Cancellation = ExitFacts.Cancellation
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
module Unwind (isBearerClosed : ErrorId → Bool)
 (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains isBearerClosed s t → Obs s → Obs t) where
 private module R = UnwindModel isBearerClosed using (counterRow; Action; Fault; Plan; State; acknowledge; allowed; async; asyncDead; asyncStatus; awaitingClose; base; beginClose; beginDead; cancellationPlan; choose; closing; commitDead; continueSync; deadThrowPoint; deliverCancel; deliverShutdown; deliveryControl; deliveryRoute; enact; faults; finishClose; finishDead; handedOff; handoff; inherited; initial; join; local; machine; mux; observeCancellation; observeDeadTraceException; observeFailure; outcome; owner; phase; pool; poolAt; poolClosed; protocols; readyBody; readyBuffer; requestCancel; run; sameClose; sampleDead; setPhase; setPool; setSource; siteControl; siteRoute; source; start; step; sync; transfer; withPool; writeAsyncFailure)
 private module W = ExitModel isBearerClosed using (base; control; exits; setShutdown; shutdown)
 private module X = CancellationModel isBearerClosed using (initial; step)
 private module G = GroupModel isBearerClosed using (module M; protocolState; wholeDeliverable)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; muxAt)
 private module U = P.U using (captured; frames)
 private module Up = Updates isBearerClosed
 private module Pool = P.Pool using (beginClose; cancelPending; closedPool; closing; finishClose; join; joinPending; openPool; phase; requestCancel; step)
 private module M = G.M using (failed; finishMatches)
 private module F = UnwindProperties isBearerClosed using (Selection; selection-observation)
 private module Lower = Exit isBearerClosed Obs stable using (Valid; control-preserves; pool-valid; shutdown-valid; source-valid; source-quiet)
 private module Cancel = Cancellation isBearerClosed Obs stable using (step-preserves)
 Valid : R.State → Set
 Valid s = Lower.Valid (R.base s)
 source-valid : ∀ c s {as} → O.Executes (R.source s) as c → Valid s → Valid (R.setSource c s)
 source-valid c s path = Lower.source-valid c (R.base s) path
 shutdown-valid : ∀ coordinator s → Valid s → Valid (record s { base = W.setShutdown coordinator (R.base s) })
 shutdown-valid coordinator s = Lower.shutdown-valid coordinator (R.base s)
 data PlanSafe : R.Plan → R.State → Set₁ where
  safe-local : ∀ {fs s} → PlanSafe (R.local fs) s
  safe-machine : ∀ {a fs s} → PlanSafe (R.machine a fs) s
  safe-pool : ∀ {w u a fs s} → lookup w (U.frames (P.base (R.protocols s))) ≡ just u →
    (∀ C → Up.Kernel.NewReturn a C) → PlanSafe (R.pool w u a fs) s
  safe-transfer : ∀ {w f fs s} → PlanSafe (R.transfer w f fs) s
  safe-inherited : ∀ {a s} → PlanSafe (R.inherited a) s
  safe-acknowledge : ∀ {p s} → PlanSafe p s → PlanSafe (R.acknowledge p) s
 enact-preserves : ∀ p s {t} → R.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (R.local fs) s eq valid safe-local = case just-injective eq of λ { refl → valid }
 enact-preserves (R.machine a fs) s eq valid safe-machine with O.advance a (R.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → source-valid c s (O.next {a = a} actual O.done) valid }
 enact-preserves (R.pool w u a fs) s eq valid (safe-pool found new) with Pool.step a (R.poolAt w s) in actual
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → Lower.pool-valid w u a (R.base s) found actual new valid }
 enact-preserves (R.transfer w f fs) s eq valid safe-transfer = case just-injective eq of λ { refl → valid }
 enact-preserves (R.inherited a) s eq valid safe-inherited with X.step a (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancel.step-preserves a (R.base s) actual valid }
 enact-preserves (R.acknowledge p) s eq valid (safe-acknowledge safe) with R.enact p s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → Lower.control-preserves Close.acknowledgeDelivery (R.base next) acknowledged
     (enact-preserves p s actual valid safe) }
 start-safe : ∀ w result route s {p} → R.start w result route s ≡ just p → Valid s → PlanSafe p s
 start-safe w result route s chosen valid with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = safe-local
 IsDirect : R.Action → Set
 IsDirect (R.run a) = ⊥
 IsDirect (R.deliverShutdown site err) = ⊥
 IsDirect _ = ⊤
 NonAck : R.Plan → Set
 NonAck (R.acknowledge p) = ⊥
 NonAck _ = ⊤
 ChosenSafe : R.Action → R.Plan → R.State → Set₁
 ChosenSafe a p s = PlanSafe p s × (IsDirect a → NonAck p)
 start-nonack : ∀ w result route s {p} → R.start w result route s ≡ just p → NonAck p
 start-nonack w result route s chosen with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = tt
 cancellation-safe : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → Valid s → PlanSafe p s × NonAck p
 cancellation-safe w site err s eq valid with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-safe w (R.async err) (λ f m → R.deliveryRoute site f m) s eq valid ,
   start-nonack w (R.async err) (λ f m → R.deliveryRoute site f m) s eq
 pool-safe : ∀ w before action after s {p} → R.withPool w before action after s ≡ just p → (∀ C → Up.Kernel.NewReturn action C) → Valid s → PlanSafe p s × NonAck p
 pool-safe w before action after s eq new valid with lookup w (R.faults s) in found | R.owner w s in owner
 ... | just f | just u with R.sameClose before (R.phase f)
 ...   | true = case just-injective eq of λ { refl → safe-pool owner new  , tt }
 ...   | false = case eq of λ ()
 pool-safe w before action after s eq new valid | nothing | nothing = case eq of λ ()
 pool-safe w before action after s eq new valid | nothing | just u = case eq of λ ()
 pool-safe w before action after s eq new valid | just f | nothing = case eq of λ ()
 chosen-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → ChosenSafe a p s
 chosen-safe (R.run a) s eq valid with R.allowed a s
 ... | true = case just-injective eq of λ { refl → safe-inherited , λ () }
 ... | false = case eq of λ ()
 chosen-safe (R.observeFailure w site err) s eq valid with R.siteControl w site s
 ... | true = start-safe w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq valid ,
   (λ _ → start-nonack w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq)
 ... | false = case eq of λ ()
 chosen-safe (R.observeCancellation w site err) s eq valid with cancellation-safe w site err s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base s))
 ... | Close.awaitDelivery e w with R.cancellationPlan w site err s in cancelled
 ...   | just p = case just-injective eq of λ { refl → safe-acknowledge (proj₁ (cancellation-safe w site err s cancelled valid)) , λ () }
 ...   | nothing = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()
 chosen-safe (R.beginClose w order) s eq valid with pool-safe w R.awaitingClose (Pool.beginClose order) R.closing s eq (λ C → tt) valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.requestCancel w) s eq valid with pool-safe w R.closing Pool.requestCancel R.closing s eq (λ C → tt) valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.join w) s eq valid with pool-safe w R.closing Pool.join R.closing s eq (λ C → tt) valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.finishClose w) s eq valid with pool-safe w R.closing Pool.finishClose R.poolClosed s eq (λ C → tt) valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverCancel w) s eq valid with lookup w (R.faults s) | R.owner w s in owner | Pool.phase (R.poolAt w s)
 ... | just f | just u | Pool.cancelPending j with R.phase f | G.wholeDeliverable w j u (W.base (R.base s))
 ...   | R.closing | true = case just-injective eq of λ { refl → safe-pool owner (λ C → tt)  , λ _ → tt }
 ...   | R.readyBody | _ = case eq of λ ()
 ...   | R.readyBuffer | _ = case eq of λ ()
 ...   | R.awaitingClose | _ = case eq of λ ()
 ...   | R.poolClosed | _ = case eq of λ ()
 ...   | R.asyncStatus | _ = case eq of λ ()
 ...   | R.asyncDead | _ = case eq of λ ()
 ...   | R.handedOff | _ = case eq of λ ()
 ...   | R.closing | false = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | nothing | _ | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | nothing | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.openPool = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closing = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closedPool = case eq of λ ()

 chosen-safe (R.continueSync w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.sync err = case just-injective eq of λ { refl → safe-local  , λ _ → tt }
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.async err = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.writeAsyncFailure w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.async err = case just-injective eq of λ { refl → safe-machine  , λ _ → tt }
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.sync err = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.beginDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncStatus = case just-injective eq of λ { refl → safe-machine  , λ _ → tt }
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.asyncDead = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.sampleDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine  , λ _ → tt }
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.commitDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine  , λ _ → tt }
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.finishDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | R.async err | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → safe-local  , λ _ → tt }
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.returned | false = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.readActive tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterStart n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.forkPending n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterFailure | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | nothing = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.sync err | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBody | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBuffer | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.awaitingClose | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.closing | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.poolClosed | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncStatus | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.handedOff | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.observeDeadTraceException w err) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | just m with R.deadThrowPoint m
 ...     | true = case just-injective eq of λ { refl → safe-local  , λ _ → tt }
 ...     | false = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncDead | nothing = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.closing | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.handoff w) s eq valid with lookup w (R.faults s) in found | lookup w (W.exits (R.base s))
 ... | just f | nothing with R.phase f | R.outcome f
 ...   | R.readyBuffer | result with R.counterRow f s
 ...     | just _ = case just-injective eq of λ { refl → safe-machine , λ _ → tt }
 ...     | nothing = case just-injective eq of λ { refl → safe-transfer   , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.readyBody | R.sync err = case just-injective eq of λ { refl → safe-transfer   , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.readyBody | R.async err = case just-injective eq of λ { refl → safe-transfer   , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.closing | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | just exit = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe a s chosen valid = proj₁ (chosen-safe a s chosen valid)
 chosen-nonack : ∀ a s {p} → R.choose a s ≡ just p → Valid s → IsDirect a → NonAck p
 chosen-nonack a s chosen valid = proj₂ (chosen-safe a s chosen valid)
 step-preserves : ∀ a s {t} → R.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 -- Source changes leave the physical tables and all auxiliary certificates intact.
 source-quiet : ∀ c s → Valid s → Valid (R.setSource c s)
 source-quiet c s valid = Lower.source-quiet c (R.base s) valid
 shutdown-quiet = shutdown-valid

-- Plan certificates constrain the same actual pool/frame operations regardless
-- of which additional retained observer is carried by the induction.
map-safe : ∀ (b : ErrorId → Bool) (Obs : ProtocolModel.State → Set)
 (stable : ∀ {s t} → Transport.Retains b s t → Obs s → Obs t)
 (Other : ProtocolModel.State → Set)
 (retained : ∀ {s t} → Transport.Retains b s t → Other s → Other t) {p s} →
 Unwind.PlanSafe b Obs stable p s → Unwind.PlanSafe b Other retained p s
map-safe b Obs stable Other retained Unwind.safe-local = Unwind.safe-local
map-safe b Obs stable Other retained Unwind.safe-machine = Unwind.safe-machine
map-safe b Obs stable Other retained (Unwind.safe-pool found new) = Unwind.safe-pool found new
map-safe b Obs stable Other retained Unwind.safe-transfer = Unwind.safe-transfer
map-safe b Obs stable Other retained Unwind.safe-inherited = Unwind.safe-inherited
map-safe b Obs stable Other retained (Unwind.safe-acknowledge safe) = Unwind.safe-acknowledge (map-safe b Obs stable Other retained safe)
