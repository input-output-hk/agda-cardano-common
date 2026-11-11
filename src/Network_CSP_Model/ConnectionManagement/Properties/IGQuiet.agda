{-# OPTIONS --guardedness #-}

-- An exited, deactivated inbound governor stays exited and deactivated under
-- every IG step: every loop action needs a live continuation, deactivation
-- needs an active engine, and all other actions rewrite only the mux, handle,
-- timer, counter or DB tables.
module ConnectionManagement.Properties.IGQuiet where

open import Class.DecEq.Instances using (DecEq-ℕ; DecEq-×)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (ResponderMode; responderMode; noResponderMode)
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.TracerReadiness as Readiness
open import ConnectionManagement.Rules.IGRegistration

-- The governor's exited, deactivated control state.
Quiet : Runtime → Set
Quiet r = continuation r ≡ exited × active (execution r) ≡ false

db-active : ∀ a e {e′} → stepDb a e ≡ just e′ → active e′ ≡ active e
db-active (submitWrite j d) e eq with dbSealed e | lookup d (dbWrites e) | lookup j (dbWaits e)
... | nothing | nothing | nothing = case just-injective eq of λ { refl → refl }
... | nothing | nothing | just _ = case eq of λ ()
... | nothing | just _ | _ = case eq of λ ()
... | just _ | _ | _ = case eq of λ ()
db-active (completeWrite d) e eq with dbSealed e | lookup d (dbWrites e)
... | nothing | just (j , false) = case just-injective eq of λ { refl → refl }
... | nothing | nothing = case eq of λ ()
... | nothing | just (_ , true) = case eq of λ ()
... | just _ | _ = case eq of λ ()
db-active (sealQueue err) e eq with dbSealed e
... | nothing = case just-injective eq of λ { refl → refl }
... | just _ = case eq of λ ()
db-active (takeResult j) e eq with lookup j (dbWaits e)
... | nothing = case eq of λ ()
... | just d with lookup d (dbWrites e)
...   | just (_ , true) = case just-injective eq of λ { refl → refl }
...   | nothing = case eq of λ ()
...   | just (_ , false) = case eq of λ ()
db-active (abandonWait j) e eq with lookup j (dbWaits e)
... | nothing = case eq of λ ()
... | just d with lookup d (dbWrites e) | dbSealed e
...   | just (_ , false) | just _ = case just-injective eq of λ { refl → refl }
...   | nothing | _ = case eq of λ ()
...   | just (_ , true) | _ = case eq of λ ()
...   | just (_ , false) | nothing = case eq of λ ()

install-quiet : ∀ attachment hid mid k ps flow r queue {g q′} → continuation r ≡ exited → active (execution r) ≡ false →
  installWith attachment hid mid k ps flow r queue ≡ just (g , q′) → Quiet g
install-quiet attachment hid mid k ps flow r queue cont act eq
  with lookup hid (handles (execution r)) | lookup mid (muxes (execution r)) | ordered ps | supported ps
... | nothing | nothing | true | true = case just-injective eq of λ { refl → cont , act }
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
install-initiator-quiet : ∀ hid mid k ps flow r queue {g q′} → continuation r ≡ exited → active (execution r) ≡ false →
  installInitiatorWith hid mid k ps flow r queue ≡ just (g , q′) → Quiet g
install-initiator-quiet hid mid k ps flow r queue cont act eq
  with lookup hid (handles (execution r)) | lookup mid (muxes (execution r)) | ordered ps | supported ps
... | nothing | nothing | true | true = case just-injective eq of λ { refl → cont , act }
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()

quiet-worker : ∀ a r queue {g q′} → continuation r ≡ exited → active (execution r) ≡ false →
  stepWorker a r queue ≡ just (g , q′) → Quiet g
quiet-worker deactivateIG (runtimeState p n c (engine h ms ts a lt cr nr rs ds dw dwt eb)) queue cont refl eq = case eq of λ ()
quiet-worker flushOnExit (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker (captureTime time) (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker registerInactivity (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker selectBatch (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker readEvent (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker registerIdleTimer (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker runResponders (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker commitDecision (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker requestFailedStop (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker finishBatch (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker pollStopped (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker restart (runtimeState p n c e) queue refl act eq = case eq of λ ()
quiet-worker (installHandle hid mid k ps flow) r queue cont act eq = install-quiet M.igTracer hid mid k ps flow r queue cont act eq
quiet-worker (installOutboundHandle hid mid k ps flow) r queue cont act eq =
  install-quiet (outboundTracer responderMode flow) hid mid k ps flow r queue cont act eq
quiet-worker (leiosDb a) r queue cont act eq with stepDb a (execution r) in stepped
... | nothing = case eq of λ ()
... | just e = case just-injective eq of λ { refl → cont , trans (db-active a (execution r) stepped) act }
quiet-worker (expireTimer t) r queue cont act eq with lookup t (timers (execution r))
... | just ticking = case just-injective eq of λ { refl → cont , act }
... | nothing = case eq of λ ()
... | just expired = case eq of λ ()
quiet-worker (egressStep mid action) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.Egress.step action (M.egress m) | bucketStep mid action (M.egress m) (egressBuckets (execution r))
...   | just next | just bs = case just-injective eq of λ { refl → cont , act }
...   | nothing | _ = case eq of λ ()
...   | just _ | nothing = case eq of λ ()
quiet-worker (configureEgress mid plan limit bound keys) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with pristine (M.egress m) ∧ keysListed keys (M.protocols m) | M.Egress.initial plan limit bound keys
...   | true | just e = case just-injective eq of λ { refl → cont , act }
...   | true | nothing = case eq of λ ()
...   | false | _ = case eq of λ ()
quiet-worker (registerCells mid) r queue cont act eq with lookup mid (muxes (execution r)) | rowOf mid (counterRows (execution r))
... | just m | nothing = case just-injective eq of λ { refl → cont , act }
... | nothing | _ = case eq of λ ()
... | just _ | just _ = case eq of λ ()
quiet-worker (retireCells mid) r queue cont act eq with lookup mid (muxes (execution r)) | rowOf mid (counterRows (execution r))
... | just m | just i = case just-injective eq of λ { refl → cont , act }
... | nothing | _ = case eq of λ ()
... | just _ | nothing = case eq of λ ()
quiet-worker (sampleTracer mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.readActive tr = case just-injective eq of λ { refl → cont , act }
...   | M.igTracer | M.readActive tr = case just-injective eq of λ { refl → cont , act }
...   | M.noIGTracer | M.commitTrace _ _ = case eq of λ ()
...   | M.noIGTracer | M.afterStart _ = case eq of λ ()
...   | M.noIGTracer | M.forkPending _ = case eq of λ ()
...   | M.noIGTracer | M.afterFailure = case eq of λ ()
...   | M.noIGTracer | M.tracerFailed _ = case eq of λ ()
...   | M.noIGTracer | M.returned = case eq of λ ()
...   | M.igTracer | M.commitTrace _ _ = case eq of λ ()
...   | M.igTracer | M.afterStart _ = case eq of λ ()
...   | M.igTracer | M.forkPending _ = case eq of λ ()
...   | M.igTracer | M.afterFailure = case eq of λ ()
...   | M.igTracer | M.tracerFailed _ = case eq of λ ()
...   | M.igTracer | M.returned = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.commitTrace flag tr = case just-injective eq of λ { refl → cont , act }
...   | M.igTracer | M.commitTrace false tr = case just-injective eq of λ { refl → cont , act }
...   | M.igTracer | M.commitTrace true tr with Readiness.prefixReady (M.key m) tr (tracerView (M.key m) r) (M.traceCounters m) queue
...     | false = case eq of λ ()
...     | true with missingDescriptor tr (tracerView (M.key m) r) (M.traceCounters m)
...       | just n = case just-injective eq of λ { refl → cont , act }
...       | nothing with M.traceSTM (M.key m) tr (tracerView (M.key m) r) (M.traceCounters m) queue
...         | nothing = case eq of λ ()
...         | just (rc , q) = case just-injective eq of λ { refl → cont , act }
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.readActive _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.afterStart _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.forkPending _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.afterFailure = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.tracerFailed _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.noIGTracer | M.returned = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.readActive _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.afterStart _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.forkPending _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.afterFailure = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.tracerFailed _ = case eq of λ ()
quiet-worker (commitTracer mid) r queue cont act eq | just m | M.igTracer | M.returned = case eq of λ ()
quiet-worker (finishStart mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.afterStart n = case just-injective eq of λ { refl → cont , act }
...   | M.readActive _ = case eq of λ ()
...   | M.commitTrace _ _ = case eq of λ ()
...   | M.forkPending _ = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed _ = case eq of λ ()
...   | M.returned = case eq of λ ()
quiet-worker (forkResponder mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.forkPending n = case just-injective eq of λ { refl → cont , act }
...   | M.readActive _ = case eq of λ ()
...   | M.commitTrace _ _ = case eq of λ ()
...   | M.afterStart _ = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed _ = case eq of λ ()
...   | M.returned = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.completions m | M.commands m
...   | M.returned | M.ready | [] | M.startCommand p ∷ rest with startMode p
...     | eagerly = case just-injective eq of λ { refl → cont , act }
...     | onDemand = case just-injective eq of λ { refl → cont , act }
...     | onDemandAny = case just-injective eq of λ { refl → cont , act }
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.ready | [] | M.shutdown ∷ rest = case just-injective eq of λ { refl → cont , act }
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.afterFailure | _ | _ | _ = case just-injective eq of λ { refl → cont , act }
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.readActive _ | _ | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.commitTrace _ _ | _ | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.afterStart _ | _ | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.forkPending _ | _ | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.tracerFailed _ | _ | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.ready | [] | [] = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.ready | _ ∷ _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.stopping | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.stopped | _ | _ = case eq of λ ()
quiet-worker (monitorCommand mid) r queue cont act eq | just m | M.returned | M.failed _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.completions m
...   | M.returned | M.ready | M.jobResult M.responderJob n outcome ∷ rest with outcome
...     | clean = case just-injective eq of λ { refl → cont , act }
...     | errored err = case just-injective eq of λ { refl → cont , act }
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.returned | M.ready | M.jobResult M.initiatorJob n outcome ∷ rest with outcome
... | clean = case just-injective eq of λ { refl → cont , act }
... | errored err = case just-injective eq of λ { refl → cont , act }
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.readActive _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.commitTrace _ _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.afterStart _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.forkPending _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.afterFailure | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.tracerFailed _ | _ | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.returned | M.ready | [] = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.returned | M.stopping | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.returned | M.stopped | _ = case eq of λ ()
quiet-worker (monitorCompletion mid) r queue cont act eq | just m | M.returned | M.failed _ | _ = case eq of λ ()
quiet-worker (startOnDemand mid n) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.commands m | M.completions m | lookup n (M.waiting m)
...   | M.returned | M.ready | [] | [] | just onDemand = case just-injective eq of λ { refl → cont , act }
...   | M.readActive _ | _ | _ | _ | _ = case eq of λ ()
...   | M.commitTrace _ _ | _ | _ | _ | _ = case eq of λ ()
...   | M.afterStart _ | _ | _ | _ | _ = case eq of λ ()
...   | M.forkPending _ | _ | _ | _ | _ = case eq of λ ()
...   | M.afterFailure | _ | _ | _ | _ = case eq of λ ()
...   | M.tracerFailed _ | _ | _ | _ | _ = case eq of λ ()
...   | M.returned | M.ready | [] | [] | nothing = case eq of λ ()
...   | M.returned | M.ready | [] | [] | just onDemandAny = case eq of λ ()
...   | M.returned | M.ready | [] | [] | just eagerly = case eq of λ ()
...   | M.returned | M.ready | [] | _ ∷ _ | _ = case eq of λ ()
...   | M.returned | M.ready | _ ∷ _ | _ | _ = case eq of λ ()
...   | M.returned | M.stopping | _ | _ | _ = case eq of λ ()
...   | M.returned | M.stopped | _ | _ | _ = case eq of λ ()
...   | M.returned | M.failed _ | _ | _ | _ = case eq of λ ()
quiet-worker (finishProtocol mid n outcome) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with lookup n (M.protocols m) | hasJob n (M.runningJobs m)
...   | just M.running | true with outcome
...     | clean = case just-injective eq of λ { refl → cont , act }
...     | errored _ = case just-injective eq of λ { refl → cont , act }
quiet-worker (finishProtocol mid n outcome) r queue cont act eq | just m | nothing | _ = case eq of λ ()
quiet-worker (finishProtocol mid n outcome) r queue cont act eq | just m | just M.idle | _ = case eq of λ ()
quiet-worker (finishProtocol mid n outcome) r queue cont act eq | just m | just M.demand | _ = case eq of λ ()
quiet-worker (finishProtocol mid n outcome) r queue cont act eq | just m | just M.demandAny | _ = case eq of λ ()
quiet-worker (finishProtocol mid n outcome) r queue cont act eq | just m | just M.running | false = case eq of λ ()
quiet-worker (publishJobResult mid n) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with lookup n (M.finishedJobs m)
...   | nothing = case eq of λ ()
...   | just outcome = case just-injective eq of λ { refl → cont , act }
quiet-worker (publishJobOccurrence mid i) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with takePending i (M.finishedJobs m)
...   | nothing = case eq of λ ()
...   | just ((n , outcome) , retained) = case just-injective eq of λ { refl → cont , act }
quiet-worker (recordMuxFailure mid err) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | M.readActive _ = case eq of λ ()
...   | M.ready | M.commitTrace _ _ = case eq of λ ()
...   | M.ready | M.afterStart _ = case eq of λ ()
...   | M.ready | M.forkPending _ = case eq of λ ()
...   | M.ready | M.afterFailure = case eq of λ ()
...   | M.ready | M.tracerFailed _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()
quiet-worker (recordMuxStopped mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | M.readActive _ = case eq of λ ()
...   | M.ready | M.commitTrace _ _ = case eq of λ ()
...   | M.ready | M.afterStart _ = case eq of λ ()
...   | M.ready | M.forkPending _ = case eq of λ ()
...   | M.ready | M.afterFailure = case eq of λ ()
...   | M.ready | M.tracerFailed _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()
quiet-worker (traceMuxDead mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.stopped | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.failed err | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | M.readActive _ = case eq of λ ()
...   | M.stopped | M.commitTrace _ _ = case eq of λ ()
...   | M.stopped | M.afterStart _ = case eq of λ ()
...   | M.stopped | M.forkPending _ = case eq of λ ()
...   | M.stopped | M.afterFailure = case eq of λ ()
...   | M.stopped | M.tracerFailed _ = case eq of λ ()
...   | M.failed _ | M.readActive _ = case eq of λ ()
...   | M.failed _ | M.commitTrace _ _ = case eq of λ ()
...   | M.failed _ | M.afterStart _ = case eq of λ ()
...   | M.failed _ | M.forkPending _ = case eq of λ ()
...   | M.failed _ | M.afterFailure = case eq of λ ()
...   | M.failed _ | M.tracerFailed _ = case eq of λ ()
quiet-worker (traceGracefulMuxStopped mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.stopped | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | M.readActive _ = case eq of λ ()
...   | M.stopped | M.commitTrace _ _ = case eq of λ ()
...   | M.stopped | M.afterStart _ = case eq of λ ()
...   | M.stopped | M.forkPending _ = case eq of λ ()
...   | M.stopped | M.afterFailure = case eq of λ ()
...   | M.stopped | M.tracerFailed _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()
quiet-worker (enqueueMuxStop mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m = case just-injective eq of λ { refl → cont , act }
quiet-worker (takeShutdownCommand mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m | M.completions m | M.commands m
...   | M.ready | M.returned | [] | M.shutdown ∷ rest = case just-injective eq of λ { refl → cont , act }
...   | M.ready | M.readActive _ | _ | _ = case eq of λ ()
...   | M.ready | M.commitTrace _ _ | _ | _ = case eq of λ ()
...   | M.ready | M.afterStart _ | _ | _ = case eq of λ ()
...   | M.ready | M.forkPending _ | _ | _ = case eq of λ ()
...   | M.ready | M.afterFailure | _ | _ = case eq of λ ()
...   | M.ready | M.tracerFailed _ | _ | _ = case eq of λ ()
...   | M.ready | M.returned | [] | [] = case eq of λ ()
...   | M.ready | M.returned | [] | (M.startCommand _) ∷ _ = case eq of λ ()
...   | M.ready | M.returned | _ ∷ _ | _ = case eq of λ ()
...   | M.stopping | _ | _ | _ = case eq of λ ()
...   | M.stopped | _ | _ | _ = case eq of λ ()
...   | M.failed _ | _ | _ | _ = case eq of λ ()
quiet-worker (recordMuxStopping mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.ready | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | M.readActive _ = case eq of λ ()
...   | M.ready | M.commitTrace _ _ = case eq of λ ()
...   | M.ready | M.afterStart _ = case eq of λ ()
...   | M.ready | M.forkPending _ = case eq of λ ()
...   | M.ready | M.afterFailure = case eq of λ ()
...   | M.ready | M.tracerFailed _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()
quiet-worker (completeMuxStopping mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.stopping | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | _ = case eq of λ ()
...   | M.stopping | M.readActive _ = case eq of λ ()
...   | M.stopping | M.commitTrace _ _ = case eq of λ ()
...   | M.stopping | M.afterStart _ = case eq of λ ()
...   | M.stopping | M.forkPending _ = case eq of λ ()
...   | M.stopping | M.afterFailure = case eq of λ ()
...   | M.stopping | M.tracerFailed _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()
quiet-worker (discardJobOccurrence mid i) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with takePending i (M.finishedJobs m)
...   | nothing = case eq of λ ()
...   | just (chosen , retained) = case just-injective eq of λ { refl → cont , act }
quiet-worker (recordAsyncMuxFailure mid err) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.readActive _ = case eq of λ ()
...   | M.commitTrace _ _ = case eq of λ ()
...   | M.afterStart _ = case eq of λ ()
...   | M.forkPending _ = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed _ = case eq of λ ()
quiet-worker (recordInterruptedMuxFailure mid err) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.interruptibleCallback (M.callback m)
...   | true = case just-injective eq of λ { refl → cont , act }
...   | false = case eq of λ ()
quiet-worker (traceInterruptedMuxDead mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.interruptibleCallback (M.callback m)
...   | M.failed err | true = case just-injective eq of λ { refl → cont , act }
...   | M.ready | _ = case eq of λ ()
...   | M.stopping | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | false = case eq of λ ()
quiet-worker (finishStop mid) r queue cont act eq with lookup mid (muxes (execution r))
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.stopping | M.returned = case just-injective eq of λ { refl → cont , act }
...   | M.ready | _ = case eq of λ ()
...   | M.stopping | M.readActive _ = case eq of λ ()
...   | M.stopping | M.commitTrace _ _ = case eq of λ ()
...   | M.stopping | M.afterStart _ = case eq of λ ()
...   | M.stopping | M.forkPending _ = case eq of λ ()
...   | M.stopping | M.afterFailure = case eq of λ ()
...   | M.stopping | M.tracerFailed _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed _ | _ = case eq of λ ()

-- Every IG step, in either responder mode.
quiet-step : ∀ mode a r queue {g q′} → continuation r ≡ exited → active (execution r) ≡ false →
  step mode a r queue ≡ just (g , q′) → Quiet g
quiet-step noResponderMode (installOutboundHandle hid mid k ps flow) r queue cont act eq =
  install-initiator-quiet hid mid k ps flow r queue cont act eq
quiet-step noResponderMode (configureEgress mid plan limit bound keys) r queue cont act eq with initiatorKeys keys
... | true = quiet-worker (configureEgress mid plan limit bound keys) r queue cont act eq
... | false = case eq of λ ()
quiet-step noResponderMode (registerCells mid) r queue cont act eq = quiet-worker (registerCells mid) r queue cont act eq
quiet-step noResponderMode (retireCells mid) r queue cont act eq = quiet-worker (retireCells mid) r queue cont act eq
quiet-step noResponderMode (captureTime t) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode registerInactivity r queue cont act eq = case eq of λ ()
quiet-step noResponderMode selectBatch r queue cont act eq = case eq of λ ()
quiet-step noResponderMode readEvent r queue cont act eq = case eq of λ ()
quiet-step noResponderMode registerIdleTimer r queue cont act eq = case eq of λ ()
quiet-step noResponderMode runResponders r queue cont act eq = case eq of λ ()
quiet-step noResponderMode commitDecision r queue cont act eq = case eq of λ ()
quiet-step noResponderMode requestFailedStop r queue cont act eq = case eq of λ ()
quiet-step noResponderMode finishBatch r queue cont act eq = case eq of λ ()
quiet-step noResponderMode pollStopped r queue cont act eq = case eq of λ ()
quiet-step noResponderMode restart r queue cont act eq = case eq of λ ()
quiet-step noResponderMode deactivateIG r queue cont act eq = case eq of λ ()
quiet-step noResponderMode flushOnExit r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (expireTimer t) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (installHandle hid mid k ps flow) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (monitorCommand mid) r queue cont act eq with runtimeAllowed (monitorCommand mid) r
... | true = quiet-worker (monitorCommand mid) r queue cont act eq
... | false = case eq of λ ()
quiet-step noResponderMode (monitorCompletion mid) r queue cont act eq with runtimeAllowed (monitorCompletion mid) r
... | true = quiet-worker (monitorCompletion mid) r queue cont act eq
... | false = case eq of λ ()
quiet-step noResponderMode (sampleTracer mid) r queue cont act eq = quiet-worker (sampleTracer mid) r queue cont act eq
quiet-step noResponderMode (commitTracer mid) r queue cont act eq = quiet-worker (commitTracer mid) r queue cont act eq
quiet-step noResponderMode (finishStart mid) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (forkResponder mid) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (finishStop mid) r queue cont act eq = quiet-worker (finishStop mid) r queue cont act eq
quiet-step noResponderMode (startOnDemand mid n) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (publishJobResult mid n) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (publishJobOccurrence mid n) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (recordMuxFailure mid err) r queue cont act eq = quiet-worker (recordMuxFailure mid err) r queue cont act eq
quiet-step noResponderMode (recordMuxStopped mid) r queue cont act eq = quiet-worker (recordMuxStopped mid) r queue cont act eq
quiet-step noResponderMode (traceMuxDead mid) r queue cont act eq = quiet-worker (traceMuxDead mid) r queue cont act eq
quiet-step noResponderMode (takeShutdownCommand mid) r queue cont act eq = quiet-worker (takeShutdownCommand mid) r queue cont act eq
quiet-step noResponderMode (recordMuxStopping mid) r queue cont act eq = quiet-worker (recordMuxStopping mid) r queue cont act eq
quiet-step noResponderMode (completeMuxStopping mid) r queue cont act eq = quiet-worker (completeMuxStopping mid) r queue cont act eq
quiet-step noResponderMode (enqueueMuxStop mid) r queue cont act eq = quiet-worker (enqueueMuxStop mid) r queue cont act eq
quiet-step noResponderMode (discardJobOccurrence mid n) r queue cont act eq = quiet-worker (discardJobOccurrence mid n) r queue cont act eq
quiet-step noResponderMode (recordAsyncMuxFailure mid err) r queue cont act eq = quiet-worker (recordAsyncMuxFailure mid err) r queue cont act eq
quiet-step noResponderMode (recordInterruptedMuxFailure mid err) r queue cont act eq = quiet-worker (recordInterruptedMuxFailure mid err) r queue cont act eq
quiet-step noResponderMode (traceInterruptedMuxDead mid) r queue cont act eq = quiet-worker (traceInterruptedMuxDead mid) r queue cont act eq
quiet-step noResponderMode (traceGracefulMuxStopped mid) r queue cont act eq = quiet-worker (traceGracefulMuxStopped mid) r queue cont act eq
quiet-step noResponderMode (finishProtocol mid n result) r queue cont act eq = case eq of λ ()
quiet-step noResponderMode (egressStep mid action) r queue cont act eq = quiet-worker (egressStep mid action) r queue cont act eq
quiet-step noResponderMode (leiosDb a) r queue cont act eq = quiet-worker (leiosDb a) r queue cont act eq
quiet-step responderMode a r queue cont act eq = quiet-worker a r queue cont act eq
