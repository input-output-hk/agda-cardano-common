{-# OPTIONS --guardedness #-}

-- Tickets copy certified selected PCs, and retain payloads across phase marks.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxTickets (b : ErrorId → Bool) where
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
import ConnectionManagement.MuxDeltaQ as Delta
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
module D = Delta b
module R = D.R
module X = D.X
module W = D.W
module G = D.G
module M = D.M
module P = D.P
module A = Content b
module T = Transport b
module MF = MonitorFacts b

Rows : Store WorkerId D.Ticket → P.State → Set
Rows rows p = All (λ { (w , savedTicket) → A.TicketContent w savedTicket p }) rows
Tickets : D.State → Set
Tickets s = Rows (D.tickets s) (M.base (D.monitor s))
rows-kept : ∀ rows {s t} → T.Retains s t → Rows rows s → Rows rows t
rows-kept rows kept = All.map (λ { {w , savedTicket} → T.ticket-kept kept w savedTicket })
selected : ∀ w m item → M.pcAt w m ≡ M.selected item → MF.PCs (M.pcs m) (M.base m) → A.PCContent w (M.selected item) (M.base m)
selected w m item eq good with lookup w (M.pcs m) in found
... | nothing = case eq of λ ()
... | just pc = case just-injective (Relation.Binary.PropositionalEquality.cong just eq) of λ { refl →
 T.Rows.at (λ q row → A.PCContent q row (M.base m)) (M.pcs m) good w (M.selected item) found }

-- This local writer requires no fabricated owner from default pcAt waiting.
note-preserves : ∀ a r rows →
 MF.PCs (M.pcs (G.base (W.base (R.base r)))) (R.protocols r) →
 Rows rows (R.protocols r) → Rows (D.note a r rows) (R.protocols r)
note-preserves (R.run (X.run (W.run (G.run (M.consume w))))) r rows pcs good with M.pcAt w (G.base (W.base (R.base r))) in chosen
... | M.selected item = T.Rows.insert (λ q saved → A.TicketContent q saved (R.protocols r)) w (D.ticket item D.captured) rows
 (record { owner-reference = A.PCContent.owner-reference backing; payload-backed = A.PCContent.selected-backed backing item refl }) good
 where backing = selected w (G.base (W.base (R.base r))) item chosen pcs
... | M.waiting = good
... | M.responderTracing outcome = good
... | M.initiatorTracing outcome = good
... | M.deadReady outcome = good
... | M.deadTracing outcome = good
... | M.finished outcome = good
note-preserves (R.observeFailure _ _ _) r rows pcs good = good
note-preserves (R.observeCancellation _ _ _) r rows pcs good = good
note-preserves (R.deliverShutdown _ _) r rows pcs good = good
note-preserves (R.beginClose _ _) r rows pcs good = good
note-preserves (R.requestCancel _) r rows pcs good = good
note-preserves (R.deliverCancel _) r rows pcs good = good
note-preserves (R.join _) r rows pcs good = good
note-preserves (R.finishClose _) r rows pcs good = good
note-preserves (R.continueSync _) r rows pcs good = good
note-preserves (R.writeAsyncFailure _) r rows pcs good = good
note-preserves (R.beginDead _) r rows pcs good = good
note-preserves (R.sampleDead _) r rows pcs good = good
note-preserves (R.commitDead _) r rows pcs good = good
note-preserves (R.finishDead _) r rows pcs good = good
note-preserves (R.handoff _) r rows pcs good = good
note-preserves (R.observeDeadTraceException _ _) r rows pcs good = good
note-preserves (R.run (X.observeCancellation _ _ _)) r rows pcs good = good
note-preserves (R.run (X.deliverShutdown _ _)) r rows pcs good = good
note-preserves (R.run (X.observeErrorTraceException _ _)) r rows pcs good = good
note-preserves (R.run (X.run (W.beginExit _))) r rows pcs good = good
note-preserves (R.run (X.run (W.observeBufferReturn _))) r rows pcs good = good
note-preserves (R.run (X.run (W.observeBufferException _ _))) r rows pcs good = good
note-preserves (R.run (X.run (W.choosePolicy _ _))) r rows pcs good = good
note-preserves (R.run (X.run (W.observeErrorTrace _))) r rows pcs good = good
note-preserves (R.run (X.run (W.observeNodeDelivery _))) r rows pcs good = good
note-preserves (R.run (X.run (W.rethrow _))) r rows pcs good = good
note-preserves (R.run (X.run (W.enterFinalizer _))) r rows pcs good = good
note-preserves (R.run (X.run (W.finishCleanup _))) r rows pcs good = good
note-preserves (R.run (X.run (W.publishAsyncResult _))) r rows pcs good = good
note-preserves (R.run (X.run (W.cleanup _ _))) r rows pcs good = good
note-preserves (R.run (X.run (W.shutdownStep _))) r rows pcs good = good
note-preserves (R.run (X.run (W.deliverShutdownMux _))) r rows pcs good = good
note-preserves (R.run (X.run (W.deliverShutdownTimeWait _))) r rows pcs good = good
note-preserves (R.run (X.run W.acknowledgeFinished)) r rows pcs good = good
note-preserves (R.run (X.run (W.deliverReleaseMux _ _))) r rows pcs good = good
note-preserves (R.run (X.run (W.deliverReleaseTimeWait _ _))) r rows pcs good = good
note-preserves (R.run (X.run (W.acknowledgeReleaseFinished _))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.requestShutdown _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.selectShutdown _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.observeStoppingTrace _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.writeStopping _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.requestGroupCancel _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.deliverGroup _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.joinGroup _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishGroup _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.drainEmpty _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.timeout2Elapsed _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.writeStopped _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.observeTraceStopped _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.sampleStoppedTracer _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.commitStoppedTracer _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishStoppedTrace _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.retireCounters _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.captureGroup _ _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishChildUnwind _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.unwindReplacedBySync _ _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.abortOwner _ _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.beginWholeClose _ _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.requestWholeCancel _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.deliverWhole _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.joinWhole _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishWholeClose _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishNormalScope _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.writeAsyncFailure _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.beginAsyncDead _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.sampleAsyncTracer _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.commitAsyncTracer _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.finishAsyncDead _)))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.run _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.handleSelected _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.sampleTracer _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.commitTracer _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.finishProtocolTrace _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.beginDead _))))) r rows pcs good = good
note-preserves (R.run (X.run (W.run (G.run (M.finishDead _))))) r rows pcs good = good

-- Phase changes retain the payload of the selected saved savedTicket exactly.
mark-preserves : ∀ w saved phase s → lookup w (D.tickets s) ≡ just saved → Tickets s → Tickets (D.mark w saved phase s)
mark-preserves w saved phase s found good = T.Rows.insert (λ q savedTicket → A.TicketContent q savedTicket (M.base (D.monitor s))) w (record saved { phase = phase }) (D.tickets s)
 (record { owner-reference = A.TicketContent.owner-reference backing; payload-backed = A.TicketContent.payload-backed backing }) good
 where backing = T.Rows.at (λ q savedTicket → A.TicketContent q savedTicket (M.base (D.monitor s))) (D.tickets s) good w saved found
