{-# OPTIONS --guardedness #-}

-- Explicit remaining auxiliary content targets and their real writer facts.
-- Coverage is deliberately a separate obligation: these records alone do not
-- assert that all stored rows have been covered along a frontend run.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxContent (b : ErrorId → Bool) where

import Data.Nat
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain hiding (mux; job; handle)
open import ConnectionManagement.IGTypes using (RunResult)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxDeltaQ as Delta
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Properties.MuxProtocolJobs as Jobs
import ConnectionManagement.Properties.MuxDeltaQCapture as Capture
module U = P.U
module Pool = P.Pool
module M = Monitor b
module G = Group b
module D = Delta b

-- Published owner identity is independent of startup and mutable pool contents.
record Owner (w : WorkerId) (s : P.State) : Set where
 constructor owner
 field frame : U.Frame
       handle : HandleId
       mux : MuxId
       found : lookup w (U.frames (P.base s)) ≡ just frame
       published : U.progress frame ≡ U.promisePublished handle mux
open Owner public
record JobContent (j : JobId) (job : Types.ProtocolJob) (s : P.State) : Set where
 constructor job-content
 field owner-reference : Owner (Types.owner job) s
       mux-matches : mux owner-reference ≡ Types.mux job
       physical-phase : Pool.ThreadPhase
       physical-found : lookup j (Pool.handles (P.poolAt (Types.owner job) s)) ≡ just physical-phase
open JobContent public

-- A typed protocol result fixes the complete immutable captured job identity,
-- including owner, mux, direction, protocol number and generation.
ProtocolResult : WorkerId → Mux.JobDirection → Data.Nat.ℕ → RunId → RunResult → P.State → Set
ProtocolResult w dir n gen result s = Σ JobId (λ j → Σ MuxId (λ mid →
  lookup j (P.jobs s) ≡ just (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) ×
  JobContent j (Types.protocolJob w mid dir n gen (Types.resultCaptured result)) s))

-- Infrastructure tags omit the lane identity, so backing is existential in the
-- actual configured startup role; it must not be inferred from the tag alone.
record Infrastructure (w : WorkerId) (item : Types.TypedResult) (s : P.State) : Set where
 field owner-reference : Owner w s
       role : Types.Role
       job : JobId
       error : ErrorId
       role-found : P.infraId role (P.Startup.phase (U.startup (frame owner-reference))) ≡ just job
       tagged : Types.infraResult role error ≡ item
       physical-phase : Pool.ThreadPhase
       physical-found : lookup job (Pool.handles (P.poolAt w s)) ≡ just physical-phase
Completion : WorkerId → Types.TypedResult → P.State → Set
Completion w (Types.protocolCompletion dir n gen result) s = ProtocolResult w dir n gen result s
Completion w (Types.infraMuxer err) s = Infrastructure w (Types.infraMuxer err) s
Completion w (Types.infraDemuxer err) s = Infrastructure w (Types.infraDemuxer err) s

-- This mutually supporting queue/body invariant is the missing bridge between
-- actual pool publication and the typed PC/ticket content targets below.
record PoolContent (w : WorkerId) (s : P.State) : Set where
 field queued : All (λ item → Completion w item s) (Pool.completions (P.poolAt w s))
       returned : ∀ j item → lookup j (Pool.handles (P.poolAt w s)) ≡ just (Pool.bodyReturned item) → Completion w item s

-- The in-flight cancel target is a reference even between request/delivery.
CancelContent : WorkerId → G.CancelPC → P.State → Set
CancelContent w G.ready s = ⊤
CancelContent w (G.requested j) s = Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase)
CancelContent w (G.delivered j) s = Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase)

record ControlContent (w : WorkerId) (control : G.Frame) (s : P.State) : Set where
 field owner-reference : Owner w s
       cancellation-backed : CancelContent w (G.cancelPC control) s
       snapshot-backed : All (λ j → Σ Types.ProtocolJob (λ job → lookup j (P.jobs s) ≡ just job × Types.owner job ≡ w × JobContent j job s)) (G.snapshot control)
       remaining-backed : All (λ j → Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase)) (G.remaining control)
       joined-backed : All (λ j → Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles (P.poolAt w s)) ≡ just phase)) (G.joined control)
record PCContent (w : WorkerId) (pc : M.PC) (s : P.State) : Set where
 field owner-reference : Owner w s
       selected-backed : ∀ item → pc ≡ M.selected item → Completion w item s
record TicketContent (w : WorkerId) (ticket : D.Ticket) (s : P.State) : Set where
 field owner-reference : Owner w s
       payload-backed : Completion w (D.payload ticket) s

-- These are the exact all-row obligations still needed above the writer facts.
record Coverage (s : D.State) : Set where
 field controls : All (λ { (w , row) → ControlContent w row (G.protocolState (D.W.base (D.R.base (D.base s)))) }) (G.controls (D.W.base (D.R.base (D.base s))))
       pcs : All (λ { (w , pc) → PCContent w pc (M.base (D.monitor s)) }) (M.pcs (D.monitor s))
       tickets : All (λ { (w , savedTicket) → TicketContent w savedTicket (M.base (D.monitor s)) }) (D.tickets s)
       jobs : All (λ { (j , job) → JobContent j job (M.base (D.monitor s)) }) (P.jobs (M.base (D.monitor s)))

-- Actual owner-context selection establishes the owner part of new PCs and
-- controls, rather than adopting a default pcAt/frameAt value.
owner-context : ∀ w s {f mid} → M.ownerContext w s ≡ just (f , mid) → Owner w (M.base s)
owner-context w s eq with lookup w (U.frames (P.base (M.base s))) in found
... | nothing = case eq of λ ()
... | just f with U.progress f in progress | P.monitoring f
...   | U.promisePublished hid mid | Data.Bool.true = case just-injective eq of λ { refl → owner f hid mid found progress }
...   | U.promisePublished hid mid | Data.Bool.false = case eq of λ ()
...   | (U.handshakePending helperPC) | _ = case eq of λ ()
...   | U.returnedSuccess | _ = case eq of λ ()
...   | U.handleAllocated hid mid | _ = case eq of λ ()

-- The physical fork establishes a non-fabricated job handle in its owner's
-- actual pool. Both responder and initiator observations use this same lemma.
fork-handle : ∀ j pool {next} → Pool.step (Pool.fork j) pool ≡ just next → lookup j (Pool.handles next) ≡ just Pool.bodyRunning
fork-handle j pool eq with Pool.phase pool | Pool.parentFork pool | lookup j (Pool.handles pool)
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl → lookup-put j Pool.bodyRunning (Pool.handles pool) }
... | Pool.openPool | just _ | _ = case eq of λ ()
... | Pool.openPool | nothing | just _ = case eq of λ ()
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | Pool.cancelPending _ | _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ | _ = case eq of λ ()

fork-established : ∀ w j gen s {t} → (observation : Jobs.Fork w j gen s t) →
 JobContent j (Types.protocolJob w (Jobs.Fork.capturedMux observation) (Jobs.Fork.capturedDirection observation)
   (Jobs.Fork.capturedNumber observation) gen Types.executing) t
fork-established w j gen s observation rewrite Jobs.Fork.after-shape observation =
 job-content
   (owner _ (Jobs.Fork.allocatedHandle observation) (Jobs.Fork.capturedMux observation)
     (lookup-put w _ (U.frames (P.base s))) (Jobs.Fork.allocated-before observation)) refl Pool.bodyRunning
   (trans (cong (λ p → lookup j (Pool.handles p)) (Jobs.pool-same w (Jobs.Fork.ownerFrame observation) (Jobs.Fork.poolAfter observation) (P.setSource (Jobs.Fork.sourceAfter observation) s)))
     (fork-handle j (P.poolAt w s) (Jobs.Fork.actual-fork observation)))

-- The existing dequeue theorem supplies an exact FIFO origin at ticket birth.
-- Turning it into Coverage.tickets still needs Completion for every pool head.
ticket-writer = Capture.consume-captures-head b

import ConnectionManagement.Properties.MuxResultMonitor as MonitorFacts
-- A successful real dequeue plus PoolContent supplies the exact typed payload
-- at the capture boundary. PoolContent preservation is a separate open theorem.
ticket-writer-content : ∀ w s {t} →
 (actual : D.step (D.run (D.wrapMonitor (M.consume w))) s ≡ just t) →
 PoolContent w (M.base (D.monitor s)) →
 Completion w (MonitorFacts.Dequeue.head (Capture.CapturedHead.dequeue (ticket-writer w s actual))) (M.base (D.monitor s))
ticket-writer-content w s actual good = All.head
 (subst (All (λ item → Completion w item (M.base (D.monitor s))))
   (MonitorFacts.Dequeue.original-queue (Capture.CapturedHead.dequeue (ticket-writer w s actual))) (PoolContent.queued good))
