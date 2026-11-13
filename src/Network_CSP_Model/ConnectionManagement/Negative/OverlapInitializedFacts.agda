{-# OPTIONS --guardedness #-}

-- Delayed cleanup writes only the captured old entries after real replacement.
module ConnectionManagement.Negative.OverlapInitializedFacts where

open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I

import ConnectionManagement.Negative.InboundCleanLifecycle as Old
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Negative.OverlapInitialized as Run
import ConnectionManagement.Negative.OverlapInitialized16 as Before
import ConnectionManagement.Negative.OverlapInitialized17 as Tail
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- Nondependent endpoint pairing avoids an unconstrained dependent family.
pair : ∀ {A B : Set} → A → B → A × B
pair x y = x , y

handlerState : V.Runtime → W.State
handlerState s = N.R.base (N.raw (V.publication (V.base s)))

old-capture : lookup A.child₀ (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 0) (ident 0) (ident 0) A.key₀)
old-capture = refl

middle-capture : lookup (ident 31) (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 2) (ident 30) (ident 2) A.key₀)
middle-capture = refl

new-capture : lookup (ident 61) (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 3) (ident 60) (ident 3) A.key₀)
new-capture = refl

other-capture : lookup (ident 41) (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 1) (ident 40) (ident 1) A.key₁)
other-capture = refl

old-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared Run.final))) ≡ just (Shared.terminated nothing)
old-terminated = refl

middle-terminated : lookup (ident 2) (Shared.entries (Shared.cm (shared Run.final))) ≡ just (Shared.terminated nothing)
middle-terminated = refl

new-entry-unchanged : lookup (ident 3) (Shared.entries (Shared.cm (shared Run.final))) ≡ just (Shared.inboundIdle A.key₀ (ident 61) (ident 2) duplex)
new-entry-unchanged = refl

other-entry-unchanged : lookup (ident 1) (Shared.entries (Shared.cm (shared Run.final))) ≡ just (Shared.unnegotiated inbound A.key₁ (ident 41))
other-entry-unchanged = refl

before-map : Shared.mapCell (Shared.cm (shared Before.s10)) ≡ Shared.full (Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) []))
before-map = refl

after-map : Shared.mapCell (Shared.cm (shared Run.final)) ≡ Shared.full (Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) []))
after-map = refl

old-pending-result : W.resultOf A.child₀ (handlerState Before.s10) ≡ nothing
old-pending-result = refl

old-result : W.resultOf A.child₀ (handlerState Run.final) ≡ just (W.asyncException (errorId 42))
old-result = refl

old-cleanup : lookup A.child₀ (Shared.cleanups (shared Run.final)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
old-cleanup = refl

old-early-result-refused : V.advance (exit (W.publishAsyncResult A.child₀)) Before.s10 ≡ nothing
old-early-result-refused = refl

old-duplicate-finally-refused : V.advance (exit (W.cleanup A.child₀ Cleanup.finishTimeWait)) Run.final ≡ nothing
old-duplicate-finally-refused = refl

middle-pending-result : W.resultOf (ident 31) (handlerState Before.s10) ≡ nothing
middle-pending-result = refl

middle-result : W.resultOf (ident 31) (handlerState Run.final) ≡ just (W.asyncException (errorId 42))
middle-result = refl

middle-cleanup : lookup (ident 31) (Shared.cleanups (shared Run.final)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
middle-cleanup = refl

middle-early-result-refused : V.advance (exit (W.publishAsyncResult (ident 31))) Before.s10 ≡ nothing
middle-early-result-refused = refl

middle-duplicate-finally-refused : V.advance (exit (W.cleanup (ident 31) Cleanup.finishTimeWait)) Run.final ≡ nothing
middle-duplicate-finally-refused = refl

new-handler-still-live : W.resultOf (ident 61) (handlerState Run.final) ≡ nothing
new-handler-still-live = refl

new-socket-retained : lookup (ident 60) (Shared.sockets (shared Run.final)) ≡ just (Shared.handling (ident 61))
new-socket-retained = refl

other-socket-retained : lookup (ident 40) (Shared.sockets (shared Run.final)) ≡ just (Shared.handling (ident 41))
other-socket-retained = refl

new-normal-exit-not-ready : V.advance (exit (W.beginExit (ident 61))) Run.final ≡ nothing
new-normal-exit-not-ready = refl

old-cannot-purge-new : Cleanup.purgeCaptured A.key₀ (ident 0) (Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) [])) ≡ Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) [])
old-cannot-purge-new = refl

middle-cannot-purge-new : Cleanup.purgeCaptured A.key₀ (ident 2) (Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) [])) ≡ Shared.insertConnection A.key₁ (ident 1) (Shared.insertConnection A.key₀ (ident 3) [])
middle-cannot-purge-new = refl

allocation-supplies : pair (Shared.nextEntry (Shared.cm (shared Run.final))) (Shared.nextPromise (shared Run.final)) ≡ pair 4 4
allocation-supplies = refl

sockets-budget : length (Shared.sockets (shared Run.final)) ≡ 4
sockets-budget = refl

promises-budget : length (Shared.promises (shared Run.final)) ≡ 4
promises-budget = refl

handlers-budget : length (Shared.handlers (shared Run.final)) ≡ 4
handlers-budget = refl

entries-budget : length (Shared.entries (Shared.cm (shared Run.final))) ≡ 4
entries-budget = refl

handles-budget : length (IG.handles (IG.execution (governor Run.final))) ≡ 3
handles-budget = refl

muxes-budget : length (IG.muxes (IG.execution (governor Run.final))) ≡ 3
muxes-budget = refl

responder-jobs-budget : length (P.jobs (V.physical (V.base Run.final))) ≡ 2
responder-jobs-budget = refl


-- Both delayed finalizers really execute without changing the replacement map.
delayed-finalizers-preserve-map : Shared.mapCell (Shared.cm (shared Before.s10)) ≡
  Shared.mapCell (Shared.cm (shared Run.final))
delayed-finalizers-preserve-map = refl

-- Three pools retain six infrastructure allocations and two responder jobs.
old-pool-budget : length (Pool.handles (G.poolAt A.child₀ (V.group (V.base Run.final)))) ≡ 3
old-pool-budget = refl
middle-pool-budget : length (Pool.handles (G.poolAt (ident 31) (V.group (V.base Run.final)))) ≡ 3
middle-pool-budget = refl
new-pool-budget : length (Pool.handles (G.poolAt (ident 61) (V.group (V.base Run.final)))) ≡ 2
new-pool-budget = refl
timer-budget : IG.nextTimer (governor Run.final) ≡ 8
timer-budget = refl

-- The delayed work is precisely the captured TIME_WAIT finally, after receipt.
old-finally-pending : lookup A.child₀ (Shared.cleanups (shared Before.s10)) ≡
  just (Shared.cleanupFinalize (Shared.terminating A.key₀ A.child₀ nothing)
    (Shared.cleanupError (errorId 42)))
old-finally-pending = refl
middle-finally-pending : lookup (ident 31) (Shared.cleanups (shared Before.s10)) ≡
  just (Shared.cleanupFinalize (Shared.terminating A.key₀ (ident 31) nothing)
    (Shared.cleanupError (errorId 42)))
middle-finally-pending = refl
