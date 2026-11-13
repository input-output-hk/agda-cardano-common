{-# OPTIONS --guardedness #-}

-- Endpoint identities, actual branch controls, and retained allocation counts.
module ConnectionManagement.Negative.ConcurrentLifecycleFacts where

open import ConnectionManagement.Negative.ConcurrentLifecycleSupport
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.IGTypes as Types
import Data.Maybe as Maybe
import ConnectionManagement.Scenarios.Admission as A

import ConnectionManagement.Rules.MuxJobTypes as JobTypes

import ConnectionManagement.Negative.ConcurrentLifecycles as Run
import ConnectionManagement.Negative.ConcurrentLifecycle16 as Held
import ConnectionManagement.Negative.ConcurrentLifecycle17 as First
import ConnectionManagement.Negative.ConcurrentLifecycle18 as Last
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≢_)

-- A nondependent pair makes endpoint component types explicit to inference.
pair : ∀ {A B : Set} → A → B → A × B
pair x y = x , y

first-capture : lookup L.child (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 0) (ident 10) (ident 0) A.key₀)
first-capture = refl

second-capture : lookup (ident 21) (Shared.handlers (shared Run.final)) ≡ just (Shared.handlerStart (ident 1) (ident 20) (ident 1) A.key₁)
second-capture = refl

entries-terminated : pair (lookup (ident 0) (Shared.entries (Shared.cm (shared Run.final)))) (lookup (ident 1) (Shared.entries (Shared.cm (shared Run.final)))) ≡ pair (just (Shared.terminated nothing)) (just (Shared.terminated nothing))
entries-terminated = refl

sockets-closed : pair (lookup (ident 10) (Shared.sockets (shared Run.final))) (lookup (ident 20) (Shared.sockets (shared Run.final))) ≡ pair (just Shared.closed) (just Shared.closed)
sockets-closed = refl

map-empty : Shared.mapCell (Shared.cm (shared Run.final)) ≡ Shared.full []
map-empty = refl

first-result : W.resultOf L.child (handlerState Run.final) ≡ just (W.asyncException (errorId 42))
first-result = refl

first-cleanup : lookup L.child (Shared.cleanups (shared Run.final)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
first-cleanup = refl

first-normal-mux : G.phase (G.frameAt L.child (V.group (V.base Run.final))) ≡ G.scopeDone G.normalExit
first-normal-mux = refl

first-closed-pool : Pool.phase (G.poolAt L.child (V.group (V.base Run.final))) ≡ Pool.closedPool
first-closed-pool = refl

second-result : W.resultOf (ident 21) (handlerState Run.final) ≡ just (W.asyncException (errorId 42))
second-result = refl

second-cleanup : lookup (ident 21) (Shared.cleanups (shared Run.final)) ≡ just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
second-cleanup = refl

second-normal-mux : G.phase (G.frameAt (ident 21) (V.group (V.base Run.final))) ≡ G.scopeDone G.normalExit
second-normal-mux = refl

second-closed-pool : Pool.phase (G.poolAt (ident 21) (V.group (V.base Run.final))) ≡ Pool.closedPool
second-closed-pool = refl

first-cold : Maybe.map Peer.status (lookup (ident 0) (J.peers (Sub.world (PS.machine (K.peers (V.base Run.final)))))) ≡ just Peer.peerCold
first-cold = refl

first-protocol-clean : Maybe.map JobTypes.phase (lookup (ident 10) (P.jobs (V.physical (V.base Run.final)))) ≡ just (JobTypes.resultCaptured Types.clean)
first-protocol-clean = refl

first-close-job : Maybe.map (λ f → J.pc (Sub.execution f)) (lookup (ident 2) (Sub.jobs (PS.machine (K.peers (V.base Run.final))))) ≡ just (J.complete Governor.succeeded)
first-close-job = refl

first-monitor-result : lookup (ident 50) (PS.Pool.handles (PS.monitorPool (K.peers (V.base Run.final)))) ≡ just (PS.Pool.resultAvailable PS.Pool.normalExit)
first-monitor-result = refl

first-close-result : lookup (ident 2) (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base Run.final))))) ≡ just (GP.Pool.resultAvailable GP.Pool.normalExit)
first-close-result = refl

second-cold : Maybe.map Peer.status (lookup (ident 1) (J.peers (Sub.world (PS.machine (K.peers (V.base Run.final)))))) ≡ just Peer.peerCold
second-cold = refl

second-protocol-clean : Maybe.map JobTypes.phase (lookup (ident 20) (P.jobs (V.physical (V.base Run.final)))) ≡ just (JobTypes.resultCaptured Types.clean)
second-protocol-clean = refl

second-close-job : Maybe.map (λ f → J.pc (Sub.execution f)) (lookup (ident 3) (Sub.jobs (PS.machine (K.peers (V.base Run.final))))) ≡ just (J.complete Governor.succeeded)
second-close-job = refl

second-monitor-result : lookup (ident 51) (PS.Pool.handles (PS.monitorPool (K.peers (V.base Run.final)))) ≡ just (PS.Pool.resultAvailable PS.Pool.normalExit)
second-monitor-result = refl

second-close-result : lookup (ident 3) (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base Run.final))))) ≡ just (GP.Pool.resultAvailable GP.Pool.normalExit)
second-close-result = refl

first-cleanup-retains-second : lookup (ident 1) (Shared.entries (Shared.cm (shared First.s12))) ≡ just (Shared.terminating A.key₁ (ident 21) nothing)
first-cleanup-retains-second = refl

second-still-waits : W.resultOf (ident 21) (handlerState First.s12) ≡ nothing
second-still-waits = refl

no-early-first-result : V.advance (exit (W.publishAsyncResult L.child)) Held.s16 ≡ nothing
no-early-first-result = refl

no-early-second-result : V.advance (exit (W.publishAsyncResult (ident 21))) First.s8 ≡ nothing
no-early-second-result = refl

no-early-second-cold : V.advance (V.pollResults (ident 1) (ident 51)) First.s8 ≡ nothing
no-early-second-cold = refl

no-first-job-before-monitor : V.advance (ps (Sub.jobStep (ident 2) J.observeCold)) First.s15 ≡ nothing
no-first-job-before-monitor = refl

no-raw-receipt : V.advance (outRelease (OutRelease.cancellationDelivered L.child)) First.s8 ≡ nothing
no-raw-receipt = refl

no-double-receipt : V.advance (exit (W.deliverReleaseTimeWait (ident 26) (errorId 42))) Run.final ≡ nothing
no-double-receipt = refl

entry-and-promise-supplies : pair (Shared.nextEntry (Shared.cm (shared Run.final))) (Shared.nextPromise (shared Run.final)) ≡ pair 2 2
entry-and-promise-supplies = refl

socket-budget : length (Shared.sockets (shared Run.final)) ≡ 2
socket-budget = refl

promise-budget : length (Shared.promises (shared Run.final)) ≡ 2
promise-budget = refl

handler-budget : length (Shared.handlers (shared Run.final)) ≡ 2
handler-budget = refl

entry-budget : length (Shared.entries (Shared.cm (shared Run.final))) ≡ 2
entry-budget = refl

handle-budget : length (IG.handles (IG.execution (governor Run.final))) ≡ 2
handle-budget = refl

mux-budget : length (IG.muxes (IG.execution (governor Run.final))) ≡ 2
mux-budget = refl

peer-budget : length (J.peers (Sub.world (PS.machine (K.peers (V.base Run.final))))) ≡ 2
peer-budget = refl

governor-job-budget : length (Sub.jobs (PS.machine (K.peers (V.base Run.final)))) ≡ 4
governor-job-budget = refl

protocol-job-budget : length (P.jobs (V.physical (V.base Run.final))) ≡ 2
protocol-job-budget = refl

monitor-budget : length (PS.monitors (K.peers (V.base Run.final))) ≡ 2
monitor-budget = refl

-- Distinct captured entry identities cannot unify.
entry₀ entry₁ : EntryId
entry₀ = ident 0
entry₁ = ident 1
entries-distinct : entry₀ ≢ entry₁
entries-distinct ()

-- Retained physical pools count both infrastructure children and the protocol.
physical-pool-allocation-budget : pair
  (length (Pool.handles (G.poolAt L.child (V.group (V.base Run.final)))))
  (length (Pool.handles (G.poolAt (ident 21) (V.group (V.base Run.final))))) ≡ pair 3 3
physical-pool-allocation-budget = refl

-- Each close job's own captured caller returned, retiring both call frames.
first-release-returned : lookup (ident 16) (O.released (source Run.final)) ≡
  just (OutRelease.success (just (Shared.terminating A.key₀ L.child nothing)))
first-release-returned = refl
second-release-returned : lookup (ident 26) (O.released (source Run.final)) ≡
  just (OutRelease.success (just (Shared.terminating A.key₁ (ident 21) nothing)))
second-release-returned = refl
release-frames-retired : O.releasing (source Run.final) ≡ []
release-frames-retired = refl
