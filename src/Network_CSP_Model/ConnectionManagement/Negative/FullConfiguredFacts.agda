{-# OPTIONS --guardedness #-}

-- Concrete endpoint facts and controls over the initialized configured run.
module ConnectionManagement.Negative.FullConfiguredFacts where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import Data.Product using (_,_ )
import ConnectionManagement.Negative.FullConfiguredWitness as Run
import ConnectionManagement.Negative.FullConfiguredHot as Hot
import ConnectionManagement.Negative.FullConfiguredHot2 as CS
import ConnectionManagement.Negative.FullConfiguredEstablished as Established
import ConnectionManagement.Negative.FullConfiguredChain as Chain
import ConnectionManagement.Negative.FullConfiguredRelease as Release
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
import ConnectionManagement.Rules.MuxJobTypes as Jobs
import ConnectionManagement.Rules.MuxRuntime as MR
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
open import ConnectionManagement.IGTypes using (clean)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.CSP.GovernorLifecycle as L
import Data.Maybe as Maybe
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
endpoint : V.Runtime
endpoint = B.runtime Run.endpoint

-- Nonempty established and hot groups actually ran, with full captured identity.
all-six-bound : length (B.bindings Run.endpoint) ≡ 6
all-six-bound = refl
contracts-clean : B.normalDone 2 Run.endpoint ∷ B.normalDone 3 Run.endpoint ∷
  B.normalDone 4 Run.endpoint ∷ B.normalDone 8 Run.endpoint ∷
  B.normalDone 18 Run.endpoint ∷ B.normalDone 19 Run.endpoint ∷ [] ≡
  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
contracts-clean = refl
all-six-physical : Maybe.map Jobs.phase (lookup (ident 10) (P.jobs (V.physical (V.base endpoint)))) ∷
  Maybe.map Jobs.phase (lookup (ident 11) (P.jobs (V.physical (V.base endpoint)))) ∷
  Maybe.map Jobs.phase (lookup (ident 12) (P.jobs (V.physical (V.base endpoint)))) ∷
  Maybe.map Jobs.phase (lookup (ident 13) (P.jobs (V.physical (V.base endpoint)))) ∷
  Maybe.map Jobs.phase (lookup (ident 14) (P.jobs (V.physical (V.base endpoint)))) ∷
  Maybe.map Jobs.phase (lookup (ident 15) (P.jobs (V.physical (V.base endpoint)))) ∷ [] ≡
  just (Jobs.resultCaptured clean) ∷ just (Jobs.resultCaptured clean) ∷
  just (Jobs.resultCaptured clean) ∷ just (Jobs.resultCaptured clean) ∷
  just (Jobs.resultCaptured clean) ∷ just (Jobs.resultCaptured clean) ∷ []
all-six-physical = refl
hot-reached : Maybe.map Peer.status (lookup (ident 0)
  (J.peers (Sub.world (PS.machine (K.peers (V.base (B.runtime Hot.s3))))))) ≡ just Peer.peerHot
hot-reached = refl
peer-cold : Maybe.map Peer.status (lookup (ident 0)
  (J.peers (Sub.world (PS.machine (K.peers (V.base endpoint)))))) ≡ just Peer.peerCold
peer-cold = refl
mux-normal-exit : G.phase (G.frameAt L.child (V.group (V.base endpoint))) ≡ G.scopeDone G.normalExit
mux-normal-exit = refl
pool-closed : Pool.phase (G.poolAt L.child (V.group (V.base endpoint))) ≡ Pool.closedPool
pool-closed = refl
handler-result : W.resultOf L.child (handlerState endpoint) ≡ just (W.asyncException (errorId 42))
handler-result = refl
socket-closed : lookup (ident 10) (Shared.sockets (shared endpoint)) ≡ just Shared.closed
socket-closed = refl
entry-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared endpoint))) ≡ just (Shared.terminated nothing)
entry-terminated = refl
connection-removed : Shared.mapCell (Shared.cm (shared endpoint)) ≡ Shared.full []
connection-removed = refl
release-frame-retired : lookup (ident 16) (O.releasing (source endpoint)) ≡ nothing
release-frame-retired = refl
shared-resources-released : C1.syncEntry (B.batch1 Run.endpoint) ∷ C1.fetchEntry (B.batch1 Run.endpoint) ∷
  C1.candidate (B.batch1 Run.endpoint) ∷ C2.dq (B.batch2 Run.endpoint) ∷ C3.present (B.batch3 Run.endpoint) ∷ C3.charged (B.batch3 Run.endpoint) ∷ [] ≡
  false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
shared-resources-released = refl
-- The second selected establishment is a registered physical job at J.begin;
-- it has not entered acquisition or created a second connection/handler.
second-peer-job-begin : Maybe.map (λ f → J.pc (Sub.execution f))
  (lookup (ident 1) (Sub.jobs (PS.machine (K.peers (V.base endpoint))))) ≡ just J.begin
second-peer-job-begin = refl
second-peer-physical-pending : lookup (ident 1)
  (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base endpoint))))) ≡ just GP.Pool.bodyRunning
second-peer-physical-pending = refl
no-premature-body-return : B.step (B.run (protocol (P.protocolReturned (ident 11)))) CS.s8 ≡ nothing
no-premature-body-return = refl
no-raw-body-bypass : B.step (B.run (protocol (P.protocolException (ident 11) (errorId 7)))) CS.s8 ≡ nothing
no-raw-body-bypass = refl
no-premature-keepalive-terminate : B.step (B.contract2 (C2.terminate C2.keepClient)) Established.s21 ≡ nothing
no-premature-keepalive-terminate = refl
no-shared-cleanup-bypass : B.step (B.contract1 C1.removeCandidate) Chain.s3 ≡ nothing
no-shared-cleanup-bypass = refl
no-release-return-before-receipt : V.advance (outRelease OutRelease.returnResult) (B.runtime Release.s10) ≡ nothing
no-release-return-before-receipt = refl
no-premature-handler-result : V.advance (exit (W.publishAsyncResult L.child)) (B.runtime Release.s10) ≡ nothing
no-premature-handler-result = refl

-- Async availability is stronger than the captured local clean result above.
protocol-available : JobId → Bool
protocol-available j with lookup j (Pool.handles (P.poolAt L.child (V.physical (V.base endpoint))))
... | just (Pool.resultAvailable _) = true
... | _ = false
all-six-async-results : protocol-available (ident 10) ∷ protocol-available (ident 11) ∷
  protocol-available (ident 12) ∷ protocol-available (ident 13) ∷
  protocol-available (ident 14) ∷ protocol-available (ident 15) ∷ [] ≡
  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
all-six-async-results = refl
governor-available : JobId → Bool
governor-available j with lookup j (GP.Pool.handles (GP.pool (PS.governor (K.peers (V.base endpoint)))))
... | just (GP.Pool.resultAvailable _) = true
... | _ = false
selected-governor-results : governor-available (ident 0) ∷ governor-available (ident 2) ∷
  governor-available (ident 3) ∷ governor-available (ident 4) ∷ [] ≡ true ∷ true ∷ true ∷ true ∷ []
selected-governor-results = refl
monitor-result-available : Maybe.map (λ { (PS.Pool.resultAvailable _) → true ; _ → false })
  (lookup (ident 50) (PS.Pool.handles (PS.monitorPool (K.peers (V.base endpoint))))) ≡ just true
monitor-result-available = refl
no-premature-clean-commit : B.step (B.run (V.commitClean (ident 11))) CS.s8 ≡ nothing
no-premature-clean-commit = refl
no-rebinding : B.step (B.capture 2 (ident 10)) CS.s8 ≡ nothing
no-rebinding = refl

-- Descriptor Any does not park the established initiator behind ingress.
keepalive-eager : Maybe.map (λ j → Jobs.direction j , Jobs.phase j)
  (lookup (ident 10) (P.jobs (V.physical (V.base (B.runtime Established.s11))))) ≡
  just (MR.initiatorJob , Jobs.executing)
keepalive-eager = refl

captured-identities-retained : B.validBindings (B.bindings Run.endpoint) Run.endpoint ≡ true
captured-identities-retained = refl
remaining-governor-registration : GP.Pool.registered
  (GP.pool (PS.governor (K.peers (V.base endpoint)))) ≡ ident 1 ∷ []
remaining-governor-registration = refl
two-known-peers-retained : length (Governor.knownPeers
  (Sub.privateState (PS.machine (K.peers (V.base endpoint))))) ≡ 2
two-known-peers-retained = refl
