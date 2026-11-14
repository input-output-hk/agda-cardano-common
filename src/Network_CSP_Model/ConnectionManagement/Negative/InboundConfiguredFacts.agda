{-# OPTIONS --guardedness #-}

-- Endpoint facts for the finite full configured inbound run.
module ConnectionManagement.Negative.InboundConfiguredFacts where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Negative.InboundConfiguredWitness as Run
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxJobTypes as Jobs
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
import Data.Maybe as Maybe
open import ConnectionManagement.IGTypes using (clean)
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
mux-normal-exit : G.phase (G.frameAt A.child₀ (V.group (V.base endpoint))) ≡ G.scopeDone G.normalExit
mux-normal-exit = refl
pool-closed : Pool.phase (G.poolAt A.child₀ (V.group (V.base endpoint))) ≡ Pool.closedPool
pool-closed = refl
handler-result : W.resultOf A.child₀ (handlerState endpoint) ≡ just (W.asyncException (errorId 42))
handler-result = refl
socket-closed : lookup (ident 0) (Shared.sockets (shared endpoint)) ≡ just Shared.closed
socket-closed = refl
entry-terminated : lookup (ident 0) (Shared.entries (Shared.cm (shared endpoint))) ≡ just (Shared.terminated nothing)
entry-terminated = refl
connection-removed : Shared.mapCell (Shared.cm (shared endpoint)) ≡ Shared.full []
connection-removed = refl
ig-unregistered : IG.connections (IG.publishedState (governor endpoint)) ≡ []
ig-unregistered = refl
inbound-call-returned : Machine.inboundRelease (O.core (source endpoint)) ≡ nothing
inbound-call-returned = refl
cleanup-finished : lookup A.child₀ (Shared.cleanups (shared endpoint)) ≡
  just (Shared.cleanupDone (Shared.cleanupError (errorId 42)))
cleanup-finished = refl
handler-result-ready : W.resultReady A.child₀ (handlerState endpoint) ≡ true
handler-result-ready = refl
captured-identities-retained : B.validBindings (B.bindings Run.endpoint) Run.endpoint ≡ true
captured-identities-retained = refl
-- Server contracts own private brackets; no client shared registry is acquired.
shared-resources-released : C1.syncEntry (B.batch1 Run.endpoint) ∷ C1.fetchEntry (B.batch1 Run.endpoint) ∷
  C1.candidate (B.batch1 Run.endpoint) ∷ C2.dq (B.batch2 Run.endpoint) ∷ C3.present (B.batch3 Run.endpoint) ∷ C3.charged (B.batch3 Run.endpoint) ∷ [] ≡
  false ∷ false ∷ false ∷ false ∷ false ∷ false ∷ []
shared-resources-released = refl
-- Async availability is stronger than the captured local clean result above.
protocol-available : JobId → Bool
protocol-available j with lookup j (Pool.handles (P.poolAt A.child₀ (V.physical (V.base endpoint))))
... | just (Pool.resultAvailable _) = true
... | _ = false
all-six-async-results : protocol-available (ident 10) ∷ protocol-available (ident 11) ∷
  protocol-available (ident 12) ∷ protocol-available (ident 13) ∷
  protocol-available (ident 14) ∷ protocol-available (ident 15) ∷ [] ≡
  true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
all-six-async-results = refl
