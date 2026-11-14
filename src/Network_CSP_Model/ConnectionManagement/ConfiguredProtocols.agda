{-# OPTIONS --guardedness #-}

-- Selected normal outbound profile. Observed protocol operations share the
-- actual frontend, captured jobs, PSA controls and peer-resource registries.
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
module ConnectionManagement.ConfiguredProtocols
  (isBearerClosed isIOManagerError : ErrorId → Bool)
  (capability : HandleId → ℕ → Bool) where

open import Data.Bool using (true; false; _∧_; not)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import Class.DecEq.Instances using (DecEq-ℕ)
open import ConnectionManagement.Domain hiding (worker; mux; job)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
import ConnectionManagement.ProtocolContractJobs as A1
import ConnectionManagement.ProtocolContractJobs2 as A2
import ConnectionManagement.ProtocolContractJobs3 as A3
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.IGTypes as Clean
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.PeerContext as Context
private
  module K = Combined isBearerClosed isIOManagerError
  module C = Context isIOManagerError
module V = K.Protocols capability
import ConnectionManagement.MuxProtocolJobs as P

-- Each immutable binding captures a physical generation, not a protocol number
-- alias. This wrapper has one captured connection and no rebinding operation.
record State : Set where
  no-eta-equality
  constructor configured
  field runtime : V.Runtime
        owner : WorkerId
        mux : MuxId
        peerRef : PeerConnectionId
        bindings : Store ℕ (JobId × T.ProtocolJob)
        batch1 : C1.State
        batch2 : C2.State
        batch3 : C3.State
open State public
initial : V.Runtime → WorkerId → MuxId → PeerConnectionId → State
initial s w m ref = configured s w m ref [] C1.initial C2.initial C3.initial
physical : State → P.State
physical s = V.physical (V.base (runtime s))
bind : ℕ → State → JobId
bind n s with lookup n (bindings s)
... | nothing = ident 0
... | just (j , _) = j
sameCapture : T.ProtocolJob → T.ProtocolJob → Bool
sameCapture a b = does (T.owner a ≟ T.owner b) ∧ does (T.mux a ≟ T.mux b) ∧
  P.sameDirection (T.direction a) (T.direction b) ∧
  does (T.protocolNumber a ≟ T.protocolNumber b) ∧ does (T.generation a ≟ T.generation b)
backed : ℕ → JobId → State → Bool
backed n j s with lookup n (bindings s) | lookup j (P.jobs (physical s))
... | just (k , captured) | just current = does (j ≟ k) ∧ sameCapture captured current
... | _ | _ = false
attach : ℕ → JobId → State → Maybe State
attach n j s with lookup n (bindings s) | P.collector j (physical s)
... | nothing | just job with does (T.owner job ≟ owner s) ∧ does (T.mux job ≟ mux s) ∧
  does (T.protocolNumber job ≟ n) ∧ P.sameDirection (T.direction job) M.initiatorJob
...   | true = just (record s { bindings = put n (j , job) (bindings s) })
...   | false = nothing
attach n j s | _ | _ = nothing

-- Terminate observations read the actual captured PSA control, so a disconnected
-- lifecycle snapshot cannot request clean termination while the peer continues.
terminating : ℕ → State → Bool
terminating n s with lookup (peerRef s) (C.SubContext.peers (C.subsystem (K.context (V.base (runtime s)))))
... | nothing = false
... | just p with does (Peer.muxRef p ≟ mux s)
...   | false = false
...   | true with n
...   | 8 with Peer.establishedControl p
...     | Peer.terminate = true
...     | _ = false
terminating n s | just p | true | _ with Peer.hotControl p
... | Peer.terminate = true
... | _ = false
normal1 : C1.Endpoint → State → Bool
normal1 ep s with C1.at ep (batch1 s)
... | C1.finished C1.normal = true
... | _ = false
normal2 : C2.Endpoint → State → Bool
normal2 ep s with C2.at ep (batch2 s)
... | C2.finished C1.normal = true
... | _ = false
normal3 : C3.Endpoint → State → Bool
normal3 ep s with C3.at ep (batch3 s)
... | C3.finished C1.normal = true
... | _ = false
sharedReleased : State → Bool
sharedReleased s with C3.cs (batch3 s)
... | C3.outerRelease C1.normal = true
... | _ = false
normalDone : ℕ → State → Bool
normalDone 2 s = normal1 C1.chainClient s ∧ normal3 C3.chainClient s
normalDone 3 s = normal1 C1.fetchClient s
normalDone 4 s = normal2 C2.txClient s
normalDone 8 s = normal2 C2.keepClient s
normalDone 18 s = normal3 C3.notifyClient s
normalDone 19 s = normal3 C3.fetchClient s
normalDone _ s = false

-- Physical pool cancellation does not necessarily change the typed job phase.
-- Normal-only execution therefore checks both representations of body exit.
module Pool = P.Pool
capturedNormal : JobId → T.ProtocolJob → V.Runtime → Bool
capturedNormal j job next with lookup j (P.jobs (V.physical (V.base next)))
... | just current with T.phase current
...   | T.resultCaptured Clean.clean = sameCapture job current
...   | _ = false
capturedNormal j job next | nothing = false
normalPhysical : JobId → T.ProtocolJob → V.Runtime → State → Bool
normalPhysical j job next s = backed (T.protocolNumber job) j s ∧
  normalDone (T.protocolNumber job) s ∧ capturedNormal j job next
poolGate : JobId → T.ProtocolJob → V.Runtime → State → Bool
poolGate j job next s with lookup j (Pool.handles
  (P.poolAt (T.owner job) (V.physical (V.base next))))
... | just Pool.bodyRunning = true
... | just (Pool.bodyReturned value) = normalPhysical j job next s ∧ P.resultMatches job Clean.clean value
... | just (Pool.deregisterPending Pool.normalExit) = normalPhysical j job next s
... | just (Pool.deregistered Pool.normalExit) = normalPhysical j job next s
... | just (Pool.resultAvailable Pool.normalExit) = normalPhysical j job next s
... | _ = false

-- Check every actual executing→return boundary, including inherited aliases.
-- Exceptions/cancellation cannot be reclassified as normal completion here.
bodyGate : JobId → T.ProtocolJob → V.Runtime → State → Bool
bodyGate j job next s with T.phase job | lookup j (P.jobs (V.physical (V.base next)))
... | T.executing | just after with T.phase after
...   | T.waitingEgress = backed (T.protocolNumber job) j s ∧ normalDone (T.protocolNumber job) s
...   | T.resultCaptured _ = false
...   | _ = true
bodyGate j job next s | T.waitingEgress | just after with T.phase after
... | T.resultCaptured Clean.clean = backed (T.protocolNumber job) j s ∧ normalDone (T.protocolNumber job) s
... | T.resultCaptured _ = false
... | _ = true
bodyGate j job next s | _ | _ = true
allBodies : Store JobId T.ProtocolJob → V.Runtime → State → Bool
allBodies [] next s = true
allBodies ((j , job) ∷ js) next s = bodyGate j job next s ∧ poolGate j job next s ∧ allBodies js next s
frontend : V.Event → State → Maybe State
frontend a s with V.advance a (runtime s)
... | nothing = nothing
... | just next with allBodies (P.jobs (physical s)) next s
...   | false = nothing
...   | true = just (record s { runtime = next })

-- Restrict adapter lookup to immutable captured bindings. Missing bindings
-- cannot alias a real protocol job whose physical ID happens to be zero.
boundJobs : Store JobId T.ProtocolJob → State → Store JobId T.ProtocolJob
boundJobs [] s = []
boundJobs ((j , job) ∷ rest) s with backed (T.protocolNumber job) j s
... | true = (j , job) ∷ boundJobs rest s
... | false = boundJobs rest s
boundPhysical : State → P.State
boundPhysical s = record (physical s) { jobs = boundJobs (P.jobs (physical s)) s }

-- Exact shared-state guards added to the existing reviewed contract kernels.
couple1 : C1.Action → State → Bool
couple1 C1.keepAliveReady s = C2.dq (batch2 s)
couple1 C1.keepAliveDying s = C2.dying (batch2 s)
couple1 C1.registerFetch s = C2.dq (batch2 s) ∧ not (C2.dying (batch2 s))
couple1 (C1.terminate ep _) s = terminating (A1.number ep) s
couple1 C1.removeCandidate s = sharedReleased s
couple1 C1.signalSyncDone s = sharedReleased s
couple1 _ s = true
couple2 : C2.Action → State → Bool
couple2 (C2.terminate ep) s = terminating (A2.number ep) s
couple2 (C2.keepSnapshot present) s with present
... | true = C1.fetchEntry (batch1 s)
... | false = not (C1.fetchEntry (batch1 s))
couple2 C2.fetchDone s = not (C1.fetchEntry (batch1 s)) ∧ C1.syncDone (batch1 s) ∧ normal1 C1.fetchClient s
couple2 _ s = true
couple3 : C3.Action → State → Bool
couple3 (C3.terminate ep) s = terminating (A3.number ep) s
couple3 (C3.start C3.chainClient) s with C1.cs (batch1 s)
... | C1.active = true
... | _ = false
couple3 C3.chainExited s with C1.cs (batch1 s)
... | C1.cleaning C1.normal = true
... | _ = false
couple3 C3.outerClosed s = C1.syncDone (batch1 s)
couple3 _ s = true

validBindings : Store ℕ (JobId × T.ProtocolJob) → State → Bool
validBindings [] s = true
validBindings ((n , (j , _)) ∷ rest) s = backed n j s ∧ validBindings rest s
observe1 : C1.Action → State → Maybe State
observe1 a s with validBindings (bindings s) s ∧ couple1 a s ∧ A1.required (λ ep → bind (A1.number ep) s) a (boundPhysical s)
... | false = nothing
... | true with C1.step a (batch1 s)
...   | nothing = nothing
...   | just next = just (record s { batch1 = next })
observe2 : C2.Action → State → Maybe State
observe2 a s with validBindings (bindings s) s ∧ couple2 a s ∧ A2.required (λ ep → bind (A2.number ep) s) a (boundPhysical s)
... | false = nothing
... | true with C2.step a (batch2 s)
...   | nothing = nothing
...   | just next = just (record s { batch2 = next })
observe3 : C3.Action → State → Maybe State
observe3 a s with validBindings (bindings s) s ∧ couple3 a s ∧ A3.required (λ ep → bind (A3.number ep) s) a (boundPhysical s)
... | false = nothing
... | true with C3.step a (batch3 s)
...   | nothing = nothing
...   | just next = just (record s { batch3 = next })

data Action : Set where
  run : V.Event → Action
  capture : ℕ → JobId → Action
  contract1 : C1.Action → Action
  contract2 : C2.Action → Action
  contract3 : C3.Action → Action
step : Action → State → Maybe State
step (run a) = frontend a
step (capture n j) = attach n j
step (contract1 a) = observe1 a
step (contract2 a) = observe2 a
step (contract3 a) = observe3 a

data Runs : State → List Action → State → Set where
  done : ∀ {s} → Runs s [] s
  more : ∀ {s t u a as} → step a s ≡ just t → Runs t as u → Runs s (a ∷ as) u

-- Compose small checked slices without normalizing a whole initialized run.
append : ∀ {s as t bs u} → Runs s as t → Runs t bs u → Runs s (as ++ bs) u
append done tail = tail
append (more eq rest) tail = more eq (append rest tail)

-- Contract/capture inputs erase; frontend inputs retain their exact real edges.
erase : List Action → List V.Event
erase [] = []
erase (run a ∷ as) = a ∷ erase as
erase (_ ∷ as) = erase as
frontend-edge : ∀ a s {t} → frontend a s ≡ just t → V.advance a (runtime s) ≡ just (runtime t)
frontend-edge a s eq with V.advance a (runtime s) in advanced
... | just next with allBodies (P.jobs (physical s)) next s
...   | true with eq
...     | refl = refl
silent-edge : ∀ a s {t} → step a s ≡ just t → erase (a ∷ []) ≡ [] → runtime s ≡ runtime t
silent-edge (run _) s eq ()
silent-edge (capture n j) s eq silent with lookup n (bindings s) | P.collector j (physical s)
... | nothing | just job with does (T.owner job ≟ owner s) ∧ does (T.mux job ≟ mux s) ∧
  does (T.protocolNumber job ≟ n) ∧ P.sameDirection (T.direction job) M.initiatorJob
...   | true with eq
...     | refl = refl
silent-edge (contract1 a) s eq silent with validBindings (bindings s) s ∧ couple1 a s ∧ A1.required (λ ep → bind (A1.number ep) s) a (boundPhysical s)
... | true with C1.step a (batch1 s)
...   | just next with eq
...     | refl = refl
silent-edge (contract2 a) s eq silent with validBindings (bindings s) s ∧ couple2 a s ∧ A2.required (λ ep → bind (A2.number ep) s) a (boundPhysical s)
... | true with C2.step a (batch2 s)
...   | just next with eq
...     | refl = refl
silent-edge (contract3 a) s eq silent with validBindings (bindings s) s ∧ couple3 a s ∧ A3.required (λ ep → bind (A3.number ep) s) a (boundPhysical s)
... | true with C3.step a (batch3 s)
...   | just next with eq
...     | refl = refl
project : ∀ {s as t} → Runs s as t → V.Runs (runtime s) (erase as) (runtime t)
project done = V.stop
project (more {s = s} {a = run a} eq rest) = V.more (frontend-edge a s eq) (project rest)
project (more {s = s} {a = capture n j} eq rest) rewrite silent-edge (capture n j) s eq refl = project rest
project (more {s = s} {a = contract1 a} eq rest) rewrite silent-edge (contract1 a) s eq refl = project rest
project (more {s = s} {a = contract2 a} eq rest) rewrite silent-edge (contract2 a) s eq refl = project rest
project (more {s = s} {a = contract3 a} eq rest) rewrite silent-edge (contract3 a) s eq refl = project rest
