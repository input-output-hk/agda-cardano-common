{-# OPTIONS --guardedness #-}

-- Exact source/view observations and operational pool/scope certificates for
-- shared executions. Pool projections do not erase CM writes into raw stutters.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.PeerSupervision as PeerFacts
import ConnectionManagement.Properties.JobPoolClose as GovernorClose
import ConnectionManagement.Properties.JobPoolCloseKernel as MonitorClose
import ConnectionManagement.Properties.AsyncScope as ScopeFacts
import ConnectionManagement.Rules.AsyncScope as Scope
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError
  module P = PeerFacts isIOManagerError
  module GClose = GovernorClose PS.GP.Body
  module BClose = MonitorClose (Maybe ErrorId) false

shared-source : ∀ s → PS.cm (K.peers s) ≡ K.source s
shared-source s = refl
server-step : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t →
  Σ E.State (λ e → E.step a (K.server s) ≡ just e × K.server t ≡ e × K.context t ≡ K.context s)
server-step a s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s) in advanced
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → e , refl , refl , refl }
peer-step : ∀ a s {t} → K.step (K.peerStep a) s ≡ just t →
  Σ PS.State (λ p → PS.step a (K.peers s) ≡ just p × K.peers t ≡ p × K.source t ≡ PS.cm p)
peer-step a s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → p , refl , refl , refl }

-- Server and common CM actions leave the peer pool/scope view unchanged.
view : K.State → P.View
view s = P.view (K.peers s)
step-projects : ∀ a s {t} → K.step a s ≡ just t → P.Paths (view s) (view t)
step-projects (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → P.idle (view s) }
step-projects (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → P.step-projects a (K.peers s) advanced }
step-projects (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → P.idle (view s) }
exec-projects : ∀ {s as t} → K.Executes s as t → P.Paths (view s) (view t)
exec-projects K.done = P.idle _
exec-projects (K.next {s = s} {a = a} eq rest) = P.compose (step-projects a s eq) (exec-projects rest)

-- Closure certificates refer only to real captured Async handles. They do not
-- certify raw admission workers, handlers, eventual closure or Server return.
from-initial : ∀ {c g s as t} → K.initial c g ≡ just s → K.Executes s as t →
  PS.GP.Pool.phase (C.governorPool (K.context t)) ≡ PS.GP.Pool.closedPool →
  PS.Pool.phase (C.monitorPool (K.context t)) ≡ PS.Pool.closedPool →
  Scope.cursor (C.scopes (K.context t)) ≡ Scope.finishedScope →
  (∀ j → j ∈ PS.GP.Pool.snapshot (C.governorPool (K.context t)) → GClose.Terminal (C.governorPool (K.context t)) j) ×
  (∀ tid → tid ∈ PS.Pool.snapshot (C.monitorPool (K.context t)) → BClose.Terminal (C.monitorPool (K.context t)) tid) ×
  ScopeFacts.AllJoined (C.scopes (K.context t))
from-initial {c} {g} initialized path govClosed bgClosed scopesClosed with E.initial c
... | nothing = case initialized of λ ()
... | just e with just-injective initialized
...   | refl with exec-projects path
...     | P.paths (ga , gp) (ba , bp) (sa , sp) =
  GClose.from-initial gp govClosed , BClose.from-initial bp bgClosed , ScopeFacts.from-initial sp scopesClosed

-- Callback return itself establishes the closure gates, rather than requiring
-- a caller to assert them independently after an initialized shared execution.
callback-gate : ∀ s {t} → K.step (K.serverStep (E.run (S.scope S.returnAction))) s ≡ just t →
  K.peerClosed s ≡ true
callback-gate s eq with K.peerClosed s
... | false = case eq of λ ()
... | true = refl
scope-closed : ∀ scopes → Scope.closed scopes ≡ true → Scope.cursor scopes ≡ Scope.finishedScope
scope-closed scopes eq with Scope.cursor scopes
... | Scope.finishedScope = refl
... | Scope.openScope = case eq of λ ()
... | Scope.closing actor = case eq of λ ()
... | Scope.readyToFinish = case eq of λ ()
closure-observation : ∀ s → K.peerClosed s ≡ true →
  PS.GP.Pool.phase (C.governorPool (K.context s)) ≡ PS.GP.Pool.closedPool ×
  PS.Pool.phase (C.monitorPool (K.context s)) ≡ PS.Pool.closedPool ×
  Scope.cursor (C.scopes (K.context s)) ≡ Scope.finishedScope
closure-observation s eq with PS.GP.Pool.phase (C.governorPool (K.context s)) |
  PS.Pool.phase (C.monitorPool (K.context s)) | Scope.closed (C.scopes (K.context s)) in scoped
... | PS.GP.Pool.closedPool | PS.Pool.closedPool | true = refl , refl , scope-closed (C.scopes (K.context s)) scoped
... | PS.GP.Pool.closedPool | PS.Pool.closedPool | false = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.openPool | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.closing | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.cancelPending tid | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.joinPending tid | _ = case eq of λ ()
... | PS.GP.Pool.openPool | _ | _ = case eq of λ ()
... | PS.GP.Pool.closing | _ | _ = case eq of λ ()
... | PS.GP.Pool.cancelPending j | _ | _ = case eq of λ ()
... | PS.GP.Pool.joinPending j | _ | _ = case eq of λ ()
Certificates : K.State → Set
Certificates s =
  (∀ j → j ∈ PS.GP.Pool.snapshot (C.governorPool (K.context s)) → GClose.Terminal (C.governorPool (K.context s)) j) ×
  (∀ tid → tid ∈ PS.Pool.snapshot (C.monitorPool (K.context s)) → BClose.Terminal (C.monitorPool (K.context s)) tid) ×
  ScopeFacts.AllJoined (C.scopes (K.context s))
callback-from-initial : ∀ {c g s as before after} → K.initial c g ≡ just s → K.Executes s as before →
  K.step (K.serverStep (E.run (S.scope S.returnAction))) before ≡ just after → Certificates before
callback-from-initial {before = before} initialized path returned with closure-observation before (callback-gate before returned)
... | gov , bg , scopes = from-initial initialized path gov bg scopes

-- Cheap trace reuse keeps existing operational proofs opaque. Permission is
-- checked for the actual pre-state; it is never inferred from a lower success.
lift-server-step : ∀ a e {next} k → K.serverAllowed a (K.combined e k) ≡ true →
  E.step a e ≡ just next →
  K.step (K.serverStep a) (K.combined e k) ≡ just (K.combined next k)
lift-server-step a e k allowed advanced rewrite allowed | advanced = refl
append : ∀ {s as t bs u} → K.Executes s as t → K.Executes t bs u → K.Executes s (as ++ bs) u
append K.done rest = rest
append (K.next eq path) rest = K.next eq (append path rest)

-- The protocol extension keeps the same peer component certificates, even
-- though successful caller starts are more precise than a raw base execution.
open import ConnectionManagement.Domain using (HandleId; WorkerId; JobId; RunId)
open import Data.Nat using (ℕ)
module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open import Data.List using ([]; _∷_)
  open import Relation.Nullary using (yes; no)
  open import Class.DecEq using (_≟_)
  open import Relation.Binary.PropositionalEquality using (sym)
  open import ConnectionManagement.Store using (lookup)
  open import ConnectionManagement.IGTypes using (number)
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.Properties.MuxProtocolJobs as PhysicalFacts
  open import ConnectionManagement.Properties.Entries using (lookup-put)
  private
    module T = K.Protocols canInitiate
    module N = Publication isBearerClosed
    module Jobs = N.P
    module Pool = Jobs.Pool

  protocol-view : T.Runtime → P.View
  protocol-view s = view (T.base s)
  cache-view : ∀ rid r result f b → view (T.cacheResult rid r result f b) ≡ view b
  cache-view rid r result f b with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = refl
  ... | just (current , _) with current ≟ rid
  ...   | no _ = refl
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = refl
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = refl
  ...         | just rs = refl
  cache-view rid r result f b | just (current , _) | yes _ | just peer | no _ | _ = refl
  cache-view rid r result f b | just (current , _) | yes _ | just peer | yes _ | no _ = refl
  enact-projects : ∀ plan s {t} → T.enact plan s ≡ just t → P.Paths (protocol-view s) (protocol-view t)
  enact-projects (T.inherit a f) s eq with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → step-projects a (T.base s) advanced }
  enact-projects (T.caller a f) s eq with PS.step a (K.peers (T.base s)) in advanced
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → P.step-projects a (K.peers (T.base s)) advanced }
  enact-projects (T.local f) s eq = case just-injective eq of λ { refl → P.idle (protocol-view s) }
  enact-projects (T.reading r) s eq = case just-injective eq of λ { refl → P.idle (protocol-view s) }
  enact-projects (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → P.idle (protocol-view s) }
  enact-projects (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → P.idle (protocol-view s) }
  enact-projects (T.birth w capturedFrame pool j rid r f) s eq = case just-injective eq of λ { refl → P.idle (protocol-view s) }
  enact-projects (T.complete a rid r result) s eq with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → P.right-view
    (sym (cache-view rid r result (T.front s) b)) (step-projects a (T.base s) advanced) }
  advance-projects : ∀ a s {t} → T.advance a s ≡ just t → P.Paths (protocol-view s) (protocol-view t)
  advance-projects a s eq with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just plan = enact-projects plan s eq
  run-projects : ∀ {s as t} → T.Runs s as t → P.Paths (protocol-view s) (protocol-view t)
  run-projects T.stop = P.idle _
  run-projects (T.more {s = s} {a = a} eq rest) = P.compose (advance-projects a s eq) (run-projects rest)
  lift-dispatch : ∀ a b {next} f → T.inheritAllowed a (T.runtime b f) ≡ true → K.step a b ≡ just next →
    T.advance (T.dispatch a) (T.runtime b f) ≡ just (T.runtime next (T.noteLegacy a f))
  lift-dispatch a b f allowed advanced rewrite allowed | advanced = refl
  dispatch-observation : ∀ a s {t} → T.advance (T.dispatch a) s ≡ just t →
    Σ K.State (λ b → K.step a (T.base s) ≡ just b × T.base t ≡ b)
  dispatch-observation a s eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true with K.step a (T.base s)
  ...   | nothing = case eq of λ ()
  ...   | just b = case just-injective eq of λ { refl → b , refl , refl }
  initial-components : ∀ {c g s as t} → T.initialize c g ≡ just s → T.Runs s as t →
    PS.GP.Pool.phase (C.governorPool (K.context (T.base t))) ≡ PS.GP.Pool.closedPool →
    PS.Pool.phase (C.monitorPool (K.context (T.base t))) ≡ PS.Pool.closedPool →
    Scope.cursor (C.scopes (K.context (T.base t))) ≡ Scope.finishedScope → Certificates (T.base t)
  initial-components {c} {g} initialized path govClosed bgClosed scopesClosed with E.initial c
  ... | nothing = case initialized of λ ()
  ... | just e with just-injective initialized
  ...   | refl with run-projects path
  ...     | P.paths (ga , gp) (ba , bp) (sa , sp) =
    GClose.from-initial gp govClosed , BClose.from-initial bp bgClosed , ScopeFacts.from-initial sp scopesClosed
  callback-from-protocols : ∀ {c g s as before after} → T.initialize c g ≡ just s → T.Runs s as before →
    T.advance (T.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) before ≡ just after → Certificates (T.base before)
  callback-from-protocols {before = before} initialized path returned with
    dispatch-observation (K.serverStep (E.run (S.scope S.returnAction))) before returned
  ... | next , advanced , same with closure-observation (T.base before) (callback-gate (T.base before) advanced)
  ...   | gov , bg , scopes = initial-components initialized path gov bg scopes

  -- A selected initiator start forks a real job in the existing physical pool.
  -- Its source is unchanged, its captured generation is not inferred from a
  -- mutable peer cell, and no body result is manufactured by physical birth.
  record Birth (w : WorkerId) (j : JobId) (s t : T.Runtime) : Set where
    constructor birthEvidence
    field generation : RunId
          captured : T.Call
          nextPool : Pool.State
          source-same : T.sourceOf t ≡ T.sourceOf s
          actual-fork : Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s))) ≡ just nextPool
          actual-pool : Jobs.poolAt w (T.physical (T.base t)) ≡ nextPool
          actual-job : lookup j (Jobs.jobs (T.physical (T.base t))) ≡ just
            (Types.protocolJob w (T.mux captured) Mux.initiatorJob (number (T.descriptor captured)) generation Types.executing)
  fork-observation : ∀ w j s {t} → T.advance (T.forkStart w j) s ≡ just t → Birth w j s t
  fork-observation w j s eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    lookup w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
  ... | T.forkReadyC rid | true | just capturedFrame with lookup rid (T.calls (T.front s)) |
    Jobs.fresh j rid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s))) in forked
  ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
    birthEvidence rid r pool refl forked
      (PhysicalFacts.pool-same w capturedFrame pool (T.physical (T.base s)))
      (lookup-put j (Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing)
        (Jobs.jobs (T.physical (T.base s)))) }
  ...     | no _ | _ | _ | _ = case eq of λ ()
  ...     | yes _ | just _ | _ | _ = case eq of λ ()
  ...     | yes _ | nothing | just _ | _ = case eq of λ ()
  ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
  fork-observation w j s eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
  fork-observation w j s eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
  fork-observation w j s eq | T.idleC | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.selectedC rid | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.tracingC rid | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.failedC rid result | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.registeringC rid old | _ | _ = case eq of λ ()
  fork-observation w j s eq | T.forkReadyC rid | false | _ = case eq of λ ()
  fork-observation w j s eq | T.forkReadyC rid | true | nothing = case eq of λ ()
  append-protocols : ∀ {s as t bs u} → T.Runs s as t → T.Runs t bs u → T.Runs s (as ++ bs) u
  append-protocols T.stop rest = rest
  append-protocols (T.more eq path) rest = T.more eq (append-protocols path rest)

  -- Consuming a Shutdown read changes only the peer/continuation view. The
  -- actual mux, protocol cells, queues, Async pools and authoritative CM source
  -- remain available for their independent real cleanup/publication steps.
  reading-source : ∀ r s {t} → T.enact (T.reading r) s ≡ just t → T.sourceOf t ≡ T.sourceOf s
  reading-source r s eq = case just-injective eq of λ { refl → refl }
  reading-physical : ∀ r s {t} → T.enact (T.reading r) s ≡ just t →
    T.physical (T.base t) ≡ T.physical (T.base s) × T.front t ≡ T.front s
  reading-physical r s eq = case just-injective eq of λ { refl → refl , refl }

  -- Capturing a start-tracer failure does not create a child or fill a result
  -- cell. Actual close/cancellation/publication keeps its existing lower steps.
  start-fault-source : ∀ w rid result fs s → T.sourceOf (T.startFaultState w rid result fs s) ≡ T.sourceOf s
  start-fault-source w rid result fs s = refl
  start-fault-physical : ∀ w rid result fs s →
    T.physical (T.base (T.startFaultState w rid result fs s)) ≡ T.physical (T.base s) ×
    T.calls (T.front (T.startFaultState w rid result fs s)) ≡ T.calls (T.front s)
  start-fault-physical w rid result fs s = refl , refl
