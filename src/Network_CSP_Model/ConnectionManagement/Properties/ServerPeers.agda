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

  -- Committed generation cells retain the whole captured call, independently
  -- of mux status, physical Async results and handler/shutdown completion.
  module CommittedCells where
    open import Data.Empty using (⊥-elim)
    open import Data.Maybe using (Maybe)
    open import Data.List.Relation.Unary.All as All using (All)
    import Data.List.Relation.Unary.AllPairs as Pairs
    open import Relation.Binary.PropositionalEquality using (_≢_; trans; subst)
    open import ConnectionManagement.Store using (Store; put)
    open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
    import ConnectionManagement.Properties.Stores as Stores
    import ConnectionManagement.Subsystem as Sub
    import ConnectionManagement.Rules.PeerJobs as J
    import ConnectionManagement.Rules.CMShutdown as Close
    import Data.Nat as Nat

    -- Absence justifies fresh cons allocation without a hidden no-duplicates
    -- premise; replacement preserves the existing standard uniqueness predicate.
    absent-keys : ∀ k (xs : Store RunId T.Call) → lookup k xs ≡ nothing →
      Stores.KeysSatisfy (λ q → k ≢ q) xs
    absent-keys k [] eq = All.[]
    absent-keys k ((q , r) ∷ xs) eq with k ≟ q
    ... | yes _ = case eq of λ ()
    ... | no apart = apart All.∷ absent-keys k xs eq

    tail-lookup : ∀ k r q head (xs : Store RunId T.Call) →
      Stores.UniqueKeys ((q , head) ∷ xs) → lookup k xs ≡ just r →
      lookup k ((q , head) ∷ xs) ≡ just r
    tail-lookup k r q head xs (apart Pairs.∷ unique) found with k ≟ q
    ... | no _ = found
    ... | yes refl with trans (sym (Stores.apart-lookup k xs apart)) found
    ...   | ()

    -- Searching a unique call table by physical thread finds its actual key.
    by-thread-lookup : ∀ j (xs : Store RunId T.Call) rid r →
      Stores.UniqueKeys xs → T.byThread j xs ≡ just (rid , r) → lookup rid xs ≡ just r
    by-thread-lookup j [] rid r unique eq = case eq of λ ()
    by-thread-lookup j ((q , head) ∷ xs) rid r (apart Pairs.∷ unique) eq with T.thread head
    ... | nothing = tail-lookup rid r q head xs (apart Pairs.∷ unique) (by-thread-lookup j xs rid r unique eq)
    ... | just actual with j ≟ actual
    ...   | no _ = tail-lookup rid r q head xs (apart Pairs.∷ unique) (by-thread-lookup j xs rid r unique eq)
    ...   | yes _ = case just-injective eq of λ { refl → Stores.lookup-head q head xs }

    -- Only fresh allocation and writes to previously empty cells may change
    -- this table. This relation also permits the fork's captured-thread update.
    data Change (xs : Store RunId T.Call) : Store RunId T.Call → Set where
      unchanged : Change xs xs
      allocated : ∀ rid r → lookup rid xs ≡ nothing → Change xs ((rid , r) ∷ xs)
      empty-write : ∀ rid old next → lookup rid xs ≡ just old → T.value old ≡ nothing →
        Change xs (put rid next xs)

    Keeps : Store RunId T.Call → Store RunId T.Call → Set
    Keeps xs ys = ∀ rid r result → lookup rid xs ≡ just r → T.value r ≡ just result → lookup rid ys ≡ just r
    change-unique : ∀ {xs ys} → Change xs ys → Stores.UniqueKeys xs → Stores.UniqueKeys ys
    change-unique unchanged unique = unique
    change-unique (allocated rid r absent) unique = absent-keys rid _ absent Pairs.∷ unique
    change-unique (empty-write rid old next found empty) unique = Stores.put-unique rid next _ unique

    empty-is-other : ∀ k old rid r result (xs : Store RunId T.Call) →
      lookup k xs ≡ just old → T.value old ≡ nothing →
      lookup rid xs ≡ just r → T.value r ≡ just result → rid ≢ k
    empty-is-other k old .k r result xs found empty seen filled refl with just-injective (trans (sym found) seen)
    ... | refl with trans (sym empty) filled
    ...   | ()
    change-keeps : ∀ {xs ys} → Change xs ys → Keeps xs ys
    change-keeps unchanged rid r result seen filled = seen
    change-keeps (allocated k next absent) rid r result seen filled with rid ≟ k
    ... | no _ = seen
    ... | yes refl with trans (sym absent) seen
    ...   | ()
    change-keeps {xs} (empty-write k old next found empty) rid r result seen filled =
      trans (Stores.lookup-put-other k rid next xs (empty-is-other k old rid r result xs found empty seen filled)) seen

    -- Source effects are irrelevant to this projection; arbitrary Plan values
    -- are not assumed enabled, so their table changes are checked separately.
    planCalls : T.Plan → T.Runtime → Store RunId T.Call
    planCalls (T.inherit a f) s = T.calls f
    planCalls (T.caller a f) s = T.calls f
    planCalls (T.local f) s = T.calls f
    planCalls (T.birth w captured pool j rid r f) s = T.calls f
    planCalls (T.complete a rid r result) s = put rid (record r { value = just result }) (T.calls (T.front s))
    planCalls _ s = T.calls (T.front s)
    enact-calls : ∀ plan s {t} → T.enact plan s ≡ just t → T.calls (T.front t) ≡ planCalls plan s
    enact-calls (T.inherit a f) s eq with K.step a (T.base s)
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → refl }
    enact-calls (T.caller a f) s eq with PS.step a (K.peers (T.base s))
    ... | nothing = case eq of λ ()
    ... | just p = case just-injective eq of λ { refl → refl }
    enact-calls (T.local f) s eq = case just-injective eq of λ { refl → refl }
    enact-calls (T.birth w captured pool j rid r f) s eq = case just-injective eq of λ { refl → refl }
    enact-calls (T.complete a rid r result) s eq with K.step a (T.base s)
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → refl }
    enact-calls (T.reading r) s eq = case just-injective eq of λ { refl → refl }
    enact-calls (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → refl }
    enact-calls (T.deliverTraceFault w rid result fs pc) s eq = case just-injective eq of λ { refl → refl }

    -- Each successful selector supplies a justified table change. Physical
    -- source permissions remain in the unchanged executable selector.
    Effect : T.Runtime → T.Plan → Set
    Effect s p = Change (T.calls (T.front s)) (planCalls p s)
    select-change : ∀ w s p → T.selectPlan w s ≡ just p → Effect s p
    select-change w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
      N.M.ownerContext w (N.G.base (T.group (T.base s)))
    ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
      Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
      Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
    ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
    ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → unchanged }
    ...     | Mux.stopping | _ = case eq of λ ()
    ...     | Mux.stopped | _ = case eq of λ ()
    ...     | Mux.failed err | _ = case eq of λ ()
    ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
    ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
    ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
    ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
    ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
    ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
    select-change w s p eq | false | _ | _ | _ = case eq of λ ()
    select-change w s p eq | true | [] | _ | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
    select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

    register-change : ∀ j s p → T.registerPlan j s ≡ just p → Effect s p
    register-change j s p eq with T.byThread j (T.calls (T.front s))
    ... | nothing = case eq of λ ()
    ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
    ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
    ...     | yes _ | yes _ = case just-injective eq of λ { refl → unchanged }
    ...     | no _ | _ = case eq of λ ()
    ...     | yes _ | no _ = case eq of λ ()
    register-change j s p eq | just (rid , r) | T.idleC = case eq of λ ()
    register-change j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
    register-change j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
    register-change j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
    register-change j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

    fork-change : ∀ w j s p → T.forkPlan w j s ≡ just p → Effect s p
    fork-change w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
      lookup w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
    ... | T.forkReadyC rid | true | just f with lookup rid (T.calls (T.front s)) in found |
      Jobs.fresh j rid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
    ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s)))
    ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
      empty-write rid r (record r { thread = just j }) found empty }
    ...     | no _ | _ | _ | _ = case eq of λ ()
    ...     | yes _ | just thread | _ | _ = case eq of λ ()
    ...     | yes _ | nothing | just result | _ = case eq of λ ()
    ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
    fork-change w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
    fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
    fork-change w j s p eq | T.idleC | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.registeringC rid target | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
    fork-change w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
    fork-change w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()

    completion-change : ∀ j result s p → Stores.UniqueKeys (T.calls (T.front s)) →
      T.completionPlan j result s ≡ just p → Effect s p
    completion-change j result s p unique eq with T.byThread j (T.calls (T.front s)) in found |
      lookup j (Jobs.jobs (T.physical (T.base s)))
    ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
      Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
    ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
      empty-write rid r (record r { value = just result }) (by-thread-lookup j (T.calls (T.front s)) rid r unique found) empty }
    ...   | just old | _ | _ | _ | _ = case eq of λ ()
    ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
    ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
    ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
    ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
    completion-change j result s p unique eq | nothing | _ = case eq of λ ()
    completion-change j result s p unique eq | just pair | nothing = case eq of λ ()

    poll-change : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Effect s p
    poll-change ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
      lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
    ... | true | just peer | nothing with Peer.status peer
    ...   | Peer.peerCold = case just-injective eq of λ { refl → unchanged }
    ...   | Peer.peerCooling = case just-injective eq of λ { refl → unchanged }
    ...   | Peer.peerWarm with T.firstPeer ref peer s
    ...     | nothing = case eq of λ ()
    ...     | just (kind , result) with T.cleanObservation result
    ...       | true = case just-injective eq of λ { refl → unchanged }
    ...       | false = case just-injective eq of λ { refl → unchanged }
    poll-change ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
    ...     | nothing = case eq of λ ()
    ...     | just (kind , result) with T.cleanObservation result
    ...       | true = case just-injective eq of λ { refl → unchanged }
    ...       | false = case just-injective eq of λ { refl → unchanged }
    poll-change ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → unchanged }
    poll-change ref w s p eq | false | _ | _ = case eq of λ ()
    poll-change ref w s p eq | true | nothing | _ = case eq of λ ()

    job-wait-change : ∀ j s p → T.waitJobPlan j s ≡ just p → Effect s p
    job-wait-change j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
    ... | nothing = case eq of λ ()
    ... | just jf with Sub.queued jf |
      lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
    ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
    ...     | nothing = case eq of λ ()
    ...     | just results with T.allClean results
    ...       | true = case just-injective eq of λ { refl → unchanged }
    ...       | false = case just-injective eq of λ { refl → unchanged }
    job-wait-change j s p eq | just jf | true | _ | _ = case eq of λ ()
    job-wait-change j s p eq | just jf | false | nothing | _ = case eq of λ ()
    job-wait-change j s p eq | just jf | false | just peer | false = case eq of λ ()

    monitor-wait-change : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Effect s p
    monitor-wait-change ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
    ... | nothing = case eq of λ ()
    ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
    ...   | just peer | true with T.waitResults f peer s
    ...     | nothing = case eq of λ ()
    ...     | just results with T.allClean results
    ...       | true = case just-injective eq of λ { refl → unchanged }
    ...       | false = case just-injective eq of λ { refl → unchanged }
    monitor-wait-change ref s p eq | just f | nothing | _ = case eq of λ ()
    monitor-wait-change ref s p eq | just f | just peer | false = case eq of λ ()

    -- Legacy FIFO/cursor bookkeeping never changes the generation table.
    note-legacy-calls : ∀ a f → T.calls (T.noteLegacy a f) ≡ T.calls f
    note-legacy-calls a f with T.legacySelector a
    ... | nothing = refl
    ... | just w = refl

    choose-change : ∀ a s p → Stores.UniqueKeys (T.calls (T.front s)) →
      T.choose a s ≡ just p → Effect s p
    choose-change (T.dispatch a) s p unique eq with T.inheritAllowed a s
    ... | false = case eq of λ ()
    ... | true = case just-injective eq of λ { refl →
      subst (Change (T.calls (T.front s))) (sym (note-legacy-calls a (T.front s))) unchanged }
    choose-change (T.startNext j rid) s p unique eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
      lookup rid (T.calls (T.front s)) in absent | Jobs.generationFresh rid (Jobs.jobs (T.physical (T.base s)))
    ... | true | just req | nothing | true with canInitiate (Peer.handleRef (T.peer req)) (number (T.protocol req)) |
      Jobs.muxAt (Peer.muxRef (T.peer req)) (T.physical (T.base s))
    ...   | false | _ = case eq of λ ()
    ...   | true | nothing = case eq of λ ()
    ...   | true | just m with Mux.status m
    ...     | Mux.stopping = case eq of λ ()
    ...     | Mux.stopped = case eq of λ ()
    ...     | Mux.failed err = case eq of λ ()
    ...     | Mux.ready with T.slotIdle (T.worker req) (number (T.protocol req)) (T.front s)
    ...       | false = case eq of λ ()
    ...       | true = case just-injective eq of λ { refl → allocated rid _ absent }
    choose-change (T.startNext j rid) s p unique eq | false | _ | _ | _ = case eq of λ ()
    choose-change (T.startNext j rid) s p unique eq | true | nothing | _ | _ = case eq of λ ()
    choose-change (T.startNext j rid) s p unique eq | true | just req | just old | _ = case eq of λ ()
    choose-change (T.startNext j rid) s p unique eq | true | just req | nothing | false = case eq of λ ()
    choose-change (T.selectStart w) s p unique eq = select-change w s p eq
    choose-change (T.invokeStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
    ... | T.selectedC rid | true = case just-injective eq of λ { refl → unchanged }
    choose-change (T.invokeStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
    choose-change (T.invokeStartTrace w) s p unique eq | T.tracingC rid | _ = case eq of λ ()
    choose-change (T.invokeStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
    choose-change (T.invokeStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
    choose-change (T.invokeStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
    choose-change (T.invokeStartTrace w) s p unique eq | T.selectedC rid | false = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
    ... | T.tracingC rid | true = case just-injective eq of λ { refl → unchanged }
    choose-change (T.returnStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq | T.selectedC rid | _ = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
    choose-change (T.returnStartTrace w) s p unique eq | T.tracingC rid | false = case eq of λ ()
    choose-change (T.forkStart w j) s p unique eq = fork-change w j s p eq
    choose-change (T.registerStart j) s p unique eq = register-change j s p eq
    choose-change (T.commitClean j) s p unique eq = completion-change j clean s p unique eq
    choose-change (T.commitError j err) s p unique eq = completion-change j (errored err) s p unique eq
    choose-change (T.pollResults ref w) s p unique eq = poll-change ref w s p eq
    choose-change (T.waitJobResults j) s p unique eq = job-wait-change j s p eq
    choose-change (T.waitMonitorResults ref) s p unique eq = monitor-wait-change ref s p eq
    choose-change (T.observeStartTraceException w result) s p unique eq with T.startTraceSelection w result s
    ... | just (rid , fs) = case just-injective eq of λ { refl → unchanged }
    ... | nothing = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
      Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
    ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
    ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
    ...     | just received = case just-injective eq of λ { refl → unchanged }
    ...     | nothing = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | false | _ = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.initial = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.reading = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitResults = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.closed = case eq of λ ()
    choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.sendReady entry w = case eq of λ ()

    -- Every enabled event preserves uniqueness and every already committed
    -- call record. Arbitrary externally fabricated Plan values are excluded.
    advance-change : ∀ a s {t} → Stores.UniqueKeys (T.calls (T.front s)) →
      T.advance a s ≡ just t → Change (T.calls (T.front s)) (T.calls (T.front t))
    advance-change a s unique eq with T.choose a s in chosen
    ... | nothing = case eq of λ ()
    ... | just p = subst (Change (T.calls (T.front s))) (sym (enact-calls p s eq))
      (choose-change a s p unique chosen)
    advance-unique : ∀ a s {t} → Stores.UniqueKeys (T.calls (T.front s)) →
      T.advance a s ≡ just t → Stores.UniqueKeys (T.calls (T.front t))
    advance-unique a s unique eq = change-unique (advance-change a s unique eq) unique
    advance-keeps : ∀ a s {t} → Stores.UniqueKeys (T.calls (T.front s)) →
      T.advance a s ≡ just t → Keeps (T.calls (T.front s)) (T.calls (T.front t))
    advance-keeps a s unique eq = change-keeps (advance-change a s unique eq)

    -- Induction derives the representation premise along the actual trace.
    run-unique : ∀ {s as t} → T.Runs s as t → Stores.UniqueKeys (T.calls (T.front s)) →
      Stores.UniqueKeys (T.calls (T.front t))
    run-unique T.stop unique = unique
    run-unique (T.more {s = s} {a = a} eq rest) unique = run-unique rest (advance-unique a s unique eq)
    run-keeps : ∀ {s as t} → T.Runs s as t → Stores.UniqueKeys (T.calls (T.front s)) →
      Keeps (T.calls (T.front s)) (T.calls (T.front t))
    run-keeps T.stop unique rid r result found filled = found
    run-keeps (T.more {s = s} {a = a} eq rest) unique rid r result found filled =
      run-keeps rest (advance-unique a s unique eq) rid r result
        (advance-keeps a s unique eq rid r result found filled) filled
    initial-unique : ∀ c g {s} → T.initialize c g ≡ just s → Stores.UniqueKeys (T.calls (T.front s))
    initial-unique c g eq with K.initial c g
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → Pairs.[] }

    -- No extra initial supply/uniqueness assumption: the executable initializer
    -- and enabled prefix derive the unique-key premise used by the suffix.
    from-initial-keeps : ∀ {c g start prefix before suffix after} →
      T.initialize c g ≡ just start → T.Runs start prefix before → T.Runs before suffix after →
      Keeps (T.calls (T.front before)) (T.calls (T.front after))
    from-initial-keeps {c} {g} initialized prefix suffix =
      run-keeps suffix (run-unique prefix (initial-unique c g initialized))

    observe-committed : ∀ rid r result s → lookup rid (T.calls (T.front s)) ≡ just r →
      T.value r ≡ just result → T.observe rid s ≡ just (T.localResult result)
    observe-committed rid r result s found filled rewrite found | filled = refl
    from-initial-observe : ∀ {c g start prefix before suffix after} →
      T.initialize c g ≡ just start → T.Runs start prefix before → T.Runs before suffix after →
      ∀ rid r result → lookup rid (T.calls (T.front before)) ≡ just r → T.value r ≡ just result →
      T.observe rid after ≡ just (T.localResult result)
    from-initial-observe {after = after} initialized prefix suffix rid r result found filled =
      observe-committed rid r result after (from-initial-keeps initialized prefix suffix rid r result found filled) filled

-- Shared peer actions update the source but retain the physical job store.
module CaptureIdentity where
  import ConnectionManagement.Properties.ServerIGExit as ExitFacts
  module Base = ExitFacts.CaptureIdentity isBearerClosed
  module Physical = Base.Physical
  jobs : K.State → _
  jobs s = Base.jobs (K.server s)
  Stable : K.State → K.State → Set
  Stable s t = Physical.Retains (jobs s) (jobs t)
  step-stable : ∀ a s {t} → K.step a s ≡ just t → Stable s t
  step-stable (K.serverStep a) s eq with K.serverAllowed a s
  ... | false = case eq of λ ()
  ... | true with E.step a (K.server s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → Base.step-stable a (K.server s) advanced }
  step-stable (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
  ... | false = case eq of λ ()
  ... | true with PS.step a (K.peers s)
  ...   | nothing = case eq of λ ()
  ...   | just p = case just-injective eq of λ { refl → Physical.identity (jobs s) }
  step-stable (K.coreStep a) s eq with K.coreAllowed a s
  ... | false = case eq of λ ()
  ... | true with E.step (K.coreAction a) (K.server s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → Base.step-stable (K.coreAction a) (K.server s) advanced }

  -- A call's reference is justified by the immutable identity of a historical
  -- physical row, independently of its changing body/result phase.
  module Frontend (canInitiate : HandleId → ℕ → Bool) where
    open import ConnectionManagement.Store using (Store; lookup; put)
    open import Relation.Nullary using (yes; no)
    open import Class.DecEq using (_≟_)
    open import Relation.Binary.PropositionalEquality using (trans; sym)
    open import ConnectionManagement.IGTypes using (number)
    import ConnectionManagement.Rules.MuxJobTypes as Types
    import ConnectionManagement.Rules.MuxRuntime as Mux
    import ConnectionManagement.Properties.Stores as Stores
    open import ConnectionManagement.Properties.Entries using (lookup-put)
    private
      module T = K.Protocols canInitiate
      module Cells = Protocols.CommittedCells canInitiate
    Match : RunId → T.Call → Types.ProtocolJob → Set
    Match rid r job = Physical.keyOf job ≡ Physical.key (T.owner r) (T.mux r)
      Mux.initiatorJob (number (T.descriptor r)) rid
    Sound : Store RunId T.Call → Store JobId Types.ProtocolJob → Set
    Sound calls rows = ∀ rid r j → lookup rid calls ≡ just r → T.thread r ≡ just j →
      Σ Types.ProtocolJob (λ job → lookup j rows ≡ just job × Match rid r job)
    Valid : T.Runtime → Set
    Valid s = Sound (T.calls (T.front s)) (jobs (T.base s))

    -- Transport keeps the exact owner/mux/direction/number/generation tuple.
    transport : ∀ calls {before after} → Physical.Retains before after → Sound calls before → Sound calls after
    transport calls retained valid rid r j found threaded with valid rid r j found threaded
    ... | old , seen , matches with retained j old seen
    ...   | next , located , equal = next , located , trans equal matches

    -- A single call-table writer only needs a witness for its replacement;
    -- all other keys retain their previous physical capture.
    put-sound : ∀ rid r calls rows → Sound calls rows →
      (∀ j → T.thread r ≡ just j → Σ Types.ProtocolJob (λ job → lookup j rows ≡ just job × Match rid r job)) →
      Sound (put rid r calls) rows
    put-sound rid r calls rows valid new q observed j found threaded with q ≟ rid
    ... | yes refl with just-injective (trans (sym (lookup-put rid r calls)) found)
    ...   | refl = new j threaded
    put-sound rid r calls rows valid new q observed j found threaded | no apart = valid q observed j
      (trans (sym (Stores.lookup-put-other rid q r calls apart)) found) threaded

    -- Fresh caller allocation has no thread reference yet.
    cons-sound : ∀ rid r calls rows → T.thread r ≡ nothing → Sound calls rows →
      Sound ((rid , r) ∷ calls) rows
    cons-sound rid r calls rows empty valid q observed j found threaded with q ≟ rid
    ... | no _ = valid q observed j found threaded
    ... | yes _ with just-injective found
    ...   | refl with trans (sym empty) threaded
    ...     | ()

    -- Completion changes only the local result value, retaining its capture.
    completion-sound : ∀ rid r result calls rows → lookup rid calls ≡ just r → Sound calls rows →
      Sound (put rid (record r { value = just result }) calls) rows
    completion-sound rid r result calls rows found valid = put-sound rid _ calls rows valid
      (λ j threaded → valid rid r j found threaded)

    -- Physical birth adds a globally fresh job and attaches that exact handle.
    -- The owner's equality is supplied by the executable fork selector.
    birth-sound : ∀ w j rid r calls rows → T.owner r ≡ w → lookup j rows ≡ nothing →
      Sound calls rows → Sound (put rid (record r { thread = just j }) calls)
        (put j (Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing) rows)
    birth-sound w j rid r calls rows owner fresh valid = put-sound rid (record r { thread = just j }) calls (put j born rows)
      (transport calls {before = rows} {after = put j born rows} (Physical.fresh-put j born rows fresh) valid) new
      where
      born : Types.ProtocolJob
      born = Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing
      new : ∀ k → just j ≡ just k → Σ Types.ProtocolJob (λ job →
        lookup k (put j (Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing) rows)
          ≡ just job × Match rid (record r { thread = just j }) job)
      new .j refl rewrite owner = _ , lookup-put j _ rows , refl

    import ConnectionManagement.MuxProtocolJobs as Jobs
    private
      module Pool = Jobs.Pool
    -- Apply the writer lemma to the actual guarded frontend fork.
    fork-preserves : ∀ w j s {t} → T.advance (T.forkStart w j) s ≡ just t → Valid s → Valid t
    fork-preserves w j s eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
      lookup w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
    ... | T.forkReadyC rid | true | just capturedFrame with lookup rid (T.calls (T.front s)) |
      Jobs.fresh j rid (T.physical (T.base s)) in fresh | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
    ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s))) in forked
    ...     | yes owner | nothing | nothing | just pool = case just-injective eq of λ { refl →
      birth-sound w j rid r (T.calls (T.front s)) (jobs (T.base s)) owner
        (Physical.fresh-lookup j rid (T.physical (T.base s)) fresh) valid }
    ...     | no _ | _ | _ | _ = case eq of λ ()
    ...     | yes _ | just _ | _ | _ = case eq of λ ()
    ...     | yes _ | nothing | just _ | _ = case eq of λ ()
    ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
    fork-preserves w j s eq valid | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
    fork-preserves w j s eq valid | T.idleC | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.selectedC rid | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.tracingC rid | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.failedC rid result | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.registeringC rid old | _ | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.forkReadyC rid | false | _ = case eq of λ ()
    fork-preserves w j s eq valid | T.forkReadyC rid | true | nothing = case eq of λ ()

    open import Relation.Binary.PropositionalEquality using (subst)
    open import ConnectionManagement.IGTypes using (clean; errored)
    import ConnectionManagement.Subsystem as Sub
    import ConnectionManagement.Rules.PeerActions as Peer
    import ConnectionManagement.Rules.PeerJobs as J
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.MuxPublicationUnwind as Publication
    import Data.Nat as Nat
    private
      module N = Publication isBearerClosed
    Ordinary : T.Plan → Bool
    Ordinary (T.birth _ _ _ _ _ _ _) = false
    Ordinary (T.caller _ _) = false
    Ordinary (T.complete _ _ _ _) = false
    Ordinary _ = true
    record Effect (s : T.Runtime) (p : T.Plan) : Set where
      constructor effect
      field preserves : ∀ {t} → T.enact p s ≡ just t → Valid s → Valid t
    ordinary-retains : ∀ p s {t} → Ordinary p ≡ true → T.enact p s ≡ just t →
      Physical.Retains (jobs (T.base s)) (jobs (T.base t))
    ordinary-retains (T.inherit a f) s ok eq with K.step a (T.base s) in advanced
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → step-stable a (T.base s) advanced }
    ordinary-retains (T.caller a f) s () eq
    ordinary-retains (T.birth w capturedFrame pool j rid r f) s () eq
    ordinary-retains (T.complete a rid r result) s () eq
    ordinary-retains (T.local f) s ok eq = case just-injective eq of λ { refl → Physical.identity (jobs (T.base s)) }
    ordinary-retains (T.reading r) s ok eq = case just-injective eq of λ { refl → Physical.identity (jobs (T.base s)) }
    ordinary-retains (T.traceFault w rid result fs) s ok eq = case just-injective eq of λ { refl → Physical.identity (jobs (T.base s)) }
    ordinary-retains (T.deliverTraceFault w rid result fs pc) s ok eq = case just-injective eq of λ { refl → Physical.identity (jobs (T.base s)) }
    ordinary-proof : ∀ p s → Ordinary p ≡ true → Cells.planCalls p s ≡ T.calls (T.front s) → ∀ {t} → T.enact p s ≡ just t → Valid s → Valid t
    ordinary-proof p s ok same {t} eq valid = subst (λ xs → Sound xs (jobs (T.base t)))
      (sym (trans (Cells.enact-calls p s eq) same))
      (transport (T.calls (T.front s)) {before = jobs (T.base s)} {after = jobs (T.base t)} (ordinary-retains p s ok eq) valid)
    ordinary : ∀ p s → Ordinary p ≡ true → Cells.planCalls p s ≡ T.calls (T.front s) → Effect s p
    ordinary p s ok same = effect (ordinary-proof p s ok same)
    allocation-proof : ∀ a f rid r s → T.calls f ≡ (rid , r) ∷ T.calls (T.front s) → T.thread r ≡ nothing → ∀ {t} → T.enact (T.caller a f) s ≡ just t → Valid s → Valid t
    allocation-proof a f rid r s same empty eq valid with PS.step a (K.peers (T.base s))
    ... | nothing = case eq of λ ()
    ... | just peer = case just-injective eq of λ { refl → subst (λ xs → Sound xs (jobs (T.base s))) (sym same)
      (cons-sound rid r (T.calls (T.front s)) (jobs (T.base s)) empty valid) }

    allocation : ∀ a f rid r s → T.calls f ≡ (rid , r) ∷ T.calls (T.front s) → T.thread r ≡ nothing → Effect s (T.caller a f)
    allocation a f rid r s same empty = effect (allocation-proof a f rid r s same empty)
    cache-jobs : ∀ rid r result f b → jobs (T.cacheResult rid r result f b) ≡ jobs b
    cache-jobs rid r result f b with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
    ... | nothing = refl
    ... | just (current , _) with current ≟ rid
    ...   | no _ = refl
    ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
    ...     | nothing = refl
    ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
    ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
    ...         | nothing = refl
    ...         | just rs = refl
    cache-jobs rid r result f b | just (current , _) | yes _ | just peer | no _ | _ = refl
    cache-jobs rid r result f b | just (current , _) | yes _ | just peer | yes _ | no _ = refl
    completion-proof : ∀ a rid r result s → lookup rid (T.calls (T.front s)) ≡ just r → ∀ {t} → T.enact (T.complete a rid r result) s ≡ just t → Valid s → Valid t
    completion-proof a rid r result s found eq valid with K.step a (T.base s) in advanced
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → subst (Sound (put rid (record r { value = just result }) (T.calls (T.front s))))
      (sym (cache-jobs rid r result (T.front s) b))
      (completion-sound rid r result (T.calls (T.front s)) (jobs b) found
        (transport (T.calls (T.front s)) {before = jobs (T.base s)} {after = jobs b} (step-stable a (T.base s) advanced) valid)) }
    completion : ∀ a rid r result s → lookup rid (T.calls (T.front s)) ≡ just r → Effect s (T.complete a rid r result)
    completion a rid r result s found = effect (completion-proof a rid r result s found)
    selected : ∀ a s p {t} → T.choose a s ≡ just p → T.enact p s ≡ just t → T.advance a s ≡ just t
    selected a s p chosen enacted rewrite chosen = enacted
    capture-select-change : ∀ w s p → T.selectPlan w s ≡ just p → Effect s p
    capture-select-change w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
      N.M.ownerContext w (N.G.base (T.group (T.base s)))
    ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
      Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
      Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
    ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
    ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...     | Mux.stopping | _ = case eq of λ ()
    ...     | Mux.stopped | _ = case eq of λ ()
    ...     | Mux.failed err | _ = case eq of λ ()
    ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
    ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
    ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
    ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
    ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
    ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
    capture-select-change w s p eq | false | _ | _ | _ = case eq of λ ()
    capture-select-change w s p eq | true | [] | _ | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
    capture-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

    capture-register-change : ∀ j s p → T.registerPlan j s ≡ just p → Effect s p
    capture-register-change j s p eq with T.byThread j (T.calls (T.front s))
    ... | nothing = case eq of λ ()
    ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
    ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
    ...     | yes _ | yes _ = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...     | no _ | _ = case eq of λ ()
    ...     | yes _ | no _ = case eq of λ ()
    capture-register-change j s p eq | just (rid , r) | T.idleC = case eq of λ ()
    capture-register-change j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
    capture-register-change j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
    capture-register-change j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
    capture-register-change j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

    capture-completion-change : ∀ j result s p → Stores.UniqueKeys (T.calls (T.front s)) →
      T.completionPlan j result s ≡ just p → Effect s p
    capture-completion-change j result s p unique eq with T.byThread j (T.calls (T.front s)) in found |
      lookup j (Jobs.jobs (T.physical (T.base s)))
    ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
      Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
    ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
      completion _ rid r result s (Cells.by-thread-lookup j (T.calls (T.front s)) rid r unique found) }
    ...   | just old | _ | _ | _ | _ = case eq of λ ()
    ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
    ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
    ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
    ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
    capture-completion-change j result s p unique eq | nothing | _ = case eq of λ ()
    capture-completion-change j result s p unique eq | just pair | nothing = case eq of λ ()

    capture-poll-change : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Effect s p
    capture-poll-change ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
      lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
    ... | true | just peer | nothing with Peer.status peer
    ...   | Peer.peerCold = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...   | Peer.peerCooling = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...   | Peer.peerWarm with T.firstPeer ref peer s
    ...     | nothing = case eq of λ ()
    ...     | just (kind , result) with T.cleanObservation result
    ...       | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...       | false = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-poll-change ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
    ...     | nothing = case eq of λ ()
    ...     | just (kind , result) with T.cleanObservation result
    ...       | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...       | false = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-poll-change ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-poll-change ref w s p eq | false | _ | _ = case eq of λ ()
    capture-poll-change ref w s p eq | true | nothing | _ = case eq of λ ()

    capture-job-wait-change : ∀ j s p → T.waitJobPlan j s ≡ just p → Effect s p
    capture-job-wait-change j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
    ... | nothing = case eq of λ ()
    ... | just jf with Sub.queued jf |
      lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
    ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
    ...     | nothing = case eq of λ ()
    ...     | just results with T.allClean results
    ...       | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...       | false = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-job-wait-change j s p eq | just jf | true | _ | _ = case eq of λ ()
    capture-job-wait-change j s p eq | just jf | false | nothing | _ = case eq of λ ()
    capture-job-wait-change j s p eq | just jf | false | just peer | false = case eq of λ ()

    capture-monitor-wait-change : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Effect s p
    capture-monitor-wait-change ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
    ... | nothing = case eq of λ ()
    ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
      T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
    ...   | just peer | true with T.waitResults f peer s
    ...     | nothing = case eq of λ ()
    ...     | just results with T.allClean results
    ...       | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...       | false = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-monitor-wait-change ref s p eq | just f | nothing | _ = case eq of λ ()
    capture-monitor-wait-change ref s p eq | just f | just peer | false = case eq of λ ()

    -- Legacy FIFO/cursor bookkeeping never changes the generation table.
    capture-note-legacy-calls : ∀ a f → T.calls (T.noteLegacy a f) ≡ T.calls f
    capture-note-legacy-calls a f with T.legacySelector a
    ... | nothing = refl
    ... | just w = refl

    capture-choose-change : ∀ a s p → Stores.UniqueKeys (T.calls (T.front s)) →
      T.choose a s ≡ just p → Effect s p
    capture-choose-change (T.dispatch a) s p unique eq with T.inheritAllowed a s
    ... | false = case eq of λ ()
    ... | true = case just-injective eq of λ { refl →
      ordinary _ s refl (Cells.note-legacy-calls a (T.front s)) }
    capture-choose-change (T.startNext j rid) s p unique eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
      lookup rid (T.calls (T.front s)) in absent | Jobs.generationFresh rid (Jobs.jobs (T.physical (T.base s)))
    ... | true | just req | nothing | true with canInitiate (Peer.handleRef (T.peer req)) (number (T.protocol req)) |
      Jobs.muxAt (Peer.muxRef (T.peer req)) (T.physical (T.base s))
    ...   | false | _ = case eq of λ ()
    ...   | true | nothing = case eq of λ ()
    ...   | true | just m with Mux.status m
    ...     | Mux.stopping = case eq of λ ()
    ...     | Mux.stopped = case eq of λ ()
    ...     | Mux.failed err = case eq of λ ()
    ...     | Mux.ready with T.slotIdle (T.worker req) (number (T.protocol req)) (T.front s)
    ...       | false = case eq of λ ()
    ...       | true = case just-injective eq of λ { refl → allocation _ _ rid _ s refl refl }
    capture-choose-change (T.startNext j rid) s p unique eq | false | _ | _ | _ = case eq of λ ()
    capture-choose-change (T.startNext j rid) s p unique eq | true | nothing | _ | _ = case eq of λ ()
    capture-choose-change (T.startNext j rid) s p unique eq | true | just req | just old | _ = case eq of λ ()
    capture-choose-change (T.startNext j rid) s p unique eq | true | just req | nothing | false = case eq of λ ()
    capture-choose-change (T.selectStart w) s p unique eq = capture-select-change w s p eq
    capture-choose-change (T.invokeStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
    ... | T.selectedC rid | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.tracingC rid | _ = case eq of λ ()
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
    capture-choose-change (T.invokeStartTrace w) s p unique eq | T.selectedC rid | false = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
    ... | T.tracingC rid | true = case just-injective eq of λ { refl → ordinary _ s refl refl }
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.selectedC rid | _ = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
    capture-choose-change (T.returnStartTrace w) s p unique eq | T.tracingC rid | false = case eq of λ ()
    capture-choose-change (T.forkStart w j) s p unique eq = effect (λ enacted valid → fork-preserves w j s (selected (T.forkStart w j) s p eq enacted) valid)
    capture-choose-change (T.registerStart j) s p unique eq = capture-register-change j s p eq
    capture-choose-change (T.commitClean j) s p unique eq = capture-completion-change j clean s p unique eq
    capture-choose-change (T.commitError j err) s p unique eq = capture-completion-change j (errored err) s p unique eq
    capture-choose-change (T.pollResults ref w) s p unique eq = capture-poll-change ref w s p eq
    capture-choose-change (T.waitJobResults j) s p unique eq = capture-job-wait-change j s p eq
    capture-choose-change (T.waitMonitorResults ref) s p unique eq = capture-monitor-wait-change ref s p eq
    capture-choose-change (T.observeStartTraceException w result) s p unique eq with T.startTraceSelection w result s
    ... | just (rid , fs) = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ... | nothing = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
      Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
    ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
    ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
    ...     | just received = case just-injective eq of λ { refl → ordinary _ s refl refl }
    ...     | nothing = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | false | _ = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.initial = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.reading = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitResults = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.closed = case eq of λ ()
    capture-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.sendReady entry w = case eq of λ ()


    -- Derive representation and capture validity along actual enabled events.
    advance-preserves : ∀ a s {t} → Stores.UniqueKeys (T.calls (T.front s)) → T.advance a s ≡ just t → Valid s → Valid t
    advance-preserves a s unique eq valid with T.choose a s in chosen
    ... | nothing = case eq of λ ()
    ... | just p = Effect.preserves (capture-choose-change a s p unique chosen) eq valid
    runs-preserve : ∀ {s as t} → T.Runs s as t → Stores.UniqueKeys (T.calls (T.front s)) → Valid s → Valid t
    runs-preserve T.stop unique valid = valid
    runs-preserve (T.more {s = s} {a = a} eq rest) unique valid = runs-preserve rest
      (Cells.advance-unique a s unique eq) (advance-preserves a s unique eq valid)
    initial-valid : ∀ c g {s} → T.initialize c g ≡ just s → Valid s
    initial-valid c g eq with K.initial c g
    ... | nothing = case eq of λ ()
    ... | just b = case just-injective eq of λ { refl → λ rid r j () }
    initialized-soundness : ∀ {c g start as t} → T.initialize c g ≡ just start → T.Runs start as t → Valid t
    initialized-soundness {c} {g} initialized path = runs-preserve path (Cells.initial-unique c g initialized) (initial-valid c g initialized)

-- Preserve already captured physical results through this adapter.
module CommittedRows where
  import ConnectionManagement.Properties.ServerIGExit as ExitFacts
  module Base = ExitFacts.CommittedRows isBearerClosed
  module Physical = Base.Physical
  jobs : K.State → _
  jobs s = Base.jobs (K.server s)
  Stable : K.State → K.State → Set
  Stable s t = Physical.Retains (jobs s) (jobs t)
  step-stable : ∀ a s {t} → K.step a s ≡ just t → Stable s t
  step-stable (K.serverStep a) s eq with K.serverAllowed a s
  ... | false = case eq of λ ()
  ... | true with E.step a (K.server s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → Base.step-stable a (K.server s) advanced }
  step-stable (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
  ... | false = case eq of λ ()
  ... | true with PS.step a (K.peers s)
  ...   | nothing = case eq of λ ()
  ...   | just p = case just-injective eq of λ { refl → Physical.identity (jobs s) }
  step-stable (K.coreStep a) s eq with K.coreAllowed a s
  ... | false = case eq of λ ()
  ... | true with E.step (K.coreAction a) (K.server s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → Base.step-stable (K.coreAction a) (K.server s) advanced }
