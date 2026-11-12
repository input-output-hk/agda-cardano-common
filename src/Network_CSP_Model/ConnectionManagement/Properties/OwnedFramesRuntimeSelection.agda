{-# OPTIONS --guardedness #-}

-- Reach preservation for every actually selected frontend plan. The read
-- selectors certify non-CM-wait PCs; startNext certifies its direct job action.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesRuntimeSelection
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (HandleId; JobId; RunId)
open import Data.Nat using (ℕ)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.PeerContext as Context
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module C = Context isIOManagerError

import ConnectionManagement.Properties.OwnedFramesRuntime as RuntimeFacts
import ConnectionManagement.Properties.OwnedFramesRead as ReadFacts

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open import ConnectionManagement.Store using (Store; lookup; put)
  open import ConnectionManagement.IGTypes using (RunResult; clean; errored; number)
  open import Class.DecEq using (_≟_)
  open import Relation.Nullary using (yes; no)
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.Rules.CMShutdown as Close
  import Data.Nat as Nat
  private
    module T = K.Protocols canInitiate
    module N = Publication isBearerClosed
    module Jobs = N.P
    module Pool = Jobs.Pool

  open RuntimeFacts.Protocols isBearerClosed isIOManagerError canInitiate public using (Inv; initial-inv)
  private
    module Runtime = RuntimeFacts.Protocols isBearerClosed isIOManagerError canInitiate
    module Read = ReadFacts isBearerClosed isIOManagerError
  open Runtime using (Safe; safe; simple; caller; poll-read; job-read; follow-read)

  -- A successful physical wait selects only awaitHot or awaitAll.
  wait-not-await : ∀ f peer s results → T.waitResults f peer s ≡ just results → Read.NotAwait f
  wait-not-await f peer s results eq with J.pc f
  ... | J.awaitHot = (λ ()) , (λ ())
  ... | J.awaitAll = (λ ()) , (λ ())
  ... | J.begin = case eq of λ ()
  ... | J.awaitAcquire = case eq of λ ()
  ... | J.startBundle t ns = case eq of λ ()
  ... | J.publishBundle t = case eq of λ ()
  ... | J.markWarm = case eq of λ ()
  ... | J.forkMonitor = case eq of λ ()
  ... | J.finishActivation = case eq of λ ()
  ... | J.callRelease = case eq of λ ()
  ... | J.awaitRelease = case eq of λ ()
  ... | J.delayFailure = case eq of λ ()
  ... | J.awaitCold result = case eq of λ ()
  ... | J.complete result = case eq of λ ()
  ... | J.acquirePolicy fault = case eq of λ ()
  ... | J.nodeDelivery fault = case eq of λ ()
  ... | J.nodeRethrow fault = case eq of λ ()

  -- Physical fork selection changes no source or peer-context observation.
  fork-shape : ∀ w j s p → T.forkPlan w j s ≡ just p → Safe s p
  fork-shape w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    lookup w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
  ... | T.forkReadyC rid | true | just capturedFrame with lookup rid (T.calls (T.front s)) |
    Jobs.fresh j rid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s))) in forked
  ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
    simple _ s refl }
  ...     | no _ | _ | _ | _ = case eq of λ ()
  ...     | yes _ | just _ | _ | _ = case eq of λ ()
  ...     | yes _ | nothing | just _ | _ = case eq of λ ()
  ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
  fork-shape w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
  fork-shape w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
  fork-shape w j s p eq | T.idleC | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.registeringC rid old | _ | _ = case eq of λ ()
  fork-shape w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
  fork-shape w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()

  -- Selecting a queued physical start only changes the frontend cursor.
  select-shape : ∀ w s p → T.selectPlan w s ≡ just p → Safe s p
  select-shape w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
    N.M.ownerContext w (N.G.base (T.group (T.base s)))
  ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
    Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
    Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → simple _ s refl }
  ...     | Mux.stopping | _ = case eq of λ ()
  ...     | Mux.stopped | _ = case eq of λ ()
  ...     | Mux.failed err | _ = case eq of λ ()
  ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
  ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
  ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
  ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
  ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
  ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
  select-shape w s p eq | false | _ | _ | _ = case eq of λ ()
  select-shape w s p eq | true | [] | _ | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
  select-shape w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

  -- Registration delegates to a real shared physical step.
  register-shape : ∀ j s p → T.registerPlan j s ≡ just p → Safe s p
  register-shape j s p eq with T.byThread j (T.calls (T.front s))
  ... | nothing = case eq of λ ()
  ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
  ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = case just-injective eq of λ { refl → simple _ s refl }
  ...     | no _ | _ = case eq of λ ()
  ...     | yes _ | no _ = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.idleC = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

  -- Each physical completion delegates to a K step and peer-result caching.
  completion-shape : ∀ j result s p →
    T.completionPlan j result s ≡ just p → Safe s p
  completion-shape j clean s p eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    simple _ s refl }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  completion-shape j clean s p eq | nothing | _ = case eq of λ ()
  completion-shape j clean s p eq | just pair | nothing = case eq of λ ()

  completion-shape j (errored commitErr) s p eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    simple _ s refl }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  completion-shape j (errored commitErr) s p eq | nothing | _ = case eq of λ ()
  completion-shape j (errored commitErr) s p eq | just pair | nothing = case eq of λ ()

  -- Polling either delegates or changes only the peer status.
  poll-shape : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Safe s p
  poll-shape ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | true | just peer | nothing with Peer.status peer
  ...   | Peer.peerCold = case just-injective eq of λ { refl → simple _ s refl }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → simple _ s refl }
  ...   | Peer.peerWarm with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → simple _ s refl }
  ...       | false = case just-injective eq of λ { refl → poll-read ref peer s }
  poll-shape ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → simple _ s refl }
  ...       | false = case just-injective eq of λ { refl → poll-read ref peer s }
  poll-shape ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → simple _ s refl }
  poll-shape ref w s p eq | false | _ | _ = case eq of λ ()
  poll-shape ref w s p eq | true | nothing | _ = case eq of λ ()

  -- The failed job read replaces a caller-preserving non-CM-wait continuation.
  job-wait-shape : ∀ j s p → T.waitJobPlan j s ≡ just p → Safe s p
  job-wait-shape j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s)))) in found
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf |
    lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s in waited
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → simple _ s refl }
  ...       | false = case just-injective eq of λ { refl → job-read j jf peer s found
          (wait-not-await (Sub.execution jf) peer s results waited) }
  job-wait-shape j s p eq | just jf | true | _ | _ = case eq of λ ()
  job-wait-shape j s p eq | just jf | false | nothing | _ = case eq of λ ()
  job-wait-shape j s p eq | just jf | false | just peer | false = case eq of λ ()

  -- The failed followup read keeps its physical thread and caller identity.
  monitor-wait-shape : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Safe s p
  monitor-wait-shape ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s)))) in found
  ... | nothing = case eq of λ ()
  ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
  ...   | just peer | true with T.waitResults f peer s in waited
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → simple _ s refl }
  ...       | false = case just-injective eq of λ { refl → follow-read ref f peer s found
          (wait-not-await f peer s results waited) }
  monitor-wait-shape ref s p eq | just f | nothing | _ = case eq of λ ()
  monitor-wait-shape ref s p eq | just f | just peer | false = case eq of λ ()

  -- Every event selects a certified plan; the complements are impossible.
  choose-shape : ∀ a s p →
    T.choose a s ≡ just p → Safe s p
  choose-shape (T.dispatch a) s p eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl →
    simple _ s refl }
  choose-shape (T.startNext j rid) s p eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
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
  ...       | true = case just-injective eq of λ { refl → caller j _ s }
  choose-shape (T.startNext j rid) s p eq | false | _ | _ | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | nothing | _ | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | just req | just old | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | just req | nothing | false = case eq of λ ()
  choose-shape (T.selectStart w) s p eq = select-shape w s p eq
  choose-shape (T.invokeStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.selectedC rid | true = case just-injective eq of λ { refl → simple _ s refl }
  choose-shape (T.invokeStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.tracingC rid | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.selectedC rid | false = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.tracingC rid | true = case just-injective eq of λ { refl → simple _ s refl }
  choose-shape (T.returnStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.selectedC rid | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.tracingC rid | false = case eq of λ ()
  choose-shape (T.forkStart w j) s p eq = fork-shape w j s p eq
  choose-shape (T.registerStart j) s p eq = register-shape j s p eq
  choose-shape (T.commitClean j) s p eq = completion-shape j clean s p eq
  choose-shape (T.commitError j err) s p eq = completion-shape j (errored err) s p eq
  choose-shape (T.pollResults ref w) s p eq = poll-shape ref w s p eq
  choose-shape (T.waitJobResults j) s p eq = job-wait-shape j s p eq
  choose-shape (T.waitMonitorResults ref) s p eq = monitor-wait-shape ref s p eq
  choose-shape (T.observeStartTraceException w result) s p eq with T.startTraceSelection w result s
  ... | just (rid , fs) = case just-injective eq of λ { refl → simple _ s refl }
  ... | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
    Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
  ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
  ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
  ...     | just received = case just-injective eq of λ { refl → simple _ s refl }
  ...     | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | false | _ = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.initial = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.reading = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitResults = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.closed = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.sendReady entry w = case eq of λ ()

  -- choose and enact compose to preserve Reach at each actual event.
  advance-inv : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Inv t
  advance-inv a s eq held with T.choose a s in chosen
  ... | nothing = case eq of λ ()
  ... | just p = Runtime.Safe.preserves (choose-shape a s p chosen) eq held

  -- Induction retains every auxiliary fact needed by later peer steps.
  runs-inv : ∀ {s as t} → T.Runs s as t → Inv s → Inv t
  runs-inv T.stop held = held
  runs-inv (T.more {s = s} {a = a} eq rest) held = runs-inv rest (advance-inv a s eq held)
