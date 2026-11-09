{-# OPTIONS --guardedness #-}

-- One case analysis of the Protocols frontend's plan selection, shared by the
-- properties preserved along T.advance. Every enabled choose result has one of
-- four shapes; a property supplies one lemma per shape instead of repeating the
-- whole selection analysis. The shapes record facts only; no plan is assumed
-- enabled beyond the choose equation itself.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersPlanShapes
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

module Frontend (canInitiate : HandleId → ℕ → Bool) where
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

  -- Plans whose effect is a source step or local bookkeeping only.
  Ordinary : T.Plan → Bool
  Ordinary (T.birth _ _ _ _ _ _ _) = false
  Ordinary (T.caller _ _) = false
  Ordinary (T.complete _ _ _ _) = false
  Ordinary _ = true
  commitAction : JobId → RunResult → Jobs.Action
  commitAction j clean = Jobs.commitClean j
  commitAction j (errored err) = Jobs.protocolException j err

  -- The call table a plan leaves, before its source effect is consulted.
  planCalls : T.Plan → T.Runtime → Store RunId T.Call
  planCalls (T.inherit a f) s = T.calls f
  planCalls (T.caller a f) s = T.calls f
  planCalls (T.local f) s = T.calls f
  planCalls (T.birth w captured pool j rid r f) s = T.calls f
  planCalls (T.complete a rid r result) s = put rid (record r { value = just result }) (T.calls (T.front s))
  planCalls _ s = T.calls (T.front s)
  -- Legacy FIFO/cursor bookkeeping never changes the generation table.
  note-legacy-calls : ∀ a f → T.calls (T.noteLegacy a f) ≡ T.calls f
  note-legacy-calls a f with T.legacySelector a
  ... | nothing = refl
  ... | just w = refl

  -- The four shapes, each with the facts its selector established.
  data Shape (s : T.Runtime) : T.Plan → Set where
    ordinary : ∀ p → Ordinary p ≡ true → planCalls p s ≡ T.calls (T.front s) → Shape s p
    allocation : ∀ a f rid r → T.calls f ≡ (rid , r) ∷ T.calls (T.front s) → T.value r ≡ nothing →
      T.thread r ≡ nothing → lookup rid (T.calls (T.front s)) ≡ nothing → Shape s (T.caller a f)
    completion : ∀ j result rid r → T.byThread j (T.calls (T.front s)) ≡ just (rid , r) →
      T.value r ≡ nothing → Shape s (T.complete (T.physicalAction (commitAction j result)) rid r result)
    fork : ∀ w j {p} → T.choose (T.forkStart w j) s ≡ just p → Shape s p

  select-shape : ∀ w s p → T.selectPlan w s ≡ just p → Shape s p
  select-shape w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
    N.M.ownerContext w (N.G.base (T.group (T.base s)))
  ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
    Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
    Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → ordinary _ refl refl }
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

  register-shape : ∀ j s p → T.registerPlan j s ≡ just p → Shape s p
  register-shape j s p eq with T.byThread j (T.calls (T.front s))
  ... | nothing = case eq of λ ()
  ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
  ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...     | no _ | _ = case eq of λ ()
  ...     | yes _ | no _ = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.idleC = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
  register-shape j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

  completion-shape : ∀ j result s p →
    T.completionPlan j result s ≡ just p → Shape s p
  completion-shape j clean s p eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    completion j clean rid r found empty }
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
    completion j (errored commitErr) rid r found empty }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  completion-shape j (errored commitErr) s p eq | nothing | _ = case eq of λ ()
  completion-shape j (errored commitErr) s p eq | just pair | nothing = case eq of λ ()

  poll-shape : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Shape s p
  poll-shape ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | true | just peer | nothing with Peer.status peer
  ...   | Peer.peerCold = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...   | Peer.peerWarm with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...       | false = case just-injective eq of λ { refl → ordinary _ refl refl }
  poll-shape ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...       | false = case just-injective eq of λ { refl → ordinary _ refl refl }
  poll-shape ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → ordinary _ refl refl }
  poll-shape ref w s p eq | false | _ | _ = case eq of λ ()
  poll-shape ref w s p eq | true | nothing | _ = case eq of λ ()

  job-wait-shape : ∀ j s p → T.waitJobPlan j s ≡ just p → Shape s p
  job-wait-shape j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf |
    lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...       | false = case just-injective eq of λ { refl → ordinary _ refl refl }
  job-wait-shape j s p eq | just jf | true | _ | _ = case eq of λ ()
  job-wait-shape j s p eq | just jf | false | nothing | _ = case eq of λ ()
  job-wait-shape j s p eq | just jf | false | just peer | false = case eq of λ ()

  monitor-wait-shape : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Shape s p
  monitor-wait-shape ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
  ...   | just peer | true with T.waitResults f peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...       | false = case just-injective eq of λ { refl → ordinary _ refl refl }
  monitor-wait-shape ref s p eq | just f | nothing | _ = case eq of λ ()
  monitor-wait-shape ref s p eq | just f | just peer | false = case eq of λ ()

  choose-shape : ∀ a s p →
    T.choose a s ≡ just p → Shape s p
  choose-shape (T.dispatch a) s p eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl →
    ordinary _ refl (note-legacy-calls a (T.front s)) }
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
  ...       | true = case just-injective eq of λ { refl → allocation _ _ rid _ refl refl refl absent }
  choose-shape (T.startNext j rid) s p eq | false | _ | _ | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | nothing | _ | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | just req | just old | _ = case eq of λ ()
  choose-shape (T.startNext j rid) s p eq | true | just req | nothing | false = case eq of λ ()
  choose-shape (T.selectStart w) s p eq = select-shape w s p eq
  choose-shape (T.invokeStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.selectedC rid | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  choose-shape (T.invokeStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.tracingC rid | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-shape (T.invokeStartTrace w) s p eq | T.selectedC rid | false = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.tracingC rid | true = case just-injective eq of λ { refl → ordinary _ refl refl }
  choose-shape (T.returnStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.selectedC rid | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-shape (T.returnStartTrace w) s p eq | T.tracingC rid | false = case eq of λ ()
  choose-shape (T.forkStart w j) s p eq = fork w j eq
  choose-shape (T.registerStart j) s p eq = register-shape j s p eq
  choose-shape (T.commitClean j) s p eq = completion-shape j clean s p eq
  choose-shape (T.commitError j err) s p eq = completion-shape j (errored err) s p eq
  choose-shape (T.pollResults ref w) s p eq = poll-shape ref w s p eq
  choose-shape (T.waitJobResults j) s p eq = job-wait-shape j s p eq
  choose-shape (T.waitMonitorResults ref) s p eq = monitor-wait-shape ref s p eq
  choose-shape (T.observeStartTraceException w result) s p eq with T.startTraceSelection w result s
  ... | just (rid , fs) = case just-injective eq of λ { refl → ordinary _ refl refl }
  ... | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
    Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
  ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
  ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
  ...     | just received = case just-injective eq of λ { refl → ordinary _ refl refl }
  ...     | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | false | _ = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.initial = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.reading = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitResults = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.closed = case eq of λ ()
  choose-shape (T.deliverStartTraceShutdown err) s p eq | true | Close.sendReady entry w = case eq of λ ()
