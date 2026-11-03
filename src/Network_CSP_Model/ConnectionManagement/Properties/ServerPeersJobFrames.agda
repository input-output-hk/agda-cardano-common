{-# OPTIONS --guardedness #-}

-- Actual selected frontend operations and their shared job-frame effects.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersJobFrames
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (HandleId; RunId; PeerConnectionId; MuxId; WorkerId; JobId)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored; number)
open import ConnectionManagement.Store using (Store; put) renaming (lookup to find)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.ServerPeers as Facts
import ConnectionManagement.Properties.ServerPeersResults as Results
import ConnectionManagement.Properties.Stores as Stores
import ConnectionManagement.Properties.PeerJobFrames as FrameFacts
import ConnectionManagement.Properties.GovernorCompletions as QueueFacts
import ConnectionManagement.Properties.ServerPeersCompletions as CompletionFacts
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import Data.Nat as Nat
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module PS = Supervision isIOManagerError
  module GP = PS.GP
  module C = Context isIOManagerError
  module N = Publication isBearerClosed
  module Jobs = N.P
  module Pool = Jobs.Pool
  module F = FrameFacts isIOManagerError
  module Q = CompletionFacts isBearerClosed isIOManagerError


sharedTag : K.Action → F.Tag
sharedTag (K.peerStep a) = F.supervisionTag a
sharedTag _ = F.other
view : K.State → F.View
view s = F.view (K.peers s)
shared-change : ∀ a s {t} → K.step a s ≡ just t → F.Effect (sharedTag a) (view s) (view t)
shared-change (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → F.same refl }
shared-change (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → F.same refl }
shared-change (K.peerStep a) s eq with K.peerOpen s | K.peerAllowed a s
... | Data.Bool.false | _ = case eq of λ ()
... | Data.Bool.true | Data.Bool.false = case eq of λ ()
... | Data.Bool.true | Data.Bool.true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → F.supervision-change a (K.peers s) advanced }

sub-reflect : ∀ a j → F.subTag a ≡ F.jobStep j J.observeHot → a ≡ Sub.jobStep j J.observeHot
sub-reflect (Sub.core a) j ()
sub-reflect Sub.publishPublicState j ()
sub-reflect (Sub.sampleTime t) j ()
sub-reflect (Sub.applyAt t) j ()
sub-reflect (Sub.setTargets t) j ()
sub-reflect (Sub.selectMonitor d) j ()
sub-reflect Sub.selectCompletion j ()
sub-reflect Sub.selectTargets j ()
sub-reflect Sub.selectWakeup j ()
sub-reflect Sub.registerWakeup j ()
sub-reflect Sub.expireWakeup j ()
sub-reflect Sub.cancelWakeup j ()
sub-reflect Sub.publishCounters j ()
sub-reflect Sub.traceSelection j ()
sub-reflect (Sub.selectPolicy p) j ()
sub-reflect (Sub.forkJob w c s) j ()
sub-reflect Sub.registerJob j ()
sub-reflect Sub.finishLaunch j ()
sub-reflect (Sub.jobStep k a) j refl = refl
sub-reflect (Sub.enqueueCompletion k d) j ()
sub-reflect (Sub.deregisterJob k) j ()
sub-reflect (Sub.protocolResult r n o) j ()
sub-reflect (Sub.publishInitiatorResult r n) j ()
sub-reflect (Sub.pollPeer r w) j ()
sub-reflect (Sub.monitorStep r a) j ()
sub-reflect (Sub.monitorFinished r) j ()
sub-reflect (Sub.observeInitiatorFailure r) j ()
governor-reflect : ∀ a j → F.governorTag a ≡ F.jobStep j J.observeHot → a ≡ GP.run (Sub.jobStep j J.observeHot)
governor-reflect (GP.run a) j eq = cong GP.run (sub-reflect a j eq)
governor-reflect (GP.handoff w) j ()
governor-reflect (GP.beginClose order) j ()
governor-reflect GP.requestCancel j ()
governor-reflect GP.join j ()
governor-reflect GP.finishClose j ()
governor-reflect (GP.deliverCancellation err) j ()
governor-reflect (GP.deliverOpenCancellation err) j ()
governor-reflect (GP.cleanup k a) j ()
governor-reflect (GP.bodyUnwound k) j ()
governor-reflect (GP.recoverCloseFailure k) j ()
governor-reflect (GP.deregisterCancelled k) j ()
governor-reflect (GP.publishAsyncResult k) j ()
supervision-reflect : ∀ a j → F.supervisionTag a ≡ F.jobStep j J.observeHot → a ≡ PS.run (GP.run (Sub.jobStep j J.observeHot))
supervision-reflect (PS.run a) j eq = cong PS.run (governor-reflect a j eq)
supervision-reflect (PS.forkMonitor k w) j ()
supervision-reflect (PS.registerMonitor k) j ()
supervision-reflect (PS.returnEstablishment k) j ()
supervision-reflect (PS.finishEstablishment k) j ()
supervision-reflect (PS.monitorException k err) j ()
supervision-reflect (PS.commitMonitorError k) j ()
supervision-reflect (PS.finishMonitorError k) j ()
supervision-reflect (PS.finishMonitor k) j ()
supervision-reflect (PS.scope a) j ()
supervision-reflect (PS.beginMonitorClose order) j ()
supervision-reflect PS.requestMonitorCancel j ()
supervision-reflect PS.joinMonitor j ()
supervision-reflect PS.finishMonitorClose j ()
supervision-reflect (PS.deliverMonitorCancellation err) j ()
supervision-reflect (PS.deliverBlockedMonitorCancellation err) j ()
supervision-reflect (PS.monitorBodyUnwound k) j ()
supervision-reflect (PS.deregisterMonitor k) j ()
supervision-reflect (PS.publishMonitorResult k) j ()
shared-reflect : ∀ a j → sharedTag a ≡ F.jobStep j J.observeHot → a ≡ K.peerStep (PS.run (GP.run (Sub.jobStep j J.observeHot)))
shared-reflect (K.serverStep a) j ()
shared-reflect (K.coreStep a) j ()
shared-reflect (K.peerStep a) j eq = cong K.peerStep (supervision-reflect a j eq)

all-sub-reflect : ∀ a j → F.subTag a ≡ F.jobStep j J.observeAll → a ≡ Sub.jobStep j J.observeAll
all-sub-reflect (Sub.core a) j ()
all-sub-reflect Sub.publishPublicState j ()
all-sub-reflect (Sub.sampleTime t) j ()
all-sub-reflect (Sub.applyAt t) j ()
all-sub-reflect (Sub.setTargets t) j ()
all-sub-reflect (Sub.selectMonitor d) j ()
all-sub-reflect Sub.selectCompletion j ()
all-sub-reflect Sub.selectTargets j ()
all-sub-reflect Sub.selectWakeup j ()
all-sub-reflect Sub.registerWakeup j ()
all-sub-reflect Sub.expireWakeup j ()
all-sub-reflect Sub.cancelWakeup j ()
all-sub-reflect Sub.publishCounters j ()
all-sub-reflect Sub.traceSelection j ()
all-sub-reflect (Sub.selectPolicy p) j ()
all-sub-reflect (Sub.forkJob w c s) j ()
all-sub-reflect Sub.registerJob j ()
all-sub-reflect Sub.finishLaunch j ()
all-sub-reflect (Sub.jobStep k a) j refl = refl
all-sub-reflect (Sub.enqueueCompletion k d) j ()
all-sub-reflect (Sub.deregisterJob k) j ()
all-sub-reflect (Sub.protocolResult r n o) j ()
all-sub-reflect (Sub.publishInitiatorResult r n) j ()
all-sub-reflect (Sub.pollPeer r w) j ()
all-sub-reflect (Sub.monitorStep r a) j ()
all-sub-reflect (Sub.monitorFinished r) j ()
all-sub-reflect (Sub.observeInitiatorFailure r) j ()
all-governor-reflect : ∀ a j → F.governorTag a ≡ F.jobStep j J.observeAll → a ≡ GP.run (Sub.jobStep j J.observeAll)
all-governor-reflect (GP.run a) j eq = cong GP.run (all-sub-reflect a j eq)
all-governor-reflect (GP.handoff w) j ()
all-governor-reflect (GP.beginClose order) j ()
all-governor-reflect GP.requestCancel j ()
all-governor-reflect GP.join j ()
all-governor-reflect GP.finishClose j ()
all-governor-reflect (GP.deliverCancellation err) j ()
all-governor-reflect (GP.deliverOpenCancellation err) j ()
all-governor-reflect (GP.cleanup k a) j ()
all-governor-reflect (GP.bodyUnwound k) j ()
all-governor-reflect (GP.recoverCloseFailure k) j ()
all-governor-reflect (GP.deregisterCancelled k) j ()
all-governor-reflect (GP.publishAsyncResult k) j ()
all-supervision-reflect : ∀ a j → F.supervisionTag a ≡ F.jobStep j J.observeAll → a ≡ PS.run (GP.run (Sub.jobStep j J.observeAll))
all-supervision-reflect (PS.run a) j eq = cong PS.run (all-governor-reflect a j eq)
all-supervision-reflect (PS.forkMonitor k w) j ()
all-supervision-reflect (PS.registerMonitor k) j ()
all-supervision-reflect (PS.returnEstablishment k) j ()
all-supervision-reflect (PS.finishEstablishment k) j ()
all-supervision-reflect (PS.monitorException k err) j ()
all-supervision-reflect (PS.commitMonitorError k) j ()
all-supervision-reflect (PS.finishMonitorError k) j ()
all-supervision-reflect (PS.finishMonitor k) j ()
all-supervision-reflect (PS.scope a) j ()
all-supervision-reflect (PS.beginMonitorClose order) j ()
all-supervision-reflect PS.requestMonitorCancel j ()
all-supervision-reflect PS.joinMonitor j ()
all-supervision-reflect PS.finishMonitorClose j ()
all-supervision-reflect (PS.deliverMonitorCancellation err) j ()
all-supervision-reflect (PS.deliverBlockedMonitorCancellation err) j ()
all-supervision-reflect (PS.monitorBodyUnwound k) j ()
all-supervision-reflect (PS.deregisterMonitor k) j ()
all-supervision-reflect (PS.publishMonitorResult k) j ()
all-shared-reflect : ∀ a j → sharedTag a ≡ F.jobStep j J.observeAll → a ≡ K.peerStep (PS.run (GP.run (Sub.jobStep j J.observeAll)))
all-shared-reflect (K.serverStep a) j ()
all-shared-reflect (K.coreStep a) j ()
all-shared-reflect (K.peerStep a) j eq = cong K.peerStep (all-supervision-reflect a j eq)

module Frontend (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Hist = Q.Frontend canInitiate
  runtime-view : T.Runtime → F.View
  runtime-view s = view (T.base s)
  planTag : T.Plan → F.Tag
  planTag (T.inherit a _) = sharedTag a
  planTag (T.caller a _) = F.supervisionTag a
  planTag (T.complete a _ _ _) = sharedTag a
  planTag _ = F.other
  Reading : T.Runtime → T.Plan → Set
  Reading s (T.reading r) = F.Effect F.other (runtime-view s)
    (F.frameView (T.ReadState.jobRows r) (T.ReadState.peerRows r) (K.source (T.base s)))
  Reading s _ = ⊤
  -- Only the physical job-wait selector may forward observeHot; arbitrary
  -- reading plans need a derived classification of their table writes.
  record Permit (event : T.Event) (s : T.Runtime) (plan : T.Plan) : Set where
    constructor allowed
    field hot : ∀ j → planTag plan ≡ F.jobStep j J.observeHot → event ≡ T.waitJobResults j
          allResults : ∀ j → planTag plan ≡ F.jobStep j J.observeAll → event ≡ T.waitJobResults j
          reading : Reading s plan
  quiet : ∀ {event s plan} → planTag plan ≡ F.other → Reading s plan → Permit event s plan
  quiet eq safe = allowed (λ j tag → case trans (sym eq) tag of λ ()) (λ j tag → case trans (sym eq) tag of λ ()) safe
  wait-id : ∀ {j k a b} → F.jobStep k a ≡ F.jobStep j b → T.waitJobResults k ≡ T.waitJobResults j
  wait-id refl = refl
  dispatch-hot : ∀ a s → T.inheritAllowed a s ≡ true → ∀ j → sharedTag a ≡ F.jobStep j J.observeHot → T.dispatch a ≡ T.waitJobResults j
  dispatch-hot a s permitted j eq with shared-reflect a j eq
  ... | refl = case permitted of λ ()
  dispatch-all : ∀ a s → T.inheritAllowed a s ≡ true → ∀ j → sharedTag a ≡ F.jobStep j J.observeAll → T.dispatch a ≡ T.waitJobResults j
  dispatch-all a s permitted j eq with all-shared-reflect a j eq
  ... | refl = case permitted of λ ()
  permit-fork-change : ∀ {event} w j s p → T.forkPlan w j s ≡ just p → Permit event s p
  permit-fork-change w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    find w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
  ... | T.forkReadyC rid | true | just f with find rid (T.calls (T.front s)) in found |
    Jobs.fresh j rid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s)))
  ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
    quiet refl tt }
  ...     | no _ | _ | _ | _ = case eq of λ ()
  ...     | yes _ | just thread | _ | _ = case eq of λ ()
  ...     | yes _ | nothing | just result | _ = case eq of λ ()
  ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
  permit-fork-change w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
  permit-fork-change w j s p eq | T.idleC | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.registeringC rid target | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
  permit-fork-change w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()


  permit-select-change : ∀ {event} w s p → T.selectPlan w s ≡ just p → Permit event s p
  permit-select-change w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
    N.M.ownerContext w (N.G.base (T.group (T.base s)))
  ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
    Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
    Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → quiet refl tt }
  ...     | Mux.stopping | _ = case eq of λ ()
  ...     | Mux.stopped | _ = case eq of λ ()
  ...     | Mux.failed err | _ = case eq of λ ()
  ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
  ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
  ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
  ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
  ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
  ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
  permit-select-change w s p eq | false | _ | _ | _ = case eq of λ ()
  permit-select-change w s p eq | true | [] | _ | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
  permit-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

  permit-register-change : ∀ {event} j s p → T.registerPlan j s ≡ just p → Permit event s p
  permit-register-change j s p eq with T.byThread j (T.calls (T.front s))
  ... | nothing = case eq of λ ()
  ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
  ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = case just-injective eq of λ { refl → quiet refl tt }
  ...     | no _ | _ = case eq of λ ()
  ...     | yes _ | no _ = case eq of λ ()
  permit-register-change j s p eq | just (rid , r) | T.idleC = case eq of λ ()
  permit-register-change j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
  permit-register-change j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
  permit-register-change j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
  permit-register-change j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

  permit-completion-change : ∀ {event} j result s p →
    T.completionPlan j result s ≡ just p → Permit event s p
  permit-completion-change j clean s p eq with T.byThread j (T.calls (T.front s)) in found |
    find j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    quiet refl tt }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  permit-completion-change j clean s p eq | nothing | _ = case eq of λ ()
  permit-completion-change j clean s p eq | just pair | nothing = case eq of λ ()

  permit-completion-change j (errored commitErr) s p eq with T.byThread j (T.calls (T.front s)) in found |
    find j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    quiet refl tt }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  permit-completion-change j (errored commitErr) s p eq | nothing | _ = case eq of λ ()
  permit-completion-change j (errored commitErr) s p eq | just pair | nothing = case eq of λ ()

  permit-poll-change : ∀ {event} ref w s p → T.pollResultsPlan ref w s ≡ just p → Permit event s p
  permit-poll-change ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    find ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    find ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | true | just peer | nothing with Peer.status peer
  ...   | Peer.peerCold = case just-injective eq of λ { refl → quiet refl tt }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → quiet refl tt }
  ...   | Peer.peerWarm with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → quiet refl tt }
  ...       | false = case just-injective eq of λ { refl → quiet refl (F.same refl) }
  permit-poll-change ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → quiet refl tt }
  ...       | false = case just-injective eq of λ { refl → quiet refl (F.same refl) }
  permit-poll-change ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → quiet refl tt }
  permit-poll-change ref w s p eq | false | _ | _ = case eq of λ ()
  permit-poll-change ref w s p eq | true | nothing | _ = case eq of λ ()

  permit-job-wait-change : ∀ j s p → T.waitJobPlan j s ≡ just p → Permit (T.waitJobResults j) s p
  permit-job-wait-change j s p eq with find j (C.SubContext.jobs (C.subsystem (K.context (T.base s)))) in found
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf |
    find (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → allowed (λ k eq → wait-id eq) (λ k eq → wait-id eq) tt }
  ...       | false = case just-injective eq of λ { refl → quiet refl (F.failed j jf (record jf { execution = T.failedFrame (Sub.execution jf) }) found refl refl) }
  permit-job-wait-change j s p eq | just jf | true | _ | _ = case eq of λ ()
  permit-job-wait-change j s p eq | just jf | false | nothing | _ = case eq of λ ()
  permit-job-wait-change j s p eq | just jf | false | just peer | false = case eq of λ ()

  permit-monitor-wait-change : ∀ {event} ref s p → T.waitMonitorPlan ref s ≡ just p → Permit event s p
  permit-monitor-wait-change ref s p eq with find ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just f with find (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
  ...   | just peer | true with T.waitResults f peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → quiet refl tt }
  ...       | false = case just-injective eq of λ { refl → quiet refl (F.same refl) }
  permit-monitor-wait-change ref s p eq | just f | nothing | _ = case eq of λ ()
  permit-monitor-wait-change ref s p eq | just f | just peer | false = case eq of λ ()

  permit-choose-change : ∀ a s p →
    T.choose a s ≡ just p → Permit a s p
  permit-choose-change (T.dispatch a) s p eq with T.inheritAllowed a s in permitted
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl →
    allowed (dispatch-hot a s permitted) (dispatch-all a s permitted) tt }
  permit-choose-change (T.startNext j rid) s p eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
    find rid (T.calls (T.front s)) in absent | Jobs.generationFresh rid (Jobs.jobs (T.physical (T.base s)))
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
  ...       | true = case just-injective eq of λ { refl → allowed (λ k ()) (λ k ()) tt }
  permit-choose-change (T.startNext j rid) s p eq | false | _ | _ | _ = case eq of λ ()
  permit-choose-change (T.startNext j rid) s p eq | true | nothing | _ | _ = case eq of λ ()
  permit-choose-change (T.startNext j rid) s p eq | true | just req | just old | _ = case eq of λ ()
  permit-choose-change (T.startNext j rid) s p eq | true | just req | nothing | false = case eq of λ ()
  permit-choose-change (T.selectStart w) s p eq = permit-select-change w s p eq
  permit-choose-change (T.invokeStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.selectedC rid | true = case just-injective eq of λ { refl → quiet refl tt }
  permit-choose-change (T.invokeStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  permit-choose-change (T.invokeStartTrace w) s p eq | T.tracingC rid | _ = case eq of λ ()
  permit-choose-change (T.invokeStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  permit-choose-change (T.invokeStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  permit-choose-change (T.invokeStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  permit-choose-change (T.invokeStartTrace w) s p eq | T.selectedC rid | false = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.tracingC rid | true = case just-injective eq of λ { refl → quiet refl tt }
  permit-choose-change (T.returnStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq | T.selectedC rid | _ = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  permit-choose-change (T.returnStartTrace w) s p eq | T.tracingC rid | false = case eq of λ ()
  permit-choose-change (T.forkStart w j) s p eq = permit-fork-change w j s p eq
  permit-choose-change (T.registerStart j) s p eq = permit-register-change j s p eq
  permit-choose-change (T.commitClean j) s p eq = permit-completion-change j clean s p eq
  permit-choose-change (T.commitError j err) s p eq = permit-completion-change j (errored err) s p eq
  permit-choose-change (T.pollResults ref w) s p eq = permit-poll-change ref w s p eq
  permit-choose-change (T.waitJobResults j) s p eq = permit-job-wait-change j s p eq
  permit-choose-change (T.waitMonitorResults ref) s p eq = permit-monitor-wait-change ref s p eq
  permit-choose-change (T.observeStartTraceException w result) s p eq with T.startTraceSelection w result s
  ... | just (rid , fs) = case just-injective eq of λ { refl → quiet refl tt }
  ... | nothing = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
    Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
  ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
  ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
  ...     | just received = case just-injective eq of λ { refl → quiet refl tt }
  ...     | nothing = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | false | _ = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.initial = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.reading = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitResults = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.closed = case eq of λ ()
  permit-choose-change (T.deliverStartTraceShutdown err) s p eq | true | Close.sendReady entry w = case eq of λ ()

  -- Selection permissions accompany the exact enabled adapter operation.
  enact-change : ∀ plan s {t} → Reading s plan → T.enact plan s ≡ just t →
    F.Effect (planTag plan) (runtime-view s) (runtime-view t)
  enact-change (T.inherit a f) s safe eq with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → shared-change a (T.base s) advanced }
  enact-change (T.caller a f) s safe eq with PS.step a (K.peers (T.base s)) in advanced
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → F.supervision-change a (K.peers (T.base s)) advanced }
  enact-change (T.local f) s safe eq = case just-injective eq of λ { refl → F.same refl }
  enact-change (T.reading r) s safe eq = case just-injective eq of λ { refl → safe }
  enact-change (T.traceFault w rid result fs) s safe eq = case just-injective eq of λ { refl → F.same refl }
  enact-change (T.deliverTraceFault w rid result fs coordinator) s safe eq = case just-injective eq of λ { refl → F.same refl }
  enact-change (T.birth w capturedFrame pool j rid r f) s safe eq = case just-injective eq of λ { refl → F.same refl }
  enact-change (T.complete a rid r result) s safe eq with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → F.after-rows
    (cong (λ v → QueueFacts.View.frames v) (sym (Hist.cache-view rid r result (T.front s) b))) (shared-change a (T.base s) advanced) }
