{-# OPTIONS --guardedness #-}

-- Initialized historical provenance of peer caches and published constants.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersCache
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (HandleId; RunId; PeerConnectionId; MuxId)
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
import ConnectionManagement.Properties.PeerCache as Pure
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

-- Only these cells assert a stored outcome; running is an action, not a value.
data Stored (result : RunResult) : Peer.Cell → Set where
  returned : Stored result (Peer.returned result)
  retired : Stored result (Peer.notRunning result)

module Frontend (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Cells = Facts.Protocols.CommittedCells isBearerClosed isIOManagerError canInitiate
    module Read = Results.Observations isBearerClosed isIOManagerError canInitiate
  Rows = Store RunId T.Call
  -- The witness may be an older committed call, with exactly these identities.
  Back : Rows → PeerConnectionId → HandleId → MuxId → ℕ → RunResult → Set
  Back xs ref h m n result = Σ RunId (λ rid → Σ T.Call (λ r →
    find rid xs ≡ just r × T.value r ≡ just result × T.peerRef r ≡ ref ×
    T.handleRef r ≡ h × T.mux r ≡ m × number (T.descriptor r) ≡ n))
  Cache : Rows → Peer.Runtime → Set
  Cache xs = Pure.Evidence.Runtime (Back xs)
  rows : K.State → Peer.Runtime
  rows b = C.SubContext.peers (C.subsystem (K.context b))
  Valid : T.Runtime → Set
  Valid s = Cache (T.calls (T.front s)) (rows (T.base s))

  -- Already committed call records survive every enabled frontend transition.
  transport-back : ∀ before after → Cells.Keeps before after → ∀ ref h m n result →
    Back before ref h m n result → Back after ref h m n result
  transport-back before after retained ref h m n result (rid , r , found , filled , rest) =
    rid , r , retained rid r result found filled , filled , rest
  transport-cell : ∀ before after → Cells.Keeps before after → ∀ ref h m n cell →
    Pure.Evidence.Cell (Back before) ref h m n cell → Pure.Evidence.Cell (Back after) ref h m n cell
  transport-cell before after retained ref h m n Peer.notStarted valid = valid
  transport-cell before after retained ref h m n Peer.running valid = valid
  transport-cell before after retained ref h m n (Peer.returned result) valid = transport-back before after retained ref h m n result valid
  transport-cell before after retained ref h m n (Peer.notRunning result) valid = transport-back before after retained ref h m n result valid
  transport-runs : ∀ before after → Cells.Keeps before after → ∀ ref h m rs →
    Pure.Evidence.Runs (Back before) ref h m rs → Pure.Evidence.Runs (Back after) ref h m rs
  transport-runs before after retained ref h m [] [] = []
  transport-runs before after retained ref h m (r ∷ rs) ((actual , published) ∷ rest) =
    (transport-cell before after retained ref h m _ (Peer.actual r) actual ,
     transport-cell before after retained ref h m _ (Peer.published r) published) ∷
    transport-runs before after retained ref h m rs rest
  transport : ∀ before after → Cells.Keeps before after → ∀ peers → Cache before peers → Cache after peers
  transport before after retained [] [] = []
  transport before after retained ((ref , p) ∷ peers) (valid ∷ rest) =
    transport-runs before after retained ref _ _ (Peer.runs p) valid ∷ transport before after retained peers rest

  -- A completion creates the backing witness before caching its result.
  cache-preserves : ∀ xs rid r result f b → Back xs (T.peerRef r) (T.handleRef r) (T.mux r) (number (T.descriptor r)) result →
    Cache xs (rows b) → Cache xs (rows (T.cacheResult rid r result f b))
  cache-preserves xs rid r result f b backed valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = valid
  ... | just (current , _) with current ≟ rid
  ...   | no _ = valid
  ...   | yes _ with find (T.peerRef r) (rows b) in found
  ...     | nothing = valid
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes sameHandle | yes sameMux with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer) in finished
  ...         | nothing = valid
  ...         | just rs = Pure.Evidence.put-peer (Back xs) (T.peerRef r) _ (rows b)
    (Pure.Evidence.finish (Back xs) (T.peerRef r) (Peer.handleRef peer) (Peer.muxRef peer) _ result (Peer.runs peer)
      (subst (λ h → Back xs (T.peerRef r) h (Peer.muxRef peer) (number (T.descriptor r)) result) (sym sameHandle)
        (subst (λ m → Back xs (T.peerRef r) (T.handleRef r) m (number (T.descriptor r)) result) (sym sameMux) backed))
      finished (Pure.Evidence.found-peer (Back xs) (T.peerRef r) peer (rows b) valid found)) valid
  cache-preserves xs rid r result f b backed valid | just (current , _) | yes _ | just peer | no _ | _ = valid
  cache-preserves xs rid r result f b backed valid | just (current , _) | yes _ | just peer | yes _ | no _ = valid

  -- The shared gate rejects the only raw result writer. Other peer actions
  -- preserve the generic cache invariant, including nonempty start traversals.
  safeSub : Rows → Sub.Action → Bool
  safeSub xs = Pure.Evidence.Subsystem.safeSub (Back xs)
  safePeer : Rows → PS.Action → Bool
  safePeer xs = Pure.Evidence.Supervised.safePeer (Back xs) isIOManagerError
  safe-sub-allowed : ∀ xs a b → K.rawPeerAllowed a b ≡ true → safeSub xs a ≡ true
  safe-sub-allowed xs (Sub.core a) b allowed = refl
  safe-sub-allowed xs Sub.publishPublicState b allowed = refl
  safe-sub-allowed xs (Sub.sampleTime t) b allowed = refl
  safe-sub-allowed xs (Sub.applyAt t) b allowed = refl
  safe-sub-allowed xs (Sub.setTargets ts) b allowed = refl
  safe-sub-allowed xs (Sub.selectMonitor ds) b allowed = refl
  safe-sub-allowed xs Sub.selectCompletion b allowed = refl
  safe-sub-allowed xs Sub.selectTargets b allowed = refl
  safe-sub-allowed xs Sub.selectWakeup b allowed = refl
  safe-sub-allowed xs Sub.registerWakeup b allowed = refl
  safe-sub-allowed xs Sub.expireWakeup b allowed = refl
  safe-sub-allowed xs Sub.cancelWakeup b allowed = refl
  safe-sub-allowed xs Sub.publishCounters b allowed = refl
  safe-sub-allowed xs Sub.traceSelection b allowed = refl
  safe-sub-allowed xs (Sub.selectPolicy ps) b allowed = refl
  safe-sub-allowed xs (Sub.forkJob w child sock) b allowed = refl
  safe-sub-allowed xs Sub.registerJob b allowed = refl
  safe-sub-allowed xs Sub.finishLaunch b allowed = refl
  safe-sub-allowed xs (Sub.jobStep j a) b allowed = refl
  safe-sub-allowed xs (Sub.enqueueCompletion j delay) b allowed = refl
  safe-sub-allowed xs (Sub.deregisterJob j) b allowed = refl
  safe-sub-allowed xs (Sub.protocolResult ref n result) b ()
  safe-sub-allowed xs (Sub.publishInitiatorResult ref i) b allowed = refl
  safe-sub-allowed xs (Sub.pollPeer ref w) b allowed = refl
  safe-sub-allowed xs (Sub.monitorStep ref a) b allowed = refl
  safe-sub-allowed xs (Sub.monitorFinished ref) b allowed = refl
  safe-sub-allowed xs (Sub.observeInitiatorFailure ref) b allowed = refl
  safe-peer-allowed : ∀ xs a b → K.peerAllowed a b ≡ true → safePeer xs a ≡ true
  safe-peer-allowed xs (PS.run (GP.run a)) b allowed = safe-sub-allowed xs a b allowed
  safe-peer-allowed xs (PS.run (GP.handoff w)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.beginClose order)) b allowed = refl
  safe-peer-allowed xs (PS.run GP.requestCancel) b allowed = refl
  safe-peer-allowed xs (PS.run GP.join) b allowed = refl
  safe-peer-allowed xs (PS.run GP.finishClose) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.deliverCancellation err)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.deliverOpenCancellation err)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.cleanup j a)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.bodyUnwound j)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.recoverCloseFailure j)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.deregisterCancelled j)) b allowed = refl
  safe-peer-allowed xs (PS.run (GP.publishAsyncResult j)) b allowed = refl
  safe-peer-allowed xs (PS.forkMonitor j w) b allowed = refl
  safe-peer-allowed xs (PS.registerMonitor j) b allowed = refl
  safe-peer-allowed xs (PS.returnEstablishment j) b allowed = refl
  safe-peer-allowed xs (PS.finishEstablishment j) b allowed = refl
  safe-peer-allowed xs (PS.monitorException j err) b allowed = refl
  safe-peer-allowed xs (PS.commitMonitorError j) b allowed = refl
  safe-peer-allowed xs (PS.finishMonitorError j) b allowed = refl
  safe-peer-allowed xs (PS.finishMonitor j) b allowed = refl
  safe-peer-allowed xs (PS.scope a) b allowed = refl
  safe-peer-allowed xs (PS.beginMonitorClose order) b allowed = refl
  safe-peer-allowed xs PS.requestMonitorCancel b allowed = refl
  safe-peer-allowed xs PS.joinMonitor b allowed = refl
  safe-peer-allowed xs PS.finishMonitorClose b allowed = refl
  safe-peer-allowed xs (PS.deliverMonitorCancellation err) b allowed = refl
  safe-peer-allowed xs (PS.deliverBlockedMonitorCancellation err) b allowed = refl
  safe-peer-allowed xs (PS.monitorBodyUnwound j) b allowed = refl
  safe-peer-allowed xs (PS.deregisterMonitor j) b allowed = refl
  safe-peer-allowed xs (PS.publishMonitorResult j) b allowed = refl

  shared-preserves : ∀ xs a b {t} → K.step a b ≡ just t → Cache xs (rows b) → Cache xs (rows t)
  shared-preserves xs (K.serverStep a) b eq valid with K.serverAllowed a b
  ... | false = case eq of λ ()
  ... | true with E.step a (K.server b)
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → valid }
  shared-preserves xs (K.coreStep a) b eq valid with K.coreAllowed a b
  ... | false = case eq of λ ()
  ... | true with E.step (K.coreAction a) (K.server b)
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → valid }
  shared-preserves xs (K.peerStep a) b eq valid with K.peerOpen b | K.peerAllowed a b in allowed
  ... | false | _ = case eq of λ ()
  ... | true | false = case eq of λ ()
  ... | true | true with PS.step a (K.peers b) in moved
  ...   | nothing = case eq of λ ()
  ...   | just peer = case just-injective eq of λ { refl →
    Pure.Evidence.Supervised.Monitors.step-preserves (Back xs) isIOManagerError a (K.peers b)
      (safe-peer-allowed xs a b allowed) moved valid }

  -- Plans operate with the final table's backing relation. The frontend's
  -- committed-row theorem transports all old witnesses to that table first.
  record Effect (s : T.Runtime) (plan : T.Plan) : Set where
    constructor effect
    field
      preserves : ∀ {t} → T.enact plan s ≡ just t →
        Cache (T.calls (T.front t)) (rows (T.base s)) → Valid t
  Ordinary : T.Plan → Bool
  Ordinary (T.caller _ _) = false
  Ordinary (T.complete _ _ _ _) = false
  Ordinary (T.reading _) = false
  Ordinary _ = true
  ordinary-proof : ∀ plan s → Ordinary plan ≡ true → ∀ {t} → T.enact plan s ≡ just t →
    Cache (T.calls (T.front t)) (rows (T.base s)) → Valid t
  ordinary-proof (T.inherit a f) s ok eq valid with K.step a (T.base s) in moved
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → shared-preserves (T.calls f) a (T.base s) moved valid }
  ordinary-proof (T.local f) s ok eq valid = case just-injective eq of λ { refl → valid }
  ordinary-proof (T.birth w captured pool j rid r f) s ok eq valid = case just-injective eq of λ { refl → valid }
  ordinary-proof (T.traceFault w rid result fs) s ok eq valid = case just-injective eq of λ { refl → valid }
  ordinary-proof (T.deliverTraceFault w rid result fs pc) s ok eq valid = case just-injective eq of λ { refl → valid }
  ordinary-proof (T.caller _ _) s () eq valid
  ordinary-proof (T.complete _ _ _ _) s () eq valid
  ordinary-proof (T.reading _) s () eq valid
  ordinary : ∀ plan s → Ordinary plan ≡ true → Effect s plan
  ordinary plan s ok = effect (ordinary-proof plan s ok)
  caller-proof : ∀ a f s → safePeer (T.calls f) a ≡ true → ∀ {t} → T.enact (T.caller a f) s ≡ just t →
    Cache (T.calls (T.front t)) (rows (T.base s)) → Valid t
  caller-proof a f s permitted eq valid with PS.step a (K.peers (T.base s)) in moved
  ... | nothing = case eq of λ ()
  ... | just peer = case just-injective eq of λ { refl →
    Pure.Evidence.Supervised.Monitors.step-preserves (Back (T.calls f)) isIOManagerError a (K.peers (T.base s)) permitted moved valid }
  caller : ∀ a f s → safePeer (T.calls f) a ≡ true → Effect s (T.caller a f)
  caller a f s permitted = effect (caller-proof a f s permitted)
  completion-proof : ∀ a rid r result s {t} → T.enact (T.complete a rid r result) s ≡ just t →
    Cache (T.calls (T.front t)) (rows (T.base s)) → Valid t
  completion-proof a rid r result s eq valid with K.step a (T.base s) in moved
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → cache-preserves
    (put rid (record r { value = just result }) (T.calls (T.front s))) rid r result (T.front s) b
    (rid , record r { value = just result } , lookup-put rid (record r { value = just result }) (T.calls (T.front s)) , refl , refl , refl , refl , refl)
    (shared-preserves (put rid (record r { value = just result }) (T.calls (T.front s))) a (T.base s) moved valid) }
  completion : ∀ a rid r result s → Effect s (T.complete a rid r result)
  completion a rid r result s = effect (completion-proof a rid r result s)
  reading : ∀ r s → (∀ xs → Cache xs (rows (T.base s)) → Cache xs (T.ReadState.peerRows r)) → Effect s (T.reading r)
  reading r s preserves = effect (λ eq valid → case just-injective eq of λ { refl → preserves (T.calls (T.front s)) valid })
  failed-peer : ∀ xs ref f peer → Pure.Evidence.Peer (Back xs) ref peer → Pure.Evidence.Peer (Back xs) ref (T.failedPeer f peer)
  failed-peer xs ref f peer valid with J.pc f
  ... | J.awaitHot = Pure.Evidence.cool (Back xs) ref peer valid
  ... | J.begin = valid
  ... | J.awaitAcquire = valid
  ... | J.startBundle _ _ = valid
  ... | J.publishBundle _ = valid
  ... | J.markWarm = valid
  ... | J.forkMonitor = valid
  ... | J.finishActivation = valid
  ... | J.awaitAll = valid
  ... | J.callRelease = valid
  ... | J.awaitRelease = valid
  ... | J.delayFailure = valid
  ... | J.awaitCold _ = valid
  ... | J.complete _ = valid
  ... | J.acquirePolicy _ = valid
  ... | J.nodeDelivery _ = valid
  ... | J.nodeRethrow _ = valid

  -- Classify actual selectors rather than assuming arbitrary plans are safe.
  cache-fork-change : ∀ w j s p → T.forkPlan w j s ≡ just p → Effect s p
  cache-fork-change w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    find w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
  ... | T.forkReadyC rid | true | just f with find rid (T.calls (T.front s)) in found |
    Jobs.fresh j rid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s)))
  ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl →
    ordinary _ s refl }
  ...     | no _ | _ | _ | _ = case eq of λ ()
  ...     | yes _ | just thread | _ | _ = case eq of λ ()
  ...     | yes _ | nothing | just result | _ = case eq of λ ()
  ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
  cache-fork-change w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
  cache-fork-change w j s p eq | T.idleC | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.registeringC rid target | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
  cache-fork-change w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()


  cache-select-change : ∀ w s p → T.selectPlan w s ≡ just p → Effect s p
  cache-select-change w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
    N.M.ownerContext w (N.G.base (T.group (T.base s)))
  ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
    Jobs.muxAt mid (T.physical (T.base s)) | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s))) |
    Jobs.noResults (Jobs.poolAt w (T.physical (T.base s))) | Pool.phase (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → ordinary _ s refl }
  ...     | Mux.stopping | _ = case eq of λ ()
  ...     | Mux.stopped | _ = case eq of λ ()
  ...     | Mux.failed err | _ = case eq of λ ()
  ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
  ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
  ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
  ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
  ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
  ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
  cache-select-change w s p eq | false | _ | _ | _ = case eq of λ ()
  cache-select-change w s p eq | true | [] | _ | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
  cache-select-change w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

  cache-register-change : ∀ j s p → T.registerPlan j s ≡ just p → Effect s p
  cache-register-change j s p eq with T.byThread j (T.calls (T.front s))
  ... | nothing = case eq of λ ()
  ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
  ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = case just-injective eq of λ { refl → ordinary _ s refl }
  ...     | no _ | _ = case eq of λ ()
  ...     | yes _ | no _ = case eq of λ ()
  cache-register-change j s p eq | just (rid , r) | T.idleC = case eq of λ ()
  cache-register-change j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
  cache-register-change j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
  cache-register-change j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
  cache-register-change j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

  cache-completion-change : ∀ j result s p → Stores.UniqueKeys (T.calls (T.front s)) →
    T.completionPlan j result s ≡ just p → Effect s p
  cache-completion-change j clean s p unique eq with T.byThread j (T.calls (T.front s)) in found |
    find j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    completion _ rid r clean s }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  cache-completion-change j clean s p unique eq | nothing | _ = case eq of λ ()
  cache-completion-change j clean s p unique eq | just pair | nothing = case eq of λ ()

  cache-completion-change j (errored commitErr) s p unique eq with T.byThread j (T.calls (T.front s)) in found |
    find j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    completion _ rid r (errored commitErr) s }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  cache-completion-change j (errored commitErr) s p unique eq | nothing | _ = case eq of λ ()
  cache-completion-change j (errored commitErr) s p unique eq | just pair | nothing = case eq of λ ()

  cache-poll-change : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Effect s p
  cache-poll-change ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    find ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    find ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | true | just peer | nothing with Peer.status peer
  ...   | Peer.peerCold = case just-injective eq of λ { refl → ordinary _ s refl }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → ordinary _ s refl }
  ...   | Peer.peerWarm with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → ordinary _ s refl }
  ...       | false = case just-injective eq of λ { refl → reading _ s (λ xs valid → Pure.Evidence.put-peer (Back xs) ref _ (rows (T.base s))
      (Pure.Evidence.cool (Back xs) ref peer (Pure.Evidence.found-peer (Back xs) ref peer (rows (T.base s)) valid peerFound)) valid) }
  cache-poll-change ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → ordinary _ s refl }
  ...       | false = case just-injective eq of λ { refl → reading _ s (λ xs valid → Pure.Evidence.put-peer (Back xs) ref _ (rows (T.base s))
      (Pure.Evidence.cool (Back xs) ref peer (Pure.Evidence.found-peer (Back xs) ref peer (rows (T.base s)) valid peerFound)) valid) }
  cache-poll-change ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → ordinary _ s refl }
  cache-poll-change ref w s p eq | false | _ | _ = case eq of λ ()
  cache-poll-change ref w s p eq | true | nothing | _ = case eq of λ ()

  cache-job-wait-change : ∀ j s p → T.waitJobPlan j s ≡ just p → Effect s p
  cache-job-wait-change j s p eq with find j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf |
    find (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → ordinary _ s refl }
  ...       | false = case just-injective eq of λ { refl → reading _ s (λ xs valid → Pure.Evidence.put-peer (Back xs) (J.connectionRef (Sub.execution jf)) _ (rows (T.base s))
      (failed-peer xs (J.connectionRef (Sub.execution jf)) (Sub.execution jf) peer (Pure.Evidence.found-peer (Back xs) (J.connectionRef (Sub.execution jf)) peer (rows (T.base s)) valid peerFound)) valid) }
  cache-job-wait-change j s p eq | just jf | true | _ | _ = case eq of λ ()
  cache-job-wait-change j s p eq | just jf | false | nothing | _ = case eq of λ ()
  cache-job-wait-change j s p eq | just jf | false | just peer | false = case eq of λ ()

  cache-monitor-wait-change : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Effect s p
  cache-monitor-wait-change ref s p eq with find ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just f with find (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
  ...   | just peer | true with T.waitResults f peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → ordinary _ s refl }
  ...       | false = case just-injective eq of λ { refl → reading _ s (λ xs valid → Pure.Evidence.put-peer (Back xs) (J.connectionRef f) _ (rows (T.base s))
      (failed-peer xs (J.connectionRef f) f peer (Pure.Evidence.found-peer (Back xs) (J.connectionRef f) peer (rows (T.base s)) valid peerFound)) valid) }
  cache-monitor-wait-change ref s p eq | just f | nothing | _ = case eq of λ ()
  cache-monitor-wait-change ref s p eq | just f | just peer | false = case eq of λ ()

  cache-choose-change : ∀ a s p → Stores.UniqueKeys (T.calls (T.front s)) →
    T.choose a s ≡ just p → Effect s p
  cache-choose-change (T.dispatch a) s p unique eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl →
    ordinary _ s refl }
  cache-choose-change (T.startNext j rid) s p unique eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
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
  ...       | true = case just-injective eq of λ { refl → caller _ _ s refl }
  cache-choose-change (T.startNext j rid) s p unique eq | false | _ | _ | _ = case eq of λ ()
  cache-choose-change (T.startNext j rid) s p unique eq | true | nothing | _ | _ = case eq of λ ()
  cache-choose-change (T.startNext j rid) s p unique eq | true | just req | just old | _ = case eq of λ ()
  cache-choose-change (T.startNext j rid) s p unique eq | true | just req | nothing | false = case eq of λ ()
  cache-choose-change (T.selectStart w) s p unique eq = cache-select-change w s p eq
  cache-choose-change (T.invokeStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.selectedC rid | true = case just-injective eq of λ { refl → ordinary _ s refl }
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.tracingC rid | _ = case eq of λ ()
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
  cache-choose-change (T.invokeStartTrace w) s p unique eq | T.selectedC rid | false = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.tracingC rid | true = case just-injective eq of λ { refl → ordinary _ s refl }
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.idleC | _ = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.selectedC rid | _ = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.forkReadyC rid | _ = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.registeringC rid j | _ = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.failedC rid result | _ = case eq of λ ()
  cache-choose-change (T.returnStartTrace w) s p unique eq | T.tracingC rid | false = case eq of λ ()
  cache-choose-change (T.forkStart w j) s p unique eq = cache-fork-change w j s p eq
  cache-choose-change (T.registerStart j) s p unique eq = cache-register-change j s p eq
  cache-choose-change (T.commitClean j) s p unique eq = cache-completion-change j clean s p unique eq
  cache-choose-change (T.commitError j err) s p unique eq = cache-completion-change j (errored err) s p unique eq
  cache-choose-change (T.pollResults ref w) s p unique eq = cache-poll-change ref w s p eq
  cache-choose-change (T.waitJobResults j) s p unique eq = cache-job-wait-change j s p eq
  cache-choose-change (T.waitMonitorResults ref) s p unique eq = cache-monitor-wait-change ref s p eq
  cache-choose-change (T.observeStartTraceException w result) s p unique eq with T.startTraceSelection w result s
  ... | just (rid , fs) = case just-injective eq of λ { refl → ordinary _ s refl }
  ... | nothing = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
    Close.phase (N.W.shutdown (N.R.base (N.raw (T.publication (T.base s)))))
  ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (N.R.async err) s
  ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (T.publication (T.base s))))
  ...     | just received = case just-injective eq of λ { refl → ordinary _ s refl }
  ...     | nothing = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | false | _ = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.initial = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.reading = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.awaitResults = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.closed = case eq of λ ()
  cache-choose-change (T.deliverStartTraceShutdown err) s p unique eq | true | Close.sendReady entry w = case eq of λ ()



  -- Derive the cache invariant from initialization and every enabled event.
  advance-preserves : ∀ a s {t} → Stores.UniqueKeys (T.calls (T.front s)) → T.advance a s ≡ just t → Valid s → Valid t
  advance-preserves a s {t} unique eq valid with T.choose a s in chosen
  ... | nothing = case eq of λ ()
  ... | just plan = Effect.preserves (cache-choose-change a s plan unique chosen) eq
    (transport (T.calls (T.front s)) (T.calls (T.front t))
      (Cells.advance-keeps a s unique (selected eq)) (rows (T.base s)) valid)
    where
    selected : T.enact plan s ≡ just t → T.advance a s ≡ just t
    selected enacted rewrite chosen = enacted
  runs-preserve : ∀ {s as t} → T.Runs s as t → Stores.UniqueKeys (T.calls (T.front s)) → Valid s → Valid t
  runs-preserve T.stop unique valid = valid
  runs-preserve (T.more {s = s} {a = a} eq rest) unique valid =
    runs-preserve rest (Cells.advance-unique a s unique eq) (advance-preserves a s unique eq valid)
  initial-valid : ∀ c g {s} → T.initialize c g ≡ just s → Valid s
  initial-valid c g eq with E.initial c
  ... | nothing = case eq of λ ()
  ... | just e = case just-injective eq of λ { refl → [] }
  initialized-cache : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s → Valid s
  initialized-cache {c} {g} initialized path = runs-preserve path (Cells.initial-unique c g initialized) (initial-valid c g initialized)

  -- Join a retained committed-call witness to initialized physical agreement.
  Historical : T.Runtime → PeerConnectionId → HandleId → MuxId → ℕ → RunResult → Set
  Historical s ref h m n result = Σ RunId (λ rid → Σ T.Call (λ r →
    find rid (T.calls (T.front s)) ≡ just r × T.value r ≡ just result ×
    T.peerRef r ≡ ref × T.handleRef r ≡ h × T.mux r ≡ m × number (T.descriptor r) ≡ n ×
    Read.Agreement s rid r result))
  historical : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s →
    ∀ ref h m n result → Back (T.calls (T.front s)) ref h m n result → Historical s ref h m n result
  historical initialized path ref h m n result (rid , r , found , filled , peer , handle , mux , numbered) =
    rid , r , found , filled , peer , handle , mux , numbered ,
    Results.Frontend.initialized-agreement isBearerClosed isIOManagerError canInitiate initialized path rid r result found filled
  stored-back : ∀ xs ref h m n result cell → Stored result cell →
    Pure.Evidence.Cell (Back xs) ref h m n cell → Back xs ref h m n result
  stored-back xs ref h m n result .(Peer.returned result) returned backed = backed
  stored-back xs ref h m n result .(Peer.notRunning result) retired backed = backed
  initialized-actual : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s →
    ∀ ref peer run result → find ref (rows (T.base s)) ≡ just peer → run ∈ Peer.runs peer →
    Stored result (Peer.actual run) → Historical s ref (Peer.handleRef peer) (Peer.muxRef peer) (number (Peer.descriptor run)) result
  initialized-actual {s = s} initialized path ref peer run result found member stored = historical initialized path ref _ _ _ result
    (stored-back (T.calls (T.front s)) ref _ _ _ result (Peer.actual run) stored (proj₁ (All.lookup
      (Pure.Evidence.found-peer (Back (T.calls (T.front s))) ref peer (rows (T.base s)) (initialized-cache initialized path) found) member)))
  initialized-published : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s →
    ∀ ref peer run result → find ref (rows (T.base s)) ≡ just peer → run ∈ Peer.runs peer →
    Stored result (Peer.published run) → Historical s ref (Peer.handleRef peer) (Peer.muxRef peer) (number (Peer.descriptor run)) result
  initialized-published {s = s} initialized path ref peer run result found member stored = historical initialized path ref _ _ _ result
    (stored-back (T.calls (T.front s)) ref _ _ _ result (Peer.published run) stored (proj₂ (All.lookup
      (Pure.Evidence.found-peer (Back (T.calls (T.front s))) ref peer (rows (T.base s)) (initialized-cache initialized path) found) member)))

  -- The new cache invariant closes both constant branches of increment 35.
  -- Supplied peers must be the actual before-state peer, not arbitrary snapshots.
  local-origin : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s →
    ∀ ref peer run result → find ref (rows (T.base s)) ≡ just peer → run ∈ Peer.runs peer →
    Read.Origin ref peer run s (T.localResult result) →
    Historical s ref (Peer.handleRef peer) (Peer.muxRef peer) (number (Peer.descriptor run)) result
  local-origin initialized path ref peer run result found member (Read.cached .result published) =
    initialized-published initialized path ref peer run result found member (subst (Stored result) (sym published) returned)
  local-origin initialized path ref peer run result found member (Read.retired .result published) =
    initialized-published initialized path ref peer run result found member (subst (Stored result) (sym published) retired)
  local-origin initialized path ref peer run result found member (Read.generation rid r selected (Read.committed .result filled agreement)) =
    rid , r , Read.Selection.callFound selected , filled , Read.Selection.samePeer selected ,
    Read.Selection.sameHandle selected , Read.Selection.sameMux selected , Read.Selection.sameNumber selected , agreement
  initialized-pick-local : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s →
    ∀ t ref peer n result → find ref (rows (T.base s)) ≡ just peer → Read.Pick t ref peer s n (T.localResult result) →
    Historical s ref (Peer.handleRef peer) (Peer.muxRef peer) n result
  initialized-pick-local {s = s} initialized path t ref peer n result found witness =
    subst (λ number → Historical s ref (Peer.handleRef peer) (Peer.muxRef peer) number result) (Read.Picked.numbered witness)
      (local-origin initialized path ref peer (Read.Picked.run witness) result found (Read.Picked.member witness) (Read.Picked.origin witness))
