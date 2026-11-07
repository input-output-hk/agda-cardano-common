{-# OPTIONS --guardedness #-}

-- Current physical-result agreement for local cells in initialized executions.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersResults
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (HandleId; WorkerId; JobId; RunId)
open import Data.Nat using (ℕ)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.ServerPeers as Facts
import ConnectionManagement.Properties.MuxProtocolJobs as ResultPhysical
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError
module Physical = ResultPhysical.CommittedRows
jobs : K.State → _
jobs = Facts.CommittedRows.jobs isBearerClosed isIOManagerError
step-stable : ∀ a s {t} → K.step a s ≡ just t → Physical.Retains (jobs s) (jobs t)
step-stable = Facts.CommittedRows.step-stable isBearerClosed isIOManagerError

module Frontend (canInitiate : HandleId → ℕ → Bool) where
  open import ConnectionManagement.Store using (lookup; put; Store)
  open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
  open import ConnectionManagement.IGTypes using (RunResult; clean; errored; number)
  open import ConnectionManagement.Properties.Entries using (lookup-put)
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
  import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
  import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
  import ConnectionManagement.Properties.MuxStartupUnwind as RawFacts
  import ConnectionManagement.Properties.MuxProtocolJobs as PhysicalFacts
  private
    module T = K.Protocols canInitiate
    module N = Publication isBearerClosed
    module Catch = N.C
    module D = N.D
    module R = N.R
    module X = D.X
    module W = N.W
    module G = N.G
    module M = N.M
    module Jobs = N.P
  monitor-lower : ∀ a s {t} → M.step (M.run a) s ≡ just t → Jobs.step a (M.base s) ≡ just (M.base t)
  monitor-lower a s eq with M.delegateAllowed a s
  ... | false = case eq of λ ()
  ... | true with Jobs.step a (M.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just p = case just-injective eq of λ { refl → refl }
  group-lower : ∀ a s {t} → G.step (G.run (M.run a)) s ≡ just t → Jobs.step a (G.protocolState s) ≡ just (G.protocolState t)
  group-lower a s eq with G.delegateAllowed (M.run a) s
  ... | false = case eq of λ ()
  ... | true with M.step (M.run a) (G.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just m = case just-injective eq of λ { refl → monitor-lower a (G.base s) advanced }
  handler-lower : ∀ a s {t} → W.step (W.run (G.run (M.run a))) s ≡ just t →
    Jobs.step a (G.protocolState (W.base s)) ≡ just (G.protocolState (W.base t))
  handler-lower a s eq with W.delegateAllowed (G.run (M.run a))
  ... | false = case eq of λ ()
  ... | true with G.step (G.run (M.run a)) (W.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just g = case just-injective eq of λ { refl → group-lower a (W.base s) advanced }
  raw-lower : ∀ a s {t} → R.step (D.wrapMonitor (M.run a)) s ≡ just t → Jobs.step a (R.protocols s) ≡ just (R.protocols t)
  raw-lower a s eq with RawFacts.inherited-observation isBearerClosed (X.run (W.run (G.run (M.run a)))) s eq
  ... | x , advanced , refl = handler-lower a (R.base s) advanced
  delta-lower : ∀ a s {t} → D.step (D.run (D.wrapMonitor (M.run a))) s ≡ just t →
    Jobs.step a (R.protocols (D.base s)) ≡ just (R.protocols (D.base t))
  delta-lower a s eq with DeltaFacts.inherited-observation isBearerClosed (D.wrapMonitor (M.run a)) s eq
  ... | r , advanced , refl = raw-lower a (D.base s) advanced
  catch-lower : ∀ a s {t} → Catch.step (Catch.run (D.run (D.wrapMonitor (M.run a)))) s ≡ just t →
    Jobs.step a (R.protocols (D.base (Catch.base s))) ≡ just (R.protocols (D.base (Catch.base t)))
  catch-lower a s eq with CatchFacts.inherited-observation isBearerClosed (D.run (D.wrapMonitor (M.run a))) s eq
  ... | d , advanced , refl = delta-lower a (Catch.base s) advanced
  lowerAction : Jobs.Action → N.Action
  lowerAction a = N.run (Catch.run (D.run (D.wrapMonitor (M.run a))))
  publication-lower : ∀ a s {t} → N.step (lowerAction a) s ≡ just t → Jobs.step a (R.protocols (N.raw s)) ≡ just (R.protocols (N.raw t))
  publication-lower a s eq with PublicationFacts.inherited-observation isBearerClosed (Catch.run (D.run (D.wrapMonitor (M.run a)))) s eq
  ... | c , advanced , refl = catch-lower a (N.base s) advanced
  server-lower : ∀ a s {t} → S.step (S.run (lowerAction a)) s ≡ just t →
    Jobs.step a (R.protocols (N.raw (S.base s))) ≡ just (R.protocols (N.raw (S.base t)))
  server-lower a s eq with S.allowed (lowerAction a) s
  ... | false = case eq of λ ()
  ... | true with N.step (lowerAction a) (S.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just n = case just-injective eq of λ { refl → publication-lower a (S.base s) advanced }
  ig-lower : ∀ a s {t} → E.step (E.run (S.run (lowerAction a))) s ≡ just t →
    Jobs.step a (R.protocols (N.raw (S.base (E.base s)))) ≡ just (R.protocols (N.raw (S.base (E.base t))))
  ig-lower a s eq with E.runAllowed (S.run (lowerAction a)) s
  ... | false = case eq of λ ()
  ... | true with S.step (S.run (lowerAction a)) (E.base s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just server = case just-injective eq of λ { refl → server-lower a (E.base s) advanced }
  physical-lower : ∀ a s {t} → K.step (T.physicalAction a) s ≡ just t → Jobs.step a (T.physical s) ≡ just (T.physical t)
  physical-lower a s eq with K.serverAllowed (E.run (S.run (lowerAction a))) s
  ... | false = case eq of λ ()
  ... | true with E.step (E.run (S.run (lowerAction a))) (K.server s) in advanced
  ...   | nothing = case eq of λ ()
  ...   | just e = case just-injective eq of λ { refl → ig-lower a (K.server s) advanced }

  open import Class.DecEq using (_≟_)
  open import Relation.Nullary using (yes; no)
  open import Data.Product using (proj₁; proj₂)
  import ConnectionManagement.Properties.Stores as Stores
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.Rules.CMShutdown as Close
  import Data.Nat as Nat
  private
    module Cells = Facts.Protocols.CommittedCells isBearerClosed isIOManagerError canInitiate
    module Identity = Facts.CaptureIdentity.Frontend isBearerClosed isIOManagerError canInitiate
    module Pool = Jobs.Pool
  -- Every committed cell has a real handle and its same physical result.
  Backed : T.Call → RunResult → Store JobId Types.ProtocolJob → Set
  Backed r result rows = Σ JobId (λ j → T.thread r ≡ just j ×
    Σ Types.ProtocolJob (λ job → lookup j rows ≡ just job × Types.phase job ≡ Types.resultCaptured result))
  Sound : Store RunId T.Call → Store JobId Types.ProtocolJob → Set
  Sound calls rows = ∀ rid r result → lookup rid calls ≡ just r → T.value r ≡ just result → Backed r result rows
  Valid : T.Runtime → Set
  Valid s = Sound (T.calls (T.front s)) (jobs (T.base s))
  transport : ∀ calls {before after} → Physical.Retains before after → Sound calls before → Sound calls after
  transport calls retained valid rid r result found filled with valid rid r result found filled
  ... | j , threaded , job , seen , phase = j , threaded , job , retained j job result seen phase , phase
  put-sound : ∀ rid r calls rows → Sound calls rows →
    (∀ result → T.value r ≡ just result → Backed r result rows) → Sound (put rid r calls) rows
  put-sound rid r calls rows valid new q observed result found filled with q ≟ rid
  ... | yes refl with just-injective (trans (sym (lookup-put rid r calls)) found)
  ...   | refl = new result filled
  put-sound rid r calls rows valid new q observed result found filled | no apart = valid q observed result
    (trans (sym (Stores.lookup-put-other rid q r calls apart)) found) filled
  cons-sound : ∀ rid r calls rows → T.value r ≡ nothing → Sound calls rows → Sound ((rid , r) ∷ calls) rows
  cons-sound rid r calls rows empty valid q observed result found filled with q ≟ rid
  ... | no _ = valid q observed result found filled
  ... | yes _ with just-injective found
  ...   | refl with trans (sym empty) filled
  ...     | ()
  birth-sound : ∀ w j rid r calls rows → T.value r ≡ nothing → lookup j rows ≡ nothing → Sound calls rows →
    Sound (put rid (record r { thread = just j }) calls)
      (put j (Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing) rows)
  birth-sound w j rid r calls rows empty fresh valid = put-sound rid _ calls (put j born rows)
    (transport calls {before = rows} {after = put j born rows} (Physical.fresh-put j born rows fresh) valid)
    (λ result filled → case trans (sym empty) filled of λ ())
    where
    born = Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing
  fork-preserves : ∀ w j s {t} → T.advance (T.forkStart w j) s ≡ just t → Valid s → Valid t
  fork-preserves w j s eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    lookup w (Jobs.U.frames (Jobs.base (T.physical (T.base s))))
  ... | T.forkReadyC rid | true | just capturedFrame with lookup rid (T.calls (T.front s)) |
    Jobs.fresh j rid (T.physical (T.base s)) in fresh | Jobs.noParent (Jobs.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (Jobs.poolAt w (T.physical (T.base s))) in forked
  ...     | yes owner | nothing | nothing | just pool = case just-injective eq of λ { refl →
    birth-sound w j rid r (T.calls (T.front s)) (jobs (T.base s)) empty
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
  allocation-proof : ∀ a f rid r s → T.calls f ≡ (rid , r) ∷ T.calls (T.front s) → T.value r ≡ nothing → ∀ {t} → T.enact (T.caller a f) s ≡ just t → Valid s → Valid t
  allocation-proof a f rid r s same empty eq valid with PS.step a (K.peers (T.base s))
  ... | nothing = case eq of λ ()
  ... | just peer = case just-injective eq of λ { refl → subst (λ xs → Sound xs (jobs (T.base s))) (sym same)
    (cons-sound rid r (T.calls (T.front s)) (jobs (T.base s)) empty valid) }

  allocation : ∀ a f rid r s → T.calls f ≡ (rid , r) ∷ T.calls (T.front s) → T.value r ≡ nothing → Effect s (T.caller a f)
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
  commitAction : JobId → RunResult → Jobs.Action
  commitAction j clean = Jobs.commitClean j
  commitAction j (errored err) = Jobs.protocolException j err
  commit-observation : ∀ j result b {next} → K.step (T.physicalAction (commitAction j result)) b ≡ just next →
    PhysicalFacts.CompletionCommit j (T.physical b) (T.physical next)
  commit-observation j clean b eq = PhysicalFacts.clean-observation j (T.physical b) (physical-lower (Jobs.commitClean j) b eq)
  commit-observation j (errored err) b eq = PhysicalFacts.exception-observation j err (T.physical b) (physical-lower (Jobs.protocolException j err) b eq)
  capture-phase : ∀ j job result p {next} → Jobs.capture j job result p ≡ just next →
    Σ Types.ProtocolJob (λ row → lookup j (Jobs.jobs next) ≡ just row × Types.phase row ≡ Types.resultCaptured result)
  capture-phase j job result p eq with lookup (Types.owner job) (Jobs.U.frames (Jobs.base p)) |
    lookup j (Pool.handles (Jobs.poolAt (Types.owner job) p))
  ... | just f | just Pool.bodyRunning with Jobs.bodySource job result p
  ...   | nothing = case eq of λ ()
  ...   | just c = case just-injective eq of λ { refl → new ,
    trans (cong (lookup j) (Physical.pending-jobs job j (record (Jobs.setSource c p) { jobs = put j new (Jobs.jobs p) })))
      (lookup-put j new (Jobs.jobs p)) , refl }
    where new = record job { phase = Types.resultCaptured result }
  capture-phase j job result p eq | nothing | _ = case eq of λ ()
  capture-phase j job result p eq | just _ | nothing = case eq of λ ()
  capture-phase j job result p eq | just _ | just (Pool.bodyReturned _) = case eq of λ ()
  capture-phase j job result p eq | just _ | just Pool.bodyUnwinding = case eq of λ ()
  capture-phase j job result p eq | just _ | just (Pool.deregisterPending _) = case eq of λ ()
  capture-phase j job result p eq | just _ | just (Pool.deregistered _) = case eq of λ ()
  capture-phase j job result p eq | just _ | just (Pool.resultAvailable _) = case eq of λ ()
  physical-phase : ∀ j result p {next} → Jobs.step (commitAction j result) p ≡ just next →
    Σ Types.ProtocolJob (λ row → lookup j (Jobs.jobs next) ≡ just row × Types.phase row ≡ Types.resultCaptured result)
  physical-phase j clean p eq with lookup j (Jobs.jobs p)
  ... | nothing = case eq of λ ()
  ... | just job with Types.phase job
  ...   | Types.waitingEgress with Jobs.cleanReady j job p
  ...     | false = case eq of λ ()
  ...     | true = capture-phase j job clean p eq
  physical-phase j clean p eq | just job | Types.executing = case eq of λ ()
  physical-phase j clean p eq | just job | Types.resultCaptured _ = case eq of λ ()
  physical-phase j (errored err) p eq with lookup j (Jobs.jobs p)
  ... | nothing = case eq of λ ()
  ... | just job with Jobs.canCapture (Types.phase job)
  ...   | false = case eq of λ ()
  ...   | true = capture-phase j job (errored err) p eq
  commit-phase : ∀ j result b {next} → K.step (T.physicalAction (commitAction j result)) b ≡ just next →
    Σ Types.ProtocolJob (λ row → lookup j (jobs next) ≡ just row × Types.phase row ≡ Types.resultCaptured result)
  commit-phase j result b eq = physical-phase j result (T.physical b) (physical-lower (commitAction j result) b eq)
  completion-proof : ∀ j rid r result s → T.thread r ≡ just j →
    ∀ {t} → T.enact (T.complete (T.physicalAction (commitAction j result)) rid r result) s ≡ just t → Valid s → Valid t
  completion-proof j rid r result s threaded eq valid with K.step (T.physicalAction (commitAction j result)) (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b with commit-phase j result (T.base s) advanced
  ...   | row , found , phase = case just-injective eq of λ { refl → subst (Sound (put rid (record r { value = just result }) (T.calls (T.front s))))
    (sym (cache-jobs rid r result (T.front s) b))
    (put-sound rid (record r { value = just result }) (T.calls (T.front s)) (jobs b)
      (transport (T.calls (T.front s)) {before = jobs (T.base s)} {after = jobs b} (step-stable (T.physicalAction (commitAction j result)) (T.base s) advanced) valid)
      (λ observed equal → case just-injective equal of λ { refl → j , threaded , row , found , phase })) }
  completion : ∀ j rid r result s → T.thread r ≡ just j → Effect s (T.complete (T.physicalAction (commitAction j result)) rid r result)
  completion j rid r result s threaded = effect (completion-proof j rid r result s threaded)
  by-thread-ref : ∀ j calls rid r → T.byThread j calls ≡ just (rid , r) → T.thread r ≡ just j
  by-thread-ref j [] rid r eq = case eq of λ ()
  by-thread-ref j ((q , head) ∷ rest) rid r eq with T.thread head in threaded
  ... | nothing = by-thread-ref j rest rid r eq
  ... | just actual with j ≟ actual
  ...   | no _ = by-thread-ref j rest rid r eq
  ...   | yes refl = case just-injective eq of λ { refl → threaded }
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
  capture-completion-change j clean s p unique eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    completion j rid r clean s (by-thread-ref j (T.calls (T.front s)) rid r found) }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  capture-completion-change j clean s p unique eq | nothing | _ = case eq of λ ()
  capture-completion-change j clean s p unique eq | just pair | nothing = case eq of λ ()

  capture-completion-change j (errored commitErr) s p unique eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (Jobs.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
    completion j rid r (errored commitErr) s (by-thread-ref j (T.calls (T.front s)) rid r found) }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  capture-completion-change j (errored commitErr) s p unique eq | nothing | _ = case eq of λ ()
  capture-completion-change j (errored commitErr) s p unique eq | just pair | nothing = case eq of λ ()

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


  -- Join the independent identity and result invariants at the current row.
  initialized-agreement : ∀ {c g start as t} → T.initialize c g ≡ just start → T.Runs start as t →
    ∀ rid r result → lookup rid (T.calls (T.front t)) ≡ just r → T.value r ≡ just result →
    Σ JobId (λ j → T.thread r ≡ just j × Σ Types.ProtocolJob (λ job →
      lookup j (jobs (T.base t)) ≡ just job × Identity.Match rid r job × Types.phase job ≡ Types.resultCaptured result))
  initialized-agreement initialized path rid r result found filled with initialized-soundness initialized path rid r result found filled
  ... | j , threaded , job , seen , captured with Identity.initialized-soundness initialized path rid r j found threaded
  ...   | identified , located , matches with just-injective (trans (sym seen) located)
  ...     | refl = j , threaded , job , seen , matches , captured

-- Reader provenance keeps constant published actions separate from live cells.
-- A live local result has its exact generation's physical capture; Shutdown
-- instead certifies an empty local cell and the actual non-ready mux status.
module Observations (canInitiate : HandleId → ℕ → Bool) where
  open import ConnectionManagement.Domain using (PeerConnectionId)
  open import ConnectionManagement.Store using (Store; lookup)
  open import ConnectionManagement.IGTypes using (RunResult; Temperature; hot; warm; established; number)
  open import Data.List using (List; _++_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)
  open import Data.List.Relation.Unary.All as All using (All)
  import Data.List.Relation.Unary.All.Properties as AllFacts
  import Data.List.Relation.Unary.AllPairs as Pairs
  open import Data.Unit using (⊤; tt)
  open import Data.Sum using (_⊎_; inj₁; inj₂)
  open import Relation.Nullary using (yes; no; does)
  open import Class.DecEq using (_≟_)
  open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
  import Data.Nat as Nat
  import ConnectionManagement.Properties.Stores as Stores
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Rules.Pruning as Pruning
  import ConnectionManagement.MuxPublicationUnwind as Publication
  private
    module T = K.Protocols canInitiate
    module N = Publication isBearerClosed
    module P = N.P
    module U = N.U
    module Cells = Facts.Protocols.CommittedCells isBearerClosed isIOManagerError canInitiate

  -- The initializer and enabled prefix derive both premises of live reads.
  Agreement : T.Runtime → RunId → T.Call → RunResult → Set
  Agreement s rid r result = Σ JobId (λ j → T.thread r ≡ just j ×
    Σ Types.ProtocolJob (λ job → lookup j (jobs (T.base s)) ≡ just job ×
      ResultPhysical.CaptureIdentity.keyOf job ≡ ResultPhysical.CaptureIdentity.key
        (T.owner r) (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid ×
      Types.phase job ≡ Types.resultCaptured result))
  record Readable (s : T.Runtime) : Set where
    constructor readable
    field unique : Stores.UniqueKeys (T.calls (T.front s))
          sound : ∀ rid r result → lookup rid (T.calls (T.front s)) ≡ just r →
            T.value r ≡ just result → Agreement s rid r result
  initialized-readable : ∀ {c g start as s} → T.initialize c g ≡ just start → T.Runs start as s → Readable s
  initialized-readable {c} {g} initialized path = readable
    (Cells.run-unique path (Cells.initial-unique c g initialized))
    (Frontend.initialized-agreement canInitiate initialized path)

  -- latest searches by owner/number, whereas observation uses the selected key.
  latest-info : ∀ w n (xs : Store RunId T.Call) rid r → Stores.UniqueKeys xs →
    T.latest w n xs ≡ just (rid , r) →
    lookup rid xs ≡ just r × T.owner r ≡ w × number (T.descriptor r) ≡ n
  latest-info w n [] rid r unique eq = case eq of λ ()
  latest-info w n ((q , head) ∷ xs) rid r (apart Pairs.∷ unique) eq
    with w ≟ T.owner head | n Nat.≟ number (T.descriptor head)
  ... | yes owned | yes numbered = case just-injective eq of λ { refl →
    Stores.lookup-head q head xs , sym owned , sym numbered }
  ... | yes _ | no _ with latest-info w n xs rid r unique eq
  ...   | found , owned , numbered = Cells.tail-lookup rid r q head xs (apart Pairs.∷ unique) found , owned , numbered
  latest-info w n ((q , head) ∷ xs) rid r (apart Pairs.∷ unique) eq | no _ | _
    with latest-info w n xs rid r unique eq
  ... | found , owned , numbered = Cells.tail-lookup rid r q head xs (apart Pairs.∷ unique) found , owned , numbered

  data NonReady : Mux.Status → Set where
    stopping : NonReady Mux.stopping
    stopped : NonReady Mux.stopped
    failed : ∀ err → NonReady (Mux.failed err)
  record Fallback (s : T.Runtime) (r : T.Call) (status : Mux.Status) : Set where
    constructor fallback
    field empty : T.value r ≡ nothing
          actualMux : Mux.Mux
          foundMux : P.muxAt (T.mux r) (T.physical (T.base s)) ≡ just actualMux
          actualStatus : Mux.status actualMux ≡ status
          nonReady : NonReady status
  data Outcome (s : T.Runtime) (rid : RunId) (r : T.Call) : T.Observation → Set where
    committed : ∀ result → T.value r ≡ just result → Agreement s rid r result → Outcome s rid r (T.localResult result)
    shutdown : ∀ status → Fallback s r status → Outcome s rid r (T.shutdownResult status)
  observe-proof : ∀ rid r s observation → Readable s → lookup rid (T.calls (T.front s)) ≡ just r →
    T.observe rid s ≡ just observation → Outcome s rid r observation
  observe-proof rid r s observation valid found eq rewrite found with T.value r in filled
  ... | just result = case just-injective eq of λ { refl → committed result filled (Readable.sound valid rid r result found filled) }
  ... | nothing with P.muxAt (T.mux r) (T.physical (T.base s)) in located
  ...   | nothing = case eq of λ ()
  ...   | just m with Mux.status m in status
  ...     | Mux.ready = case eq of λ ()
  ...     | Mux.stopping = case just-injective eq of λ { refl → shutdown _ (fallback filled m located status stopping) }
  ...     | Mux.stopped = case just-injective eq of λ { refl → shutdown _ (fallback filled m located status stopped) }
  ...     | Mux.failed err = case just-injective eq of λ { refl → shutdown _ (fallback filled m located status (failed err)) }

  record Selection (ref : PeerConnectionId) (peer : Peer.Peer) (run : Peer.ProtocolRun)
    (s : T.Runtime) (rid : RunId) (r : T.Call) : Set where
    constructor selection
    field controller : WorkerId
          published : Peer.published run ≡ Peer.running
          ownerFound : T.ownerFor peer (U.frames (P.base (T.physical (T.base s)))) ≡ just controller
          latestFound : T.latest controller (number (Peer.descriptor run)) (T.calls (T.front s)) ≡ just (rid , r)
          callFound : lookup rid (T.calls (T.front s)) ≡ just r
          sameOwner : T.owner r ≡ controller
          sameNumber : number (T.descriptor r) ≡ number (Peer.descriptor run)
          samePeer : T.peerRef r ≡ ref
          sameHandle : T.handleRef r ≡ Peer.handleRef peer
          sameMux : T.mux r ≡ Peer.muxRef peer
  data Origin (ref : PeerConnectionId) (peer : Peer.Peer) (run : Peer.ProtocolRun) (s : T.Runtime) : T.Observation → Set where
    cached : ∀ result → Peer.published run ≡ Peer.returned result → Origin ref peer run s (T.localResult result)
    retired : ∀ result → Peer.published run ≡ Peer.notRunning result → Origin ref peer run s (T.localResult result)
    generation : ∀ rid r {observation} → Selection ref peer run s rid r → Outcome s rid r observation → Origin ref peer run s observation
  Certificate : ∀ ref peer run s → T.ReadCell → Set
  Certificate ref peer run s T.never = Peer.published run ≡ Peer.notStarted
  Certificate ref peer run s (T.retired result) = Peer.published run ≡ Peer.notRunning result
  Certificate ref peer run s T.blocked = ⊤
  Certificate ref peer run s (T.available observation) = Origin ref peer run s observation
  published-certificate : ∀ ref peer run s → Readable s → Certificate ref peer run s (T.publishedCell ref peer run s)
  published-certificate ref peer run s valid with Peer.published run in published
  ... | Peer.notStarted = published
  ... | Peer.notRunning result = published
  ... | Peer.returned result = cached result published
  ... | Peer.running with T.ownerFor peer (U.frames (P.base (T.physical (T.base s)))) in owner
  ...   | nothing = tt
  ...   | just w with T.latest w (number (Peer.descriptor run)) (T.calls (T.front s)) in latest
  ...     | nothing = tt
  ...     | just (rid , r) with T.peerRef r ≟ ref | T.handleRef r ≟ Peer.handleRef peer | T.mux r ≟ Peer.muxRef peer
  ...       | yes samePeer | yes sameHandle | yes sameMux with T.observe rid s in observed
  ...         | nothing = tt
  ...         | just observation with latest-info w (number (Peer.descriptor run)) (T.calls (T.front s)) rid r (Readable.unique valid) latest
  ...           | found , sameOwner , sameNumber = generation rid r
    (selection w published owner latest found sameOwner sameNumber samePeer sameHandle sameMux)
    (observe-proof rid r s observation valid found observed)
  published-certificate ref peer run s valid | Peer.running | just w | just (rid , r) | yes _ | yes _ | no _ = tt
  published-certificate ref peer run s valid | Peer.running | just w | just (rid , r) | yes _ | no _ | _ = tt
  published-certificate ref peer run s valid | Peer.running | just w | just (rid , r) | no _ | _ | _ = tt
  available-origin : ∀ ref peer run s observation → Readable s →
    T.publishedCell ref peer run s ≡ T.available observation → Origin ref peer run s observation
  available-origin ref peer run s observation valid eq = subst (Certificate ref peer run s) eq (published-certificate ref peer run s valid)
  retired-origin : ∀ ref peer run s result → Readable s →
    T.publishedCell ref peer run s ≡ T.retired result → Origin ref peer run s (T.localResult result)
  retired-origin ref peer run s result valid eq = retired result
    (subst (Certificate ref peer run s) eq (published-certificate ref peer run s valid))

  -- Every returned pair names an actual run in the selected temperature bundle.
  record Picked (t : Temperature) (ref : PeerConnectionId) (peer : Peer.Peer)
    (runs : List Peer.ProtocolRun) (s : T.Runtime) (n : ℕ) (observation : T.Observation) : Set where
    constructor picked
    field run : Peer.ProtocolRun
          member : run ∈ runs
          belongs : Peer.belongs t run ≡ true
          numbered : number (Peer.descriptor run) ≡ n
          origin : Origin ref peer run s observation
  lift-picked : ∀ {t ref peer xs ys s n observation} → (∀ {run} → run ∈ xs → run ∈ ys) →
    Picked t ref peer xs s n observation → Picked t ref peer ys s n observation
  lift-picked lift (picked run member belongs numbered origin) = picked run (lift member) belongs numbered origin
  first-cells : ∀ t ref peer runs s n observation → Readable s →
    T.firstCells t ref peer runs s ≡ just (n , observation) → Picked t ref peer runs s n observation
  first-cells t ref peer [] s n observation valid eq = case eq of λ ()
  first-cells t ref peer (run ∷ runs) s n observation valid eq with Peer.belongs t run in belongs
  ... | false = lift-picked there (first-cells t ref peer runs s n observation valid eq)
  ... | true with T.publishedCell ref peer run s in cell
  ...   | T.never = case eq of λ ()
  ...   | T.retired _ = case eq of λ ()
  ...   | T.blocked = lift-picked there (first-cells t ref peer runs s n observation valid eq)
  ...   | T.available result = case just-injective eq of λ { refl →
    picked run (here refl) belongs refl (available-origin ref peer run s result valid cell) }
  all-cells : ∀ t ref peer runs s results → Readable s → T.allCells t ref peer runs s ≡ just results →
    All (λ { (n , observation) → Picked t ref peer runs s n observation }) results
  all-cells t ref peer [] s results valid eq = case just-injective eq of λ { refl → All.[] }
  all-cells t ref peer (run ∷ runs) s results valid eq with Peer.belongs t run in belongs
  ... | false = All.map (lift-picked there) (all-cells t ref peer runs s results valid eq)
  ... | true with T.publishedCell ref peer run s in cell | T.allCells t ref peer runs s in tail
  ...   | T.never | rest = All.map (lift-picked there) (all-cells t ref peer runs s results valid (trans tail eq))
  ...   | T.retired result | just rest = case just-injective eq of λ { refl →
    picked run (here refl) belongs refl (retired-origin ref peer run s result valid cell) All.∷
    All.map (lift-picked there) (all-cells t ref peer runs s rest valid tail) }
  ...   | T.available result | just rest = case just-injective eq of λ { refl →
    picked run (here refl) belongs refl (available-origin ref peer run s result valid cell) All.∷
    All.map (lift-picked there) (all-cells t ref peer runs s rest valid tail) }
  ...   | T.retired _ | nothing = case eq of λ ()
  ...   | T.available _ | nothing = case eq of λ ()
  ...   | T.blocked | _ = case eq of λ ()

  -- The local insertion sort changes order, never the provenance of a run.
  insert-member : ∀ {A : Set} less (x : A) xs {r} → r ∈ Pruning.insertBy less x xs → r ≡ x ⊎ r ∈ xs
  insert-member less x [] (here eq) = inj₁ eq
  insert-member less x [] (there ())
  insert-member less x (y ∷ ys) member with less y x
  ... | false with member
  ...   | here eq = inj₁ eq
  ...   | there rest = inj₂ rest
  insert-member less x (y ∷ ys) member | true with member
  ... | here eq = inj₂ (here eq)
  ... | there rest with insert-member less x ys rest
  ...   | inj₁ eq = inj₁ eq
  ...   | inj₂ found = inj₂ (there found)
  sort-member : ∀ {A : Set} less (xs : List A) {r} → r ∈ Pruning.sortBy less xs → r ∈ xs
  sort-member less [] ()
  sort-member less (x ∷ xs) member with insert-member less x (Pruning.sortBy less xs) member
  ... | inj₁ eq = here eq
  ... | inj₂ found = there (sort-member less xs found)
  by-number : Peer.ProtocolRun → Peer.ProtocolRun → Bool
  by-number a b = does (Nat._<?_ (number (Peer.descriptor a)) (number (Peer.descriptor b)))
  ordered : Peer.Peer → List Peer.ProtocolRun
  ordered peer = Pruning.sortBy by-number (Peer.runs peer)
  Pick : Temperature → PeerConnectionId → Peer.Peer → T.Runtime → ℕ → T.Observation → Set
  Pick t ref peer s = Picked t ref peer (Peer.runs peer) s
  first-proof : ∀ t ref peer s n observation → Readable s →
    T.firstPublished t ref peer s ≡ just (n , observation) → Pick t ref peer s n observation
  first-proof t ref peer s n observation valid eq = lift-picked (sort-member by-number (Peer.runs peer))
    (first-cells t ref peer (ordered peer) s n observation valid eq)
  all-proof : ∀ t ref peer s results → Readable s → T.allPublished t ref peer s ≡ just results →
    All (λ { (n , observation) → Pick t ref peer s n observation }) results
  all-proof t ref peer s results valid eq = All.map (lift-picked (sort-member by-number (Peer.runs peer)))
    (all-cells t ref peer (ordered peer) s results valid eq)
  AnyPick : PeerConnectionId → Peer.Peer → T.Runtime → ℕ → T.Observation → Set
  AnyPick ref peer s n observation = Σ Temperature (λ t → Pick t ref peer s n observation)
  peer-proof : ∀ ref peer s kind observation → Readable s → T.firstPeer ref peer s ≡ just (kind , observation) →
    Σ ℕ (λ n → AnyPick ref peer s n observation)
  peer-proof ref peer s kind observation valid eq with T.firstPublished established ref peer s in chosen
  ... | just (n , result) = case just-injective eq of λ { refl → n , established , first-proof established ref peer s n result valid chosen }
  ... | nothing with T.firstPublished warm ref peer s in chosen
  ...   | just (n , result) = case just-injective eq of λ { refl → n , warm , first-proof warm ref peer s n result valid chosen }
  ...   | nothing with T.firstPublished hot ref peer s in chosen
  ...     | just (n , result) = case just-injective eq of λ { refl → n , hot , first-proof hot ref peer s n result valid chosen }
  ...     | nothing = case eq of λ ()
  wait-proof : ∀ f peer s results → Readable s → T.waitResults f peer s ≡ just results →
    All (λ { (n , observation) → AnyPick (J.connectionRef f) peer s n observation }) results
  wait-proof f peer s results valid eq with J.pc f
  ... | J.awaitHot = All.map (λ picked → hot , picked) (all-proof hot (J.connectionRef f) peer s results valid eq)
  ... | J.awaitAll with T.allPublished hot (J.connectionRef f) peer s in hs |
    T.allPublished warm (J.connectionRef f) peer s in ws | T.allPublished established (J.connectionRef f) peer s in es
  ...   | just h | just w | just e = case just-injective eq of λ { refl → AllFacts.++⁺
    (All.map (λ picked → hot , picked) (all-proof hot (J.connectionRef f) peer s h valid hs))
    (AllFacts.++⁺ (All.map (λ picked → warm , picked) (all-proof warm (J.connectionRef f) peer s w valid ws))
      (All.map (λ picked → established , picked) (all-proof established (J.connectionRef f) peer s e valid es))) }
  ...   | nothing | _ | _ = case eq of λ ()
  ...   | just _ | nothing | _ = case eq of λ ()
  ...   | just _ | just _ | nothing = case eq of λ ()
  wait-proof f peer s results valid eq | J.begin = case eq of λ ()
  wait-proof f peer s results valid eq | J.awaitAcquire = case eq of λ ()
  wait-proof f peer s results valid eq | J.startBundle _ _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.publishBundle _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.markWarm = case eq of λ ()
  wait-proof f peer s results valid eq | J.forkMonitor = case eq of λ ()
  wait-proof f peer s results valid eq | J.finishActivation = case eq of λ ()
  wait-proof f peer s results valid eq | J.callRelease = case eq of λ ()
  wait-proof f peer s results valid eq | J.awaitRelease = case eq of λ ()
  wait-proof f peer s results valid eq | J.delayFailure = case eq of λ ()
  wait-proof f peer s results valid eq | J.awaitCold _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.complete _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.acquirePolicy _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.nodeDelivery _ = case eq of λ ()
  wait-proof f peer s results valid eq | J.nodeRethrow _ = case eq of λ ()

  import ConnectionManagement.Subsystem as Sub
  peerRows : T.Runtime → Peer.Runtime
  peerRows s = C.SubContext.peers (C.subsystem (K.context (T.base s)))
  monitorRows : T.Runtime → Store PeerConnectionId J.Frame
  monitorRows s = C.SubContext.monitors (C.subsystem (K.context (T.base s)))
  jobRows : T.Runtime → Store JobId Sub.JobFrame
  jobRows s = C.SubContext.jobs (C.subsystem (K.context (T.base s)))

  -- Cold/demotion and existing-followup polls do not select a new result.
  data PollSource (ref : PeerConnectionId) (peer : Peer.Peer) (s : T.Runtime) : Set where
    cold : Peer.status peer ≡ Peer.peerCold → PollSource ref peer s
    cooling : Peer.status peer ≡ Peer.peerCooling → PollSource ref peer s
    following : ∀ f → lookup ref (monitorRows s) ≡ just f → PollSource ref peer s
    observed : ∀ kind observation → lookup ref (monitorRows s) ≡ nothing →
      T.firstPeer ref peer s ≡ just (kind , observation) →
      Σ ℕ (λ n → AnyPick ref peer s n observation) → PollSource ref peer s
  record PollRead (ref : PeerConnectionId) (w : WorkerId) (s : T.Runtime) : Set where
    constructor pollRead
    field peer : Peer.Peer
          foundPeer : lookup ref (peerRows s) ≡ just peer
          allowed : T.readAllowed (Sub.pollPeer ref w) (T.base s) ≡ true
          source : PollSource ref peer s
  poll-plan-proof : ∀ ref w s plan → Readable s → T.pollResultsPlan ref w s ≡ just plan → PollRead ref w s
  poll-plan-proof ref w s plan valid eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) in allowed |
    lookup ref (peerRows s) in found | lookup ref (monitorRows s) in monitor
  ... | true | just peer | nothing with Peer.status peer in status
  ...   | Peer.peerCold = pollRead peer found allowed (cold status)
  ...   | Peer.peerCooling = pollRead peer found allowed (cooling status)
  ...   | Peer.peerWarm with T.firstPeer ref peer s in selected
  ...     | nothing = case eq of λ ()
  ...     | just (kind , observation) = pollRead peer found allowed
    (observed kind observation monitor selected (peer-proof ref peer s kind observation valid selected))
  poll-plan-proof ref w s plan valid eq | true | just peer | nothing | Peer.peerHot
    with T.firstPeer ref peer s in selected
  ... | nothing = case eq of λ ()
  ... | just (kind , observation) = pollRead peer found allowed
    (observed kind observation monitor selected (peer-proof ref peer s kind observation valid selected))
  poll-plan-proof ref w s plan valid eq | true | just peer | just f = pollRead peer found allowed (following f monitor)
  poll-plan-proof ref w s plan valid eq | false | _ | _ = case eq of λ ()
  poll-plan-proof ref w s plan valid eq | true | nothing | _ = case eq of λ ()

  -- Both successful and failed continuations consume the same certified read.
  record JobRead (j : JobId) (s : T.Runtime) : Set where
    constructor jobRead
    field frame : Sub.JobFrame
          foundJob : lookup j (jobRows s) ≡ just frame
          notQueued : Sub.queued frame ≡ false
          peer : Peer.Peer
          foundPeer : lookup (J.connectionRef (Sub.execution frame)) (peerRows s) ≡ just peer
          allowed : T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution frame))) (T.base s) ≡ true
          results : List (ℕ × T.Observation)
          selected : T.waitResults (Sub.execution frame) peer s ≡ just results
          provenance : All (λ { (n , observation) → AnyPick (J.connectionRef (Sub.execution frame)) peer s n observation }) results
  job-plan-proof : ∀ j s plan → Readable s → T.waitJobPlan j s ≡ just plan → JobRead j s
  job-plan-proof j s plan valid eq with lookup j (jobRows s) in foundJob
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf in queued | lookup (J.connectionRef (Sub.execution jf)) (peerRows s) in foundPeer |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s) in allowed
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s in selected
  ...     | nothing = case eq of λ ()
  ...     | just results = jobRead jf foundJob queued peer foundPeer allowed results selected
    (wait-proof (Sub.execution jf) peer s results valid selected)
  job-plan-proof j s plan valid eq | just jf | true | _ | _ = case eq of λ ()
  job-plan-proof j s plan valid eq | just jf | false | nothing | _ = case eq of λ ()
  job-plan-proof j s plan valid eq | just jf | false | just _ | false = case eq of λ ()
  record MonitorRead (ref : PeerConnectionId) (s : T.Runtime) : Set where
    constructor monitorRead
    field frame : J.Frame
          foundMonitor : lookup ref (monitorRows s) ≡ just frame
          peer : Peer.Peer
          foundPeer : lookup (J.connectionRef frame) (peerRows s) ≡ just peer
          allowed : T.readAllowed (Sub.monitorStep ref (T.waitAction frame)) (T.base s) ≡ true
          results : List (ℕ × T.Observation)
          selected : T.waitResults frame peer s ≡ just results
          provenance : All (λ { (n , observation) → AnyPick (J.connectionRef frame) peer s n observation }) results
  monitor-plan-proof : ∀ ref s plan → Readable s → T.waitMonitorPlan ref s ≡ just plan → MonitorRead ref s
  monitor-plan-proof ref s plan valid eq with lookup ref (monitorRows s) in foundMonitor
  ... | nothing = case eq of λ ()
  ... | just f with lookup (J.connectionRef f) (peerRows s) in foundPeer |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s) in allowed
  ...   | just peer | true with T.waitResults f peer s in selected
  ...     | nothing = case eq of λ ()
  ...     | just results = monitorRead f foundMonitor peer foundPeer allowed results selected
    (wait-proof f peer s results valid selected)
  monitor-plan-proof ref s plan valid eq | just f | nothing | _ = case eq of λ ()
  monitor-plan-proof ref s plan valid eq | just f | just _ | false = case eq of λ ()

  -- Actual initialized events provide the read gates; no extra representation
  -- or caller-supplied physical-result premise is added to these statements.
  poll-advance-proof : ∀ ref w s {t} → Readable s → T.advance (T.pollResults ref w) s ≡ just t → PollRead ref w s
  poll-advance-proof ref w s valid eq with T.pollResultsPlan ref w s in chosen
  ... | nothing = case eq of λ ()
  ... | just plan = poll-plan-proof ref w s plan valid chosen
  job-advance-proof : ∀ j s {t} → Readable s → T.advance (T.waitJobResults j) s ≡ just t → JobRead j s
  job-advance-proof j s valid eq with T.waitJobPlan j s in chosen
  ... | nothing = case eq of λ ()
  ... | just plan = job-plan-proof j s plan valid chosen
  monitor-advance-proof : ∀ ref s {t} → Readable s → T.advance (T.waitMonitorResults ref) s ≡ just t → MonitorRead ref s
  monitor-advance-proof ref s valid eq with T.waitMonitorPlan ref s in chosen
  ... | nothing = case eq of λ ()
  ... | just plan = monitor-plan-proof ref s plan valid chosen
  initialized-poll : ∀ {c g start as s t} ref w → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.pollResults ref w) s ≡ just t → PollRead ref w s
  initialized-poll ref w initialized path eq = poll-advance-proof ref w _ (initialized-readable initialized path) eq
  initialized-job-wait : ∀ {c g start as s t} j → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.waitJobResults j) s ≡ just t → JobRead j s
  initialized-job-wait j initialized path eq = job-advance-proof j _ (initialized-readable initialized path) eq
  initialized-monitor-wait : ∀ {c g start as s t} ref → T.initialize c g ≡ just start → T.Runs start as s →
    T.advance (T.waitMonitorResults ref) s ≡ just t → MonitorRead ref s
  initialized-monitor-wait ref initialized path eq = monitor-advance-proof ref _ (initialized-readable initialized path) eq
