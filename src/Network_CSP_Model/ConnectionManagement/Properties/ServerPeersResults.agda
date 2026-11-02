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
  ...   | Types.waitingEgress = capture-phase j job clean p eq
  ...   | Types.executing = case eq of λ ()
  ...   | Types.resultCaptured _ = case eq of λ ()
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
