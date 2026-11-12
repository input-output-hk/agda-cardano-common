{-# OPTIONS --guardedness #-}

-- Joint frontend induction: core content, PCs, controls, tickets and saved calls.
module ConnectionManagement.Properties.LiveTrackerAuxCoverageFrontend where
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId; RunId; DecEq-Id)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored; number)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.ServerPeers as Model
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Transport
import ConnectionManagement.Properties.LiveTrackerAuxContent as Content
import ConnectionManagement.Properties.LiveTrackerAuxMonitor as MonitorFacts
import ConnectionManagement.Properties.LiveTrackerAuxCoverageLayers as Layers
import ConnectionManagement.Properties.LiveTrackerAuxBirth as Birth
import ConnectionManagement.Properties.LiveTrackerAuxCoverageUnwind as UnwindFacts
import ConnectionManagement.Properties.LiveTrackerCalls as CallFacts
import ConnectionManagement.Properties.MuxProtocolJobs as JobFacts
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxDeltaQ as DeltaModel
import ConnectionManagement.Properties.LiveTrackerAuxControls as ControlsFacts
import ConnectionManagement.Properties.LiveTrackerAuxTickets as TicketFacts
import ConnectionManagement.Properties.LiveTrackerAuxCoverageInitial as Initial
module U = P.U
module Pool = P.Pool

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = Model.Protocols b io canInitiate using (Call; Front; noteLegacy; legacySelector; setStartShutdown; startFaultState; setPhysical; runtime; enqueue; Plan; Runs; Runtime; advance; allClean; base; birth; byThread; cacheResult; caller; calls; choose; cleanObservation; command; commitClean; commitError; complete; completionPlan; controllerFree; cursor; deliverStartTraceShutdown; deliverTraceFault; descriptor; dispatch; enact; failedC; firstPeer; forkPlan; forkReadyC; forkStart; front; group; handleRef; idle; idleC; inherit; inheritAllowed; initialize; invokeStartTrace; latest; local; more; mux; nextRequest; observeStartTraceException; owner; peer; peerRef; pending; physical; pollResults; pollResultsPlan; protocol; publication; readAllowed; reading; registerPlan; registerStart; registeringC; returnStartTrace; selectPlan; selectStart; selectedC; slotIdle; startNext; startTraceSelection; stop; thread; traceFault; tracingC; value; waitAction; waitJobPlan; waitJobResults; waitMonitorPlan; waitMonitorResults; waitResults; worker)
 private module K = Model b io using (State; context; initial; peerOpen; peers; server; step)
 private module PS = PeerModel io using (cm; step)
 private module C = PeerContext io using (SubContext; subsystem)
 private module N = PublicationModel b using (raw)
 private module G = GroupModel b using (controls; protocolState; base)
 private module Monitor = MonitorModel b using (pcs; ownerContext)
 private module R = UnwindModel b using (faults; State; acknowledge; async; base; inherited; local; machine; pool; poolBody; start; transfer)
 private module W = ExitModel b using (control; physical; shutdown)
 private module S = AdmissionModel b using (inCMClose; stage)
 private module E = IGExitModel b using (base)
 private module Up = Updates b using (Valid; source-valid; pool-retains; fresh-job; module Kernel)
 private module Tr = Transport b using (Retains; OwnerKept; module Rows; source; compose; pc-kept; identity)
 private module A = Content b using (Coverage)
 private module MF = MonitorFacts b using (PCs)
 open CallFacts.Front b io canInitiate using (CallOwner; Calls; rows-kept; enqueue-backed; byThread-backed)
 Rows : Store ConnectionManagement.Domain.RunId T.Call → P.State → Set
 Rows rows p = All (λ { (rid , saved) → CallOwner saved p }) rows
 private module CT = ControlsFacts b using (Controls; rows-kept)
 private module TK = TicketFacts b using (Tickets; Rows; rows-kept)
 delta : K.State → DeltaModel.State b
 delta s = CatchModel.base (PublicationModel.base (T.publication s))
 Base : K.State → Set
 Base s = Up.Valid (T.physical s) × (MF.PCs (Monitor.pcs (G.base (T.group s))) (T.physical s) × (CT.Controls (T.group s) × TK.Tickets (delta s)))
 Valid : T.Runtime → Set
 Valid s = Up.Valid (T.physical (T.base s)) ×
   (MF.PCs (Monitor.pcs (G.base (T.group (T.base s)))) (T.physical (T.base s)) × (CT.Controls (T.group (T.base s)) × (TK.Tickets (delta (T.base s)) × Calls s)))
 record Safe (s : T.Runtime) (p : T.Plan) : Set where
  constructor safe
  field preserves : ∀ {t} → T.enact p s ≡ just t → Valid s → Valid t
 SafePlan : T.Plan → T.Runtime → Set
 SafePlan p s = Safe s p

 -- The observer extracts only small reference tables from an actual K step.
 step-effect : ∀ a s {t} → K.step a s ≡ just t → Base s →
   Up.Valid (T.physical t) × (MF.PCs (Monitor.pcs (G.base (T.group t))) (T.physical t) ×
   (CT.Controls (T.group t) × (TK.Tickets (delta t) × Tr.Retains (T.physical s) (T.physical t))))
 step-effect a s actual (core , pcs , controls , tickets) =
   proj₁ (proj₁ next) , proj₁ (proj₂ (proj₁ next)) , proj₁ (proj₂ (proj₂ (proj₁ next))) , proj₂ next , proj₂ (proj₂ (proj₂ (proj₁ next)))
  where next = Layers.SharedLayer.step-preserves b io (Tr.Retains (T.physical s))
          (λ kept old → Tr.compose old kept) a s actual ((core , pcs , controls , Tr.identity _) , tickets)

 -- Cache writes only peer bookkeeping, so arbitrary physical observers persist.
 cache-valid : ∀ (Obs : P.State → Set) (rid : RunId) (r : T.Call) (result : RunResult) (f : T.Front) (s : K.State) →
   (Up.Valid (T.physical s) × (MF.PCs (Monitor.pcs (G.base (T.group s))) (T.physical s) × (CT.Controls (T.group s) × (TK.Tickets (delta s) × Obs (T.physical s))))) →
   Up.Valid (T.physical (T.cacheResult rid r result f s)) ×
   (MF.PCs (Monitor.pcs (G.base (T.group (T.cacheResult rid r result f s)))) (T.physical (T.cacheResult rid r result f s)) × (CT.Controls (T.group (T.cacheResult rid r result f s)) × (TK.Tickets (delta (T.cacheResult rid r result f s)) × Obs (T.physical (T.cacheResult rid r result f s)))))
 cache-valid Obs rid r result f s valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
 ... | nothing = valid
 ... | just (current , _) with current ≟ rid
 ...   | no _ = valid
 ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context s)))
 ...     | nothing = valid
 ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
 ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
 ...         | nothing = valid
 ...         | just rs = valid
 cache-valid Obs rid r result f s valid | just (current , _) | yes _ | just peer | no _ | _ = valid
 cache-valid Obs rid r result f s valid | just (current , _) | yes _ | just peer | yes _ | no _ = valid

 inherit-safe : ∀ a f s → T.calls f ≡ T.calls (T.front s) → Safe s (T.inherit a f)
 inherit-safe a f s same = safe proof
  where
  proof : ∀ {t} → T.enact (T.inherit a f) s ≡ just t → Valid s → Valid t
  proof eq (core , pcs , controls , tickets , calls) with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just k = case just-injective eq of λ { refl → let changed = step-effect a (T.base s) actual (core , pcs , controls , tickets) in
    proj₁ changed , proj₁ (proj₂ changed) , proj₁ (proj₂ (proj₂ changed)) , proj₁ (proj₂ (proj₂ (proj₂ changed))) , rows-kept _ (proj₂ (proj₂ (proj₂ (proj₂ changed)))) (subst (λ rows → Rows rows _) (sym same) calls) }
 local-safe : ∀ f s → T.calls f ≡ T.calls (T.front s) → Safe s (T.local f)
 local-safe f s same = safe λ eq (core , pcs , controls , tickets , calls) → case just-injective eq of λ { refl → core , pcs , controls , tickets , subst (λ rows → Rows rows _) (sym same) calls }
 reading-safe : ∀ r s → Safe s (T.reading r)
 reading-safe r s = safe λ eq valid → case just-injective eq of λ { refl → valid }
 trace-safe : ∀ w rid result fs s → Safe s (T.traceFault w rid result fs)
 trace-safe w rid result fs s = safe λ eq valid → case just-injective eq of λ { refl → valid }
 deliver-trace-safe : ∀ w rid result fs coordinator s → Safe s (T.deliverTraceFault w rid result fs coordinator)
 deliver-trace-safe w rid result fs coordinator s = safe λ eq (core , pcs , controls , tickets , calls) → case just-injective eq of λ { refl →
   let next = UnwindFacts.Unwind.shutdown-quiet b
         (λ p → Rows (T.calls (T.front s)) p × TK.Rows (DeltaModel.tickets (delta (T.base s))) p)
         (λ kept (oldCalls , oldTickets) → rows-kept _ kept oldCalls , TK.rows-kept _ kept oldTickets)
         coordinator (record (N.raw (T.publication (T.base s))) { faults = fs })
         (core , pcs , controls , calls , tickets)
   in proj₁ next , proj₁ (proj₂ next) , proj₁ (proj₂ (proj₂ next)) , proj₂ (proj₂ (proj₂ (proj₂ next))) , proj₁ (proj₂ (proj₂ (proj₂ next))) }

 caller-safe : ∀ a f s → Rows (T.calls f) (T.physical (T.base s)) → Base (T.base s) → Safe s (T.caller a f)
 caller-safe a f s calls base = safe proof
  where
  proof : ∀ {t} → T.enact (T.caller a f) s ≡ just t → Valid s → Valid t
  proof eq (core , pcs , controls , tickets , old) with PS.step a (K.peers (T.base s))
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → Up.source-valid (PS.cm p) _ core ,
    All.map (λ { {w , pc} → Tr.pc-kept (Tr.source (PS.cm p) _) w pc }) pcs , CT.rows-kept _ (Tr.source (PS.cm p) _) controls , TK.rows-kept _ (Tr.source (PS.cm p) _) tickets , rows-kept _ (Tr.source (PS.cm p) _) calls }
 complete-safe : ∀ a rid r result s → CallOwner r (T.physical (T.base s)) → Safe s (T.complete a rid r result)
 complete-safe a rid r result s backing = safe proof
  where
  proof : ∀ {t} → T.enact (T.complete a rid r result) s ≡ just t → Valid s → Valid t
  proof eq (core , pcs , controls , tickets , calls) with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just k = case just-injective eq of λ { refl → cache-valid (Rows _) rid r result (T.front s) k
    (proj₁ changed , proj₁ (proj₂ changed) , proj₁ (proj₂ (proj₂ changed)) , proj₁ (proj₂ (proj₂ (proj₂ changed))) , Tr.Rows.insert (λ gen saved → CallOwner saved (T.physical k)) rid (record r { value = just result }) (T.calls (T.front s)) good (rows-kept _ kept calls)) }
   where
   changed = step-effect a (T.base s) actual (core , pcs , controls , tickets)
   kept = proj₂ (proj₂ (proj₂ (proj₂ changed)))
   next = Tr.Retains.owners kept (T.owner r) (proj₁ backing)
   good = proj₁ next , trans (Tr.OwnerKept.same-mux (proj₂ next)) (proj₂ backing)
 -- Cursor/legacy bookkeeping never changes the saved calls themselves.
 legacy-calls : ∀ a f → T.calls (T.noteLegacy a f) ≡ T.calls f
 legacy-calls a f with T.legacySelector a
 ... | nothing = refl
 ... | just w = refl

 -- Direct birth simultaneously updates the physical pool, typed job and call.
 birth-safe : ∀ w f pool j rid r fs s →
   lookup w (U.frames (P.base (T.physical (T.base s)))) ≡ just f →
   lookup j (P.jobs (T.physical (T.base s))) ≡ nothing →
   Pool.step (Pool.fork j) (P.poolAt w (T.physical (T.base s))) ≡ just pool →
   T.owner r ≡ w → lookup rid (T.calls (T.front s)) ≡ just r →
   T.calls fs ≡ put rid (record r { thread = just j }) (T.calls (T.front s)) →
   Safe s (T.birth w f pool j rid r fs)
 birth-safe w f pool j rid r fs s found fresh actual refl call-found same = safe proof
  where
  old = T.physical (T.base s)
  job = Types.protocolJob w (T.mux r) Mux.initiatorJob (number (T.descriptor r)) rid Types.executing
  middle = P.setPool w f pool old
  poolKept = Up.pool-retains w f pool old found (Up.Kernel.handles-retained (Pool.fork j) (P.poolAt w old) actual)
  kept = Tr.compose poolKept (Up.fresh-job j job middle fresh)
  proof : ∀ {t} → T.enact (T.birth w f pool j rid r fs) s ≡ just t → Valid s → Valid t
  proof eq (core , pcs , controls , tickets , calls) = case just-injective eq of λ { refl →
    Birth.core-birth b w f pool j rid Mux.initiatorJob (number (T.descriptor r)) (T.mux r) old found fresh actual (proj₁ backing) (proj₂ backing) core ,
    All.map (λ { {q , pc} → Tr.pc-kept kept q pc }) pcs , CT.rows-kept _ kept controls , TK.rows-kept _ kept tickets ,
    subst (λ rows → Rows rows _) (sym same)
      (rows-kept _ kept (Tr.Rows.insert (λ gen saved → CallOwner saved old) rid (record r { thread = just j }) (T.calls (T.front s)) backing calls)) }
   where
   backing = Tr.Rows.at (λ gen saved → CallOwner saved old) (T.calls (T.front s)) calls rid r call-found
 fork-safe : ∀ w j s p → T.forkPlan w j s ≡ just p → Valid s → SafePlan p s
 fork-safe w j s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
   lookup w (U.frames (P.base (T.physical (T.base s)))) in ownerFrame-found
 ... | T.forkReadyC rid | true | just f with lookup rid (T.calls (T.front s)) in found |
   P.fresh j rid (T.physical (T.base s)) in fresh | P.noParent (P.poolAt w (T.physical (T.base s)))
 ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (P.poolAt w (T.physical (T.base s))) in actual
 ...     | yes refl | nothing | nothing | just pool = case just-injective eq of λ { refl →
   birth-safe w f pool j rid r _ s ownerFrame-found (JobFacts.CaptureIdentity.fresh-lookup j rid (T.physical (T.base s)) fresh) actual refl found refl }
 ...     | no _ | _ | _ | _ = case eq of λ ()
 ...     | yes _ | just thread | _ | _ = case eq of λ ()
 ...     | yes _ | nothing | just result | _ = case eq of λ ()
 ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
 fork-safe w j s p eq valid | T.idleC | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.selectedC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.tracingC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.registeringC rid target | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.failedC rid result | _ | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | false | _ = case eq of λ ()
 fork-safe w j s p eq valid | T.forkReadyC rid | true | nothing = case eq of λ ()


 select-safe : ∀ w s p → T.selectPlan w s ≡ just p → Valid s → SafePlan p s
 select-safe w s p eq valid with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
   Monitor.ownerContext w (G.base (T.group (T.base s)))
 ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
   P.muxAt mid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s))) |
   P.noResults (P.poolAt w (T.physical (T.base s))) | Pool.phase (P.poolAt w (T.physical (T.base s)))
 ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
 ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → local-safe _ s refl }
 ...     | Mux.stopping | _ = case eq of λ ()
 ...     | Mux.stopped | _ = case eq of λ ()
 ...     | Mux.failed err | _ = case eq of λ ()
 ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
 ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
 ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
 ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
 ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
 ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
 select-safe w s p eq valid | false | _ | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | [] | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
 select-safe w s p eq valid | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

 register-safe : ∀ j s p → T.registerPlan j s ≡ just p → Valid s → SafePlan p s
 register-safe j s p eq valid with T.byThread j (T.calls (T.front s))
 ... | nothing = case eq of λ ()
 ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
 ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
 ...     | yes _ | yes _ = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...     | no _ | _ = case eq of λ ()
 ...     | yes _ | no _ = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.idleC = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.selectedC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.tracingC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.forkReadyC gen = case eq of λ ()
 register-safe j s p eq valid | just (rid , r) | T.failedC gen result = case eq of λ ()

 completion-safe : ∀ j result s p → T.completionPlan j result s ≡ just p → Valid s → SafePlan p s
 completion-safe j clean s p eq valid with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
   complete-safe _ rid r _ s (byThread-backed j (T.calls (T.front s)) (T.physical (T.base s)) found (proj₂ (proj₂ (proj₂ (proj₂ valid))))) }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j clean s p eq valid | nothing | _ = case eq of λ ()
 completion-safe j clean s p eq valid | just pair | nothing = case eq of λ ()

 completion-safe j (errored commitErr) s p eq valid with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl →
   complete-safe _ rid r _ s (byThread-backed j (T.calls (T.front s)) (T.physical (T.base s)) found (proj₂ (proj₂ (proj₂ (proj₂ valid))))) }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j (errored commitErr) s p eq valid | nothing | _ = case eq of λ ()
 completion-safe j (errored commitErr) s p eq valid | just pair | nothing = case eq of λ ()

 poll-safe : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → Valid s → SafePlan p s
 poll-safe ref w s p eq valid with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
   lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | true | just peer | nothing with Peer.status peer
 ...   | Peer.peerCold = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...   | Peer.peerCooling = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...   | Peer.peerWarm with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...       | false = case just-injective eq of λ { refl → reading-safe _ s }
 poll-safe ref w s p eq valid | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...       | false = case just-injective eq of λ { refl → reading-safe _ s }
 poll-safe ref w s p eq valid | true | just peer | just f = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 poll-safe ref w s p eq valid | false | _ | _ = case eq of λ ()
 poll-safe ref w s p eq valid | true | nothing | _ = case eq of λ ()

 job-wait-safe : ∀ j s p → T.waitJobPlan j s ≡ just p → Valid s → SafePlan p s
 job-wait-safe j s p eq valid with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just jf with Sub.queued jf |
   lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
 ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...       | false = case just-injective eq of λ { refl → reading-safe _ s }
 job-wait-safe j s p eq valid | just jf | true | _ | _ = case eq of λ ()
 job-wait-safe j s p eq valid | just jf | false | nothing | _ = case eq of λ ()
 job-wait-safe j s p eq valid | just jf | false | just peer | false = case eq of λ ()

 monitor-wait-safe : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → Valid s → SafePlan p s
 monitor-wait-safe ref s p eq valid with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
 ...   | just peer | true with T.waitResults f peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → inherit-safe _ _ s refl }
 ...       | false = case just-injective eq of λ { refl → reading-safe _ s }
 monitor-wait-safe ref s p eq valid | just f | nothing | _ = case eq of λ ()
 monitor-wait-safe ref s p eq valid | just f | just peer | false = case eq of λ ()

 choose-safe : ∀ a s p → T.choose a s ≡ just p → Valid s → SafePlan p s
 choose-safe (T.dispatch a) s p eq valid with T.inheritAllowed a s
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl →
   inherit-safe a _ s (legacy-calls a (T.front s)) }
 choose-safe (T.startNext j rid) s p eq valid with K.peerOpen (T.base s) | T.nextRequest j (T.base s) in requested |
   lookup rid (T.calls (T.front s)) in absent | P.generationFresh rid (P.jobs (T.physical (T.base s)))
 ... | true | just req | nothing | true with canInitiate (Peer.handleRef (T.peer req)) (number (T.protocol req)) |
   P.muxAt (Peer.muxRef (T.peer req)) (T.physical (T.base s))
 ...   | false | _ = case eq of λ ()
 ...   | true | nothing = case eq of λ ()
 ...   | true | just m with Mux.status m
 ...     | Mux.stopping = case eq of λ ()
 ...     | Mux.stopped = case eq of λ ()
 ...     | Mux.failed err = case eq of λ ()
 ...     | Mux.ready with T.slotIdle (T.worker req) (number (T.protocol req)) (T.front s)
 ...       | false = case eq of λ ()
 ...       | true = case just-injective eq of λ { refl → caller-safe _ _ s (enqueue-backed j rid req m s (Up.Valid.unique (proj₁ valid)) requested (proj₂ (proj₂ (proj₂ (proj₂ valid))))) (proj₁ valid , proj₁ (proj₂ valid) , proj₁ (proj₂ (proj₂ valid)) , proj₁ (proj₂ (proj₂ (proj₂ valid)))) }
 choose-safe (T.startNext j rid) s p eq valid | false | _ | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | nothing | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | just req | just old | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq valid | true | just req | nothing | false = case eq of λ ()
 choose-safe (T.selectStart w) s p eq valid = select-safe w s p eq valid
 choose-safe (T.invokeStartTrace w) s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.selectedC rid | true = case just-injective eq of λ { refl → local-safe _ s refl }
 choose-safe (T.invokeStartTrace w) s p eq valid | T.idleC | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.tracingC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq valid | T.selectedC rid | false = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.tracingC rid | true = case just-injective eq of λ { refl → local-safe _ s refl }
 choose-safe (T.returnStartTrace w) s p eq valid | T.idleC | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.selectedC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq valid | T.tracingC rid | false = case eq of λ ()
 choose-safe (T.forkStart w j) s p eq valid = fork-safe w j s p eq valid
 choose-safe (T.registerStart j) s p eq valid = register-safe j s p eq valid
 choose-safe (T.commitClean j) s p eq valid = completion-safe j clean s p eq valid
 choose-safe (T.commitError j err) s p eq valid = completion-safe j (errored err) s p eq valid
 choose-safe (T.pollResults ref w) s p eq valid = poll-safe ref w s p eq valid
 choose-safe (T.waitJobResults j) s p eq valid = job-wait-safe j s p eq valid
 choose-safe (T.waitMonitorResults ref) s p eq valid = monitor-wait-safe ref s p eq valid
 choose-safe (T.observeStartTraceException w result) s p eq valid with T.startTraceSelection w result s in selected
 ... | just (rid , fs) = case just-injective eq of λ { refl → trace-safe w rid result fs s }
 ... | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
   Close.phase (W.shutdown (R.base (N.raw (T.publication (T.base s))))) in awaiting
 ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (R.async err) s in selected
 ...   | just (rid , fs) with W.control Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) in received
 ...     | just target = case just-injective eq of λ { refl →
   deliver-trace-safe w rid (R.async err) fs (W.shutdown target) s }
 ...     | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | false | _ = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.initial = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.reading = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.awaitResults = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.closed = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq valid | true | Close.sendReady entry w = case eq of λ ()
 -- Preservation follows actual enabled event selection, including all guarded
 -- acknowledgments. It assumes no physical registry oracle from callers.
 step-preserves : ∀ a s {t} → T.advance a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with T.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = Safe.preserves (choose-safe a s p chosen valid) eq valid
 run-preserves : ∀ {s events t} → T.Runs s events t → Valid s → Valid t
 run-preserves T.stop valid = valid
 run-preserves (T.more {s = s} {a = a} actual rest) valid = run-preserves rest (step-preserves a s actual valid)

 -- The frontend adopts no saved call rows at initialization.
 initialized-valid : ∀ c g {s} → T.initialize c g ≡ just s → Valid s
 initialized-valid c g eq with K.initial c g in actual
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl →
   proj₁ (proj₁ initial) , proj₁ (proj₂ (proj₁ initial)) , proj₂ (proj₂ (proj₁ initial)) , proj₂ initial , [] }
  where initial = Initial.For.combined b io c g actual
 from-initial : ∀ c₀ g {start events s} → T.initialize (O.initial c₀) g ≡ just start →
   T.Runs start events s → Valid s
 from-initial c₀ g initialized path = run-preserves path (initialized-valid (O.initial c₀) g initialized)
 calls-from-initial : ∀ c₀ g {start events s} → T.initialize (O.initial c₀) g ≡ just start →
   T.Runs start events s → Calls s
 calls-from-initial c₀ g initialized path = proj₂ (proj₂ (proj₂ (proj₂ (from-initial c₀ g initialized path))))

 -- The former saved-call premise is discharged for every initialized history.
 fork-from-initial : ∀ c₀ g {start events s} → T.initialize (O.initial c₀) g ≡ just start →
   T.Runs start events s → ∀ w j {plan t} → T.forkPlan w j s ≡ just plan →
   T.enact plan s ≡ just t → Up.Valid (T.physical (T.base t))
 fork-from-initial c₀ g initialized path w j selected enacted =
   Birth.Front.fork-preserves b io canInitiate w j _ selected
     (calls-from-initial c₀ g initialized path) (proj₁ (from-initial c₀ g initialized path)) enacted

 coverage-from-initial : ∀ c₀ g {start events s} → T.initialize (O.initial c₀) g ≡ just start →
   T.Runs start events s → A.Coverage (delta (T.base s))
 coverage-from-initial c₀ g initialized path = record
   { controls = proj₁ (proj₂ (proj₂ valid)); pcs = proj₁ (proj₂ valid)
   ; tickets = proj₁ (proj₂ (proj₂ (proj₂ valid))); jobs = Up.Valid.jobs (proj₁ valid) }
  where valid = from-initial c₀ g initialized path
