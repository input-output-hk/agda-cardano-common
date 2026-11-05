{-# OPTIONS --guardedness #-}

-- Only the actual eager-start caller plan enters the peer job interpreter.
module ConnectionManagement.Properties.InboundOriginPlanSafety where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (ErrorId; HandleId; JobId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (clean; errored; number)
import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.GovernorPool as PoolModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = SharedModel.Protocols b io canInitiate using (Plan; Runs; Runtime; advance; allClean; base; birth; byThread; cacheResult; caller; calls; choose; cleanObservation; command; commitClean; commitError; complete; completionPlan; controllerFree; cursor; deliverStartTraceShutdown; deliverTraceFault; descriptor; dispatch; enact; failedC; firstPeer; forkPlan; forkReadyC; forkStart; front; group; handleRef; idle; idleC; inherit; inheritAllowed; initialize; invokeStartTrace; latest; local; more; mux; nextRequest; observeStartTraceException; owner; peer; peerRef; pending; physical; pollResults; pollResultsPlan; protocol; publication; readAllowed; reading; registerPlan; registerStart; registeringC; returnStartTrace; selectPlan; selectStart; selectedC; slotIdle; startNext; startTraceSelection; stop; thread; traceFault; tracingC; value; waitAction; waitJobPlan; waitJobResults; waitMonitorPlan; waitMonitorResults; waitResults; worker)
 private module K = SharedModel b io using (context; initial; peerOpen; peers; server; step)
 private module PS = PeerModel io using (Action; run; module GP)
 private module GP = PS.GP using (run)
 private module C = PeerContext io using (SubContext; subsystem)
 private module N = PublicationModel b using (raw)
 private module G = GroupModel b using (base)
 private module Monitor = MonitorModel b using (ownerContext)
 private module R = UnwindModel b using (State; acknowledge; async; base; inherited; local; machine; pool; poolBody; start; transfer)
 private module W = ExitModel b using (control; physical; shutdown)
 private module U = MuxModel Types.TypedResult using (frames)
 private module P = ProtocolModel using (base; fresh; generationFresh; jobs; muxAt; noParent; noResults; poolAt)
 private module Pool = ProtocolModel.Pool using (cancelPending; closedPool; closing; fork; joinPending; openPool; phase; step)
 private module S = AdmissionModel b using (inCMClose; stage)
 private module E = IGExitModel b using (base)
 -- The witness identifies the permitted caller rather than assuming arbitrary
 -- peer-core actions are quiet. Every other selected plan is unrestricted here.
 SafePlan : T.Plan → Set
 SafePlan (T.caller a f) = Σ JobId (λ j → a ≡ PS.run (GP.run (Sub.jobStep j J.runNext)))
 SafePlan _ = ⊤

 fork-safe : ∀ w j s p → T.forkPlan w j s ≡ just p → SafePlan p
 fork-safe w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
   lookup w (U.frames (P.base (T.physical (T.base s)))) in ownerFrame-found
 ... | T.forkReadyC rid | true | just f with lookup rid (T.calls (T.front s)) in found |
   P.fresh j rid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s)))
 ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (P.poolAt w (T.physical (T.base s)))
 ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl → tt }
 ...     | no _ | _ | _ | _ = case eq of λ ()
 ...     | yes _ | just thread | _ | _ = case eq of λ ()
 ...     | yes _ | nothing | just result | _ = case eq of λ ()
 ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
 fork-safe w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
 fork-safe w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
 fork-safe w j s p eq | T.idleC | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.registeringC rid target | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
 fork-safe w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
 fork-safe w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()


 select-safe : ∀ w s p → T.selectPlan w s ≡ just p → SafePlan p
 select-safe w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
   Monitor.ownerContext w (G.base (T.group (T.base s)))
 ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
   P.muxAt mid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s))) |
   P.noResults (P.poolAt w (T.physical (T.base s))) | Pool.phase (P.poolAt w (T.physical (T.base s)))
 ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
 ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → tt }
 ...     | Mux.stopping | _ = case eq of λ ()
 ...     | Mux.stopped | _ = case eq of λ ()
 ...     | Mux.failed err | _ = case eq of λ ()
 ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
 ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
 ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
 ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
 ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
 ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
 select-safe w s p eq | false | _ | _ | _ = case eq of λ ()
 select-safe w s p eq | true | [] | _ | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
 select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

 register-safe : ∀ j s p → T.registerPlan j s ≡ just p → SafePlan p
 register-safe j s p eq with T.byThread j (T.calls (T.front s))
 ... | nothing = case eq of λ ()
 ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
 ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
 ...     | yes _ | yes _ = case just-injective eq of λ { refl → tt }
 ...     | no _ | _ = case eq of λ ()
 ...     | yes _ | no _ = case eq of λ ()
 register-safe j s p eq | just (rid , r) | T.idleC = case eq of λ ()
 register-safe j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
 register-safe j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
 register-safe j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
 register-safe j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

 completion-safe : ∀ j result s p → T.completionPlan j result s ≡ just p → SafePlan p
 completion-safe j clean s p eq with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl → tt }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j clean s p eq | nothing | _ = case eq of λ ()
 completion-safe j clean s p eq | just pair | nothing = case eq of λ ()

 completion-safe j (errored commitErr) s p eq with T.byThread j (T.calls (T.front s)) in found |
   lookup j (P.jobs (T.physical (T.base s)))
 ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
   Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
 ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl → tt }
 ...   | just old | _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
 ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
 completion-safe j (errored commitErr) s p eq | nothing | _ = case eq of λ ()
 completion-safe j (errored commitErr) s p eq | just pair | nothing = case eq of λ ()

 poll-safe : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → SafePlan p
 poll-safe ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
   lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | true | just peer | nothing with Peer.status peer
 ...   | Peer.peerCold = case just-injective eq of λ { refl → tt }
 ...   | Peer.peerCooling = case just-injective eq of λ { refl → tt }
 ...   | Peer.peerWarm with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
 ...     | nothing = case eq of λ ()
 ...     | just (kind , result) with T.cleanObservation result
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → tt }
 poll-safe ref w s p eq | false | _ | _ = case eq of λ ()
 poll-safe ref w s p eq | true | nothing | _ = case eq of λ ()

 job-wait-safe : ∀ j s p → T.waitJobPlan j s ≡ just p → SafePlan p
 job-wait-safe j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just jf with Sub.queued jf |
   lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
 ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 job-wait-safe j s p eq | just jf | true | _ | _ = case eq of λ ()
 job-wait-safe j s p eq | just jf | false | nothing | _ = case eq of λ ()
 job-wait-safe j s p eq | just jf | false | just peer | false = case eq of λ ()

 monitor-wait-safe : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → SafePlan p
 monitor-wait-safe ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
 ... | nothing = case eq of λ ()
 ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
   T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
 ...   | just peer | true with T.waitResults f peer s
 ...     | nothing = case eq of λ ()
 ...     | just results with T.allClean results
 ...       | true = case just-injective eq of λ { refl → tt }
 ...       | false = case just-injective eq of λ { refl → tt }
 monitor-wait-safe ref s p eq | just f | nothing | _ = case eq of λ ()
 monitor-wait-safe ref s p eq | just f | just peer | false = case eq of λ ()

 choose-safe : ∀ a s p → T.choose a s ≡ just p → SafePlan p
 choose-safe (T.dispatch a) s p eq with T.inheritAllowed a s
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.startNext j rid) s p eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
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
 ...       | true = case just-injective eq of λ { refl → j , refl }
 choose-safe (T.startNext j rid) s p eq | false | _ | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq | true | nothing | _ | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq | true | just req | just old | _ = case eq of λ ()
 choose-safe (T.startNext j rid) s p eq | true | just req | nothing | false = case eq of λ ()
 choose-safe (T.selectStart w) s p eq = select-safe w s p eq
 choose-safe (T.invokeStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.selectedC rid | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.invokeStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq | T.tracingC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.invokeStartTrace w) s p eq | T.selectedC rid | false = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
 ... | T.tracingC rid | true = case just-injective eq of λ { refl → tt }
 choose-safe (T.returnStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq | T.selectedC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
 choose-safe (T.returnStartTrace w) s p eq | T.tracingC rid | false = case eq of λ ()
 choose-safe (T.forkStart w j) s p eq = fork-safe w j s p eq
 choose-safe (T.registerStart j) s p eq = register-safe j s p eq
 choose-safe (T.commitClean j) s p eq = completion-safe j clean s p eq
 choose-safe (T.commitError j err) s p eq = completion-safe j (errored err) s p eq
 choose-safe (T.pollResults ref w) s p eq = poll-safe ref w s p eq
 choose-safe (T.waitJobResults j) s p eq = job-wait-safe j s p eq
 choose-safe (T.waitMonitorResults ref) s p eq = monitor-wait-safe ref s p eq
 choose-safe (T.observeStartTraceException w result) s p eq with T.startTraceSelection w result s in selected
 ... | just (rid , fs) = case just-injective eq of λ { refl → tt }
 ... | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
   Close.phase (W.shutdown (R.base (N.raw (T.publication (T.base s))))) in awaiting
 ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (R.async err) s in selected
 ...   | just (rid , fs) with W.control Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) in received
 ...     | just target = case just-injective eq of λ { refl → tt }
 ...     | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | false | _ = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.initial = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.reading = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitResults = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.closed = case eq of λ ()
 choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.sendReady entry w = case eq of λ ()
