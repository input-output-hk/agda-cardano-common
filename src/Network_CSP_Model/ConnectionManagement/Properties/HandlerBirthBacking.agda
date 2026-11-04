{-# OPTIONS --guardedness #-}

-- Invert current physical-handler membership through actual initialized frontend runs.
module ConnectionManagement.Properties.HandlerBirthBacking where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Properties.MuxHandlerSupervision as MuxProperties
import ConnectionManagement.Rules.MuxJobTypes as Types
open import Data.Bool using (_∧_)
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.MuxResultMonitor as MonitorModel
open import ConnectionManagement.IGTypes using (clean; errored)
import Data.Nat as Nat
open import Relation.Nullary using (does)
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
open import ConnectionManagement.Properties.HandlerBirthEffects public
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.Properties.MuxDeltaQ as DeltaQProperties
import ConnectionManagement.Properties.MuxCatchUnwind as CatchRoutes
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationRoutes
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.Rules.PeerActions as Peer
open import ConnectionManagement.Domain using (HandleId)
open import Data.Nat using (ℕ)
open import ConnectionManagement.IGTypes using (number)
import ConnectionManagement.Properties.MuxResultMonitor as MonitorInit
import ConnectionManagement.Properties.MuxHandlerExit as ExitInit
import ConnectionManagement.Properties.MuxCatchUnwind as CatchInit
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationInit

module Frontend (isBearerClosed isIOManagerError : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module K = SharedModel isBearerClosed isIOManagerError using (State; context; coreAction; coreAllowed; coreStep; peers; server; serverAllowed; serverStep; step)
 private module T = SharedModel.Protocols isBearerClosed isIOManagerError canInitiate using (Event; Plan; Runs; Runtime; advance; base; birth; cacheResult; caller; calls; choose; complete; deliverTraceFault; descriptor; enact; front; handleRef; inherit; initialize; latest; local; more; mux; owner; peerRef; reading; stop; traceFault)
 private module E = IGExitModel isBearerClosed using (State; base; choose; delegate; enact; initial; step)
 private module SA = AdmissionModel isBearerClosed using (State; allowed; base; chooseScope; enactScope; initial; physicalAction; run; scope; scopeAdvance; step)
 private module N = PublicationModel isBearerClosed using (State; allowed; base; initial; run; step)
 private module PS = PeerModel isIOManagerError using (step)
 private module C = PeerContext isIOManagerError using (SubContext; subsystem)
 view : T.Runtime → Registry
 view s = (SharedLayer.view isBearerClosed isIOManagerError) (T.base s)
 data PlanSelected : T.Plan → T.Runtime → Set where
  inherited-birth : ∀ {a f s} → (SharedLayer.Selected isBearerClosed isIOManagerError) a (T.base s) → PlanSelected (T.inherit a f) s
  completing-birth : ∀ {a rid r result s} → (SharedLayer.Selected isBearerClosed isIOManagerError) a (T.base s) → PlanSelected (T.complete a rid r result) s
 data Selected (a : T.Event) (s : T.Runtime) : Set where
  chosen-birth : ∀ {p} → T.choose a s ≡ just p → PlanSelected p s → Selected a s
 cache-same : ∀ rid r result f b → (SharedLayer.view isBearerClosed isIOManagerError) (T.cacheResult rid r result f b) ≡ (SharedLayer.view isBearerClosed isIOManagerError) b
 cache-same rid r result f b with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
 ... | nothing = refl
 ... | just (current , _) with current ≟ rid
 ...   | no _ = refl
 ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
 ...     | nothing = refl
 ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
 ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
 ...         | nothing = refl
 ...         | just rs = refl
 cache-same rid r result f b | just (current , _) | yes _ | just peer | no _ | _ = refl
 cache-same rid r result f b | just (current , _) | yes _ | just peer | yes _ | no _ = refl
 enact-change : ∀ p s {t} → T.enact p s ≡ just t → Change (PlanSelected p s) (view s) (view t)
 enact-change (T.inherit a f) s eq with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → map-change inherited-birth ((SharedLayer.change isBearerClosed isIOManagerError) a (T.base s) actual) }
 enact-change (T.complete a rid r result) s eq with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just b = case just-injective eq of λ { refl → followed (map-change completing-birth ((SharedLayer.change isBearerClosed isIOManagerError) a (T.base s) actual)) (stable (cache-same rid r result (T.front s) b)) }
 enact-change (T.caller a f) s eq with PS.step a (K.peers (T.base s))
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → stable refl }
 enact-change (T.local f) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (T.reading r) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (T.traceFault w rid result fs) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (T.deliverTraceFault w rid result fs coordinator) s eq = case just-injective eq of λ { refl → stable refl }
 enact-change (T.birth w capturedFrame pool j rid r f) s eq = case just-injective eq of λ { refl → stable refl }
 change : ∀ a s {t} → T.advance a s ≡ just t → Change (Selected a s) (view s) (view t)
 change a s eq with T.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = map-change (chosen-birth chosen) (enact-change p s eq)
 module LocatedSearch = Search T.Runtime T.Event T.advance view (λ s a _ → Selected a s) change
 execution : ∀ {s actions t} → T.Runs s actions t → LocatedSearch.Runs s actions t
 execution T.stop = LocatedSearch.done
 execution (T.more actual rest) = LocatedSearch.next actual (execution rest)

 -- Every certificate below follows an actual nested call. Capture-map equality
 -- tolerates only wrapper bookkeeping after that call, including shutdown Ack.
 private module U = MuxModel Types.TypedResult using (State; base; run; step)
 private module P = ProtocolModel using (State; base; run; step)
 private module Monitor = MonitorModel isBearerClosed using (State; base; run; step)
 private module G = GroupModel isBearerClosed using (State; base; run; step)
 private module W = ExitModel isBearerClosed using (State; base; choose; control; enact; inherited; step)
 private module X = CancellationModel isBearerClosed using (run; step)
 private module R = UnwindModel isBearerClosed using (State; acknowledge; base; choose; enact; inherited; step)
 private module D = DeltaQModel isBearerClosed using (State; allowed; base; run; step)
 private module Catch = CatchModel isBearerClosed using (State; allowed; base; run; step)
 private module MuxProof = MuxLayer using (Selected; inherited-birth; view)
 private module JobProof = ProtocolLayer using (Selected; inherited-birth; view)
 private module MonitorProof = MonitorLayer isBearerClosed using (Selected; inherited-birth; view)
 private module GroupProof = GroupLayer isBearerClosed using (Selected; inherited-birth; view)
 private module ExitProof = ExitLayer isBearerClosed using (CIPaths; PlanSelected; Selected; chosen-birth; ci-control-projects; inherited-plan; view)
 private module CancelProof = CancellationLayer isBearerClosed using (Selected; inherited-birth; view)
 private module UnwindProof = UnwindLayer isBearerClosed using (PlanSelected; Selected; acknowledged-plan; chosen-birth; inherited-plan; view)
 private module DeltaProof = DeltaQLayer isBearerClosed using (Selected; inherited-birth; view)
 private module CatchProof = CatchLayer isBearerClosed using (Selected; inherited-birth; view)
 private module PublicationProof = PublicationLayer isBearerClosed using (Selected; inherited-birth; view)
 private module Route = InheritedRoutes isBearerClosed using (group-inherited; jobs-inherited; monitor-inherited; mux-inherited)
 mux-state : U.State → B.State
 mux-state = U.base
 job-state : P.State → B.State
 job-state s = mux-state (P.base s)
 monitor-state : Monitor.State → B.State
 monitor-state s = job-state (Monitor.base s)
 group-state : G.State → B.State
 group-state s = monitor-state (G.base s)
 exit-state : W.State → B.State
 exit-state s = group-state (W.base s)
 unwind-state : R.State → B.State
 unwind-state s = exit-state (R.base s)
 delta-state : D.State → B.State
 delta-state s = unwind-state (D.base s)
 catch-state : Catch.State → B.State
 catch-state s = delta-state (Catch.base s)
 publication-state : N.State → B.State
 publication-state s = catch-state (N.base s)
 server-state : SA.State → B.State
 server-state s = publication-state (SA.base s)
 ig-state : E.State → B.State
 ig-state s = server-state (E.base s)
 shared-state : K.State → B.State
 shared-state s = ig-state (K.server s)
 physical-state : T.Runtime → B.State
 physical-state s = shared-state (T.base s)
 record ForkStep (before : B.State) (after : Registry) : Set where
  constructor fork-step
  field
   command : B.Action
   target : B.State
   enabled : B.step command before ≡ just target
   kind : PhysicalBirth command
   captures-after : physical target ≡ after
 retarget : ∀ {before after next} → after ≡ next → ForkStep before after → ForkStep before next
 retarget same (fork-step command target enabled kind captures-after) = fork-step command target enabled kind (trans captures-after same)
 mux-fork : ∀ a s {t} → U.step a s ≡ just t → MuxProof.Selected a → ForkStep (mux-state s) (MuxProof.view t)
 mux-fork (U.run a) s {t} actual (MuxProof.inherited-birth kind) = fork-step a (U.base t) (Route.mux-inherited a s actual) kind refl
 job-fork : ∀ a s {t} → P.step a s ≡ just t → JobProof.Selected a → ForkStep (job-state s) (JobProof.view t)
 job-fork (P.run a) s actual (JobProof.inherited-birth selected) = mux-fork a (P.base s) (Route.jobs-inherited a s actual) selected
 monitor-fork : ∀ a s {t} → Monitor.step a s ≡ just t → MonitorProof.Selected a → ForkStep (monitor-state s) (MonitorProof.view t)
 monitor-fork (Monitor.run a) s actual (MonitorProof.inherited-birth selected) = job-fork a (Monitor.base s) (Route.monitor-inherited a s actual) selected
 group-fork : ∀ a s {t} → G.step a s ≡ just t → GroupProof.Selected a → ForkStep (group-state s) (GroupProof.view t)
 group-fork (G.run a) s actual (GroupProof.inherited-birth selected) = monitor-fork a (G.base s) (Route.group-inherited a s actual) selected
 exit-enact : ∀ a p s {t} → W.choose a s ≡ just p → W.step a s ≡ just t → W.enact p s ≡ just t
 exit-enact a p s chosen actual with W.choose a s
 ... | nothing = case chosen of λ ()
 ... | just q = case just-injective chosen of λ { refl → actual }
 exit-enact-fork : ∀ p s {t} → W.enact p s ≡ just t → ExitProof.PlanSelected p s → ForkStep (exit-state s) (ExitProof.view t)
 exit-enact-fork (W.inherited a) s actual (ExitProof.inherited-plan selected) with G.step a (W.base s) in advanced
 ... | nothing = case actual of λ ()
 ... | just g = case just-injective actual of λ { refl → group-fork a (W.base s) advanced selected }
 exit-fork : ∀ a s {t} → W.step a s ≡ just t → ExitProof.Selected a s → ForkStep (exit-state s) (ExitProof.view t)
 exit-fork a s actual (ExitProof.chosen-birth {p} chosen selected) = exit-enact-fork p s (exit-enact a p s chosen actual) selected
 cancel-fork : ∀ a s {t} → X.step a s ≡ just t → CancelProof.Selected a s → ForkStep (exit-state s) (CancelProof.view t)
 cancel-fork (X.run a) s actual (CancelProof.inherited-birth selected) = exit-fork a s actual selected
 unwind-enact : ∀ a p s {t} → R.choose a s ≡ just p → R.step a s ≡ just t → R.enact p s ≡ just t
 unwind-enact a p s chosen actual with R.choose a s
 ... | nothing = case chosen of λ ()
 ... | just q = case just-injective chosen of λ { refl → actual }
 unwind-enact-fork : ∀ p s {t} → R.enact p s ≡ just t → UnwindProof.PlanSelected p s → ForkStep (unwind-state s) (UnwindProof.view t)
 unwind-enact-fork (R.inherited a) s actual (UnwindProof.inherited-plan selected) with X.step a (R.base s) in advanced
 ... | nothing = case actual of λ ()
 ... | just x = case just-injective actual of λ { refl → cancel-fork a (R.base s) advanced selected }
 unwind-enact-fork (R.acknowledge p) s actual (UnwindProof.acknowledged-plan selected) with R.enact p s in advanced
 ... | nothing = case actual of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case actual of λ ()
 ...   | just w = case just-injective actual of λ { refl → retarget
   (sym (ExitProof.CIPaths.retention (ExitProof.ci-control-projects Close.acknowledgeDelivery (R.base next) acknowledged)))
   (unwind-enact-fork p s advanced selected) }
 unwind-fork : ∀ a s {t} → R.step a s ≡ just t → UnwindProof.Selected a s → ForkStep (unwind-state s) (UnwindProof.view t)
 unwind-fork a s actual (UnwindProof.chosen-birth {p} chosen selected) = unwind-enact-fork p s (unwind-enact a p s chosen actual) selected
 delta-fork : ∀ a s {t} → D.step a s ≡ just t → DeltaProof.Selected a s → ForkStep (delta-state s) (DeltaProof.view t)
 delta-fork (D.run a) s actual (DeltaProof.inherited-birth selected) with D.allowed a s
 ... | false = case actual of λ ()
 ... | true with R.step a (D.base s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just r = case just-injective actual of λ { refl → unwind-fork a (D.base s) advanced selected }
 catch-fork : ∀ a s {t} → Catch.step a s ≡ just t → CatchProof.Selected a s → ForkStep (catch-state s) (CatchProof.view t)
 catch-fork (Catch.run a) s actual (CatchProof.inherited-birth selected) with Catch.allowed a
 ... | false = case actual of λ ()
 ... | true with D.step a (Catch.base s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just d = case just-injective actual of λ { refl → delta-fork a (Catch.base s) advanced selected }
 publication-fork : ∀ a s {t} → N.step a s ≡ just t → PublicationProof.Selected a s → ForkStep (publication-state s) (PublicationProof.view t)
 publication-fork (N.run a) s actual (PublicationProof.inherited-birth selected) with N.allowed a s
 ... | false = case actual of λ ()
 ... | true with Catch.step a (N.base s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just c = case just-injective actual of λ { refl → catch-fork a (N.base s) advanced selected }
 server-scope-fork : ∀ a p command s {t} → SA.chooseScope a s ≡ just p → SA.physicalAction p ≡ just command → SA.enactScope p s ≡ just t →
   PublicationProof.Selected command (SA.base s) → ForkStep (server-state s) ((ServerLayer.view isBearerClosed) t)
 server-scope-fork a p command s chosen selected actual witness with SA.physicalAction p
 ... | nothing = case selected of λ ()
 ... | just op with just-injective selected
 ...   | refl with N.step command (SA.base s) in advanced
 ...     | nothing = case actual of λ ()
 ...     | just n = case just-injective actual of λ { refl → publication-fork command (SA.base s) advanced witness }
 server-scope-enact : ∀ a p s {t} → SA.chooseScope a s ≡ just p → SA.scopeAdvance a s ≡ just t → SA.enactScope p s ≡ just t
 server-scope-enact a p s chosen actual with SA.chooseScope a s
 ... | nothing = case chosen of λ ()
 ... | just q = case just-injective chosen of λ { refl → actual }
 server-fork : ∀ a s {t} → SA.step a s ≡ just t → (ServerLayer.Selected isBearerClosed) a s → ForkStep (server-state s) ((ServerLayer.view isBearerClosed) t)
 server-fork (SA.run a) s actual (ServerLayer.inherited-birth selected) with SA.allowed a s
 ... | false = case actual of λ ()
 ... | true with N.step a (SA.base s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just n = case just-injective actual of λ { refl → publication-fork a (SA.base s) advanced selected }
 server-fork (SA.scope a) s actual (ServerLayer.scoped-birth {p = p} {command} chosen selected witness) =
   server-scope-fork a p command s chosen selected (server-scope-enact a p s chosen actual) witness
 ig-enact : ∀ a p s {t} → E.choose a s ≡ just p → E.step a s ≡ just t → E.enact p s ≡ just t
 ig-enact a p s chosen actual with E.choose a s
 ... | nothing = case chosen of λ ()
 ... | just q = case just-injective chosen of λ { refl → actual }
 ig-enact-fork : ∀ p s {t} → E.enact p s ≡ just t → (IGExitLayer.PlanSelected isBearerClosed) p s → ForkStep (ig-state s) ((IGExitLayer.view isBearerClosed) t)
 ig-enact-fork (E.delegate a e) s actual (IGExitLayer.delegated-birth selected) with SA.step a (E.base s) in advanced
 ... | nothing = case actual of λ ()
 ... | just server = case just-injective actual of λ { refl → server-fork a (E.base s) advanced selected }
 ig-fork : ∀ a s {t} → E.step a s ≡ just t → (IGExitLayer.Selected isBearerClosed) a s → ForkStep (ig-state s) ((IGExitLayer.view isBearerClosed) t)
 ig-fork a s actual (IGExitLayer.chosen-birth {p} chosen selected) = ig-enact-fork p s (ig-enact a p s chosen actual) selected
 shared-fork : ∀ a s {t} → K.step a s ≡ just t → (SharedLayer.Selected isBearerClosed isIOManagerError) a s → ForkStep (shared-state s) ((SharedLayer.view isBearerClosed isIOManagerError) t)
 shared-fork (K.serverStep a) s actual (SharedLayer.server-birth selected) with K.serverAllowed a s
 ... | false = case actual of λ ()
 ... | true with E.step a (K.server s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just e = case just-injective actual of λ { refl → ig-fork a (K.server s) advanced selected }
 shared-fork (K.coreStep a) s actual (SharedLayer.core-birth selected) with K.coreAllowed a s
 ... | false = case actual of λ ()
 ... | true with E.step (K.coreAction a) (K.server s) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just e = case just-injective actual of λ { refl → ig-fork (K.coreAction a) (K.server s) advanced selected }
 frontend-enact : ∀ a p s {t} → T.choose a s ≡ just p → T.advance a s ≡ just t → T.enact p s ≡ just t
 frontend-enact a p s chosen actual with T.choose a s
 ... | nothing = case chosen of λ ()
 ... | just q = case just-injective chosen of λ { refl → actual }
 enact-fork : ∀ p s {t} → T.enact p s ≡ just t → PlanSelected p s → ForkStep (physical-state s) (view t)
 enact-fork (T.inherit a f) s actual (inherited-birth selected) with K.step a (T.base s) in advanced
 ... | nothing = case actual of λ ()
 ... | just b = case just-injective actual of λ { refl → shared-fork a (T.base s) advanced selected }
 enact-fork (T.complete a rid r result) s actual (completing-birth selected) with K.step a (T.base s) in advanced
 ... | nothing = case actual of λ ()
 ... | just b = case just-injective actual of λ { refl → retarget (sym (cache-same rid r result (T.front s) b)) (shared-fork a (T.base s) advanced selected) }
 actual-fork : ∀ a s {t} → T.advance a s ≡ just t → Selected a s → ForkStep (physical-state s) (view t)
 actual-fork a s actual (chosen-birth {p} chosen selected) = enact-fork p s (frontend-enact a p s chosen actual) selected

 -- Successful initialization refuses adoption of an already populated physical
 -- registry. No caller-supplied supply or resource-validity premise is needed.
 publication-empty : ∀ c {n} → N.initial c ≡ just n → PublicationProof.view n ≡ []
 publication-empty c initialized = initial-empty c
   (MuxProperties.initial-base Types.TypedResult c
   (ProtocolProperties.initial-base c
   (MonitorInit.initial-base isBearerClosed c
   (GroupProperties.initial-base isBearerClosed c
   (ExitInit.initial-base isBearerClosed c
   (UnwindProperties.initial-base isBearerClosed c
   (DeltaQProperties.initial-base isBearerClosed c
   (CatchInit.initial-base isBearerClosed c
   (PublicationInit.initial-base isBearerClosed c initialized)))))))))
 server-empty : ∀ c {a} → SA.initial c ≡ just a → (ServerLayer.view isBearerClosed) a ≡ []
 server-empty c initialized with Shared.admissions (M.world (O.core c)) | Shared.sockets (M.world (O.core c)) | N.initial c in lower
 ... | [] | [] | just n = case just-injective initialized of λ { refl → publication-empty c lower }
 ... | _ ∷ _ | _ | _ = case initialized of λ ()
 ... | [] | _ ∷ _ | _ = case initialized of λ ()
 ... | [] | [] | nothing = case initialized of λ ()
 ig-empty : ∀ c {e} → E.initial c ≡ just e → (IGExitLayer.view isBearerClosed) e ≡ []
 ig-empty c initialized with M.inboundRelease (O.core c) | M.remoteCall (O.core c) | SA.initial c in lower
 ... | nothing | nothing | just a = case just-injective initialized of λ { refl → server-empty c lower }
 ... | just _ | _ | _ = case initialized of λ ()
 ... | nothing | just _ | _ = case initialized of λ ()
 ... | nothing | nothing | nothing = case initialized of λ ()
 initialized-empty : ∀ c g {start} → T.initialize c g ≡ just start → view start ≡ []
 initialized-empty c g initialized with E.initial c in lower
 ... | nothing = case initialized of λ ()
 ... | just e = case just-injective initialized of λ { refl → ig-empty c lower }
 -- The location records the actual frontend prefix/event/suffix. Its nested
 -- physical operation is enabled at that event's physical input, and has the
 -- same capture map at output; wrapper-only bookkeeping is accounted for.
 record Backing (start current : T.Runtime) (events : List T.Event) (w : WorkerId) (captured : S.HandlerStart) : Set where
  constructor backing
  field
   location : LocatedSearch.Located start current events w captured
   operation : ForkStep (physical-state (LocatedSearch.Located.before location))
     (view (LocatedSearch.Located.after location))
   selected-operation : operation ≡ actual-fork
     (LocatedSearch.Located.action location) (LocatedSearch.Located.before location)
     (LocatedSearch.Located.actual location) (LocatedSearch.Located.selected location)
   at-physical-fork : lookup w (physical (ForkStep.target operation)) ≡ just captured
 initialized-birth : ∀ {c g start events current w thread} → T.initialize c g ≡ just start → T.Runs start events current →
   lookup w (B.threads (physical-state current)) ≡ just thread → Backing start current events w (H.captured thread)
 initialized-birth {c} {g} {start} {events} {current} {w} {thread} initialized path found =
   backing located nested-fork refl (trans (cong (lookup w) (ForkStep.captures-after nested-fork)) (LocatedSearch.Located.at-birth located))
   where
   located : LocatedSearch.Located start current events w (H.captured thread)
   located = LocatedSearch.locate (execution path) w (H.captured thread)
     (trans (cong (lookup w) (initialized-empty c g initialized)) refl)
     (trans (lookup-captures w (B.threads (physical-state current))) (cong (Data.Maybe.map H.captured) found))
   nested-fork : ForkStep (physical-state (LocatedSearch.Located.before located)) (view (LocatedSearch.Located.after located))
   nested-fork = actual-fork (LocatedSearch.Located.action located) (LocatedSearch.Located.before located)
     (LocatedSearch.Located.actual located) (LocatedSearch.Located.selected located)

 -- Opaque frontend traces extend the same discovered fork. No new birth,
 -- resource premise or physical lookup is supplied at subsequent checkpoints.
 search-append : ∀ {s as t bs u} → LocatedSearch.Runs s as t → LocatedSearch.Runs t bs u → LocatedSearch.Runs s (as ++ bs) u
 search-append LocatedSearch.done rest = rest
 search-append (LocatedSearch.next actual path) rest = LocatedSearch.next actual (search-append path rest)
 follow : ∀ {start before after events tail w captured} → T.Runs before tail after →
   Backing start before events w captured → Backing start after (events ++ tail) w captured
 follow {start} {before} {after} {events} {tail} {w} {captured} path history =
   backing located (Backing.operation history) (Backing.selected-operation history) (Backing.at-physical-fork history)
   where
   previous = Backing.location history
   located : LocatedSearch.Located start after (events ++ tail) w captured
   located = record
     { before = LocatedSearch.Located.before previous
     ; after = LocatedSearch.Located.after previous
     ; action = LocatedSearch.Located.action previous
     ; prefix = LocatedSearch.Located.prefix previous
     ; suffix = LocatedSearch.Located.suffix previous ++ tail
     ; decomposition = trans (cong (λ es → es ++ tail) (LocatedSearch.Located.decomposition previous))
         (++-assoc (LocatedSearch.Located.prefix previous) (LocatedSearch.Located.action previous ∷ LocatedSearch.Located.suffix previous) tail)
     ; prefix-run = LocatedSearch.Located.prefix-run previous
     ; actual = LocatedSearch.Located.actual previous
     ; selected = LocatedSearch.Located.selected previous
     ; absent-before = LocatedSearch.Located.absent-before previous
     ; at-birth = LocatedSearch.Located.at-birth previous
     ; suffix-run = search-append (LocatedSearch.Located.suffix-run previous) (execution path)
     ; retained-descriptor = LocatedSearch.retained (execution path) w captured (LocatedSearch.Located.retained-descriptor previous) }
 follow-operation : ∀ {start before after events tail w captured} (path : T.Runs before tail after)
   (history : Backing start before events w captured) → Backing.operation (follow path history) ≡ Backing.operation history
 follow-operation path history = refl
 -- A retained capture denotes an actual current physical thread, and every
 -- lookup of that worker has the same original captured descriptor.
 capture-of-found : ∀ {start current events w captured thread} → Backing start current events w captured →
   lookup w (B.threads (physical-state current)) ≡ just thread → H.captured thread ≡ captured
 capture-of-found {current = current} {w = w} history found = just-injective (trans
   (sym (trans (lookup-captures w (B.threads (physical-state current))) (cong (Data.Maybe.map H.captured) found)))
   (LocatedSearch.Located.retained-descriptor (Backing.location history)))
 current-thread : ∀ {start current events w captured} → Backing start current events w captured →
   Σ H.Thread (λ thread → lookup w (B.threads (physical-state current)) ≡ just thread × H.captured thread ≡ captured)
 current-thread {current = current} {w = w} history with lookup w (B.threads (physical-state current)) in found
 ... | nothing = case trans (sym (trans (lookup-captures w (B.threads (physical-state current)))
     (cong (Data.Maybe.map H.captured) found))) (LocatedSearch.Located.retained-descriptor (Backing.location history)) of λ ()
 ... | just thread = thread , refl , capture-of-found history found
