{-# OPTIONS --guardedness #-}

-- The physical-birth certificate retains actual frontend labels. Its inbound
-- branch recovers source ownership; outbound births remain an explicit branch.
module ConnectionManagement.Properties.InboundBirthLabels where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Properties.HandlerBirthEffects as Effects
import ConnectionManagement.Properties.HandlerBirthBacking as Backing
import ConnectionManagement.Properties.InboundOriginReconstruction as Reconstruction

-- Only a newly written key can explain an absent-before/present-after row.
private
 put-identifies : ∀ (writer queried : WorkerId) (descriptor : S.HandlerStart) (registry : Effects.Registry) (captured : S.HandlerStart) →
   lookup queried registry ≡ nothing → lookup queried (put writer descriptor registry) ≡ just captured →
   queried ≡ writer × descriptor ≡ captured
 put-identifies writer queried descriptor registry captured absent found with queried ≟ writer
 ... | yes refl = refl , just-injective (trans (sym (lookup-put writer descriptor registry)) found)
 ... | no different = case trans (sym absent)
   (trans (sym (lookup-put-other writer queried descriptor registry different)) found) of λ ()

 fork-installed : ∀ parent request saved promise entry before {after} →
   lookup parent (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) →
   M.advance (M.admissionStep parent Admission.fork) before ≡ just after →
   lookup (S.child request) (S.handlers (M.world after)) ≡ just (S.handlerStart entry (S.socketRef request) promise (S.key request))
 fork-installed parent request saved promise entry before beforePC actual rewrite beforePC
   with lookup (S.child request) (S.handlers (M.world before)) | lookup (S.child request) (S.admissions (M.world before))
 ... | just _ | _ = case actual of λ ()
 ... | nothing | just _ = case actual of λ ()
 ... | nothing | nothing with just-injective actual
 ...   | refl = lookup-put (S.child request) _ (S.handlers (M.world before))

 record RawInbound (parent : WorkerId) (before after : B.State) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   request : S.Admission
   heldLease : S.Lease
   promise : PromiseId
   entry : EntryId
   before-PC : lookup parent (S.admissions (M.world (O.core (B.source before)))) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))
   source : M.advance (M.admissionStep parent Admission.fork) (O.core (B.source before)) ≡ just (O.core (B.source after))
   worker : queried ≡ S.child request
   descriptor : captured ≡ S.handlerStart entry (S.socketRef request) promise (S.key request)

 raw-handler : ∀ parent before {next queried captured} →
   H.forkAdmission parent (B.view before) ≡ just next →
   lookup queried (Effects.physical before) ≡ nothing → lookup queried (Effects.physical (B.setView next before)) ≡ just captured →
   RawInbound parent before (B.setView next before) queried captured
 raw-handler parent before {queried = queried} {captured} actual absent found
   with lookup parent (S.admissions (M.world (O.core (B.source before)))) in owned
 ... | nothing = case actual of λ ()
 ... | just row with lookup (S.child (S.request row)) (B.threads before)
 ...   | just _ = case actual of λ ()
 ...   | nothing with M.advance (M.admissionStep parent Admission.fork) (O.core (B.source before)) in sourceStep
 ...     | nothing = case actual of λ ()
 ...     | just next with lookup (S.child (S.request row)) (S.handlers (M.world next)) in installed
 ...       | nothing = case actual of λ ()
 ...       | just handler with just-injective actual
 ...         | refl with Reconstruction.fork-PC parent (O.core (B.source before)) sourceStep
 ...           | request , saved , promise , entry , beforePC with just-injective (trans (sym owned) beforePC)
 ...             | refl with put-identifies (S.child request) queried handler (Effects.physical before) captured absent
   (trans (sym (cong (lookup queried) (Effects.captures-put (S.child request) (H.handlerThread handler H.maskedSetup) (B.threads before)))) found)
 ...               | workerEq , captureEq = record
   { request = request; heldLease = saved; promise = promise; entry = entry; before-PC = beforePC
   ; source = sourceStep; worker = workerEq
   ; descriptor = trans (sym captureEq) (just-injective (trans (sym installed)
       (fork-installed parent request saved promise entry (O.core (B.source before)) beforePC sourceStep))) }

 raw-inbound : ∀ parent before {after queried captured} →
   B.step (B.handler (H.run (M.admissionStep parent Admission.fork))) before ≡ just after →
   lookup queried (Effects.physical before) ≡ nothing → lookup queried (Effects.physical after) ≡ just captured →
   RawInbound parent before after queried captured
 raw-inbound parent before actual absent found with B.handlerAllowed (H.run (M.admissionStep parent Admission.fork)) before
 ... | false = case actual of λ ()
 ... | true with H.step (H.run (M.admissionStep parent Admission.fork)) (B.view before) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → raw-handler parent before advanced absent found }


import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxExitCancellation as CancellationModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as ServerModel
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.InboundOriginRuntime as Runtime

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module K = Combined b io using (source; step; serverStep; serverAllowed; server; coreStep; coreAllowed; coreAction)
  module T = Combined.Protocols b io capability using (Runtime; Event; Runs; stop; more; advance; base; enact; inherit; complete; front)
  module Back = Backing.Frontend b io capability using (Backing; ForkStep; PlanSelected; Selected; cache-same; catch-state; chosen-birth; completing-birth; delta-state; exit-enact; exit-state; fork-step; frontend-enact; group-state; ig-enact; ig-state; inherited-birth; job-state; monitor-state; mux-fork; mux-state; physical-state; publication-state; retarget; server-scope-enact; server-state; shared-state; unwind-enact; unwind-state; view)
 core : T.Runtime → M.Configuration
 core state = O.core (K.source (T.base state))
 record Inbound (before born : T.Runtime) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   parent : WorkerId
   request : S.Admission
   heldLease : S.Lease
   promise : PromiseId
   entry : EntryId
   before-PC : lookup parent (S.admissions (M.world (core before))) ≡ just (S.admissionWorker request (S.forkHandler heldLease promise entry))
   source : M.advance (M.admissionStep parent Admission.fork) (core before) ≡ just (core born)
   worker : queried ≡ S.child request
   descriptor : captured ≡ S.handlerStart entry (S.socketRef request) promise (S.key request)
 record Outbound (before born : T.Runtime) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   caller : WorkerId
   target : B.State
   enabled : B.step (B.outbound (O.acquire caller Acquire.forkOK)) (Back.physical-state before) ≡ just target
   at-physical-fork : lookup queried (Effects.physical target) ≡ just captured
 record Decomposition (start current : T.Runtime) (events : List T.Event) (queried : WorkerId) (captured : S.HandlerStart) : Set where
  field
   before born : T.Runtime
   label : T.Event
   prefix suffix : List T.Event
   decomposition : events ≡ prefix ++ (label ∷ suffix)
   prefix-run : T.Runs start prefix before
   actual : T.advance label before ≡ just born
   suffix-run : T.Runs born suffix current
   branch : Inbound before born queried captured ⊎ Outbound before born queried captured

 private
  module U = MuxModel Types.TypedResult using (State; step; run; source; base)
  module P = ProtocolModel using (State; step; run; source; base)
  module Monitor = MonitorModel b using (State; step; run; source; base)
  module G = GroupModel b using (State; step; run; source; base)
  module W = ExitModel b using (State; step; run; choose; enact; inherited; control; resultReady; shutdown; shared; source; base)
  module X = CancellationModel b using (step; run)
  module R = UnwindModel b using (State; step; choose; enact; inherited; acknowledge; source; base)
  module D = DeltaModel b using (State; step; run; allowed; source; base)
  module Catch = CatchModel b using (State; step; run; allowed; source; base)
  module N = PublicationModel b using (State; step; run; allowed; source; base)
  module SA = ServerModel b using (State; step; run; scope; allowed; chooseScope; physicalAction; enactScope; scopeAdvance; source; base)
  module E = IGExitModel b using (State; step; choose; enact; delegate; source; base)
  module Route = Effects.InheritedRoutes b using (mux-inherited; jobs-inherited; monitor-inherited; group-inherited)
  module EL = Effects.ExitLayer b using (Selected; PlanSelected; chosen-birth; inherited-plan; CIPaths; ci-control-projects)
  module XL = Effects.CancellationLayer b using (Selected; inherited-birth)
  module RL = Effects.UnwindLayer b using (Selected; PlanSelected; chosen-birth; inherited-plan; acknowledged-plan)
  module DL = Effects.DeltaQLayer b using (Selected; inherited-birth)
  module CL = Effects.CatchLayer b using (Selected; inherited-birth)
  module NL = Effects.PublicationLayer b using (Selected; inherited-birth)
  module SL = Effects.ServerLayer b using (Selected; inherited-birth; scoped-birth)
  module IL = Effects.IGExitLayer b using (Selected; PlanSelected; chosen-birth; delegated-birth)
  module KL = Effects.SharedLayer b io using (Selected; server-birth; core-birth)
  module Cache = Runtime.Frontend b io capability using (cache-core)
 source-at : ∀ {before after} → Back.ForkStep before after → M.Configuration
 source-at operation = O.core (B.source (Back.ForkStep.target operation))
 -- Package the selected operation without indexing the result by its proof.
 -- This keeps selector case analysis from abstracting an occurrence of itself.
 record SourceFork (before : B.State) (after : Effects.Registry) (afterCore : M.Configuration) : Set where
  constructor source-fork
  field
   operation : Back.ForkStep before after
   source-after : source-at operation ≡ afterCore
 -- Retargeting alters only the capture-map equality in the certificate.
 retarget-source : ∀ {before after next} same (operation : Back.ForkStep before after) →
   source-at (Back.retarget {next = next} same operation) ≡ source-at operation
 retarget-source same (Back.fork-step command target enabled kind capturesAfter) = refl
 mux-source : ∀ action state {after} (actual : U.step action state ≡ just after) (selected : Effects.MuxLayer.Selected action) →
   SourceFork (Back.mux-state state) (Effects.MuxLayer.view after) (O.core (U.source after))
 mux-source (U.run action) state actual (Effects.MuxLayer.inherited-birth selected) = source-fork (Back.mux-fork (U.run action) state actual (Effects.MuxLayer.inherited-birth selected)) refl
 job-source : ∀ action state {after} (actual : P.step action state ≡ just after) (selected : Effects.ProtocolLayer.Selected action) →
   SourceFork (Back.job-state state) (Effects.ProtocolLayer.view after) (O.core (P.source after))
 job-source (P.run action) state actual (Effects.ProtocolLayer.inherited-birth selected) =
   mux-source action (P.base state) (Route.jobs-inherited action state actual) selected
 monitor-source : ∀ action state {after} (actual : Monitor.step action state ≡ just after) (selected : Effects.MonitorLayer.Selected b action) →
   SourceFork (Back.monitor-state state) (Effects.MonitorLayer.view b after) (O.core (Monitor.source after))
 monitor-source (Monitor.run action) state actual (Effects.MonitorLayer.inherited-birth selected) =
   job-source action (Monitor.base state) (Route.monitor-inherited action state actual) selected
 group-source : ∀ action state {after} (actual : G.step action state ≡ just after) (selected : Effects.GroupLayer.Selected b action) →
   SourceFork (Back.group-state state) (Effects.GroupLayer.view b after) (O.core (G.source after))
 group-source (G.run action) state actual (Effects.GroupLayer.inherited-birth selected) =
   monitor-source action (G.base state) (Route.group-inherited action state actual) selected
 exit-enact-source : ∀ plan state {after} (actual : W.enact plan state ≡ just after) (selected : EL.PlanSelected plan state) →
   SourceFork (Back.exit-state state) (Effects.ExitLayer.view b after) (O.core (W.source after))
 exit-enact-source (W.inherited action) state actual (EL.inherited-plan selected) with G.step action (W.base state) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → group-source action (W.base state) advanced selected }
 exit-source : ∀ action state {after} (actual : W.step action state ≡ just after) (selected : EL.Selected action state) →
   SourceFork (Back.exit-state state) (Effects.ExitLayer.view b after) (O.core (W.source after))
 exit-source action state actual (EL.chosen-birth {plan} chosen selected) =
   exit-enact-source plan state (Back.exit-enact action plan state chosen actual) selected
 cancel-source : ∀ action state {after} (actual : X.step action state ≡ just after) (selected : XL.Selected action state) →
   SourceFork (Back.exit-state state) (Effects.CancellationLayer.view b after) (O.core (W.source after))
 cancel-source (X.run action) state actual (XL.inherited-birth selected) = exit-source action state actual selected
 -- A coordinator acknowledgement changes only coordinator metadata.
 control-source : ∀ action state {after} → W.control action state ≡ just after → W.source after ≡ W.source state
 control-source action state actual with Close.step (S.cm (W.shared state)) (λ worker → W.resultReady worker state) action (W.shutdown state)
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → refl }
 unwind-enact-source : ∀ plan state {after} (actual : R.enact plan state ≡ just after) (selected : RL.PlanSelected plan state) →
   SourceFork (Back.unwind-state state) (Effects.UnwindLayer.view b after) (O.core (R.source after))
 unwind-enact-source (R.inherited action) state actual (RL.inherited-plan selected) with X.step action (R.base state) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → cancel-source action (R.base state) advanced selected }
 unwind-enact-source (R.acknowledge plan) state actual (RL.acknowledged-plan selected) with R.enact plan state in advanced
 ... | nothing = case actual of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case actual of λ ()
 ...   | just exit = case just-injective actual of λ { refl → source-fork
   (Back.retarget (sym (EL.CIPaths.retention (EL.ci-control-projects Close.acknowledgeDelivery (R.base next) acknowledged)))
     (SourceFork.operation (unwind-enact-source plan state advanced selected)))
   (trans (retarget-source (sym (EL.CIPaths.retention (EL.ci-control-projects Close.acknowledgeDelivery (R.base next) acknowledged)))
       (SourceFork.operation (unwind-enact-source plan state advanced selected)))
     (trans (SourceFork.source-after (unwind-enact-source plan state advanced selected))
       (sym (cong O.core (control-source Close.acknowledgeDelivery (R.base next) acknowledged))))) }

 unwind-source : ∀ action state {after} (actual : R.step action state ≡ just after) (selected : RL.Selected action state) →
   SourceFork (Back.unwind-state state) (Effects.UnwindLayer.view b after) (O.core (R.source after))
 unwind-source action state actual (RL.chosen-birth {plan} chosen selected) =
   unwind-enact-source plan state (Back.unwind-enact action plan state chosen actual) selected
 delta-source : ∀ action state {after} (actual : D.step action state ≡ just after) (selected : DL.Selected action state) →
   SourceFork (Back.delta-state state) (Effects.DeltaQLayer.view b after) (O.core (D.source after))
 delta-source (D.run action) state actual (DL.inherited-birth selected) with D.allowed action state
 ... | false = case actual of λ ()
 ... | true with R.step action (D.base state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → unwind-source action (D.base state) advanced selected }
 catch-source : ∀ action state {after} (actual : Catch.step action state ≡ just after) (selected : CL.Selected action state) →
   SourceFork (Back.catch-state state) (Effects.CatchLayer.view b after) (O.core (Catch.source after))
 catch-source (Catch.run action) state actual (CL.inherited-birth selected) with Catch.allowed action
 ... | false = case actual of λ ()
 ... | true with D.step action (Catch.base state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → delta-source action (Catch.base state) advanced selected }
 publication-source : ∀ action state {after} (actual : N.step action state ≡ just after) (selected : NL.Selected action state) →
   SourceFork (Back.publication-state state) (Effects.PublicationLayer.view b after) (O.core (N.source after))
 publication-source (N.run action) state actual (NL.inherited-birth selected) with N.allowed action state
 ... | false = case actual of λ ()
 ... | true with Catch.step action (N.base state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → catch-source action (N.base state) advanced selected }
 -- The remaining wrappers change only local scope/context/frontend metadata
 -- around the selected physical operation. Keep its actual core endpoints.
 server-scope-source : ∀ action plan command state {after}
   (chosen : SA.chooseScope action state ≡ just plan)
   (selected : SA.physicalAction plan ≡ just command)
   (actual : SA.enactScope plan state ≡ just after)
   (witness : NL.Selected command (SA.base state)) →
   SourceFork (Back.server-state state) (Effects.ServerLayer.view b after) (O.core (SA.source after))
 server-scope-source action plan command state chosen selected actual witness with SA.physicalAction plan
 ... | nothing = case selected of λ ()
 ... | just operation with just-injective selected
 ...   | refl with N.step command (SA.base state) in advanced
 ...     | nothing = case actual of λ ()
 ...     | just next = case just-injective actual of λ { refl → publication-source command (SA.base state) advanced witness }
 server-source : ∀ action state {after} (actual : SA.step action state ≡ just after) (selected : SL.Selected action state) →
   SourceFork (Back.server-state state) (Effects.ServerLayer.view b after) (O.core (SA.source after))
 server-source (SA.run action) state actual (SL.inherited-birth selected) with SA.allowed action state
 ... | false = case actual of λ ()
 ... | true with N.step action (SA.base state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → publication-source action (SA.base state) advanced selected }
 server-source (SA.scope action) state actual (SL.scoped-birth {p = plan} {command} chosen selected witness) =
   server-scope-source action plan command state chosen selected (Back.server-scope-enact action plan state chosen actual) witness

 ig-enact-source : ∀ plan state {after} (actual : E.enact plan state ≡ just after) (selected : IL.PlanSelected plan state) →
   SourceFork (Back.ig-state state) (Effects.IGExitLayer.view b after) (O.core (E.source after))
 ig-enact-source (E.delegate action exit) state actual (IL.delegated-birth selected) with SA.step action (E.base state) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → server-source action (E.base state) advanced selected }
 ig-source : ∀ action state {after} (actual : E.step action state ≡ just after) (selected : IL.Selected action state) →
   SourceFork (Back.ig-state state) (Effects.IGExitLayer.view b after) (O.core (E.source after))
 ig-source action state actual (IL.chosen-birth {plan} chosen selected) =
   ig-enact-source plan state (Back.ig-enact action plan state chosen actual) selected

 shared-source : ∀ action state {after} (actual : K.step action state ≡ just after) (selected : KL.Selected action state) →
   SourceFork (Back.shared-state state) (Effects.SharedLayer.view b io after) (O.core (K.source after))
 shared-source (K.serverStep action) state actual (KL.server-birth selected) with K.serverAllowed action state
 ... | false = case actual of λ ()
 ... | true with E.step action (K.server state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → ig-source action (K.server state) advanced selected }
 shared-source (K.coreStep action) state actual (KL.core-birth selected) with K.coreAllowed action state
 ... | false = case actual of λ ()
 ... | true with E.step (K.coreAction action) (K.server state) in advanced
 ...   | nothing = case actual of λ ()
 ...   | just next = case just-injective actual of λ { refl → ig-source (K.coreAction action) (K.server state) advanced selected }

 enact-source : ∀ plan state {after} (actual : T.enact plan state ≡ just after) (selected : Back.PlanSelected plan state) →
   SourceFork (Back.physical-state state) (Back.view after) (core after)
 enact-source (T.inherit action front) state actual (Back.inherited-birth selected) with K.step action (T.base state) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → shared-source action (T.base state) advanced selected }
 enact-source (T.complete action rid capturedCall result) state actual (Back.completing-birth selected) with K.step action (T.base state) in advanced
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → source-fork
   (Back.retarget (sym (Back.cache-same rid capturedCall result (T.front state) next))
     (SourceFork.operation (shared-source action (T.base state) advanced selected)))
   (trans (retarget-source (sym (Back.cache-same rid capturedCall result (T.front state) next))
       (SourceFork.operation (shared-source action (T.base state) advanced selected)))
     (trans (SourceFork.source-after (shared-source action (T.base state) advanced selected))
       (sym (Cache.cache-core rid capturedCall result (T.front state) next)))) }

 actual-source : ∀ action state {after} (actual : T.advance action state ≡ just after) (selected : Back.Selected action state) →
   SourceFork (Back.physical-state state) (Back.view after) (core after)
 actual-source action state actual (Back.chosen-birth {plan} chosen selected) =
   enact-source plan state (Back.frontend-enact action plan state chosen actual) selected
 -- Convert only the existing search trace datatype, retaining each actual label.
 private
  module Search = Backing.Frontend.LocatedSearch b io capability using (Runs; done; next)
  module L = Backing.Frontend.LocatedSearch.Located b io capability using (before; after; action; prefix; suffix; decomposition; prefix-run; actual; selected; absent-before; at-birth; suffix-run)
 from-runs : ∀ {before events after} → Search.Runs before events after → T.Runs before events after
 from-runs Search.done = T.stop
 from-runs (Search.next actual rest) = T.more actual (from-runs rest)

 -- The source equation is annotated over all certified wrappers, rather than
 -- assuming that a selected event has either of two convenient syntactic forms.
 operation-owner : ∀ before born {registry queried captured}
   (operation : Back.ForkStep (Back.physical-state before) registry) → source-at operation ≡ core born →
   lookup queried (Effects.physical (Back.physical-state before)) ≡ nothing →
   lookup queried (Effects.physical (Back.ForkStep.target operation)) ≡ just captured →
   Inbound before born queried captured ⊎ Outbound before born queried captured
 operation-owner before born (Back.fork-step _ target enabled (Effects.inbound-physical parent) _) sourceAfter absent found = inj₁ (record
   { parent = parent; request = RawInbound.request owner; heldLease = RawInbound.heldLease owner
   ; promise = RawInbound.promise owner; entry = RawInbound.entry owner; before-PC = RawInbound.before-PC owner
   ; source = trans (RawInbound.source owner) (cong just sourceAfter)
   ; worker = RawInbound.worker owner; descriptor = RawInbound.descriptor owner })
   where owner = raw-inbound parent (Back.physical-state before) enabled absent found
 operation-owner before born (Back.fork-step _ target enabled (Effects.outbound-physical caller) _) sourceAfter absent found = inj₂ (record
   { caller = caller; target = target; enabled = enabled; at-physical-fork = found })

 classify : ∀ {start current events queried captured} (history : Back.Backing start current events queried captured) →
   Inbound (L.before (Back.Backing.location history)) (L.after (Back.Backing.location history)) queried captured ⊎
   Outbound (L.before (Back.Backing.location history)) (L.after (Back.Backing.location history)) queried captured
 classify {queried = queried} history = operation-owner (L.before location) (L.after location) (SourceFork.operation observed)
   (SourceFork.source-after observed) (L.absent-before location)
   (trans (cong (lookup queried) (Back.ForkStep.captures-after (SourceFork.operation observed))) (L.at-birth location))
   where
   location = Back.Backing.location history
   observed = actual-source (L.action location) (L.before location) (L.actual location) (L.selected location)

 -- Every field is copied from the located birth; no trace is searched again.
 decompose : ∀ {start current events queried captured} → Back.Backing start current events queried captured →
   Decomposition start current events queried captured
 decompose history = record
   { before = L.before location; born = L.after location; label = L.action location
   ; prefix = L.prefix location; suffix = L.suffix location; decomposition = L.decomposition location
   ; prefix-run = from-runs (L.prefix-run location); actual = L.actual location
   ; suffix-run = from-runs (L.suffix-run location); branch = classify history }
   where location = Back.Backing.location history
