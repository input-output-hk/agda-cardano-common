{-# OPTIONS --guardedness #-}

-- Joint job/pool-content preservation at every typed protocol writer.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxMonitor (b : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
import Data.Empty
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as WireMux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.MuxProtocolJobs as Old
import ConnectionManagement.Properties.LiveTrackerAuxContent as Aux
import ConnectionManagement.Properties.LiveTrackerAuxTransport as Trans
import ConnectionManagement.Properties.LiveTrackerAuxUpdates as Updates
import ConnectionManagement.Properties.LiveTrackerAuxProtocol as Protocol
import ConnectionManagement.MuxResultMonitor as Monitor
import ConnectionManagement.Properties.MuxResultMonitor as MonitorFacts
module A = Aux b
module T = Trans b
module Up = Updates b
module U = P.U
module Pool = P.Pool
module Startup = P.Startup
open T using (Retains; job-kept; completion-kept; job-phase)

module W = Monitor b
module F = MonitorFacts b
PCs : ConnectionManagement.Store.Store WorkerId W.PC → P.State → Set
PCs rows s = All (λ { (w , pc) → A.PCContent w pc s }) rows
Plain : W.PC → Set
Plain pc = ∀ item → pc ≢ W.selected item
plain-content : ∀ w pc s → A.Owner w s → Plain pc → A.PCContent w pc s
plain-content w pc s own plain = record { owner-reference = own; selected-backed = λ item eq → Data.Empty.⊥-elim (plain item eq) }
owner-frame : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → lookup w (U.frames (P.base (W.base s))) ≡ just f
owner-frame w s actual with lookup w (U.frames (P.base (W.base s))) in found
... | nothing = case actual of λ ()
... | just f with U.progress f | P.monitoring f
...   | U.promisePublished hid mid | true = case just-injective actual of λ { refl → refl }
...   | U.promisePublished hid mid | false = case actual of λ ()
...   | (U.handshakePending helperPC) | _ = case actual of λ ()
...   | U.returnedSuccess | _ = case actual of λ ()
...   | U.handleAllocated hid mid | _ = case actual of λ ()

module For (Obs : P.State → Set) (stable : ∀ {s t} → Retains s t → Obs s → Obs t) where
 Valid : W.State → Set
 Valid s = Up.Valid (W.base s) × (PCs (W.pcs s) (W.base s) × Obs (W.base s))
 observer : ∀ rows {s t} → Retains s t → PCs rows s × Obs s → PCs rows t × Obs t
 observer rows kept (pcs , observed) = All.map (λ { {w , pc} → T.pc-kept kept w pc }) pcs , stable kept observed
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s (core , observed) = Up.source-valid c (W.base s) core , observer _ (T.source c (W.base s)) observed
 pc-valid : ∀ w pc s → A.PCContent w pc (W.base s) → Valid s → Valid (W.setPC w pc s)
 pc-valid w pc s good (core , pcs , observed) = core , T.Rows.insert (λ w pc → A.PCContent w pc (W.base s)) w pc (W.pcs s) good pcs , observed
 record CIPaths (s t : W.State) : Set where
  constructor paths
  field preserves : Valid s → Valid t
        retention : Valid s → Retains (W.base s) (W.base t)
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid) (λ valid → T.identity (W.base s))
 ci-compose : ∀ {s t u} → CIPaths s t → CIPaths t u → CIPaths s u
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
   (λ valid → T.compose (CIPaths.retention first valid) (CIPaths.retention second (CIPaths.preserves first valid)))
 ci-pc-paths : ∀ w pc s → A.Owner w (W.base s) → Plain pc → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s own plain = paths (pc-valid w pc s (plain-content w pc _ own plain)) (λ valid → T.identity (W.base s))
 ci-pc-after : ∀ w pc {before after} → A.Owner w (W.base before) → Plain pc → CIPaths before after → CIPaths before (W.setPC w pc after)
 ci-pc-after w pc {after = after} own plain path = paths
   (λ valid → pc-valid w pc after (plain-content w pc _ (proj₁ (Retains.owners (CIPaths.retention path valid) w own)) plain) (CIPaths.preserves path valid))
   (CIPaths.retention path)
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s actual = paths (source-valid _ s) (λ valid → T.source _ (W.base s))
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Protocol.For.step-preserves b (λ p → PCs (W.pcs s) p × Obs p) (observer _) a (W.base s) actual valid }
 ci-via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-select-projects : ∀ w s {t} → W.selectHead w s ≡ just t → CIPaths s t
 ci-select-projects w s actual with F.consume-observation w s actual
 ... | observation rewrite F.Dequeue.after-shape observation = paths preserves (λ valid → kept)
   where
   f = F.Dequeue.ownerFrame observation
   pool = F.Dequeue.poolAfter observation
   item = F.Dequeue.head observation
   found = owner-frame w s (F.Dequeue.context-before observation)
   changed = F.Dequeue.actual-consumption observation
   kept = Up.pool-retains w f pool (W.base s) found (Up.Kernel.handles-retained Pool.consumeCompletion (P.poolAt w (W.base s)) changed)
   preserves : Valid s → Valid (W.setPC w (W.selected item) (W.setPool w f pool s))
   preserves valid = pc-valid w (W.selected item) (W.setPool w f pool s)
     (record { owner-reference = proj₁ (Retains.owners kept w (A.owner-context w s (F.Dequeue.context-before observation)))
             ; selected-backed = λ { other refl → payload } })
     (Protocol.For.pool-valid b (λ p → PCs (W.pcs s) p × Obs p) (observer _) w f Pool.consumeCompletion (W.base s) found changed tt valid)
     where
     payload = completion-kept kept w item (All.head
       (subst (All (λ item → A.Completion w item (W.base s))) (F.Dequeue.original-queue observation)
         (A.PoolContent.queued (Up.Valid.pools (proj₁ valid) w))))
 ci-protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → A.Owner w (W.base s) → CIPaths s s′
 ci-protocol-source-projects w mid WireMux.responderJob n outcome s eq own with W.muxAt mid s
 ... | nothing = case eq of λ ()
 ... | just m with W.legacyMatches n outcome (WireMux.completions m)
 ...   | false = case eq of λ ()
 ...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-pc-after w (W.responderTracing outcome) own (λ item ()) (ci-via-projects (IG.monitorCompletion mid) s advanced) }
 ci-protocol-source-projects w mid WireMux.initiatorJob n clean s eq own = case just-injective eq of λ { refl → ci-pc-paths w (W.initiatorTracing clean) s own (λ item ()) }
 ci-protocol-source-projects w mid WireMux.initiatorJob n (errored err) s eq own with W.viaSource (IG.recordMuxFailure mid err) s in advanced
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → ci-pc-after w (W.initiatorTracing (errored err)) own (λ item ()) (ci-via-projects (IG.recordMuxFailure mid err) s advanced) }
 ci-handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → CIPaths s s′
 ci-handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s in context | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
 ... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
 ...   | true | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned = ci-protocol-source-projects w mid dir n outcome s eq (A.owner-context w s context)
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopping | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.stopped | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.failed err | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterStart k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.forkPending k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | just m | WireMux.ready | WireMux.tracerFailed k = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | false | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just (f , mid) | just (j , job) | true | nothing = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | nothing | _ = case eq of λ ()
 ci-handle-protocol-projects w dir n gen outcome s eq | just _ | nothing = case eq of λ ()
 ci-record-finish-projects : ∀ w outcome s {s′} → W.recordFinish w outcome s ≡ just s′ → CIPaths s s′
 ci-record-finish-projects w outcome s eq with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadReady outcome) (A.owner-context w s context) (λ item ()) (ci-via-projects (W.statusAction outcome mid) s advanced) }
 ci-handle-projects : ∀ w s {s′} → W.handleHead w s ≡ just s′ → CIPaths s s′
 ci-handle-projects w s eq with W.pcAt w s
 ... | W.selected (Types.protocolCompletion dir n gen outcome) = ci-handle-protocol-projects w dir n gen outcome s eq
 ... | W.selected (Types.infraMuxer err) = ci-record-finish-projects w (W.failed err) s eq
 ... | W.selected (Types.infraDemuxer err) = ci-record-finish-projects w (W.demuxFinish w err s) s eq
 ... | W.waiting = case eq of λ ()
 ... | W.responderTracing _ = case eq of λ ()
 ... | W.initiatorTracing _ = case eq of λ ()
 ... | W.deadReady _ = case eq of λ ()
 ... | W.deadTracing _ = case eq of λ ()
 ... | W.finished _ = case eq of λ ()
 ci-trace-projects : ∀ sample w s {s′} → W.traceSource sample w s ≡ just s′ → CIPaths s s′
 ci-trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s in context
 ... | true | just (f , mid) with sample
 ...   | true = ci-via-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-projects (IG.commitTracer mid) s eq
 ci-trace-projects sample w s eq | false | _ = case eq of λ ()
 ci-trace-projects sample w s eq | true | nothing = case eq of λ ()
 ci-finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → CIPaths s s′
 ci-finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s (A.owner-context w s context) (λ item ()) }
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.afterFailure = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s (A.owner-context w s context) (λ item ()) }
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.returned = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s (A.owner-context w s context) (λ item ()) }
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s (A.owner-context w s context) (λ item ()) }
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing result | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-start-dead-projects : ∀ w s {s′} → W.startDead w s ≡ just s′ → CIPaths s s′
 ci-start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with W.finishMatches outcome (WireMux.status m) | W.deadAction outcome (WireMux.callback m) mid
 ...     | true | just action with W.viaSource action s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadTracing outcome) (A.owner-context w s context) (λ item ()) (ci-via-projects action s advanced) }
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | false | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | just m | true | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | just (f , mid) | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadReady outcome | nothing = case eq of λ ()
 ci-start-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-start-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()
 ci-finish-dead-projects : ∀ w s {s′} → W.finishMux w s ≡ just s′ → CIPaths s s′
 ci-finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with WireMux.callback m | W.finishMatches outcome (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-pc-paths w (W.finished outcome) s (A.owner-context w s context) (λ item ()) }
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | just m | WireMux.returned | false = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | just (f , mid) | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadTracing outcome | nothing = case eq of λ ()
 ci-finish-dead-projects w s eq | W.waiting | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-finish-dead-projects w s eq | W.finished outcome | _ = case eq of λ ()

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.consume w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.handleSelected w) s eq = CIPaths.preserves (ci-handle-projects w s eq)
 step-preserves (W.sampleTracer w) s eq = CIPaths.preserves (ci-trace-projects true w s eq)
 step-preserves (W.commitTracer w) s eq = CIPaths.preserves (ci-trace-projects false w s eq)
 step-preserves (W.finishProtocolTrace w) s eq = CIPaths.preserves (ci-finish-protocol-projects w s eq)
 step-preserves (W.beginDead w) s eq = CIPaths.preserves (ci-start-dead-projects w s eq)
 step-preserves (W.finishDead w) s eq = CIPaths.preserves (ci-finish-dead-projects w s eq)
