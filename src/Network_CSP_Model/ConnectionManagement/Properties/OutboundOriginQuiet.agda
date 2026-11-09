{-# OPTIONS --guardedness #-}

-- Direct mux/protocol/monitor/group actions preserve the active acquisition
-- runtime. Only inherited outbound calls need acquisition-effect classification.
module ConnectionManagement.Properties.OutboundOriginQuiet where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG


-- Inbound writes leave the whole outbound acquisition runtime untouched.
inbound-same : ∀ action c {d} → O.advance (O.inbound action) c ≡ just d → ⊤ → O.acquiring d ≡ O.acquiring c
inbound-same action c eq quiet with Machine.advance action (O.core c)
... | nothing = case eq of λ ()
... | just next with just-injective eq
...   | refl = refl

module Mux where
 private module U = MuxModel Types.TypedResult using (Action; Frame; module Startup; State; advanceStartup; allocate; allocateHandle; configure; configureMux; registerFor; registerCounters; beforePool; allocationAction; base; baseAllowed; birth; birthFresh; flow; frames; handleAllocated; inherit; initial; negotiate; negotiateReturned; noteBirth; origins; progress; promisePublished; publish; publishSuccess; returnedSuccess; run; setupFor; scheduled; nextSetup; setup; egressSetup; whenSetupDone-just; setFrame; setSource; source; startup; startupAllowed; startupStep; step)
 private module Startup = U.Startup using (observePublication; step)
 table : U.State → Acquire.Runtime
 table s = O.acquiring (U.source s)
 negotiate-same : ∀ w ps flow s {s′} → U.negotiateReturned w ps flow s ≡ just s′ → table s′ ≡ table s
 negotiate-same w ps flow s eq with lookup w (B.threads (U.base s)) |
   lookup w (U.origins s) | lookup w (U.frames s) in absent
 ... | just t | just origin | nothing with H.phase t
 ...   | H.handshaking = case just-injective eq of λ { refl → refl }
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.maskedSetup = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.caughtCancellation err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.cancellationPublished err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.bodyExited err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.finalizing err = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
 negotiate-same w ps flow s eq | nothing | origin | previous = case eq of λ ()
 negotiate-same w ps flow s eq | just t | nothing | previous = case eq of λ ()
 negotiate-same w ps flow s eq | just t | just origin | just previous = case eq of λ ()

 allocate-same : ∀ w hid mid s {s′} → U.allocate w hid mid s ≡ just s′ → table s′ ≡ table s
 allocate-same w hid mid s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → inbound-same (Machine.igStep (U.allocationAction f hid mid)) (U.source s) advanced tt }
 allocate-same w hid mid s eq | just f | U.handleAllocated oldHandle oldMux = case eq of λ ()
 allocate-same w hid mid s eq | just f | U.promisePublished oldHandle oldMux = case eq of λ ()

 -- Configured egress installation writes only the actual allocated mux.
 configure-same : ∀ w plan limit bound keys s {s′} → U.configure w plan limit bound keys s ≡ just s′ → table s′ ≡ table s
 configure-same w EgressLayout.plainLayout limit bound keys s eq = case eq of λ ()
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance (O.inbound (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → inbound-same (Machine.igStep (IG.configureEgress mid (EgressLayout.scheduledLayout slice) limit bound keys)) (U.source s) advanced tt }
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.returnedSuccess = case eq of λ ()
 configure-same w (EgressLayout.scheduledLayout slice) limit bound keys s eq | just f | U.promisePublished h m = case eq of λ ()

 -- Counter registration writes only the actual IG registry.
 register-same : ∀ w s {s′} → U.registerFor w s ≡ just s′ → table s′ ≡ table s
 register-same w s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.beforePool (U.Startup.phase (U.startup f))
 ...   | U.promisePublished hid mid | true with O.advance (O.inbound (Machine.igStep (IG.registerCells mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → inbound-same (Machine.igStep (IG.registerCells mid)) (U.source s) advanced tt }
 register-same w s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 register-same w s eq | just f | U.returnedSuccess | _ = case eq of λ ()
 register-same w s eq | just f | U.handleAllocated h m | _ = case eq of λ ()

 setup-same : ∀ w s {s′} → U.setupFor w s ≡ just s′ → table s′ ≡ table s
 setup-same w s eq with lookup w (U.frames s)
 ... | nothing = case eq of λ ()
 ... | just f with U.scheduled f (U.source s) | U.nextSetup (U.setup f)
 ...   | true | just next = case just-injective eq of λ { refl → refl }
 ...   | true | nothing = case eq of λ ()
 ...   | false | _ = case eq of λ ()
 publish-same : ∀ w s {s′} → U.publish w s ≡ just s′ → table s′ ≡ table s
 publish-same w s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f) in progressed
 ...     | just c | just next = case just-injective eq of λ { refl → inbound-same (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten) (U.source s) advanced tt }
 publish-same w s eq | just f | U.handleAllocated hid mid | nothing | startupResult = case eq of λ ()
 publish-same w s eq | just f | U.handleAllocated hid mid | just c | nothing = case eq of λ ()
 publish-same w s eq | just f | U.returnedSuccess = case eq of λ ()
 publish-same w s eq | just f | U.promisePublished hid mid = case eq of λ ()

 startup-shutdown : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → table t ≡ table s
 startup-shutdown w a s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.startupAllowed a f s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f)
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → refl }
 startup-shutdown w a s eq | just f | U.returnedSuccess | allowed = case eq of λ ()
 startup-shutdown w a s eq | just f | U.handleAllocated hid mid | allowed = case eq of λ ()
 startup-shutdown w a s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 IsDirect : U.Action → Set
 IsDirect (U.run a) = ⊥
 IsDirect _ = ⊤
 direct-same : ∀ a s {t} → U.step a s ≡ just t → IsDirect a → table t ≡ table s
 direct-same (U.run a) s eq ()
 direct-same (U.negotiate w ps flow) s eq direct = negotiate-same w ps flow s eq
 direct-same (U.allocateHandle w hid mid) s eq direct = allocate-same w hid mid s eq
 direct-same (U.configureMux w plan limit bound keys) s eq direct = configure-same w plan limit bound keys s eq
 direct-same (U.registerCounters w) s eq direct = register-same w s eq
 direct-same (U.egressSetup w) s eq direct = setup-same w s eq
 direct-same (U.publishSuccess w) s eq direct = publish-same w s (U.whenSetupDone-just w s (U.publish w s) eq)
 direct-same (U.startupStep w a) s eq direct = startup-shutdown w a s eq


import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as WireMux
import Data.Nat as Nat

module Protocol where
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; bodySource; publicationSource; locate; pendingAt; sameOutcome; Action; module Pool; module Startup; State; module U; appendPending; asyncInfraResult; asyncProtocolResult; base; commitClean; control; controlReady; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infraId; infrastructureReturn; inherit; inheritedAllowed; initial; jobs; monitorControl; monitoring; muxAt; noParent; poolAt; protocolException; protocolReturned; unlessAwaiting-just; publishInfra; publishProtocol; register; registerProtocol; removePublished; returnProtocol; returned; run; setPool; setSource; source; sourceControl; step; viaInfra; viaProtocol; viaDb; viaDb-source; submitDb-via; awaitDb-via; dbFailure-via; DbFailure; refused; abandoned; submitDbWrite; awaitDbWrite; dbWriteFailed; writerComplete; writerSeal)
 private module U = P.U using (base; frames; handleAllocated; initial; progress; promisePublished; returnedSuccess; startup; step)
 private module Pool = P.Pool using (bodyReturnedWith; deregister; parentFork; publishAsyncResult; publishCompletion; register; step)
 private module Startup = P.Startup using (phase)
 private module Old = ProtocolProperties using (EgressChange; enter-observation; send-observation; muxer-egress-observation; ForkSource; responderSource; initiatorSource; BodyReturn; CompletionCommit; Fork; Publication; clean-observation; exception-observation; initiator-fork-observation; publication-observation; responder-fork-observation; return-observation)
 table : P.State → Acquire.Runtime
 table s = O.acquiring (P.source s)
 fork-same : ∀ w j gen s {t} → Old.Fork w j gen s t → table t ≡ table s
 fork-same w j gen s observation rewrite Old.Fork.after-shape observation with Old.Fork.source-boundary observation
 ... | Old.responderSource m found callback advanced = inbound-same (Machine.igStep (IG.forkResponder (Old.Fork.capturedMux observation))) (P.source s) advanced tt
 ... | Old.initiatorSource descriptor found unchanged = cong (λ c → O.acquiring c) unchanged
 pending-table : ∀ job j s → table (P.appendPending job j s) ≡ table s
 pending-table job j s with Types.direction job
 ... | WireMux.initiatorJob = refl
 ... | WireMux.responderJob = refl
 removed-table : ∀ job kept s → table (P.removePublished job kept s) ≡ table s
 removed-table job kept s with Types.direction job
 ... | WireMux.initiatorJob = refl
 ... | WireMux.responderJob = refl
 body-source-same : ∀ job result s {c} → P.bodySource job result s ≡ just c → O.acquiring c ≡ table s
 body-source-same job result s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob = inbound-same (Machine.igStep (IG.finishProtocol (Types.mux job) (Types.protocolNumber job) result)) (P.source s) eq tt
 publication-source-same : ∀ j job result s {c kept} → P.publicationSource j job result s ≡ just (c , kept) → O.acquiring c ≡ table s
 publication-source-same j job result s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → refl }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) s) | P.muxAt (Types.mux job) s
 ...   | just (i , pendingRest) | just m with IG.takePending i (WireMux.finishedJobs m)
 ...     | just ((n , outcome) , rest) with does (Types.protocolNumber job Nat.≟ n) ∧ P.sameOutcome result outcome
 ...       | true with O.advance (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (P.source s) in advanced
 ...         | just c = case just-injective eq of λ { refl → inbound-same (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i)) (P.source s) advanced tt }
 ...         | nothing = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just (i , pendingRest) | just m | just ((n , outcome) , rest) | false = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just (i , pendingRest) | just m | nothing = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 publication-source-same j job result s eq | WireMux.responderJob | just _ | nothing = case eq of λ ()
 commit-same : ∀ j s {t} → Old.CompletionCommit j s t → table t ≡ table s
 commit-same j s observation rewrite Old.CompletionCommit.after-shape observation =
  trans (pending-table (Old.CompletionCommit.capturedJob observation) j _)
   (body-source-same (Old.CompletionCommit.capturedJob observation) (Old.CompletionCommit.outcome observation) s (Old.CompletionCommit.actual-source-commit observation))
 returned-body-same : ∀ j s {t} → Old.BodyReturn j s t → table t ≡ table s
 returned-body-same j s observation rewrite Old.BodyReturn.after-shape observation = refl
 published-same : ∀ j s {t} → Old.Publication j s t → table t ≡ table s
 published-same j s observation rewrite Old.Publication.after-shape observation =
  trans (removed-table (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _)
   (publication-source-same j (Old.Publication.capturedJob observation) (Old.Publication.outcome observation) s (Old.Publication.actual-source observation))
 returned-same : ∀ j s {t} → P.returned j s ≡ just t → table t ≡ table s
 returned-same j s eq with lookup j (P.jobs s) in found
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl →
   refl }
 returned-same j s eq | just job | Types.waitingEgress = case eq of λ ()
 returned-same j s eq | just job | Types.resultCaptured result = case eq of λ ()
 registered-same : ∀ j s {t} → P.register j s ≡ just t → table t ≡ table s
 registered-same j s eq with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → refl }
 registered-same j s eq | just job | nothing | _ = case eq of λ ()
 registered-same j s eq | just job | just f | nothing = case eq of λ ()

 via-protocol-same : ∀ j action s {t} → P.viaProtocol j action s ≡ just t → table t ≡ table s
 via-protocol-same j action s eq with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.step action (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → refl }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra-same : ∀ w role action s {t} → P.viaInfra w role action s ≡ just t → table t ≡ table s
 via-infra-same w role action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (action j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → refl }

 control-same : ∀ w action s {s′} → P.monitorControl w action s ≡ just s′ → table s′ ≡ table s
 control-same w action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady action m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl action mid))) (P.source s) in advanced
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → inbound-same (Machine.igStep (P.sourceControl action mid)) (P.source s) advanced tt }
 control-same w action s eq | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | true | false = case eq of λ ()

 -- Preserve the actual source step while observing the unchanged caller table.
 egress-same : ∀ s {t} → Old.EgressChange s t → table t ≡ table s
 egress-same s observation rewrite Old.EgressChange.after-shape observation =
  inbound-same (Machine.igStep (IG.egressStep (Old.EgressChange.capturedMux observation)
    (Old.EgressChange.operation observation))) (P.source s) (Old.EgressChange.actual-source observation) tt
 -- A DB queue/await step is a quiet IG source step.
 db-same : ∀ a s {t} → P.viaDb a s ≡ just t → table t ≡ table s
 db-same a s eq with P.viaDb-source a s eq
 ... | c , advanced , refl = inbound-same (Machine.igStep (IG.leiosDb a)) (P.source s) advanced tt
 IsDirect : P.Action → Set
 IsDirect (P.run a) = ⊥
 IsDirect _ = ⊤
 direct-same : ∀ a s {t} → P.step a s ≡ just t → IsDirect a → table t ≡ table s
 direct-same (P.run a) s eq ()
 direct-same (P.forkResponder w j gen) s eq direct = fork-same w j gen s (Old.responder-fork-observation w j gen s eq)
 direct-same (P.forkInitiator w j gen n) s eq direct = fork-same w j gen s (Old.initiator-fork-observation w j gen n s eq)
 direct-same (P.registerProtocol j) s eq direct = registered-same j s eq
 direct-same (P.enterProtocolBody j) s eq direct = egress-same s (Old.enter-observation j s eq)
 direct-same (P.appendProtocolPayload j bytes) s eq direct = egress-same s (Old.send-observation j bytes s eq)
 direct-same (P.egressMuxer w action) s eq direct = egress-same s (Old.muxer-egress-observation w action s eq)
 direct-same (P.protocolReturned j) s eq direct = returned-same j s (P.unlessAwaiting-just j s _ eq)
 direct-same (P.commitClean j) s eq direct = commit-same j s (Old.clean-observation j s eq)
 direct-same (P.protocolException j err) s eq direct = commit-same j s (Old.exception-observation j err s eq)
 direct-same (P.returnProtocol j) s eq direct = returned-body-same j s (Old.return-observation j s eq)
 direct-same (P.publishProtocol j) s eq direct = published-same j s (Old.publication-observation j s eq)
 direct-same (P.deregisterProtocol j) s eq direct = via-protocol-same j (Pool.deregister j) s eq
 direct-same (P.asyncProtocolResult j) s eq direct = via-protocol-same j (Pool.publishAsyncResult j) s eq
 direct-same (P.infrastructureReturn w role err) s eq direct = via-infra-same w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s eq
 direct-same (P.publishInfra w role) s eq direct = via-infra-same w role Pool.publishCompletion s eq
 direct-same (P.deregisterInfra w role) s eq direct = via-infra-same w role Pool.deregister s eq
 direct-same (P.asyncInfraResult w role) s eq direct = via-infra-same w role Pool.publishAsyncResult s eq
 direct-same (P.control w a) s eq direct = control-same w a s eq
 direct-same (P.submitDbWrite j d) s eq direct = db-same _ s (P.submitDb-via j d s eq)
 direct-same (P.awaitDbWrite j) s eq direct = db-same _ s (P.awaitDb-via j s eq)
 direct-same (P.writerComplete d) s eq direct = db-same _ s eq
 direct-same (P.writerSeal err) s eq direct = db-same _ s eq
 direct-same (P.dbWriteFailed j) s eq direct with P.dbFailure-via j s eq
 ... | P.refused err failed = commit-same j s (Old.exception-observation j err s failed)
 ... | P.abandoned err mid abandon failed = trans (commit-same j mid (Old.exception-observation j err mid failed)) (db-same _ s abandon)


import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
open import ConnectionManagement.IGTypes using (clean; errored)

module Monitor (isBearerClosed : ErrorId → Bool) where
 private module W = MonitorModel isBearerClosed using (Action; State; base; beginDead; commitTracer; consume; deadAction; deadReady; deadTracing; demuxFinish; failed; findCaptured; finishDead; finishMatches; finishMux; finishProtocol; finishProtocolTrace; finished; handleHead; handleProtocol; handleSelected; initiatorTracing; legacyMatches; muxAt; ownerContext; pcAt; poolAt; protocolSource; recordFinish; responderTracing; run; sampleTracer; selectHead; selected; setPC; setSource; source; startDead; statusAction; step; traceSource; tracing; viaSource; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; jobs; noParent)
 private module Pool = P.Pool using (completions; consumeCompletion; step)
 table : W.State → Acquire.Runtime
 table s = O.acquiring (W.source s)
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field same-acquiring : table after ≡ table before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths refl
 ci-pc-paths : ∀ w pc s → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s = paths refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (trans (CIPaths.same-acquiring second) (CIPaths.same-acquiring first))
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (inbound-same (Machine.igStep action) (W.source s) eq tt)
 ci-via-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-select-projects : ∀ w s {s′} → W.selectHead w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.pcAt w s | W.ownerContext w s in context
 ... | W.waiting | just (f , mid) with W.muxAt mid s | P.noParent (W.poolAt w s) | Pool.completions (W.poolAt w s)
 ...   | just m | true | item ∷ rest with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned with Pool.step Pool.consumeCompletion (W.poolAt w s) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → paths refl }
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopping | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.stopped | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.failed err | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.readActive tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.commitTrace active tr = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterStart n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.forkPending n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.afterFailure = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just m | true | item ∷ rest | WireMux.ready | WireMux.tracerFailed n = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | nothing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.waiting | just (f , mid) | just _ | true | [] = case eq of λ ()
 ci-select-projects w s eq | W.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.finished outcome | _ = case eq of λ ()

 ci-pc-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPC w pc after)
 ci-pc-after w pc {after = after} path = ci-compose path (ci-pc-paths w pc after)
 ci-protocol-source-projects : ∀ w mid dir n outcome s {s′} → W.protocolSource w mid dir n outcome s ≡ just s′ → CIPaths s s′
 ci-protocol-source-projects w mid WireMux.responderJob n outcome s eq with W.muxAt mid s
 ... | nothing = case eq of λ ()
 ... | just m with W.legacyMatches n outcome (WireMux.completions m)
 ...   | false = case eq of λ ()
 ...   | true with W.viaSource (IG.monitorCompletion mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-pc-after w (W.responderTracing outcome) (ci-via-projects (IG.monitorCompletion mid) s advanced) }
 ci-protocol-source-projects w mid WireMux.initiatorJob n clean s eq = case just-injective eq of λ { refl → ci-pc-paths w (W.initiatorTracing clean) s }
 ci-protocol-source-projects w mid WireMux.initiatorJob n (errored err) s eq with W.viaSource (IG.recordMuxFailure mid err) s in advanced
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → ci-pc-after w (W.initiatorTracing (errored err)) (ci-via-projects (IG.recordMuxFailure mid err) s advanced) }
 ci-handle-protocol-projects : ∀ w dir n gen outcome s {s′} → W.handleProtocol w dir n gen outcome s ≡ just s′ → CIPaths s s′
 ci-handle-protocol-projects w dir n gen outcome s eq with W.ownerContext w s | W.findCaptured w dir n gen outcome (P.jobs (W.base s))
 ... | just (f , mid) | just (j , job) with does (Types.mux job ≟ mid) | W.muxAt mid s
 ...   | true | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.ready | WireMux.returned = ci-protocol-source-projects w mid dir n outcome s eq
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
 ci-record-finish-projects w outcome s eq with W.ownerContext w s
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with W.viaSource (W.statusAction outcome mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadReady outcome) (ci-via-projects (W.statusAction outcome mid) s advanced) }
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
 ci-trace-projects sample w s eq with W.tracing (W.pcAt w s) | W.ownerContext w s
 ... | true | just (f , mid) with sample
 ...   | true = ci-via-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-projects (IG.commitTracer mid) s eq
 ci-trace-projects sample w s eq | false | _ = case eq of λ ()
 ci-trace-projects sample w s eq | true | nothing = case eq of λ ()
 ci-finish-protocol-projects : ∀ w s {s′} → W.finishProtocol w s ≡ just s′ → CIPaths s s′
 ci-finish-protocol-projects w s eq with W.pcAt w s | W.ownerContext w s
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.afterFailure = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | just m | WireMux.returned = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.responderTracing (errored err) | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.waiting) s }
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.readActive tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterStart n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.forkPending n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.afterFailure = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing clean | just (f , mid) | nothing = case eq of λ ()
 ci-finish-protocol-projects w s eq | W.initiatorTracing (errored err) | just (f , mid) with W.muxAt mid s
 ... | just m with WireMux.callback m
 ...   | WireMux.returned = case just-injective eq of λ { refl → ci-pc-paths w (W.deadReady (W.failed err)) s }
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
 ci-start-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadReady outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with W.finishMatches outcome (WireMux.status m) | W.deadAction outcome (WireMux.callback m) mid
 ...     | true | just action with W.viaSource action s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-pc-after w (W.deadTracing outcome) (ci-via-projects action s advanced) }
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
 ci-finish-dead-projects w s eq with W.pcAt w s | W.ownerContext w s
 ... | W.deadTracing outcome | just (f , mid) with W.muxAt mid s
 ...   | just m with WireMux.callback m | W.finishMatches outcome (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-pc-paths w (W.finished outcome) s }
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

 IsDirect : W.Action → Set
 IsDirect (W.run a) = ⊥
 IsDirect _ = ⊤
 direct-same : ∀ a s {t} → W.step a s ≡ just t → IsDirect a → table t ≡ table s
 direct-same (W.run a) s eq ()
 direct-same (W.consume w) s eq direct = CIPaths.same-acquiring (ci-select-projects w s eq)
 direct-same (W.handleSelected w) s eq direct = CIPaths.same-acquiring (ci-handle-projects w s eq)
 direct-same (W.sampleTracer w) s eq direct = CIPaths.same-acquiring (ci-trace-projects true w s eq)
 direct-same (W.commitTracer w) s eq direct = CIPaths.same-acquiring (ci-trace-projects false w s eq)
 direct-same (W.finishProtocolTrace w) s eq direct = CIPaths.same-acquiring (ci-finish-protocol-projects w s eq)
 direct-same (W.beginDead w) s eq direct = CIPaths.same-acquiring (ci-start-dead-projects w s eq)
 direct-same (W.finishDead w) s eq direct = CIPaths.same-acquiring (ci-finish-dead-projects w s eq)

module Group (isBearerClosed : ErrorId → Bool) where
 private module W = GroupModel isBearerClosed using (Action; module M; State; abortMonitor; abortOwner; abortStage; asyncDead; asyncDeadTracing; asyncExit; asyncFailure; asyncFailureWritten; asyncTrace; base; beginAsyncDead; beginWhole; beginWholeClose; cancelPC; captureGroup; captureMini; childEligible; commitAsyncTracer; commitStoppedTracer; deliverGroup; deliverMini; deliverWhole; deliverWholeChild; delivered; discardClean; drainEmpty; drainReady; draining; failedExit; finishAsync; finishAsyncDead; finishChildUnwind; finishGroup; finishMini; finishNormalScope; finishOrdinary; finishStopped; finishStoppedTrace; finishWhole; finishWholeClose; frameAt; fromPhase; groupClosing; idle; isInfra; joined; joinGroup; joinMini; joinMiniHead; joinWhole; miniMember; monitorReturnedNormal; normalExit; observeStoppingTrace; observeTraceStopped; ownerAborting; ownerContext; ownerOf; phase; poolAt; prepareUnwind; protocolState; ready; registeredMini; remaining; replaceUnwind; replacementEligible; requestGroup; requestGroupCancel; requestShutdown; requestStop; retireFor; retireAllowed; retireCounters; requestWholeCancel; requested; run; sameStage; sampleAsyncTracer; sampleStoppedTracer; scopeDone; selectShutdown; selectStop; setFrame; setPhase; setPool; setProtocols; setSource; shutdownSelected; source; sourcePhase; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; timeout2Elapsed; unwindChild; unwindReplacedBySync; viaPool; viaSource; wholeAction; wholeClosed; wholeClosing; wholeDeliverable; wholeOutcome; writeAsyncFailure; writeStopped; writeStopping)
 private module M = W.M using (deadReady; deadTracing; failed; finishMatches; finished; initiatorTracing; pcAt; responderTracing; selected; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; jobs; locate; muxAt; noParent; noResults; pendingAt; source; protocolException; sameOutcome; step)
 private module U = P.U using (module Startup; frames; handleAllocated; progress; promisePublished; returnedSuccess)
 private module Pool = P.Pool using (beginClose; bodyReturned; bodyRunning; bodyUnwinding; bodyUnwound; cancelPending; closedPool; closing; deliverCancel; deregisterPending; deregistered; finishClose; handles; interruptJob; join; joinPending; openPool; phase; requestCancel; resultAvailable; resumeAfterUnwindError; sameSnapshot; step)
 open W using (remaining; joined; cancelPC)
 table : W.State → Acquire.Runtime
 table s = O.acquiring (W.source s)
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field same-acquiring : table after ≡ table before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths
   (trans (CIPaths.same-acquiring second) (CIPaths.same-acquiring first))
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = paths refl
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-protocol-projects : ∀ s p →
   Protocol.table p ≡ Protocol.table (W.protocolState s) → CIPaths s (W.setProtocols p s)
 ci-protocol-projects s p same = paths same
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (inbound-same (Machine.igStep action) (W.source s) eq tt)
 ci-via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p →
   CIPaths s (W.setPool w f p s)
 ci-pool-step w f action s {p} eq = paths refl
 ci-via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → CIPaths s s′
 ci-via-pool-projects w action s eq with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → ci-pool-step w f action s advanced }
 ci-from-phase-projects : ∀ w before after s {s′} → W.fromPhase w before after s ≡ just s′ → CIPaths s s′
 ci-from-phase-projects w before after s eq with W.sameStage before (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true = case just-injective eq of λ { refl → ci-phase-paths w after s }
 ci-source-phase-projects : ∀ w before after action s {s′} → W.sourcePhase w before after action s ≡ just s′ → CIPaths s s′
 ci-source-phase-projects w before after action s eq with W.sameStage before (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with W.viaSource (action mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w after (ci-via-source-projects (action mid) s advanced) }
 ci-source-phase-projects w before after action s eq | false | _ = case eq of λ ()
 ci-source-phase-projects w before after action s eq | true | nothing = case eq of λ ()
 ci-request-projects : ∀ w s {s′} → W.requestStop w s ≡ just s′ → CIPaths s s′
 ci-request-projects w s eq with lookup w (U.frames (P.base (W.protocolState s)))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.promisePublished hid mid = ci-via-source-projects (IG.enqueueMuxStop mid) s eq
 ...   | U.returnedSuccess = case eq of λ ()
 ...   | U.handleAllocated hid mid = case eq of λ ()
 -- Counter retirement writes only the actual IG registry at scopeDone.
 ci-retire-projects : ∀ w s {s′} → W.retireFor w s ≡ just s′ → CIPaths s s′
 ci-retire-projects w s eq with W.retireAllowed (W.phase (W.frameAt w s))
 ... | false = case eq of λ ()
 ... | true with lookup w (U.frames (P.base (W.protocolState s)))
 ...   | nothing = case eq of λ ()
 ...   | just f with U.progress f
 ...     | U.promisePublished hid mid = ci-via-source-projects (IG.retireCells mid) s eq
 ...     | U.returnedSuccess = case eq of λ ()
 ...     | U.handleAllocated hid mid = case eq of λ ()
 ci-select-projects : ∀ w s {s′} → W.selectStop w s ≡ just s′ → CIPaths s s′
 ci-select-projects w s eq with W.phase (W.frameAt w s) | M.pcAt w (W.base s) | W.ownerContext w s
 ... | W.idle | M.waiting | just (f , mid) with P.noParent (W.poolAt w s) | P.noResults (W.poolAt w s)
 ...   | true | true with W.viaSource (IG.takeShutdownCommand mid) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-phase-after w W.shutdownSelected (ci-via-source-projects (IG.takeShutdownCommand mid) s advanced) }
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | false | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | just (f , mid) | true | false = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.waiting | nothing = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.selected item | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.responderTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.initiatorTracing result | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadReady outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.deadTracing outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.idle | M.finished outcome | _ = case eq of λ ()
 ci-select-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-select-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-capture-projects : ∀ w order s {s′} → W.captureMini w order s ≡ just s′ → CIPaths s s′
 ci-capture-projects w order s eq with W.phase (W.frameAt w s) | Pool.sameSnapshot order (W.registeredMini w s) | P.noParent (W.poolAt w s)
 ... | W.stoppingWritten | true | true = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.stoppingWritten | false | _ = case eq of λ ()
 ... | W.stoppingWritten | true | false = case eq of λ ()
 ci-capture-projects w order s eq | W.idle | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.draining | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-capture-projects w order s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-request-group-projects : ∀ w s {s′} → W.requestGroup w s ≡ just s′ → CIPaths s s′
 ci-request-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | j ∷ rest = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ... | W.groupClosing | W.ready | [] = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-request-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects : ∀ w s {s′} → W.deliverMini w s ≡ just s′ → CIPaths s s′
 ci-deliver-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.requested j | current ∷ rest with j ≟ current | W.miniMember w j s | W.childEligible j s
 ...   | yes same | true | true with W.viaPool w (Pool.interruptJob j) s in advanced
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → ci-frame-after w _ (ci-via-pool-projects w (Pool.interruptJob j) s advanced) }
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | no apart | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | false | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | current ∷ rest | yes same | true | false = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.requested j | [] = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.ready | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-deliver-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-join-head-projects : ∀ w current s {s′} → W.joinMiniHead w current s ≡ just s′ → CIPaths s s′
 ci-join-head-projects w current s eq with W.remaining (W.frameAt w s) | lookup current (Pool.handles (W.poolAt w s))
 ... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
 ...   | yes same = case just-injective eq of λ { refl → ci-frame-paths w _ s }
 ...   | no apart = case eq of λ ()
 ci-join-head-projects w current s eq | [] | _ = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | nothing = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.bodyReturned result) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-join-head-projects w current s eq | _ ∷ _ | just (Pool.deregistered exit) = case eq of λ ()
 ci-join-group-projects : ∀ w s {s′} → W.joinMini w s ≡ just s′ → CIPaths s s′
 ci-join-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s)
 ... | W.groupClosing | W.requested j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.delivered j = ci-join-head-projects w j s eq
 ... | W.groupClosing | W.ready = case eq of λ ()
 ci-join-group-projects w s eq | W.idle | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.draining | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-join-group-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-group-projects : ∀ w s {s′} → W.finishMini w s ≡ just s′ → CIPaths s s′
 ci-finish-group-projects w s eq with W.phase (W.frameAt w s) | W.cancelPC (W.frameAt w s) | W.remaining (W.frameAt w s)
 ... | W.groupClosing | W.ready | [] = case just-injective eq of λ { refl → ci-phase-paths w W.draining s }
 ... | W.groupClosing | W.ready | _ ∷ _ = case eq of λ ()
 ... | W.groupClosing | W.requested j | _ = case eq of λ ()
 ... | W.groupClosing | W.delivered j | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-finish-group-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-discard-projects : ∀ j job s {s′} → W.discardClean j job s ≡ just s′ → CIPaths s s′
 ci-discard-projects j job s eq with Types.direction job
 ... | WireMux.initiatorJob = case just-injective eq of λ { refl → ci-idle s }
 ... | WireMux.responderJob with P.locate j (P.pendingAt (Types.owner job) (W.protocolState s)) | P.muxAt (Types.mux job) (W.protocolState s)
 ...   | just (index , kept) | just m with IG.takePending index (WireMux.finishedJobs m)
 ...     | just ((n , result) , rest) with does (n Nat.≟ Types.protocolNumber job) ∧ P.sameOutcome ConnectionManagement.IGTypes.clean result
 ...       | true with W.viaSource (IG.discardJobOccurrence (Types.mux job) index) s in advanced
 ...         | nothing = case eq of λ ()
 ...         | just next = case just-injective eq of λ { refl → ci-compose
   (ci-via-source-projects (IG.discardJobOccurrence (Types.mux job) index) s advanced)
   (ci-protocol-projects next _ refl) }
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just (index , kept) | just m | nothing = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | nothing | _ = case eq of λ ()
 ci-discard-projects j job s eq | WireMux.responderJob | just pair | nothing = case eq of λ ()
 ci-prepare-projects : ∀ j w f s {s′} → W.prepareUnwind j w f s ≡ just s′ → CIPaths s s′
 ci-prepare-projects j w f s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing with W.isInfra j f
 ...   | true = case just-injective eq of λ { refl → ci-idle s }
 ...   | false = case eq of λ ()
 ci-prepare-projects j w f s eq | just job with does (w ≟ Types.owner job) | Types.phase job
 ... | true | Types.executing = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.waitingEgress = case just-injective eq of λ { refl → ci-idle s }
 ... | true | Types.resultCaptured ConnectionManagement.IGTypes.clean = ci-discard-projects j job s eq
 ... | true | Types.resultCaptured (ConnectionManagement.IGTypes.errored err) = case eq of λ ()
 ... | false | _ = case eq of λ ()
 ci-unwind-projects : ∀ j s {s′} → W.unwindChild j s ≡ just s′ → CIPaths s s′
 ci-unwind-projects j s eq with W.ownerOf j s in owned
 ... | nothing = case eq of λ ()
 ... | just (w , f) with lookup j (Pool.handles (W.poolAt w s))
 ...   | just Pool.bodyUnwinding with W.prepareUnwind j w f s in prepared
 ...     | nothing = case eq of λ ()
 ...     | just next with Pool.step (Pool.bodyUnwound j) (W.poolAt w next) in advanced
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → paths
   (CIPaths.same-acquiring (ci-prepare-projects j w f s prepared)) }
 ci-unwind-projects j s eq | just (w , f) | nothing = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just Pool.bodyRunning = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.bodyReturned result) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregisterPending exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.deregistered exit) = case eq of λ ()
 ci-unwind-projects j s eq | just (w , f) | just (Pool.resultAvailable exit) = case eq of λ ()
 ci-replacement-projects : ∀ j err s {s′} → W.replaceUnwind j err s ≡ just s′ → CIPaths s s′
 ci-replacement-projects j err s eq with lookup j (P.jobs (W.protocolState s))
 ... | nothing = case eq of λ ()
 ... | just job with W.replacementEligible (Types.phase job) | W.ownerOf j s in owned
 ...   | true | just (w , f) with does (w ≟ Types.owner job) | Pool.step (Pool.resumeAfterUnwindError j) (W.poolAt w s) in advanced
 ...     | true | just p with P.step (P.protocolException j err) (W.protocolState (W.setPool w f p s)) in captured
 ...       | nothing = case eq of λ ()
 ...       | just next = case just-injective eq of λ { refl → ci-compose
   (ci-pool-step w f (Pool.resumeAfterUnwindError j) s advanced)
   (ci-protocol-projects (W.setPool w f p s) next
     (Protocol.direct-same (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured tt)) }
 ci-replacement-projects j err s eq | just job | true | just (w , f) | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | just (w , f) | true | nothing = case eq of λ ()
 ci-replacement-projects j err s eq | just job | false | _ = case eq of λ ()
 ci-replacement-projects j err s eq | just job | true | nothing = case eq of λ ()
 ci-abort-projects : ∀ w err s {s′} → W.abortMonitor w err s ≡ just s′ → CIPaths s s′
 ci-abort-projects w err s eq with W.abortStage w s | W.ownerContext w s | P.noParent (W.poolAt w s)
 ... | true | just (f , mid) | true with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m
 ...     | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w (W.ownerAborting err) s }
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.readActive tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.commitTrace active tr = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterStart n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.forkPending n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.afterFailure = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | just m | WireMux.tracerFailed n = case eq of λ ()
 ci-abort-projects w err s eq | true | just (f , mid) | true | nothing = case eq of λ ()
 ci-abort-projects w err s eq | false | _ | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | nothing | _ = case eq of λ ()
 ci-abort-projects w err s eq | true | just pair | false = case eq of λ ()
 ci-begin-whole-projects : ∀ w order s {s′} → W.beginWhole w order s ≡ just s′ → CIPaths s s′
 ci-begin-whole-projects w order s eq with W.wholeOutcome w s
 ... | nothing = case eq of λ ()
 ... | just outcome with W.viaPool w (Pool.beginClose order) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosing outcome) (ci-via-pool-projects w (Pool.beginClose order) s advanced) }
 ci-whole-action-projects : ∀ w action s {s′} → W.wholeAction w action s ≡ just s′ → CIPaths s s′
 ci-whole-action-projects w action s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome = ci-via-pool-projects w action s eq
 ci-whole-action-projects w action s eq | W.idle = case eq of λ ()
 ci-whole-action-projects w action s eq | W.shutdownSelected = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingTraced = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppingWritten = case eq of λ ()
 ci-whole-action-projects w action s eq | W.groupClosing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.draining = case eq of λ ()
 ci-whole-action-projects w action s eq | W.drainReady = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTrace = case eq of λ ()
 ci-whole-action-projects w action s eq | W.stoppedTracing = case eq of λ ()
 ci-whole-action-projects w action s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-whole-action-projects w action s eq | W.ownerAborting err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.wholeClosed outcome = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-whole-action-projects w action s eq | W.scopeDone outcome = case eq of λ ()
 ci-whole-delivery-projects : ∀ w s {s′} → W.deliverWholeChild w s ≡ just s′ → CIPaths s s′
 ci-whole-delivery-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.wholeClosing outcome | just (f , mid) | Pool.cancelPending j with W.wholeDeliverable w j f s
 ...   | true = ci-via-pool-projects w Pool.deliverCancel s eq
 ...   | false = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | nothing | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closing = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.closedPool = case eq of λ ()
 ci-whole-delivery-projects w s eq | W.wholeClosing outcome | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-whole-projects : ∀ w s {s′} → W.finishWhole w s ≡ just s′ → CIPaths s s′
 ci-finish-whole-projects w s eq with W.phase (W.frameAt w s)
 ... | W.wholeClosing outcome with W.viaPool w Pool.finishClose s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.wholeClosed outcome) (ci-via-pool-projects w Pool.finishClose s advanced) }
 ci-finish-whole-projects w s eq | W.idle = case eq of λ ()
 ci-finish-whole-projects w s eq | W.shutdownSelected = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingTraced = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppingWritten = case eq of λ ()
 ci-finish-whole-projects w s eq | W.groupClosing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.draining = case eq of λ ()
 ci-finish-whole-projects w s eq | W.drainReady = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTrace = case eq of λ ()
 ci-finish-whole-projects w s eq | W.stoppedTracing = case eq of λ ()
 ci-finish-whole-projects w s eq | W.monitorReturnedNormal = case eq of λ ()
 ci-finish-whole-projects w s eq | W.ownerAborting err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.wholeClosed outcome = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncFailureWritten err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.asyncDeadTracing err = case eq of λ ()
 ci-finish-whole-projects w s eq | W.scopeDone outcome = case eq of λ ()
 ci-async-failure-projects : ∀ w s {s′} → W.asyncFailure w s ≡ just s′ → CIPaths s s′
 ci-async-failure-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s) | W.ownerContext w s
 ... | W.wholeClosed (W.asyncExit err) | Pool.closedPool | just (f , mid) with W.viaSource (IG.recordAsyncMuxFailure mid err) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncFailureWritten err) (ci-via-source-projects (IG.recordAsyncMuxFailure mid err) s advanced) }
 ci-async-failure-projects w s eq | W.wholeClosed W.normalExit | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.failedExit err) | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closedPool | nothing = case eq of λ ()
 ci-async-failure-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.asyncDeadTracing err | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.openPool | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.closing | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.cancelPending j | _ = case eq of λ ()
 ci-async-failure-projects w s eq | W.wholeClosed (W.asyncExit err) | Pool.joinPending j | _ = case eq of λ ()
 ci-async-dead-projects : ∀ w s {s′} → W.asyncDead w s ≡ just s′ → CIPaths s s′
 ci-async-dead-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncFailureWritten err | just (f , mid) with W.viaSource (IG.traceMuxDead mid) s in advanced
 ...   | nothing = case eq of λ ()
 ...   | just next = case just-injective eq of λ { refl → ci-phase-after w (W.asyncDeadTracing err) (ci-via-source-projects (IG.traceMuxDead mid) s advanced) }
 ci-async-dead-projects w s eq | W.asyncFailureWritten err | nothing = case eq of λ ()
 ci-async-dead-projects w s eq | W.idle | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.draining | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-async-dead-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-async-trace-projects : ∀ sample w s {s′} → W.asyncTrace sample w s ≡ just s′ → CIPaths s s′
 ci-async-trace-projects sample w s eq with W.phase (W.frameAt w s) | W.ownerContext w s
 ... | W.asyncDeadTracing err | just (f , mid) with sample
 ...   | true = ci-via-source-projects (IG.sampleTracer mid) s eq
 ...   | false = ci-via-source-projects (IG.commitTracer mid) s eq
 ci-async-trace-projects sample w s eq | W.asyncDeadTracing err | nothing = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.idle | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.groupClosing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.draining | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.drainReady | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.wholeClosed outcome | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-async-trace-projects sample w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-async-projects : ∀ w s {s′} → W.finishAsync w s ≡ just s′ → CIPaths s s′
 ci-finish-async-projects w s eq with W.phase (W.frameAt w s) | W.ownerContext w s | Pool.phase (W.poolAt w s)
 ... | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.asyncExit err)) s }
 ...     | WireMux.returned | false = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.readActive tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterStart n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.forkPending n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.afterFailure | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closedPool | nothing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | nothing | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.idle | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.shutdownSelected | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingTraced | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppingWritten | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.groupClosing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.draining | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.drainReady | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTrace | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.stoppedTracing | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.monitorReturnedNormal | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.ownerAborting err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosing outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.wholeClosed outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncFailureWritten err | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.scopeDone outcome | _ | _ = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.openPool = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.closing = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.cancelPending j = case eq of λ ()
 ci-finish-async-projects w s eq | W.asyncDeadTracing err | just (f , mid) | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects : ∀ w s {s′} → W.finishOrdinary w s ≡ just s′ → CIPaths s s′
 ci-finish-ordinary-projects w s eq with W.phase (W.frameAt w s) | Pool.phase (W.poolAt w s)
 ... | W.wholeClosed W.normalExit | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone W.normalExit) s }
 ... | W.wholeClosed (W.failedExit err) | Pool.closedPool = case just-injective eq of λ { refl → ci-phase-paths w (W.scopeDone (W.failedExit err)) s }
 ... | W.wholeClosed (W.asyncExit err) | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.idle | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.shutdownSelected | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingTraced | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppingWritten | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.groupClosing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.draining | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.drainReady | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTrace | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.stoppedTracing | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.monitorReturnedNormal | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.ownerAborting err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosing outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncFailureWritten err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.asyncDeadTracing err | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.scopeDone outcome | _ = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed W.normalExit | Pool.joinPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.openPool = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.closing = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.cancelPending j = case eq of λ ()
 ci-finish-ordinary-projects w s eq | W.wholeClosed (W.failedExit err) | Pool.joinPending j = case eq of λ ()
 ci-finish-stopped-projects : ∀ w s {s′} → W.finishStopped w s ≡ just s′ → CIPaths s s′
 ci-finish-stopped-projects w s eq with W.sameStage W.stoppedTracing (W.phase (W.frameAt w s)) | W.ownerContext w s
 ... | true | just (f , mid) with P.muxAt mid (W.protocolState s)
 ...   | just m with WireMux.status m | WireMux.callback m
 ...     | WireMux.stopped | WireMux.returned = case just-injective eq of λ { refl → ci-phase-paths w W.monitorReturnedNormal s }
 ...     | WireMux.stopped | WireMux.readActive tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.commitTrace flag tr = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterStart n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.forkPending n = case eq of λ ()
 ...     | WireMux.stopped | WireMux.afterFailure = case eq of λ ()
 ...     | WireMux.stopped | WireMux.tracerFailed n = case eq of λ ()
 ...     | WireMux.ready | _ = case eq of λ ()
 ...     | WireMux.stopping | _ = case eq of λ ()
 ...     | WireMux.failed err | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | just (f , mid) | nothing = case eq of λ ()
 ci-finish-stopped-projects w s eq | false | _ = case eq of λ ()
 ci-finish-stopped-projects w s eq | true | nothing = case eq of λ ()

 IsDirect : W.Action → Set
 IsDirect (W.run a) = ⊥
 IsDirect _ = ⊤
 direct-same : ∀ a s {t} → W.step a s ≡ just t → IsDirect a → table t ≡ table s
 direct-same (W.run a) s eq ()
 direct-same (W.requestShutdown w) s eq direct = CIPaths.same-acquiring (ci-request-projects w s eq)
 direct-same (W.retireCounters w) s eq direct = CIPaths.same-acquiring (ci-retire-projects w s eq)
 direct-same (W.selectShutdown w) s eq direct = CIPaths.same-acquiring (ci-select-projects w s eq)
 direct-same (W.observeStoppingTrace w) s eq direct = CIPaths.same-acquiring (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 direct-same (W.writeStopping w) s eq direct = CIPaths.same-acquiring (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 direct-same (W.captureGroup w order) s eq direct = CIPaths.same-acquiring (ci-capture-projects w order s eq)
 direct-same (W.requestGroupCancel w) s eq direct = CIPaths.same-acquiring (ci-request-group-projects w s eq)
 direct-same (W.deliverGroup w) s eq direct = CIPaths.same-acquiring (ci-deliver-group-projects w s eq)
 direct-same (W.joinGroup w) s eq direct = CIPaths.same-acquiring (ci-join-group-projects w s eq)
 direct-same (W.finishGroup w) s eq direct = CIPaths.same-acquiring (ci-finish-group-projects w s eq)
 direct-same (W.drainEmpty w) s eq direct = CIPaths.same-acquiring (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 direct-same (W.timeout2Elapsed w) s eq direct = CIPaths.same-acquiring (ci-from-phase-projects w W.draining W.drainReady s eq)
 direct-same (W.writeStopped w) s eq direct = CIPaths.same-acquiring (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 direct-same (W.observeTraceStopped w) s eq direct = CIPaths.same-acquiring (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 direct-same (W.sampleStoppedTracer w) s eq direct = CIPaths.same-acquiring (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 direct-same (W.commitStoppedTracer w) s eq direct = CIPaths.same-acquiring (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 direct-same (W.finishStoppedTrace w) s eq direct = CIPaths.same-acquiring (ci-finish-stopped-projects w s eq)
 direct-same (W.finishChildUnwind j) s eq direct = CIPaths.same-acquiring (ci-unwind-projects j s eq)
 direct-same (W.unwindReplacedBySync j err) s eq direct = CIPaths.same-acquiring (ci-replacement-projects j err s eq)
 direct-same (W.abortOwner w err) s eq direct = CIPaths.same-acquiring (ci-abort-projects w err s eq)
 direct-same (W.beginWholeClose w order) s eq direct = CIPaths.same-acquiring (ci-begin-whole-projects w order s eq)
 direct-same (W.requestWholeCancel w) s eq direct = CIPaths.same-acquiring (ci-whole-action-projects w Pool.requestCancel s eq)
 direct-same (W.deliverWhole w) s eq direct = CIPaths.same-acquiring (ci-whole-delivery-projects w s eq)
 direct-same (W.joinWhole w) s eq direct = CIPaths.same-acquiring (ci-whole-action-projects w Pool.join s eq)
 direct-same (W.finishWholeClose w) s eq direct = CIPaths.same-acquiring (ci-finish-whole-projects w s eq)
 direct-same (W.finishNormalScope w) s eq direct = CIPaths.same-acquiring (ci-finish-ordinary-projects w s eq)
 direct-same (W.writeAsyncFailure w) s eq direct = CIPaths.same-acquiring (ci-async-failure-projects w s eq)
 direct-same (W.beginAsyncDead w) s eq direct = CIPaths.same-acquiring (ci-async-dead-projects w s eq)
 direct-same (W.sampleAsyncTracer w) s eq direct = CIPaths.same-acquiring (ci-async-trace-projects true w s eq)
 direct-same (W.commitAsyncTracer w) s eq direct = CIPaths.same-acquiring (ci-async-trace-projects false w s eq)
 direct-same (W.finishAsyncDead w) s eq direct = CIPaths.same-acquiring (ci-finish-async-projects w s eq)
