{-# OPTIONS --guardedness #-}

-- Every actual mux-prefix writer preserves current-frame negotiated content.
module ConnectionManagement.Properties.LiveTrackerContentProtocol where

open import Data.Bool using (true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Properties.HandlerAuxBacking as Presence
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxEgress as EgressLayout
import ConnectionManagement.Properties.OutboundHandlerSupervision as Base
import ConnectionManagement.Properties.LiveTrackerChainSteps as Chain
open import ConnectionManagement.Properties.LiveTrackerFrameContent using
 (Content; content; allocation; publication; Covers; at; insert; transport; advance; startup-content; setup-content; publication-writer)
import Data.Unit
import Data.List.Relation.Unary.All
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst)
open import ConnectionManagement.Properties.LiveTrackerFrameContent using (execute)
import ConnectionManagement.Properties.LiveTrackerContentMux as Lower
module Mux = Lower.Mux
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as WireMux
module Protocol where
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; Action; module Pool; module Startup; State; module U; appendPending; asyncInfraResult; asyncProtocolResult; base; commitClean; control; controlReady; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infraId; infrastructureReturn; inherit; inheritedAllowed; initial; jobs; monitorControl; monitoring; muxAt; noParent; poolAt; protocolException; protocolReturned; unlessAwaiting-just; publishInfra; publishProtocol; register; registerProtocol; removePublished; returnProtocol; returned; run; setPool; setSource; source; sourceControl; step; viaInfra; viaProtocol; viaDb; viaDb-source; submitDb-via; awaitDb-via; dbFailure-via; DbFailure; refused; abandoned; submitDbWrite; awaitDbWrite; dbWriteFailed; writerComplete; writerSeal)
 private module U = P.U using (handshakePending; captured; base; frames; handleAllocated; initial; progress; promisePublished; returnedSuccess; startup; step)
 private module Pool = P.Pool using (bodyReturnedWith; deregister; parentFork; publishAsyncResult; publishCompletion; register; step)
 private module Startup = P.Startup using (phase)
 private module Old = ProtocolProperties using (EgressChange; enter-observation; send-observation; muxer-egress-observation; BodyReturn; CompletionCommit; Fork; Publication; clean-observation; exception-observation; initiator-fork-observation; publication-observation; responder-fork-observation; return-observation)
 Valid : P.State → Set
 Valid s = Mux.Valid (P.base s)
 source-valid : ∀ c s {as} → O.Executes (P.source s) as c → Valid s → Valid (P.setSource c s)
 source-valid c s path valid = Mux.source-valid c (P.base s) path valid
 pool-valid : ∀ w f p s → Content w f (P.source s) → Valid s → Valid (P.setPool w f p s)
 pool-valid w f p s present valid = Mux.put-valid w _ (P.base s) (startup-content w f _ (P.source s) present) valid
 pending-valid : ∀ job j s → Valid s → Valid (P.appendPending job j s)
 pending-valid job j s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 removed-valid : ∀ job kept s → Valid s → Valid (P.removePublished job kept s)
 removed-valid job kept s valid with Types.direction job
 ... | WireMux.initiatorJob = valid
 ... | WireMux.responderJob = valid
 inherited : ∀ a s {t} → P.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with P.inheritedAllowed a
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → Mux.step-preserves a (P.base s) actual valid }
 fork-source : ∀ {w j gen s t} → (observation : Old.Fork w j gen s t) →
   Data.Product.Σ (Data.List.List O.Action) (λ actions → O.Executes (P.source s) actions (Old.Fork.sourceAfter observation))
 fork-source {s = s} observation with ProtocolProperties.Fork.source-boundary observation
 ... | ProtocolProperties.responderSource m found callback advanced = _ , O.next {a = O.inbound (Machine.igStep (IG.forkResponder (Old.Fork.capturedMux observation)))} advanced O.done
 ... | ProtocolProperties.initiatorSource descriptor found same = [] , subst (λ c → O.Executes _ [] c) (sym same) O.done
 fork-valid : ∀ w j gen s {t} → Old.Fork w j gen s t → Valid s → Valid t
 fork-valid w j gen s observation valid rewrite Old.Fork.after-shape observation =
   pool-valid w (Old.Fork.ownerFrame observation) (Old.Fork.poolAfter observation)
     (P.setSource (Old.Fork.sourceAfter observation) s)
     (execute (proj₂ (fork-source observation)) w (Old.Fork.ownerFrame observation)
       (at (P.U.frames (P.base s)) (P.source s) valid w _ (Old.Fork.frame-before observation)))
     (source-valid (Old.Fork.sourceAfter observation) s (proj₂ (fork-source observation)) valid)
 commit-valid : ∀ j s {t} → Old.CompletionCommit j s t → Valid s → Valid t
 commit-valid j s observation valid rewrite Old.CompletionCommit.after-shape observation =
   pending-valid (Old.CompletionCommit.capturedJob observation) j _
     (source-valid (Old.CompletionCommit.sourceAfter observation) s
       (proj₂ (ProtocolProperties.body-source-trace (Old.CompletionCommit.capturedJob observation) (Old.CompletionCommit.outcome observation) s (Old.CompletionCommit.actual-source-commit observation))) valid)
 body-valid : ∀ j s {t} → Old.BodyReturn j s t → Valid s → Valid t
 body-valid j s observation valid rewrite Old.BodyReturn.after-shape observation =
   pool-valid (Types.owner (Old.BodyReturn.capturedJob observation))
     (Old.BodyReturn.ownerFrame observation) (Old.BodyReturn.poolAfter observation) s
     (at (P.U.frames (P.base s)) (P.source s) valid _ _ (Old.BodyReturn.frame-before observation)) valid
 publication-valid : ∀ j s {t} → Old.Publication j s t → Valid s → Valid t
 publication-valid j s observation valid rewrite Old.Publication.after-shape observation =
   removed-valid (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
     (pool-valid (Types.owner (Old.Publication.capturedJob observation))
       (Old.Publication.ownerFrame observation) (Old.Publication.poolAfter observation)
       (P.setSource (Old.Publication.sourceAfter observation) s)
       (execute (proj₂ (ProtocolProperties.publication-source-trace j (Old.Publication.capturedJob observation) (Old.Publication.outcome observation) s (Old.Publication.actual-source observation))) _ _
         (at (P.U.frames (P.base s)) (P.source s) valid _ _ (Old.Publication.frame-before observation)))
       (source-valid (Old.Publication.sourceAfter observation) s
         (proj₂ (ProtocolProperties.publication-source-trace j (Old.Publication.capturedJob observation) (Old.Publication.outcome observation) s (Old.Publication.actual-source observation))) valid))
 returned : ∀ j s {t} → P.returned j s ≡ just t → Valid s → Valid t
 returned j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl → valid }
 returned j s eq valid | just job | Types.waitingEgress = case eq of λ ()
 returned j s eq valid | just job | Types.resultCaptured result = case eq of λ ()
 registered : ∀ j s {t} → P.register j s ≡ just t → Valid s → Valid t
 registered j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (at (P.U.frames (P.base s)) (P.source s) valid _ _ found) valid }
 registered j s eq valid | just job | nothing | _ = case eq of λ ()
 registered j s eq valid | just job | just f | nothing = case eq of λ ()
 via-protocol : ∀ j a s {t} → P.viaProtocol j a s ≡ just t → Valid s → Valid t
 via-protocol j a s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.step a (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (at (P.U.frames (P.base s)) (P.source s) valid _ _ found) valid }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra : ∀ w role a s {t} → P.viaInfra w role a s ≡ just t → Valid s → Valid t
 via-infra w role a s eq valid with lookup w (U.frames (P.base s)) in found
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (a j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → pool-valid w f p s (at (P.U.frames (P.base s)) (P.source s) valid _ _ found) valid }
 control : ∀ w a s {t} → P.monitorControl w a s ≡ just t → Valid s → Valid t
 control w a s eq valid with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady a m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl a mid))) (P.source s) in advanced
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → source-valid c s (O.next {a = O.inbound (Machine.igStep (P.sourceControl a mid))} advanced O.done) valid }
 control w a s eq valid | just f | (U.handshakePending helperPC) | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | true | false = case eq of λ ()
 -- Source egress changes do not replace any captured owner frame.
 egress-valid : ∀ s {t} → Old.EgressChange s t → Valid s → Valid t
 egress-valid s observation valid rewrite Old.EgressChange.after-shape observation = source-valid _ s (O.next {a = O.inbound (Machine.igStep (IG.egressStep (Old.EgressChange.capturedMux observation) (Old.EgressChange.operation observation)))} (Old.EgressChange.actual-source observation) O.done) valid
 -- DB queue/await steps change only the source configuration.
 db-valid : ∀ a s {t} → P.viaDb a s ≡ just t → Valid s → Valid t
 db-valid a s eq valid with P.viaDb-source a s eq
 ... | c , advanced , refl = source-valid c s (O.next {a = O.inbound (Machine.igStep (IG.leiosDb a))} advanced O.done) valid
 step-preserves : ∀ a s {t} → P.step a s ≡ just t → Valid s → Valid t
 step-preserves (P.run a) = inherited a
 step-preserves (P.forkResponder w j gen) s eq = fork-valid w j gen s (Old.responder-fork-observation w j gen s eq)
 step-preserves (P.forkInitiator w j gen n) s eq = fork-valid w j gen s (Old.initiator-fork-observation w j gen n s eq)
 step-preserves (P.registerProtocol j) = registered j
 step-preserves (P.enterProtocolBody j) s eq = egress-valid s (Old.enter-observation j s eq)
 step-preserves (P.appendProtocolPayload j bytes) s eq = egress-valid s (Old.send-observation j bytes s eq)
 step-preserves (P.egressMuxer w action) s eq = egress-valid s (Old.muxer-egress-observation w action s eq)
 step-preserves (P.protocolReturned j) s eq = returned j s (P.unlessAwaiting-just j s _ eq)
 step-preserves (P.commitClean j) s eq = commit-valid j s (Old.clean-observation j s eq)
 step-preserves (P.protocolException j err) s eq = commit-valid j s (Old.exception-observation j err s eq)
 step-preserves (P.returnProtocol j) s eq = body-valid j s (Old.return-observation j s eq)
 step-preserves (P.publishProtocol j) s eq = publication-valid j s (Old.publication-observation j s eq)
 step-preserves (P.deregisterProtocol j) = via-protocol j (Pool.deregister j)
 step-preserves (P.asyncProtocolResult j) = via-protocol j (Pool.publishAsyncResult j)
 step-preserves (P.infrastructureReturn w role err) = via-infra w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err))
 step-preserves (P.publishInfra w role) = via-infra w role Pool.publishCompletion
 step-preserves (P.deregisterInfra w role) = via-infra w role Pool.deregister
 step-preserves (P.asyncInfraResult w role) = via-infra w role Pool.publishAsyncResult
 step-preserves (P.control w a) = control w a
 step-preserves (P.submitDbWrite j d) s eq = db-valid _ s (P.submitDb-via j d s eq)
 step-preserves (P.awaitDbWrite j) s eq = db-valid _ s (P.awaitDb-via j s eq)
 step-preserves (P.writerComplete d) s eq = db-valid _ s eq
 step-preserves (P.writerSeal err) s eq = db-valid _ s eq
 step-preserves (P.dbWriteFailed j) s eq valid with P.dbFailure-via j s eq
 ... | P.refused err failed = commit-valid j s (Old.exception-observation j err s failed) valid
 ... | P.abandoned err mid abandon failed = commit-valid j mid (Old.exception-observation j err mid failed) (db-valid _ s abandon valid)
 initialized-valid : ∀ c {s} → P.initial c ≡ just s → Valid s
 initialized-valid c eq with U.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just u = case just-injective eq of λ { refl → Mux.initialized-valid c actual }

 open Presence.Protocol public using (coordinator; IsDirect; direct-shutdown-same)

