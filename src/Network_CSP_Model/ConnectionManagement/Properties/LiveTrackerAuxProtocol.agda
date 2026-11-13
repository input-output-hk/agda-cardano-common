{-# OPTIONS --guardedness #-}

-- Joint job/pool-content preservation at every typed protocol writer.
open import Data.Bool using (Bool)
open import ConnectionManagement.Domain using (ErrorId)
module ConnectionManagement.Properties.LiveTrackerAuxProtocol (b : ErrorId → Bool) where
open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
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
import ConnectionManagement.Properties.LiveTrackerAuxMux as Lower
module A = Aux b
module T = Trans b
module Up = Updates b
module U = P.U
module Pool = P.Pool
module Startup = P.Startup
open T using (Retains; job-kept; completion-kept; job-phase)

-- Capture commits require a writable body phase, and cannot replace an older
-- captured result. This is the exact existing source input classification.
uncommitted : ∀ job result → Old.CompletionInput job result → ∀ old → Types.phase job ≢ Types.resultCaptured old
uncommitted job result input old eq with Old.CommittedRows.input-writable job result input
... | eligible rewrite eq = case eligible of λ ()
captured-completion : ∀ j job result s → lookup j (P.jobs s) ≡ just job → Types.phase job ≡ Types.resultCaptured result →
 A.JobContent j job s → A.Completion (Types.owner job) (P.capturedResult job result) s
captured-completion j (Types.protocolJob w mid dir n gen phase) result s found refl good = j , mid , found , good

module For (Obs : P.State → Set) (stable : ∀ {s t} → Retains s t → Obs s → Obs t) where
 Valid : P.State → Set
 Valid s = Up.Valid s × Obs s
 source-valid : ∀ c s → Valid s → Valid (P.setSource c s)
 source-valid c s (valid , observed) = Up.source-valid c s valid , stable (T.source c s) observed
 same : ∀ s t → P.U.frames (P.base t) ≡ P.U.frames (P.base s) → P.jobs t ≡ P.jobs s →
   (∀ w → P.poolAt w t ≡ P.poolAt w s) → Valid s → Valid t
 same s t frames jobs pools (valid , observed) = Up.same-valid s t kept frames jobs pools valid , stable kept observed
   where
   kept = T.by-fields s t frames
     (λ w j phase found → phase , subst (λ p → lookup j (Pool.handles p) ≡ just phase) (sym (pools w)) found)
     (λ j job found → Types.phase job , trans (cong (lookup j) jobs) found)
     (λ j w mid dir n gen result found → trans (cong (lookup j) jobs) found)
 pool-valid : ∀ w f a s {p} → lookup w (U.frames (P.base s)) ≡ just f →
   (actual : Pool.step a (P.poolAt w s) ≡ just p) →
   Up.Kernel.NewReturn a (λ value → A.Completion w value (P.setPool w f p s)) → Valid s → Valid (P.setPool w f p s)
 pool-valid w f a s found actual new (valid , observed) = Up.pool-valid w f a s found actual new valid ,
   stable (Up.pool-retains w f _ s found (Up.Kernel.handles-retained a (P.poolAt w s) actual)) observed
 job-valid : ∀ j job s → (kept : Retains s (record s { jobs = put j job (P.jobs s) })) →
   A.JobContent j job (record s { jobs = put j job (P.jobs s) }) → Valid s → Valid (record s { jobs = put j job (P.jobs s) })
 job-valid j job s kept good (valid , observed) = Up.job-valid j job s kept good valid , stable kept observed
 phase-valid : ∀ j job phase s → lookup j (P.jobs s) ≡ just job →
   (∀ result → Types.phase job ≢ Types.resultCaptured result) → Valid s → Valid (record s { jobs = put j (record job { phase = phase }) (P.jobs s) })
 phase-valid j job phase s found writable valid = job-valid j _ s kept
   (job-phase j job phase _ (job-kept kept j job (Up.at (Up.Valid.jobs (proj₁ valid)) j job found))) valid
   where kept = Up.phase-job j job phase s found writable
 pending-valid : ∀ job j s → Valid s → Valid (P.appendPending job j s)
 pending-valid job j s with Types.direction job
 ... | WireMux.initiatorJob = λ valid → valid
 ... | WireMux.responderJob = same s _ refl refl (λ w → refl)
 removed-valid : ∀ job kept s → Valid s → Valid (P.removePublished job kept s)
 removed-valid job kept s with Types.direction job
 ... | WireMux.initiatorJob = λ valid → valid
 ... | WireMux.responderJob = same s _ refl refl (λ w → refl)
 inherited : ∀ a s {t} → P.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with P.inheritedAllowed a in allowed
 ... | false = case eq of λ ()
 ... | true with U.step a (P.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just u = case just-injective eq of λ { refl → Lower.For.step-preserves b (P.jobs s) (P.pending s) Obs stable a (P.base s) actual allowed valid }
 fork-valid : ∀ w j gen s {t} → Old.Fork w j gen s t → Valid s → Valid t
 fork-valid w j gen s observation valid rewrite Old.Fork.after-shape observation =
   job-valid j _ middle (Up.fresh-job j _ middle fresh) (subst (A.JobContent j _) (Old.Fork.after-shape observation) (A.fork-established w j gen s observation))
     (pool-valid w f (Pool.fork j) (P.setSource (Old.Fork.sourceAfter observation) s) (Old.Fork.frame-before observation)
       (Old.Fork.actual-fork observation) tt (source-valid (Old.Fork.sourceAfter observation) s valid))
   where
   f = Old.Fork.ownerFrame observation
   middle = P.setPool w f (Old.Fork.poolAfter observation) (P.setSource (Old.Fork.sourceAfter observation) s)
   fresh = Old.CaptureIdentity.fresh-lookup j gen s (Old.Fork.globally-fresh observation)
 commit-valid : ∀ j s {t} → Old.CompletionCommit j s t → Valid s → Valid t
 commit-valid j s observation valid rewrite Old.CompletionCommit.after-shape observation =
   pending-valid job j _ (phase-valid j job (Types.resultCaptured (Old.CompletionCommit.outcome observation))
     (P.setSource (Old.CompletionCommit.sourceAfter observation) s) (Old.CompletionCommit.job-before observation)
     (uncommitted job _ (Old.CompletionCommit.input-boundary observation)) (source-valid (Old.CompletionCommit.sourceAfter observation) s valid))
   where job = Old.CompletionCommit.capturedJob observation
 body-valid : ∀ j s {t} → Old.BodyReturn j s t → Valid s → Valid t
 body-valid j s observation valid rewrite Old.BodyReturn.after-shape observation =
   pool-valid w f (Pool.bodyReturnedWith j (P.capturedResult job result)) s found actual
     (completion-kept kept w _ (captured-completion j job result s (Old.BodyReturn.job-before observation)
       (Old.BodyReturn.local-result-before observation) (Up.at (Up.Valid.jobs (proj₁ valid)) j job (Old.BodyReturn.job-before observation)))) valid
   where
   job = Old.BodyReturn.capturedJob observation
   w = Types.owner job
   f = Old.BodyReturn.ownerFrame observation
   result = Old.BodyReturn.outcome observation
   found = Old.BodyReturn.frame-before observation
   actual = Old.BodyReturn.actual-return observation
   kept = Up.pool-retains w f (Old.BodyReturn.poolAfter observation) s found (Up.Kernel.handles-retained (Pool.bodyReturnedWith j (P.capturedResult job result)) (P.poolAt w s) actual)
 publication-valid : ∀ j s {t} → Old.Publication j s t → Valid s → Valid t
 publication-valid j s observation valid rewrite Old.Publication.after-shape observation =
   removed-valid (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
     (pool-valid _ _ (Pool.publishCompletion j) (P.setSource (Old.Publication.sourceAfter observation) s)
       (Old.Publication.frame-before observation) (Old.Publication.actual-publication observation) tt
       (source-valid (Old.Publication.sourceAfter observation) s valid))
 returned : ∀ j s {t} → P.returned j s ≡ just t → Valid s → Valid t
 returned j s eq valid with lookup j (P.jobs s) in found
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job in phase
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl → phase-valid j job Types.waitingEgress s found (λ result eq → case trans (sym phase) eq of λ ()) valid }
 returned j s eq valid | just job | Types.waitingEgress = case eq of λ ()
 returned j s eq valid | just job | Types.resultCaptured result = case eq of λ ()
 registered : ∀ j s {t} → P.register j s ≡ just t → Valid s → Valid t
 registered j s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.parentFork (P.poolAt (Types.owner job) s)
 ...   | just f | just current with j ≟ current
 ...     | no _ = case eq of λ ()
 ...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s) in poolActual
 ...       | nothing = case eq of λ ()
 ...       | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f Pool.register s found poolActual tt valid }
 registered j s eq valid | just job | nothing | _ = case eq of λ ()
 registered j s eq valid | just job | just f | nothing = case eq of λ ()
 via-protocol : ∀ j a s {t} → P.viaProtocol j a s ≡ just t → (∀ C → Up.Kernel.NewReturn a C) → Valid s → Valid t
 via-protocol j a s eq new valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.step a (P.poolAt (Types.owner job) s) in poolActual
 ...   | just f | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f a s found (Old.computation-from-lookup (Types.owner job) f a s p found poolActual) (new _) valid }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra : ∀ w role a s {t} → P.viaInfra w role a s ≡ just t → (∀ j f p → lookup w (U.frames (P.base s)) ≡ just f → P.infraId role (Startup.phase (U.startup f)) ≡ just j → Pool.step (a j) (P.poolAt w s) ≡ just p → Up.Valid s → Up.Kernel.NewReturn (a j) (λ value → A.Completion w value (P.setPool w f p s))) → Valid s → Valid t
 via-infra w role a s eq new valid with lookup w (U.frames (P.base s)) in found
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f)) in bound
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (a j) (P.poolAt w s) in poolActual
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → pool-valid w f (a j) s found poolActual (new j f p refl bound (subst (λ pool → Pool.step (a j) pool ≡ just p) (cong Startup.pool (Old.Base.startup-found w (P.base s) f found)) poolActual) (proj₁ valid)) valid }
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
 ...         | just c = case just-injective eq of λ { refl → source-valid c s valid }
 control w a s eq valid | just f | (U.handshakePending helperPC) | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | true | false = case eq of λ ()
 -- Source egress changes do not replace any captured owner frame.
 egress-valid : ∀ s {t} → Old.EgressChange s t → Valid s → Valid t
 egress-valid s observation valid rewrite Old.EgressChange.after-shape observation = source-valid _ s valid
 -- DB queue/await steps change only the source configuration.
 db-valid : ∀ a s {t} → P.viaDb a s ≡ just t → Valid s → Valid t
 db-valid a s eq valid with P.viaDb-source a s eq
 ... | c , advanced , refl = source-valid c s valid
 -- Infrastructure result writers recover their owner from the retained
 -- unpublished/startup fact, then carry the configured role and real handle.
 infra-return : ∀ w role err s {t} → P.viaInfra w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s ≡ just t → Valid s → Valid t
 infra-return w role err s eq = via-infra w role _ s eq supply
   where
   supply : ∀ j f p → lookup w (U.frames (P.base s)) ≡ just f → P.infraId role (Startup.phase (U.startup f)) ≡ just j →
     Pool.step (Pool.bodyReturnedWith j (Types.infraResult role err)) (P.poolAt w s) ≡ just p → Up.Valid s → A.Completion w (Types.infraResult role err) (P.setPool w f p s)
   supply j f p found bound actual valid = as-completion role transported
     where
     own = Up.role-owner w f s role j found (Up.early-at (Up.Valid.frames valid) w f found) bound
     before : A.Infrastructure w (Types.infraResult role err) s
     before = record
       { owner-reference = own; role = role; job = j; error = err
       ; role-found = subst (λ f′ → P.infraId role (Startup.phase (U.startup f′)) ≡ just j)
           (sym (Up.role-owner-frame w f s role j found (Up.early-at (Up.Valid.frames valid) w f found) bound)) bound; tagged = refl
       ; physical-phase = Pool.bodyRunning
       ; physical-found = Up.Kernel.return-running j _ (P.poolAt w s) actual }
     transported = T.infra-kept (Up.pool-retains w f p s found (Up.Kernel.handles-retained (Pool.bodyReturnedWith j (Types.infraResult role err)) (P.poolAt w s) actual)) w _ before
     as-completion : ∀ role → A.Infrastructure w (Types.infraResult role err) (P.setPool w f p s) → A.Completion w (Types.infraResult role err) (P.setPool w f p s)
     as-completion Types.muxer good = good
     as-completion Types.demuxer good = good
     as-completion (Types.laneMuxer lane) good = good
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
 step-preserves (P.deregisterProtocol j) = λ s eq → via-protocol j (Pool.deregister j) s eq (λ C → tt)
 step-preserves (P.asyncProtocolResult j) = λ s eq → via-protocol j (Pool.publishAsyncResult j) s eq (λ C → tt)
 step-preserves (P.infrastructureReturn w role err) = infra-return w role err
 step-preserves (P.publishInfra w role) = λ s eq → via-infra w role Pool.publishCompletion s eq (λ j f p found bound actual valid → tt)
 step-preserves (P.deregisterInfra w role) = λ s eq → via-infra w role Pool.deregister s eq (λ j f p found bound actual valid → tt)
 step-preserves (P.asyncInfraResult w role) = λ s eq → via-infra w role Pool.publishAsyncResult s eq (λ j f p found bound actual valid → tt)
 step-preserves (P.control w a) = control w a
 step-preserves (P.submitDbWrite j d) s eq = db-valid _ s (P.submitDb-via j d s eq)
 step-preserves (P.awaitDbWrite j) s eq = db-valid _ s (P.awaitDb-via j s eq)
 step-preserves (P.writerComplete d) s eq = db-valid _ s eq
 step-preserves (P.writerSeal err) s eq = db-valid _ s eq
 step-preserves (P.dbWriteFailed j) s eq valid with P.dbFailure-via j s eq
 ... | P.refused err failed = commit-valid j s (Old.exception-observation j err s failed) valid
 ... | P.abandoned err mid abandon failed = commit-valid j mid (Old.exception-observation j err mid failed) (db-valid _ s abandon valid)
