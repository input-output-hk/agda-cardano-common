{-# OPTIONS --guardedness #-}

-- Auxiliary mux/exit owners denote historical physical handlers. This tracks
-- presence only; the physical birth theorem separately recovers descriptors.
module ConnectionManagement.Properties.HandlerAuxBacking where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other; lookup-head)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as OutboundRelease

-- Projected captures keep the presence predicate independent of mutable phases.
Present : WorkerId → Birth.Registry → Set
Present w registry = Σ S.HandlerStart (λ captured → lookup w registry ≡ just captured)
Covers : ∀ {A : Set} → Store WorkerId A → Birth.Registry → Set
Covers rows registry = ∀ w row → lookup w rows ≡ just row → Present w registry
Retains : Birth.Registry → Birth.Registry → Set
Retains before after = ∀ w → Present w before → Present w after
change-retains : ∀ {P before after} → Birth.Change P before after → Retains before after
change-retains change w (captured , found) = captured , Birth.retains change w captured found
covers-retained : ∀ {A : Set} {rows : Store WorkerId A} {before after} → Retains before after → Covers rows before → Covers rows after
covers-retained retained valid w row found = retained w (valid w row found)
covers-empty : ∀ {A : Set} registry → Covers {A} [] registry
covers-empty registry w row ()
covers-put : ∀ {A : Set} w (row : A) rows registry → Present w registry → Covers rows registry → Covers (put w row rows) registry
covers-put w row rows registry present valid q other found with q ≟ w
... | yes refl = present
... | no different = valid q other (trans (sym (lookup-put-other w q row rows different)) found)
lookup-cons-other : ∀ {A : Set} (q w : WorkerId) (row : A) (rows : Store WorkerId A) → w ≢ q → lookup w ((q , row) ∷ rows) ≡ lookup w rows
lookup-cons-other q w row rows different with w ≟ q
... | yes same = ⊥-elim (different same)
... | no _ = refl
covers-tail : ∀ {A : Set} q (row : A) rows registry → Covers ((q , row) ∷ rows) registry → Covers rows registry
covers-tail q row rows registry valid w other found with w ≟ q
... | yes refl = valid q row (lookup-head q row rows)
... | no different = valid w other (trans (lookup-cons-other q w row rows different) found)
physical-present : ∀ w state → (Σ H.Thread (λ thread → lookup w (B.threads state) ≡ just thread)) → Present w (Birth.physical state)
physical-present w state (thread , found) = H.captured thread ,
  trans (Birth.lookup-captures w (B.threads state)) (cong (Data.Maybe.map H.captured) found)

module Mux where
 private module U = MuxModel Types.TypedResult using (Action; Frame; module Startup; State; advanceStartup; allocate; allocateHandle; allocationAction; base; baseAllowed; birth; birthFresh; flow; frames; handleAllocated; inherit; initial; negotiate; negotiateReturned; noteBirth; origins; progress; promisePublished; publish; publishSuccess; returnedSuccess; run; setFrame; setSource; source; startup; startupAllowed; startupStep; step)
 private module Startup = U.Startup using (observePublication; step)
 Valid : U.State → Set
 Valid s = Covers (U.frames s) (Birth.MuxLayer.view s)
 put-valid : ∀ w f s → Present w (Birth.MuxLayer.view s) → Valid s → Valid (U.setFrame w f s)
 put-valid w f s present valid = covers-put w f (U.frames s) (Birth.MuxLayer.view s) present valid
 source-valid : ∀ c s → Valid s → Valid (U.setSource c s)
 source-valid c s valid = valid
 note-valid : ∀ birth s → Valid s → Valid (U.noteBirth birth s)
 note-valid nothing s valid = valid
 note-valid (just origin) s valid = valid
 inherited : ∀ a s {t} → U.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with U.baseAllowed a s ∧ U.birthFresh (U.birth a (U.base s)) (U.origins s)
 ... | false = case eq of λ ()
 ... | true with B.step a (U.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just b = case just-injective eq of λ { refl → note-valid (U.birth a (U.base s)) (record s { base = b })
   (covers-retained {rows = U.frames s} {before = Birth.physical (U.base s)} {after = Birth.physical b}
     (change-retains (Birth.physical-step-change a (U.base s) actual)) valid) }
 negotiated : ∀ w ps flow s {t} → U.negotiateReturned w ps flow s ≡ just t → Valid s → Valid t
 negotiated w ps flow s eq valid with lookup w (B.threads (U.base s)) in found |
   lookup w (U.origins s) | lookup w (U.frames s)
 ... | just thread | just origin | nothing with H.phase thread
 ...   | H.handshaking = case just-injective eq of λ { refl → put-valid w _ s (physical-present w (U.base s) (thread , found)) valid }
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.maskedSetup = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.caughtCancellation err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.cancellationPublished err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.bodyExited err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.finalizing err = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.cleanupComplete err outcome = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | nothing | H.resultAvailable err outcome = case eq of λ ()
 negotiated w ps flow s eq valid | nothing | origin | old = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | nothing | old = case eq of λ ()
 negotiated w ps flow s eq valid | just thread | just origin | just old = case eq of λ ()
 allocated : ∀ w hid mid s {t} → U.allocate w hid mid s ≡ just t → Valid s → Valid t
 allocated w hid mid s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s)
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (valid w f found) valid }
 allocated w hid mid s eq valid | just f | U.handleAllocated old mid′ = case eq of λ ()
 allocated w hid mid s eq valid | just f | U.promisePublished old mid′ = case eq of λ ()
 published : ∀ w s {t} → U.publish w s ≡ just t → Valid s → Valid t
 published w s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) |
   Startup.step Startup.observePublication (U.startup f)
 ...     | just c | just next = case just-injective eq of λ { refl → put-valid w _ (U.setSource c s) (valid w f found) valid }
 ...     | nothing | _ = case eq of λ ()
 ...     | just c | nothing = case eq of λ ()
 published w s eq valid | just f | U.returnedSuccess = case eq of λ ()
 published w s eq valid | just f | U.promisePublished hid mid = case eq of λ ()
 startup : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → Valid s → Valid t
 startup w a s eq valid with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.startupAllowed a s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f)
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → put-valid w _ s (valid w f found) valid }
 startup w a s eq valid | just f | U.returnedSuccess | allowed = case eq of λ ()
 startup w a s eq valid | just f | U.handleAllocated hid mid | allowed = case eq of λ ()
 startup w a s eq valid | just f | U.promisePublished hid mid | false = case eq of λ ()
 step-preserves : ∀ a s {t} → U.step a s ≡ just t → Valid s → Valid t
 step-preserves (U.run a) = inherited a
 step-preserves (U.negotiate w ps flow) = negotiated w ps flow
 step-preserves (U.allocateHandle w hid mid) = allocated w hid mid
 step-preserves (U.publishSuccess w) = published w
 step-preserves (U.startupStep w a) = startup w a
 initialized-valid : ∀ c {s} → U.initial c ≡ just s → Valid s
 initialized-valid c eq with IG.handles (IG.execution (Machine.inboundGovernor (O.core c))) |
   IG.muxes (IG.execution (Machine.inboundGovernor (O.core c))) | B.initial c
 ... | [] | [] | just b = case just-injective eq of λ { refl → covers-empty {U.Frame} (Birth.physical b) }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

 coordinator : U.State → Close.State
 coordinator s = B.shutdown (U.base s)
 negotiate-same : ∀ w ps flow s {s′} → U.negotiateReturned w ps flow s ≡ just s′ → coordinator s′ ≡ coordinator s
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

 allocate-same : ∀ w hid mid s {s′} → U.allocate w hid mid s ≡ just s′ → coordinator s′ ≡ coordinator s
 allocate-same w hid mid s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.returnedSuccess with O.advance (O.inbound (Machine.igStep (U.allocationAction f hid mid))) (U.source s) in advanced
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → refl }
 allocate-same w hid mid s eq | just f | U.handleAllocated oldHandle oldMux = case eq of λ ()
 allocate-same w hid mid s eq | just f | U.promisePublished oldHandle oldMux = case eq of λ ()

 publish-same : ∀ w s {s′} → U.publish w s ≡ just s′ → coordinator s′ ≡ coordinator s
 publish-same w s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f
 ...   | U.handleAllocated hid mid with O.advance
   (O.inbound (Machine.handlerPublication w (S.negotiated hid (U.flow f)) Machine.resultWritten)) (U.source s) in advanced |
   Startup.step Startup.observePublication (U.startup f) in progressed
 ...     | just c | just next = case just-injective eq of λ { refl → refl }
 publish-same w s eq | just f | U.handleAllocated hid mid | nothing | startupResult = case eq of λ ()
 publish-same w s eq | just f | U.handleAllocated hid mid | just c | nothing = case eq of λ ()
 publish-same w s eq | just f | U.returnedSuccess = case eq of λ ()
 publish-same w s eq | just f | U.promisePublished hid mid = case eq of λ ()

 startup-shutdown : ∀ w a s {t} → U.advanceStartup w a s ≡ just t → coordinator t ≡ coordinator s
 startup-shutdown w a s eq with lookup w (U.frames s) in found
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | U.startupAllowed a s
 ...   | U.promisePublished hid mid | true with Startup.step a (U.startup f)
 ...     | nothing = case eq of λ ()
 ...     | just next = case just-injective eq of λ { refl → refl }
 startup-shutdown w a s eq | just f | U.returnedSuccess | allowed = case eq of λ ()
 startup-shutdown w a s eq | just f | U.handleAllocated hid mid | allowed = case eq of λ ()
 startup-shutdown w a s eq | just f | U.promisePublished hid mid | false = case eq of λ ()
 IsDirect : U.Action → Set
 IsDirect (U.run a) = ⊥
 IsDirect _ = ⊤
 direct-shutdown-same : ∀ a s {t} → U.step a s ≡ just t → IsDirect a → coordinator t ≡ coordinator s
 direct-shutdown-same (U.run a) s eq ()
 direct-shutdown-same (U.negotiate w ps flow) s eq direct = negotiate-same w ps flow s eq
 direct-shutdown-same (U.allocateHandle w hid mid) s eq direct = allocate-same w hid mid s eq
 direct-shutdown-same (U.publishSuccess w) s eq direct = publish-same w s eq
 direct-shutdown-same (U.startupStep w a) s eq direct = startup-shutdown w a s eq

import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolProperties
import ConnectionManagement.Rules.MuxRuntime as WireMux
module Protocol where
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; Action; module Pool; module Startup; State; module U; appendPending; asyncInfraResult; asyncProtocolResult; base; commitClean; control; controlReady; deregisterInfra; deregisterProtocol; forkInitiator; forkResponder; infraId; infrastructureReturn; inherit; inheritedAllowed; initial; jobs; monitorControl; monitoring; muxAt; noParent; poolAt; protocolException; protocolReturned; publishInfra; publishProtocol; register; registerProtocol; removePublished; returnProtocol; returned; run; setPool; setSource; source; sourceControl; step; viaInfra; viaProtocol)
 private module U = P.U using (base; frames; handleAllocated; initial; progress; promisePublished; returnedSuccess; startup; step)
 private module Pool = P.Pool using (bodyReturnedWith; deregister; parentFork; publishAsyncResult; publishCompletion; register; step)
 private module Startup = P.Startup using (phase)
 private module Old = ProtocolProperties using (EgressChange; enter-observation; send-observation; muxer-egress-observation; BodyReturn; CompletionCommit; Fork; Publication; clean-observation; exception-observation; initiator-fork-observation; publication-observation; responder-fork-observation; return-observation)
 Valid : P.State → Set
 Valid s = Mux.Valid (P.base s)
 source-valid : ∀ c s → Valid s → Valid (P.setSource c s)
 source-valid c s valid = valid
 pool-valid : ∀ w f p s → Present w (Birth.ProtocolLayer.view s) → Valid s → Valid (P.setPool w f p s)
 pool-valid w f p s present valid = Mux.put-valid w _ (P.base s) present valid
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
 fork-valid : ∀ w j gen s {t} → Old.Fork w j gen s t → Valid s → Valid t
 fork-valid w j gen s observation valid rewrite Old.Fork.after-shape observation =
   pool-valid w (Old.Fork.ownerFrame observation) (Old.Fork.poolAfter observation)
     (P.setSource (Old.Fork.sourceAfter observation) s)
     (valid w (Old.Fork.ownerFrame observation) (Old.Fork.frame-before observation)) valid
 commit-valid : ∀ j s {t} → Old.CompletionCommit j s t → Valid s → Valid t
 commit-valid j s observation valid rewrite Old.CompletionCommit.after-shape observation =
   pending-valid (Old.CompletionCommit.capturedJob observation) j _ valid
 body-valid : ∀ j s {t} → Old.BodyReturn j s t → Valid s → Valid t
 body-valid j s observation valid rewrite Old.BodyReturn.after-shape observation =
   pool-valid (Types.owner (Old.BodyReturn.capturedJob observation))
     (Old.BodyReturn.ownerFrame observation) (Old.BodyReturn.poolAfter observation) s
     (valid _ _ (Old.BodyReturn.frame-before observation)) valid
 publication-valid : ∀ j s {t} → Old.Publication j s t → Valid s → Valid t
 publication-valid j s observation valid rewrite Old.Publication.after-shape observation =
   removed-valid (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
     (pool-valid (Types.owner (Old.Publication.capturedJob observation))
       (Old.Publication.ownerFrame observation) (Old.Publication.poolAfter observation)
       (P.setSource (Old.Publication.sourceAfter observation) s)
       (valid _ _ (Old.Publication.frame-before observation)) valid)
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
 ...       | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (valid _ _ found) valid }
 registered j s eq valid | just job | nothing | _ = case eq of λ ()
 registered j s eq valid | just job | just f | nothing = case eq of λ ()
 via-protocol : ∀ j a s {t} → P.viaProtocol j a s ≡ just t → Valid s → Valid t
 via-protocol j a s eq valid with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) in found | Pool.step a (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → pool-valid (Types.owner job) f p s (valid _ _ found) valid }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra : ∀ w role a s {t} → P.viaInfra w role a s ≡ just t → Valid s → Valid t
 via-infra w role a s eq valid with lookup w (U.frames (P.base s)) in found
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (a j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → pool-valid w f p s (valid _ _ found) valid }
 control : ∀ w a s {t} → P.monitorControl w a s ≡ just t → Valid s → Valid t
 control w a s eq valid with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady a m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl a mid))) (P.source s)
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → valid }
 control w a s eq valid | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control w a s eq valid | just f | U.promisePublished hid mid | true | false = case eq of λ ()
 -- Source egress changes do not replace any captured owner frame.
 egress-valid : ∀ s {t} → Old.EgressChange s t → Valid s → Valid t
 egress-valid s observation valid rewrite Old.EgressChange.after-shape observation = valid
 step-preserves : ∀ a s {t} → P.step a s ≡ just t → Valid s → Valid t
 step-preserves (P.run a) = inherited a
 step-preserves (P.forkResponder w j gen) s eq = fork-valid w j gen s (Old.responder-fork-observation w j gen s eq)
 step-preserves (P.forkInitiator w j gen n) s eq = fork-valid w j gen s (Old.initiator-fork-observation w j gen n s eq)
 step-preserves (P.registerProtocol j) = registered j
 step-preserves (P.enterProtocolBody j) s eq = egress-valid s (Old.enter-observation j s eq)
 step-preserves (P.appendProtocolPayload j bytes) s eq = egress-valid s (Old.send-observation j bytes s eq)
 step-preserves (P.egressMuxer w action) s eq = egress-valid s (Old.muxer-egress-observation w action s eq)
 step-preserves (P.protocolReturned j) = returned j
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
 initialized-valid : ∀ c {s} → P.initial c ≡ just s → Valid s
 initialized-valid c eq with U.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just u = case just-injective eq of λ { refl → Mux.initialized-valid c actual }

 coordinator : P.State → Close.State
 coordinator s = B.shutdown (U.base (P.base s))
 fork-same : ∀ w j gen s {t} → Old.Fork w j gen s t → coordinator t ≡ coordinator s
 fork-same w j gen s observation rewrite Old.Fork.after-shape observation = refl
 pending-coordinator : ∀ job j s → coordinator (P.appendPending job j s) ≡ coordinator s
 pending-coordinator job j s with Types.direction job
 ... | WireMux.initiatorJob = refl
 ... | WireMux.responderJob = refl
 removed-coordinator : ∀ job kept s → coordinator (P.removePublished job kept s) ≡ coordinator s
 removed-coordinator job kept s with Types.direction job
 ... | WireMux.initiatorJob = refl
 ... | WireMux.responderJob = refl
 commit-same : ∀ j s {t} → Old.CompletionCommit j s t → coordinator t ≡ coordinator s
 commit-same j s observation rewrite Old.CompletionCommit.after-shape observation =
  pending-coordinator (Old.CompletionCommit.capturedJob observation) j _
 returned-body-same : ∀ j s {t} → Old.BodyReturn j s t → coordinator t ≡ coordinator s
 returned-body-same j s observation rewrite Old.BodyReturn.after-shape observation = refl
 published-same : ∀ j s {t} → Old.Publication j s t → coordinator t ≡ coordinator s
 published-same j s observation rewrite Old.Publication.after-shape observation =
  removed-coordinator (Old.Publication.capturedJob observation) (Old.Publication.remainingPending observation) _
 returned-same : ∀ j s {t} → P.returned j s ≡ just t → coordinator t ≡ coordinator s
 returned-same j s eq with lookup j (P.jobs s) in found
 ... | nothing = case eq of λ ()
 ... | just job with Types.phase job
 ...   | Types.executing with P.hasWanton j job s
 ...     | false = case eq of λ ()
 ...     | true = case just-injective eq of λ { refl →
   refl }
 returned-same j s eq | just job | Types.waitingEgress = case eq of λ ()
 returned-same j s eq | just job | Types.resultCaptured result = case eq of λ ()
 registered-same : ∀ j s {t} → P.register j s ≡ just t → coordinator t ≡ coordinator s
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

 via-protocol-same : ∀ j action s {t} → P.viaProtocol j action s ≡ just t → coordinator t ≡ coordinator s
 via-protocol-same j action s eq with lookup j (P.jobs s)
 ... | nothing = case eq of λ ()
 ... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.step action (P.poolAt (Types.owner job) s)
 ...   | just f | just p = case just-injective eq of λ { refl → refl }
 ...   | nothing | _ = case eq of λ ()
 ...   | just f | nothing = case eq of λ ()
 via-infra-same : ∀ w role action s {t} → P.viaInfra w role action s ≡ just t → coordinator t ≡ coordinator s
 via-infra-same w role action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with P.infraId role (Startup.phase (U.startup f))
 ...   | nothing = case eq of λ ()
 ...   | just j with Pool.step (action j) (P.poolAt w s)
 ...     | nothing = case eq of λ ()
 ...     | just p = case just-injective eq of λ { refl → refl }

 control-same : ∀ w action s {s′} → P.monitorControl w action s ≡ just s′ → coordinator s′ ≡ coordinator s
 control-same w action s eq with lookup w (U.frames (P.base s))
 ... | nothing = case eq of λ ()
 ... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
 ...   | U.promisePublished hid mid | true | true with P.muxAt mid s
 ...     | nothing = case eq of λ ()
 ...     | just m with P.controlReady action m (P.poolAt w s)
 ...       | false = case eq of λ ()
 ...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl action mid))) (P.source s) in advanced
 ...         | nothing = case eq of λ ()
 ...         | just c = case just-injective eq of λ { refl → refl }
 control-same w action s eq | just f | U.returnedSuccess | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
 control-same w action s eq | just f | U.promisePublished hid mid | true | false = case eq of λ ()

 IsDirect : P.Action → Set
 IsDirect (P.run a) = ⊥
 IsDirect _ = ⊤
 -- A child/muxer egress update does not acknowledge CM shutdown.
 egress-same : ∀ s {t} → Old.EgressChange s t → coordinator t ≡ coordinator s
 egress-same s observation rewrite Old.EgressChange.after-shape observation = refl
 direct-shutdown-same : ∀ a s {t} → P.step a s ≡ just t → IsDirect a → coordinator t ≡ coordinator s
 direct-shutdown-same (P.run a) s eq ()
 direct-shutdown-same (P.forkResponder w j gen) s eq direct = fork-same w j gen s (Old.responder-fork-observation w j gen s eq)
 direct-shutdown-same (P.forkInitiator w j gen n) s eq direct = fork-same w j gen s (Old.initiator-fork-observation w j gen n s eq)
 direct-shutdown-same (P.registerProtocol j) s eq direct = registered-same j s eq
 direct-shutdown-same (P.enterProtocolBody j) s eq direct = egress-same s (Old.enter-observation j s eq)
 direct-shutdown-same (P.appendProtocolPayload j bytes) s eq direct = egress-same s (Old.send-observation j bytes s eq)
 direct-shutdown-same (P.egressMuxer w action) s eq direct = egress-same s (Old.muxer-egress-observation w action s eq)
 direct-shutdown-same (P.protocolReturned j) s eq direct = returned-same j s eq
 direct-shutdown-same (P.commitClean j) s eq direct = commit-same j s (Old.clean-observation j s eq)
 direct-shutdown-same (P.protocolException j err) s eq direct = commit-same j s (Old.exception-observation j err s eq)
 direct-shutdown-same (P.returnProtocol j) s eq direct = returned-body-same j s (Old.return-observation j s eq)
 direct-shutdown-same (P.publishProtocol j) s eq direct = published-same j s (Old.publication-observation j s eq)
 direct-shutdown-same (P.deregisterProtocol j) s eq direct = via-protocol-same j (Pool.deregister j) s eq
 direct-shutdown-same (P.asyncProtocolResult j) s eq direct = via-protocol-same j (Pool.publishAsyncResult j) s eq
 direct-shutdown-same (P.infrastructureReturn w role err) s eq direct = via-infra-same w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s eq
 direct-shutdown-same (P.publishInfra w role) s eq direct = via-infra-same w role Pool.publishCompletion s eq
 direct-shutdown-same (P.deregisterInfra w role) s eq direct = via-infra-same w role Pool.deregister s eq
 direct-shutdown-same (P.asyncInfraResult w role) s eq direct = via-infra-same w role Pool.publishAsyncResult s eq
 direct-shutdown-same (P.control w a) s eq direct = control-same w a s eq

import ConnectionManagement.MuxResultMonitor as MonitorModel
open import ConnectionManagement.IGTypes using (clean; errored)
open import Relation.Nullary using (does)
module Monitor (isBearerClosed : ErrorId → Bool) where
 private module W = MonitorModel isBearerClosed using (Action; State; base; beginDead; commitTracer; consume; deadAction; deadReady; deadTracing; delegateAllowed; demuxFinish; failed; findCaptured; finishDead; finishMatches; finishMux; finishProtocol; finishProtocolTrace; finished; handleHead; handleProtocol; handleSelected; inherit; initial; initiatorTracing; legacyMatches; muxAt; ownerContext; pcAt; poolAt; protocolSource; recordFinish; responderTracing; run; sampleTracer; selectHead; selected; setPC; setSource; source; startDead; statusAction; step; traceSource; tracing; viaSource; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; initial; jobs; monitoring; noParent; step)
 private module U = P.U using (base; frames; handleAllocated; progress; promisePublished; returnedSuccess)
 private module Pool = P.Pool using (completions; consumeCompletion; step)
 Valid : W.State → Set
 Valid s = Protocol.Valid (W.base s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 coordinator : W.State → Close.State
 coordinator s = B.shutdown (U.base (P.base (W.base s)))
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
        same-shutdown : coordinator after ≡ coordinator before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid) refl
 ci-pc-paths : ∀ w pc s → CIPaths s (W.setPC w pc s)
 ci-pc-paths w pc s = paths (λ valid → valid) refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid)) (trans (CIPaths.same-shutdown second) (CIPaths.same-shutdown first))
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (λ valid → valid) refl
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with P.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Protocol.step-preserves a (W.base s) actual valid }
 owner-present : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → Valid s → Present w (Birth.MonitorLayer.view isBearerClosed s)
 owner-present w s eq valid with lookup w (U.frames (P.base (W.base s))) in found
 ... | nothing = case eq of λ ()
 ... | just actual with U.progress actual | P.monitoring actual
 ...   | U.promisePublished hid mid | true = valid w actual found
 ...   | U.promisePublished hid mid | false = case eq of λ ()
 ...   | U.returnedSuccess | _ = case eq of λ ()
 ...   | U.handleAllocated hid mid | _ = case eq of λ ()
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
 ...       | just next = case just-injective eq of λ { refl → paths (λ valid → Protocol.pool-valid w f next (W.base s) (owner-present w s context valid) valid) refl }
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

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.consume w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.handleSelected w) s eq = CIPaths.preserves (ci-handle-projects w s eq)
 step-preserves (W.sampleTracer w) s eq = CIPaths.preserves (ci-trace-projects true w s eq)
 step-preserves (W.commitTracer w) s eq = CIPaths.preserves (ci-trace-projects false w s eq)
 step-preserves (W.finishProtocolTrace w) s eq = CIPaths.preserves (ci-finish-protocol-projects w s eq)
 step-preserves (W.beginDead w) s eq = CIPaths.preserves (ci-start-dead-projects w s eq)
 step-preserves (W.finishDead w) s eq = CIPaths.preserves (ci-finish-dead-projects w s eq)
 IsDirect : W.Action → Set
 IsDirect (W.run a) = ⊥
 IsDirect _ = ⊤
 direct-shutdown-same : ∀ a s {t} → W.step a s ≡ just t → IsDirect a → coordinator t ≡ coordinator s
 direct-shutdown-same (W.run a) s eq ()
 direct-shutdown-same (W.consume w) s eq direct = CIPaths.same-shutdown (ci-select-projects w s eq)
 direct-shutdown-same (W.handleSelected w) s eq direct = CIPaths.same-shutdown (ci-handle-projects w s eq)
 direct-shutdown-same (W.sampleTracer w) s eq direct = CIPaths.same-shutdown (ci-trace-projects true w s eq)
 direct-shutdown-same (W.commitTracer w) s eq direct = CIPaths.same-shutdown (ci-trace-projects false w s eq)
 direct-shutdown-same (W.finishProtocolTrace w) s eq direct = CIPaths.same-shutdown (ci-finish-protocol-projects w s eq)
 direct-shutdown-same (W.beginDead w) s eq direct = CIPaths.same-shutdown (ci-start-dead-projects w s eq)
 direct-shutdown-same (W.finishDead w) s eq direct = CIPaths.same-shutdown (ci-finish-dead-projects w s eq)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with P.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → Protocol.initialized-valid c actual }

import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.Properties.MuxGroupShutdown as GroupProperties
import Data.Nat as Nat
module Group (isBearerClosed : ErrorId → Bool) where
 private module W = GroupModel isBearerClosed using (Action; module M; State; abortMonitor; abortOwner; abortStage; asyncDead; asyncDeadTracing; asyncExit; asyncFailure; asyncFailureWritten; asyncTrace; base; beginAsyncDead; beginWhole; beginWholeClose; cancelPC; captureGroup; captureMini; childEligible; commitAsyncTracer; commitStoppedTracer; delegateAllowed; deliverGroup; deliverMini; deliverWhole; deliverWholeChild; delivered; discardClean; drainEmpty; drainReady; draining; failedExit; findOwner; finishAsync; finishAsyncDead; finishChildUnwind; finishGroup; finishMini; finishNormalScope; finishOrdinary; finishStopped; finishStoppedTrace; finishWhole; finishWholeClose; frameAt; fromPhase; groupClosing; idle; inherit; initial; isInfra; joinGroup; joinMini; joinMiniHead; joinWhole; joined; miniMember; monitorReturnedNormal; normalExit; observeStoppingTrace; observeTraceStopped; ownerAborting; ownerContext; ownerOf; phase; poolAt; prepareUnwind; protocolState; ready; registeredMini; remaining; replaceUnwind; replacementEligible; requestGroup; requestGroupCancel; requestShutdown; requestStop; requestWholeCancel; requested; run; sameStage; sampleAsyncTracer; sampleStoppedTracer; scopeDone; selectShutdown; selectStop; setFrame; setPhase; setPool; setProtocols; setSource; shutdownSelected; source; sourcePhase; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; timeout2Elapsed; unwindChild; unwindReplacedBySync; viaPool; viaSource; wholeAction; wholeClosed; wholeClosing; wholeDeliverable; wholeOutcome; writeAsyncFailure; writeStopped; writeStopping)
 private module M = W.M using (deadReady; deadTracing; failed; finishMatches; finished; initial; initiatorTracing; pcAt; responderTracing; selected; step; waiting)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; jobs; locate; muxAt; noParent; noResults; pendingAt; protocolException; sameOutcome; step)
 private module U = P.U using (module Startup; frames; handleAllocated; progress; promisePublished; returnedSuccess; startup)
 private module Startup = U.Startup using (pool)
 private module Pool = P.Pool using (beginClose; bodyReturned; bodyRunning; bodyUnwinding; bodyUnwound; cancelPending; closedPool; closing; deliverCancel; deregisterPending; deregistered; finishClose; handles; interruptJob; join; joinPending; openPool; phase; requestCancel; resultAvailable; resumeAfterUnwindError; sameSnapshot; step)
 private module Lower = Monitor isBearerClosed using (Valid; coordinator; initialized-valid; owner-present; step-preserves)
 open W using (remaining; joined; cancelPC)
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s)
 coordinator : W.State → Close.State
 coordinator s = Lower.coordinator (W.base s)
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 record CIPaths (before after : W.State) : Set where
  constructor paths
  field preserves : Valid before → Valid after
        same-shutdown : coordinator after ≡ coordinator before
 ci-idle : ∀ s → CIPaths s s
 ci-idle s = paths (λ valid → valid) refl
 ci-compose : ∀ {p q r} → CIPaths p q → CIPaths q r → CIPaths p r
 ci-compose first second = paths (λ valid → CIPaths.preserves second (CIPaths.preserves first valid))
   (trans (CIPaths.same-shutdown second) (CIPaths.same-shutdown first))
 ci-frame-paths : ∀ w f s → CIPaths s (W.setFrame w f s)
 ci-frame-paths w f s = paths (λ valid → valid) refl
 ci-phase-paths : ∀ w pc s → CIPaths s (W.setPhase w pc s)
 ci-phase-paths w pc s = ci-frame-paths w _ s
 ci-phase-after : ∀ w pc {before after} → CIPaths before after → CIPaths before (W.setPhase w pc after)
 ci-phase-after w pc {after = after} path = ci-compose path (ci-phase-paths w pc after)
 ci-frame-after : ∀ w f {before after} → CIPaths before after → CIPaths before (W.setFrame w f after)
 ci-frame-after w f {after = after} path = ci-compose path (ci-frame-paths w f after)
 ci-protocol-projects : ∀ s p → (Protocol.Valid (W.protocolState s) → Protocol.Valid p) →
   Protocol.coordinator p ≡ Protocol.coordinator (W.protocolState s) → CIPaths s (W.setProtocols p s)
 ci-protocol-projects s p proof same = paths proof same
 ci-source-step : ∀ action s {c} → O.advance (O.inbound (Machine.igStep action)) (W.source s) ≡ just c → CIPaths s (W.setSource c s)
 ci-source-step action s eq = paths (λ valid → valid) refl
 inherited : ∀ a s {t} → W.inherit a s ≡ just t → Valid s → Valid t
 inherited a s eq valid with W.delegateAllowed a s
 ... | false = case eq of λ ()
 ... | true with M.step a (W.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just m = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual valid }
 owner-present : ∀ w s {f mid} → W.ownerContext w s ≡ just (f , mid) → Valid s → Present w (Birth.GroupLayer.view isBearerClosed s)
 owner-present w s found = Lower.owner-present w (W.base s) found
 find-present : ∀ j rows {w f registry} → W.findOwner j rows ≡ just (w , f) → Covers rows registry → Present w registry
 find-present j [] () valid
 find-present j ((q , first) ∷ rows) {registry = registry} eq valid with lookup j (Pool.handles (Startup.pool (U.startup first)))
 ... | just result = case just-injective eq of λ { refl → valid q first (lookup-head q first rows) }
 ... | nothing = find-present j rows {registry = registry} eq (covers-tail q first rows registry valid)
 ownerOf-present : ∀ j s {w f} → W.ownerOf j s ≡ just (w , f) → Valid s → Present w (Birth.GroupLayer.view isBearerClosed s)
 ownerOf-present j s eq valid = find-present j (U.frames (P.base (W.protocolState s))) {registry = Birth.GroupLayer.view isBearerClosed s} eq valid
 ci-via-source-projects : ∀ action s {s′} → W.viaSource action s ≡ just s′ → CIPaths s s′
 ci-via-source-projects action s eq with O.advance (O.inbound (Machine.igStep action)) (W.source s) in advanced
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → ci-source-step action s advanced }
 ci-pool-step : ∀ w f action s {p} → Pool.step action (W.poolAt w s) ≡ just p →
   (Valid s → Present w (Birth.GroupLayer.view isBearerClosed s)) → CIPaths s (W.setPool w f p s)
 ci-pool-step w f action s {p} eq present = paths (λ valid → Protocol.pool-valid w f p (W.protocolState s) (present valid) valid) refl
 ci-via-pool-projects : ∀ w action s {s′} → W.viaPool w action s ≡ just s′ → CIPaths s s′
 ci-via-pool-projects w action s eq with W.ownerContext w s in context
 ... | nothing = case eq of λ ()
 ... | just (f , mid) with Pool.step action (W.poolAt w s) in advanced
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → ci-pool-step w f action s advanced (owner-present w s context) }
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
   (ci-protocol-projects next _ (λ valid → valid) refl) }
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
   (λ valid → Protocol.pool-valid w f p (W.protocolState next)
     (subst (Present w) (sym (Birth.GroupLayer.CIPaths.retention (Birth.GroupLayer.ci-prepare-projects isBearerClosed j w f s prepared)))
       (ownerOf-present j s owned valid))
     (CIPaths.preserves (ci-prepare-projects j w f s prepared) valid))
   (CIPaths.same-shutdown (ci-prepare-projects j w f s prepared)) }
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
   (ci-pool-step w f (Pool.resumeAfterUnwindError j) s advanced (ownerOf-present j s owned))
   (ci-protocol-projects (W.setPool w f p s) next
     (Protocol.step-preserves (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured)
     (Protocol.direct-shutdown-same (P.protocolException j err) (W.protocolState (W.setPool w f p s)) captured tt)) }
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

 step-preserves : ∀ action s {s′} → W.step action s ≡ just s′ → Valid s → Valid s′
 step-preserves (W.run action) s eq = inherited action s eq
 step-preserves (W.requestShutdown w) s eq = CIPaths.preserves (ci-request-projects w s eq)
 step-preserves (W.selectShutdown w) s eq = CIPaths.preserves (ci-select-projects w s eq)
 step-preserves (W.observeStoppingTrace w) s eq = CIPaths.preserves (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 step-preserves (W.writeStopping w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 step-preserves (W.captureGroup w order) s eq = CIPaths.preserves (ci-capture-projects w order s eq)
 step-preserves (W.requestGroupCancel w) s eq = CIPaths.preserves (ci-request-group-projects w s eq)
 step-preserves (W.deliverGroup w) s eq = CIPaths.preserves (ci-deliver-group-projects w s eq)
 step-preserves (W.joinGroup w) s eq = CIPaths.preserves (ci-join-group-projects w s eq)
 step-preserves (W.finishGroup w) s eq = CIPaths.preserves (ci-finish-group-projects w s eq)
 step-preserves (W.drainEmpty w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 step-preserves (W.timeout2Elapsed w) s eq = CIPaths.preserves (ci-from-phase-projects w W.draining W.drainReady s eq)
 step-preserves (W.writeStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 step-preserves (W.observeTraceStopped w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 step-preserves (W.sampleStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 step-preserves (W.commitStoppedTracer w) s eq = CIPaths.preserves (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 step-preserves (W.finishStoppedTrace w) s eq = CIPaths.preserves (ci-finish-stopped-projects w s eq)
 step-preserves (W.finishChildUnwind j) s eq = CIPaths.preserves (ci-unwind-projects j s eq)
 step-preserves (W.unwindReplacedBySync j err) s eq = CIPaths.preserves (ci-replacement-projects j err s eq)
 step-preserves (W.abortOwner w err) s eq = CIPaths.preserves (ci-abort-projects w err s eq)
 step-preserves (W.beginWholeClose w order) s eq = CIPaths.preserves (ci-begin-whole-projects w order s eq)
 step-preserves (W.requestWholeCancel w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.requestCancel s eq)
 step-preserves (W.deliverWhole w) s eq = CIPaths.preserves (ci-whole-delivery-projects w s eq)
 step-preserves (W.joinWhole w) s eq = CIPaths.preserves (ci-whole-action-projects w Pool.join s eq)
 step-preserves (W.finishWholeClose w) s eq = CIPaths.preserves (ci-finish-whole-projects w s eq)
 step-preserves (W.finishNormalScope w) s eq = CIPaths.preserves (ci-finish-ordinary-projects w s eq)
 step-preserves (W.writeAsyncFailure w) s eq = CIPaths.preserves (ci-async-failure-projects w s eq)
 step-preserves (W.beginAsyncDead w) s eq = CIPaths.preserves (ci-async-dead-projects w s eq)
 step-preserves (W.sampleAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects true w s eq)
 step-preserves (W.commitAsyncTracer w) s eq = CIPaths.preserves (ci-async-trace-projects false w s eq)
 step-preserves (W.finishAsyncDead w) s eq = CIPaths.preserves (ci-finish-async-projects w s eq)
 IsDirect : W.Action → Set
 IsDirect (W.run a) = ⊥
 IsDirect _ = ⊤
 direct-shutdown-same : ∀ a s {t} → W.step a s ≡ just t → IsDirect a → coordinator t ≡ coordinator s
 direct-shutdown-same (W.run a) s eq ()
 direct-shutdown-same (W.requestShutdown w) s eq direct = CIPaths.same-shutdown (ci-request-projects w s eq)
 direct-shutdown-same (W.selectShutdown w) s eq direct = CIPaths.same-shutdown (ci-select-projects w s eq)
 direct-shutdown-same (W.observeStoppingTrace w) s eq direct = CIPaths.same-shutdown (ci-from-phase-projects w W.shutdownSelected W.stoppingTraced s eq)
 direct-shutdown-same (W.writeStopping w) s eq direct = CIPaths.same-shutdown (ci-source-phase-projects w W.stoppingTraced W.stoppingWritten IG.recordMuxStopping s eq)
 direct-shutdown-same (W.captureGroup w order) s eq direct = CIPaths.same-shutdown (ci-capture-projects w order s eq)
 direct-shutdown-same (W.requestGroupCancel w) s eq direct = CIPaths.same-shutdown (ci-request-group-projects w s eq)
 direct-shutdown-same (W.deliverGroup w) s eq direct = CIPaths.same-shutdown (ci-deliver-group-projects w s eq)
 direct-shutdown-same (W.joinGroup w) s eq direct = CIPaths.same-shutdown (ci-join-group-projects w s eq)
 direct-shutdown-same (W.finishGroup w) s eq direct = CIPaths.same-shutdown (ci-finish-group-projects w s eq)
 direct-shutdown-same (W.drainEmpty w) s eq direct = CIPaths.same-shutdown (ci-from-phase-projects w W.draining W.drainReady s (GroupProperties.drain-phase isBearerClosed w s eq))
 direct-shutdown-same (W.timeout2Elapsed w) s eq direct = CIPaths.same-shutdown (ci-from-phase-projects w W.draining W.drainReady s eq)
 direct-shutdown-same (W.writeStopped w) s eq direct = CIPaths.same-shutdown (ci-source-phase-projects w W.drainReady W.stoppedTrace IG.completeMuxStopping s eq)
 direct-shutdown-same (W.observeTraceStopped w) s eq direct = CIPaths.same-shutdown (ci-source-phase-projects w W.stoppedTrace W.stoppedTracing IG.traceGracefulMuxStopped s eq)
 direct-shutdown-same (W.sampleStoppedTracer w) s eq direct = CIPaths.same-shutdown (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.sampleTracer s eq)
 direct-shutdown-same (W.commitStoppedTracer w) s eq direct = CIPaths.same-shutdown (ci-source-phase-projects w W.stoppedTracing W.stoppedTracing IG.commitTracer s eq)
 direct-shutdown-same (W.finishStoppedTrace w) s eq direct = CIPaths.same-shutdown (ci-finish-stopped-projects w s eq)
 direct-shutdown-same (W.finishChildUnwind j) s eq direct = CIPaths.same-shutdown (ci-unwind-projects j s eq)
 direct-shutdown-same (W.unwindReplacedBySync j err) s eq direct = CIPaths.same-shutdown (ci-replacement-projects j err s eq)
 direct-shutdown-same (W.abortOwner w err) s eq direct = CIPaths.same-shutdown (ci-abort-projects w err s eq)
 direct-shutdown-same (W.beginWholeClose w order) s eq direct = CIPaths.same-shutdown (ci-begin-whole-projects w order s eq)
 direct-shutdown-same (W.requestWholeCancel w) s eq direct = CIPaths.same-shutdown (ci-whole-action-projects w Pool.requestCancel s eq)
 direct-shutdown-same (W.deliverWhole w) s eq direct = CIPaths.same-shutdown (ci-whole-delivery-projects w s eq)
 direct-shutdown-same (W.joinWhole w) s eq direct = CIPaths.same-shutdown (ci-whole-action-projects w Pool.join s eq)
 direct-shutdown-same (W.finishWholeClose w) s eq direct = CIPaths.same-shutdown (ci-finish-whole-projects w s eq)
 direct-shutdown-same (W.finishNormalScope w) s eq direct = CIPaths.same-shutdown (ci-finish-ordinary-projects w s eq)
 direct-shutdown-same (W.writeAsyncFailure w) s eq direct = CIPaths.same-shutdown (ci-async-failure-projects w s eq)
 direct-shutdown-same (W.beginAsyncDead w) s eq direct = CIPaths.same-shutdown (ci-async-dead-projects w s eq)
 direct-shutdown-same (W.sampleAsyncTracer w) s eq direct = CIPaths.same-shutdown (ci-async-trace-projects true w s eq)
 direct-shutdown-same (W.commitAsyncTracer w) s eq direct = CIPaths.same-shutdown (ci-async-trace-projects false w s eq)
 direct-shutdown-same (W.finishAsyncDead w) s eq direct = CIPaths.same-shutdown (ci-finish-async-projects w s eq)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with M.initial c in actual
 ... | nothing = case eq of λ ()
 ... | just m = case just-injective eq of λ { refl → Lower.initialized-valid c actual }


import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.HandlerLifecycle as Life
module Exit (isBearerClosed : ErrorId → Bool) where
 private module W = ExitModel isBearerClosed using (Action; Frame; Plan; State; acknowledgeFinished; acknowledgeReleaseFinished; deliverReleaseMux; releaseTarget; releaseDelivery; base; beginExit; bodyExited; bufferScope; choose; choosePolicy; classifying; cleanup; cleanupComplete; cleanupException; cleanupFault; control; coordinator; currentCapture; delegateAllowed; deliverShutdownMux; deliverShutdownTimeWait; edit; effectiveResult; enact; enterFinalizer; errorTracing; exits; finalizing; finishCleanup; inherited; initial; local; machine; muxDelivery; nodeDelivery; nodeRethrow; noteCleanup; observeBufferException; observeBufferReturn; observeErrorTrace; observeNodeDelivery; peerRethrow; phase; physical; poolAt; publishAsyncResult; resultAvailable; resultReady; rethrow; run; sameCleanup; sameStart; setShutdown; setSource; shared; shutdown; shutdownStep; source; step; timeWaitDelivery)
 private module G = GroupModel isBearerClosed using (abortOwner; asyncDeadTracing; asyncExit; asyncFailureWritten; drainReady; draining; failedExit; frameAt; groupClosing; idle; initial; monitorReturnedNormal; normalExit; ownerAborting; phase; protocolState; scopeDone; setPool; shutdownSelected; step; stoppedTrace; stoppedTracing; stoppingTraced; stoppingWritten; wholeClosed; wholeClosing)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base)
 private module U = P.U using (captured; frames)
 private module Pool = P.Pool using (cancelPending; closedPool; closing; joinPending; openPool; phase)
 private module Lower = Group isBearerClosed using (Valid; initialized-valid; step-preserves; direct-shutdown-same)
 view : W.State → Birth.Registry
 view = Birth.ExitLayer.view isBearerClosed
 Valid : W.State → Set
 Valid s = Lower.Valid (W.base s) × Covers (W.exits s) (view s)
 lower-valid : ∀ {s} → Valid s → Lower.Valid (W.base s)
 lower-valid = proj₁
 exits-present : ∀ {s} → Valid s → Covers (W.exits s) (view s)
 exits-present = proj₂
 frames-present : ∀ {s} → Valid s → Covers (U.frames (P.base (G.protocolState (W.base s)))) (view s)
 frames-present valid = proj₁ valid
 source-valid : ∀ c s → Valid s → Valid (W.setSource c s)
 source-valid c s valid = valid
 shutdown-valid : ∀ coordinator s → Valid s → Valid (W.setShutdown coordinator s)
 shutdown-valid coordinator s valid = valid
 local-valid : ∀ fs s → Covers fs (view s) → Valid s → Valid (record s { exits = fs })
 local-valid fs s cover valid = proj₁ valid , cover
 setPool-valid : ∀ w f p s → Present w (view s) → Valid s → Valid (record s { base = G.setPool w f p (W.base s) })
 setPool-valid w f p s present valid = Protocol.pool-valid w f p (G.protocolState (W.base s)) present (proj₁ valid) , proj₂ valid
 edit-covers : ∀ w f pc s → lookup w (W.exits s) ≡ just f → Valid s → Covers (W.edit w f pc s) (view s)
 edit-covers w f pc s found valid = covers-put w _ (W.exits s) (view s) (proj₂ valid w f found) (proj₂ valid)
 note-covers : ∀ w action s → Valid s → Covers (W.noteCleanup w action s) (view s)
 note-covers w action s valid with lookup w (W.exits s) in found | W.cleanupFault action
 ... | just f | just fault = covers-put w _ (W.exits s) (view s) (proj₂ valid w f found) (proj₂ valid)
 ... | nothing | _ = proj₂ valid
 ... | just f | nothing = proj₂ valid
 control-preserves : ∀ a s {t} → W.control a s ≡ just t → Valid s → Valid t
 control-preserves a s eq valid with Close.step (S.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → shutdown-valid next s valid }
 data PlanSafe : W.Plan → W.State → Set where
  safe-local : ∀ {fs s} → Covers fs (view s) → PlanSafe (W.local fs) s
  safe-machine : ∀ {a fs s} → Covers fs (view s) → PlanSafe (W.machine a fs) s
  safe-inherited : ∀ {a s} → PlanSafe (W.inherited a) s
  safe-coordinator : ∀ {a s} → PlanSafe (W.coordinator a) s
  safe-muxDelivery : ∀ {w err s} → PlanSafe (W.muxDelivery w err) s
  safe-timeWaitDelivery : ∀ {w err s} → PlanSafe (W.timeWaitDelivery w err) s
  safe-releaseDelivery : ∀ {caller worker err s} → PlanSafe (W.releaseDelivery caller worker err) s
 enact-preserves : ∀ p s {t} → W.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (W.local fs) s eq valid (safe-local cover) = case just-injective eq of λ { refl → local-valid fs s cover valid }
 enact-preserves (W.machine a fs) s eq valid (safe-machine cover) with O.advance a (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → local-valid fs (W.setSource c s) cover valid }
 enact-preserves (W.inherited a) s eq valid safe-inherited with G.step a (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Lower.step-preserves a (W.base s) actual (proj₁ valid) ,
   covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
     (change-retains (Birth.GroupLayer.change isBearerClosed a (W.base s) actual)) (proj₂ valid) }
 enact-preserves (W.coordinator a) s eq valid safe-coordinator = control-preserves a s eq valid
 enact-preserves (W.muxDelivery w err) s eq valid safe-muxDelivery with G.step (G.abortOwner w err) (W.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just g = control-preserves Close.acknowledgeDelivery (record s { base = g }) eq
   (Lower.step-preserves (G.abortOwner w err) (W.base s) actual (proj₁ valid) ,
    covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
     (change-retains (Birth.GroupLayer.change isBearerClosed (G.abortOwner w err) (W.base s) actual)) (proj₂ valid))
 enact-preserves (W.timeWaitDelivery w err) s eq valid safe-timeWaitDelivery with O.advance
   (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = control-preserves Close.acknowledgeDelivery
   (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq
   (proj₁ valid , note-covers w (Cleanup.interruptTimeWait err) s valid)
 enact-preserves (W.releaseDelivery caller worker err) s eq valid safe-releaseDelivery with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → source-valid c (record s { base = g })
   (Lower.step-preserves (G.abortOwner worker err) (W.base s) aborted (proj₁ valid) ,
    covers-retained {rows = W.exits s} {before = view s} {after = Birth.GroupLayer.view isBearerClosed g}
      (change-retains (Birth.GroupLayer.change isBearerClosed (G.abortOwner worker err) (W.base s) aborted)) (proj₂ valid)) }
 choose-safe : ∀ a s {p} → W.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe (W.run a) s eq valid with W.delegateAllowed a
 ... | true = case just-injective eq of λ { refl → safe-inherited }
 ... | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid with lookup w (W.exits s) | lookup w (U.frames (P.base (G.protocolState (W.base s)))) in found |
   G.phase (G.frameAt w (W.base s)) | Pool.phase (W.poolAt w s)
 ... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (S.handlers (W.shared s))
 ...   | just h with W.sameStart (U.captured f) h
 ...     | true = case just-injective eq of λ { refl → safe-local (covers-put w _ (W.exits s) (view s) (frames-present {s = s} valid w f found) (proj₂ valid)) }
 ...     | false = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | just old | _ | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | nothing | _ | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.idle | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.shutdownSelected | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingTraced | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppingWritten | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.groupClosing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.draining | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.drainReady | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTrace | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.stoppedTracing | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.monitorReturnedNormal | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.ownerAborting err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosing outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.wholeClosed outcome | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncFailureWritten err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.asyncDeadTracing err | _ = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.openPool = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.closing = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.cancelPending j = case eq of λ ()
 choose-safe (W.beginExit w) s eq valid | nothing | just f | G.scopeDone outcome | Pool.joinPending j = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferReturn w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w G.normalExit) s eq valid = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.failedExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeBufferException w (G.asyncExit err)) s eq valid | nothing = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.classifying err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.choosePolicy w policy) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.errorTracing err Life.shutdownPeer = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...   | W.errorTracing err Life.shutdownNode = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeErrorTrace w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.nodeDelivery err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.observeNodeDelivery w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.peerRethrow err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...   | W.nodeRethrow err = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 choose-safe (W.rethrow w) s eq valid | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.classifying otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.rethrow w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid with lookup w (W.exits s) in found
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.bodyExited result | true = case just-injective eq of λ { refl → safe-machine (edit-covers w f _ s found valid) }
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.finalizing otherResult | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | just f | W.bodyExited otherResult | false = case eq of λ ()
 choose-safe (W.enterFinalizer w) s eq valid | nothing = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid with lookup w (W.exits s)
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.finalizing result | true = case just-injective eq of λ { refl → safe-machine (note-covers w action s valid) }
 choose-safe (W.cleanup w action) s eq valid | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | just f | W.finalizing otherResult | false = case eq of λ ()
 choose-safe (W.cleanup w action) s eq valid | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.finalizing result with W.effectiveResult result outcome (W.cleanupException f)
 ...     | just effective = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...     | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.finishCleanup w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.cleanupComplete result observed with W.sameCleanup observed outcome
 ...     | true = case just-injective eq of λ { refl → safe-local (edit-covers w f _ s found valid) }
 ...     | false = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.finalizing otherResult = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | nothing = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.publishAsyncResult w) s eq valid | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.shutdownStep Close.acknowledgeDelivery) s eq valid = case eq of λ ()
 choose-safe (W.shutdownStep Close.captureSnapshot) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.readEntry) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.requestCancellation) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishTraversal) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.shutdownStep Close.finishClose) s eq valid = case just-injective eq of λ { refl → safe-coordinator }
 choose-safe (W.deliverShutdownMux err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w = case just-injective eq of λ { refl → safe-muxDelivery }
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownMux err) s eq valid | Close.closed = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with lookup w (W.exits s) | lookup w (S.cleanups (W.shared s))
 ...   | just f | just (S.cleanupWaiting h) with W.phase f | W.currentCapture w f s
 ...     | W.finalizing result | true = case just-injective eq of λ { refl → safe-timeWaitDelivery }
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.classifying otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.peerRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.bodyExited otherResult | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupWaiting h) | W.finalizing result | false = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | nothing | _ = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | nothing = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitDelivery e w | just f | just (S.cleanupDone outcome) = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.initial = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.reading = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe (W.deliverShutdownTimeWait err) s eq valid | Close.closed = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with W.resultReady w s
 ...   | true = case just-injective eq of λ { refl → safe-coordinator }
 ...   | false = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.initial = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.reading = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.sendReady e w = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.awaitResults = case eq of λ ()
 choose-safe W.acknowledgeFinished s eq valid | Close.closed = case eq of λ ()

 choose-safe (W.deliverReleaseMux caller err) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → safe-releaseDelivery }
 choose-safe (W.acknowledgeReleaseFinished caller) s eq valid with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker with W.resultReady worker s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → safe-machine (proj₂ valid) }

 step-preserves : ∀ a s {t} → W.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with W.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 initialized-valid : ∀ c {s} → W.initial c ≡ just s → Valid s
 initialized-valid c eq with G.initial c in initialized
 ... | nothing = case eq of λ ()
 ... | just g = case just-injective eq of λ { refl → Lower.initialized-valid c initialized , covers-empty {W.Frame} (Birth.GroupLayer.view isBearerClosed g) }
 resultReady-present : ∀ {s w} → Valid s → W.resultReady w s ≡ true → Present w (view s)
 resultReady-present {s} {w} valid ready with lookup w (W.exits s) in found
 ... | just f = proj₂ valid w f found
 ... | nothing with lookup w (U.frames (P.base (G.protocolState (W.base s))))
 ...   | just f = case ready of λ ()
 ...   | nothing with lookup w (B.threads (W.physical s)) in thread
 ...     | just physical = physical-present w (W.physical s) (physical , thread)
 ...     | nothing = case ready of λ ()
 IsPlain : W.Action → Set
 IsPlain (W.run a) = ⊥
 IsPlain (W.shutdownStep a) = ⊥
 IsPlain (W.deliverShutdownMux err) = ⊥
 IsPlain (W.deliverShutdownTimeWait err) = ⊥
 IsPlain W.acknowledgeFinished = ⊥
 IsPlain _ = ⊤
 PlainPlan : W.Plan → Set
 PlainPlan (W.local fs) = ⊤
 PlainPlan (W.machine a fs) = ⊤
 PlainPlan (W.releaseDelivery caller worker err) = ⊤
 PlainPlan _ = ⊥
 choose-plain : ∀ a s {p} → W.choose a s ≡ just p → IsPlain a → PlainPlan p
 choose-plain (W.run a) s eq ()
 choose-plain (W.shutdownStep a) s eq ()
 choose-plain (W.deliverShutdownMux err) s eq ()
 choose-plain (W.deliverShutdownTimeWait err) s eq ()
 choose-plain W.acknowledgeFinished s eq ()
 choose-plain (W.deliverReleaseMux caller err) s eq plain with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker = case just-injective eq of λ { refl → tt }
 choose-plain (W.acknowledgeReleaseFinished caller) s eq plain with W.releaseTarget caller s
 ... | nothing = case eq of λ ()
 ... | just worker with W.resultReady worker s
 ...   | false = case eq of λ ()
 ...   | true = case just-injective eq of λ { refl → tt }
 choose-plain (W.beginExit w) s eq plain with lookup w (W.exits s) | lookup w (U.frames (P.base (G.protocolState (W.base s)))) in found |
   G.phase (G.frameAt w (W.base s)) | Pool.phase (W.poolAt w s)
 ... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (S.handlers (W.shared s))
 ...   | just h with W.sameStart (U.captured f) h
 ...     | true = case just-injective eq of λ { refl → tt }
 ...     | false = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | just old | _ | _ | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | nothing | _ | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.idle | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.shutdownSelected | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.stoppingTraced | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.stoppingWritten | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.groupClosing | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.draining | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.drainReady | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.stoppedTrace | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.stoppedTracing | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.monitorReturnedNormal | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.ownerAborting err | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.wholeClosing outcome | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.wholeClosed outcome | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.asyncFailureWritten err | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.asyncDeadTracing err | _ = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.scopeDone outcome | Pool.openPool = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.scopeDone outcome | Pool.closing = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.scopeDone outcome | Pool.cancelPending j = case eq of λ ()
 choose-plain (W.beginExit w) s eq plain | nothing | just f | G.scopeDone outcome | Pool.joinPending j = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → tt }
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferReturn w) s eq plain | nothing = case eq of λ ()
 choose-plain (W.observeBufferException w G.normalExit) s eq plain = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → tt }
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferException w (G.failedExit err)) s eq plain | nothing = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.bufferScope outcome = case just-injective eq of λ { refl → tt }
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeBufferException w (G.asyncExit err)) s eq plain | nothing = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.classifying err = case just-injective eq of λ { refl → tt }
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.choosePolicy w policy) s eq plain | nothing = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.errorTracing err Life.shutdownPeer = case just-injective eq of λ { refl → tt }
 ...   | W.errorTracing err Life.shutdownNode = case just-injective eq of λ { refl → tt }
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeErrorTrace w) s eq plain | nothing = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.nodeDelivery err = case just-injective eq of λ { refl → tt }
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.observeNodeDelivery w) s eq plain | nothing = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f
 ...   | W.peerRethrow err = case just-injective eq of λ { refl → tt }
 ...   | W.nodeRethrow err = case just-injective eq of λ { refl → tt }
 choose-plain (W.rethrow w) s eq plain | just f | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.classifying otherError = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | just f | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.rethrow w) s eq plain | nothing = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain with lookup w (W.exits s) in found
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.bodyExited result | true = case just-injective eq of λ { refl → tt }
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.classifying otherError | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.finalizing otherResult | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | just f | W.bodyExited otherResult | false = case eq of λ ()
 choose-plain (W.enterFinalizer w) s eq plain | nothing = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain with lookup w (W.exits s)
 ... | just f with W.phase f | W.currentCapture w f s
 ...   | W.finalizing result | true = case just-injective eq of λ { refl → tt }
 choose-plain (W.cleanup w action) s eq plain | just f | W.bufferScope otherOutcome | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.classifying otherError | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.errorTracing otherError otherPolicy | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.peerRethrow otherError | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.nodeDelivery otherError | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.nodeRethrow otherError | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.bodyExited otherResult | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.cleanupComplete otherResult otherCleanup | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.resultAvailable otherResult otherCleanup | _ = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | just f | W.finalizing otherResult | false = case eq of λ ()
 choose-plain (W.cleanup w action) s eq plain | nothing = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.finalizing result with W.effectiveResult result outcome (W.cleanupException f)
 ...     | just effective = case just-injective eq of λ { refl → tt }
 ...     | nothing = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.cleanupComplete otherResult otherCleanup = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | nothing | _ = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | nothing = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-plain (W.finishCleanup w) s eq plain | just f | just (S.cleanupCount outcome) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain with lookup w (W.exits s) in found | lookup w (S.cleanups (W.shared s))
 ... | just f | just (S.cleanupDone outcome) with W.phase f
 ...   | W.cleanupComplete result observed with W.sameCleanup observed outcome
 ...     | true = case just-injective eq of λ { refl → tt }
 ...     | false = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.bufferScope otherOutcome = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.classifying otherError = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.errorTracing otherError otherPolicy = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.peerRethrow otherError = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.nodeDelivery otherError = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.nodeRethrow otherError = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.bodyExited otherResult = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.finalizing otherResult = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupDone outcome) | W.resultAvailable otherResult otherCleanup = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | nothing | _ = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | nothing = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupAcquire) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupSelect savedLease) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupClose savedLease map tail) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupPublish savedLease map tail) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupRestore savedLease error) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupWaiting captured) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupFinalize captured outcome) = case eq of λ ()
 choose-plain (W.publishAsyncResult w) s eq plain | just f | just (S.cleanupCount outcome) = case eq of λ ()

 enact-shutdown-same : ∀ p s {t} → W.enact p s ≡ just t → PlainPlan p → W.shutdown t ≡ W.shutdown s
 enact-shutdown-same (W.local fs) s eq plain = case just-injective eq of λ { refl → refl }
 enact-shutdown-same (W.machine a fs) s eq plain with O.advance a (W.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → refl }
 enact-shutdown-same (W.inherited a) s eq ()
 enact-shutdown-same (W.coordinator a) s eq ()
 enact-shutdown-same (W.muxDelivery w err) s eq ()
 enact-shutdown-same (W.timeWaitDelivery w err) s eq ()
 enact-shutdown-same (W.releaseDelivery caller worker err) s eq plain with G.step (G.abortOwner worker err) (W.base s) in aborted
 ... | nothing = case eq of λ ()
 ... | just g with O.advance (O.release caller (OutboundRelease.cancellationDelivered worker)) (W.source (record s { base = g })) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just c = case just-injective eq of λ { refl → Lower.direct-shutdown-same (G.abortOwner worker err) (W.base s) aborted tt }
 plain-shutdown-same : ∀ a s {t} → W.step a s ≡ just t → IsPlain a → W.shutdown t ≡ W.shutdown s
 plain-shutdown-same a s eq plain with W.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-shutdown-same p s eq (choose-plain a s chosen plain)

import ConnectionManagement.MuxExitCancellation as CancellationModel
module Cancellation (isBearerClosed : ErrorId → Bool) where
 private module X = CancellationModel isBearerClosed using (State; deliver; deliverShutdown; observeCancellation; observeErrorTraceException; run; shutdownDelivery; step; target; traceThrew)
 private module W = ExitModel isBearerClosed using (bodyExited; bufferScope; classifying; cleanupComplete; edit; errorTracing; exits; finalizing; nodeDelivery; nodeRethrow; peerRethrow; phase; resultAvailable; shutdown; syncException)
 private module Lower = Exit isBearerClosed using (Valid; control-preserves; edit-covers; local-valid; step-preserves)
 Valid : X.State → Set
 Valid = Lower.Valid
 deliver-preserves : ∀ window w err s {t} → X.deliver window w err s ≡ just t → Valid s → Valid t
 deliver-preserves window w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with X.target window err (W.phase f)
 ...   | nothing = case eq of λ ()
 ...   | just pc = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f pc s) s (Lower.edit-covers w f pc s found valid) valid }
 trace-preserves : ∀ w err s {t} → X.traceThrew w err s ≡ just t → Valid s → Valid t
 trace-preserves w err s eq valid with lookup w (W.exits s) in found
 ... | nothing = case eq of λ ()
 ... | just f with W.phase f
 ...   | W.errorTracing original policy = case just-injective eq of λ { refl → Lower.local-valid (W.edit w f (W.bodyExited (W.syncException err)) s) s (Lower.edit-covers w f (W.bodyExited (W.syncException err)) s found valid) valid }
 ...   | W.bufferScope outcome = case eq of λ ()
 ...   | W.classifying original = case eq of λ ()
 ...   | W.peerRethrow original = case eq of λ ()
 ...   | W.nodeDelivery original = case eq of λ ()
 ...   | W.nodeRethrow original = case eq of λ ()
 ...   | W.bodyExited result = case eq of λ ()
 ...   | W.finalizing result = case eq of λ ()
 ...   | W.cleanupComplete result outcome = case eq of λ ()
 ...   | W.resultAvailable result outcome = case eq of λ ()
 shutdown-preserves : ∀ window err s {t} → X.shutdownDelivery window err s ≡ just t → Valid s → Valid t
 shutdown-preserves window err s eq valid with Close.phase (W.shutdown s)
 ... | Close.awaitDelivery e w with X.deliver window w err s in delivered
 ...   | nothing = case eq of λ ()
 ...   | just next = Lower.control-preserves Close.acknowledgeDelivery next eq (deliver-preserves window w err s delivered valid)
 shutdown-preserves window err s eq valid | Close.initial = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.reading = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.sendReady e w = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.awaitResults = case eq of λ ()
 shutdown-preserves window err s eq valid | Close.closed = case eq of λ ()
 step-preserves : ∀ a s {t} → X.step a s ≡ just t → Valid s → Valid t
 step-preserves (X.run a) = Lower.step-preserves a
 step-preserves (X.observeCancellation window w err) = deliver-preserves window w err
 step-preserves (X.deliverShutdown window err) = shutdown-preserves window err
 step-preserves (X.observeErrorTraceException w err) = trace-preserves w err

import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProperties
module Unwind (isBearerClosed : ErrorId → Bool) where
 private module R = UnwindModel isBearerClosed using (Action; Fault; Plan; State; acknowledge; allowed; async; asyncDead; asyncStatus; awaitingClose; base; beginClose; beginDead; cancellationPlan; choose; closing; commitDead; continueSync; deadThrowPoint; deliverCancel; deliverShutdown; deliveryControl; deliveryRoute; enact; faults; finishClose; finishDead; handedOff; handoff; inherited; initial; join; local; machine; mux; observeCancellation; observeDeadTraceException; observeFailure; outcome; owner; phase; pool; poolAt; poolClosed; protocols; readyBody; readyBuffer; requestCancel; run; sameClose; sampleDead; setPhase; setPool; setSource; siteControl; siteRoute; source; start; step; sync; transfer; withPool; writeAsyncFailure)
 private module W = ExitModel isBearerClosed using (base; control; exits; setShutdown; shutdown)
 private module X = CancellationModel isBearerClosed using (initial; step)
 private module G = GroupModel isBearerClosed using (module M; protocolState; wholeDeliverable)
 private module P = ProtocolModel using (hasWanton; enterProtocolBody; appendProtocolPayload; egressMuxer; module Pool; module U; base; muxAt)
 private module U = P.U using (frames)
 private module Pool = P.Pool using (beginClose; cancelPending; closedPool; closing; finishClose; join; joinPending; openPool; phase; requestCancel; step)
 private module M = G.M using (failed; finishMatches)
 private module F = UnwindProperties isBearerClosed using (Selection; selection-observation)
 private module Lower = Exit isBearerClosed using (Valid; control-preserves; exits-present; frames-present; initialized-valid; local-valid; setPool-valid; shutdown-valid)
 private module Cancel = Cancellation isBearerClosed using (step-preserves)
 view : R.State → Birth.Registry
 view = Birth.UnwindLayer.view isBearerClosed
 Valid : R.State → Set
 Valid s = Lower.Valid (R.base s) × Covers (R.faults s) (view s)
 lower-valid : ∀ {s} → Valid s → Lower.Valid (R.base s)
 lower-valid = proj₁
 frames-present : ∀ {s} → Valid s → Covers (U.frames (P.base (G.protocolState (W.base (R.base s))))) (view s)
 frames-present {s} valid = Lower.frames-present {s = R.base s} (proj₁ valid)
 exits-present : ∀ {s} → Valid s → Covers (W.exits (R.base s)) (view s)
 exits-present {s} valid = Lower.exits-present {s = R.base s} (proj₁ valid)
 faults-present : ∀ {s} → Valid s → Covers (R.faults s) (view s)
 faults-present = proj₂
 source-valid : ∀ c s → Valid s → Valid (R.setSource c s)
 source-valid c s valid = valid
 shutdown-valid : ∀ coordinator s → Valid s → Valid (record s { base = W.setShutdown coordinator (R.base s) })
 shutdown-valid coordinator s valid = Lower.shutdown-valid coordinator (R.base s) (proj₁ valid) , proj₂ valid
 local-valid : ∀ fs s → Covers fs (view s) → Valid s → Valid (record s { faults = fs })
 local-valid fs s cover valid = proj₁ valid , cover
 setPool-valid : ∀ w f p s → Present w (view s) → Valid s → Valid (R.setPool w f p s)
 setPool-valid w f p s present valid = Lower.setPool-valid w f p (R.base s) present (proj₁ valid) , proj₂ valid
 phase-covers : ∀ w f pc s → lookup w (R.faults s) ≡ just f → Valid s → Covers (R.setPhase w f pc s) (view s)
 phase-covers w f pc s found valid = covers-put w _ (R.faults s) (view s) (proj₂ valid w f found) (proj₂ valid)
 data PlanSafe : R.Plan → R.State → Set where
  safe-local : ∀ {fs s} → Covers fs (view s) → PlanSafe (R.local fs) s
  safe-machine : ∀ {a fs s} → Covers fs (view s) → PlanSafe (R.machine a fs) s
  safe-pool : ∀ {w u a fs s} → Present w (view s) → Covers fs (view s) → PlanSafe (R.pool w u a fs) s
  safe-transfer : ∀ {w f fs s} → Present w (view s) → Covers fs (view s) → PlanSafe (R.transfer w f fs) s
  safe-inherited : ∀ {a s} → PlanSafe (R.inherited a) s
  safe-acknowledge : ∀ {p s} → PlanSafe p s → PlanSafe (R.acknowledge p) s
 enact-preserves : ∀ p s {t} → R.enact p s ≡ just t → Valid s → PlanSafe p s → Valid t
 enact-preserves (R.local fs) s eq valid (safe-local cover) = case just-injective eq of λ { refl → local-valid fs s cover valid }
 enact-preserves (R.machine a fs) s eq valid (safe-machine cover) with O.advance a (R.source s)
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → local-valid fs (R.setSource c s) cover valid }
 enact-preserves (R.pool w u a fs) s eq valid (safe-pool present cover) with Pool.step a (R.poolAt w s)
 ... | nothing = case eq of λ ()
 ... | just p = case just-injective eq of λ { refl → local-valid fs (R.setPool w u p s) cover (setPool-valid w u p s present valid) }
 enact-preserves (R.transfer w f fs) s eq valid (safe-transfer present cover) = case just-injective eq of λ { refl →
   Lower.local-valid (put w f (W.exits (R.base s))) (R.base s)
     (covers-put w f (W.exits (R.base s)) (view s) present (exits-present {s = s} valid)) (proj₁ valid) , cover }
 enact-preserves (R.inherited a) s eq valid safe-inherited with X.step a (R.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Cancel.step-preserves a (R.base s) actual (proj₁ valid) ,
   covers-retained {rows = R.faults s} {before = view s} {after = Birth.CancellationLayer.view isBearerClosed x}
     (change-retains (Birth.CancellationLayer.change isBearerClosed a (R.base s) actual)) (proj₂ valid) }
 enact-preserves (R.acknowledge p) s eq valid (safe-acknowledge safe) with R.enact p s in actual
 ... | nothing = case eq of λ ()
 ... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
 ...   | nothing = case eq of λ ()
 ...   | just w = case just-injective eq of λ { refl → Lower.control-preserves Close.acknowledgeDelivery (R.base next) acknowledged (proj₁ following) ,
   subst (Covers (R.faults next))
     (sym (Birth.ExitLayer.CIPaths.retention (Birth.ExitLayer.ci-control-projects isBearerClosed Close.acknowledgeDelivery (R.base next) acknowledged)))
     (proj₂ following) }
   where following = enact-preserves p s actual valid safe
 start-safe : ∀ w result route s {p} → R.start w result route s ≡ just p → Valid s → PlanSafe p s
 start-safe w result route s chosen valid with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = safe-local
   (covers-put w _ (R.faults s) (view s) (frames-present {s = s} valid w _ (F.Selection.owner-found selected)) (proj₂ valid))
 IsDirect : R.Action → Set
 IsDirect (R.run a) = ⊥
 IsDirect (R.deliverShutdown site err) = ⊥
 IsDirect _ = ⊤
 NonAck : R.Plan → Set
 NonAck (R.acknowledge p) = ⊥
 NonAck _ = ⊤
 ChosenSafe : R.Action → R.Plan → R.State → Set
 ChosenSafe a p s = PlanSafe p s × (IsDirect a → NonAck p)
 start-nonack : ∀ w result route s {p} → R.start w result route s ≡ just p → NonAck p
 start-nonack w result route s chosen with F.selection-observation w result route s chosen
 ... | selected rewrite F.Selection.plan-shape selected = tt
 cancellation-safe : ∀ w site err s {p} → R.cancellationPlan w site err s ≡ just p → Valid s → PlanSafe p s × NonAck p
 cancellation-safe w site err s eq valid with R.deliveryControl w site s
 ... | false = case eq of λ ()
 ... | true = start-safe w (R.async err) (λ f m → R.deliveryRoute site f m) s eq valid ,
   start-nonack w (R.async err) (λ f m → R.deliveryRoute site f m) s eq
 pool-safe : ∀ w before action after s {p} → R.withPool w before action after s ≡ just p → Valid s → PlanSafe p s × NonAck p
 pool-safe w before action after s eq valid with lookup w (R.faults s) in found | R.owner w s in owner
 ... | just f | just u with R.sameClose before (R.phase f)
 ...   | true = case just-injective eq of λ { refl → safe-pool (frames-present {s = s} valid w u owner) (phase-covers w f after s found valid) , tt }
 ...   | false = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | nothing = case eq of λ ()
 pool-safe w before action after s eq valid | nothing | just u = case eq of λ ()
 pool-safe w before action after s eq valid | just f | nothing = case eq of λ ()
 chosen-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → ChosenSafe a p s
 chosen-safe (R.run a) s eq valid with R.allowed a s
 ... | true = case just-injective eq of λ { refl → safe-inherited , λ () }
 ... | false = case eq of λ ()
 chosen-safe (R.observeFailure w site err) s eq valid with R.siteControl w site s
 ... | true = start-safe w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq valid ,
   (λ _ → start-nonack w (R.sync err) (λ f m → R.siteRoute w site f m s) s eq)
 ... | false = case eq of λ ()
 chosen-safe (R.observeCancellation w site err) s eq valid with cancellation-safe w site err s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverShutdown site err) s eq valid with Close.phase (W.shutdown (R.base s))
 ... | Close.awaitDelivery e w with R.cancellationPlan w site err s in cancelled
 ...   | just p = case just-injective eq of λ { refl → safe-acknowledge (proj₁ (cancellation-safe w site err s cancelled valid)) , λ () }
 ...   | nothing = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.initial = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.reading = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.sendReady e w = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.awaitResults = case eq of λ ()
 chosen-safe (R.deliverShutdown site err) s eq valid | Close.closed = case eq of λ ()
 chosen-safe (R.beginClose w order) s eq valid with pool-safe w R.awaitingClose (Pool.beginClose order) R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.requestCancel w) s eq valid with pool-safe w R.closing Pool.requestCancel R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.join w) s eq valid with pool-safe w R.closing Pool.join R.closing s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.finishClose w) s eq valid with pool-safe w R.closing Pool.finishClose R.poolClosed s eq valid
 ... | safe , plain = safe , (λ _ → plain)
 chosen-safe (R.deliverCancel w) s eq valid with lookup w (R.faults s) | R.owner w s in owner | Pool.phase (R.poolAt w s)
 ... | just f | just u | Pool.cancelPending j with R.phase f | G.wholeDeliverable w j u (W.base (R.base s))
 ...   | R.closing | true = case just-injective eq of λ { refl → safe-pool (frames-present {s = s} valid w u owner) (proj₂ valid) , λ _ → tt }
 ...   | R.readyBody | _ = case eq of λ ()
 ...   | R.readyBuffer | _ = case eq of λ ()
 ...   | R.awaitingClose | _ = case eq of λ ()
 ...   | R.poolClosed | _ = case eq of λ ()
 ...   | R.asyncStatus | _ = case eq of λ ()
 ...   | R.asyncDead | _ = case eq of λ ()
 ...   | R.handedOff | _ = case eq of λ ()
 ...   | R.closing | false = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | nothing | _ | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | nothing | _ = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.openPool = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closing = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.deliverCancel w) s eq valid | just f | just u | Pool.closedPool = case eq of λ ()

 chosen-safe (R.continueSync w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.sync err = case just-injective eq of λ { refl → safe-local (phase-covers w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.async err = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.continueSync w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.writeAsyncFailure w) s eq valid with lookup w (R.faults s) in found | Pool.phase (R.poolAt w s)
 ... | just f | Pool.closedPool with R.phase f | R.outcome f
 ...   | R.poolClosed | R.async err = case just-injective eq of λ { refl → safe-machine (phase-covers w f R.asyncStatus s found valid) , λ _ → tt }
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.poolClosed | R.sync err = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.closing | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closedPool | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.openPool = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.closing = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.cancelPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | just f | Pool.joinPending j = case eq of λ ()
 chosen-safe (R.writeAsyncFailure w) s eq valid | nothing | _ = case eq of λ ()

 chosen-safe (R.beginDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncStatus = case just-injective eq of λ { refl → safe-machine (phase-covers w f R.asyncDead s found valid) , λ _ → tt }
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.asyncDead = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.beginDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.sampleDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine (proj₂ valid) , λ _ → tt }
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.sampleDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.commitDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f
 ...   | R.asyncDead = case just-injective eq of λ { refl → safe-machine (proj₂ valid) , λ _ → tt }
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBody = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.readyBuffer = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.awaitingClose = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.closing = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.poolClosed = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.asyncStatus = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | just f | R.handedOff = case eq of λ ()
 chosen-safe (R.commitDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.finishDead w) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | R.async err | just m with WireMux.callback m | M.finishMatches (M.failed err) (WireMux.status m)
 ...     | WireMux.returned | true = case just-injective eq of λ { refl → safe-local (phase-covers w f R.readyBuffer s found valid) , λ _ → tt }
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.returned | false = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.readActive tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.commitTrace active tr | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterStart n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.forkPending n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.afterFailure | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | just m | WireMux.tracerFailed n | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.async err | nothing = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncDead | R.sync err | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBody | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.readyBuffer | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.awaitingClose | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.closing | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.poolClosed | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.asyncStatus | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | just f | R.handedOff | _ | _ = case eq of λ ()
 chosen-safe (R.finishDead w) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.observeDeadTraceException w err) s eq valid with lookup w (R.faults s) in found
 ... | just f with R.phase f | P.muxAt (R.mux f) (R.protocols s)
 ...   | R.asyncDead | just m with R.deadThrowPoint m
 ...     | true = case just-injective eq of λ { refl → safe-local (covers-put w _ (R.faults s) (view s) (proj₂ valid w f found) (proj₂ valid)) , λ _ → tt }
 ...     | false = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncDead | nothing = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBody | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.readyBuffer | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.closing | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | just f | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.observeDeadTraceException w err) s eq valid | nothing = case eq of λ ()

 chosen-safe (R.handoff w) s eq valid with lookup w (R.faults s) in found | lookup w (W.exits (R.base s))
 ... | just f | nothing with R.phase f | R.outcome f
 ...   | R.readyBuffer | result = case just-injective eq of λ { refl → safe-transfer (proj₂ valid w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.sync err = case just-injective eq of λ { refl → safe-transfer (proj₂ valid w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 ...   | R.readyBody | R.async err = case just-injective eq of λ { refl → safe-transfer (proj₂ valid w f found) (phase-covers w f R.handedOff s found valid) , λ _ → tt }
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.awaitingClose | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.closing | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.poolClosed | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncStatus | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.asyncDead | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | nothing | R.handedOff | _ = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | just f | just exit = case eq of λ ()
 chosen-safe (R.handoff w) s eq valid | nothing | _ = case eq of λ ()
 choose-safe : ∀ a s {p} → R.choose a s ≡ just p → Valid s → PlanSafe p s
 choose-safe a s chosen valid = proj₁ (chosen-safe a s chosen valid)
 chosen-nonack : ∀ a s {p} → R.choose a s ≡ just p → Valid s → IsDirect a → NonAck p
 chosen-nonack a s chosen valid = proj₂ (chosen-safe a s chosen valid)
 step-preserves : ∀ a s {t} → R.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with R.choose a s in chosen
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid (choose-safe a s chosen valid)
 initialized-valid : ∀ c {s} → R.initial c ≡ just s → Valid s
 initialized-valid c eq with X.initial c in initialized
 ... | nothing = case eq of λ ()
 ... | just x = case just-injective eq of λ { refl → Lower.initialized-valid c initialized , covers-empty {R.Fault} (Birth.ExitLayer.view isBearerClosed x) }
