{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through the protocol-job layer: its own actions write the
-- source only by inbound dispatcher steps; a lifted action has the lower effect.
module ConnectionManagement.Properties.SourceKeysProtocol where

open import Data.Bool using (true; false)
import Data.Bool.Base
import Data.Nat
import Relation.Nullary
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxProtocolJobs as P
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysBase as Base
private
  module U = P.U
  module Pool = P.Pool
  module UK = Base.U Types.TypedResult

rootP : P.Action → Maybe O.Action
rootP (P.run a) = UK.rootU a
rootP _ = nothing

Same : P.State → P.State → Set
Same s s′ = KeySame (P.source s) (P.source s′)

inherit-keys : ∀ a s {s′} → P.inherit a s ≡ just s′ → Effect (UK.rootU a) (P.source s) (P.source s′)
inherit-keys a s eq with P.inheritedAllowed a
... | false = case eq of λ ()
... | true with U.step a (P.base s) in stepped
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → UK.step-keysU a (P.base s) stepped }

egress-keys : ∀ j act s {s′} → P.protocolEgress j act s ≡ just s′ → Same s s′
egress-keys j act s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (P.base s)) |
  lookup j (Pool.handles (P.poolAt (Types.owner job) s))
...   | Types.executing | just f | just Pool.bodyRunning with O.advance
  (O.inbound (Machine.igStep (IG.egressStep (Types.mux job) (act job)))) (P.source s) in advanced
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl →
  nonkey (O.inbound (Machine.igStep (IG.egressStep (Types.mux job) (act job)))) (P.source s) refl advanced }
egress-keys j act s eq | just job | Types.executing | just f | just Pool.bodyUnwinding = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | just f | just (Pool.bodyReturned _) = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | just f | just (Pool.deregisterPending _) = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | just f | just (Pool.deregistered _) = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | just f | just (Pool.resultAvailable _) = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | just f | nothing = case eq of λ ()
egress-keys j act s eq | just job | Types.executing | nothing | _ = case eq of λ ()
egress-keys j act s eq | just job | Types.waitingEgress | _ | _ = case eq of λ ()
egress-keys j act s eq | just job | Types.resultCaptured _ | _ | _ = case eq of λ ()
send-keys : ∀ j bytes s {s′} → P.sendProtocol j bytes s ≡ just s′ → Same s s′
send-keys j bytes s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with P.hasWanton j job s
...   | false = case eq of λ ()
...   | true = egress-keys j _ s eq

responder-keys : ∀ w j gen s {s′} → P.responderFork w j gen s ≡ just s′ → Same s s′
responder-keys w j gen s eq with lookup w (U.frames (P.base s)) | P.fresh j gen s
... | just f | true with U.progress f | P.monitoring f
...   | U.promisePublished hid mid | true with P.muxAt mid s
...     | just m with M.callback m
...       | M.forkPending n with P.forkBlocked w M.responderJob n (P.jobs s) m
...         | false with O.advance (O.inbound (Machine.igStep (IG.forkResponder mid))) (P.source s) in advanced |
  Pool.step (Pool.fork j) (P.poolAt w s)
...           | just c | just p = case just-injective eq of λ { refl →
  nonkey (O.inbound (Machine.igStep (IG.forkResponder mid))) (P.source s) refl advanced }
...           | just c | nothing = case eq of λ ()
...           | nothing | _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.forkPending n | true = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.readActive _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.commitTrace _ _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.afterStart _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.afterFailure = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.tracerFailed _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | M.returned = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | true | nothing = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.promisePublished hid mid | false = case eq of λ ()
responder-keys w j gen s eq | just f | true | (U.handshakePending helperPC) | _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.returnedSuccess | _ = case eq of λ ()
responder-keys w j gen s eq | just f | true | U.handleAllocated _ _ | _ = case eq of λ ()
responder-keys w j gen s eq | just f | false = case eq of λ ()
responder-keys w j gen s eq | nothing | _ = case eq of λ ()

initiator-keys : ∀ w j gen n s {s′} → P.initiatorFork w j gen n s ≡ just s′ → Same s s′
initiator-keys w j gen n s eq with lookup w (U.frames (P.base s)) | P.fresh j gen s
... | just f | true with U.progress f | P.monitoring f | M.findProtocol n (U.bundle f)
...   | U.promisePublished hid mid | true | just descriptor with P.muxAt mid s
...     | just m with M.status m | M.callback m | M.commands m | P.noResults (P.poolAt w s) | P.forkBlocked w M.initiatorJob n (P.jobs s) m
...       | M.ready | M.returned | [] | true | false with Pool.step (Pool.fork j) (P.poolAt w s)
...         | just p = case just-injective eq of λ { refl → same-refl _ }
...         | nothing = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.readActive _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.commitTrace _ _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.afterStart _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.forkPending _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.afterFailure | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.tracerFailed _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.returned | [] | true | true = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.returned | [] | false | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.ready | M.returned | _ ∷ _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.stopping | _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.stopped | _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | M.failed _ | _ | _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | nothing = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | (U.handshakePending helperPC) | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.returnedSuccess | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.handleAllocated _ _ | _ | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished _ _ | true | nothing = case eq of λ ()
initiator-keys w j gen n s eq | just f | true | U.promisePublished _ _ | false | _ = case eq of λ ()
initiator-keys w j gen n s eq | just f | false = case eq of λ ()
initiator-keys w j gen n s eq | nothing | _ = case eq of λ ()

register-keys : ∀ j s {s′} → P.register j s ≡ just s′ → Same s s′
register-keys j s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.parentFork (P.poolAt (Types.owner job) s)
...   | just f | just current with j ≟ current
...     | yes _ with Pool.step Pool.register (P.poolAt (Types.owner job) s)
...       | just p = case just-injective eq of λ { refl → same-refl _ }
...       | nothing = case eq of λ ()
register-keys j s eq | just job | just f | just current | no _ = case eq of λ ()
register-keys j s eq | just job | nothing | _ = case eq of λ ()
register-keys j s eq | just job | just _ | nothing = case eq of λ ()
returned-keys : ∀ j s {s′} → P.returned j s ≡ just s′ → Same s s′
returned-keys j s eq with lookup j (P.jobs s)
... | just job with Types.phase job
...   | Types.executing with P.hasWanton j job s
...     | false = case eq of λ ()
...     | true = case just-injective eq of λ { refl → same-refl _ }
returned-keys j s eq | just job | Types.waitingEgress = case eq of λ ()
returned-keys j s eq | just job | Types.resultCaptured _ = case eq of λ ()
returned-keys j s eq | nothing = case eq of λ ()

body-keys : ∀ job result s {c} → P.bodySource job result s ≡ just c → KeySame (P.source s) c
body-keys job result s eq with Types.direction job
... | M.initiatorJob = case just-injective eq of λ { refl → same-refl _ }
... | M.responderJob = nonkey (O.inbound (Machine.igStep
  (IG.finishProtocol (Types.mux job) (Types.protocolNumber job) result))) (P.source s) refl eq
append-source : ∀ job j s → P.source (P.appendPending job j s) ≡ P.source s
append-source job j s with Types.direction job
... | M.initiatorJob = refl
... | M.responderJob = refl
capture-keys : ∀ j job result s {s′} → P.capture j job result s ≡ just s′ → Same s s′
capture-keys j job result s eq with lookup (Types.owner job) (U.frames (P.base s)) |
  lookup j (Pool.handles (P.poolAt (Types.owner job) s))
... | just f | just Pool.bodyRunning with P.bodySource job result s in body
...   | just c = case just-injective eq of λ { refl → subst (λ x → KeySame (P.source s) x)
  (sym (append-source job j (record (P.setSource c s) { jobs = _ }))) (body-keys job result s body) }
...   | nothing = case eq of λ ()
capture-keys j job result s eq | nothing | _ = case eq of λ ()
capture-keys j job result s eq | just _ | nothing = case eq of λ ()
capture-keys j job result s eq | just _ | just Pool.bodyUnwinding = case eq of λ ()
capture-keys j job result s eq | just _ | just (Pool.bodyReturned _) = case eq of λ ()
capture-keys j job result s eq | just _ | just (Pool.deregisterPending _) = case eq of λ ()
capture-keys j job result s eq | just _ | just (Pool.deregistered _) = case eq of λ ()
capture-keys j job result s eq | just _ | just (Pool.resultAvailable _) = case eq of λ ()
clean-keys : ∀ j s {s′} → P.cleanCommit j s ≡ just s′ → Same s s′
clean-keys j s eq with lookup j (P.jobs s)
... | just job with Types.phase job
...   | Types.waitingEgress with P.cleanReady j job s
...     | false = case eq of λ ()
...     | true = capture-keys j job _ s eq
clean-keys j s eq | just job | Types.executing = case eq of λ ()
clean-keys j s eq | just job | Types.resultCaptured _ = case eq of λ ()
clean-keys j s eq | nothing = case eq of λ ()
sync-keys : ∀ j err s {s′} → P.syncError j err s ≡ just s′ → Same s s′
sync-keys j err s eq with lookup j (P.jobs s)
... | just job with P.canCapture (Types.phase job)
...   | true = capture-keys j job _ s eq
...   | false = case eq of λ ()
sync-keys j err s eq | nothing = case eq of λ ()

return-keys : ∀ j s {s′} → P.returnBody j s ≡ just s′ → Same s s′
return-keys j s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (P.base s))
...   | Types.resultCaptured result | just f with Pool.step
  (Pool.bodyReturnedWith j (P.capturedResult job result)) (P.poolAt (Types.owner job) s)
...     | just p = case just-injective eq of λ { refl → same-refl _ }
...     | nothing = case eq of λ ()
return-keys j s eq | just job | Types.executing | _ = case eq of λ ()
return-keys j s eq | just job | Types.waitingEgress | _ = case eq of λ ()
return-keys j s eq | just job | Types.resultCaptured _ | nothing = case eq of λ ()

publication-keys : ∀ j job outcome s {c kept} → P.publicationSource j job outcome s ≡ just (c , kept) → KeySame (P.source s) c
publication-keys j job outcome s eq with Types.direction job
... | M.initiatorJob = case just-injective eq of λ { refl → same-refl _ }
... | M.responderJob with P.locate j (P.pendingAt (Types.owner job) s) | P.muxAt (Types.mux job) s
...   | just (i , kept) | just m with IG.takePending i (M.finishedJobs m)
...     | just ((n , result) , rest) with Data.Bool.Base._∧_ (Relation.Nullary.does (Types.protocolNumber job Data.Nat.≟ n)) (P.sameOutcome outcome result)
...       | true with O.advance (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (P.source s) in advanced
...         | just c′ = case just-injective eq of λ { refl →
  nonkey (O.inbound (Machine.igStep (IG.publishJobOccurrence (Types.mux job) i))) (P.source s) refl advanced }
...         | nothing = case eq of λ ()
publication-keys j job outcome s eq | M.responderJob | just (i , kept) | just m | just ((n , result) , rest) | false = case eq of λ ()
publication-keys j job outcome s eq | M.responderJob | just (i , kept) | just m | nothing = case eq of λ ()
publication-keys j job outcome s eq | M.responderJob | just _ | nothing = case eq of λ ()
publication-keys j job outcome s eq | M.responderJob | nothing | _ = case eq of λ ()
removed-source : ∀ job kept s → P.source (P.removePublished job kept s) ≡ P.source s
removed-source job kept s with Types.direction job
... | M.initiatorJob = refl
... | M.responderJob = refl
publish-keys : ∀ j s {s′} → P.publish j s ≡ just s′ → Same s s′
publish-keys j s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (P.base s)) | lookup j (Pool.handles (P.poolAt (Types.owner job) s))
...   | Types.resultCaptured result | just f | just (Pool.bodyReturned value) with P.resultMatches job result value
...     | true with P.publicationSource j job result s in pub | Pool.step (Pool.publishCompletion j) (P.poolAt (Types.owner job) s)
...       | just (c , kept) | just p = case just-injective eq of λ { refl → subst (λ x → KeySame (P.source s) x)
  (sym (removed-source job kept (P.setPool (Types.owner job) f p (P.setSource c s)))) (publication-keys j job result s pub) }
...       | just _ | nothing = case eq of λ ()
...       | nothing | _ = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured result | just f | just (Pool.bodyReturned value) | false = case eq of λ ()
publish-keys j s eq | just job | Types.executing | _ | _ = case eq of λ ()
publish-keys j s eq | just job | Types.waitingEgress | _ | _ = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | nothing | _ = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | nothing = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyRunning = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyUnwinding = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregisterPending _) = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregistered _) = case eq of λ ()
publish-keys j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.resultAvailable _) = case eq of λ ()

via-protocol-keys : ∀ j act s {s′} → P.viaProtocol j act s ≡ just s′ → Same s s′
via-protocol-keys j act s eq with lookup j (P.jobs s)
... | nothing = case eq of λ ()
... | just job with lookup (Types.owner job) (U.frames (P.base s)) | Pool.step act (P.poolAt (Types.owner job) s)
...   | just f | just p = case just-injective eq of λ { refl → same-refl _ }
...   | just _ | nothing = case eq of λ ()
...   | nothing | _ = case eq of λ ()
via-infra-keys : ∀ w role act s {s′} → P.viaInfra w role act s ≡ just s′ → Same s s′
via-infra-keys w role act s eq with lookup w (U.frames (P.base s))
... | nothing = case eq of λ ()
... | just f with P.infraId role (P.Startup.phase (U.startup f))
...   | nothing = case eq of λ ()
...   | just j with Pool.step (act j) (P.poolAt w s)
...     | nothing = case eq of λ ()
...     | just p = case just-injective eq of λ { refl → same-refl _ }
muxer-keys : ∀ w act s {s′} → P.muxerEgress w act s ≡ just s′ → Same s s′
muxer-keys w act s eq with lookup w (U.frames (P.base s))
... | nothing = case eq of λ ()
... | just f with P.laneWorker f act s
...   | nothing = case eq of λ ()
...   | just (mid , j) with lookup j (Pool.handles (P.poolAt w s))
...     | just Pool.bodyRunning with O.advance (O.inbound (Machine.igStep (IG.egressStep mid act))) (P.source s) in advanced
...       | nothing = case eq of λ ()
...       | just next = case just-injective eq of λ { refl → nonkey (O.inbound (Machine.igStep (IG.egressStep mid act))) (P.source s) refl advanced }
muxer-keys w act s eq | just f | just (mid , j) | nothing = case eq of λ ()
muxer-keys w act s eq | just f | just (mid , j) | just Pool.bodyUnwinding = case eq of λ ()
muxer-keys w act s eq | just f | just (mid , j) | just (Pool.bodyReturned _) = case eq of λ ()
muxer-keys w act s eq | just f | just (mid , j) | just (Pool.deregisterPending _) = case eq of λ ()
muxer-keys w act s eq | just f | just (mid , j) | just (Pool.deregistered _) = case eq of λ ()
muxer-keys w act s eq | just f | just (mid , j) | just (Pool.resultAvailable _) = case eq of λ ()
control-keys : ∀ w act s {s′} → P.monitorControl w act s ≡ just s′ → Same s s′
control-keys w act s eq with lookup w (U.frames (P.base s))
... | nothing = case eq of λ ()
... | just f with U.progress f | P.monitoring f | P.noParent (P.poolAt w s)
...   | U.promisePublished hid mid | true | true with P.muxAt mid s
...     | nothing = case eq of λ ()
...     | just m with P.controlReady act m (P.poolAt w s)
...       | false = case eq of λ ()
...       | true with O.advance (O.inbound (Machine.igStep (P.sourceControl act mid))) (P.source s) in advanced
...         | nothing = case eq of λ ()
...         | just c = case just-injective eq of λ { refl → nonkey (O.inbound (Machine.igStep (P.sourceControl act mid))) (P.source s) refl advanced }
control-keys w act s eq | just f | (U.handshakePending helperPC) | _ | _ = case eq of λ ()
control-keys w act s eq | just f | U.returnedSuccess | _ | _ = case eq of λ ()
control-keys w act s eq | just f | U.handleAllocated _ _ | _ | _ = case eq of λ ()
control-keys w act s eq | just f | U.promisePublished _ _ | true | false = case eq of λ ()
control-keys w act s eq | just f | U.promisePublished _ _ | false | _ = case eq of λ ()

via-db-keys : ∀ a s {s′} → P.viaDb a s ≡ just s′ → Same s s′
via-db-keys a s eq with P.viaDb-source a s eq
... | c , advanced , refl = nonkey (O.inbound (Machine.igStep (IG.leiosDb a))) (P.source s) refl advanced
db-failure-keys : ∀ j s {s′} → P.dbFailure j s ≡ just s′ → Same s s′
db-failure-keys j s eq with P.dbFailure-via j s eq
... | P.refused err se = sync-keys j err s se
... | P.abandoned err mid via se = same-trans (via-db-keys (IG.abandonWait j) s via) (sync-keys j err mid se)

step-keysP : ∀ a s {s′} → P.step a s ≡ just s′ → Effect (rootP a) (P.source s) (P.source s′)
step-keysP (P.run a) s eq = inherit-keys a s eq
step-keysP (P.forkResponder w j gen) s eq = responder-keys w j gen s eq
step-keysP (P.forkInitiator w j gen n) s eq = initiator-keys w j gen n s eq
step-keysP (P.enterProtocolBody j) s eq = egress-keys j _ s eq
step-keysP (P.appendProtocolPayload j bytes) s eq = send-keys j bytes s (P.unlessAwaiting-just j s _ eq)
step-keysP (P.egressMuxer w act) s eq = muxer-keys w act s eq
step-keysP (P.registerProtocol j) s eq = register-keys j s eq
step-keysP (P.protocolReturned j) s eq = returned-keys j s (P.unlessAwaiting-just j s _ eq)
step-keysP (P.commitClean j) s eq = clean-keys j s eq
step-keysP (P.protocolException j err) s eq = sync-keys j err s eq
step-keysP (P.returnProtocol j) s eq = return-keys j s eq
step-keysP (P.publishProtocol j) s eq = publish-keys j s eq
step-keysP (P.deregisterProtocol j) s eq = via-protocol-keys j _ s eq
step-keysP (P.asyncProtocolResult j) s eq = via-protocol-keys j _ s eq
step-keysP (P.infrastructureReturn w role err) s eq = via-infra-keys w role _ s eq
step-keysP (P.publishInfra w role) s eq = via-infra-keys w role _ s eq
step-keysP (P.deregisterInfra w role) s eq = via-infra-keys w role _ s eq
step-keysP (P.asyncInfraResult w role) s eq = via-infra-keys w role _ s eq
step-keysP (P.control w act) s eq = control-keys w act s eq
step-keysP (P.submitDbWrite j d) s eq = via-db-keys _ s (P.submitDb-via j d s eq)
step-keysP (P.awaitDbWrite j) s eq = via-db-keys _ s (P.awaitDb-via j s eq)
step-keysP (P.dbWriteFailed j) s eq = db-failure-keys j s eq
step-keysP (P.writerComplete d) s eq = via-db-keys _ s eq
step-keysP (P.writerSeal err) s eq = via-db-keys _ s eq
