{-# OPTIONS --guardedness #-}

-- Actual source writes and per-physical-handler queued-pool histories. New
-- protocol forks extend the pool, so these are not old Startup.Executes claims.
module ConnectionManagement.Properties.MuxProtocolJobs where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (job; worker)
open import ConnectionManagement.IGTypes using (clean; errored; RunResult)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxProtocolJobs as W
module U = W.U
module S = W.Startup
module Pool = W.Pool
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import Data.Nat as Nat
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.MuxHandlerSupervision as HandlerProperties
module Base = HandlerProperties Types.TypedResult
import ConnectionManagement.Properties.MuxStartup as StartupProperties
module Startup = StartupProperties Types.TypedResult
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply

OTrace : O.Configuration → O.Configuration → Set
OTrace p q = Σ (List O.Action) (λ actions → O.Executes p actions q)
PTrace : Pool.State → Pool.State → Set
PTrace p q = Σ (List Pool.Action) (λ actions → Pool.Executes p actions q)
record Paths (before after : W.State) : Set where
  constructor paths
  field machine : OTrace (W.source before) (W.source after)
        pools : ∀ selected → PTrace (W.poolAt selected before) (W.poolAt selected after)
open Paths public
idle : ∀ s → Paths s s
idle s = paths ([] , O.done) (λ selected → [] , Pool.done)
right : ∀ {p q r} → q ≡ r → Paths p q → Paths p r
right refl path = path
trace-right : ∀ {p q r} → q ≡ r → PTrace p q → PTrace p r
trace-right refl path = path
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) first) (paths (bs , oq) second) = paths
  (as ++ bs , O.append op oq) (λ selected → let
    left = first selected; right = second selected in
    proj₁ left ++ proj₁ right , append-pool (proj₂ left) (proj₂ right))
  where
  append-pool : ∀ {p as q bs r} → Pool.Executes p as q → Pool.Executes q bs r → Pool.Executes p (as ++ bs) r
  append-pool Pool.done tail = tail
  append-pool (Pool.next eq path) tail = Pool.next eq (append-pool path tail)

metadata : ∀ s jobs pending → Paths s (record s { jobs = jobs; pending = pending })
metadata s jobs pending = paths ([] , O.done) (λ selected → [] , Pool.done)
source-step : ∀ action s {c} → O.advance action (W.source s) ≡ just c → Paths s (W.setSource c s)
source-step action s eq = paths (action ∷ [] , O.next eq O.done) (λ selected → [] , Pool.done)
pool-same : ∀ owner f pool s → W.poolAt owner (W.setPool owner f pool s) ≡ pool
pool-same owner f pool s = cong S.pool (Base.put-same owner
  (record f { startup = record (U.startup f) { pool = pool } }) (W.base s))
pool-other : ∀ owner selected f pool s → selected ≢ owner →
  W.poolAt selected (W.setPool owner f pool s) ≡ W.poolAt selected s
pool-other owner selected f pool s apart = cong S.pool (Base.put-other owner selected
  (record f { startup = record (U.startup f) { pool = pool } }) (W.base s) apart)
pool-step : ∀ owner f action s {pool} → Pool.step action (W.poolAt owner s) ≡ just pool →
  Paths s (W.setPool owner f pool s)
pool-step owner f action s {pool} advanced = paths ([] , O.done) selected
  where
  selected : ∀ worker → PTrace (W.poolAt worker s) (W.poolAt worker (W.setPool owner f pool s))
  selected worker with worker ≟ owner
  ... | yes refl = trace-right (sym (pool-same owner f pool s)) (action ∷ [] , Pool.next advanced Pool.done)
  ... | no apart = trace-right (sym (pool-other owner worker f pool s apart)) ([] , Pool.done)
pool-step-lookup : ∀ owner f action s {pool} → lookup owner (U.frames (W.base s)) ≡ just f →
  Pool.step action (S.pool (U.startup f)) ≡ just pool → Paths s (W.setPool owner f pool s)
pool-step-lookup owner f action s {pool} found advanced = pool-step owner f action s
  (subst (λ before → Pool.step action before ≡ just pool)
    (sym (cong S.pool (Base.startup-found owner (W.base s) f found))) advanced)
append-pending : ∀ job j s → Paths s (W.appendPending job j s)
append-pending job j s with Types.direction job
... | Mux.initiatorJob = idle s
... | Mux.responderJob = metadata s (W.jobs s) _

inherit-projects : ∀ action s {s′} → W.inherit action s ≡ just s′ → Paths s s′
inherit-projects action s eq with W.inheritedAllowed action
... | false = case eq of λ ()
... | true with U.step action (W.base s) in advanced
...   | nothing = case eq of λ ()
...   | just next with Base.step-projects action (W.base s) advanced
...     | Base.paths sourceTrace coordinator wait startups = case just-injective eq of λ { refl →
  paths sourceTrace (λ selected → Startup.exec-projects (proj₂ (startups selected))) }

source-trace : ∀ s {c} → OTrace (W.source s) c → Paths s (W.setSource c s)
source-trace s path = paths path (λ selected → [] , Pool.done)
fork-paths : ∀ owner f sourceAction j job s {c p} →
  O.advance sourceAction (W.source s) ≡ just c →
  Pool.step (Pool.fork j) (W.poolAt owner s) ≡ just p →
  Paths s (record (W.setPool owner f p (W.setSource c s)) { jobs = put j job (W.jobs s) })
fork-paths owner f sourceAction j job s {c} {p} sourceAdvanced poolAdvanced = compose
  (compose (source-step sourceAction s sourceAdvanced) (pool-step owner f (Pool.fork j) (W.setSource c s) poolAdvanced))
  (metadata (W.setPool owner f p (W.setSource c s)) (put j job (W.jobs s)) (W.pending s))
responder-projects : ∀ w j gen s {s′} → W.responderFork w j gen s ≡ just s′ → Paths s s′
responder-projects w j gen s eq with lookup w (U.frames (W.base s)) | W.fresh j gen s
... | just f | true with U.progress f | W.monitoring f
...   | U.promisePublished hid mid | true with W.muxAt mid s
...     | just m with Mux.callback m
...       | Mux.forkPending n with W.active w Mux.responderJob n (W.jobs s)
...         | false with O.advance (O.inbound (M.igStep (IG.forkResponder mid))) (W.source s) in sourceAdvanced |
  Pool.step (Pool.fork j) (W.poolAt w s) in poolAdvanced
...           | just c | just p = case just-injective eq of λ { refl →
  fork-paths w f (O.inbound (M.igStep (IG.forkResponder mid))) j
    (Types.protocolJob w mid Mux.responderJob n gen Types.executing) s sourceAdvanced poolAdvanced }
...           | nothing | _ = case eq of λ ()
...           | just _ | nothing = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.forkPending n | true = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.readActive tr = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.commitTrace enabled tr = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.afterStart n = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.afterFailure = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.tracerFailed n = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.returned = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | true | nothing = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.returnedSuccess | _ = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.handleAllocated hid mid | _ = case eq of λ ()
responder-projects w j gen s eq | just f | true | U.promisePublished hid mid | false = case eq of λ ()
responder-projects w j gen s eq | nothing | _ = case eq of λ ()
responder-projects w j gen s eq | just _ | false = case eq of λ ()

initiator-projects : ∀ w j gen n s {s′} → W.initiatorFork w j gen n s ≡ just s′ → Paths s s′
initiator-projects w j gen n s eq with lookup w (U.frames (W.base s)) | W.fresh j gen s
... | just f | true with U.progress f | W.monitoring f | Mux.findProtocol n (U.bundle f)
...   | U.promisePublished hid mid | true | just descriptor with W.muxAt mid s
...     | just m with Mux.status m | Mux.callback m | Mux.commands m | W.noResults (W.poolAt w s) | W.active w Mux.initiatorJob n (W.jobs s)
...       | Mux.ready | Mux.returned | [] | true | false with Pool.step (Pool.fork j) (W.poolAt w s) in advanced
...         | just p = case just-injective eq of λ { refl → compose (pool-step w f (Pool.fork j) s advanced)
  (metadata (W.setPool w f p s) (put j (Types.protocolJob w mid Mux.initiatorJob n gen Types.executing) (W.jobs s)) (W.pending s)) }
...         | nothing = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.stopping | _ | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.stopped | _ | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.failed err | _ | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.readActive tr | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.commitTrace enabled tr | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.afterStart k | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.forkPending k | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.afterFailure | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.tracerFailed k | _ | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | command ∷ rest | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | [] | false | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | [] | true | true = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | nothing = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.returnedSuccess | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.handleAllocated hid mid | _ | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | false | _ = case eq of λ ()
initiator-projects w j gen n s eq | just f | true | U.promisePublished hid mid | true | nothing = case eq of λ ()
initiator-projects w j gen n s eq | nothing | _ = case eq of λ ()
initiator-projects w j gen n s eq | just _ | false = case eq of λ ()

register-projects : ∀ j s {s′} → W.register j s ≡ just s′ → Paths s s′
register-projects j s eq with lookup j (W.jobs s)
... | nothing = case eq of λ ()
... | just job with lookup (Types.owner job) (U.frames (W.base s)) | Pool.parentFork (W.poolAt (Types.owner job) s)
...   | just f | just current with j ≟ current
...     | yes same with Pool.step Pool.register (W.poolAt (Types.owner job) s) in advanced
...       | just p = case just-injective eq of λ { refl → pool-step (Types.owner job) f Pool.register s advanced }
...       | nothing = case eq of λ ()
register-projects j s eq | just job | just f | just current | no apart = case eq of λ ()
register-projects j s eq | just job | nothing | _ = case eq of λ ()
register-projects j s eq | just job | just _ | nothing = case eq of λ ()
returned-projects : ∀ j s {s′} → W.returned j s ≡ just s′ → Paths s s′
returned-projects j s eq with lookup j (W.jobs s)
... | just job with Types.phase job
...   | Types.executing = case just-injective eq of λ { refl → metadata s _ _ }
...   | Types.waitingEgress = case eq of λ ()
...   | Types.resultCaptured _ = case eq of λ ()
returned-projects j s eq | nothing = case eq of λ ()

body-source-trace : ∀ job result s {c} → W.bodySource job result s ≡ just c → OTrace (W.source s) c
body-source-trace job result s eq with Types.direction job
... | Mux.initiatorJob = case just-injective eq of λ { refl → [] , O.done }
... | Mux.responderJob = O.inbound (M.igStep (IG.finishProtocol (Types.mux job) (Types.protocolNumber job) result)) ∷ [] , O.next eq O.done
capture-projects : ∀ j job result s {s′} → W.capture j job result s ≡ just s′ → Paths s s′
capture-projects j job result s eq with lookup (Types.owner job) (U.frames (W.base s)) |
  lookup j (Pool.handles (W.poolAt (Types.owner job) s))
... | just f | just Pool.bodyRunning with W.bodySource job result s in sourceAdvanced
...   | just c = case just-injective eq of λ { refl → compose
  (compose (source-trace s (body-source-trace job result s sourceAdvanced))
    (metadata (W.setSource c s) (put j (record job { phase = Types.resultCaptured result }) (W.jobs s)) (W.pending s)))
  (append-pending job j _) }
...   | nothing = case eq of λ ()
capture-projects j job result s eq | nothing | _ = case eq of λ ()
capture-projects j job result s eq | just _ | nothing = case eq of λ ()
capture-projects j job result s eq | just _ | just (Pool.bodyReturned _) = case eq of λ ()
capture-projects j job result s eq | just _ | just Pool.bodyUnwinding = case eq of λ ()
capture-projects j job result s eq | just _ | just (Pool.deregisterPending _) = case eq of λ ()
capture-projects j job result s eq | just _ | just (Pool.deregistered _) = case eq of λ ()
capture-projects j job result s eq | just _ | just (Pool.resultAvailable _) = case eq of λ ()
clean-projects : ∀ j s {s′} → W.cleanCommit j s ≡ just s′ → Paths s s′
clean-projects j s eq with lookup j (W.jobs s)
... | just job with Types.phase job
...   | Types.waitingEgress = capture-projects j job clean s eq
...   | Types.executing = case eq of λ ()
...   | Types.resultCaptured _ = case eq of λ ()
clean-projects j s eq | nothing = case eq of λ ()
error-projects : ∀ j err s {s′} → W.syncError j err s ≡ just s′ → Paths s s′
error-projects j err s eq with lookup j (W.jobs s)
... | just job with W.canCapture (Types.phase job)
...   | true = capture-projects j job (errored err) s eq
...   | false = case eq of λ ()
error-projects j err s eq | nothing = case eq of λ ()

publication-source-trace : ∀ j job result s {c kept} → W.publicationSource j job result s ≡ just (c , kept) → OTrace (W.source s) c
publication-source-trace j job result s eq with Types.direction job
... | Mux.initiatorJob = case just-injective eq of λ { refl → [] , O.done }
... | Mux.responderJob with W.locate j (W.pendingAt (Types.owner job) s) | W.muxAt (Types.mux job) s
...   | just (i , pendingRest) | just m with IG.takePending i (Mux.finishedJobs m)
...     | just ((n , outcome) , rest) with does (Types.protocolNumber job Nat.≟ n) ∧ W.sameOutcome result outcome
...       | true with O.advance (O.inbound (M.igStep (IG.publishJobOccurrence (Types.mux job) i))) (W.source s) in advanced
...         | just c = case just-injective eq of λ { refl → O.inbound (M.igStep (IG.publishJobOccurrence (Types.mux job) i)) ∷ [] , O.next advanced O.done }
...         | nothing = case eq of λ ()
publication-source-trace j job result s eq | Mux.responderJob | just (i , pendingRest) | just m | just ((n , outcome) , rest) | false = case eq of λ ()
publication-source-trace j job result s eq | Mux.responderJob | just (i , pendingRest) | just m | nothing = case eq of λ ()
publication-source-trace j job result s eq | Mux.responderJob | nothing | _ = case eq of λ ()
publication-source-trace j job result s eq | Mux.responderJob | just _ | nothing = case eq of λ ()
remove-published : ∀ job kept s → Paths s (W.removePublished job kept s)
remove-published job kept s with Types.direction job
... | Mux.initiatorJob = idle s
... | Mux.responderJob = metadata s (W.jobs s) (put (Types.owner job) kept (W.pending s))
publish-projects : ∀ j s {s′} → W.publish j s ≡ just s′ → Paths s s′
publish-projects j s eq with lookup j (W.jobs s)
... | nothing = case eq of λ ()
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (W.base s)) | lookup j (Pool.handles (W.poolAt (Types.owner job) s))
...   | Types.resultCaptured result | just f | just (Pool.bodyReturned value) with W.resultMatches job result value
...     | true with W.publicationSource j job result s in sourceAdvanced | Pool.step (Pool.publishCompletion j) (W.poolAt (Types.owner job) s) in poolAdvanced
...       | just (c , kept) | just p = case just-injective eq of λ { refl → compose
  (compose (source-trace s (publication-source-trace j job result s sourceAdvanced))
    (pool-step (Types.owner job) f (Pool.publishCompletion j) (W.setSource c s) poolAdvanced))
  (remove-published job kept (W.setPool (Types.owner job) f p (W.setSource c s))) }
...       | nothing | _ = case eq of λ ()
...       | just _ | nothing = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured result | just f | just (Pool.bodyReturned value) | false = case eq of λ ()
publish-projects j s eq | just job | Types.executing | _ | _ = case eq of λ ()
publish-projects j s eq | just job | Types.waitingEgress | _ | _ = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | nothing | _ = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | nothing = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyRunning = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyUnwinding = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregisterPending _) = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregistered _) = case eq of λ ()
publish-projects j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.resultAvailable _) = case eq of λ ()

via-protocol-projects : ∀ j action s {s′} → W.viaProtocol j action s ≡ just s′ → Paths s s′
via-protocol-projects j action s eq with lookup j (W.jobs s)
... | nothing = case eq of λ ()
... | just job with lookup (Types.owner job) (U.frames (W.base s)) in frameFound | Pool.step action (W.poolAt (Types.owner job) s) in advanced
...   | just f | just p = case just-injective eq of λ { refl → pool-step-lookup (Types.owner job) f action s frameFound advanced }
...   | nothing | _ = case eq of λ ()
...   | just _ | nothing = case eq of λ ()
via-infra-projects : ∀ w role action s {s′} → W.viaInfra w role action s ≡ just s′ → Paths s s′
via-infra-projects w role action s eq with lookup w (U.frames (W.base s))
... | nothing = case eq of λ ()
... | just f with W.infraId role (S.phase (U.startup f))
...   | nothing = case eq of λ ()
...   | just j with Pool.step (action j) (W.poolAt w s) in advanced
...     | nothing = case eq of λ ()
...     | just p = case just-injective eq of λ { refl → pool-step w f (action j) s advanced }
control-projects : ∀ w action s {s′} → W.monitorControl w action s ≡ just s′ → Paths s s′
control-projects w action s eq with lookup w (U.frames (W.base s))
... | nothing = case eq of λ ()
... | just f with U.progress f | W.monitoring f | W.noParent (W.poolAt w s)
...   | U.promisePublished hid mid | true | true with W.muxAt mid s
...     | nothing = case eq of λ ()
...     | just m with W.controlReady action m (W.poolAt w s)
...       | false = case eq of λ ()
...       | true with O.advance (O.inbound (M.igStep (W.sourceControl action mid))) (W.source s) in advanced
...         | nothing = case eq of λ ()
...         | just c = case just-injective eq of λ { refl → source-step (O.inbound (M.igStep (W.sourceControl action mid))) s advanced }
control-projects w action s eq | just f | U.returnedSuccess | _ | _ = case eq of λ ()
control-projects w action s eq | just f | U.handleAllocated hid mid | _ | _ = case eq of λ ()
control-projects w action s eq | just f | U.promisePublished hid mid | false | _ = case eq of λ ()
control-projects w action s eq | just f | U.promisePublished hid mid | true | false = case eq of λ ()

return-body-projects : ∀ j s {s′} → W.returnBody j s ≡ just s′ → Paths s s′
return-body-projects j s eq with lookup j (W.jobs s)
... | nothing = case eq of λ ()
... | just job with Types.phase job | lookup (Types.owner job) (U.frames (W.base s))
...   | Types.resultCaptured result | just f with Pool.step
  (Pool.bodyReturnedWith j (W.capturedResult job result)) (W.poolAt (Types.owner job) s) in advanced
...     | just p = case just-injective eq of λ { refl → pool-step (Types.owner job) f (Pool.bodyReturnedWith j (W.capturedResult job result)) s advanced }
...     | nothing = case eq of λ ()
return-body-projects j s eq | just job | Types.executing | _ = case eq of λ ()
return-body-projects j s eq | just job | Types.waitingEgress | _ = case eq of λ ()
return-body-projects j s eq | just job | Types.resultCaptured _ | nothing = case eq of λ ()
step-projects : ∀ action s {s′} → W.step action s ≡ just s′ → Paths s s′
step-projects (W.run a) s eq = inherit-projects a s eq
step-projects (W.forkResponder w j gen) s eq = responder-projects w j gen s eq
step-projects (W.forkInitiator w j gen n) s eq = initiator-projects w j gen n s eq
step-projects (W.registerProtocol j) s eq = register-projects j s eq
step-projects (W.protocolReturned j) s eq = returned-projects j s eq
step-projects (W.commitClean j) s eq = clean-projects j s eq
step-projects (W.protocolException j err) s eq = error-projects j err s eq
step-projects (W.returnProtocol j) s eq = return-body-projects j s eq
step-projects (W.publishProtocol j) s eq = publish-projects j s eq
step-projects (W.deregisterProtocol j) s eq = via-protocol-projects j (Pool.deregister j) s eq
step-projects (W.asyncProtocolResult j) s eq = via-protocol-projects j (Pool.publishAsyncResult j) s eq
step-projects (W.infrastructureReturn w role err) s eq = via-infra-projects w role (λ j → Pool.bodyReturnedWith j (Types.infraResult role err)) s eq
step-projects (W.publishInfra w role) s eq = via-infra-projects w role Pool.publishCompletion s eq
step-projects (W.deregisterInfra w role) s eq = via-infra-projects w role Pool.deregister s eq
step-projects (W.asyncInfraResult w role) s eq = via-infra-projects w role Pool.publishAsyncResult s eq
step-projects (W.control w action) s eq = control-projects w action s eq
append-pools : ∀ {p as q bs r} → Pool.Executes p as q → Pool.Executes q bs r → Pool.Executes p (as ++ bs) r
append-pools Pool.done tail = tail
append-pools (Pool.next eq path) tail = Pool.next eq (append-pools path tail)
exec-projects : ∀ {s actions s′} → W.Executes s actions s′ → Paths s s′
exec-projects {s = s} W.done = idle s
exec-projects (W.next {s = s} {a = action} eq path) = compose (step-projects action s eq) (exec-projects path)

-- Initializers retain exact source and empty selected physical pools.
initial-base : ∀ c {s} → W.initial c ≡ just s → U.initial c ≡ just (W.base s)
initial-base c eq with U.initial c in initialized
... | nothing = case eq of λ ()
... | just base = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c eq = Base.initial-source c (initial-base c eq)
initial-pool : ∀ c {s} → W.initial c ≡ just s → ∀ selected → W.poolAt selected s ≡ Pool.initial
initial-pool c eq selected = cong S.pool (Base.initial-startup c (initial-base c eq) selected)
trace-left : ∀ {p p′ q} → p ≡ p′ → PTrace p′ q → PTrace p q
trace-left refl path = path
pool-from-initial : ∀ {c start actions s} → W.initial c ≡ just start → W.Executes start actions s →
  ∀ selected → PTrace Pool.initial (W.poolAt selected s)
pool-from-initial {c} initialized path selected = trace-left (sym (initial-pool c initialized selected)) (pools (exec-projects path) selected)
captures-preserves : ∀ {s actions s′} → Capture.Captures (W.source s) → W.Executes s actions s′ → Capture.Captures (W.source s′)
captures-preserves valid path = Capture.exec-preserves valid (proj₂ (machine (exec-projects path)))
supply-preserves : ∀ {s actions s′} → Supply.Valid (W.source s) → W.Executes s actions s′ → Supply.Valid (W.source s′)
supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
from-initial-captures : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → W.Executes start actions s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = captures-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) path
from-initial-supply : ∀ {c start actions s} → W.initial (O.initial c) ≡ just start → SupplyBounds (M.world c) → W.Executes start actions s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounded path = supply-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounded)) path

handle-from-lookup : ∀ owner f j s value → lookup owner (U.frames (W.base s)) ≡ just f →
  lookup j (Pool.handles (S.pool (U.startup f))) ≡ just value →
  lookup j (Pool.handles (W.poolAt owner s)) ≡ just value
handle-from-lookup owner f j s value found advanced = trans
  (cong (λ p → lookup j (Pool.handles p)) (cong S.pool (Base.startup-found owner (W.base s) f found))) advanced
computation-from-lookup : ∀ owner f action s pool → lookup owner (U.frames (W.base s)) ≡ just f →
  Pool.step action (S.pool (U.startup f)) ≡ just pool → Pool.step action (W.poolAt owner s) ≡ just pool
computation-from-lookup owner f action s pool found advanced = subst (λ p → Pool.step action p ≡ just pool)
  (sym (cong S.pool (Base.startup-found owner (W.base s) f found))) advanced

-- A physical body return retains its exact captured descriptor/generation and
-- outcome. It is separate from the earlier local completion/status commit.
record BodyReturn (j : JobId) (before after : W.State) : Set where
  constructor bodyReturn
  field capturedJob : Types.ProtocolJob
        outcome : RunResult
        ownerFrame : U.Frame
        poolAfter : Pool.State
        job-before : lookup j (W.jobs before) ≡ just capturedJob
        local-result-before : Types.phase capturedJob ≡ Types.resultCaptured outcome
        frame-before : lookup (Types.owner capturedJob) (U.frames (W.base before)) ≡ just ownerFrame
        actual-return : Pool.step (Pool.bodyReturnedWith j (W.capturedResult capturedJob outcome))
          (W.poolAt (Types.owner capturedJob) before) ≡ just poolAfter
        after-shape : after ≡ W.setPool (Types.owner capturedJob) ownerFrame poolAfter before
        source-unchanged : W.source after ≡ W.source before
open BodyReturn public
return-observation : ∀ j s {s′} → W.step (W.returnProtocol j) s ≡ just s′ → BodyReturn j s s′
return-observation j s eq with lookup j (W.jobs s) in jobFound
... | nothing = case eq of λ ()
... | just job with Types.phase job in phaseFound | lookup (Types.owner job) (U.frames (W.base s)) in frameFound
...   | Types.resultCaptured result | just f with Pool.step
  (Pool.bodyReturnedWith j (W.capturedResult job result)) (W.poolAt (Types.owner job) s) in advanced
...     | just p = case just-injective eq of λ { refl → bodyReturn job result f p jobFound phaseFound frameFound advanced refl refl }
...     | nothing = case eq of λ ()
return-observation j s eq | just job | Types.executing | _ = case eq of λ ()
return-observation j s eq | just job | Types.waitingEgress | _ = case eq of λ ()
return-observation j s eq | just job | Types.resultCaptured _ | nothing = case eq of λ ()

-- A successful publication observes the exact physical body's return value and
-- commits the real queued-pool publication. Bool matches retain all four tags:
-- direction, protocol number, generation and outcome.
record Publication (j : JobId) (before after : W.State) : Set where
  constructor publication
  field capturedJob : Types.ProtocolJob
        outcome : RunResult
        ownerFrame : U.Frame
        bodyValue : Types.TypedResult
        sourceAfter : O.Configuration
        remainingPending : List JobId
        poolAfter : Pool.State
        job-before : lookup j (W.jobs before) ≡ just capturedJob
        local-result-before : Types.phase capturedJob ≡ Types.resultCaptured outcome
        frame-before : lookup (Types.owner capturedJob) (U.frames (W.base before)) ≡ just ownerFrame
        body-returned-before : lookup j (Pool.handles (W.poolAt (Types.owner capturedJob) before)) ≡ just (Pool.bodyReturned bodyValue)
        value-matches : W.resultMatches capturedJob outcome bodyValue ≡ true
        actual-source : W.publicationSource j capturedJob outcome before ≡ just (sourceAfter , remainingPending)
        actual-publication : Pool.step (Pool.publishCompletion j) (W.poolAt (Types.owner capturedJob) before) ≡ just poolAfter
        after-shape : after ≡ W.removePublished capturedJob remainingPending
          (W.setPool (Types.owner capturedJob) ownerFrame poolAfter (W.setSource sourceAfter before))
open Publication public
publication-observation : ∀ j s {s′} → W.step (W.publishProtocol j) s ≡ just s′ → Publication j s s′
publication-observation j s eq with lookup j (W.jobs s) in jobFound
... | nothing = case eq of λ ()
... | just job with Types.phase job in phaseFound |
  lookup (Types.owner job) (U.frames (W.base s)) in frameFound |
  lookup j (Pool.handles (W.poolAt (Types.owner job) s)) in bodyFound
...   | Types.resultCaptured result | just f | just (Pool.bodyReturned value) with W.resultMatches job result value in matched
...     | true with W.publicationSource j job result s in sourceAdvanced |
  Pool.step (Pool.publishCompletion j) (W.poolAt (Types.owner job) s) in poolAdvanced
...       | just (c , kept) | just p = case just-injective eq of λ { refl →
  publication job result f value c kept p jobFound phaseFound frameFound
    (handle-from-lookup (Types.owner job) f j s (Pool.bodyReturned value) frameFound bodyFound) matched sourceAdvanced
    poolAdvanced refl }
...       | nothing | _ = case eq of λ ()
...       | just _ | nothing = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured result | just f | just (Pool.bodyReturned value) | false = case eq of λ ()
publication-observation j s eq | just job | Types.executing | _ | _ = case eq of λ ()
publication-observation j s eq | just job | Types.waitingEgress | _ | _ = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | nothing | _ = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | nothing = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyRunning = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | just Pool.bodyUnwinding = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregisterPending _) = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.deregistered _) = case eq of λ ()
publication-observation j s eq | just job | Types.resultCaptured _ | just _ | just (Pool.resultAvailable _) = case eq of λ ()

-- Responders additionally select the current physical occurrence by its exact
-- ordinal. This witness does not identify two generations by protocol number.
record ResponderOccurrence (j : JobId) (job : Types.ProtocolJob) (result : RunResult)
  (before : W.State) (sourceAfter : O.Configuration) (kept : List JobId) : Set where
  constructor responderOccurrence
  field index : Nat.ℕ
        observedMux : Mux.Mux
        selectedNumber : Nat.ℕ
        selectedOutcome : RunResult
        remainingSource : List (Nat.ℕ × RunResult)
        located : W.locate j (W.pendingAt (Types.owner job) before) ≡ just (index , kept)
        mux-before : W.muxAt (Types.mux job) before ≡ just observedMux
        selected-source : IG.takePending index (Mux.finishedJobs observedMux) ≡ just ((selectedNumber , selectedOutcome) , remainingSource)
        descriptor-outcome-match : does (Types.protocolNumber job Nat.≟ selectedNumber) ∧ W.sameOutcome result selectedOutcome ≡ true
        actual-source-publication : O.advance (O.inbound (M.igStep (IG.publishJobOccurrence (Types.mux job) index)))
          (W.source before) ≡ just sourceAfter
open ResponderOccurrence public
responder-occurrence-observation : ∀ j job result s {c kept} → Types.direction job ≡ Mux.responderJob →
  W.publicationSource j job result s ≡ just (c , kept) → ResponderOccurrence j job result s c kept
responder-occurrence-observation j job result s direction eq with Types.direction job
... | Mux.initiatorJob = case direction of λ ()
... | Mux.responderJob with W.locate j (W.pendingAt (Types.owner job) s) in located | W.muxAt (Types.mux job) s in muxFound
...   | just (i , pendingRest) | just m with IG.takePending i (Mux.finishedJobs m) in selected
...     | just ((n , outcome) , rest) with does (Types.protocolNumber job Nat.≟ n) ∧ W.sameOutcome result outcome in matched
...       | true with O.advance (O.inbound (M.igStep (IG.publishJobOccurrence (Types.mux job) i))) (W.source s) in advanced
...         | just c = case just-injective eq of λ { refl → responderOccurrence i m n outcome rest located muxFound selected matched advanced }
...         | nothing = case eq of λ ()
responder-occurrence-observation j job result s direction eq | Mux.responderJob | just (i , pendingRest) | just m | just ((n , outcome) , rest) | false = case eq of λ ()
responder-occurrence-observation j job result s direction eq | Mux.responderJob | just (i , pendingRest) | just m | nothing = case eq of λ ()
responder-occurrence-observation j job result s direction eq | Mux.responderJob | nothing | _ = case eq of λ ()
responder-occurrence-observation j job result s direction eq | Mux.responderJob | just _ | nothing = case eq of λ ()

-- The normal Wanton-drain/status commit and exception-local result commit do
-- not yet return the physical job body. Preserve that actual source window.
data CompletionInput (job : Types.ProtocolJob) : RunResult → Set where
  normalInput : Types.phase job ≡ Types.waitingEgress → CompletionInput job clean
  exceptionInput : ∀ err → W.canCapture (Types.phase job) ≡ true → CompletionInput job (errored err)
record CompletionCommit (j : JobId) (before after : W.State) : Set where
  constructor completionCommit
  field capturedJob : Types.ProtocolJob
        outcome : RunResult
        ownerFrame : U.Frame
        sourceAfter : O.Configuration
        job-before : lookup j (W.jobs before) ≡ just capturedJob
        frame-before : lookup (Types.owner capturedJob) (U.frames (W.base before)) ≡ just ownerFrame
        input-boundary : CompletionInput capturedJob outcome
        physical-body-running : lookup j (Pool.handles (W.poolAt (Types.owner capturedJob) before)) ≡ just Pool.bodyRunning
        actual-source-commit : W.bodySource capturedJob outcome before ≡ just sourceAfter
        after-shape : after ≡ W.appendPending capturedJob j (record (W.setSource sourceAfter before)
          { jobs = put j (record capturedJob { phase = Types.resultCaptured outcome }) (W.jobs before) })
        pools-unchanged : ∀ selected → W.poolAt selected after ≡ W.poolAt selected before
open CompletionCommit public
append-pending-pool : ∀ job j s selected → W.poolAt selected (W.appendPending job j s) ≡ W.poolAt selected s
append-pending-pool job j s selected with Types.direction job
... | Mux.initiatorJob = refl
... | Mux.responderJob = refl
capture-observation : ∀ j job result s {s′} → lookup j (W.jobs s) ≡ just job → CompletionInput job result →
  W.capture j job result s ≡ just s′ → CompletionCommit j s s′
capture-observation j job result s jobFound input eq with
  lookup (Types.owner job) (U.frames (W.base s)) in frameFound |
  lookup j (Pool.handles (W.poolAt (Types.owner job) s)) in runningFound
... | just f | just Pool.bodyRunning with W.bodySource job result s in sourceAdvanced
...   | just c = case just-injective eq of λ { refl → completionCommit job result f c jobFound frameFound input
  (handle-from-lookup (Types.owner job) f j s Pool.bodyRunning frameFound runningFound) sourceAdvanced refl
  (λ selected → append-pending-pool job j
    (record (W.setSource c s) { jobs = put j (record job { phase = Types.resultCaptured result }) (W.jobs s) }) selected) }
...   | nothing = case eq of λ ()
capture-observation j job result s jobFound input eq | nothing | _ = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | nothing = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | just (Pool.bodyReturned _) = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | just Pool.bodyUnwinding = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | just (Pool.deregisterPending _) = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | just (Pool.deregistered _) = case eq of λ ()
capture-observation j job result s jobFound input eq | just _ | just (Pool.resultAvailable _) = case eq of λ ()
clean-observation : ∀ j s {s′} → W.step (W.commitClean j) s ≡ just s′ → CompletionCommit j s s′
clean-observation j s eq with lookup j (W.jobs s) in found
... | nothing = case eq of λ ()
... | just job with Types.phase job in phaseFound
...   | Types.waitingEgress = capture-observation j job clean s found (normalInput phaseFound) eq
...   | Types.executing = case eq of λ ()
...   | Types.resultCaptured _ = case eq of λ ()
exception-observation : ∀ j err s {s′} → W.step (W.protocolException j err) s ≡ just s′ → CompletionCommit j s s′
exception-observation j err s eq with lookup j (W.jobs s) in found
... | nothing = case eq of λ ()
... | just job with W.canCapture (Types.phase job) in canCapture
...   | true = capture-observation j job (errored err) s found (exceptionInput err canCapture) eq
...   | false = case eq of λ ()

open import ConnectionManagement.IGTypes using (Protocol)
-- Responder fork observes its actual source forkPending descriptor; initiator
-- fork is an explicit observed boundary, with no old PSA frontend write claim.
data ForkSource (f : U.Frame) (mid : MuxId) (n : Nat.ℕ) (before : W.State) (afterSource : O.Configuration) : Mux.JobDirection → Set where
  responderSource : ∀ m → W.muxAt mid before ≡ just m → Mux.callback m ≡ Mux.forkPending n →
    O.advance (O.inbound (M.igStep (IG.forkResponder mid))) (W.source before) ≡ just afterSource →
    ForkSource f mid n before afterSource Mux.responderJob
  initiatorSource : ∀ descriptor → Mux.findProtocol n (U.bundle f) ≡ just descriptor → afterSource ≡ W.source before →
    ForkSource f mid n before afterSource Mux.initiatorJob
record Fork (w : WorkerId) (j : JobId) (gen : RunId) (before after : W.State) : Set where
  constructor physicalFork
  field ownerFrame : U.Frame
        allocatedHandle : HandleId
        capturedMux : MuxId
        capturedNumber : Nat.ℕ
        capturedDirection : Mux.JobDirection
        sourceAfter : O.Configuration
        poolAfter : Pool.State
        frame-before : lookup w (U.frames (W.base before)) ≡ just ownerFrame
        allocated-before : U.progress ownerFrame ≡ U.promisePublished allocatedHandle capturedMux
        globally-fresh : W.fresh j gen before ≡ true
        source-boundary : ForkSource ownerFrame capturedMux capturedNumber before sourceAfter capturedDirection
        actual-fork : Pool.step (Pool.fork j) (W.poolAt w before) ≡ just poolAfter
        after-shape : after ≡ record (W.setPool w ownerFrame poolAfter (W.setSource sourceAfter before))
          { jobs = put j (Types.protocolJob w capturedMux capturedDirection capturedNumber gen Types.executing) (W.jobs before) }
open Fork public
responder-fork-observation : ∀ w j gen s {s′} → W.step (W.forkResponder w j gen) s ≡ just s′ → Fork w j gen s s′
responder-fork-observation w j gen s eq with lookup w (U.frames (W.base s)) in frameFound | W.fresh j gen s in freshFound
... | just f | true with U.progress f in progressFound | W.monitoring f
...   | U.promisePublished hid mid | true with W.muxAt mid s in muxFound
...     | just m with Mux.callback m in callbackFound
...       | Mux.forkPending n with W.active w Mux.responderJob n (W.jobs s)
...         | false with O.advance (O.inbound (M.igStep (IG.forkResponder mid))) (W.source s) in sourceAdvanced |
  Pool.step (Pool.fork j) (W.poolAt w s) in poolAdvanced
...           | just c | just p = case just-injective eq of λ { refl →
  physicalFork f hid mid n Mux.responderJob c p frameFound progressFound freshFound
    (responderSource m muxFound callbackFound sourceAdvanced) poolAdvanced refl }
...           | nothing | _ = case eq of λ ()
...           | just _ | nothing = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.forkPending n | true = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.readActive tr = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.commitTrace enabled tr = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.afterStart n = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.afterFailure = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.tracerFailed n = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | just m | Mux.returned = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | true | nothing = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.returnedSuccess | _ = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.handleAllocated hid mid | _ = case eq of λ ()
responder-fork-observation w j gen s eq | just f | true | U.promisePublished hid mid | false = case eq of λ ()
responder-fork-observation w j gen s eq | nothing | _ = case eq of λ ()
responder-fork-observation w j gen s eq | just _ | false = case eq of λ ()

initiator-fork-observation : ∀ w j gen n s {s′} → W.step (W.forkInitiator w j gen n) s ≡ just s′ → Fork w j gen s s′
initiator-fork-observation w j gen n s eq with lookup w (U.frames (W.base s)) in frameFound | W.fresh j gen s in freshFound
... | just f | true with U.progress f in progressFound | W.monitoring f | Mux.findProtocol n (U.bundle f) in descriptorFound
...   | U.promisePublished hid mid | true | just descriptor with W.muxAt mid s in muxFound
...     | just m with Mux.status m | Mux.callback m | Mux.commands m | W.noResults (W.poolAt w s) | W.active w Mux.initiatorJob n (W.jobs s)
...       | Mux.ready | Mux.returned | [] | true | false with Pool.step (Pool.fork j) (W.poolAt w s) in advanced
...         | just p = case just-injective eq of λ { refl → physicalFork f hid mid n Mux.initiatorJob (W.source s) p frameFound progressFound freshFound
    (initiatorSource descriptor descriptorFound refl) advanced refl }
...         | nothing = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.stopping | _ | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.stopped | _ | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.failed err | _ | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.readActive tr | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.commitTrace enabled tr | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.afterStart k | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.forkPending k | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.afterFailure | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.tracerFailed k | _ | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | command ∷ rest | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | [] | false | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | just m | Mux.ready | Mux.returned | [] | true | true = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | just descriptor | nothing = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.returnedSuccess | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.handleAllocated hid mid | _ | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | false | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just f | true | U.promisePublished hid mid | true | nothing = case eq of λ ()
initiator-fork-observation w j gen n s eq | nothing | _ = case eq of λ ()
initiator-fork-observation w j gen n s eq | just _ | false = case eq of λ ()
