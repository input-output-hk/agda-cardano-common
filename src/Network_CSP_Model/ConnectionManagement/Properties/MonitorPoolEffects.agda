{-# OPTIONS --guardedness #-}

-- Total handle-write classification of the queue-free physical monitor pool.
-- Primitive terminal transitions retain their cause; source exits are supplied
-- only by the actual enabled supervision action, never by a phase lookup.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MonitorPoolEffects
  (isBearerClosed isIOManagerError : ErrorId → Bool) where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId; ident)
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.PeerSupervision as Projection
import ConnectionManagement.Properties.ServerPeersMonitorReturns as Returns
import ConnectionManagement.Rules.AsyncScope as Scope
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as CM
private
 module PS = Supervision isIOManagerError
 module GP = PS.GP
 module GPool = GP.Pool
 module BPool = PS.Pool
 module P = Projection isIOManagerError
 module R = Returns isBearerClosed isIOManagerError
 module Gov = P.Gov
open P using (View; view; bg; gov; scopes; finish-view; note-view; detach-view; oneG; oneS)

-- All three terminal phases carry the same exit classification. A bodyReturned
-- cell is deliberately absent: the queue-free specialization never writes one.
data Terminal : BPool.ThreadPhase → BPool.Exit → Set where
 isPending : ∀ {ex} → Terminal (BPool.deregisterPending ex) ex
 isRemoved : ∀ {ex} → Terminal (BPool.deregistered ex) ex
 isAvailable : ∀ {ex} → Terminal (BPool.resultAvailable ex) ex
data Active : BPool.ThreadPhase → Set where
 running : Active BPool.bodyRunning
 unwinding : Active BPool.bodyUnwinding

-- Deregistration and Async publication are separate source/primitive moves.
data Move : Set where
 deregistering publishing : Move
fromPhase : Move → BPool.Exit → BPool.ThreadPhase
fromPhase deregistering ex = BPool.deregisterPending ex
fromPhase publishing ex = BPool.deregistered ex
toPhase : Move → BPool.Exit → BPool.ThreadPhase
toPhase deregistering ex = BPool.deregistered ex
toPhase publishing ex = BPool.resultAvailable ex
fromTerminal : ∀ move ex → Terminal (fromPhase move ex) ex
fromTerminal deregistering ex = isPending
fromTerminal publishing ex = isRemoved
toTerminal : ∀ move ex → Terminal (toPhase move ex) ex
toTerminal deregistering ex = isRemoved
toTerminal publishing ex = isAvailable
moveAction : Move → JobId → PS.Action
moveAction deregistering tid = PS.deregisterMonitor tid
moveAction publishing tid = PS.publishMonitorResult tid
poolMove : Move → JobId → BPool.Action
poolMove deregistering tid = BPool.deregister tid
poolMove publishing tid = BPool.publishAsyncResult tid

data Tag : Set where
 other : Tag
 exitTag : R.Kind → JobId → Tag
 moveTag : Move → JobId → Tag
resultKind : Maybe ErrorId → R.Kind
resultKind nothing = R.normal
resultKind (just err) = R.exceptional
poolTag : BPool.Action → Tag
poolTag (BPool.bodyReturnedWith tid result) = exitTag (resultKind result) tid
poolTag (BPool.bodyUnwound tid) = exitTag R.cancelled tid
poolTag (BPool.deregister tid) = moveTag deregistering tid
poolTag (BPool.publishAsyncResult tid) = moveTag publishing tid
poolTag _ = other
supervisionTag : PS.Action → Tag
supervisionTag (PS.finishMonitor tid) = exitTag R.normal tid
supervisionTag (PS.finishMonitorError tid) = exitTag R.exceptional tid
supervisionTag (PS.monitorBodyUnwound tid) = exitTag R.cancelled tid
supervisionTag (PS.deregisterMonitor tid) = moveTag deregistering tid
supervisionTag (PS.publishMonitorResult tid) = moveTag publishing tid
supervisionTag _ = other

-- A tagged write cannot invent an exit witness: its supply remains explicit
-- until the total source-action classifier discharges it below.
data Change (Witness : R.Kind → JobId → Set) (before after : BPool.State) : Set where
 same : BPool.handles after ≡ BPool.handles before → Change Witness before after
 active : ∀ tid phase → Active phase →
   BPool.handles after ≡ put tid phase (BPool.handles before) → Change Witness before after
 carry : ∀ tid ex old next → Terminal old ex → Terminal next ex →
   lookup tid (BPool.handles before) ≡ just old →
   BPool.handles after ≡ put tid next (BPool.handles before) → Change Witness before after
 ending : ∀ tid kind → Witness kind tid →
   BPool.handles after ≡ put tid (BPool.deregisterPending (R.exit kind)) (BPool.handles before) → Change Witness before after
Raw : Tag → BPool.State → BPool.State → Set
Raw tag = Change (λ kind tid → tag ≡ exitTag kind tid)
map-exit : ∀ {A B before after} → (∀ kind tid → A kind tid → B kind tid) →
 Change A before after → Change B before after
map-exit f (same eq) = same eq
map-exit f (active tid phase act eq) = active tid phase act eq
map-exit f (carry tid ex old next was now found eq) = carry tid ex old next was now found eq
map-exit f (ending tid kind evidence eq) = ending tid kind (f kind tid evidence) eq
right-pool : ∀ {A before after after′} → after ≡ after′ → Change A before after → Change A before after′
right-pool refl evidence = evidence

-- The detailed view adds movement witnesses without changing the earlier
-- Change/source-change/located-change interfaces used by terminal exit proofs.
module Detailed where
 data Effect (ExitWitness : R.Kind → JobId → Set) (MoveWitness : Move → JobId → Set)
   (before after : BPool.State) : Set where
  kept : BPool.handles after ≡ BPool.handles before → Effect ExitWitness MoveWitness before after
  written : ∀ tid phase → Active phase → BPool.handles after ≡ put tid phase (BPool.handles before) → Effect ExitWitness MoveWitness before after
  moved : ∀ tid move ex → MoveWitness move tid → lookup tid (BPool.handles before) ≡ just (fromPhase move ex) →
    BPool.handles after ≡ put tid (toPhase move ex) (BPool.handles before) → Effect ExitWitness MoveWitness before after
  returnedStep : ∀ tid kind → ExitWitness kind tid → BPool.handles after ≡ put tid (BPool.deregisterPending (R.exit kind)) (BPool.handles before) → Effect ExitWitness MoveWitness before after
 Labelled : Tag → BPool.State → BPool.State → Set
 Labelled tag = Effect (λ kind tid → tag ≡ exitTag kind tid) (λ move tid → tag ≡ moveTag move tid)
 map-evidence : ∀ {A B C D before after} → (∀ kind tid → A kind tid → C kind tid) →
   (∀ move tid → B move tid → D move tid) → Effect A B before after → Effect C D before after
 map-evidence f g (kept eq) = kept eq
 map-evidence f g (written tid phase act eq) = written tid phase act eq
 map-evidence f g (moved tid move ex evidence found eq) = moved tid move ex (g move tid evidence) found eq
 map-evidence f g (returnedStep tid kind evidence eq) = returnedStep tid kind (f kind tid evidence) eq
 retarget : ∀ {A B before after after′} → after ≡ after′ → Effect A B before after → Effect A B before after′
 retarget refl evidence = evidence

 d-join-handles : ∀ current c {d} → BPool.joinHead current c ≡ just d → Labelled other c d
 d-join-handles current c eq with BPool.remaining c | lookup current (BPool.handles c)
 ... | head ∷ rest | just (BPool.resultAvailable exit) with current ≟ head
 ...   | no _ = case eq of λ ()
 ...   | yes refl = case just-injective eq of λ { refl → kept refl }
 d-join-handles current c eq | [] | _ = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | nothing = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | just BPool.bodyRunning = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | just (BPool.bodyReturned _) = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | just BPool.bodyUnwinding = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | just (BPool.deregisterPending _) = case eq of λ ()
 d-join-handles current c eq | _ ∷ _ | just (BPool.deregistered _) = case eq of λ ()
 d-handle-effect : ∀ a c {d} → BPool.step a c ≡ just d → Labelled (poolTag a) c d
 d-handle-effect (BPool.fork k) c eq with BPool.phase c | BPool.parentFork c | lookup k (BPool.handles c) in absent
 ... | BPool.openPool | nothing | nothing with just-injective eq
 ...   | refl = written k BPool.bodyRunning running refl
 d-handle-effect (BPool.fork k) c eq | BPool.closing | _ | _ = case eq of λ ()
 d-handle-effect (BPool.fork k) c eq | BPool.closedPool | _ | _ = case eq of λ ()
 d-handle-effect (BPool.fork k) c eq | (BPool.cancelPending k₁) | _ | _ = case eq of λ ()
 d-handle-effect (BPool.fork k) c eq | (BPool.joinPending k₁) | _ | _ = case eq of λ ()
 d-handle-effect (BPool.fork k) c eq | BPool.openPool | just pending | _ = case eq of λ ()
 d-handle-effect (BPool.fork k) c eq | BPool.openPool | nothing | just old = case eq of λ ()
 d-handle-effect (BPool.forkConcurrent k) c eq with BPool.phase c | lookup k (BPool.handles c)
 ... | BPool.openPool | nothing = case just-injective eq of λ { refl → written k BPool.bodyRunning running refl }
 ... | BPool.openPool | just _ = case eq of λ ()
 ... | BPool.closing | _ = case eq of λ ()
 ... | BPool.closedPool | _ = case eq of λ ()
 ... | BPool.cancelPending _ | _ = case eq of λ ()
 ... | BPool.joinPending _ | _ = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq with BPool.phase c | lookup k (BPool.handles c) | BPool.member k (BPool.registered c)
 ... | BPool.openPool | just ex | false with BPool.awaitingRegistration ex
 ...   | true = case just-injective eq of λ { refl → kept refl }
 ...   | false = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.openPool | nothing | _ = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.openPool | just _ | true = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.closing | _ | _ = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.closedPool | _ | _ = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.cancelPending _ | _ | _ = case eq of λ ()
 d-handle-effect (BPool.registerConcurrent k) c eq | BPool.joinPending _ | _ | _ = case eq of λ ()
 d-handle-effect BPool.register c eq with BPool.phase c | BPool.parentFork c
 ... | BPool.openPool | just k with BPool.member k (BPool.registered c)
 ...   | false = case just-injective eq of λ { refl → kept refl }
 ...   | true = case eq of λ ()
 d-handle-effect BPool.register c eq | BPool.closing | _ = case eq of λ ()
 d-handle-effect BPool.register c eq | BPool.closedPool | _ = case eq of λ ()
 d-handle-effect BPool.register c eq | (BPool.cancelPending k₁) | _ = case eq of λ ()
 d-handle-effect BPool.register c eq | (BPool.joinPending k₁) | _ = case eq of λ ()
 d-handle-effect BPool.register c eq | BPool.openPool | nothing = case eq of λ ()
 d-handle-effect (BPool.bodyReturnedWith k nothing) c eq with lookup k (BPool.handles c)
 ... | just BPool.bodyRunning = case just-injective eq of λ { refl → returnedStep k R.normal refl refl }
 ... | nothing = case eq of λ ()
 ... | just (BPool.bodyReturned _) = case eq of λ ()
 ... | just BPool.bodyUnwinding = case eq of λ ()
 ... | just (BPool.deregisterPending _) = case eq of λ ()
 ... | just (BPool.deregistered _) = case eq of λ ()
 ... | just (BPool.resultAvailable _) = case eq of λ ()
 d-handle-effect (BPool.bodyReturnedWith k (just err)) c eq with lookup k (BPool.handles c)
 ... | just BPool.bodyRunning = case just-injective eq of λ { refl → returnedStep k R.exceptional refl refl }
 ... | nothing = case eq of λ ()
 ... | just (BPool.bodyReturned _) = case eq of λ ()
 ... | just BPool.bodyUnwinding = case eq of λ ()
 ... | just (BPool.deregisterPending _) = case eq of λ ()
 ... | just (BPool.deregistered _) = case eq of λ ()
 ... | just (BPool.resultAvailable _) = case eq of λ ()
 d-handle-effect (BPool.publishCompletion k) c eq = case eq of λ ()
 d-handle-effect BPool.consumeCompletion c eq = case eq of λ ()
 d-handle-effect (BPool.interruptJob k) c eq with BPool.phase c | lookup k (BPool.handles c) in found
 ... | BPool.openPool | just BPool.bodyRunning = case just-injective eq of λ { refl → written k BPool.bodyUnwinding unwinding refl }
 ... | BPool.closing | _ = case eq of λ ()
 ... | BPool.closedPool | _ = case eq of λ ()
 ... | BPool.cancelPending j | _ = case eq of λ ()
 ... | BPool.joinPending j | _ = case eq of λ ()
 ... | BPool.openPool | nothing = case eq of λ ()
 ... | BPool.openPool | just (BPool.bodyReturned value) = case eq of λ ()
 ... | BPool.openPool | just BPool.bodyUnwinding = case eq of λ ()
 ... | BPool.openPool | just (BPool.deregisterPending ex) = case eq of λ ()
 ... | BPool.openPool | just (BPool.deregistered ex) = case eq of λ ()
 ... | BPool.openPool | just (BPool.resultAvailable ex) = case eq of λ ()
 d-handle-effect (BPool.bodyUnwound k) c eq with lookup k (BPool.handles c) in found
 ... | just BPool.bodyUnwinding = case just-injective eq of λ { refl → returnedStep k R.cancelled refl refl }
 ... | nothing = case eq of λ ()
 ... | just BPool.bodyRunning = case eq of λ ()
 ... | just (BPool.bodyReturned value) = case eq of λ ()
 ... | just (BPool.deregisterPending ex) = case eq of λ ()
 ... | just (BPool.deregistered ex) = case eq of λ ()
 ... | just (BPool.resultAvailable ex) = case eq of λ ()
 d-handle-effect (BPool.resumeAfterUnwindError k) c eq with lookup k (BPool.handles c) in found
 ... | just BPool.bodyUnwinding = case just-injective eq of λ { refl → written k BPool.bodyRunning running refl }
 ... | nothing = case eq of λ ()
 ... | just BPool.bodyRunning = case eq of λ ()
 ... | just (BPool.bodyReturned value) = case eq of λ ()
 ... | just (BPool.deregisterPending ex) = case eq of λ ()
 ... | just (BPool.deregistered ex) = case eq of λ ()
 ... | just (BPool.resultAvailable ex) = case eq of λ ()
 d-handle-effect (BPool.deregister k) c eq with lookup k (BPool.handles c) in found | BPool.member k (BPool.registered c)
 ... | just (BPool.deregisterPending exit) | true = case just-injective eq of λ { refl → moved k deregistering exit refl found refl }
 ... | nothing | _ = case eq of λ ()
 ... | just (BPool.deregisterPending exit) | false = case eq of λ ()
 ... | just BPool.bodyRunning | _ = case eq of λ ()
 ... | just (BPool.bodyReturned value) | _ = case eq of λ ()
 ... | just BPool.bodyUnwinding | _ = case eq of λ ()
 ... | just (BPool.deregistered ex) | _ = case eq of λ ()
 ... | just (BPool.resultAvailable ex) | _ = case eq of λ ()
 d-handle-effect (BPool.publishAsyncResult k) c eq with lookup k (BPool.handles c) in found
 ... | just (BPool.deregistered exit) = case just-injective eq of λ { refl → moved k publishing exit refl found refl }
 ... | nothing = case eq of λ ()
 ... | just BPool.bodyRunning = case eq of λ ()
 ... | just (BPool.bodyReturned value) = case eq of λ ()
 ... | just BPool.bodyUnwinding = case eq of λ ()
 ... | just (BPool.deregisterPending ex) = case eq of λ ()
 ... | just (BPool.resultAvailable ex) = case eq of λ ()
 d-handle-effect (BPool.beginClose order) c eq with BPool.phase c | BPool.parentFork c | BPool.canSnapshot false order c
 ... | BPool.openPool | nothing | true = case just-injective eq of λ { refl → kept refl }
 ... | BPool.closing | _ | _ = case eq of λ ()
 ... | BPool.closedPool | _ | _ = case eq of λ ()
 ... | (BPool.cancelPending k₁) | _ | _ = case eq of λ ()
 ... | (BPool.joinPending k₁) | _ | _ = case eq of λ ()
 ... | BPool.openPool | just pending | _ = case eq of λ ()
 ... | BPool.openPool | nothing | false = case eq of λ ()
 d-handle-effect BPool.requestCancel c eq with BPool.phase c | BPool.remaining c in restEq
 ... | BPool.closing | k ∷ rest with lookup k (BPool.handles c)
 ...   | nothing = case eq of λ ()
 ...   | just (BPool.resultAvailable exit) = case just-injective eq of λ { refl → kept refl }
 ...   | just BPool.bodyRunning = case just-injective eq of λ { refl → kept refl }
 ...   | just (BPool.bodyReturned result) = case just-injective eq of λ { refl → kept refl }
 ...   | just BPool.bodyUnwinding = case just-injective eq of λ { refl → kept refl }
 ...   | just (BPool.deregisterPending exit) = case just-injective eq of λ { refl → kept refl }
 ...   | just (BPool.deregistered exit) = case just-injective eq of λ { refl → kept refl }
 d-handle-effect BPool.requestCancel c eq | BPool.openPool | _ = case eq of λ ()
 d-handle-effect BPool.requestCancel c eq | BPool.closedPool | _ = case eq of λ ()
 d-handle-effect BPool.requestCancel c eq | (BPool.cancelPending k₁) | _ = case eq of λ ()
 d-handle-effect BPool.requestCancel c eq | (BPool.joinPending k₁) | _ = case eq of λ ()
 d-handle-effect BPool.requestCancel c eq | BPool.closing | [] = case eq of λ ()
 d-handle-effect BPool.deliverCancel c eq with BPool.phase c
 ... | BPool.cancelPending k with lookup k (BPool.handles c) in found
 ...   | just BPool.bodyRunning = case just-injective eq of λ { refl → written k BPool.bodyUnwinding unwinding refl }
 ...   | nothing = case eq of λ ()
 ...   | just (BPool.bodyReturned value) = case eq of λ ()
 ...   | just BPool.bodyUnwinding = case eq of λ ()
 ...   | just (BPool.deregisterPending ex) = case eq of λ ()
 ...   | just (BPool.deregistered ex) = case eq of λ ()
 ...   | just (BPool.resultAvailable ex) = case eq of λ ()
 d-handle-effect BPool.deliverCancel c eq | BPool.openPool = case eq of λ ()
 d-handle-effect BPool.deliverCancel c eq | BPool.closing = case eq of λ ()
 d-handle-effect BPool.deliverCancel c eq | BPool.closedPool = case eq of λ ()
 d-handle-effect BPool.deliverCancel c eq | (BPool.joinPending k₁) = case eq of λ ()
 d-handle-effect BPool.join c eq with BPool.phase c
 ... | BPool.cancelPending k = d-join-handles k c eq
 ... | BPool.joinPending k = d-join-handles k c eq
 ... | BPool.openPool = case eq of λ ()
 ... | BPool.closing = case eq of λ ()
 ... | BPool.closedPool = case eq of λ ()
 d-handle-effect BPool.finishClose c eq with BPool.phase c | BPool.remaining c in restEq
 ... | BPool.closing | [] = case just-injective eq of λ { refl → kept refl }
 ... | BPool.openPool | _ = case eq of λ ()
 ... | BPool.closedPool | _ = case eq of λ ()
 ... | (BPool.cancelPending k₁) | _ = case eq of λ ()
 ... | (BPool.joinPending k₁) | _ = case eq of λ ()
 ... | BPool.closing | _ ∷ _ = case eq of λ ()


 -- The established metadata projections discharge source/CM bookkeeping. Their
 -- governor and outer-scope paths leave the physical handle table unchanged.
 d-idle : ∀ v → Labelled other (bg v) (bg v)
 d-idle v = kept refl
 d-right-view : ∀ {tag before w w′} → w ≡ w′ → Labelled tag before (bg w) → Labelled tag before (bg w′)
 d-right-view refl evidence = evidence
 d-onlyG : ∀ v {p′} → P.GTrace (P.gov v) p′ → Labelled other (bg v) (bg (record v { gov = p′ }))
 d-onlyG v trace = kept refl
 d-onlyS : ∀ v {p′} → P.STrace (P.scopes v) p′ → Labelled other (bg v) (bg (record v { scopes = p′ }))
 d-onlyS v trace = kept refl
 d-onlyB : ∀ {tag} v {p′} → Labelled tag (bg v) p′ → Labelled tag (bg v) (bg (record v { bg = p′ }))
 d-onlyB v trace = trace
 d-oneB : ∀ a p {p′} → BPool.step a p ≡ just p′ → Labelled (poolTag a) p p′
 d-oneB = d-handle-effect

 d-fork-projects : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Labelled other (bg (view s)) (bg (view s′))
 d-fork-projects j (ident wid) s eq with lookup j (Sub.jobs (PS.machine s)) | PS.byParent j (PS.monitors s) | PS.freshWorker (ident wid) s
 ... | just jf | nothing | true with G.kind (J.work (Sub.execution jf)) |
   J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s)) |
   PS.byPeer (J.connectionRef (Sub.execution jf)) (PS.monitors s)
 ...   | G.establish | J.forkMonitor | true | nothing with
   Sub.advance (Sub.jobStep j J.launchMonitor) (PS.machine s) |
   BPool.step (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) in forked
 ...     | just c′ | just p′ = case just-injective eq of λ { refl →
   d-onlyB (view s) (d-oneB (BPool.forkConcurrent (ident wid)) (PS.monitorPool s) forked) }
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | nothing | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | nothing | just c′ | nothing = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.forget | _ | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.activate | _ | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.close | _ | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.deactivate | _ | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.begin | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAcquire | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.startBundle temp ns) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.publishBundle temp) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.markWarm | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.finishActivation | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitHot | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitAll | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.callRelease | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.awaitRelease | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.delayFailure | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.awaitCold result) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.complete result) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.acquirePolicy fault) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeDelivery fault) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | (J.nodeRethrow fault) | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | false | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | true | G.establish | J.forkMonitor | true | just found = case eq of λ ()
 d-fork-projects j (ident wid) s eq | nothing | _ | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | just found | _ = case eq of λ ()
 d-fork-projects j (ident wid) s eq | just jf | nothing | false = case eq of λ ()

 d-monitor-delivery-projects : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Labelled other (bg (view s)) (bg (view s′))
 d-monitor-delivery-projects blocked err s eq with BPool.phase (PS.monitorPool s)
 ... | BPool.cancelPending tid with lookup tid (PS.monitors s)
 ...   | nothing = case eq of λ ()
 ...   | just t with PS.monitorDeliverable blocked (PS.pc t) | BPool.step BPool.deliverCancel (PS.monitorPool s) in delivered
 ...     | true | just p′ with PS.detach err t s in detached
 ...       | just (f , s′) = case just-injective eq of λ { refl →
   d-right-view (sym (cong (λ v → record v { bg = p′ }) (detach-view err t s detached)))
     (d-onlyB (view s) (d-oneB BPool.deliverCancel (PS.monitorPool s) delivered)) }
 ...       | nothing = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.cancelPending tid | just t | false | _ = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.cancelPending tid | just t | true | nothing = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.openPool = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.closing = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.closedPool = case eq of λ ()
 d-monitor-delivery-projects blocked err s eq | BPool.joinPending tid = case eq of λ ()

 -- Every accepted action has real component paths; direct establishment return
 -- contributes a governor body-return step rather than inventing a GP dispatch.
 d-step-projects : ∀ action s {s′} → PS.step action s ≡ just s′ → Labelled (supervisionTag action) (bg (view s)) (bg (view s′))
 d-step-projects (PS.run a) s eq with PS.governorAllowed a s
 ... | false = case eq of λ ()
 ... | true with GP.step a (PS.governor s) in stepped
 ...   | nothing = case eq of λ ()
 ...   | just g′ = case just-injective eq of λ { refl →
   d-right-view (sym (note-view a s (record s { governor = g′ })))
     (d-onlyG (view s) (Gov.step-projects a (PS.governor s) stepped)) }
 d-step-projects (PS.forkMonitor j w) s eq = d-fork-projects j w s eq
 d-step-projects (PS.registerMonitor tid) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.parentPC t | BPool.step (BPool.registerConcurrent tid) (PS.monitorPool s) in registered
 ...   | PS.created | just p′ = case just-injective eq of λ { refl →
   d-onlyB (view s) (d-oneB (BPool.registerConcurrent tid) (PS.monitorPool s) registered) }
 d-step-projects (PS.registerMonitor tid) s eq | just t | PS.created | nothing = case eq of λ ()
 d-step-projects (PS.registerMonitor tid) s eq | just t | PS.registered | _ = case eq of λ ()
 d-step-projects (PS.registerMonitor tid) s eq | just t | PS.returned | _ = case eq of λ ()
 d-step-projects (PS.registerMonitor tid) s eq | nothing = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
 ... | just (tid , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf) | GP.running j (GP.pool (PS.governor s))
 ...   | PS.registered | J.forkMonitor | true = case just-injective eq of λ { refl → d-idle (view s) }
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.returned | _ | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.begin | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAcquire | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.startBundle temp ns) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.publishBundle temp) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.markWarm | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.finishActivation | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitHot | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitAll | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.callRelease | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.awaitRelease | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.delayFailure | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.awaitCold result) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.complete result) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.acquirePolicy fault) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeDelivery fault) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | (J.nodeRethrow fault) | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just (tid , t) | just jf | PS.registered | J.forkMonitor | false = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | nothing | _ = case eq of λ ()
 d-step-projects (PS.returnEstablishment j) s eq | just found | nothing = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq with PS.byParent j (PS.monitors s) | lookup j (Sub.jobs (PS.machine s))
 ... | just (_ , t) | just jf with PS.parentPC t | J.pc (Sub.execution jf)
 ...   | PS.returned | J.complete result with GPool.step
     (GPool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) in returned
 ...     | just p′ = case just-injective eq of λ { refl →
   d-onlyG (view s) (oneG (GPool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (GP.pool (PS.governor s)) returned) }
 ...     | nothing = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.created | _ = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.registered | _ = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.begin = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAcquire = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.startBundle temp ns) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.publishBundle temp) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.markWarm = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.forkMonitor = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.finishActivation = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitHot = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitAll = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.callRelease = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.awaitRelease = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | J.delayFailure = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.awaitCold result) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.acquirePolicy fault) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeDelivery fault) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just (tid , t) | just jf | PS.returned | (J.nodeRethrow fault) = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | nothing | _ = case eq of λ ()
 d-step-projects (PS.finishEstablishment j) s eq | just found | nothing = case eq of λ ()
 d-step-projects (PS.monitorException tid err) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.bodyActive tid t s | PS.detach err t s in detached
 ...   | true | just (f , s′) = case just-injective eq of λ { refl → d-right-view (sym (detach-view err t s detached)) (d-idle (view s)) }
 d-step-projects (PS.monitorException tid err) s eq | just t | false | _ = case eq of λ ()
 d-step-projects (PS.monitorException tid err) s eq | just t | true | nothing = case eq of λ ()
 d-step-projects (PS.monitorException tid err) s eq | nothing = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.pc t | lookup (PS.peerRef t) (J.peers (Sub.world (PS.machine s)))
 ...   | PS.errorWait err | just peer with Peer.demoted (Peer.key peer) (PS.shared s)
 ...     | true = case just-injective eq of λ { refl → d-idle (view s) }
 ...     | false = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | PS.errorWait err | nothing = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | PS.observing | _ = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | PS.exited | _ = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
 d-step-projects (PS.commitMonitorError tid) s eq | nothing = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.pc t | BPool.step (BPool.bodyReturnedWith tid nothing) (PS.monitorPool s) in returned
 ...   | PS.normalFinishing | just p′ = case just-injective eq of λ { refl →
   d-right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view true (PS.peerRef t) s)))
     (d-onlyB (view s) (d-oneB (BPool.bodyReturnedWith tid nothing) (PS.monitorPool s) returned)) }
 d-step-projects (PS.finishMonitor tid) s eq | just t | PS.normalFinishing | nothing = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | just t | PS.observing | _ = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | just t | PS.cancelling | _ = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | just t | PS.exited | _ = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
 d-step-projects (PS.finishMonitor tid) s eq | nothing = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.pc t
 ...   | PS.errorFinishing err with BPool.step (BPool.bodyReturnedWith tid (just err)) (PS.monitorPool s) in returned
 ...     | just p′ = case just-injective eq of λ { refl →
   d-right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view true (PS.peerRef t) s)))
     (d-onlyB (view s) (d-oneB (BPool.bodyReturnedWith tid (just err)) (PS.monitorPool s) returned)) }
 ...     | nothing = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | just t | PS.observing = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | just t | PS.normalFinishing = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | just t | PS.cancelling = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | just t | PS.exited = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | just t | (PS.errorWait err) = case eq of λ ()
 d-step-projects (PS.finishMonitorError tid) s eq | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq with Scope.cursor (PS.scopes s) | GPool.parentFork (GP.pool (PS.governor s))
 ... | Scope.closing Scope.governor | just pending = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.openScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.churn | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.localRoot | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.ledger | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.closing Scope.governor | nothing with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.readyToFinish | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.deliverCancel) s eq | Scope.finishedScope | _ with Scope.step (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.deliverCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.beginUnwind) s eq with Scope.step (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.beginUnwind (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.requestCancel) s eq with Scope.step (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.requestCancel (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.join) s eq with Scope.step (PS.governorPoolClosed s) Scope.join (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.join (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope Scope.finishClose) s eq with Scope.step (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) Scope.finishClose (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope (Scope.beginFailure actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.beginFailure actor) (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope (Scope.bodyExit actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.bodyExit actor) (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.scope (Scope.publishResult actor)) s eq with Scope.step (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) in advanced
 ... | just next = case just-injective eq of λ { refl → d-onlyS (view s) (oneS (PS.governorPoolClosed s) (Scope.publishResult actor) (PS.scopes s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.beginMonitorClose order) s eq with Scope.closed (PS.scopes s)
 ... | false = case eq of λ ()
 ... | true with BPool.step (BPool.beginClose order) (PS.monitorPool s) in advanced
 ...   | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB (BPool.beginClose order) (PS.monitorPool s) advanced) }
 ...   | nothing = case eq of λ ()
 d-step-projects PS.requestMonitorCancel s eq with BPool.step BPool.requestCancel (PS.monitorPool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB BPool.requestCancel (PS.monitorPool s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects PS.joinMonitor s eq with BPool.step BPool.join (PS.monitorPool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB BPool.join (PS.monitorPool s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects PS.finishMonitorClose s eq with BPool.step BPool.finishClose (PS.monitorPool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB BPool.finishClose (PS.monitorPool s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.deregisterMonitor tid) s eq with BPool.step (BPool.deregister tid) (PS.monitorPool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB (BPool.deregister tid) (PS.monitorPool s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.publishMonitorResult tid) s eq with BPool.step (BPool.publishAsyncResult tid) (PS.monitorPool s) in advanced
 ... | just p′ = case just-injective eq of λ { refl → d-onlyB (view s) (d-oneB (BPool.publishAsyncResult tid) (PS.monitorPool s) advanced) }
 ... | nothing = case eq of λ ()
 d-step-projects (PS.deliverMonitorCancellation err) s eq = d-monitor-delivery-projects false err s eq
 d-step-projects (PS.deliverBlockedMonitorCancellation err) s eq = d-monitor-delivery-projects true err s eq
 d-step-projects (PS.monitorBodyUnwound tid) s eq with lookup tid (PS.monitors s)
 ... | just t with PS.pc t | PS.interrupted t
 ...   | PS.cancelling | just f with Cancel.pc f
 ...     | Cancel.finished Cancel.abandoned with BPool.step (BPool.bodyUnwound tid) (PS.monitorPool s) in advanced
 ...       | just p′ = case just-injective eq of λ { refl →
   d-right-view (sym (cong (λ v → record v { bg = p′ }) (finish-view false (PS.peerRef t) s)))
     (d-onlyB (view s) (d-oneB (BPool.bodyUnwound tid) (PS.monitorPool s) advanced)) }
 ...       | nothing = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.cleaning capturedCaller = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished Cancel.cleanupComplete = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | just f | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.cancelling | nothing = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.observing | _ = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.normalFinishing | _ = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | PS.exited | _ = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorWait err) | _ = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | just t | (PS.errorFinishing err) | _ = case eq of λ ()
 d-step-projects (PS.monitorBodyUnwound tid) s eq | nothing = case eq of λ ()


-- Forget movement labels to retain the complete increment-45 API.
forget : ∀ {tag before after} → Detailed.Labelled tag before after → Raw tag before after
forget (Detailed.kept eq) = same eq
forget (Detailed.written tid phase act eq) = active tid phase act eq
forget (Detailed.moved tid move ex witness found eq) = carry tid ex (fromPhase move ex) (toPhase move ex)
 (fromTerminal move ex) (toTerminal move ex) found eq
forget (Detailed.returnedStep tid kind witness eq) = ending tid kind witness eq
join-handles : ∀ current c {d} → BPool.joinHead current c ≡ just d → Raw other c d
join-handles current c eq = forget (Detailed.d-join-handles current c eq)
handle-effect : ∀ a c {d} → BPool.step a c ≡ just d → Raw (poolTag a) c d
handle-effect a c eq = forget (Detailed.d-handle-effect a c eq)
idle : ∀ v → Raw other (bg v) (bg v)
idle v = same refl
right-view : ∀ {tag before w w′} → w ≡ w′ → Raw tag before (bg w) → Raw tag before (bg w′)
right-view refl evidence = evidence
onlyG : ∀ v {p′} → P.GTrace (P.gov v) p′ → Raw other (bg v) (bg (record v { gov = p′ }))
onlyG v trace = same refl
onlyS : ∀ v {p′} → P.STrace (P.scopes v) p′ → Raw other (bg v) (bg (record v { scopes = p′ }))
onlyS v trace = same refl
onlyB : ∀ {tag} v {p′} → Raw tag (bg v) p′ → Raw tag (bg v) (bg (record v { bg = p′ }))
onlyB v trace = trace
oneB : ∀ a p {p′} → BPool.step a p ≡ just p′ → Raw (poolTag a) p p′
oneB = handle-effect
fork-projects : ∀ j w s {s′} → PS.fork j w s ≡ just s′ → Raw other (bg (view s)) (bg (view s′))
fork-projects j w s eq = forget (Detailed.d-fork-projects j w s eq)
monitor-delivery-projects : ∀ blocked err s {s′} → PS.deliverMonitor blocked err s ≡ just s′ → Raw other (bg (view s)) (bg (view s′))
monitor-delivery-projects blocked err s eq = forget (Detailed.d-monitor-delivery-projects blocked err s eq)
step-projects : ∀ action s {s′} → PS.step action s ≡ just s′ → Raw (supervisionTag action) (bg (view s)) (bg (view s′))
step-projects a s eq = forget (Detailed.d-step-projects a s eq)

-- Only these three source actions can supply a fresh physical exit. The
-- reflection is over action constructors, independent of any table coherence.
supervision-reflect : ∀ a kind tid → supervisionTag a ≡ exitTag kind tid → a ≡ R.action kind tid
supervision-reflect (PS.run a) kind tid ()
supervision-reflect (PS.forkMonitor j w) kind tid ()
supervision-reflect (PS.registerMonitor j) kind tid ()
supervision-reflect (PS.returnEstablishment j) kind tid ()
supervision-reflect (PS.finishEstablishment j) kind tid ()
supervision-reflect (PS.monitorException j err) kind tid ()
supervision-reflect (PS.commitMonitorError j) kind tid ()
supervision-reflect (PS.finishMonitorError j) kind tid refl = refl
supervision-reflect (PS.finishMonitor j) kind tid refl = refl
supervision-reflect (PS.scope a) kind tid ()
supervision-reflect (PS.beginMonitorClose order) kind tid ()
supervision-reflect PS.requestMonitorCancel kind tid ()
supervision-reflect PS.joinMonitor kind tid ()
supervision-reflect PS.finishMonitorClose kind tid ()
supervision-reflect (PS.deliverMonitorCancellation err) kind tid ()
supervision-reflect (PS.deliverBlockedMonitorCancellation err) kind tid ()
supervision-reflect (PS.monitorBodyUnwound j) kind tid refl = refl
supervision-reflect (PS.deregisterMonitor j) kind tid ()
supervision-reflect (PS.publishMonitorResult j) kind tid ()

record PhysicalExit (s : PS.State) (kind : R.Kind) (tid : JobId) : Set where
 constructor physical
 field
  after : PS.State
  advanced : PS.step (R.action kind tid) s ≡ just after
  body : R.BodyExit kind tid s after

-- Discharge the tagged primitive supply using the real enabled source step.
source-change : ∀ a s {t} → PS.step a s ≡ just t → Change (PhysicalExit s) (PS.monitorPool s) (PS.monitorPool t)
source-change a s {t} stepped = map-exit supply (step-projects a s stepped)
 where
 supply : ∀ kind tid → supervisionTag a ≡ exitTag kind tid → PhysicalExit s kind tid
 supply kind tid sameTag with supervision-reflect a kind tid sameTag
 ... | refl = physical t stepped (R.physical-exit kind tid s stepped)

-- Retain action identity as well as the enabled source exit, so integration
-- layers can state which selected frontend plan performed this operation.
located-change : ∀ a s {t} → PS.step a s ≡ just t →
 Change (λ kind tid → a ≡ R.action kind tid × PhysicalExit s kind tid) (PS.monitorPool s) (PS.monitorPool t)
located-change a s {t} stepped = map-exit supply (step-projects a s stepped)
 where
 supply : ∀ kind tid → supervisionTag a ≡ exitTag kind tid → a ≡ R.action kind tid × PhysicalExit s kind tid
 supply kind tid sameTag with supervision-reflect a kind tid sameTag
 ... | refl = refl , physical t stepped (R.physical-exit kind tid s stepped)

-- Both movement tags identify their exact physical-supervision action.
move-reflect : ∀ a move tid → supervisionTag a ≡ moveTag move tid → a ≡ moveAction move tid
move-reflect (PS.run a) move tid ()
move-reflect (PS.forkMonitor j w) move tid ()
move-reflect (PS.registerMonitor j) move tid ()
move-reflect (PS.returnEstablishment j) move tid ()
move-reflect (PS.finishEstablishment j) move tid ()
move-reflect (PS.monitorException j err) move tid ()
move-reflect (PS.commitMonitorError j) move tid ()
move-reflect (PS.finishMonitorError j) move tid ()
move-reflect (PS.finishMonitor j) move tid ()
move-reflect (PS.scope a) move tid ()
move-reflect (PS.beginMonitorClose order) move tid ()
move-reflect PS.requestMonitorCancel move tid ()
move-reflect PS.joinMonitor move tid ()
move-reflect PS.finishMonitorClose move tid ()
move-reflect (PS.deliverMonitorCancellation err) move tid ()
move-reflect (PS.deliverBlockedMonitorCancellation err) move tid ()
move-reflect (PS.monitorBodyUnwound j) move tid ()
move-reflect (PS.deregisterMonitor j) move tid refl = refl
move-reflect (PS.publishMonitorResult j) move tid refl = refl

move-pool-step : ∀ move tid s {t} → PS.step (moveAction move tid) s ≡ just t →
 BPool.step (poolMove move tid) (PS.monitorPool s) ≡ just (PS.monitorPool t)
move-pool-step deregistering tid s eq with BPool.step (BPool.deregister tid) (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → refl }
move-pool-step publishing tid s eq with BPool.step (BPool.publishAsyncResult tid) (PS.monitorPool s) in advanced
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → refl }

-- The source registry changes only at deregistration; publishing preserves it.
RegistryEffect : Move → JobId → BPool.State → BPool.State → Set
RegistryEffect deregistering tid p q = BPool.registered q ≡ BPool.remove tid (BPool.registered p)
RegistryEffect publishing tid p q = BPool.registered q ≡ BPool.registered p
move-registry : ∀ move tid p {q} → BPool.step (poolMove move tid) p ≡ just q → RegistryEffect move tid p q
move-registry deregistering tid p eq with lookup tid (BPool.handles p) | BPool.member tid (BPool.registered p)
... | just (BPool.deregisterPending ex) | true = case just-injective eq of λ { refl → refl }
... | just (BPool.deregisterPending ex) | false = case eq of λ ()
... | nothing | _ = case eq of λ ()
... | just BPool.bodyRunning | _ = case eq of λ ()
... | just (BPool.bodyReturned _) | _ = case eq of λ ()
... | just BPool.bodyUnwinding | _ = case eq of λ ()
... | just (BPool.deregistered _) | _ = case eq of λ ()
... | just (BPool.resultAvailable _) | _ = case eq of λ ()
move-registry publishing tid p eq with lookup tid (BPool.handles p)
... | just (BPool.deregistered ex) = case just-injective eq of λ { refl → refl }
... | nothing = case eq of λ ()
... | just BPool.bodyRunning = case eq of λ ()
... | just (BPool.bodyReturned _) = case eq of λ ()
... | just BPool.bodyUnwinding = case eq of λ ()
... | just (BPool.deregisterPending _) = case eq of λ ()
... | just (BPool.resultAvailable _) = case eq of λ ()

record PhysicalMove (s : PS.State) (move : Move) (tid : JobId) : Set where
 constructor physical-move
 field
  after : PS.State
  advanced : PS.step (moveAction move tid) s ≡ just after
  poolStep : BPool.step (poolMove move tid) (PS.monitorPool s) ≡ just (PS.monitorPool after)
  registry : RegistryEffect move tid (PS.monitorPool s) (PS.monitorPool after)

-- The detailed supply is discharged by real enabled source actions, just as
-- the old projection discharges exit witnesses; no caller supplies histories.
full-located-change : ∀ a s {t} → PS.step a s ≡ just t →
 Detailed.Effect (λ kind tid → a ≡ R.action kind tid × PhysicalExit s kind tid)
   (λ move tid → a ≡ moveAction move tid × PhysicalMove s move tid) (PS.monitorPool s) (PS.monitorPool t)
full-located-change a s {t} stepped = Detailed.map-evidence exits moves (Detailed.d-step-projects a s stepped)
 where
 exits : ∀ kind tid → supervisionTag a ≡ exitTag kind tid → a ≡ R.action kind tid × PhysicalExit s kind tid
 exits kind tid tagged with supervision-reflect a kind tid tagged
 ... | refl = refl , physical t stepped (R.physical-exit kind tid s stepped)
 moves : ∀ move tid → supervisionTag a ≡ moveTag move tid → a ≡ moveAction move tid × PhysicalMove s move tid
 moves move tid tagged with move-reflect a move tid tagged
 ... | refl = refl , physical-move t stepped (move-pool-step move tid s stepped)
   (move-registry move tid (PS.monitorPool s) (move-pool-step move tid s stepped))
