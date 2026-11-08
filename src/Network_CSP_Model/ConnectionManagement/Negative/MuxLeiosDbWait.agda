{-# OPTIONS --guardedness #-}

-- M5 controls: collector-owned synchronous LeiosDB waits (consensus 2e44d98,
-- LeiosDemoLogic processLeiosBlock/ingestAcquiredTxs; LeiosDB WriteQueue
-- submitJob/startWriter). A collector that submitted a write cannot send or
-- return its body until its await ends; a completed write lets the await
-- return, a sealed queue makes it throw into the existing synchronous error
-- capture; cancelling the collector neither blocks its unwind nor retracts the
-- queued write, which the node-owned writer can still complete.
module ConnectionManagement.Negative.MuxLeiosDbWait where

open import Agda.Builtin.Reflection using (Term; TC; normalise; unify; bindTC)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.IGTypes using (errored)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.MuxProtocolJobs as W
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxResultMonitor as ResultMonitor
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Negative.MuxResultMonitor as F
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Negative.MuxProtocolJobs as Plain
module G = Group F.bearerClosed
module MM = ResultMonitor F.bearerClosed

-- One-step snapshot builder (see MuxConfiguredWholeClose); edges stay refl.
macro
  snapshot : Term → Term → TC ⊤
  snapshot t hole = bindTC (normalise t) (unify hole)
pafter : W.Action → W.State → W.State
pafter a s with W.step a s
... | just t = t
... | nothing = s
gafter : G.Action → G.State → G.State
gafter a s with G.step a s
... | just t = t
... | nothing = s
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false

j : JobId
j = Plain.j₁₀
err : ErrorId
err = Plain.err
engine : O.Configuration → IG.Engine
engine c = IG.execution (M.inboundGovernor (O.core c))
writes : O.Configuration → Store ℕ (JobId × Bool)
writes c = IG.dbWrites (engine c)
waits : O.Configuration → Store JobId ℕ
waits c = IG.dbWaits (engine c)

-- The entered responder body can still send and return before any DB wait.
entered-can-send : isJust (W.step (W.appendProtocolPayload j 1) Plain.r6Entered) ≡ true
entered-can-send = refl
entered-can-return : isJust (W.step (W.protocolReturned j) Plain.r6Entered) ≡ true
entered-can-return = refl

-- Submission: the write is queued for this collector, which now awaits it.
d1 d2 d3 d4 : W.State
d1 = snapshot (pafter (W.submitDbWrite j 0) Plain.r6Entered)
d2 = snapshot (pafter (W.writerComplete 0) d1)
d3 = snapshot (pafter (W.awaitDbWrite j) d2)
d4 = snapshot (pafter (W.protocolReturned j) d3)
submitted : W.step (W.submitDbWrite j 0) Plain.r6Entered ≡ just d1
submitted = refl
queued : writes (W.source d1) ≡ (0 , j , false) ∷ []
queued = refl
awaiting : waits (W.source d1) ≡ (j , 0) ∷ []
awaiting = refl

-- A pending write blocks the body: no send, no return (hence no clean commit).
pending-blocks-send : W.step (W.appendProtocolPayload j 1) d1 ≡ nothing
pending-blocks-send = refl
pending-blocks-return : W.step (W.protocolReturned j) d1 ≡ nothing
pending-blocks-return = refl
await-before-completion-refused : W.step (W.awaitDbWrite j) d1 ≡ nothing
await-before-completion-refused = refl
failure-before-seal-refused : W.step (W.dbWriteFailed j) d1 ≡ nothing
failure-before-seal-refused = refl
second-submit-refused : W.step (W.submitDbWrite j 1) d1 ≡ nothing
second-submit-refused = refl

-- Successful completion: the writer fills the result, the await returns and
-- the body may return; the completed write stays recorded.
completed : W.step (W.writerComplete 0) d1 ≡ just d2
completed = refl
duplicate-completion-refused : W.step (W.writerComplete 0) d2 ≡ nothing
duplicate-completion-refused = refl
await-returns : W.step (W.awaitDbWrite j) d2 ≡ just d3
await-returns = refl
await-cleared : waits (W.source d3) ≡ []
await-cleared = refl
write-kept : writes (W.source d3) ≡ (0 , j , true) ∷ []
write-kept = refl
completion-enables-return : W.step (W.protocolReturned j) d3 ≡ just d4
completion-enables-return = refl
returned-phase : lookup j (W.jobs d4) ≡ just (Plain.rJob T.waitingEgress)
returned-phase = refl

-- Sealed queue: no later completion; the await throws the seal cause into the
-- collector's synchronous error capture; the queued write is not retracted.
e2 e3 : W.State
e2 = snapshot (pafter (W.writerSeal err) d1)
e3 = snapshot (pafter (W.dbWriteFailed j) e2)
sealed : W.step (W.writerSeal err) d1 ≡ just e2
sealed = refl
completion-after-seal-refused : W.step (W.writerComplete 0) e2 ≡ nothing
completion-after-seal-refused = refl
await-after-seal-refused : W.step (W.awaitDbWrite j) e2 ≡ nothing
await-after-seal-refused = refl
seal-failure : W.step (W.dbWriteFailed j) e2 ≡ just e3
seal-failure = refl
seal-error-captured : lookup j (W.jobs e3) ≡ just (Plain.rJob (T.resultCaptured (errored err)))
seal-error-captured = refl
failed-await-cleared : waits (W.source e3) ≡ []
failed-await-cleared = refl
failed-write-kept : writes (W.source e3) ≡ (0 , j , false) ∷ []
failed-write-kept = refl
failed-body-returns : isJust (W.step (W.returnProtocol j) e3) ≡ true
failed-body-returns = refl

-- A result completed before the seal still wins the await.
f2 : W.State
f2 = snapshot (pafter (W.writerSeal err) d2)
completed-before-seal : W.step (W.writerSeal err) d2 ≡ just f2
completed-before-seal = refl
completed-wins-await : isJust (W.step (W.awaitDbWrite j) f2) ≡ true
completed-wins-await = refl
completed-not-failed : W.step (W.dbWriteFailed j) f2 ≡ nothing
completed-not-failed = refl

-- Submission to an already sealed queue throws at once: nothing is queued.
s1 : W.State
s1 = snapshot (pafter (W.writerSeal err) Plain.r6Entered)
sealed-submit-refused : W.step (W.submitDbWrite j 0) s1 ≡ nothing
sealed-submit-refused = refl
sealed-submit-throws : lookup j (W.jobs (pafter (W.dbWriteFailed j) s1)) ≡ just (Plain.rJob (T.resultCaptured (errored err)))
sealed-submit-throws = refl

-- Initialized successful path: start, responder entry, submit, complete,
-- await and body return.
pappend : ∀ {p as q bs r} → W.Executes p as q → W.Executes q bs r → W.Executes p (as ++ bs) r
pappend W.done tail = tail
pappend (W.next eq path) tail = W.next eq (pappend path tail)
waitActions : List W.Action
waitActions = W.control Plain.owner W.selectCommand ∷ W.control Plain.owner (W.demand 1) ∷
  W.control Plain.owner W.sampleTracer ∷ W.control Plain.owner W.commitTracer ∷
  W.control Plain.owner W.finishStart ∷ W.forkResponder Plain.owner j Plain.r₀ ∷
  W.enterProtocolBody j ∷ W.submitDbWrite j 0 ∷ W.writerComplete 0 ∷ W.awaitDbWrite j ∷
  W.protocolReturned j ∷ []
waitPath : W.Executes Plain.z12 waitActions d4
waitPath = W.next Plain.responder1 (W.next Plain.responder2 (W.next Plain.responder3
  (W.next Plain.responder4 (W.next Plain.responder5 (W.next Plain.responder6
  (W.next Plain.responderEntry (W.next submitted (W.next completed (W.next await-returns
  (W.next completion-enables-return W.done))))))))))
abstract
  initialized-db-wait : W.Executes Plain.b0 (Plain.startActions ++ waitActions) d4
  initialized-db-wait = pappend Plain.initialized-start waitPath

-- Group cancellation of a collector blocked in its await: from the actual
-- running fixture, submit, then graceful shutdown captures, cancels and
-- unwinds the job while its write is still queued.
g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 : G.State
g0 = GF.normal0
g1 = snapshot (gafter (G.run (MM.run (W.submitDbWrite j 0))) g0)
g2 = snapshot (gafter (G.requestShutdown Plain.owner) g1)
g3 = snapshot (gafter (G.selectShutdown Plain.owner) g2)
g4 = snapshot (gafter (G.observeStoppingTrace Plain.owner) g3)
g5 = snapshot (gafter (G.writeStopping Plain.owner) g4)
g6 = snapshot (gafter (G.captureGroup Plain.owner (j ∷ [])) g5)
g7 = snapshot (gafter (G.requestGroupCancel Plain.owner) g6)
g8 = snapshot (gafter (G.deliverGroup Plain.owner) g7)
g9 = snapshot (gafter (G.finishChildUnwind j) g8)
h1 : G.step (G.run (MM.run (W.submitDbWrite j 0))) g0 ≡ just g1
h1 = refl
h2 : G.step (G.requestShutdown Plain.owner) g1 ≡ just g2
h2 = refl
h3 : G.step (G.selectShutdown Plain.owner) g2 ≡ just g3
h3 = refl
h4 : G.step (G.observeStoppingTrace Plain.owner) g3 ≡ just g4
h4 = refl
h5 : G.step (G.writeStopping Plain.owner) g4 ≡ just g5
h5 = refl
h6 : G.step (G.captureGroup Plain.owner (j ∷ [])) g5 ≡ just g6
h6 = refl
h7 : G.step (G.requestGroupCancel Plain.owner) g6 ≡ just g7
h7 = refl
-- Delivery and unwind are not blocked by the pending await.
h8 : G.step (G.deliverGroup Plain.owner) g7 ≡ just g8
h8 = refl
h9 : G.step (G.finishChildUnwind j) g8 ≡ just g9
h9 = refl
cancelActions : List G.Action
cancelActions = G.run (MM.run (W.submitDbWrite j 0)) ∷ G.requestShutdown Plain.owner ∷
  G.selectShutdown Plain.owner ∷ G.observeStoppingTrace Plain.owner ∷ G.writeStopping Plain.owner ∷
  G.captureGroup Plain.owner (j ∷ []) ∷ G.requestGroupCancel Plain.owner ∷
  G.deliverGroup Plain.owner ∷ G.finishChildUnwind j ∷ []
cancelPath : G.Executes g0 cancelActions g9
cancelPath = G.next h1 (G.next h2 (G.next h3 (G.next h4 (G.next h5 (G.next h6
  (G.next h7 (G.next h8 (G.next h9 G.done))))))))
gappend : ∀ {p as q bs r} → G.Executes p as q → G.Executes q bs r → G.Executes p (as ++ bs) r
gappend G.done tail = tail
gappend (G.next eq path) tail = G.next eq (gappend path tail)
abstract
  initialized-cancelled-wait : G.Executes (GF.wrap (F.wrap Plain.b0))
    (map G.run (map MM.run Plain.startActions ++ F.errorPrefixActions) ++ cancelActions) g9
  initialized-cancelled-wait = gappend GF.initialized-running cancelPath

-- The interrupted collector cannot resume its await, even once the write
-- completes; the queued write is not retracted and the writer completes it.
cancelled-write-queued : writes (G.source g9) ≡ (0 , j , false) ∷ []
cancelled-write-queued = refl
writer-completes-after-cancel : isJust (G.step (G.run (MM.run (W.writerComplete 0))) g9) ≡ true
writer-completes-after-cancel = refl
cancelled-await-refused : G.step (G.run (MM.run (W.awaitDbWrite j)))
  (gafter (G.run (MM.run (W.writerComplete 0))) g9) ≡ nothing
cancelled-await-refused = refl

-- Universal guard: in every state, a collector with an outstanding DB await
-- can neither append payload nor return its body (so it cannot reach clean
-- completion) until the await is taken or abandoned.
awaiting-blocks : ∀ k s r {d} → lookup k (IG.dbWaits (W.dbEngine s)) ≡ just d →
  W.unlessAwaiting k s r ≡ nothing
awaiting-blocks k s r eq with lookup k (IG.dbWaits (W.dbEngine s)) | eq
... | just _ | refl = refl
awaiting-blocks-send : ∀ k bytes s {d} → lookup k (IG.dbWaits (W.dbEngine s)) ≡ just d →
  W.step (W.appendProtocolPayload k bytes) s ≡ nothing
awaiting-blocks-send k bytes s = awaiting-blocks k s (W.sendProtocol k bytes s)
awaiting-blocks-return : ∀ k s {d} → lookup k (IG.dbWaits (W.dbEngine s)) ≡ just d →
  W.step (W.protocolReturned k) s ≡ nothing
awaiting-blocks-return k s = awaiting-blocks k s (W.returned k s)
