{-# OPTIONS --guardedness #-}

-- Actual initialized final-tracer failures; separate conditional pruning and
-- malformed-input controls. No deployed failure/permanent-blocking claim.
module ConnectionManagement.Negative.ServerIGExitControls where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerIGExitInvariants as Invariants
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitRelease as R
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Negative.ServerIGExitCasesFixtures as Z
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.Pruning as Prune
import ConnectionManagement.Scenarios.Admission as A
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
  module Facts = Proof I.bearerClosed
  module Inv = Invariants I.bearerClosed

toCallback : List E.Action
toCallback = R.birthActions ++ (R.handshakeActions ++ (R.registerActions ++
  (R.callActions ++ (R.scopeActions ++ (E.receive E.releaseCounters X.err ∷
    E.run (S.scope S.deactivateIG) ∷ E.run (S.scope S.flushIG) ∷ E.captureSnapshot ∷ E.invokeFinal ∷ [])))))
abstract
  initialized-callback : E.Executes X.start toCallback X.invoked
  initialized-callback = Facts.append R.birthPath (Facts.append R.handshakePath (Facts.append R.registerPath
    (Facts.append R.callPath (Facts.append R.scopePath (E.next R.exit1 (E.next R.exit2 (E.next R.exit3 (E.next R.exit4 (E.next R.exit5 E.done)))))))))

-- A failed catch-handler tracer escapes with its replacement exception. The
-- failed row remains pending, and subsequent callback attempts are disabled.
module Failure (fault : S.Fault) where
  failed exited published : E.State
  failed = record X.invoked { exit = record (E.exit X.invoked) { phase = E.failed; outcome = just fault } }
  exited = record failed { base = record (E.base failed) { stage = S.igBodyExited }
    ; exit = record (E.exit failed) { phase = E.bodyDone } }
  published = record exited { base = record (E.base exited) { stage = S.igResultAvailable }
    ; exit = record (E.exit exited) { result = just fault } }
  fail-step : E.step (E.failFinal fault) X.invoked ≡ just failed
  fail-step = refl
  exit-step : E.step E.finishFinal failed ≡ just exited
  exit-step = refl
  publish-step : E.step (E.run (S.scope S.publishIGResult)) exited ≡ just published
  publish-step = refl
  actions : List E.Action
  actions = toCallback ++ (E.failFinal fault ∷ E.finishFinal ∷ E.run (S.scope S.publishIGResult) ∷ [])
  abstract
    initialized : E.Executes X.start actions published
    initialized = Facts.append initialized-callback (E.next fail-step (E.next exit-step (E.next publish-step E.done)))
  supply : Supply.Valid (E.source published)
  supply = Inv.from-initial-supply R.actual-initializer (All.[] , All.[]) initialized
  replacement-result : E.result (E.exit published) ≡ just fault
  replacement-result = refl
  original-receipt-retained : E.received (E.exit published) ≡ just X.receivedRelease
  original-receipt-retained = refl
  not-a-return : E.returned (E.exit published) ≡ []
  not-a-return = refl
  pending-row-retained : E.remaining (E.exit published) ≡ X.rows
  pending-row-retained = refl
  registry-retained : IG.publishedState (E.governor published) ≡ X.registeredState
  registry-retained = refl
  no-next-invocation : E.step E.invokeFinal failed ≡ nothing
  no-next-invocation = refl
  no-false-return : E.step E.returnFinal failed ≡ nothing
  no-false-return = refl
module SyncFailure = Failure (S.sync (errorId 141))
-- This action observes blocking in the MaskedInterruptible final tracer.
module AsyncFailure = Failure (S.async (errorId 142))
no-failure-before-invocation : E.step (E.failFinal (S.sync (errorId 141))) X.snapshot ≡ nothing
no-failure-before-invocation = refl

-- Conditional pruning-cursor input: no initialized pruning history is claimed.
-- In particular this does not manufacture births/results for the victim tokens.
victim other : Prune.Candidate
victim = Prune.candidate A.key₀ (ident 0) A.child₀ 4 false
other = Prune.candidate A.key₁ (ident 1) A.child₁ 4 false
pruningFrame : Remote.Frame
pruningFrame = record Y.promotedFrame
  { pc = Remote.awaitDelivery victim (other ∷ []); pruneVictims = victim ∷ other ∷ [] }
pruning : E.State
pruning = X.atScope S.igCancelRequested false (Y.render (record Y.g6 { cmRemote = just pruningFrame }))
pruningReceipt : E.Receipt
pruningReceipt = E.receipt E.promoteSend X.err (just (E.remoteCall pruningFrame))
pruningCaught : E.State
pruningCaught = E.igExitState
  (record (S.setSource (E.clearPending (E.source pruning)) (E.base pruning)) { stage = S.igCancelDelivered })
  (E.caughtExit pruningReceipt)
conditional-prune-send : E.step (E.receive E.promoteSend X.err) pruning ≡ just pruningCaught
conditional-prune-send = refl
whole-pruning-cursor-retained : E.received (E.exit pruningCaught) ≡ just pruningReceipt
whole-pruning-cursor-retained = refl
handler-descriptors-retained : Shared.handlers (Machine.world (O.core (E.source pruningCaught))) ≡ Shared.handlers (Machine.world (O.core (E.source pruning)))
handler-descriptors-retained = refl
no-synthetic-receiver-step : S.setSource (E.source pruning) (E.base pruningCaught) ≡
  record (E.base pruning) { stage = S.igCancelDelivered }
no-synthetic-receiver-step = refl
exact-source-unwind : E.source pruningCaught ≡ E.clearPending (E.source pruning)
exact-source-unwind = Facts.receive-source E.promoteSend X.err pruning conditional-prune-send

-- Malformed dual caller frames cannot be silently resolved by dropping one.
dual : E.State
dual = X.atScope S.igCancelRequested false (Y.render (record Y.g5 { cmRelease = just X.releaseFrame }))
no-dual-receipt : E.step (E.receive E.promoteRead X.err) dual ≡ nothing
no-dual-receipt = refl

-- Conditional registry-order control; these extra registrations are data, not
-- a claim of a second initialized connection. Timers are absent from the view.
second : IG.Registration
second = IG.registration (Shared.newConnectionInfo inbound A.key₁ duplex (ident 1)) IG.remoteWarm
reversed : E.snapshotRows ((A.key₁ , second) ∷ (A.key₀ , IG.registered X.F.info (ident 1)) ∷ []) ≡
  (A.key₀ , E.idle) ∷ (A.key₁ , E.warm) ∷ []
reversed = refl
no-duplicate-snapshot-input : E.unique ((A.key₀ , second) ∷ (A.key₀ , second) ∷ []) ≡ false
no-duplicate-snapshot-input = refl
