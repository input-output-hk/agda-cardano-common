{-# OPTIONS --guardedness #-}

-- Apply the unchanged invariants to initialized histories and enabled writers.
-- The nonempty acquisition fixture below is explicitly conditional, not a new
-- initialized outbound-lifecycle claim. Resources mean historical presence.
module ConnectionManagement.Negative.ServerAdmissionInvariants where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Properties.ServerAdmissionInvariants as Proof
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerAdmissionPrefix as Prefix
import ConnectionManagement.Negative.ServerAdmission as Owned
import ConnectionManagement.Scenarios.Admission as A
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit; append)
import ConnectionManagement.Rules.Server as Admission
private
  module S = Server I.bearerClosed
  module Facts = Proof I.bearerClosed
  module H = Prefix.HardLimit
  module F = H.F
  module Fork = Prefix.ForkFailure
  module Denied = Prefix.Forbidden

-- All seven accepted prefix/close histories satisfy the real supply theorem.
hard-supply : Supply.Valid (S.source F.h6)
hard-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) H.initialized
hard-captures : Capture.Captures (S.source F.h6)
hard-captures = Facts.from-initial-captures H.actual-initializer H.initialized
fork-supply : Supply.Valid (S.source F.f5)
fork-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) Fork.initialized
forbidden-supply : Supply.Valid (S.source Denied.F.b8)
forbidden-supply = Facts.from-initial-supply Denied.actual-initializer (All.[] , All.[]) Denied.initialized
retry-success-supply : Supply.Valid (S.source H.retryOKResult)
retry-success-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) H.initialized-retry-success
retry-failure-supply : Supply.Valid (S.source H.retryResult)
retry-failure-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) H.initialized-retry-failure
fork-replacement-supply : Supply.Valid (S.source Fork.replacedResult)
fork-replacement-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) Fork.initialized-cleanup-failure
forbidden-replacement-supply : Supply.Valid (S.source Denied.replacedResult)
forbidden-replacement-supply = Facts.from-initial-supply Denied.actual-initializer (All.[] , All.[]) Denied.initialized-cleanup-failure

-- The earlier initialized Server-return counterexample exercises actual IG
-- deactivation/flush and CM shutdown. Invariants do not finish its raw worker.
scope-supply : Supply.Valid (S.source Owned.returnedServer)
scope-supply = Facts.from-initial-supply Owned.actual-initializer (All.[] , All.[]) Owned.initialized
scope-recovery : S.Executes Owned.returnedServer
  (S.workerException A.w₀ Owned.recoveryError ∷ S.workerClose A.w₀ nothing ∷ S.workerResult A.w₀ ∷ []) Owned.recovered
scope-recovery = S.next Owned.recovery1 (S.next Owned.recovery2 (S.next Owned.recovery3 S.done))
scope-recovery-supply : Supply.Valid (S.source Owned.recovered)
scope-recovery-supply = Facts.supply-exec scope-recovery scope-supply

-- Resource suffixes start AFTER the actual first handler birth, with its exact
-- original descriptor. No handler certificate is assumed in the empty start.
hard-suffix : S.Executes F.p5
  (admit A.w₀ Admission.putMapBack ∷ admit A.w₀ Admission.readCounters ∷ H.rejectActions) F.h6
hard-suffix = S.next H.installed2 (S.next H.installed3 H.rejectPath)
hard-resources : ResourceFacts.Facts A.child₀ I.captured (S.shared F.h6)
hard-resources = Facts.For.exec-preserves A.child₀ I.captured hard-suffix
  (refl , (F.unneg , refl) , (Shared.handling A.child₀ , refl))
forbidden-suffix : S.Executes Denied.F.p5
  (admit A.w₀ Admission.putMapBack ∷ admit A.w₀ Admission.readCounters ∷ (Denied.handshakeActions ++ Denied.rejectActions)) Denied.F.b8
forbidden-suffix = S.next Denied.installed2 (S.next Denied.installed3 (append Denied.handshakePath Denied.rejectPath))
forbidden-resources : ResourceFacts.Facts A.child₀ I.captured (S.shared Denied.F.b8)
forbidden-resources = Facts.For.exec-preserves A.child₀ I.captured forbidden-suffix
  (refl , (Denied.F.unneg , refl) , (Shared.handling A.child₀ , refl))

-- A real raw caller can receive cancellation at its promise wait, then close
-- the SAME stored socket while its handler's resource record remains present.
err : S.Fault
err = S.async (errorId 130)
cancelled closed finished : S.State
cancelled = S.setPC A.w₀ (S.rawWorker F.r₀ S.calling 0) (S.closeException err) F.p7
closed = record (S.setWorld (record (S.shared F.p7)
  { sockets = put (ident 0) Shared.closed (Shared.sockets (S.shared F.p7)) }) F.p7)
  { workers = put A.w₀ (S.rawWorker F.r₀ (S.bodyExited (S.raised err)) 1) (S.workers F.p7) }
finished = S.setPC A.w₀ (S.rawWorker F.r₀ (S.bodyExited (S.raised err)) 1) (S.resultAvailable (S.raised err)) closed
cancel-step : S.step (S.workerException A.w₀ err) F.p7 ≡ just cancelled
cancel-step = refl
close-step : S.step (S.workerClose A.w₀ nothing) cancelled ≡ just closed
close-step = refl
result-step : S.step (S.workerResult A.w₀) closed ≡ just finished
result-step = refl
caller-actions : List S.Action
caller-actions = S.workerException A.w₀ err ∷ S.workerClose A.w₀ nothing ∷ S.workerResult A.w₀ ∷ []
caller-suffix : S.Executes F.p7 caller-actions finished
caller-suffix = S.next cancel-step (S.next close-step (S.next result-step S.done))
abstract
  caller-initialized : S.Executes F.start (H.birthActions ++ (H.installedActions ++ caller-actions)) finished
  caller-initialized = append H.birthPath (append H.installedPath caller-suffix)
caller-supply : Supply.Valid (S.source finished)
caller-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) caller-initialized
closed-resource-retained : ResourceFacts.Facts A.child₀ I.captured (S.shared finished)
closed-resource-retained = Facts.For.exec-preserves A.child₀ I.captured caller-suffix
  (refl , (F.unneg , refl) , (Shared.handling A.child₀ , refl))

-- Inject a well-formed pending capture to test that writer preservation is
-- nonvacuous. This input is conditional; no forged frame gets a birth history.
pending : Acquire.Runtime
pending = (ident 20 , Acquire.frame
  (Acquire.acquireRequest (remote A.key₀) (ident 21) (ident 20) outbound nothing)
  (Acquire.awaitResult (ident 0) (ident 0) A.key₀)) ∷ []
withPending : S.State → S.State
withPending s = S.setSource (record (S.source s) { acquiring = pending }) s
pending-captures : Capture.Captures (S.source (withPending F.p7))
pending-captures = (F.unneg , refl) All.∷ All.[]
wait-supply : Supply.Valid (S.source F.p7)
wait-supply = Facts.from-initial-supply H.actual-initializer (All.[] , All.[]) (append H.birthPath H.installedPath)
lateRequest : Shared.Admission
lateRequest = Shared.admission A.key₁ (ident 2) (ident 5) 1
late : S.State
late = record (S.setWorld (record (S.shared (withPending F.p7))
  { admissions = put (ident 4) (Shared.admissionWorker lateRequest Shared.acquireMap) (Shared.admissions (S.shared F.p7))
  ; sockets = put (ident 2) (Shared.admitting (ident 4)) (Shared.sockets (S.shared F.p7)) }) (withPending F.p7))
  { workers = put (ident 4) (S.rawWorker lateRequest S.calling 0) (S.workers F.p7) }
late-handoff : S.step (S.acceptedFork (ident 4) lateRequest) (withPending F.p7) ≡ just late
late-handoff = refl
late-captures : Capture.Captures (S.source late)
late-captures = Facts.captures-step (S.acceptedFork (ident 4) lateRequest) (withPending F.p7) late-handoff pending-captures
late-supply : Supply.Valid (S.source late)
late-supply = Facts.supply-step (S.acceptedFork (ident 4) lateRequest) (withPending F.p7) late-handoff
  (pending-captures , proj₂ wait-supply)
late-resources : ResourceFacts.Facts A.child₀ I.captured (S.shared late)
late-resources = Facts.For.step-preserves A.child₀ I.captured
  (S.acceptedFork (ident 4) lateRequest) (withPending F.p7) late-handoff
  (refl , (F.unneg , refl) , (Shared.handling A.child₀ , refl))
pending-close : S.step (S.workerClose A.w₀ nothing) (withPending cancelled) ≡ just (withPending closed)
pending-close = refl
pending-after-cancel : Capture.Captures (S.source (withPending cancelled))
pending-after-cancel = (F.unneg , refl) All.∷ All.[]
pending-after-close : Capture.Captures (S.source (withPending closed))
pending-after-close = Facts.captures-step (S.workerClose A.w₀ nothing) (withPending cancelled) pending-close pending-after-cancel
pending-close-supply : Supply.Valid (S.source (withPending closed))
pending-close-supply = Facts.supply-step (S.workerClose A.w₀ nothing) (withPending cancelled) pending-close
  (pending-after-cancel , proj₂ wait-supply)

-- The initializer does not manufacture missing initial supply bounds.
badWorld : Shared.State
badWorld = record F.empty { promises = ident 0 ∷ [] }
badStart : S.State
badStart = S.setWorld badWorld F.start
bad-initializer : S.initial (O.initial (Machine.initial Shared.responderMode badWorld)) ≡ just badStart
bad-initializer = refl
no-initial-supply : Supply.Valid (S.source badStart) → ⊥
no-initial-supply (_ , _ , (() All.∷ _))
no-unconditional-initial-supply :
  (∀ {c start} → S.initial (O.initial c) ≡ just start → Supply.Valid (S.source start)) → ⊥
no-unconditional-initial-supply claim = no-initial-supply (claim bad-initializer)
