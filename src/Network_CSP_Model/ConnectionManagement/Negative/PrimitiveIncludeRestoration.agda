{-# OPTIONS --guardedness #-}

-- G1 F1: observed restored-body exceptions restore the saved map, retaining
-- current heap/promise writes and any physical child already forked. The raw
-- worker then runs its separate outer onException socket close/result path.
module ConnectionManagement.Negative.PrimitiveIncludeRestoration where

open import Data.Bool using (false)
open import Data.List using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.OutboundHandlerSupervision as Physical
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Fixtures
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Scenarios.Admission as A
module F = Fixtures 2 A.key₀
module S = Server I.bearerClosed
module N = Publication I.bearerClosed
module W = N.W
module R = N.R

fault : S.Fault
fault = S.async (errorId 44)
receipt restored closed : S.State
receipt = F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p5
restored = F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0
 (F.early (Shared.full []) (Shared.closeSocket Shared.bodyFailed) Shared.acquireMap (Shared.admitting A.w₁))
closed = F.raw₀ (S.bodyExited (S.raised fault)) 1
 (F.early (Shared.full []) (Shared.finished Shared.bodyFailed) Shared.acquireMap (Shared.admitting A.w₁))
-- The helper for expected close also applies the actual source socket update.
expectedClosed : S.State
expectedClosed = S.setWorld (record (S.shared closed)
 { sockets = put (ident 0) Shared.closed (Shared.sockets (S.shared closed)) }) closed

after-fork-receipt : S.step (S.workerException A.w₀ fault) F.p5 ≡ just receipt
after-fork-receipt = refl
restore-saved-map : S.step (S.workerRestore A.w₀) receipt ≡ just restored
restore-saved-map = refl
map-is-original : Shared.mapCell (Shared.cm (S.shared restored)) ≡ Shared.full []
map-is-original = refl
heap-not-rolled-back : Shared.entries (Shared.cm (S.shared restored)) ≡ Shared.entries (Shared.cm (S.shared F.p5))
heap-not-rolled-back = refl
promise-not-rolled-back : Shared.promises (S.shared restored) ≡ Shared.promises (S.shared F.p5)
promise-not-rolled-back = refl
child-not-rolled-back : Shared.handlers (S.shared restored) ≡ Shared.handlers (S.shared F.p5)
child-not-rolled-back = refl
physical-child-kept : Physical.threads (W.physical (R.base (N.raw (S.base restored)))) ≡ Physical.threads (W.physical (R.base (N.raw (S.base F.p5))))
physical-child-kept = refl
restore-does-not-close : lookup (ident 0) (Shared.sockets (S.shared restored)) ≡ just (Shared.handling A.child₀)
restore-does-not-close = refl
close-separate : S.step (S.workerClose A.w₀ nothing) restored ≡ just expectedClosed
close-separate = refl
result-after-close : S.step (S.workerResult A.w₀) expectedClosed ≡ just
 (F.raw₀ (S.resultAvailable (S.raised fault)) 1 expectedClosed)
result-after-close = refl
no-close-before-restore : S.step (S.workerClose A.w₀ nothing) receipt ≡ nothing
no-close-before-restore = refl
no-result-before-restore : S.step (S.workerResult A.w₀) receipt ≡ nothing
no-result-before-restore = refl
no-normal-publication-after-receipt : S.step (S.run (S.runMachine (Machine.admissionStep A.w₀ Admission.putMapBack))) receipt ≡ nothing
no-normal-publication-after-receipt = refl
no-unaccompanied-restore : S.step (S.run (S.runMachine (Machine.admissionStep A.w₀ Admission.restoreBody))) receipt ≡ nothing
no-unaccompanied-restore = refl
no-second-receipt-in-masked-restore : S.step (S.workerException A.w₀ fault) receipt ≡ nothing
no-second-receipt-in-masked-restore = refl
no-restore-twice : S.step (S.workerRestore A.w₀) restored ≡ nothing
no-restore-twice = refl
post-publication-exception : S.step (S.workerException A.w₀ fault) F.p6 ≡ just (F.raw₀ (S.closeException fault) 0 F.p6)
post-publication-exception = refl
post-publication-no-rollback : S.step (S.workerRestore A.w₀) (F.raw₀ (S.closeException fault) 0 F.p6) ≡ nothing
post-publication-no-rollback = refl
before-fork-receipt : S.step (S.workerException A.w₀ fault) F.p4 ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p4)
before-fork-receipt = refl
before-count-receipt : S.step (S.workerException A.w₀ fault) F.p1 ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p1)
before-count-receipt = refl
before-lease-refused : S.step (S.workerException A.w₀ fault) F.two ≡ nothing
before-lease-refused = refl
foreign-lease-refused : S.step (S.workerRestore A.w₀)
 (S.setWorld (record (S.shared receipt) { cm = record (Shared.cm (S.shared receipt)) { mapCell = Shared.taken A.w₁ } }) receipt) ≡ nothing
foreign-lease-refused = refl
no-child-result-fabricated : W.resultReady A.child₀ (R.base (N.raw (S.base restored))) ≡ false
no-child-result-fabricated = refl

after-count-receipt : S.step (S.workerException A.w₀ fault) F.p2 ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p2)
after-count-receipt = refl
after-promise-receipt : S.step (S.workerException A.w₀ fault) F.p3 ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p3)
after-promise-receipt = refl
synchronous-body-receipt : S.step (S.workerException A.w₀ (S.sync (errorId 45))) F.p5 ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised (S.sync (errorId 45)))) 0 F.p5)
synchronous-body-receipt = refl
before-fork-restore : S.step (S.workerRestore A.w₀)
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0 F.p4) ≡ just
 (F.raw₀ (S.closePrefix Shared.bodyFailed (S.raised fault)) 0
   (F.pre (F.allocated (Shared.full [])) (Shared.closeSocket Shared.bodyFailed)
     Shared.acquireMap F.ps₀ 1 (Shared.admitting A.w₀)))
before-fork-restore = refl
