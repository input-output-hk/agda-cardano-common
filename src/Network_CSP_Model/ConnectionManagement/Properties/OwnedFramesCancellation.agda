{-# OPTIONS --guardedness #-}

-- Cancellation removes the source frames before the job handle stops running.
-- This component retains both ownership clauses and all auxiliary metadata.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesCancellation
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
open import ConnectionManagement.Properties.OutboundKeys using (Unique; acquireFrames; releaseFrames)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesCancel as CancelFacts
import ConnectionManagement.Properties.OwnedFramesUniquePeers as UniqueFacts
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)
private module U = UniqueFacts isIOManagerError

-- Deleting an acquisition cannot invalidate any retained ownership witness.
delete-acquire-inv : ∀ c k w → Unique c → Inv c k → Inv (record c { acquiring = delete w (O.acquiring c) }) k
delete-acquire-inv c k w unique inv = owned-frames acq (releasing inv)
  where
  acq : ∀ q → is-just (lookup q (delete w (O.acquiring c))) ≡ true →
    lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire k
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (delete-self w (O.acquiring c) (acquireFrames unique)))) present of λ ()
  ... | no apart = acquiring inv q (trans (sym (cong is-just (delete-other w q (O.acquiring c) apart))) present)

-- The corresponding deletion for a release is symmetric.
delete-release-inv : ∀ c k w → Unique c → Inv c k → Inv (record c { releasing = delete w (O.releasing c) }) k
delete-release-inv c k w unique inv = owned-frames (acquiring inv) rel
  where
  rel : ∀ q → is-just (lookup q (delete w (O.releasing c))) ≡ true →
    lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease k
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (delete-self w (O.releasing c) (releaseFrames unique)))) present of λ ()
  ... | no apart = releasing inv q (trans (sym (cong is-just (delete-other w q (O.releasing c) apart))) present)

-- Every successful start preserves ownership at the old peer context.
start-inv : ∀ w err context c {f d} → Cancel.start w err context c ≡ just (f , d) →
  ∀ k → Unique c → Inv c k → Inv d k
start-inv w err Cancel.protectedCleanup c eq k unique inv = case eq of λ ()
start-inv w err Cancel.ordinary c eq k unique inv with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire-inv c k w unique inv }
start-inv w err Cancel.ordinary c eq k unique inv | nothing | just active = case just-injective eq of λ { refl → delete-release-inv c k w unique inv }
start-inv w err Cancel.ordinary c eq k unique inv | nothing | nothing = case just-injective eq of λ { refl → inv }
start-inv w err Cancel.ordinary c eq k unique inv | just _ | just _ = case eq of λ ()
start-inv w err Cancel.forkedBeforeHandoff c eq k unique inv with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire-inv c k w unique inv }
start-inv w err Cancel.forkedBeforeHandoff c eq k unique inv | nothing | nothing = case eq of λ ()
start-inv w err Cancel.forkedBeforeHandoff c eq k unique inv | nothing | just _ = case eq of λ ()
start-inv w err Cancel.forkedBeforeHandoff c eq k unique inv | just _ | just _ = case eq of λ ()
start-inv w err Cancel.interruptibleOpen c eq k unique inv with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active)
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl → delete-acquire-inv c k w unique inv }
start-inv w err Cancel.interruptibleOpen c eq k unique inv | nothing | nothing = case eq of λ ()
start-inv w err Cancel.interruptibleOpen c eq k unique inv | nothing | just _ = case eq of λ ()
start-inv w err Cancel.interruptibleOpen c eq k unique inv | just _ | just _ = case eq of λ ()

-- Named context writer for the governor's detached-call and pool update.
cancel-context : C.Context → JobId → Cancel.Frame → GP.Pool.State → C.Context
cancel-context k j f p = record k { governorPool = p; unwinding = put j f (C.unwinding k) }

-- Other callers' owners survive the canceled job's handle replacement.
cancel-owner : ∀ k j jf f p → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  GP.Pool.handles p ≡ put j GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)) →
  ∀ q pc → q ≢ J.caller (Sub.execution jf) → Owner q pc k → Owner q pc (cancel-context k j f p)
cancel-owner k j jf f p found handles q pc apart (inj₁ foreign) = inj₁ foreign
cancel-owner k j jf f p found handles q pc apart (inj₂ (inj₁ owner)) with JobAwait.job owner ≟ j
... | yes refl = case just-injective (trans (sym found) (JobAwait.found owner)) of λ
  { refl → ⊥-elim (apart (sym (JobAwait.caller owner))) }
... | no other = inj₂ (inj₁ (job-await (JobAwait.job owner) (JobAwait.frame owner)
  (JobAwait.found owner) (JobAwait.caller owner) (JobAwait.waiting owner)
  (trans (cong (lookup (JobAwait.job owner)) handles)
    (trans (lookup-put-other j (JobAwait.job owner) GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)) other) (JobAwait.running owner)))))
cancel-owner k j jf f p found handles q pc apart (inj₂ (inj₂ owner)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner)
    (FollowAwait.caller owner) (FollowAwait.waiting owner) (FollowAwait.tid owner)
    (FollowAwait.thread owner) (FollowAwait.byPeer owner) (FollowAwait.worker owner)
    (FollowAwait.running owner) (FollowAwait.observing owner)))

-- Followup attachment does not depend on the governor pool or unwind store.
cancel-follow : ∀ k j f p ref follow → FollowThread ref follow k → FollowThread ref follow (cancel-context k j f p)
cancel-follow k j f p ref follow old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- The new unwind row has the job's exact caller and non-running handle.
cancel-aux : ∀ k j jf f p → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  Cancel.caller f ≡ J.caller (Sub.execution jf) →
  GP.Pool.handles p ≡ put j GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)) →
  Aux k → Aux (cancel-context k j f p)
cancel-aux k j jf f p found caller handles old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old
  ; unwindKeys = put-unique j f (C.unwinding k) (Aux.unwindKeys old)
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref follow present → cancel-follow k j f p ref follow (Aux.followThreads old ref follow present)
  ; unwindingJobs = unwinds }
  where
  unwinds : ∀ q cf → lookup q (put j f (C.unwinding k)) ≡ just cf → UnwindJob q cf (cancel-context k j f p)
  unwinds q cf present with q ≟ j
  ... | yes refl with just-injective (trans (sym (lookup-put j f (C.unwinding k))) present)
  ...   | refl = record
    { frame = jf; found = found; caller = caller; phase = GP.Pool.bodyUnwinding
    ; handle = trans (cong (lookup j) handles) (lookup-put j GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)))
    ; notRunning = λ () }
  unwinds q cf present | no other = record
    { frame = UnwindJob.frame backing; found = UnwindJob.found backing
    ; caller = UnwindJob.caller backing; phase = UnwindJob.phase backing
    ; handle = trans (cong (lookup q) handles)
        (trans (lookup-put-other j q GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)) other) (UnwindJob.handle backing))
    ; notRunning = UnwindJob.notRunning backing }
    where
    backing = Aux.unwindingJobs old q cf (trans (sym (lookup-put-other j q f (C.unwinding k) other)) present)

-- Both frame kinds are absent at the canceled caller before its handle write;
-- every surviving frame therefore belongs to a different worker.
cancel-inv : ∀ c k j jf err context {f d} p →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  Cancel.start (J.caller (Sub.execution jf)) err context c ≡ just (f , d) →
  GP.Pool.handles p ≡ put j GP.Pool.bodyUnwinding (GP.Pool.handles (C.governorPool k)) →
  Unique c → Inv c k → Inv d (cancel-context k j f p)
cancel-inv c k j jf err context {f} {d} p found started handles unique inv = owned-frames acq rel
  where
  w = J.caller (Sub.execution jf)
  clears = CancelFacts.start-clears w err context c started (acquireFrames unique) (releaseFrames unique)
  retained = start-inv w err context c started k unique inv
  acq : ∀ q → is-just (lookup q (O.acquiring d)) ≡ true →
    lookup q (O.acquired d) ≡ nothing × Owner q J.awaitAcquire (cancel-context k j f p)
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (proj₁ (proj₂ clears)))) present of λ ()
  ... | no apart = proj₁ (acquiring retained q present) ,
    cancel-owner k j jf f p found handles q J.awaitAcquire apart (proj₂ (acquiring retained q present))
  rel : ∀ q → is-just (lookup q (O.releasing d)) ≡ true →
    lookup q (O.released d) ≡ nothing × Owner q J.awaitRelease (cancel-context k j f p)
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (proj₂ (proj₂ clears)))) present of λ ()
  ... | no apart = proj₁ (releasing retained q present) ,
    cancel-owner k j jf f p found handles q J.awaitRelease apart (proj₂ (releasing retained q present))

-- Actual pool delivery changes exactly the selected running handle.
deliver-handles : ∀ p j {p′} → GP.Pool.phase p ≡ GP.Pool.cancelPending j →
  GP.Pool.step GP.Pool.deliverCancel p ≡ just p′ →
  GP.Pool.handles p′ ≡ put j GP.Pool.bodyUnwinding (GP.Pool.handles p)
deliver-handles p j phase stepped rewrite phase with lookup j (GP.Pool.handles p)
... | just GP.Pool.bodyRunning = case just-injective stepped of λ { refl → refl }
... | nothing = case stepped of λ ()
... | just GP.Pool.bodyUnwinding = case stepped of λ ()
... | just (GP.Pool.bodyReturned _) = case stepped of λ ()
... | just (GP.Pool.deregisterPending _) = case stepped of λ ()
... | just (GP.Pool.deregistered _) = case stepped of λ ()
... | just (GP.Pool.resultAvailable _) = case stepped of λ ()

-- The full predicate at a PS state is definitionally the K predicate after
-- source/context reassembly; it includes the same A and R clauses.
Held : PS.State → Set
Held s = Inv (PS.cm s) (C.capture s) × Unique (PS.cm s) × Aux (C.capture s)

-- Both ordinary and blocked-open cancellation deliveries preserve all clauses.
governor-delivery : ∀ blocked err s {g′} →
  GP.deliver blocked err (PS.governor s) ≡ just g′ → Held s → Held (record s { governor = g′ })
governor-delivery blocked err s stepped (inv , unique , aux) with GP.Pool.phase (GP.pool (PS.governor s)) in phase
... | GP.Pool.cancelPending j with lookup j (Sub.jobs (PS.machine s)) in found |
  GP.Pool.step GP.Pool.deliverCancel (GP.pool (PS.governor s)) in delivered
...   | just jf | just p′ with Cancel.start (J.caller (Sub.execution jf)) err
  (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) (PS.cm s) in started
...     | just (f , d) = case just-injective stepped of λ { refl →
  cancel-inv (PS.cm s) (C.capture s) j jf err (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) p′ found started handles unique inv ,
  U.start-unique (J.caller (Sub.execution jf)) err (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) (PS.cm s) started unique ,
  cancel-aux (C.capture s) j jf f p′ found
    (proj₁ (CancelFacts.start-clears (J.caller (Sub.execution jf)) err (GP.deliveryContext blocked (GP.region (J.caller (Sub.execution jf)) (PS.governor s))) (PS.cm s) started (acquireFrames unique) (releaseFrames unique))) handles aux }
  where
  handles = deliver-handles (GP.pool (PS.governor s)) j phase delivered
...     | nothing = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.cancelPending j | nothing | _ = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.cancelPending j | just jf | nothing = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.openPool = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.closing = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.closedPool = case stepped of λ ()
governor-delivery blocked err s stepped held | GP.Pool.joinPending j = case stepped of λ ()

-- PS permissions may delay delivery, but every successful ordinary delivery
-- still performs exactly the governor transition checked above.
ordinary-delivery : ∀ err s {t} → PS.step (PS.run (GP.deliverCancellation err)) s ≡ just t → Held s → Held t
ordinary-delivery err s stepped held with PS.governorAllowed (GP.deliverCancellation err) s
... | false = case stepped of λ ()
... | true with GP.deliver false err (PS.governor s) in delivered
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → governor-delivery false err s delivered held }

-- An explicit blocked-open observation uses the same detachment proof.
blocked-delivery : ∀ err s {t} → PS.step (PS.run (GP.deliverOpenCancellation err)) s ≡ just t → Held s → Held t
blocked-delivery err s stepped held with PS.governorAllowed (GP.deliverOpenCancellation err) s
... | false = case stepped of λ ()
... | true with GP.deliver true err (PS.governor s) in delivered
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → governor-delivery true err s delivered held }

import ConnectionManagement.Properties.OwnedFramesReach as FullReach
private module R = FullReach isBearerClosed isIOManagerError

-- The concrete ordinary-delivery K constructor preserves full Reach.
k-ordinary-delivery : ∀ err s {t} →
  K.step (K.peerStep (PS.run (GP.deliverCancellation err))) s ≡ just t → R.Reach s → R.Reach t
k-ordinary-delivery err s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.deliverCancellation err)) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.deliverCancellation err)) (K.peers s) in delivered
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → ordinary-delivery err (K.peers s) delivered held }

-- The concrete blocked-open-delivery K constructor is covered separately.
k-blocked-delivery : ∀ err s {t} →
  K.step (K.peerStep (PS.run (GP.deliverOpenCancellation err))) s ≡ just t → R.Reach s → R.Reach t
k-blocked-delivery err s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.deliverOpenCancellation err)) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.deliverOpenCancellation err)) (K.peers s) in delivered
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → blocked-delivery err (K.peers s) delivered held }
