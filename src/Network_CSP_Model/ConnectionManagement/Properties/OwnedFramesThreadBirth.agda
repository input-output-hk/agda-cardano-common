{-# OPTIONS --guardedness #-}

-- Fresh monitor birth preserves existing owners and all caller separation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesThreadBirth
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobBirth as Birth
import ConnectionManagement.Properties.OwnedFramesThreadBirthStores as Stores
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob; unowned-found)
private
  module B = Birth isBearerClosed isIOManagerError
  module S = Stores isIOManagerError

-- The logical thread table is written before composing its independent pool fork.
born-context : C.Context → ConnectionManagement.Domain.JobId → PS.Thread → C.Context
born-context k tid next = record k { monitors = put tid next (C.monitors k) }

-- Active old followups use neither the fresh handle nor its fresh peer identity.
born-follow : ∀ k tid next → PS.byPeer (PS.peerRef next) (C.monitors k) ≡ nothing →
  lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ nothing → ∀ ref f → FollowThread ref f k → FollowThread ref f (born-context k tid next)
born-follow k tid next peer-fresh fresh ref f old with FollowThread.tid old ≟ tid
... | yes refl = case trans (sym fresh) (FollowThread.running old) of λ ()
... | no apart = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = S.peer-put-other ref (C.monitors k) tid next (FollowThread.tid old) (FollowThread.thread old)
      (λ same → case trans (sym peer-fresh) (trans (cong (λ q → PS.byPeer q (C.monitors k)) same) (FollowThread.found old)) of λ ()) apart (FollowThread.found old)
  ; caller = FollowThread.caller old; running = FollowThread.running old; observing = FollowThread.observing old }

-- Other callers retain every owner alternative, with exact old thread rows.
born-owner : ∀ k tid next → PS.byPeer (PS.peerRef next) (C.monitors k) ≡ nothing →
  lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ nothing → ∀ w pc → w ≢ PS.worker next →
  Owner w pc k → Owner w pc (born-context k tid next)
born-owner k tid next peer-fresh fresh w pc apart (inj₁ foreign) = inj₁
  (proj₁ foreign , S.worker-put-none w (C.monitors k) tid next apart (proj₂ foreign))
born-owner k tid next peer-fresh fresh w pc apart (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old) (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
born-owner k tid next peer-fresh fresh w pc apart (inj₂ (inj₂ old)) with FollowAwait.tid old ≟ tid
... | yes refl = case trans (sym fresh) (FollowAwait.running old) of λ ()
... | no other = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old) (FollowAwait.caller old) (FollowAwait.waiting old)
    (FollowAwait.tid old) (FollowAwait.thread old)
    (S.peer-put-other (FollowAwait.ref old) (C.monitors k) tid next (FollowAwait.tid old) (FollowAwait.thread old)
      (λ same → case trans (sym peer-fresh) (trans (cong (λ q → PS.byPeer q (C.monitors k)) same) (FollowAwait.byPeer old)) of λ ()) other (FollowAwait.byPeer old))
    (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- No source frame exists at the freshly allocated monitor worker.
born-inv : ∀ c k tid next → B.Free (PS.worker next) c k → PS.byPeer (PS.peerRef next) (C.monitors k) ≡ nothing →
  lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ nothing → Inv c k → Inv c (born-context k tid next)
born-inv c k tid next free peer-fresh fresh inv = owned-frames acq rel
  where
  acq : ∀ w → is-just (lookup w (O.acquiring c)) ≡ true → lookup w (O.acquired c) ≡ nothing × Owner w J.awaitAcquire (born-context k tid next)
  acq w present with w ≟ PS.worker next
  ... | yes refl = case trans (sym (cong is-just (B.Free.acquiring free))) present of λ ()
  ... | no apart = proj₁ (acquiring inv w present) , born-owner k tid next peer-fresh fresh w J.awaitAcquire apart (proj₂ (acquiring inv w present))
  rel : ∀ w → is-just (lookup w (O.releasing c)) ≡ true → lookup w (O.released c) ≡ nothing × Owner w J.awaitRelease (born-context k tid next)
  rel w present with w ≟ PS.worker next
  ... | yes refl = case trans (sym (cong is-just (B.Free.releasing free))) present of λ ()
  ... | no apart = proj₁ (releasing inv w present) , born-owner k tid next peer-fresh fresh w J.awaitRelease apart (proj₂ (releasing inv w present))

-- Detached governor identities are independent of monitor allocation.
born-unwind : ∀ k tid next j f → UnwindJob j f k → UnwindJob j f (born-context k tid next)
born-unwind k tid next j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- New thread names are distinct from every old thread and historical job caller.
born-aux : ∀ c k tid next → B.Free (PS.worker next) c k → PS.byPeer (PS.peerRef next) (C.monitors k) ≡ nothing →
  lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ nothing → Aux k → Aux (born-context k tid next)
born-aux c k tid next free peer-fresh fresh old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = put-unique tid next rows (Aux.monitorKeys old)
  ; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old; jobCallers = Aux.jobCallers old; jobNotMonitor = disjoint
  ; threadWorkers = workers; threadPeers = peers
  ; followThreads = λ ref f found → born-follow k tid next peer-fresh fresh ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → born-unwind k tid next j f (Aux.unwindingJobs old j f found) }
  where
  rows = C.monitors k
  disjoint : ∀ j jf → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf → PS.byWorker (J.caller (Sub.execution jf)) (put tid next rows) ≡ nothing
  disjoint j jf found = S.worker-put-none (J.caller (Sub.execution jf)) rows tid next
    (unowned-found (PS.worker next) (C.SubContext.jobs (C.subsystem k)) j jf (B.Free.unowned free) found) (Aux.jobNotMonitor old j jf found)
  workers : ∀ uid u vid v → lookup uid (put tid next rows) ≡ just u → lookup vid (put tid next rows) ≡ just v → PS.worker u ≡ PS.worker v → uid ≡ vid
  workers uid u vid v found₁ found₂ same with uid ≟ tid | vid ≟ tid
  ... | yes refl | yes refl = refl
  ... | yes refl | no apart with just-injective (trans (sym (lookup-put tid next rows)) found₁)
  ...   | refl = ⊥-elim (S.worker-absent (PS.worker next) rows vid v (B.Free.unmonitored free)
    (trans (sym (lookup-put-other tid vid next rows apart)) found₂) (sym same))
  workers uid u vid v found₁ found₂ same | no apart | yes refl with just-injective (trans (sym (lookup-put tid next rows)) found₂)
  ... | refl = ⊥-elim (S.worker-absent (PS.worker next) rows uid u (B.Free.unmonitored free)
    (trans (sym (lookup-put-other tid uid next rows apart)) found₁) same)
  workers uid u vid v found₁ found₂ same | no apart₁ | no apart₂ = Aux.threadWorkers old uid u vid v
    (trans (sym (lookup-put-other tid uid next rows apart₁)) found₁) (trans (sym (lookup-put-other tid vid next rows apart₂)) found₂) same
  peers : ∀ uid u vid v → lookup uid (put tid next rows) ≡ just u → lookup vid (put tid next rows) ≡ just v → PS.peerRef u ≡ PS.peerRef v → uid ≡ vid
  peers uid u vid v found₁ found₂ same with uid ≟ tid | vid ≟ tid
  ... | yes refl | yes refl = refl
  ... | yes refl | no apart with just-injective (trans (sym (lookup-put tid next rows)) found₁)
  ...   | refl = ⊥-elim (S.peer-absent (PS.peerRef next) rows vid v peer-fresh
    (trans (sym (lookup-put-other tid vid next rows apart)) found₂) (sym same))
  peers uid u vid v found₁ found₂ same | no apart | yes refl with just-injective (trans (sym (lookup-put tid next rows)) found₂)
  ... | refl = ⊥-elim (S.peer-absent (PS.peerRef next) rows uid u peer-fresh
    (trans (sym (lookup-put-other tid uid next rows apart)) found₁) same)
  peers uid u vid v found₁ found₂ same | no apart₁ | no apart₂ = Aux.threadPeers old uid u vid v
    (trans (sym (lookup-put-other tid uid next rows apart₁)) found₁) (trans (sym (lookup-put-other tid vid next rows apart₂)) found₂) same
