{-# OPTIONS --guardedness #-}

-- Removing one followup transports every retained exact ownership witness.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesFollowDelete
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
open import ConnectionManagement.Store using (lookup; delete)
open import ConnectionManagement.Properties.Stores using (delete-unique)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)

-- Named logical-followup deletion, leaving all physical thread rows intact.
delete-context : C.Context → ConnectionManagement.Domain.PeerConnectionId → C.Context
delete-context k ref = record k { subsystem = record (C.subsystem k)
  { monitors = delete ref (C.SubContext.monitors (C.subsystem k)) } }

-- Only a witness for this exact deleted followup needs to be ruled out.
delete-owner : ∀ k ref w pc → (∀ (owner : FollowAwait w pc k) → FollowAwait.ref owner ≢ ref) →
  Owner w pc k → Owner w pc (delete-context k ref)
delete-owner k ref w pc cannot (inj₁ foreign) = inj₁ foreign
delete-owner k ref w pc cannot (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old) (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
delete-owner k ref w pc cannot (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old)
    (trans (delete-other ref (FollowAwait.ref old) (C.SubContext.monitors (C.subsystem k)) (cannot old)) (FollowAwait.found old))
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old) (FollowAwait.thread old)
    (FollowAwait.byPeer old) (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- Another caller cannot own the captured followup being detached.
caller-other : ∀ k ref f w → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f → J.caller f ≡ w →
  ∀ q pc → q ≢ w → (owner : FollowAwait q pc k) → FollowAwait.ref owner ≢ ref
caller-other k ref f w saved caller q pc apart owner refl with just-injective (trans (sym saved) (FollowAwait.found owner))
... | refl = apart (trans (sym (FollowAwait.caller owner)) caller)

-- Once cancellation removes both source frame kinds, deleting the matching
-- followup cannot remove the owner of any remaining source frame.
detach-inv : ∀ c k ref f w → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f → J.caller f ≡ w →
  lookup w (O.acquiring c) ≡ nothing → lookup w (O.releasing c) ≡ nothing → Inv c k → Inv c (delete-context k ref)
detach-inv c k ref f w saved caller acq-none rel-none inv = owned-frames acq rel
  where
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true → lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire (delete-context k ref)
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just acq-none)) present of λ ()
  ... | no apart = proj₁ (acquiring inv q present) , delete-owner k ref q J.awaitAcquire
    (caller-other k ref f w saved caller q J.awaitAcquire apart) (proj₂ (acquiring inv q present))
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true → lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease (delete-context k ref)
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just rel-none)) present of λ ()
  ... | no apart = proj₁ (releasing inv q present) , delete-owner k ref q J.awaitRelease
    (caller-other k ref f w saved caller q J.awaitRelease apart) (proj₂ (releasing inv q present))

-- A complete followup cannot also be a matching await owner of either kind.
complete-inv : ∀ c k ref f result → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.pc f ≡ J.complete result → Inv c k → Inv c (delete-context k ref)
complete-inv c k ref f result saved complete inv = owned-frames
  (λ w present → let old = acquiring inv w present in proj₁ old , delete-owner k ref w J.awaitAcquire (cannot w J.awaitAcquire (λ ())) (proj₂ old))
  (λ w present → let old = releasing inv w present in proj₁ old , delete-owner k ref w J.awaitRelease (cannot w J.awaitRelease (λ ())) (proj₂ old))
  where
  cannot : ∀ w pc → J.complete result ≢ pc → (owner : FollowAwait w pc k) → FollowAwait.ref owner ≢ ref
  cannot w pc different owner refl with just-injective (trans (sym saved) (FollowAwait.found owner))
  ... | refl = different (trans (sym complete) (FollowAwait.waiting owner))

-- Physical attachment does not inspect the logical followup table itself.
copy-follow : ∀ k ref q f → FollowThread q f k → FollowThread q f (delete-context k ref)
copy-follow k ref q f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old; found = FollowThread.found old
  ; caller = FollowThread.caller old; running = FollowThread.running old; observing = FollowThread.observing old }

-- Governor unwind backing is independent of logical followup deletion.
copy-unwind : ∀ k ref j f → UnwindJob j f k → UnwindJob j f (delete-context k ref)
copy-unwind k ref j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- The unique followup key is absent after deletion; all other keys retain F.
delete-aux : ∀ k ref → Aux k → Aux (delete-context k ref)
delete-aux k ref old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old
  ; followKeys = delete-unique ref (C.SubContext.monitors (C.subsystem k)) (Aux.followKeys old); unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = follows
  ; unwindingJobs = λ j f found → copy-unwind k ref j f (Aux.unwindingJobs old j f found) }
  where
  follows : ∀ q f → lookup q (delete ref (C.SubContext.monitors (C.subsystem k))) ≡ just f → FollowThread q f (delete-context k ref)
  follows q f found with q ≟ ref
  ... | yes refl = case trans (sym (delete-self ref (C.SubContext.monitors (C.subsystem k)) (Aux.followKeys old))) found of λ ()
  ... | no apart = copy-follow k ref q f (Aux.followThreads old q f
    (trans (sym (delete-other ref q (C.SubContext.monitors (C.subsystem k)) apart)) found))
