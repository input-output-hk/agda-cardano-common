{-# OPTIONS --guardedness #-}

-- Fresh caller allocation cannot steal an existing frame's owner. Historical
-- job identities are also protected by the physical pool's fresh-handle guard.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesJobBirth
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
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
import ConnectionManagement.State as Shared
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobNames as Names
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob; unowned-found)
private module N = Names isBearerClosed isIOManagerError

-- The four facts needed at a new job/monitor caller's allocation boundary.
record Free (w : ConnectionManagement.Domain.WorkerId) (c : O.Configuration) (k : C.Context) : Set where
  field
    unowned : GP.unowned w (C.SubContext.jobs (C.subsystem k)) ≡ true
    unmonitored : PS.byWorker w (C.monitors k) ≡ nothing
    acquiring : lookup w (O.acquiring c) ≡ nothing
    releasing : lookup w (O.releasing c) ≡ nothing

-- A distinct caller at the head preserves a structurally unowned tail.
unowned-cons : ∀ w j next rows → w ≢ J.caller (Sub.execution next) → GP.unowned w rows ≡ true →
  GP.unowned w ((j , next) ∷ rows) ≡ true
unowned-cons w j next rows apart free with w ≟ J.caller (Sub.execution next)
... | yes same = ⊥-elim (apart same)
... | no different = free

-- Adding a different caller preserves the structural unowned traversal.
unowned-put : ∀ w rows j next → w ≢ J.caller (Sub.execution next) → GP.unowned w rows ≡ true →
  GP.unowned w (put j next rows) ≡ true
unowned-put w [] j next apart free = unowned-cons w j next [] apart refl
unowned-put w ((uid , old) ∷ rows) j next apart free with w ≟ J.caller (Sub.execution old)
... | yes same = case free of λ ()
... | no other with j ≟ uid
...   | yes same = unowned-cons w j next rows apart free
...   | no different = unowned-cons w uid old (put j next rows) other (unowned-put w rows j next apart free)

-- Every existing owner at another caller survives the new logical job row.
born-owner : ∀ k j next → lookup j (GP.Pool.handles (C.governorPool k)) ≡ nothing →
  ∀ w pc → w ≢ J.caller (Sub.execution next) → Owner w pc k →
  Owner w pc (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
born-owner k j next fresh w pc apart (inj₁ foreign) = inj₁
  (unowned-put w (C.SubContext.jobs (C.subsystem k)) j next apart (proj₁ foreign) , proj₂ foreign)
born-owner k j next fresh w pc apart (inj₂ (inj₁ old)) with JobAwait.job old ≟ j
... | yes refl = case trans (sym fresh) (JobAwait.running old) of λ ()
... | no other = inj₂ (inj₁ (job-await (JobAwait.job old) (JobAwait.frame old)
  (trans (lookup-put-other j (JobAwait.job old) next (C.SubContext.jobs (C.subsystem k)) other) (JobAwait.found old))
  (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
born-owner k j next fresh w pc apart (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old)
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old) (FollowAwait.thread old)
    (FollowAwait.byPeer old) (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- No pre-existing source frame belongs to the freshly allocated caller.
born-inv : ∀ c k j next → Free (J.caller (Sub.execution next)) c k →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ nothing → Inv c k →
  Inv c (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
born-inv c k j next free fresh inv = owned-frames acq rel
  where
  w = J.caller (Sub.execution next)
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true → lookup q (O.acquired c) ≡ nothing ×
    Owner q J.awaitAcquire (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (Free.acquiring free))) present of λ ()
  ... | no apart = proj₁ (acquiring inv q present) , born-owner k j next fresh q J.awaitAcquire apart (proj₂ (acquiring inv q present))
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true → lookup q (O.released c) ≡ nothing ×
    Owner q J.awaitRelease (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (Free.releasing free))) present of λ ()
  ... | no apart = proj₁ (releasing inv q present) , born-owner k j next fresh q J.awaitRelease apart (proj₂ (releasing inv q present))

-- Caller uniqueness and job/monitor separation extend to the fresh job.
born-aux : ∀ c k j next → Free (J.caller (Sub.execution next)) c k →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ nothing → Aux k →
  Aux (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
born-aux c k j next free fresh old = record
  { jobKeys = put-unique j next rows (Aux.jobKeys old); monitorKeys = Aux.monitorKeys old
  ; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old; jobCallers = callers; jobNotMonitor = disjoint
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → N.job-follow k (put j next rows) ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = unwinds }
  where
  rows = C.SubContext.jobs (C.subsystem k)
  w = J.caller (Sub.execution next)
  callers : ∀ uid u vid v → lookup uid (put j next rows) ≡ just u → lookup vid (put j next rows) ≡ just v →
    J.caller (Sub.execution u) ≡ J.caller (Sub.execution v) → uid ≡ vid
  callers uid u vid v found₁ found₂ same with uid ≟ j | vid ≟ j
  ... | yes refl | yes refl = refl
  ... | yes refl | no apart with just-injective (trans (sym (lookup-put j next rows)) found₁)
  ...   | refl = ⊥-elim (unowned-found w rows vid v (Free.unowned free)
    (trans (sym (lookup-put-other j vid next rows apart)) found₂) (sym same))
  callers uid u vid v found₁ found₂ same | no apart | yes refl with just-injective (trans (sym (lookup-put j next rows)) found₂)
  ... | refl = ⊥-elim (unowned-found w rows uid u (Free.unowned free)
    (trans (sym (lookup-put-other j uid next rows apart)) found₁) same)
  callers uid u vid v found₁ found₂ same | no apart₁ | no apart₂ = Aux.jobCallers old uid u vid v
    (trans (sym (lookup-put-other j uid next rows apart₁)) found₁)
    (trans (sym (lookup-put-other j vid next rows apart₂)) found₂) same
  disjoint : ∀ uid u → lookup uid (put j next rows) ≡ just u → PS.byWorker (J.caller (Sub.execution u)) (C.monitors k) ≡ nothing
  disjoint uid u found with uid ≟ j
  ... | yes refl with just-injective (trans (sym (lookup-put j next rows)) found)
  ...   | refl = Free.unmonitored free
  disjoint uid u found | no apart = Aux.jobNotMonitor old uid u (trans (sym (lookup-put-other j uid next rows apart)) found)
  unwinds : ∀ uid f → lookup uid (C.unwinding k) ≡ just f → UnwindJob uid f (N.job-context k (put j next rows))
  unwinds uid f found with uid ≟ j
  ... | yes refl = case trans (sym fresh) (UnwindJob.handle backing) of λ ()
    where backing = Aux.unwindingJobs old j f found
  ... | no apart = record
    { frame = UnwindJob.frame backing
    ; found = trans (lookup-put-other j uid next rows apart) (UnwindJob.found backing)
    ; caller = UnwindJob.caller backing; phase = UnwindJob.phase backing
    ; handle = UnwindJob.handle backing; notRunning = UnwindJob.notRunning backing }
    where backing = Aux.unwindingJobs old uid f found

-- The child component of freshWorker is stronger than caller unownership.
job-worker-unowned : ∀ w rows → PS.jobWorkerFree w rows ≡ true → GP.unowned w rows ≡ true
job-worker-unowned w [] free = refl
job-worker-unowned w ((j , jf) ∷ rows) free with w ≟ J.caller (Sub.execution jf) | w ≟ J.child (Sub.execution jf)
... | no apart | no other = job-worker-unowned w rows free
... | yes same | child = case free of λ ()
... | no apart | yes same = case free of λ ()

-- Every real freshWorker guard supplies the complete Free certificate.
fresh-worker : ∀ w s → PS.freshWorker w s ≡ true → Free w (PS.cm s) (C.capture s)
fresh-worker w s permit with PS.byWorker w (PS.monitors s) in worker |
  lookup w (Shared.admissions (PS.shared s)) | lookup w (Shared.handlers (PS.shared s)) | lookup w (Shared.cleanups (PS.shared s)) |
  lookup w (O.acquiring (PS.cm s)) in acq | lookup w (O.releasing (PS.cm s)) in rel
... | nothing | nothing | nothing | nothing | nothing | nothing = record
  { unowned = job-worker-unowned w (Sub.jobs (PS.machine s)) permit
  ; unmonitored = worker; acquiring = acq; releasing = rel }
... | just t | admission | handler | cleanup | acquire | release = case permit of λ ()
... | nothing | just a | handler | cleanup | acquire | release = case permit of λ ()
... | nothing | nothing | just h | cleanup | acquire | release = case permit of λ ()
... | nothing | nothing | nothing | just u | acquire | release = case permit of λ ()
... | nothing | nothing | nothing | nothing | just a | release = case permit of λ ()
... | nothing | nothing | nothing | nothing | nothing | just r = case permit of λ ()
