{-# OPTIONS --guardedness #-}

-- Metadata supporting frame ownership. Unwinding absence is derived from
-- ownership and caller separation, rather than assumed as a source clause.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesAux
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; JobId; PeerConnectionId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Stores using (UniqueKeys)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.OwnedFrames as Frames
open Frames isBearerClosed isIOManagerError

-- Every active followup is still attached to its observing, running thread.
record FollowThread (ref : PeerConnectionId) (f : J.Frame) (k : C.Context) : Set where
  field
    tid : JobId
    thread : PS.Thread
    found : PS.byPeer ref (C.monitors k) ≡ just (tid , thread)
    caller : J.caller f ≡ PS.worker thread
    running : lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ just PS.Pool.bodyRunning
    observing : PS.pc thread ≡ PS.observing

-- The caller/handle identity of each detached governor continuation survives.
record UnwindJob (j : JobId) (f : Cancel.Frame) (k : C.Context) : Set where
  field
    frame : Sub.JobFrame
    found : lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just frame
    caller : Cancel.caller f ≡ J.caller (Sub.execution frame)
    phase : GP.Pool.ThreadPhase
    handle : lookup j (GP.Pool.handles (C.governorPool k)) ≡ just phase
    notRunning : phase ≢ GP.Pool.bodyRunning

-- All identity constraints are stated on the real stores and lookup functions.
record Aux (k : C.Context) : Set where
  field
    jobKeys : UniqueKeys (C.SubContext.jobs (C.subsystem k))
    monitorKeys : UniqueKeys (C.monitors k)
    followKeys : UniqueKeys (C.SubContext.monitors (C.subsystem k))
    unwindKeys : UniqueKeys (C.unwinding k)
    jobCallers : ∀ j jf q qf →
      lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
      lookup q (C.SubContext.jobs (C.subsystem k)) ≡ just qf →
      J.caller (Sub.execution jf) ≡ J.caller (Sub.execution qf) → j ≡ q
    jobNotMonitor : ∀ j jf → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
      PS.byWorker (J.caller (Sub.execution jf)) (C.monitors k) ≡ nothing
    threadWorkers : ∀ tid t uid u → lookup tid (C.monitors k) ≡ just t →
      lookup uid (C.monitors k) ≡ just u → PS.worker t ≡ PS.worker u → tid ≡ uid
    threadPeers : ∀ tid t uid u → lookup tid (C.monitors k) ≡ just t →
      lookup uid (C.monitors k) ≡ just u → PS.peerRef t ≡ PS.peerRef u → tid ≡ uid
    followThreads : ∀ ref f → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f → FollowThread ref f k
    unwindingJobs : ∀ j f → lookup j (C.unwinding k) ≡ just f → UnwindJob j f k

-- Initial peer tables are empty, independently of the supplied CM and governor.
aux-initial : ∀ c g → Aux (C.capture (PS.initial c g))
aux-initial c g = record
  { jobKeys = []; monitorKeys = []; followKeys = []; unwindKeys = []
  ; jobCallers = λ j jf q qf ()
  ; jobNotMonitor = λ j jf ()
  ; threadWorkers = λ tid t uid u ()
  ; threadPeers = λ tid t uid u ()
  ; followThreads = λ ref f ()
  ; unwindingJobs = λ j f () }

-- A foreign caller cannot be the caller of any looked-up job, even without
-- table uniqueness: unowned traverses every association-store row.
unowned-found : ∀ w rows j jf → GP.unowned w rows ≡ true → lookup j rows ≡ just jf →
  J.caller (Sub.execution jf) ≢ w
unowned-found w [] j jf free ()
unowned-found w ((q , old) ∷ rows) j jf free found with w ≟ J.caller (Sub.execution old)
... | yes same = case free of λ ()
... | no apart with j ≟ q
...   | yes same = case just-injective found of λ { refl → λ eq → apart (sym eq) }
...   | no other = unowned-found w rows j jf free found

-- A byPeer witness's worker is visible to byWorker, including when other
-- threads occur earlier in the association list.
peer-worker-absent : ∀ w ref rows tid t → PS.byWorker w rows ≡ nothing →
  PS.byPeer ref rows ≡ just (tid , t) → PS.worker t ≢ w
peer-worker-absent w ref [] tid t absent ()
peer-worker-absent w ref ((uid , u) ∷ rows) tid t absent found with w ≟ PS.worker u
... | yes same = case absent of λ ()
... | no apart with ref ≟ PS.peerRef u
...   | yes same = case just-injective found of λ { refl → λ eq → apart (sym eq) }
...   | no other = peer-worker-absent w ref rows tid t absent found

-- A non-running job cannot have any of the three ownership alternatives.
not-running-owner : ∀ k → Aux k → ∀ j jf pc →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  lookup j (GP.Pool.handles (C.governorPool k)) ≢ just GP.Pool.bodyRunning →
  Owner (J.caller (Sub.execution jf)) pc k → ⊥
not-running-owner k aux j jf pc found stopped (inj₁ foreign) =
  unowned-found (J.caller (Sub.execution jf)) (C.SubContext.jobs (C.subsystem k)) j jf (proj₁ foreign) found refl
not-running-owner k aux j jf pc found stopped (inj₂ (inj₁ owner)) with
  Aux.jobCallers aux (JobAwait.job owner) (JobAwait.frame owner) j jf
    (JobAwait.found owner) found (JobAwait.caller owner)
... | refl = stopped (JobAwait.running owner)
not-running-owner k aux j jf pc found stopped (inj₂ (inj₂ owner)) =
  peer-worker-absent (J.caller (Sub.execution jf)) (FollowAwait.ref owner) (C.monitors k) (FollowAwait.tid owner) (FollowAwait.thread owner)
    (Aux.jobNotMonitor aux j jf found) (FollowAwait.byPeer owner) (FollowAwait.worker owner)

-- A/R thus entail the proposed Unw clause once detached identity and the
-- actual non-running handle have been maintained by the metadata invariant.
unwinding-no-frames : ∀ c k → Inv c k → Aux k → ∀ j f → lookup j (C.unwinding k) ≡ just f →
  lookup (Cancel.caller f) (O.acquiring c) ≡ nothing ×
  lookup (Cancel.caller f) (O.releasing c) ≡ nothing
unwinding-no-frames c k inv aux j f found with Aux.unwindingJobs aux j f found
... | backing = no-acquire , no-release
  where
  stopped : lookup j (GP.Pool.handles (C.governorPool k)) ≢ just GP.Pool.bodyRunning
  stopped running = UnwindJob.notRunning backing
    (just-injective (trans (sym (UnwindJob.handle backing)) running))
  impossible : ∀ pc → Owner (Cancel.caller f) pc k → ⊥
  impossible pc owner = not-running-owner k aux j (UnwindJob.frame backing) pc
    (UnwindJob.found backing) stopped
    (subst (λ w → Owner w pc k) (UnwindJob.caller backing) owner)
  no-acquire : lookup (Cancel.caller f) (O.acquiring c) ≡ nothing
  no-acquire with lookup (Cancel.caller f) (O.acquiring c) in present
  ... | nothing = refl
  ... | just active = ⊥-elim (impossible J.awaitAcquire
    (proj₂ (acquiring inv (Cancel.caller f) (cong is-just present))))
  no-release : lookup (Cancel.caller f) (O.releasing c) ≡ nothing
  no-release with lookup (Cancel.caller f) (O.releasing c) in present
  ... | nothing = refl
  ... | just active = ⊥-elim (impossible J.awaitRelease
    (proj₂ (releasing inv (Cancel.caller f) (cong is-just present))))
