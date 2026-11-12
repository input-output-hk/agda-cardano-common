{-# OPTIONS --guardedness #-}

-- The extra invariant is orthogonal to Reach: present frames cannot be foreign.
-- Existing Reach supplies the precise active owners at allocation boundaries.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersBase
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; JobId)
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.OutboundKeys using
  (KeySame; acquiringKeys; releasingKeys; Unique; acquireFrames; releaseFrames; keyChanging; nonkey)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as AuxFacts
import ConnectionManagement.Properties.OwnedFramesJobNames as NamesFacts
import ConnectionManagement.Properties.OwnedFramesThreads as ThreadFacts
open Frames isBearerClosed isIOManagerError public using (module K; module PS; module GP; module C; Foreign)
open Frames isBearerClosed isIOManagerError using (Inv; Owned; Owner; acquiring; releasing; JobAwait; FollowAwait)
private
  module X = AuxFacts isBearerClosed isIOManagerError
  module Names = NamesFacts isBearerClosed isIOManagerError
  module Threads = ThreadFacts isIOManagerError

-- The union records only presence, independently of continuation payloads.
Present : WorkerId → O.Configuration → Set
Present w c = is-just (lookup w (O.acquiring c)) ≡ true ⊎ is-just (lookup w (O.releasing c)) ≡ true

-- No frame's worker is foreign to the historical owner tables.
NoForeign : O.Configuration → C.Context → Set
NoForeign c k = ∀ w → Present w c → Foreign w k → ⊥

-- This is the extra shared-state invariant, alongside the unchanged Reach.
NF : K.State → Set
NF s = NoForeign (K.source s) (K.context s)

-- The same observations on a peer state permit small component proofs.
PeerNF : PS.State → Set
PeerNF s = NoForeign (PS.cm s) (C.capture s)

-- Empty initialization needs no assumption on either owner table.
empty : ∀ c k → NoForeign (O.initial c) k
empty c k w (inj₁ ()) foreign
empty c k w (inj₂ ()) foreign

-- A source change retaining caller key sets transports the extra invariant.
same-source : ∀ {c d k} → KeySame c d → NoForeign c k → NoForeign d k
same-source same held w (inj₁ p) = held w (inj₁ (trans (sym (acquiringKeys same w)) p))
same-source same held w (inj₂ p) = held w (inj₂ (trans (sym (releasingKeys same w)) p))

-- Only the two ownership observations are needed for context transport.
context : ∀ c k l →
  (∀ w → Foreign w l → Foreign w k) → NoForeign c k → NoForeign c l
context c k l back held w present foreign = held w present (back w foreign)

-- Continuation updates retain the exact job caller partition.
job-update : ∀ c k j old next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) → NoForeign c k →
  NoForeign c (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
job-update c k j old next found caller = context c k (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k)))) λ w foreign →
  trans (sym (Names.unowned-put w j old next (C.SubContext.jobs (C.subsystem k)) found caller)) (proj₁ foreign) , proj₂ foreign

-- Inserting an absent association cannot make an old job caller unowned.
job-insert-back : ∀ w rows j next → lookup j rows ≡ nothing → GP.unowned w (put j next rows) ≡ true → GP.unowned w rows ≡ true
job-insert-back w [] j next absent foreign = refl
job-insert-back w ((uid , old) ∷ rows) j next absent foreign with j ≟ uid
... | yes _ = case absent of λ ()
... | no _ with w ≟ J.caller (Sub.execution old)
...   | yes _ = case foreign of λ ()
...   | no _ = job-insert-back w rows j next absent foreign

-- Presence selects the existing exact active-owner theorem.
frame-owner : ∀ c k → Inv c k → ∀ w → Present w c → Owner w J.awaitAcquire k ⊎ Owner w J.awaitRelease k
frame-owner c k inv w (inj₁ p) = inj₁ (proj₂ (acquiring inv w p))
frame-owner c k inv w (inj₂ p) = inj₂ (proj₂ (releasing inv w p))

-- Either kind of present frame admits a caller-polymorphic owner consumer.
consume-owner : ∀ {c k w} {B : Set} → Inv c k → Present w c → (∀ pc → Owner w pc k → B) → B
consume-owner inv (inj₁ p) use = use J.awaitAcquire (proj₂ (acquiring inv _ p))
consume-owner inv (inj₂ p) use = use J.awaitRelease (proj₂ (releasing inv _ p))

-- New allocation cannot steal an active frame owner: its physical handle was
-- absent, whereas Reach's job owner requires bodyRunning at that same identity.
job-birth : ∀ c k j next → lookup j (GP.Pool.handles (C.governorPool k)) ≡ nothing →
  Inv c k → NoForeign c k →
  NoForeign c (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
job-birth c k j next fresh inv held w present foreign = consume-owner inv present proof
  where
  -- Consume the existing active owner at this writer boundary.
  proof : ∀ pc → Owner w pc k → ⊥
  proof pc (inj₁ old) = held w present old
  proof pc (inj₂ (inj₁ job)) with JobAwait.job job ≟ j
  ... | yes refl = case trans (sym fresh) (JobAwait.running job) of λ ()
  ... | no apart = X.unowned-found w (put j next (C.SubContext.jobs (C.subsystem k))) (JobAwait.job job) (JobAwait.frame job) (proj₁ foreign)
    (trans (lookup-put-other j (JobAwait.job job) next (C.SubContext.jobs (C.subsystem k)) apart) (JobAwait.found job)) (JobAwait.caller job)
  proof pc (inj₂ (inj₂ follow)) = X.peer-worker-absent w (FollowAwait.ref follow) (C.monitors k)
    (FollowAwait.tid follow) (FollowAwait.thread follow) (proj₂ foreign) (FollowAwait.byPeer follow) (FollowAwait.worker follow)

-- Thread replacement keeps the worker of the overwritten historical binding.
thread-back : ∀ w rows tid old next → lookup tid rows ≡ just old → PS.worker next ≡ PS.worker old →
  PS.byWorker w (put tid next rows) ≡ nothing → PS.byWorker w rows ≡ nothing
thread-back w [] tid old next () worker foreign
thread-back w ((uid , t) ∷ rows) tid old next saved worker foreign with tid ≟ uid
... | yes refl with just-injective saved
...   | refl with w ≟ PS.worker next | w ≟ PS.worker old
...     | yes _ | _ = case foreign of λ ()
...     | no apart | yes same = ⊥-elim (apart (trans same (sym worker)))
...     | no _ | no _ = foreign
thread-back w ((uid , t) ∷ rows) tid old next saved worker foreign | no _ with w ≟ PS.worker t
... | yes _ = case foreign of λ ()
... | no _ = thread-back w rows tid old next saved worker foreign

-- Any source-preserving immutable-worker thread update preserves NoForeign.
thread-update : ∀ c k tid old next → lookup tid (C.monitors k) ≡ just old → PS.worker next ≡ PS.worker old →
  NoForeign c k → NoForeign c (record k { monitors = put tid next (C.monitors k) })
thread-update c k tid old next saved worker = context c k (record k { monitors = put tid next (C.monitors k) }) λ w foreign →
  proj₁ foreign , thread-back w (C.monitors k) tid old next saved worker (proj₂ foreign)

-- New thread insertion is handled by active monitor identity, just like jobs.
thread-birth : ∀ c k tid next → lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ nothing →
  Inv c k → X.Aux k → NoForeign c k → NoForeign c (record k { monitors = put tid next (C.monitors k) })
thread-birth c k tid next fresh inv aux held w present foreign = consume-owner inv present proof
  where
  -- A captured thread visible by key cannot be invisible by worker.
  absent-worker : ∀ w rows uid t → PS.byWorker w rows ≡ nothing → lookup uid rows ≡ just t → PS.worker t ≢ w
  absent-worker w [] uid t absent ()
  absent-worker w ((vid , v) ∷ rows) uid t absent found with w ≟ PS.worker v
  ... | yes _ = case absent of λ ()
  ... | no apart with uid ≟ vid
  ...   | yes _ = case just-injective found of λ { refl → λ same → apart (sym same) }
  ...   | no _ = absent-worker w rows uid t absent found
  -- Consume the existing active owner at this writer boundary.
  proof : ∀ pc → Owner w pc k → ⊥
  proof pc (inj₁ old) = held w present old
  proof pc (inj₂ (inj₁ job)) = X.unowned-found w (C.SubContext.jobs (C.subsystem k)) (JobAwait.job job) (JobAwait.frame job)
    (proj₁ foreign) (JobAwait.found job) (JobAwait.caller job)
  proof pc (inj₂ (inj₂ follow)) with FollowAwait.tid follow ≟ tid
  ... | yes refl = case trans (sym fresh) (FollowAwait.running follow) of λ ()
  ... | no apart = absent-worker w (put tid next (C.monitors k)) (FollowAwait.tid follow) (FollowAwait.thread follow) (proj₂ foreign)
    (trans (lookup-put-other tid (FollowAwait.tid follow) next (C.monitors k) apart)
      (Threads.byPeer-lookup (FollowAwait.ref follow) (C.monitors k) (X.Aux.monitorKeys aux) (FollowAwait.tid follow) (FollowAwait.thread follow) (FollowAwait.byPeer follow)))
    (FollowAwait.worker follow)

-- Absence in a store survives deletion, even when association keys repeat.
delete-empty : ∀ {V : Set} w q (rows : Store WorkerId V) → lookup w rows ≡ nothing → lookup w (delete q rows) ≡ nothing
delete-empty w q [] empty = refl
delete-empty w q ((uid , v) ∷ rows) empty with q ≟ uid
... | yes refl with w ≟ q
...   | yes _ = case empty of λ ()
...   | no _ = empty
delete-empty w q ((uid , v) ∷ rows) empty | no _ with w ≟ uid
... | yes _ = case empty of λ ()
... | no _ = delete-empty w q rows empty

-- A Boolean empty lookup is equivalent to the requested lookup equality.
empty-lookup : ∀ {V : Set} {x : Maybe V} → is-just x ≡ false → x ≡ nothing
empty-lookup {x = nothing} eq = refl
empty-lookup {x = just _} ()

-- No presence at a worker supplies both exact absence equalities.
not-present : ∀ c w → (Present w c → ⊥) → lookup w (O.acquiring c) ≡ nothing × lookup w (O.releasing c) ≡ nothing
not-present c w absent with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = refl , refl
... | just _ | _ = ⊥-elim (absent (inj₁ refl))
... | nothing | just _ = ⊥-elim (absent (inj₂ refl))

-- Conversely exact empty fields contradict frame presence.
no-present : ∀ c w → lookup w (O.acquiring c) ≡ nothing → lookup w (O.releasing c) ≡ nothing → Present w c → ⊥
no-present c w acq rel (inj₁ p) = case trans (sym (cong is-just acq)) p of λ ()
no-present c w acq rel (inj₂ p) = case trans (sym (cong is-just rel)) p of λ ()

-- Key-set preservation transports exact empty lookups without payload equality.
keep-empty : ∀ {c d} → KeySame c d → ∀ w → lookup w (O.acquiring c) ≡ nothing → lookup w (O.releasing c) ≡ nothing →
  lookup w (O.acquiring d) ≡ nothing × lookup w (O.releasing d) ≡ nothing
keep-empty {c} {d} same w acq rel = not-present d w λ
  { (inj₁ p) → no-present c w acq rel (inj₁ (trans (sym (acquiringKeys same w)) p))
  ; (inj₂ p) → no-present c w acq rel (inj₂ (trans (sym (releasingKeys same w)) p)) }

-- A primitive call initializer keeps every other worker's empty frames.
begin-other : ∀ a c {d} w →
  (∀ q req → a ≡ O.beginAcquire q req → w ≢ q) →
  (∀ q key → a ≡ O.beginRelease q key → w ≢ q) →
  keyChanging a ≡ true → O.advance a c ≡ just d → lookup w (O.acquiring c) ≡ nothing → lookup w (O.releasing c) ≡ nothing →
  lookup w (O.acquiring d) ≡ nothing × lookup w (O.releasing d) ≡ nothing
begin-other (O.beginAcquire q req) c w acq rel changing eq absentA absentR with lookup q (O.acquiring c) | lookup q (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → trans (lookup-put-other q w (A.frame req A.selecting) (O.acquiring c) (acq q req refl)) absentA , absentR }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
begin-other (O.beginRelease q key) c w acq rel changing eq absentA absentR with lookup q (O.acquiring c) | lookup q (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → absentA , trans (lookup-put-other q w (R.frame key R.transaction false) (O.releasing c) (rel q key refl)) absentR }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()

begin-other (O.acquire q A.returnResult) c w acq rel changing eq absentA absentR with lookup q (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = case just-injective eq of λ { refl → delete-empty w q (O.acquiring c) absentA , absentR }
...   | A.selecting = case eq of λ ()
...   | (A.count p) = case eq of λ ()
...   | (A.allocatePromise e) = case eq of λ ()
...   | (A.openSocket e p) = case eq of λ ()
...   | (A.configureSocket e p) = case eq of λ ()
...   | (A.bindSocket e p) = case eq of λ ()
...   | (A.connectSocket e p) = case eq of λ ()
...   | (A.localAddress e p) = case eq of λ ()
...   | (A.updateAddress e p key) = case eq of λ ()
...   | (A.forkHandler e p key) = case eq of λ ()
...   | (A.connectedCommit e p key) = case eq of λ ()
...   | (A.awaitResult e p key) = case eq of λ ()
...   | (A.commitResult e key result) = case eq of λ ()
...   | (A.waitingInbound e key) = case eq of λ ()
...   | (A.closeError e err) = case eq of λ ()
...   | (A.removeError e err) = case eq of λ ()

begin-other (O.release q R.returnResult) c w acq rel changing eq absentA absentR with lookup q (O.releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = case just-injective eq of λ { refl → absentA , delete-empty w q (O.releasing c) absentR }
...   | R.transaction = case eq of λ ()
...   | (R.check b next) = case eq of λ ()
...   | (R.count next) = case eq of λ ()
...   | (R.armTimer e w) = case eq of λ ()
...   | (R.waitIdle e w) = case eq of λ ()
...   | (R.timeoutWrite e w) = case eq of λ ()
...   | (R.cancel w next) = case eq of λ ()
...   | (R.delivering w next) = case eq of λ ()
...   | (R.prune choices result) = case eq of λ ()
begin-other (O.inbound _) c w acq rel () eq absentA absentR
begin-other (O.acquire q (A.select e)) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.readCounters) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.newPromise) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.openOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.configureOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.bindOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.connectOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q (A.gotLocal p)) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.updateLocalAddress) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.forkOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.commitConnected) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.readResult) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.commitHandshake) c w acq rel () eq absentA absentR
begin-other (O.acquire q (A.failIO e)) c w acq rel () eq absentA absentR
begin-other (O.acquire q (A.closeFailed e)) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.closeOK) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.removeReservation) c w acq rel () eq absentA absentR
begin-other (O.acquire q A.waitNegotiated) c w acq rel () eq absentA absentR
begin-other (O.release q R.transactionStep) c w acq rel () eq absentA absentR
begin-other (O.release q R.checkAssertion) c w acq rel () eq absentA absentR
begin-other (O.release q R.readCounters) c w acq rel () eq absentA absentR
begin-other (O.release q R.registerTimer) c w acq rel () eq absentA absentR
begin-other (O.release q R.expireTimer) c w acq rel () eq absentA absentR
begin-other (O.release q R.selectWakeup) c w acq rel () eq absentA absentR
begin-other (O.release q R.commitTimeout) c w acq rel () eq absentA absentR
begin-other (O.release q R.requestCancellation) c w acq rel () eq absentA absentR
begin-other (O.release q (R.transactionPruning choices)) c w acq rel () eq absentA absentR
begin-other (O.release q (R.cancellationDelivered target)) c w acq rel () eq absentA absentR

-- The general primitive source lemma excludes begins only at the observed worker.
primitive-empty : ∀ a c {d} w →
  (∀ q req → a ≡ O.beginAcquire q req → w ≢ q) →
  (∀ q key → a ≡ O.beginRelease q key → w ≢ q) →
  O.advance a c ≡ just d → lookup w (O.acquiring c) ≡ nothing → lookup w (O.releasing c) ≡ nothing →
  lookup w (O.acquiring d) ≡ nothing × lookup w (O.releasing d) ≡ nothing
primitive-empty a c w acq rel eq absentA absentR with keyChanging a in changing
... | true = begin-other a c w acq rel changing eq absentA absentR
... | false = keep-empty (nonkey a c changing eq) w absentA absentR

-- Irrelevant peer/pool/scope fields may change without affecting this invariant.
copy-peer : ∀ s t → KeySame (PS.cm s) (PS.cm t) →
  Sub.jobs (PS.machine t) ≡ Sub.jobs (PS.machine s) → PS.monitors t ≡ PS.monitors s → PeerNF s → PeerNF t
copy-peer s t keys rows threads held = context (PS.cm t) (C.capture s) (C.capture t)
  (λ w foreign → trans (sym (cong (GP.unowned w) rows)) (proj₁ foreign) ,
    trans (sym (cong (PS.byWorker w) threads)) (proj₂ foreign)) (same-source {k = C.capture s} keys held)
