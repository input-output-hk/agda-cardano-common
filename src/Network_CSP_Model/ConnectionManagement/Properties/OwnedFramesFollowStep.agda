{-# OPTIONS --guardedness #-}

-- Logical monitor-followup steps retain their physical observing-thread owner.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesFollowStep
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
open import ConnectionManagement.Properties.OutboundKeys using
  (Unique; KeySame; acquiringKeys; releasingKeys; acquiredSame; releasedSame; uniqueSame; advance-unique)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesAwait as AwaitFacts
import ConnectionManagement.Properties.OwnedFramesIdentity as Identity
import ConnectionManagement.Properties.OwnedFramesJobSource as Source
import ConnectionManagement.Properties.OwnedFramesBegin as Begin
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)
private
  module Waiting = AwaitFacts isBearerClosed isIOManagerError
  module B = Begin isBearerClosed isIOManagerError

-- Named writer for the sole logical followup frame.
follow-context : C.Context → ConnectionManagement.Domain.PeerConnectionId → J.Frame → C.Context
follow-context k ref f = record k { subsystem = record (C.subsystem k)
  { monitors = put ref f (C.SubContext.monitors (C.subsystem k)) } }

-- Followup-table replacement does not affect thread attachment itself.
copy-follow : ∀ k ref next q f → FollowThread q f k → FollowThread q f (follow-context k ref next)
copy-follow k ref next q f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- Unwind backing uses jobs and handles, independent of followup-table entries.
copy-unwind : ∀ k ref next j f → UnwindJob j f k → UnwindJob j f (follow-context k ref next)
copy-unwind k ref next j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- A caller-preserving followup write maintains the entire metadata invariant.
follow-aux : ∀ k ref f next → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.caller next ≡ J.caller f → Aux k → Aux (follow-context k ref next)
follow-aux k ref f next found caller old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old
  ; followKeys = put-unique ref next _ (Aux.followKeys old); unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = follows
  ; unwindingJobs = λ j cf present → copy-unwind k ref next j cf (Aux.unwindingJobs old j cf present) }
  where
  follows : ∀ q nf → lookup q (put ref next (C.SubContext.monitors (C.subsystem k))) ≡ just nf → FollowThread q nf (follow-context k ref next)
  follows q nf present with q ≟ ref
  ... | yes refl with just-injective (trans (sym (lookup-put ref next (C.SubContext.monitors (C.subsystem k)))) present)
  ...   | refl = record
    { tid = FollowThread.tid backing; thread = FollowThread.thread backing
    ; found = FollowThread.found backing; caller = trans caller (FollowThread.caller backing)
    ; running = FollowThread.running backing; observing = FollowThread.observing backing }
    where backing = Aux.followThreads old ref f found
  follows q nf present | no apart = copy-follow k ref next q nf
    (Aux.followThreads old q nf (trans (sym (lookup-put-other ref q next (C.SubContext.monitors (C.subsystem k)) apart)) present))

-- Other followups keep their exact frame; job and foreign owners are unchanged.
replace-owner : ∀ k ref next q pc →
  (∀ (owner : FollowAwait q pc k) → FollowAwait.ref owner ≢ ref) →
  Owner q pc k → Owner q pc (follow-context k ref next)
replace-owner k ref next q pc cannot (inj₁ foreign) = inj₁ foreign
replace-owner k ref next q pc cannot (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old)
    (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
replace-owner k ref next q pc cannot (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old)
    (trans (lookup-put-other ref (FollowAwait.ref old) next (C.SubContext.monitors (C.subsystem k)) (cannot old)) (FollowAwait.found old))
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old)
    (FollowAwait.thread old) (FollowAwait.byPeer old) (FollowAwait.worker old)
    (FollowAwait.running old) (FollowAwait.observing old)))

-- An await owner for the selected followup is frozen while its result is empty.
acquire-other : ∀ k ref f a c peers {next w′} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.step a f (J.world c peers) ≡ just (next , w′) → ∀ q → lookup q (O.acquired c) ≡ nothing →
  (owner : FollowAwait q J.awaitAcquire k) → FollowAwait.ref owner ≢ ref
acquire-other k ref f a c peers found stepped q absent owner refl with just-injective (trans (sym found) (FollowAwait.found owner))
... | refl = case trans (sym (Waiting.acquire-stuck a _ c peers q (FollowAwait.caller owner) (FollowAwait.waiting owner) absent)) stepped of λ ()

-- The releasing alternative reads the released table independently.
release-other : ∀ k ref f a c peers {next w′} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.step a f (J.world c peers) ≡ just (next , w′) → ∀ q → lookup q (O.released c) ≡ nothing →
  (owner : FollowAwait q J.awaitRelease k) → FollowAwait.ref owner ≢ ref
release-other k ref f a c peers found stepped q absent owner refl with just-injective (trans (sym found) (FollowAwait.found owner))
... | refl = case trans (sym (Waiting.release-stuck a _ c peers q (FollowAwait.caller owner) (FollowAwait.waiting owner) absent)) stepped of λ ()

-- All source-key-preserving followup steps preserve both ownership clauses.
follow-step-inv : ∀ c k ref f a peers {next w′} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.step a f (J.world c peers) ≡ just (next , w′) → KeySame c (J.cm w′) → Inv c k →
  Inv (J.cm w′) (follow-context k ref next)
follow-step-inv c k ref f a peers {next} {w′} found stepped same inv = owned-frames acq rel
  where
  acq : ∀ q → is-just (lookup q (O.acquiring (J.cm w′))) ≡ true →
    lookup q (O.acquired (J.cm w′)) ≡ nothing × Owner q J.awaitAcquire (follow-context k ref next)
  acq q present = trans (cong (lookup q) (acquiredSame same)) (proj₁ old) ,
    replace-owner k ref next q J.awaitAcquire (acquire-other k ref f a c peers found stepped q (proj₁ old)) (proj₂ old)
    where old = acquiring inv q (trans (sym (acquiringKeys same q)) present)
  rel : ∀ q → is-just (lookup q (O.releasing (J.cm w′))) ≡ true →
    lookup q (O.released (J.cm w′)) ≡ nothing × Owner q J.awaitRelease (follow-context k ref next)
  rel q present = trans (cong (lookup q) (releasedSame same)) (proj₁ old) ,
    replace-owner k ref next q J.awaitRelease (release-other k ref f a c peers found stepped q (proj₁ old)) (proj₂ old)
    where old = releasing inv q (trans (sym (releasingKeys same q)) present)

-- A caller different from the updated followup cannot name that same row.
caller-other : ∀ k ref f → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  ∀ q pc → q ≢ J.caller f → (owner : FollowAwait q pc k) → FollowAwait.ref owner ≢ ref
caller-other k ref f found q pc apart owner refl with just-injective (trans (sym found) (FollowAwait.found owner))
... | refl = apart (sym (FollowAwait.caller owner))

-- Matching await creation retains its existing physical-thread witness.
new-owner : ∀ k ref f next pc → J.caller next ≡ J.caller f → J.pc next ≡ pc →
  FollowThread ref f k → Owner (J.caller f) pc (follow-context k ref next)
new-owner k ref f next pc caller waiting backing = inj₂ (inj₂
  (follow-await ref next (lookup-put ref next (C.SubContext.monitors (C.subsystem k))) caller waiting (FollowThread.tid backing)
    (FollowThread.thread backing) (FollowThread.found backing) (sym (FollowThread.caller backing))
    (FollowThread.running backing) (FollowThread.observing backing)))

-- Invert an acquisition begin, retaining the monitor's old physical owner.
raw-acquire : ∀ c k ref f next req {d} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.caller next ≡ J.caller f → J.pc next ≡ J.awaitAcquire →
  O.advance (O.beginAcquire (J.caller f) req) c ≡ just d → Inv c k → Unique c → Aux k → Inv d (follow-context k ref next)
raw-acquire c k ref f next req found caller waiting advanced inv unique aux with
  lookup (J.caller f) (O.acquiring c) | lookup (J.caller f) (O.releasing c) in absent
... | nothing | nothing = case just-injective advanced of λ { refl → B.acquire-begin c k (follow-context k ref next) (J.caller f) req
  unique inv absent (new-owner k ref f next J.awaitAcquire caller waiting (Aux.followThreads aux ref f found))
  (λ q pc apart → replace-owner k ref next q pc (caller-other k ref f found q pc apart)) }
... | just _ | _ = case advanced of λ ()
... | nothing | just _ = case advanced of λ ()

-- Release creation supplies the corresponding awaitRelease followup witness.
raw-release : ∀ c k ref f next key {d} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.caller next ≡ J.caller f → J.pc next ≡ J.awaitRelease →
  O.advance (O.beginRelease (J.caller f) key) c ≡ just d → Inv c k → Unique c → Aux k → Inv d (follow-context k ref next)
raw-release c k ref f next key found caller waiting advanced inv unique aux with
  lookup (J.caller f) (O.acquiring c) in absent | lookup (J.caller f) (O.releasing c)
... | nothing | nothing = case just-injective advanced of λ { refl → B.release-begin c k (follow-context k ref next) (J.caller f) key
  unique inv absent (new-owner k ref f next J.awaitRelease caller waiting (Aux.followThreads aux ref f found))
  (λ q pc apart → replace-owner k ref next q pc (caller-other k ref f found q pc apart)) }
... | just _ | _ = case advanced of λ ()
... | nothing | just _ = case advanced of λ ()

-- All successful logical followup actions retain the full source and metadata
-- invariant. The PS/K adapter wrapper is separate from this component theorem.
follow-step-preserves : ∀ c k ref f a peers {next w′} → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  J.step a f (J.world c peers) ≡ just (next , w′) → Inv c k → Unique c → Aux k →
  Inv (J.cm w′) (follow-context k ref next) × Unique (J.cm w′) × Aux (follow-context k ref next)
follow-step-preserves c k ref f a peers {next} found stepped inv unique aux with Source.step-effect a f (J.world c peers) stepped
... | Source.same same = follow-step-inv c k ref f a peers found stepped same inv , uniqueSame same unique ,
  follow-aux k ref f next found (Identity.step-caller a f (J.world c peers) stepped) aux
... | Source.acquired req advanced waiting =
  raw-acquire c k ref f next req found caller waiting advanced inv unique aux ,
  advance-unique (O.beginAcquire (J.caller f) req) c advanced unique , follow-aux k ref f next found caller aux
  where caller = Identity.step-caller a f (J.world c peers) stepped
... | Source.released key advanced waiting =
  raw-release c k ref f next key found caller waiting advanced inv unique aux ,
  advance-unique (O.beginRelease (J.caller f) key) c advanced unique , follow-aux k ref f next found caller aux
  where caller = Identity.step-caller a f (J.world c peers) stepped
