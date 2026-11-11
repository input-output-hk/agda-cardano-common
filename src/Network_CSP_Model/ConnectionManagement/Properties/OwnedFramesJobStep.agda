{-# OPTIONS --guardedness #-}

-- A successful job update cannot advance an existing await owner while that
-- caller's result cell is empty. Other job owners keep their exact rows.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesJobStep
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.OutboundKeys using
  (KeySame; acquiringKeys; releasingKeys; acquiredSame; releasedSame)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAwait as AwaitFacts
import ConnectionManagement.Properties.OwnedFramesJobNames as NameFacts
import ConnectionManagement.Properties.OwnedFramesIdentity as Identity
open Frames isBearerClosed isIOManagerError
private
  module Waiting = AwaitFacts isBearerClosed isIOManagerError
  module Names = NameFacts isBearerClosed isIOManagerError

-- Caller-preserving replacement transports all owners except an await witness
-- for the very job that was advanced; that case is excluded by AwaitStuck.
replace-owner : ∀ k j jf next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution jf) →
  ∀ q pc → (∀ (owner : JobAwait q pc k) → JobAwait.job owner ≢ j) →
  Owner q pc k → Owner q pc (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
replace-owner k j jf next found caller q pc cannot (inj₁ foreign) = inj₁
  (trans (Names.SameJobs.unowned (Names.replace-jobs (C.SubContext.jobs (C.subsystem k)) j jf next found caller) q) (proj₁ foreign) , proj₂ foreign)
replace-owner k j jf next found caller q pc cannot (inj₂ (inj₁ owner)) = inj₂ (inj₁
  (job-await (JobAwait.job owner) (JobAwait.frame owner)
    (trans (lookup-put-other j (JobAwait.job owner) next (C.SubContext.jobs (C.subsystem k)) (cannot owner)) (JobAwait.found owner))
    (JobAwait.caller owner) (JobAwait.waiting owner) (JobAwait.running owner)))
replace-owner k j jf next found caller q pc cannot (inj₂ (inj₂ owner)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner)
    (FollowAwait.caller owner) (FollowAwait.waiting owner) (FollowAwait.tid owner)
    (FollowAwait.thread owner) (FollowAwait.byPeer owner) (FollowAwait.worker owner)
    (FollowAwait.running owner) (FollowAwait.observing owner)))

-- Result absence excludes an acquisition witness for the job taking this step.
acquire-other-job : ∀ k j jf a c peers {next w′} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.step a (Sub.execution jf) (J.world c peers) ≡ just (next , w′) →
  ∀ q → lookup q (O.acquired c) ≡ nothing → (owner : JobAwait q J.awaitAcquire k) → JobAwait.job owner ≢ j
acquire-other-job k j jf a c peers found stepped q absent owner refl with
  just-injective (trans (sym found) (JobAwait.found owner))
... | refl = case trans (sym (Waiting.acquire-stuck a _ c peers q
  (JobAwait.caller owner) (JobAwait.waiting owner) absent)) stepped of λ ()

-- Release waits have the same non-advancement property on the released table.
release-other-job : ∀ k j jf a c peers {next w′} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.step a (Sub.execution jf) (J.world c peers) ≡ just (next , w′) →
  ∀ q → lookup q (O.released c) ≡ nothing → (owner : JobAwait q J.awaitRelease k) → JobAwait.job owner ≢ j
release-other-job k j jf a c peers found stepped q absent owner refl with
  just-injective (trans (sym found) (JobAwait.found owner))
... | refl = case trans (sym (Waiting.release-stuck a _ c peers q
  (JobAwait.caller owner) (JobAwait.waiting owner) absent)) stepped of λ ()

-- Every source-key-preserving job update preserves A/R before its separate
-- pool noteReturn. This applies to all successful actions with that source effect.
job-step-inv : ∀ c k j jf a peers {next w′} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.step a (Sub.execution jf) (J.world c peers) ≡ just (next , w′) →
  KeySame c (J.cm w′) → Inv c k →
  Inv (J.cm w′) (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
job-step-inv c k j jf a peers {next} {w′} found stepped same inv = owned-frames acq rel
  where
  caller = Identity.step-caller a (Sub.execution jf) (J.world c peers) stepped
  acq : ∀ q → is-just (lookup q (O.acquiring (J.cm w′))) ≡ true →
    lookup q (O.acquired (J.cm w′)) ≡ nothing ×
    Owner q J.awaitAcquire (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
  acq q present = trans (cong (lookup q) (acquiredSame same)) (proj₁ old) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitAcquire
      (acquire-other-job k j jf a c peers found stepped q (proj₁ old)) (proj₂ old)
    where
    old = acquiring inv q (trans (sym (acquiringKeys same q)) present)
  rel : ∀ q → is-just (lookup q (O.releasing (J.cm w′))) ≡ true →
    lookup q (O.released (J.cm w′)) ≡ nothing ×
    Owner q J.awaitRelease (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
  rel q present = trans (cong (lookup q) (releasedSame same)) (proj₁ old) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitRelease
      (release-other-job k j jf a c peers found stepped q (proj₁ old)) (proj₂ old)
    where
    old = releasing inv q (trans (sym (releasingKeys same q)) present)

-- Different callers cannot name the same looked-up job row.
caller-apart-job : ∀ k j jf → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  ∀ q pc → q ≢ J.caller (Sub.execution jf) → (owner : JobAwait q pc k) → JobAwait.job owner ≢ j
caller-apart-job k j jf found q pc apart owner refl with
  just-injective (trans (sym found) (JobAwait.found owner))
... | refl = apart (sym (JobAwait.caller owner))

open import ConnectionManagement.Properties.OutboundKeys using (Unique; acquireResults; releaseResults)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

-- Beginning acquisition installs the exact job-at-awaitAcquire owner, while
-- incoming absence protects both clauses for every other retained frame.
job-begin-acquire : ∀ c k j jf next req →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.caller next ≡ J.caller (Sub.execution jf) → J.pc next ≡ J.awaitAcquire →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  lookup (J.caller (Sub.execution jf)) (O.acquiring c) ≡ nothing →
  lookup (J.caller (Sub.execution jf)) (O.releasing c) ≡ nothing → Unique c → Inv c k →
  Inv (record c { acquiring = put (J.caller (Sub.execution jf)) (A.frame req A.selecting) (O.acquiring c)
               ; acquired = delete (J.caller (Sub.execution jf)) (O.acquired c) })
    (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
job-begin-acquire c k j jf next req found caller waiting running absent-acquire absent-release unique inv = owned-frames acq rel
  where
  w = J.caller (Sub.execution jf)
  rows = C.SubContext.jobs (C.subsystem k)
  next-context = Names.job-context k (put j (record jf { execution = next }) rows)
  acq : ∀ q → is-just (lookup q (put w (A.frame req A.selecting) (O.acquiring c))) ≡ true →
    lookup q (delete w (O.acquired c)) ≡ nothing × Owner q J.awaitAcquire next-context
  acq q present with q ≟ w
  ... | yes refl = delete-self w (O.acquired c) (acquireResults unique) , inj₂ (inj₁
    (job-await j (record jf { execution = next }) (lookup-put j _ rows) caller waiting running))
  ... | no apart = trans (delete-other w q (O.acquired c) apart) (proj₁ old) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitAcquire
      (caller-apart-job k j jf found q J.awaitAcquire apart) (proj₂ old)
    where
    old = acquiring inv q (trans (sym (cong is-just (lookup-put-other w q (A.frame req A.selecting) (O.acquiring c) apart))) present)
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true →
    lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease next-context
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just absent-release)) present of λ ()
  ... | no apart = proj₁ (releasing inv q present) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitRelease
      (caller-apart-job k j jf found q J.awaitRelease apart) (proj₂ (releasing inv q present))

-- Release creation uses the same caller partition and the matching await PC.
job-begin-release : ∀ c k j jf next key →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.caller next ≡ J.caller (Sub.execution jf) → J.pc next ≡ J.awaitRelease →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  lookup (J.caller (Sub.execution jf)) (O.acquiring c) ≡ nothing →
  lookup (J.caller (Sub.execution jf)) (O.releasing c) ≡ nothing → Unique c → Inv c k →
  Inv (record c { releasing = put (J.caller (Sub.execution jf)) (R.frame key R.transaction false) (O.releasing c)
               ; released = delete (J.caller (Sub.execution jf)) (O.released c) })
    (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
job-begin-release c k j jf next key found caller waiting running absent-acquire absent-release unique inv = owned-frames acq rel
  where
  w = J.caller (Sub.execution jf)
  rows = C.SubContext.jobs (C.subsystem k)
  next-context = Names.job-context k (put j (record jf { execution = next }) rows)
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true →
    lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire next-context
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just absent-acquire)) present of λ ()
  ... | no apart = proj₁ (acquiring inv q present) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitAcquire
      (caller-apart-job k j jf found q J.awaitAcquire apart) (proj₂ (acquiring inv q present))
  rel : ∀ q → is-just (lookup q (put w (R.frame key R.transaction false) (O.releasing c))) ≡ true →
    lookup q (delete w (O.released c)) ≡ nothing × Owner q J.awaitRelease next-context
  rel q present with q ≟ w
  ... | yes refl = delete-self w (O.released c) (releaseResults unique) , inj₂ (inj₁
    (job-await j (record jf { execution = next }) (lookup-put j _ rows) caller waiting running))
  ... | no apart = trans (delete-other w q (O.released c) apart) (proj₁ old) ,
    replace-owner k j jf (record jf { execution = next }) found caller q J.awaitRelease
      (caller-apart-job k j jf found q J.awaitRelease apart) (proj₂ old)
    where
    old = releasing inv q (trans (sym (cong is-just (lookup-put-other w q (R.frame key R.transaction false) (O.releasing c) apart))) present)

open import ConnectionManagement.Properties.OutboundKeys using (advance-unique; uniqueSame)
import ConnectionManagement.Properties.OwnedFramesJobSource as Source
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
private module X = Auxiliary isBearerClosed isIOManagerError

-- Invert the actual begin guard to expose both incoming absence premises.
raw-job-acquire : ∀ c k j jf next req {d} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.caller next ≡ J.caller (Sub.execution jf) → J.pc next ≡ J.awaitAcquire →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  O.advance (O.beginAcquire (J.caller (Sub.execution jf)) req) c ≡ just d → Unique c → Inv c k →
  Inv d (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
raw-job-acquire c k j jf next req found caller waiting running advanced unique inv with
  lookup (J.caller (Sub.execution jf)) (O.acquiring c) in absent-acquire |
  lookup (J.caller (Sub.execution jf)) (O.releasing c) in absent-release
... | nothing | nothing = case just-injective advanced of λ { refl →
  job-begin-acquire c k j jf next req found caller waiting running absent-acquire absent-release unique inv }
... | just _ | _ = case advanced of λ ()
... | nothing | just _ = case advanced of λ ()

-- Release inversion is independent of the job's mutable peer-world fields.
raw-job-release : ∀ c k j jf next key {d} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.caller next ≡ J.caller (Sub.execution jf) → J.pc next ≡ J.awaitRelease →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  O.advance (O.beginRelease (J.caller (Sub.execution jf)) key) c ≡ just d → Unique c → Inv c k →
  Inv d (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
raw-job-release c k j jf next key found caller waiting running advanced unique inv with
  lookup (J.caller (Sub.execution jf)) (O.acquiring c) in absent-acquire |
  lookup (J.caller (Sub.execution jf)) (O.releasing c) in absent-release
... | nothing | nothing = case just-injective advanced of λ { refl →
  job-begin-release c k j jf next key found caller waiting running absent-acquire absent-release unique inv }
... | just _ | _ = case advanced of λ ()
... | nothing | just _ = case advanced of λ ()

-- Every successful J.step preserves the complete logical job-frame invariant.
-- The physical pool noteReturn and the unused context fields are separate
-- adapter obligations; this theorem does not claim their K-level wrapper.
job-step-preserves : ∀ c k j jf a peers {next w′} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  J.step a (Sub.execution jf) (J.world c peers) ≡ just (next , w′) →
  Inv c k → Unique c → X.Aux k →
  Inv (J.cm w′) (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k)))) ×
  Unique (J.cm w′) × X.Aux (Names.job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
job-step-preserves c k j jf a peers {next} found running stepped inv unique aux with
  Source.step-effect a (Sub.execution jf) (J.world c peers) stepped
... | Source.same same = job-step-inv c k j jf a peers found stepped same inv , uniqueSame same unique ,
  Names.job-step-aux k j jf a (J.world c peers) found stepped aux
... | Source.acquired req advanced waiting =
  raw-job-acquire c k j jf next req found caller waiting running advanced unique inv ,
  advance-unique (O.beginAcquire (J.caller (Sub.execution jf)) req) c advanced unique ,
  Names.job-step-aux k j jf a (J.world c peers) found stepped aux
  where caller = Identity.step-caller a (Sub.execution jf) (J.world c peers) stepped
... | Source.released key advanced waiting =
  raw-job-release c k j jf next key found caller waiting running advanced unique inv ,
  advance-unique (O.beginRelease (J.caller (Sub.execution jf)) key) c advanced unique ,
  Names.job-step-aux k j jf a (J.world c peers) found stepped aux
  where caller = Identity.step-caller a (Sub.execution jf) (J.world c peers) stepped
