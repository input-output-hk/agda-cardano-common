{-# OPTIONS --guardedness #-}

-- Common creation proof for job and monitor-followup CM calls.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesBegin
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (nothing; is-just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
open import ConnectionManagement.Properties.OutboundKeys using (Unique; acquireResults; releaseResults)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerJobs as J
open Frames isBearerClosed isIOManagerError

-- A caller begin installs the supplied matching owner and transports all others.
acquire-begin : ∀ c k next w req → Unique c → Inv c k →
  lookup w (O.releasing c) ≡ nothing → Owner w J.awaitAcquire next →
  (∀ q pc → q ≢ w → Owner q pc k → Owner q pc next) →
  Inv (record c { acquiring = put w (A.frame req A.selecting) (O.acquiring c)
               ; acquired = delete w (O.acquired c) }) next
acquire-begin c k next w req unique inv absent owner carry = owned-frames acq rel
  where
  acq : ∀ q → is-just (lookup q (put w (A.frame req A.selecting) (O.acquiring c))) ≡ true →
    lookup q (delete w (O.acquired c)) ≡ nothing × Owner q J.awaitAcquire next
  acq q present with q ≟ w
  ... | yes refl = delete-self w (O.acquired c) (acquireResults unique) , owner
  ... | no apart = trans (delete-other w q (O.acquired c) apart) (proj₁ old) , carry q J.awaitAcquire apart (proj₂ old)
    where old = acquiring inv q (trans (sym (cong is-just (lookup-put-other w q (A.frame req A.selecting) (O.acquiring c) apart))) present)
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true → lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease next
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just absent)) present of λ ()
  ... | no apart = proj₁ (releasing inv q present) , carry q J.awaitRelease apart (proj₂ (releasing inv q present))

-- The release version retains the separate released-table deletion premise.
release-begin : ∀ c k next w key → Unique c → Inv c k →
  lookup w (O.acquiring c) ≡ nothing → Owner w J.awaitRelease next →
  (∀ q pc → q ≢ w → Owner q pc k → Owner q pc next) →
  Inv (record c { releasing = put w (R.frame key R.transaction false) (O.releasing c)
               ; released = delete w (O.released c) }) next
release-begin c k next w key unique inv absent owner carry = owned-frames acq rel
  where
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true → lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire next
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just absent)) present of λ ()
  ... | no apart = proj₁ (acquiring inv q present) , carry q J.awaitAcquire apart (proj₂ (acquiring inv q present))
  rel : ∀ q → is-just (lookup q (put w (R.frame key R.transaction false) (O.releasing c))) ≡ true →
    lookup q (delete w (O.released c)) ≡ nothing × Owner q J.awaitRelease next
  rel q present with q ≟ w
  ... | yes refl = delete-self w (O.released c) (releaseResults unique) , owner
  ... | no apart = trans (delete-other w q (O.released c) apart) (proj₁ old) , carry q J.awaitRelease apart (proj₂ old)
    where old = releasing inv q (trans (sym (cong is-just (lookup-put-other w q (R.frame key R.transaction false) (O.releasing c) apart))) present)
