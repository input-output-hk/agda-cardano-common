{-# OPTIONS --guardedness #-}

-- Outbound caller bookkeeping that a step can change: which workers have an
-- acquisition or release frame, and the two returned-result tables. Only the
-- two begins and the two returns change it; every other outbound-machine step
-- (inbound dispatcher steps, and acquire/release steps on an existing frame)
-- keeps the key sets and result tables.
module ConnectionManagement.Properties.OutboundKeys where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; put-unique; delete-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

-- The four actions that add or remove a frame and write a result table.
keyChanging : O.Action → Bool
keyChanging (O.beginAcquire _ _) = true
keyChanging (O.beginRelease _ _) = true
keyChanging (O.acquire _ A.returnResult) = true
keyChanging (O.release _ R.returnResult) = true
keyChanging _ = false

-- The four caller stores have unique keys; deletion therefore removes a caller.
record Unique (c : O.Configuration) : Set where
  constructor unique-tables
  field
    acquireFrames : UniqueKeys (O.acquiring c)
    releaseFrames : UniqueKeys (O.releasing c)
    acquireResults : UniqueKeys (O.acquired c)
    releaseResults : UniqueKeys (O.released c)
open Unique public

record KeySame (c c′ : O.Configuration) : Set where
  field
    uniqueSame : Unique c → Unique c′
    acquiringKeys : ∀ w → is-just (lookup w (O.acquiring c′)) ≡ is-just (lookup w (O.acquiring c))
    releasingKeys : ∀ w → is-just (lookup w (O.releasing c′)) ≡ is-just (lookup w (O.releasing c))
    acquiredSame : O.acquired c′ ≡ O.acquired c
    releasedSame : O.released c′ ≡ O.released c
open KeySame public

same-refl : ∀ c → KeySame c c
same-refl c = record { uniqueSame = λ u → u ; acquiringKeys = λ _ → refl ; releasingKeys = λ _ → refl ; acquiredSame = refl ; releasedSame = refl }
same-trans : ∀ {c d e} → KeySame c d → KeySame d e → KeySame c e
same-trans p q = record
  { uniqueSame = λ u → uniqueSame q (uniqueSame p u)
  ; acquiringKeys = λ w → trans (acquiringKeys q w) (acquiringKeys p w)
  ; releasingKeys = λ w → trans (releasingKeys q w) (releasingKeys p w)
  ; acquiredSame = trans (acquiredSame q) (acquiredSame p)
  ; releasedSame = trans (releasedSame q) (releasedSame p) }

-- Any write that keeps the four caller fields.
fields-same : ∀ c c′ → O.acquiring c′ ≡ O.acquiring c → O.releasing c′ ≡ O.releasing c →
  O.acquired c′ ≡ O.acquired c → O.released c′ ≡ O.released c → KeySame c c′
fields-same c c′ a r q d = record
  { uniqueSame = λ u → unique-tables
      (subst UniqueKeys (sym a) (acquireFrames u))
      (subst UniqueKeys (sym r) (releaseFrames u))
      (subst UniqueKeys (sym q) (acquireResults u))
      (subst UniqueKeys (sym d) (releaseResults u))
  ; acquiringKeys = λ w → cong (λ xs → is-just (lookup w xs)) a
  ; releasingKeys = λ w → cong (λ xs → is-just (lookup w xs)) r
  ; acquiredSame = q ; releasedSame = d }

-- Overwriting an existing key keeps every key's presence.
put-present : ∀ {V : Set} (xs : Store WorkerId V) w v {old} → lookup w xs ≡ just old →
  ∀ k → is-just (lookup k (put w v xs)) ≡ is-just (lookup k xs)
put-present xs w v found k with k ≟ w
... | yes refl = trans (cong is-just (lookup-put k v xs)) (sym (cong is-just found))
... | no apart = cong is-just (lookup-put-other w k v xs apart)

acquire-keys : ∀ c w f′ core′ gen {old} → lookup w (O.acquiring c) ≡ just old →
  KeySame c (record c { core = core′; acquiring = put w f′ (O.acquiring c); randomGeneration = gen })
acquire-keys c w f′ core′ gen found = record
  { uniqueSame = λ u → unique-tables
      (put-unique w f′ (O.acquiring c) (acquireFrames u))
      (releaseFrames u) (acquireResults u) (releaseResults u)
  ; acquiringKeys = put-present (O.acquiring c) w f′ found
  ; releasingKeys = λ _ → refl ; acquiredSame = refl ; releasedSame = refl }
release-keys : ∀ c w f′ core′ gen {old} → lookup w (O.releasing c) ≡ just old →
  KeySame c (record c { core = core′; releasing = put w f′ (O.releasing c); randomGeneration = gen })
release-keys c w f′ core′ gen found = record
  { uniqueSame = λ u → unique-tables (acquireFrames u)
      (put-unique w f′ (O.releasing c) (releaseFrames u))
      (acquireResults u) (releaseResults u)
  ; acquiringKeys = λ _ → refl
  ; releasingKeys = put-present (O.releasing c) w f′ found
  ; acquiredSame = refl ; releasedSame = refl }

-- Every other outbound-machine step keeps the caller keys and result tables.
nonkey : ∀ a c {c′} → keyChanging a ≡ false → O.advance a c ≡ just c′ → KeySame c c′
nonkey (O.inbound a) c nk eq with I.advance a (O.core c)
... | nothing = case eq of λ ()
... | just core′ = case just-injective eq of λ { refl → fields-same c _ refl refl refl refl }
nonkey (O.beginAcquire w r) c () eq
nonkey (O.beginRelease w k) c () eq
nonkey (O.acquire w A.returnResult) c () eq
nonkey (O.release w R.returnResult) c () eq
nonkey (O.acquire w (A.select e)) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) (A.select e) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.readCounters) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.readCounters f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.newPromise) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.newPromise f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.openOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.openOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.configureOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.configureOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.bindOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.bindOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.connectOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.connectOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w (A.gotLocal p)) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) (A.gotLocal p) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.updateLocalAddress) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.updateLocalAddress f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.forkOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.forkOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.commitConnected) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.commitConnected f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.readResult) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.readResult f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.commitHandshake) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.commitHandshake f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w (A.failIO e)) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) (A.failIO e) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w (A.closeFailed e)) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) (A.closeFailed e) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.closeOK) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.closeOK f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.removeReservation) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.removeReservation f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.acquire w A.waitNegotiated) c nk eq with lookup w (O.acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (O.core c)) A.waitNegotiated f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → acquire-keys c w f′ _ _ found }
nonkey (O.release w R.transactionStep) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.transactionStep c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.transactionStep f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.transactionStep) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.transactionStep) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.checkAssertion) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.checkAssertion c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.checkAssertion f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.checkAssertion) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.checkAssertion) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.readCounters) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.readCounters c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.readCounters f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.readCounters) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.readCounters) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.registerTimer) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.registerTimer c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.registerTimer f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.registerTimer) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.registerTimer) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.expireTimer) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.expireTimer c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.expireTimer f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.expireTimer) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.expireTimer) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.selectWakeup) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.selectWakeup c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.selectWakeup f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.selectWakeup) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.selectWakeup) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.commitTimeout) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.commitTimeout c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.commitTimeout f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.commitTimeout) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.commitTimeout) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w R.requestCancellation) c nk eq with lookup w (O.releasing c) in found | O.canDeliver R.requestCancellation c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) R.requestCancellation f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w R.requestCancellation) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w R.requestCancellation) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w (R.transactionPruning ss)) c nk eq with lookup w (O.releasing c) in found | O.canDeliver (R.transactionPruning ss) c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) (R.transactionPruning ss) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w (R.transactionPruning ss)) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w (R.transactionPruning ss)) c nk eq | nothing | _ = case eq of λ ()
nonkey (O.release w (R.cancellationDelivered t)) c nk eq with lookup w (O.releasing c) in found | O.canDeliver (R.cancellationDelivered t) c
... | just f | true with R.step (I.promotionHardLimit (O.core c)) (R.cancellationDelivered t) f (I.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → release-keys c w f′ _ _ found }
nonkey (O.release w (R.cancellationDelivered t)) c nk eq | just f | false = case eq of λ ()
nonkey (O.release w (R.cancellationDelivered t)) c nk eq | nothing | _ = case eq of λ ()

-- A begin or return preserves uniqueness using the actual put/delete writers.
changing-unique : ∀ a c {d} → keyChanging a ≡ true →
  O.advance a c ≡ just d → Unique c → Unique d
changing-unique (O.beginAcquire w req) c changes eq u with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → unique-tables
  (put-unique w _ (O.acquiring c) (acquireFrames u)) (releaseFrames u)
  (delete-unique w (O.acquired c) (acquireResults u)) (releaseResults u) }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
changing-unique (O.beginRelease w key) c changes eq u with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → unique-tables
  (acquireFrames u) (put-unique w _ (O.releasing c) (releaseFrames u))
  (acquireResults u) (delete-unique w (O.released c) (releaseResults u)) }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = case just-injective eq of λ { refl → unique-tables
  (delete-unique w (O.acquiring c) (acquireFrames u)) (releaseFrames u)
  (put-unique w result (O.acquired c) (acquireResults u)) (releaseResults u) }
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | A.selecting = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.count next) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.allocatePromise e) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.openSocket e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.configureSocket e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.bindSocket e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.connectSocket e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.localAddress e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.updateAddress e p q) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.forkHandler e p q) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.connectedCommit e p q) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.awaitResult e p q) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.commitResult e p q) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.waitingInbound e p) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.closeError e err) = case eq of λ ()
changing-unique (O.acquire w A.returnResult) c changes eq u | just f | (A.removeError e err) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u with lookup w (O.releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = case just-injective eq of λ { refl → unique-tables
  (acquireFrames u) (delete-unique w (O.releasing c) (releaseFrames u))
  (acquireResults u) (put-unique w result (O.released c) (releaseResults u)) }
changing-unique (O.release w R.returnResult) c changes eq u | just f | R.transaction = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.check b next) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.count next) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.delivering t next) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.armTimer e t) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.waitIdle e t) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.timeoutWrite e t) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.cancel t next) = case eq of λ ()
changing-unique (O.release w R.returnResult) c changes eq u | just f | (R.prune ss result) = case eq of λ ()
changing-unique (O.inbound _) c () eq u
changing-unique (O.acquire w (A.select e)) c () eq u
changing-unique (O.acquire w A.readCounters) c () eq u
changing-unique (O.acquire w A.newPromise) c () eq u
changing-unique (O.acquire w A.openOK) c () eq u
changing-unique (O.acquire w A.configureOK) c () eq u
changing-unique (O.acquire w A.bindOK) c () eq u
changing-unique (O.acquire w A.connectOK) c () eq u
changing-unique (O.acquire w (A.gotLocal p)) c () eq u
changing-unique (O.acquire w A.updateLocalAddress) c () eq u
changing-unique (O.acquire w A.forkOK) c () eq u
changing-unique (O.acquire w A.commitConnected) c () eq u
changing-unique (O.acquire w A.readResult) c () eq u
changing-unique (O.acquire w A.commitHandshake) c () eq u
changing-unique (O.acquire w (A.failIO e)) c () eq u
changing-unique (O.acquire w (A.closeFailed e)) c () eq u
changing-unique (O.acquire w A.closeOK) c () eq u
changing-unique (O.acquire w A.removeReservation) c () eq u
changing-unique (O.acquire w A.waitNegotiated) c () eq u
changing-unique (O.release w R.transactionStep) c () eq u
changing-unique (O.release w R.checkAssertion) c () eq u
changing-unique (O.release w R.readCounters) c () eq u
changing-unique (O.release w R.registerTimer) c () eq u
changing-unique (O.release w R.expireTimer) c () eq u
changing-unique (O.release w R.selectWakeup) c () eq u
changing-unique (O.release w R.commitTimeout) c () eq u
changing-unique (O.release w R.requestCancellation) c () eq u
changing-unique (O.release w (R.transactionPruning choices)) c () eq u
changing-unique (O.release w (R.cancellationDelivered target)) c () eq u

-- Every outbound action preserves uniqueness, including non-key frame updates.
advance-unique : ∀ a c {d} → O.advance a c ≡ just d → Unique c → Unique d
advance-unique a c eq u with keyChanging a in changes
... | false = uniqueSame (nonkey a c changes eq) u
... | true = changing-unique a c changes eq u

-- The effect of a layered step on the caller bookkeeping: unchanged keys, or
-- (for a lifted key-changing outbound action) exactly that machine step
-- followed by key-preserving writes.
open import Data.Product using (Σ; _×_)
Effect : Maybe O.Action → O.Configuration → O.Configuration → Set
Effect nothing c c′ = KeySame c c′
Effect (just x) c c′ = Σ O.Configuration (λ d → O.advance x c ≡ just d × KeySame d c′)
effect-after : ∀ r {c d e} → Effect r c d → KeySame d e → Effect r c e
effect-after nothing p q = same-trans p q
effect-after (just x) (d , stepped , p) q = d , stepped , same-trans p q

-- The root of a lifted outbound action, when it changes keys.
keyRoot : O.Action → Maybe O.Action
keyRoot x with keyChanging x
... | true = just x
... | false = nothing
root-true : ∀ x → keyChanging x ≡ true → keyRoot x ≡ just x
root-true x eq with keyChanging x
root-true x refl | true = refl
root-false : ∀ x → keyChanging x ≡ false → keyRoot x ≡ nothing
root-false x eq with keyChanging x
root-false x refl | false = refl

-- One outbound-machine step, as an effect of its own root.
advance-effect : ∀ x c {c′} → O.advance x c ≡ just c′ → Effect (keyRoot x) c c′
advance-effect x c {c′} eq with keyChanging x in kc
... | true = c′ , eq , same-refl c′
... | false = nonkey x c kc eq

-- An Effect carries uniqueness through its raw action and all later writes.
effect-unique : ∀ r {c d} → Effect r c d → Unique c → Unique d
effect-unique nothing same u = uniqueSame same u
effect-unique (just a) (d , stepped , same) u = uniqueSame same (advance-unique a _ stepped u)
