{-# OPTIONS --guardedness #-}

-- Core-step ownership. The representation premise is explicit: association
-- stores have unique keys, including both result stores cleared at begin.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesCore
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.SourceKeysShared as SharedKeys
open import ConnectionManagement.Properties.OutboundKeys using (keyChanging; keyRoot; Effect; root-false)
open Frames isBearerClosed isIOManagerError
private
  module Keys = SharedKeys isBearerClosed isIOManagerError

-- Caller uniqueness is shared with the complete source-effect relation.
open import ConnectionManagement.Properties.OutboundKeys using (Unique; unique-tables) public

-- All four source tables start empty in the outer O.initial profile.
initial-unique : ∀ c → Unique (O.initial c)
initial-unique c = unique-tables [] [] [] []

-- Starting a foreign acquisition adds precisely its own ownership witness.
begin-acquire : ∀ c k w req → UniqueKeys (O.acquired c) → Foreign w k → Inv c k →
  Inv (record c { acquiring = put w (A.frame req A.selecting) (O.acquiring c)
                ; acquired = delete w (O.acquired c) }) k
begin-acquire c k w req unique foreign inv = owned-frames acq (releasing inv)
  where
  acq : ∀ q → is-just (lookup q (put w (A.frame req A.selecting) (O.acquiring c))) ≡ true →
    lookup q (delete w (O.acquired c)) ≡ nothing × Owner q J.awaitAcquire k
  acq q present with q ≟ w
  ... | yes refl = delete-self w (O.acquired c) unique , inj₁ foreign
  ... | no apart = let old = acquiring inv q
                           (trans (sym (cong is-just (lookup-put-other w q _ (O.acquiring c) apart))) present)
    in trans (delete-other w q (O.acquired c) apart) (proj₁ old) , proj₂ old

-- Starting a foreign release is the corresponding released-table operation.
begin-release : ∀ c k w key → UniqueKeys (O.released c) → Foreign w k → Inv c k →
  Inv (record c { releasing = put w (R.frame key R.transaction false) (O.releasing c)
                ; released = delete w (O.released c) }) k
begin-release c k w key unique foreign inv = owned-frames (acquiring inv) rel
  where
  rel : ∀ q → is-just (lookup q (put w (R.frame key R.transaction false) (O.releasing c))) ≡ true →
    lookup q (delete w (O.released c)) ≡ nothing × Owner q J.awaitRelease k
  rel q present with q ≟ w
  ... | yes refl = delete-self w (O.released c) unique , inj₁ foreign
  ... | no apart = let old = releasing inv q
                           (trans (sym (cong is-just (lookup-put-other w q _ (O.releasing c) apart))) present)
    in trans (delete-other w q (O.released c) apart) (proj₁ old) , proj₂ old

-- Returning an acquisition publishes a result only after its frame is absent.
return-acquire : ∀ c k w result → UniqueKeys (O.acquiring c) → Inv c k →
  Inv (record c { acquiring = delete w (O.acquiring c); acquired = put w result (O.acquired c) }) k
return-acquire c k w result unique inv = owned-frames acq (releasing inv)
  where
  acq : ∀ q → is-just (lookup q (delete w (O.acquiring c))) ≡ true →
    lookup q (put w result (O.acquired c)) ≡ nothing × Owner q J.awaitAcquire k
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (delete-self w (O.acquiring c) unique))) present of λ ()
  ... | no apart = let old = acquiring inv q
                           (trans (sym (cong is-just (delete-other w q (O.acquiring c) apart))) present)
    in trans (lookup-put-other w q result (O.acquired c) apart) (proj₁ old) , proj₂ old

-- Returning a release likewise cannot leave its caller's frame behind.
return-release : ∀ c k w result → UniqueKeys (O.releasing c) → Inv c k →
  Inv (record c { releasing = delete w (O.releasing c); released = put w result (O.released c) }) k
return-release c k w result unique inv = owned-frames (acquiring inv) rel
  where
  rel : ∀ q → is-just (lookup q (delete w (O.releasing c))) ≡ true →
    lookup q (put w result (O.released c)) ≡ nothing × Owner q J.awaitRelease k
  rel q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just (delete-self w (O.releasing c) unique))) present of λ ()
  ... | no apart = let old = releasing inv q
                           (trans (sym (cong is-just (delete-other w q (O.releasing c) apart))) present)
    in trans (lookup-put-other w q result (O.released c) apart) (proj₁ old) , proj₂ old

-- Boolean permissions expose both conjuncts without normalising the runtime.
and-true : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
and-true true true refl = refl , refl
and-true true false ()
and-true false b ()

-- A successful shared core step passed its outer permission check.
core-permitted : ∀ a s {t} → K.step (K.coreStep a) s ≡ just t → K.coreAllowed a s ≡ true
core-permitted a s stepped with K.coreAllowed a s in permission
... | false = case stepped of λ ()
... | true = refl

-- Raw beginAcquire is permitted only for a caller outside both owner tables.
acquire-foreign : ∀ w req s → K.coreAllowed (O.beginAcquire w req) s ≡ true → Foreign w (K.context s)
acquire-foreign w req s allowed with and-true (K.peerOpen s)
  (K.newActors w (A.child req) (A.socketRef req) s ∧
   PS.governorAllowed (GP.run (Sub.core (O.beginAcquire w req))) (K.peers s) ∧
   GP.coreAllowed (O.beginAcquire w req) (PS.governor (K.peers s))) allowed
... | opened , rest with and-true (K.newActors w (A.child req) (A.socketRef req) s)
  (PS.governorAllowed (GP.run (Sub.core (O.beginAcquire w req))) (K.peers s) ∧
   GP.coreAllowed (O.beginAcquire w req) (PS.governor (K.peers s))) rest
... | actors , permissions with and-true
  (PS.governorAllowed (GP.run (Sub.core (O.beginAcquire w req))) (K.peers s))
  (GP.coreAllowed (O.beginAcquire w req) (PS.governor (K.peers s))) permissions
... | raw , unowned with PS.byWorker w (C.monitors (K.context s))
...   | just _ = case raw of λ ()
...   | nothing = unowned , refl

-- beginRelease has the same foreign-caller gate, without new actor allocation.
release-foreign : ∀ w key s → K.coreAllowed (O.beginRelease w key) s ≡ true → Foreign w (K.context s)
release-foreign w key s allowed with and-true (K.peerOpen s)
  (PS.governorAllowed (GP.run (Sub.core (O.beginRelease w key))) (K.peers s) ∧
   GP.coreAllowed (O.beginRelease w key) (PS.governor (K.peers s))) allowed
... | opened , permissions with and-true
  (PS.governorAllowed (GP.run (Sub.core (O.beginRelease w key))) (K.peers s))
  (GP.coreAllowed (O.beginRelease w key) (PS.governor (K.peers s))) permissions
... | raw , unowned with PS.byWorker w (C.monitors (K.context s))
...   | just _ = case raw of λ ()
...   | nothing = unowned , refl

-- Non-key core actions preserve ownership through the existing source effect.
nonkey-core : ∀ a s {t} → keyChanging a ≡ false →
  K.step (K.coreStep a) s ≡ just t → Owned s → Owned t
nonkey-core a s {t} nonkey stepped inv with Keys.core-keys a s stepped
... | effect , context = subst (Inv (K.source t)) (sym context)
  (note-inv a (K.source t) (K.source t) (K.context s)
    (same-source (subst (λ root → Effect root (K.source s) (K.source t)) (root-false a nonkey) effect) inv))

-- A real raw begin has the named begin writer, or is refused.
raw-begin-acquire : ∀ c k w req {d} → O.advance (O.beginAcquire w req) c ≡ just d →
  Unique c → Foreign w k → Inv c k → Inv d k
raw-begin-acquire c k w req stepped unique foreign inv with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective stepped of λ { refl → begin-acquire c k w req (Unique.acquireResults unique) foreign inv }
... | just _ | _ = case stepped of λ ()
... | nothing | just _ = case stepped of λ ()

-- The release begin is the same guarded source operation.
raw-begin-release : ∀ c k w key {d} → O.advance (O.beginRelease w key) c ≡ just d →
  Unique c → Foreign w k → Inv c k → Inv d k
raw-begin-release c k w key stepped unique foreign inv with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective stepped of λ { refl → begin-release c k w key (Unique.releaseResults unique) foreign inv }
... | just _ | _ = case stepped of λ ()
... | nothing | just _ = case stepped of λ ()

-- An actual return is allowed only at the source's complete continuation.
raw-return-acquire : ∀ c k w {d} → O.advance (O.acquire w A.returnResult) c ≡ just d →
  Unique c → Inv c k → Inv d k
raw-return-acquire c k w stepped unique inv with lookup w (O.acquiring c)
... | nothing = case stepped of λ ()
... | just f with A.pc f
...   | A.complete result = case just-injective stepped of λ { refl → return-acquire c k w result (Unique.acquireFrames unique) inv }
...   | A.selecting = case stepped of λ ()
...   | (A.count p) = case stepped of λ ()
...   | (A.allocatePromise e) = case stepped of λ ()
...   | (A.openSocket e p) = case stepped of λ ()
...   | (A.configureSocket e p) = case stepped of λ ()
...   | (A.bindSocket e p) = case stepped of λ ()
...   | (A.connectSocket e p) = case stepped of λ ()
...   | (A.localAddress e p) = case stepped of λ ()
...   | (A.updateAddress e p key) = case stepped of λ ()
...   | (A.forkHandler e p key) = case stepped of λ ()
...   | (A.connectedCommit e p key) = case stepped of λ ()
...   | (A.awaitResult e p key) = case stepped of λ ()
...   | (A.commitResult e key result) = case stepped of λ ()
...   | (A.waitingInbound e key) = case stepped of λ ()
...   | (A.closeError e err) = case stepped of λ ()
...   | (A.removeError e err) = case stepped of λ ()

-- The release return has the corresponding complete-continuation guard.
raw-return-release : ∀ c k w {d} → O.advance (O.release w R.returnResult) c ≡ just d →
  Unique c → Inv c k → Inv d k
raw-return-release c k w stepped unique inv with lookup w (O.releasing c)
... | nothing = case stepped of λ ()
... | just f with R.pc f
...   | R.complete result = case just-injective stepped of λ { refl → return-release c k w result (Unique.releaseFrames unique) inv }
...   | R.transaction = case stepped of λ ()
...   | (R.check b next) = case stepped of λ ()
...   | (R.count next) = case stepped of λ ()
...   | (R.armTimer e w) = case stepped of λ ()
...   | (R.waitIdle e w) = case stepped of λ ()
...   | (R.timeoutWrite e w) = case stepped of λ ()
...   | (R.cancel w next) = case stepped of λ ()
...   | (R.delivering w next) = case stepped of λ ()
...   | (R.prune choices result) = case stepped of λ ()

-- Reuse core-keys for all non-key writes after the one primitive source step.
changing-core : ∀ a s {t} → keyChanging a ≡ true → K.step (K.coreStep a) s ≡ just t →
  Unique (K.source s) → Owned s → Owned t
changing-core (O.beginAcquire w req) s {t} changes stepped unique inv with Keys.core-keys (O.beginAcquire w req) s stepped
... | (d , raw , same) , context = subst (Inv (K.source t)) (sym context)
  (note-inv (O.beginAcquire w req) (K.source t) (K.source t) (K.context s)
    (same-source same (raw-begin-acquire (K.source s) (K.context s) w req raw unique
      (acquire-foreign w req s (core-permitted (O.beginAcquire w req) s stepped)) inv)))
changing-core (O.beginRelease w key) s {t} changes stepped unique inv with Keys.core-keys (O.beginRelease w key) s stepped
... | (d , raw , same) , context = subst (Inv (K.source t)) (sym context)
  (note-inv (O.beginRelease w key) (K.source t) (K.source t) (K.context s)
    (same-source same (raw-begin-release (K.source s) (K.context s) w key raw unique
      (release-foreign w key s (core-permitted (O.beginRelease w key) s stepped)) inv)))
changing-core (O.acquire w A.returnResult) s {t} changes stepped unique inv with Keys.core-keys (O.acquire w A.returnResult) s stepped
... | (d , raw , same) , context = subst (Inv (K.source t)) (sym context)
  (note-inv (O.acquire w A.returnResult) (K.source t) (K.source t) (K.context s)
    (same-source same (raw-return-acquire (K.source s) (K.context s) w raw unique inv)))
changing-core (O.release w R.returnResult) s {t} changes stepped unique inv with Keys.core-keys (O.release w R.returnResult) s stepped
... | (d , raw , same) , context = subst (Inv (K.source t)) (sym context)
  (note-inv (O.release w R.returnResult) (K.source t) (K.source t) (K.context s)
    (same-source same (raw-return-release (K.source s) (K.context s) w raw unique inv)))
changing-core (O.inbound _) s () stepped unique inv
changing-core (O.acquire w (A.select e)) s () stepped unique inv
changing-core (O.acquire w A.readCounters) s () stepped unique inv
changing-core (O.acquire w A.newPromise) s () stepped unique inv
changing-core (O.acquire w A.openOK) s () stepped unique inv
changing-core (O.acquire w A.configureOK) s () stepped unique inv
changing-core (O.acquire w A.bindOK) s () stepped unique inv
changing-core (O.acquire w A.connectOK) s () stepped unique inv
changing-core (O.acquire w (A.gotLocal p)) s () stepped unique inv
changing-core (O.acquire w A.updateLocalAddress) s () stepped unique inv
changing-core (O.acquire w A.forkOK) s () stepped unique inv
changing-core (O.acquire w A.commitConnected) s () stepped unique inv
changing-core (O.acquire w A.readResult) s () stepped unique inv
changing-core (O.acquire w A.commitHandshake) s () stepped unique inv
changing-core (O.acquire w (A.failIO e)) s () stepped unique inv
changing-core (O.acquire w (A.closeFailed e)) s () stepped unique inv
changing-core (O.acquire w A.closeOK) s () stepped unique inv
changing-core (O.acquire w A.removeReservation) s () stepped unique inv
changing-core (O.acquire w A.waitNegotiated) s () stepped unique inv
changing-core (O.release w R.transactionStep) s () stepped unique inv
changing-core (O.release w R.checkAssertion) s () stepped unique inv
changing-core (O.release w R.readCounters) s () stepped unique inv
changing-core (O.release w R.registerTimer) s () stepped unique inv
changing-core (O.release w R.expireTimer) s () stepped unique inv
changing-core (O.release w R.selectWakeup) s () stepped unique inv
changing-core (O.release w R.commitTimeout) s () stepped unique inv
changing-core (O.release w R.requestCancellation) s () stepped unique inv
changing-core (O.release w (R.transactionPruning choices)) s () stepped unique inv
changing-core (O.release w (R.cancellationDelivered target)) s () stepped unique inv

-- Every K-permitted core action preserves the ownership clauses when its
-- incoming four caller stores have unique keys. Reachable uniqueness is a
-- separate supporting obligation, not an assumption hidden in Inv.
core-preserves : ∀ a s {t} → K.step (K.coreStep a) s ≡ just t →
  Unique (K.source s) → Owned s → Owned t
core-preserves a s stepped unique inv with keyChanging a in changes
... | false = nonkey-core a s changes stepped inv
... | true = changing-core a s changes stepped unique inv
