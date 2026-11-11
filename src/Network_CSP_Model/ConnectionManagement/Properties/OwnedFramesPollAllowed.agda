{-# OPTIONS --guardedness #-}

-- Decode the actual PSA poll guard into its captured physical observer facts.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPollAllowed
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId; PeerConnectionId; WorkerId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCore as Core
open Frames isBearerClosed isIOManagerError
private module B = Core isBearerClosed isIOManagerError

-- A true decidable-equality guard exposes its actual equality proof.
sound : ∀ {P : Set} (decision : Dec P) → does decision ≡ true → P
sound (yes proof) eq = proof
sound (no apart) ()

-- The physical thread-running guard means exactly bodyRunning and observing.
thread-fields : ∀ tid t s → PS.threadRunning tid t s ≡ true →
  lookup tid (PS.Pool.handles (PS.monitorPool s)) ≡ just PS.Pool.bodyRunning × PS.pc t ≡ PS.observing
thread-fields tid t s eq with lookup tid (PS.Pool.handles (PS.monitorPool s)) | PS.pc t
... | just PS.Pool.bodyRunning | PS.observing = refl , refl
... | nothing | pc = case eq of λ ()
... | just PS.Pool.bodyUnwinding | pc = case eq of λ ()
... | just (PS.Pool.bodyReturned _) | pc = case eq of λ ()
... | just (PS.Pool.deregisterPending _) | pc = case eq of λ ()
... | just (PS.Pool.deregistered _) | pc = case eq of λ ()
... | just (PS.Pool.resultAvailable _) | pc = case eq of λ ()
... | just PS.Pool.bodyRunning | PS.normalFinishing = case eq of λ ()
... | just PS.Pool.bodyRunning | PS.cancelling = case eq of λ ()
... | just PS.Pool.bodyRunning | PS.exited = case eq of λ ()
... | just PS.Pool.bodyRunning | PS.errorWait err = case eq of λ ()
... | just PS.Pool.bodyRunning | PS.errorFinishing err = case eq of λ ()

-- All facts refer to the actual thread selected by this ref before the poll.
record Allowed (ref : PeerConnectionId) (caller : WorkerId) (s : PS.State) : Set where
  field
    tid : JobId
    thread : PS.Thread
    selected : PS.byPeer ref (PS.monitors s) ≡ just (tid , thread)
    observing : PS.pc thread ≡ PS.observing
    running : lookup tid (PS.Pool.handles (PS.monitorPool s)) ≡ just PS.Pool.bodyRunning
    callerSame : caller ≡ PS.worker thread

-- No caller/observer premise is added: all follow from governorAllowed itself.
allowed-poll : ∀ ref caller s → PS.governorAllowed (GP.run (Sub.pollPeer ref caller)) s ≡ true → Allowed ref caller s
allowed-poll ref caller s permit with PS.byPeer ref (PS.monitors s) in selected
... | nothing = case permit of λ ()
... | just (tid , t) = record
  { tid = tid; thread = t; selected = selected; observing = proj₂ fields; running = proj₁ fields
  ; callerSame = sound (caller ≟ PS.worker t) (proj₁ guards) }
  where
  split = B.and-true (PS.threadRunning tid t s) (does (caller ≟ PS.worker t) ∧ PS.followupOwned ref t s) permit
  fields = thread-fields tid t s (proj₁ split)
  guards = B.and-true (does (caller ≟ PS.worker t)) (PS.followupOwned ref t s) (proj₂ split)
