{-# OPTIONS --guardedness #-}

-- Atomicity, captured identity and timer-winner controls for outbound CM.
module ConnectionManagement.Negative.Outbound where

open import Data.Bool using (false; true)
open import Data.List using ([]; _∷_; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.CSP.OutboundAdmission as Trace
open import ConnectionManagement.Scenarios.Admission using (key₀)

frame : A.Frame
frame = A.frame Trace.req (A.commitResult (ident 0) key₀ (S.negotiated (ident 0) duplex))
fullQueue : S.State
fullQueue = record Trace.published { inboundInfo = replicate 100 S.inactivityTimeout }
-- Negotiation's entry write cannot commit while its same-STM enqueue retries.
full-queue-refuses-entire-commit : A.step Trace.caller S.responderMode A.commitHandshake frame fullQueue ≡ nothing
full-queue-refuses-entire-commit = refl

replacement : S.ConnectionState
replacement = S.inboundActive key₀ (ident 99) (ident 99) duplex
replaced : S.State
replaced = record Trace.published { cm = record (S.cm Trace.published)
  { mapCell = S.full (S.insertConnection key₀ (ident 1) [])
  ; entries = put (ident 1) replacement (S.entries (S.cm Trace.published)) } }
errorFrame : A.Frame
errorFrame = A.frame Trace.req (A.commitResult (ident 0) key₀ (S.handlerError S.protocolViolation (errorId 3)))
errorWorld : S.State
errorWorld = record replaced { cm = record (S.cm replaced)
  { entries = put (ident 0) (S.terminated (just (errorId 3))) (S.entries (S.cm replaced)) } }
-- Outbound writes the old captured TVar even when deletion is disallowed.
error-writes-captured-only : A.step Trace.caller S.responderMode A.commitHandshake errorFrame replaced ≡
  just (A.frame Trace.req (A.count (A.complete (C.disconnected key₀ (S.handshakeError S.protocolViolation (errorId 3))))) , errorWorld)
error-writes-captured-only = refl
replacement-retained : lookup (ident 1) (S.entries (S.cm errorWorld)) ≡ just replacement
replacement-retained = refl

collision : S.ConnMap
collision = S.insertLocal (remote key₀) unknownLocal (ident 0) (S.insertConnection key₀ (ident 1) [])
collision-deletes-reservation : A.updateLocal key₀ collision ≡ (false , S.insertConnection key₀ (ident 1) [])
collision-deletes-reservation = refl
reservation-wins-selection : A.validSelection (remote key₀) (just (ident 1)) collision ≡ false
reservation-wins-selection = refl

changed : S.State
changed = record Trace.negotiated { cm = record (S.cm Trace.negotiated)
  { entries = put (ident 0) replacement (S.entries (S.cm Trace.negotiated)) } }
race : R.Frame
race = R.frame key₀ (R.waitIdle (ident 0) Trace.child) true
entry-change-wins-ready-timer : R.step 10 R.selectWakeup race changed ≡
  just (R.frame key₀ (R.complete (R.unsupported (just replacement))) true , changed)
entry-change-wins-ready-timer = refl
selectedTimeout : R.Frame
selectedTimeout = R.frame key₀ (R.timeoutWrite (ident 0) Trace.child) true
-- The source's later write does not recheck OutboundIdle after timeout selection.
later-timeout-write-is-separate : R.step 10 R.commitTimeout selectedTimeout changed ≡
  just (R.frame key₀ (R.count (R.cancel Trace.child (R.complete
    (R.success (just (S.terminating key₀ Trace.child nothing)))))) true ,
    record changed { cm = record (S.cm changed)
      { entries = put (ident 0) (S.terminating key₀ Trace.child nothing) (S.entries (S.cm changed)) } })
later-timeout-write-is-separate = refl

-- Initial acquire retries on terminal entries; an already captured inbound wait
-- returns a disconnection instead. These operations cannot share one case table.
initial-terminal-retries : C.acquireCase (S.terminated nothing) ≡ C.retry
initial-terminal-retries = refl
captured-terminal-returns : C.waitCase key₀ (S.terminated nothing) ≡ C.gone (C.disconnected key₀ (S.inTerminated nothing))
captured-terminal-returns = refl
