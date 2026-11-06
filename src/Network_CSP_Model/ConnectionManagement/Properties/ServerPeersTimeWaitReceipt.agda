{-# OPTIONS --guardedness #-}

-- A genuine TIME_WAIT delivery records the interrupted cleanup operation and
-- CM acknowledgement separately from its later finally and Async result.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersTimeWaitReceipt
 (b io : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; EntryId; HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
import ConnectionManagement.ServerPeers as Combined

private
 module W = Exit b
 module Handler = ExitFacts b using (Control; control; control-observation)

-- This intermediate state changes only the real cleanup source and its exit
-- metadata. The coordinator remains at its original awaited delivery.
interrupted : WorkerId → ErrorId → O.Configuration → W.State → W.State
interrupted worker err next before = record (W.setSource next before)
 { exits = W.noteCleanup worker (Cleanup.interruptTimeWait err) before }
interrupted-coordinator : ∀ worker err next before →
 W.shutdown (interrupted worker err next before) ≡ W.shutdown before
interrupted-coordinator worker err next before = refl

record Receipt (err : ErrorId) (before after : W.State) : Set where
 constructor receipt
 field
  entry : EntryId
  worker : WorkerId
  frame : W.Frame
  captured : Shared.ConnectionState
  original : W.BodyResult
  next : O.Configuration
  awaiting : Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker
  frame-found : lookup worker (W.exits before) ≡ just frame
  cleanup-found : lookup worker (Shared.cleanups (W.shared before)) ≡ just (Shared.cleanupWaiting captured)
  finalizing : W.phase frame ≡ W.finalizing original
  same-capture : W.currentCapture worker frame before ≡ true
  actual-interruption : O.advance (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err)))
    (W.source before) ≡ just next
  acknowledged : W.control Close.acknowledgeDelivery (interrupted worker err next before) ≡ just after

-- Invert the existing guarded action rather than taking an awaited worker,
-- cleanup phase, capture, interruption or membership as a caller premise.
receipt-observation : ∀ err before {after} →
 W.step (W.deliverShutdownTimeWait err) before ≡ just after → Receipt err before after
receipt-observation err before actual with Close.phase (W.shutdown before) in awaited
... | Close.awaitDelivery e worker with lookup worker (W.exits before) in found
 | lookup worker (Shared.cleanups (W.shared before)) in cleaned
...   | just frame | just (Shared.cleanupWaiting captured) with W.phase frame in phase
 | W.currentCapture worker frame before in matched
...     | W.finalizing original | true with O.advance
 (O.inbound (Machine.cleanupStep worker (Cleanup.interruptTimeWait err))) (W.source before) in advanced
...       | nothing = case actual of λ ()
...       | just next = receipt e worker frame captured original next awaited found cleaned phase matched advanced actual
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.finalizing original | false = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.bufferScope _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.classifying _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.errorTracing _ _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.peerRethrow _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.nodeDelivery _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.nodeRethrow _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.bodyExited _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.cleanupComplete _ _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupWaiting captured) | W.resultAvailable _ _ | _ = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just Shared.cleanupAcquire = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupSelect _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupClose _ _ _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupPublish _ _ _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupRestore _ _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupFinalize _ _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupCount _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | just (Shared.cleanupDone _) = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | just frame | nothing = case actual of λ ()
receipt-observation err before actual | Close.awaitDelivery e worker | nothing | _ = case actual of λ ()
receipt-observation err before actual | Close.initial = case actual of λ ()
receipt-observation err before actual | Close.reading = case actual of λ ()
receipt-observation err before actual | Close.sendReady _ _ = case actual of λ ()
receipt-observation err before actual | Close.awaitResults = case actual of λ ()
receipt-observation err before actual | Close.closed = case actual of λ ()

private
 acknowledgment-shape : ∀ current available before entry worker {after} →
  Close.phase before ≡ Close.awaitDelivery entry worker →
  Close.step current available Close.acknowledgeDelivery before ≡ just after →
  after ≡ record before { phase = Close.reading;
    collected = Close.collected before ++ (worker ∷ []) }
 acknowledgment-shape current available before entry worker awaited actual
  rewrite awaited = sym (just-injective actual)
 last-member : ∀ (workers : List WorkerId) worker → worker ∈ workers ++ (worker ∷ [])
 last-member [] worker = here refl
 last-member (head ∷ tail) worker = there (last-member tail worker)
 control-shape : ∀ before {after entry worker} →
  Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
  Handler.Control Close.acknowledgeDelivery before after →
  W.shutdown after ≡ record (W.shutdown before)
   { phase = Close.reading; collected = Close.collected (W.shutdown before) ++ (worker ∷ []) }
 control-shape before {entry = entry} {worker = worker} awaited (Handler.control successor primitiveStep refl) =
  acknowledgment-shape (Shared.cm (W.shared before)) (λ target → W.resultReady target before)
   (W.shutdown before) entry worker awaited primitiveStep

-- Only the actual acknowledgement appends this internally observed worker.
coordinator-shape : ∀ {err before after} (observed : Receipt err before after) →
 W.shutdown after ≡ record (W.shutdown before)
  { phase = Close.reading;
    collected = Close.collected (W.shutdown before) ++ (Receipt.worker observed ∷ []) }
coordinator-shape {err = err} {before = before} observed = trans
 (control-shape (interrupted (Receipt.worker observed) err (Receipt.next observed) before)
  (trans (cong Close.phase same) (Receipt.awaiting observed))
  (Handler.control-observation Close.acknowledgeDelivery _ (Receipt.acknowledged observed)))
 (cong (λ coordinator → record coordinator
  { phase = Close.reading; collected = Close.collected coordinator ++ (Receipt.worker observed ∷ []) }) same)
 where
 same = interrupted-coordinator (Receipt.worker observed) err (Receipt.next observed) before
collected-append : ∀ {err before after} (observed : Receipt err before after) →
 Close.collected (W.shutdown after) ≡ Close.collected (W.shutdown before) ++ (Receipt.worker observed ∷ [])
collected-append observed = cong Close.collected (coordinator-shape observed)
receipt-member : ∀ {err before after} (observed : Receipt err before after) →
 Receipt.worker observed ∈ Close.collected (W.shutdown after)
receipt-member {before = before} observed = subst (Receipt.worker observed ∈_)
 (sym (collected-append observed)) (last-member (Close.collected (W.shutdown before)) (Receipt.worker observed))
observed-worker : ∀ {err before after entry worker} (observed : Receipt err before after) →
 Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker → Receipt.worker observed ≡ worker
observed-worker observed known with trans (sym (Receipt.awaiting observed)) known
... | refl = refl
observed-entry : ∀ {err before after entry worker} (observed : Receipt err before after) →
 Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker → Receipt.entry observed ≡ entry
observed-entry observed known with trans (sym (Receipt.awaiting observed)) known
... | refl = refl

module Frontend (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; advance)
  module J = Joins.Frontend b io capability using (physical; physical-lower; handler-event)
 event : ErrorId → T.Event
 event err = J.handler-event (W.deliverShutdownTimeWait err)
 physical-receipt : ∀ err before {after} →
  T.advance (event err) before ≡ just after → Receipt err (J.physical before) (J.physical after)
 physical-receipt err before actual = receipt-observation err (J.physical before)
  (J.physical-lower (W.deliverShutdownTimeWait err) before actual)
