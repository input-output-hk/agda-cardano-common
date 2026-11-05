{-# OPTIONS --guardedness #-}

-- An actual finished-target acknowledgment retains the exact physical result
-- branch and captured CM identity. This local observation does not reconstruct
-- an earlier readEntry, establish initialization, or complete CM's final wait.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersFinishedReceipt
 (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (WorkerId; EntryId; HandleId)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.MuxHandlerSupervision as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins

private
 module W = Exit isBearerClosed using
  (State; Frame; BodyResult; phase; exits; resultAvailable; cleanupComplete;
   bufferScope; classifying; errorTracing; peerRethrow; nodeDelivery; nodeRethrow;
   bodyExited; finalizing; resultReady; physical; base; shutdown; setShutdown;
   control; step; choose; coordinator; acknowledgeFinished; shared)
 module G = Group isBearerClosed using (protocolState)
 module U = Mux Types.TypedResult using (Frame; frames)
 module Handler = ExitFacts isBearerClosed using
  (Control; control; control-observation; successor; actual-step; after-shape)
 module K = Combined isBearerClosed isIOManagerError

-- The fallback oracle reads the original physical registry only when neither
-- an exit frame nor a negotiated mux frame masks that registry's observation.
raw : W.State → H.State
raw s = B.view (W.physical s)
mux-frames : W.State → Store WorkerId U.Frame
mux-frames s = U.frames (P.base (G.protocolState (W.base s)))

data Ready (worker : WorkerId) (state : W.State) : Set where
 mux-result : (savedFrame : W.Frame) (body : W.BodyResult)
  (outcome : Shared.CleanupOutcome) →
  lookup worker (W.exits state) ≡ just savedFrame →
  W.phase savedFrame ≡ W.resultAvailable body outcome → Ready worker state
 handshake-result : (thread : H.Thread) (original : ErrorId)
  (outcome : Shared.CleanupOutcome) →
  lookup worker (W.exits state) ≡ nothing →
  lookup worker (mux-frames state) ≡ nothing →
  lookup worker (H.threads (raw state)) ≡ just thread →
  H.phase thread ≡ H.resultAvailable original outcome → Ready worker state

-- No body/finally cause is collapsed: mux Frame retains cleanupException, while
-- the handshake alternative retains both original error and cleanup outcome.
ready-observation : ∀ worker state → W.resultReady worker state ≡ true → Ready worker state
ready-observation worker state ready with lookup worker (W.exits state) in found
... | just savedFrame with W.phase savedFrame in pc
...   | W.resultAvailable body outcome = mux-result savedFrame body outcome found pc
ready-observation worker state () | just savedFrame | W.bufferScope outcome
ready-observation worker state () | just savedFrame | W.classifying err
ready-observation worker state () | just savedFrame | W.errorTracing err policy
ready-observation worker state () | just savedFrame | W.peerRethrow err
ready-observation worker state () | just savedFrame | W.nodeDelivery err
ready-observation worker state () | just savedFrame | W.nodeRethrow err
ready-observation worker state () | just savedFrame | W.bodyExited body
ready-observation worker state () | just savedFrame | W.finalizing body
ready-observation worker state () | just savedFrame | W.cleanupComplete body outcome
ready-observation worker state ready | nothing with lookup worker (mux-frames state) in muxFound
... | just muxFrame = case ready of λ ()
... | nothing with lookup worker (H.threads (raw state)) in threadFound
...   | nothing = case ready of λ ()
...   | just thread with H.phase thread in pc
...     | H.resultAvailable original outcome = handshake-result thread original outcome found muxFound threadFound pc
ready-observation worker state () | nothing | nothing | just thread | H.maskedSetup
ready-observation worker state () | nothing | nothing | just thread | H.handshaking
ready-observation worker state () | nothing | nothing | just thread | H.caughtCancellation err
ready-observation worker state () | nothing | nothing | just thread | H.cancellationPublished err
ready-observation worker state () | nothing | nothing | just thread | H.bodyExited err
ready-observation worker state () | nothing | nothing | just thread | H.finalizing err
ready-observation worker state () | nothing | nothing | just thread | H.cleanupComplete err outcome

-- Identity and availability are outputs of the real acknowledgeFinished guard;
-- the primitive coordinator step remains attached to the same physical states.
record Receipt (before after : W.State) : Set where
 constructor finished-receipt
 field
  entry : EntryId
  worker : WorkerId
  awaiting : Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker
  ready : W.resultReady worker before ≡ true
  result : Ready worker before
  actual : W.step W.acknowledgeFinished before ≡ just after
  acknowledged : Handler.Control Close.acknowledgeDelivery before after

private
 finished-choice : ∀ before entry worker →
  Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
  W.resultReady worker before ≡ true →
  W.choose W.acknowledgeFinished before ≡ just (W.coordinator Close.acknowledgeDelivery)
 finished-choice before entry worker awaited ready rewrite awaited | ready = refl

 finished-computation : ∀ before entry worker →
  Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
  W.resultReady worker before ≡ true →
  W.step W.acknowledgeFinished before ≡ W.control Close.acknowledgeDelivery before
 finished-computation before entry worker awaited ready
  rewrite finished-choice before entry worker awaited ready = refl

receipt-observation : ∀ before {after} →
 W.step W.acknowledgeFinished before ≡ just after → Receipt before after
receipt-observation before actual with Close.phase (W.shutdown before) in awaited
... | Close.awaitDelivery entry worker with W.resultReady worker before in ready
...   | true = finished-receipt entry worker awaited ready
 (ready-observation worker before ready)
 (trans (finished-computation before entry worker awaited ready) actual)
 (Handler.control-observation Close.acknowledgeDelivery before actual)
...   | false = case actual of λ ()
receipt-observation before actual | Close.initial = case actual of λ ()
receipt-observation before actual | Close.reading = case actual of λ ()
receipt-observation before actual | Close.sendReady entry worker = case actual of λ ()
receipt-observation before actual | Close.awaitResults = case actual of λ ()
receipt-observation before actual | Close.closed = case actual of λ ()

private
 acknowledgment-shape : ∀ current available before entry worker {after} →
  Close.phase before ≡ Close.awaitDelivery entry worker →
  Close.step current available Close.acknowledgeDelivery before ≡ just after →
  after ≡ record before { phase = Close.reading;
   collected = Close.collected before ++ (worker ∷ []) }
 acknowledgment-shape current available before entry worker awaited actual
  rewrite awaited = sym (just-injective actual)

coordinator-shape : ∀ {before after} (receipt : Receipt before after) →
 W.shutdown after ≡ record (W.shutdown before)
  { phase = Close.reading;
    collected = Close.collected (W.shutdown before) ++ (Receipt.worker receipt ∷ []) }
coordinator-shape {before} receipt with Receipt.acknowledged receipt
... | Handler.control successor primitiveStep refl = acknowledgment-shape (Shared.cm (W.shared before)) (λ worker → W.resultReady worker before) (W.shutdown before)
 (Receipt.entry receipt) (Receipt.worker receipt) (Receipt.awaiting receipt) primitiveStep

collected-append : ∀ {before after} (receipt : Receipt before after) →
 Close.collected (W.shutdown after) ≡
 Close.collected (W.shutdown before) ++ (Receipt.worker receipt ∷ [])
collected-append receipt = cong Close.collected (coordinator-shape receipt)

private
 last-member : ∀ (workers : List WorkerId) worker → worker ∈ workers ++ (worker ∷ [])
 last-member [] worker = here refl
 last-member (head ∷ tail) worker = there (last-member tail worker)

receipt-member : ∀ {before after} (receipt : Receipt before after) →
 Receipt.worker receipt ∈ Close.collected (W.shutdown after)
receipt-member {before} receipt = subst (Receipt.worker receipt ∈_)
 (sym (collected-append receipt))
 (last-member (Close.collected (W.shutdown before)) (Receipt.worker receipt))

private
 awaiting-identities : ∀ {entry worker otherEntry otherWorker} →
  Close.awaitDelivery entry worker ≡ Close.awaitDelivery otherEntry otherWorker →
  (entry ≡ otherEntry) × (worker ≡ otherWorker)
 awaiting-identities refl = refl , refl

observed-worker : ∀ {before after entry worker} (receipt : Receipt before after) →
 Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
 Receipt.worker receipt ≡ worker
observed-worker receipt known = proj₂
 (awaiting-identities (trans (sym (Receipt.awaiting receipt)) known))

observed-entry : ∀ {before after entry worker} (receipt : Receipt before after) →
 Close.phase (W.shutdown before) ≡ Close.awaitDelivery entry worker →
 Receipt.entry receipt ≡ entry
observed-entry receipt known = proj₁
 (awaiting-identities (trans (sym (Receipt.awaiting receipt)) known))

-- Reuse the existing complete handler-event lowering; no wrapper permissions
-- or controller dispatch are reimplemented here.
module Frontend (canInitiate : HandleId → ℕ → Bool) where
 private
  module T = K.Protocols canInitiate using (Runtime; advance)
  module J = Joins.Frontend isBearerClosed isIOManagerError canInitiate using
   (handler-event; physical; physical-lower)
 event = J.handler-event W.acknowledgeFinished
 physical-receipt : ∀ before {after} →
  T.advance event before ≡ just after → Receipt (J.physical before) (J.physical after)
 physical-receipt before actual = receipt-observation (J.physical before)
  (J.physical-lower W.acknowledgeFinished before actual)
