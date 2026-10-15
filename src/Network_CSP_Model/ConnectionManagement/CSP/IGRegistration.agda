{-# OPTIONS --guardedness #-}

-- First-batch registration traces, conditional on abstract handler publication
-- and successful responder startup. No source-reachability/deadlock claim.
module ConnectionManagement.CSP.IGRegistration where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.Scope
open import ConnectionManagement.CSP.Fixtures
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (info; success)
open import ConnectionManagement.Properties.Ownership using (Ownership)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.Scenarios.OwnershipInvariant as Ownership
import ConnectionManagement.Scenarios.SupplyInvariant as Supply
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Handshake as H
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- CM completes notification and return without registering any responders.
notify : List Action
notify = handshakeStep w₀ H.readResultCounters ∷ handshakeStep w₀ H.enqueueInbound ∷
  handshakeStep w₀ H.returnResult ∷ []

notified : Configuration
notified = snapshot idle (full binding) (completedHandshake (connected info))
  (handling child₀) resultStore (info ∷ []) []

notify-path : Executes committed notify notified
notify-path = next {c₁ = counted} refl (next {c₁ = enqueued} refl (next refl done))
  where
  counted = snapshot idle (full binding) (notifyInbound info) (handling child₀) resultStore [] []
  enqueued = snapshot idle (full binding) (returnHandshake (connected info)) (handling child₀) resultStore (info ∷ []) []

-- Explicit snapshots keep the trace proof from normalizing a long replay.
withIG : Configuration → IG.Runtime → List NewConnectionInfo → Configuration
withIG c ig queue = record c { inboundGovernor = ig ; world = record (world c) { inboundInfo = queue } }

timeRead timerArmed drained eventRead prepared registered : Configuration
timeRead = withIG notified (IG.runtime IG.emptyPublished 0 (IG.armInactivity 10)) (info ∷ [])
timerArmed = withIG notified (IG.runtime IG.emptyPublished 1 (IG.awaitFirstBatch 10 (ident 0))) (info ∷ [])
drained = withIG notified (IG.runtime IG.emptyPublished 1 (IG.readNext 10 (info ∷ []))) []
eventRead = withIG notified (IG.runtime IG.emptyPublished 1 (IG.prepareNew 10 info [] IG.emptyPublished)) []
prepared = withIG notified (IG.runtime IG.emptyPublished 2 (IG.startResponders 10 info [] IG.emptyPublished (ident 1))) []

registeredState : IG.Published
registeredState = IG.published ((key₀ , IG.registered info (ident 1)) ∷ [])
  ((remote key₀ , IG.freshPeer 10 (ident 0)) ∷ [])
registered = withIG notified (IG.runtime registeredState 2 (IG.readNext 10 [])) []

register : List Action
register = igStep (IG.captureTime 10) ∷ igStep IG.registerInactivity ∷
  igStep IG.drainFirstBatch ∷ igStep IG.readEvent ∷ igStep IG.registerIdleTimer ∷
  igStep IG.successfulResponderStart ∷ []

register-path : Executes notified register registered
register-path = next {c₁ = timeRead} refl (next {c₁ = timerArmed} refl
  (next {c₁ = drained} refl (next {c₁ = eventRead} refl
  (next {c₁ = prepared} refl (next refl done)))))

lifecycle : List Action
lifecycle = admit ++ (handlerPublication child₀ success resultWritten ∷ []) ++ consume ++ notify ++ register

lifecycle-path : Executes start lifecycle registered
lifecycle-path = exec-append admit-path (exec-append publication-path
  (exec-append consume-path (exec-append notify-path register-path)))

registration-trace : traces (Process start) (map label lifecycle)
registration-trace = trace-intro lifecycle-path

registration-hidden-trace : traces (HiddenProcess start) (map label (project lifecycle))
registration-hidden-trace = hidden-trace lifecycle-path

-- Existing invariants now quantify over the extended action datatype too.
registration-owned : Ownership (world registered)
registration-owned = Ownership.from-start lifecycle-path
registration-supply-bounded : SupplyBounds (world registered)
registration-supply-bounded = Supply.from-start lifecycle-path

-- Atomic startup/publication: preparation has no registry entry, and the success
-- step both establishes registration and advances the cursor. No split start.
not-yet-registered : IG.connections (IG.publishedState (inboundGovernor prepared)) ≡ []
not-yet-registered = refl
registered-handle-and-timer : lookup key₀ (IG.connections (IG.publishedState (inboundGovernor registered)))
  ≡ just (IG.registered info (ident 1))
registered-handle-and-timer = refl
empty-queue-before-registration : inboundInfo (world drained) ≡ []
empty-queue-before-registration = refl
startup-before-read-refused : advance (igStep IG.successfulResponderStart) drained ≡ nothing
startup-before-read-refused = refl
no-premature-start-trace : ¬ traces (Process drained) (map label (igStep IG.successfulResponderStart ∷ []))
no-premature-start-trace = refused-extension done startup-before-read-refused
no-second-drain : advance (igStep IG.drainFirstBatch) registered ≡ nothing
no-second-drain = refl
at-next-batch-frontier : igFrontier (inboundGovernor registered) ≡ just igNextBatch
at-next-batch-frontier = refl

-- Local duplicate fixture: a second notification of the SAME key but a different
-- handle/capability must not replace the existing registration, timer or freshness.
-- This is a branch check, not a source-reachability claim for the injected message.
replacementInfo : NewConnectionInfo
replacementInfo = newConnectionInfo outbound key₀ unidirectional (ident 9)

duplicateBatch duplicateRead duplicateCommitted : Configuration
duplicateBatch = withIG registered (IG.runtime registeredState 2 (IG.readNext 10 (replacementInfo ∷ []))) []
duplicateRead = withIG registered (IG.runtime registeredState 2 (IG.publishDuplicate 10 [] registeredState)) []
duplicateCommitted = registered

duplicate-keeps-state : Executes duplicateBatch
  (igStep IG.readEvent ∷ igStep IG.commitDuplicate ∷ []) duplicateCommitted
duplicate-keeps-state = next {c₁ = duplicateRead} refl (next refl done)

duplicate-does-not-arm-timer : advance (igStep IG.registerIdleTimer) duplicateRead ≡ nothing
duplicate-does-not-arm-timer = refl

-- Branch check: unidirectional registration never adds a fresh duplex peer.
unidirectional-no-freshness : IG.addFresh 10 replacementInfo IG.emptyPublished ≡ []
unidirectional-no-freshness = refl

-- A CM enqueue can happen after the batch drain. It stays in the live queue;
-- completing the captured batch does not absorb or discard this later message.
producerPending : Configuration
producerPending = withIG
  (snapshot idle (full binding) (notifyInbound info) (handling child₀) resultStore [] [])
  (inboundGovernor prepared) []
producerEnqueued : Configuration
producerEnqueued = withIG
  (snapshot idle (full binding) (returnHandshake (connected info)) (handling child₀) resultStore (info ∷ []) [])
  (inboundGovernor prepared) (info ∷ [])
lateMessageRetained : Configuration
lateMessageRetained = withIG producerEnqueued (inboundGovernor registered) (info ∷ [])

late-enqueue-path : Executes producerPending
  (handshakeStep w₀ H.enqueueInbound ∷ igStep IG.successfulResponderStart ∷ []) lateMessageRetained
late-enqueue-path = next {c₁ = producerEnqueued} refl (next refl done)

late-enqueue-trace : traces (Process producerPending)
  (map label (handshakeStep w₀ H.enqueueInbound ∷ igStep IG.successfulResponderStart ∷ []))
late-enqueue-trace = trace-intro late-enqueue-path

initiatorOnly : Configuration
initiatorOnly = record notified { responder = noResponderMode }
no-IG-in-initiator-only : advance (igStep (IG.captureTime 10)) initiatorOnly ≡ nothing
no-IG-in-initiator-only = refl
