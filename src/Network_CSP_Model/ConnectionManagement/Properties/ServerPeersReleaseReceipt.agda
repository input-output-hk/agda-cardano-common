{-# OPTIONS --guardedness #-}

-- Release receipts belong to the actual delivering caller. They neither
-- acknowledge CM nor return the caller nor supply a future physical result.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersReleaseReceipt
 (b io : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import ConnectionManagement.Domain using (WorkerId; HandleId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.Properties.ServerPeersFinishedReceipt as FinishedFacts
import ConnectionManagement.Properties.ServerPeersMuxReceipt as MuxFacts
import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
import ConnectionManagement.Properties.ServerPeers as Shared
import ConnectionManagement.ServerPeers as Combined

private
 module W = Exit b using
  (State; source; setSource; base; exits; releaseTarget; step; deliverReleaseMux;
   acknowledgeReleaseFinished; resultReady; shutdown)
 module G = Group b using (State; step; abortOwner; source)
 module Ready = FinishedFacts b io using (Ready; ready-observation)
 module Mux = MuxFacts b io using (abort-coordinator)

-- The source frame, not a current CM map binding, determines throwTo's target.
record CapturedTarget (caller : WorkerId) (before : W.State) (target : WorkerId) : Set where
 constructor captured-target
 field
  saved : Release.Frame
  continuation : Release.PC
  frame-found : lookup caller (O.releasing (W.source before)) ≡ just saved
  delivering : Release.pc saved ≡ Release.delivering target continuation

target-observation : ∀ caller before {target} →
 W.releaseTarget caller before ≡ just target → CapturedTarget caller before target
target-observation caller before actual with lookup caller (O.releasing (W.source before)) in found
... | nothing = case actual of λ ()
... | just saved with Release.pc saved in phase
...   | Release.delivering target next with just-injective actual
...     | refl = captured-target saved next found phase
target-observation caller before actual | just saved | Release.transaction = case actual of λ ()
target-observation caller before actual | just saved | Release.check _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.count _ = case actual of λ ()
target-observation caller before actual | just saved | Release.armTimer _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.waitIdle _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.timeoutWrite _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.cancel _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.prune _ _ = case actual of λ ()
target-observation caller before actual | just saved | Release.complete _ = case actual of λ ()

record LiveReceipt (caller : WorkerId) (err : ErrorId) (before after : W.State) : Set where
 constructor live-receipt
 field
  target : WorkerId
  captured : CapturedTarget caller before target
  nextGroup : G.State
  nextSource : O.Configuration
  delivered : G.step (G.abortOwner target err) (W.base before) ≡ just nextGroup
  acknowledged : O.advance (O.release caller (Release.cancellationDelivered target))
    (G.source nextGroup) ≡ just nextSource
  after-shape : after ≡ W.setSource nextSource (record before { base = nextGroup })

live-observation : ∀ caller err before {after} →
 W.step (W.deliverReleaseMux caller err) before ≡ just after → LiveReceipt caller err before after
live-observation caller err before actual with W.releaseTarget caller before in selected
... | nothing = case actual of λ ()
... | just target with G.step (G.abortOwner target err) (W.base before) in delivered
...   | nothing = case actual of λ ()
...   | just nextGroup with O.advance (O.release caller (Release.cancellationDelivered target))
 (G.source nextGroup) in acknowledged
...     | nothing = case actual of λ ()
...     | just nextSource = live-receipt target (target-observation caller before selected)
 nextGroup nextSource delivered acknowledged (sym (just-injective actual))

record FinishedReceipt (caller : WorkerId) (before after : W.State) : Set where
 constructor finished-receipt
 field
  target : WorkerId
  captured : CapturedTarget caller before target
  ready : Ready.Ready target before
  nextSource : O.Configuration
  acknowledged : O.advance (O.release caller (Release.cancellationDelivered target))
    (W.source before) ≡ just nextSource
  after-shape : after ≡ record (W.setSource nextSource before) { exits = W.exits before }

finished-observation : ∀ caller before {after} →
 W.step (W.acknowledgeReleaseFinished caller) before ≡ just after → FinishedReceipt caller before after
finished-observation caller before actual with W.releaseTarget caller before in selected
... | nothing = case actual of λ ()
... | just target with W.resultReady target before in available
...   | false = case actual of λ ()
...   | true with O.advance (O.release caller (Release.cancellationDelivered target)) (W.source before) in acknowledged
...     | nothing = case actual of λ ()
...     | just nextSource = finished-receipt target (target-observation caller before selected)
 (Ready.ready-observation target before available) nextSource acknowledged (sym (just-injective actual))

private
 source-shutdown : ∀ next before → W.shutdown (W.setSource next before) ≡ W.shutdown before
 source-shutdown next before = refl

-- Only the release caller's source acknowledgement occurs in these events.
-- CM collection and its later collective wait remain independent obligations.
live-shutdown : ∀ {caller err before after} → LiveReceipt caller err before after → W.shutdown after ≡ W.shutdown before
live-shutdown {err = err} {before = before} observed = trans (cong W.shutdown (LiveReceipt.after-shape observed))
 (trans (source-shutdown (LiveReceipt.nextSource observed) (record before { base = LiveReceipt.nextGroup observed }))
  (Mux.abort-coordinator (LiveReceipt.target observed) err before (LiveReceipt.delivered observed)))
finished-shutdown : ∀ {caller before after} → FinishedReceipt caller before after → W.shutdown after ≡ W.shutdown before
finished-shutdown {before = before} observed = trans (cong W.shutdown (FinishedReceipt.after-shape observed))
 (source-shutdown (FinishedReceipt.nextSource observed) before)

module Frontend (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; advance; base)
  module J = Joins.Frontend b io capability using (physical; physical-lower; handler-event; handler-action)
  module K = Combined b io using (State; step; serverStep; serverAllowed; releaseCallerAllowed)
 live-event : WorkerId → ErrorId → T.Event
 live-event caller err = J.handler-event (W.deliverReleaseMux caller err)
 finished-event : WorkerId → T.Event
 finished-event caller = J.handler-event (W.acknowledgeReleaseFinished caller)
 physical-live : ∀ caller err before {after} →
  T.advance (live-event caller err) before ≡ just after → LiveReceipt caller err (J.physical before) (J.physical after)
 physical-live caller err before actual = live-observation caller err (J.physical before)
  (J.physical-lower (W.deliverReleaseMux caller err) before actual)
 physical-finished : ∀ caller before {after} →
  T.advance (finished-event caller) before ≡ just after → FinishedReceipt caller (J.physical before) (J.physical after)
 physical-finished caller before actual = finished-observation caller (J.physical before)
  (J.physical-lower (W.acknowledgeReleaseFinished caller) before actual)

 -- Outer receipts retain the existing governor-owned caller permissions.
 private
  server-permitted : ∀ action before {after} →
   K.step (K.serverStep action) before ≡ just after → K.serverAllowed action before ≡ true
  server-permitted action before actual with K.serverAllowed action before in allowed
  ... | false = case actual of λ ()
  ... | true = refl
  frontend-permitted : ∀ action before {after} →
   T.advance (J.handler-event action) before ≡ just after →
   K.serverAllowed (J.handler-action action) (T.base before) ≡ true
  frontend-permitted action before actual with
   Shared.Protocols.dispatch-observation b io capability (K.serverStep (J.handler-action action)) before actual
  ... | next , advanced , same = server-permitted (J.handler-action action) (T.base before) advanced
 live-permission : ∀ caller err before {after} →
  T.advance (live-event caller err) before ≡ just after → K.releaseCallerAllowed caller (T.base before) ≡ true
 live-permission caller err before actual = frontend-permitted (W.deliverReleaseMux caller err) before actual
 finished-permission : ∀ caller before {after} →
  T.advance (finished-event caller) before ≡ just after → K.releaseCallerAllowed caller (T.base before) ≡ true
 finished-permission caller before actual = frontend-permitted (W.acknowledgeReleaseFinished caller) before actual
