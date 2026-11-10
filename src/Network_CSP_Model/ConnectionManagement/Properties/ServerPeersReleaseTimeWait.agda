{-# OPTIONS --guardedness #-}

-- A release caller's cancellation that lands in its target's TIME_WAIT delay
-- (network 2f1c154, Core.hs 2032 and 667-668). The target comes from the
-- caller's own delivering frame and waits in cleanup with its current
-- capture. The step interrupts that wait and acknowledges the caller; it
-- neither acknowledges CM shutdown, publishes a handler result nor returns
-- the caller.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersReleaseTimeWait
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
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.ServerPeersReleaseReceipt as Receipt
import ConnectionManagement.Properties.ServerPeersMonitorJoins as Joins
import ConnectionManagement.Properties.ServerPeers as SharedFacts
import ConnectionManagement.ServerPeers as Combined

private
 module W = Exit b using
  (State; Frame; BodyResult; source; setSource; exits; shared; shutdown; phase; currentCapture;
   releaseTarget; timeWaitTarget; noteCleanup; step; deliverReleaseTimeWait;
   bufferScope; classifying; errorTracing; peerRethrow; nodeDelivery; nodeRethrow;
   bodyExited; finalizing; cleanupComplete; resultAvailable)

-- The handler the caller's throwTo reaches: finalizing, current, in TIME_WAIT.
record WaitingTarget (caller : WorkerId) (before : W.State) (target : WorkerId) : Set where
 constructor waiting-target
 field
  captured : Receipt.CapturedTarget b io caller before target
  frame : W.Frame
  frame-found : lookup target (W.exits before) ≡ just frame
  held : Shared.ConnectionState
  waiting : lookup target (Shared.cleanups (W.shared before)) ≡ just (Shared.cleanupWaiting held)
  result : W.BodyResult
  finalizing : W.phase frame ≡ W.finalizing result
  current : W.currentCapture target frame before ≡ true

waiting-observation : ∀ caller before {target} →
 W.timeWaitTarget caller before ≡ just target → WaitingTarget caller before target
waiting-observation caller before actual with W.releaseTarget caller before in selected
... | nothing = case actual of λ ()
... | just target with lookup target (W.exits before) in found | lookup target (Shared.cleanups (W.shared before)) in cleanup
...   | just f | just (Shared.cleanupWaiting h) with W.phase f in phase | W.currentCapture target f before in current
...     | W.finalizing r | true = case just-injective actual of λ { refl →
  waiting-target (Receipt.target-observation b io caller before selected) f found h cleanup r phase current }
...     | W.finalizing r | false = case actual of λ ()
...     | W.bufferScope _ | _ = case actual of λ ()
...     | W.classifying _ | _ = case actual of λ ()
...     | W.errorTracing _ _ | _ = case actual of λ ()
...     | W.peerRethrow _ | _ = case actual of λ ()
...     | W.nodeDelivery _ | _ = case actual of λ ()
...     | W.nodeRethrow _ | _ = case actual of λ ()
...     | W.bodyExited _ | _ = case actual of λ ()
...     | W.cleanupComplete _ _ | _ = case actual of λ ()
...     | W.resultAvailable _ _ | _ = case actual of λ ()
waiting-observation caller before actual | just target | nothing | _ = case actual of λ ()
waiting-observation caller before actual | just target | just f | nothing = case actual of λ ()
waiting-observation caller before actual | just target | just f | just Shared.cleanupAcquire = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupSelect _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupClose _ _ _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupPublish _ _ _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupRestore _ _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupFinalize _ _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupCount _) = case actual of λ ()
waiting-observation caller before actual | just target | just f | just (Shared.cleanupDone _) = case actual of λ ()

record TimeWaitReceipt (caller : WorkerId) (err : ErrorId) (before after : W.State) : Set where
 constructor timewait-receipt
 field
  target : WorkerId
  waiting : WaitingTarget caller before target
  interrupted nextSource : O.Configuration
  cleaned : O.advance (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source before) ≡ just interrupted
  acknowledged : O.advance (O.release caller (Release.cancellationDelivered target)) interrupted ≡ just nextSource
  after-shape : after ≡ record (W.setSource nextSource before) { exits = W.noteCleanup target (Cleanup.interruptTimeWait err) before }

timewait-observation : ∀ caller err before {after} →
 W.step (W.deliverReleaseTimeWait caller err) before ≡ just after → TimeWaitReceipt caller err before after
timewait-observation caller err before actual with W.timeWaitTarget caller before in selected
... | nothing = case actual of λ ()
... | just target with O.advance (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source before) in cleaned
...   | nothing = case actual of λ ()
...   | just interrupted with O.advance (O.release caller (Release.cancellationDelivered target)) interrupted in acknowledged
...     | nothing = case actual of λ ()
...     | just nextSource = timewait-receipt target (waiting-observation caller before selected)
 interrupted nextSource cleaned acknowledged (sym (just-injective actual))

-- Only the caller's acknowledgement and the target's own cleanup change; the
-- CM shutdown coordinator is untouched.
timewait-shutdown : ∀ {caller err before after} → TimeWaitReceipt caller err before after → W.shutdown after ≡ W.shutdown before
timewait-shutdown observed = cong W.shutdown (TimeWaitReceipt.after-shape observed)

module Frontend (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; advance; base)
  module J = Joins.Frontend b io capability using (physical; physical-lower; handler-event; handler-action)
  module K = Combined b io using (State; step; serverStep; serverAllowed; releaseCallerAllowed)
 timewait-event : WorkerId → ErrorId → T.Event
 timewait-event caller err = J.handler-event (W.deliverReleaseTimeWait caller err)
 physical-timewait : ∀ caller err before {after} →
  T.advance (timewait-event caller err) before ≡ just after → TimeWaitReceipt caller err (J.physical before) (J.physical after)
 physical-timewait caller err before actual = timewait-observation caller err (J.physical before)
  (J.physical-lower (W.deliverReleaseTimeWait caller err) before actual)

 -- The outer receipt keeps the governor-owned caller permission.
 private
  server-permitted : ∀ action before {after} →
   K.step (K.serverStep action) before ≡ just after → K.serverAllowed action before ≡ true
  server-permitted action before actual with K.serverAllowed action before in allowed
  ... | false = case actual of λ ()
  ... | true = refl
 timewait-permission : ∀ caller err before {after} →
  T.advance (timewait-event caller err) before ≡ just after → K.releaseCallerAllowed caller (T.base before) ≡ true
 timewait-permission caller err before actual with
  SharedFacts.Protocols.dispatch-observation b io capability (K.serverStep (J.handler-action (W.deliverReleaseTimeWait caller err))) before actual
 ... | next , advanced , same = server-permitted (J.handler-action (W.deliverReleaseTimeWait caller err)) (T.base before) advanced
