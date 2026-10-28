{-# OPTIONS --guardedness #-}

-- Post-startup mux outcomes, observed withBuffer exit, and the captured CM
-- finally. Source: ConnectionHandler.hs:286-309,378-380,450-452;
-- Core.hs:584-713 at 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Buffer-provider behavior, policy/trace return, and node delivery are explicit
-- observations. No new physical handler or copy of its JobPool is introduced.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxHandlerExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (local)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.MuxGroupShutdown as Group
module G = Group isBearerClosed
module M = G.M
module P = G.P
module U = G.U
module Pool = G.Pool

-- Peer policy wraps the synchronous exception; node policy sends that wrapper
-- to main but rethrows the original. Async exceptions bypass the classifier.
data BodyResult : Set where
  returned : BodyResult
  asyncException syncException peerException : ErrorId → BodyResult
data Phase : Set where
  bufferScope : G.Outcome → Phase
  classifying : ErrorId → Phase
  errorTracing : ErrorId → Life.Policy → Phase
  peerRethrow nodeDelivery nodeRethrow : ErrorId → Phase
  bodyExited finalizing : BodyResult → Phase
  cleanupComplete resultAvailable : BodyResult → Shared.CleanupOutcome → Phase
record Frame : Set where
  constructor exitFrame
  field captured : Shared.HandlerStart
        phase : Phase
        cleanupException : Maybe G.Outcome
open Frame public
record State : Set where
  constructor handlerExitState
  field base : G.State
        exits : Store WorkerId Frame
open State public
initial : O.Configuration → Maybe State
initial c with G.initial c
... | nothing = nothing
... | just g = just (handlerExitState g [])
source : State → O.Configuration
source s = G.source (base s)
setSource : O.Configuration → State → State
setSource c s = record s { base = G.setSource c (base s) }
poolAt : WorkerId → State → Pool.State
poolAt w s = G.poolAt w (base s)
physical : State → B.State
physical s = U.base (P.base (G.protocolState (base s)))
setPhysical : B.State → State → State
setPhysical b s = record s { base = G.setProtocols
  (record (G.protocolState (base s)) { base = record (P.base (G.protocolState (base s))) { base = b } }) (base s) }
shutdown : State → Close.State
shutdown s = B.shutdown (physical s)
setShutdown : Close.State → State → State
setShutdown c s = setPhysical (record (physical s) { shutdown = c }) s
shared : State → Shared.State
shared s = Machine.world (O.core (source s))
resultReady : WorkerId → State → Bool
resultReady w s with lookup w (exits s)
... | just f with phase f
...   | resultAvailable _ _ = true
...   | _ = false
resultReady w s | nothing with lookup w (U.frames (P.base (G.protocolState (base s))))
... | just _ = false
... | nothing = H.resultReady w (B.view (physical s))

-- Cleanup failure overrides any body outcome, retaining both in the record.
sameError : ErrorId → ErrorId → Bool
sameError e f = does (ErrorId.errorNumber e Nat.≟ ErrorId.errorNumber f)
effectiveResult : BodyResult → Shared.CleanupOutcome → Maybe G.Outcome → Maybe BodyResult
effectiveResult result Shared.cleanupNormal fault = just result
effectiveResult result (Shared.cleanupError err) (just (G.failedExit observed)) with sameError err observed
... | true = just (syncException err)
... | false = nothing
effectiveResult result (Shared.cleanupError err) (just (G.asyncExit observed)) with sameError err observed
... | true = just (asyncException err)
... | false = nothing
effectiveResult result (Shared.cleanupError err) _ = nothing
-- The value is exposed only at the physical Async-result publication boundary.
resultOf : WorkerId → State → Maybe BodyResult
resultOf w s with lookup w (exits s)
... | just f with phase f
...   | resultAvailable body outcome = effectiveResult body outcome (cleanupException f)
...   | _ = nothing
resultOf w s | nothing = nothing
sameCleanup : Shared.CleanupOutcome → Shared.CleanupOutcome → Bool
sameCleanup Shared.cleanupNormal Shared.cleanupNormal = true
sameCleanup (Shared.cleanupError e) (Shared.cleanupError f) = does (ErrorId.errorNumber e Nat.≟ ErrorId.errorNumber f)
sameCleanup _ _ = false
sameStart : Shared.HandlerStart → Shared.HandlerStart → Bool
sameStart h k = does (Shared.handlerEntry h ≟ Shared.handlerEntry k) ∧
  does (Shared.handlerSocket h ≟ Shared.handlerSocket k) ∧
  does (Shared.handlerPromise h ≟ Shared.handlerPromise k) ∧
  does (Shared.handlerKey h ≟ Shared.handlerKey k)
currentCapture : WorkerId → Frame → State → Bool
currentCapture w f s with lookup w (Shared.handlers (shared s))
... | nothing = false
... | just h = sameStart (captured f) h
phaseAfterBuffer : G.Outcome → Phase
phaseAfterBuffer G.normalExit = bodyExited returned
phaseAfterBuffer (G.failedExit err) = classifying err
phaseAfterBuffer (G.asyncExit err) = bodyExited (asyncException err)

-- Plans keep actual source effects separate from local bookkeeping. The only
-- interpreter below executes the real operation; a failed operation stays failed.
data Plan : Set where
  local : Store WorkerId Frame → Plan
  machine : O.Action → Store WorkerId Frame → Plan
  inherited : G.Action → Plan
  coordinator : Close.Action → Plan
  muxDelivery : WorkerId → ErrorId → Plan
  timeWaitDelivery : WorkerId → ErrorId → Plan
edit : WorkerId → Frame → Phase → State → Store WorkerId Frame
edit w f pc s = put w (record f { phase = pc }) (exits s)
-- Preserve the class of the ACTUAL cleanup fault: finally is outside the
-- handler classifier, and TIME_WAIT cancellation must remain asynchronous.
cleanupFault : Cleanup.CleanupAction → Maybe G.Outcome
cleanupFault (Cleanup.failSocketClose err) = just (G.failedExit err)
cleanupFault (Cleanup.interruptTimeWait err) = just (G.asyncExit err)
cleanupFault _ = nothing
noteCleanup : WorkerId → Cleanup.CleanupAction → State → Store WorkerId Frame
noteCleanup w action s with lookup w (exits s) | cleanupFault action
... | just f | just fault = put w (record f { cleanupException = just fault }) (exits s)
... | _ | _ = exits s

-- Old coordinator waits use the pre-handshake result oracle. Successful mux
-- owners instead use the combined physical result observation above.
delegateAllowed : G.Action → Bool
delegateAllowed (G.run (M.run (P.run (U.run (B.handler (H.shutdownStep _)))))) = false
delegateAllowed (G.run (M.run (P.run (U.run (B.handler H.acknowledgeFinished))))) = false
delegateAllowed _ = true

data Action : Set where
  run : G.Action → Action
  beginExit observeBufferReturn : WorkerId → Action
  observeBufferException : WorkerId → G.Outcome → Action
  choosePolicy : WorkerId → Life.Policy → Action
  observeErrorTrace observeNodeDelivery rethrow enterFinalizer finishCleanup publishAsyncResult : WorkerId → Action
  cleanup : WorkerId → Cleanup.CleanupAction → Action
  shutdownStep : Close.Action → Action
  deliverShutdownMux deliverShutdownTimeWait : ErrorId → Action
  acknowledgeFinished : Action

choose : Action → State → Maybe Plan
choose (run action) s with delegateAllowed action
... | true = just (inherited action)
... | false = nothing
choose (beginExit w) s with lookup w (exits s) | lookup w (U.frames (P.base (G.protocolState (base s)))) |
  G.phase (G.frameAt w (base s)) | Pool.phase (poolAt w s)
... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (Shared.handlers (shared s))
...   | just h with sameStart (U.captured f) h
...     | true = just (local (put w (exitFrame (U.captured f) (bufferScope outcome) nothing) (exits s)))
...     | false = nothing
choose (beginExit w) s | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = nothing
choose (beginExit w) s | _ | _ | _ | _ = nothing
choose (observeBufferReturn w) s with lookup w (exits s)
... | just f with phase f
...   | bufferScope outcome = just (local (edit w f (phaseAfterBuffer outcome) s))
...   | _ = nothing
choose (observeBufferReturn w) s | nothing = nothing
-- An observed exception from the provider can replace the mux outcome. Normal
-- return is a separate observation, never an exception-to-success conversion.
choose (observeBufferException w G.normalExit) s = nothing
choose (observeBufferException w outcome@(G.failedExit err)) s with lookup w (exits s)
... | just f with phase f
...   | bufferScope _ = just (local (edit w f (phaseAfterBuffer outcome) s))
...   | _ = nothing
choose (observeBufferException w (G.failedExit err)) s | nothing = nothing
choose (observeBufferException w outcome@(G.asyncExit err)) s with lookup w (exits s)
... | just f with phase f
...   | bufferScope _ = just (local (edit w f (phaseAfterBuffer outcome) s))
...   | _ = nothing
choose (observeBufferException w (G.asyncExit err)) s | nothing = nothing
choose (choosePolicy w policy) s with lookup w (exits s)
... | just f with phase f
...   | classifying err = just (local (edit w f (errorTracing err policy) s))
...   | _ = nothing
choose (choosePolicy w policy) s | nothing = nothing
choose (observeErrorTrace w) s with lookup w (exits s)
... | just f with phase f
...   | errorTracing err Life.shutdownPeer = just (local (edit w f (peerRethrow err) s))
...   | errorTracing err Life.shutdownNode = just (local (edit w f (nodeDelivery err) s))
...   | _ = nothing
choose (observeErrorTrace w) s | nothing = nothing
choose (observeNodeDelivery w) s with lookup w (exits s)
... | just f with phase f
...   | nodeDelivery err = just (local (edit w f (nodeRethrow err) s))
...   | _ = nothing
choose (observeNodeDelivery w) s | nothing = nothing
choose (rethrow w) s with lookup w (exits s)
... | just f with phase f
...   | peerRethrow err = just (local (edit w f (bodyExited (peerException err)) s))
...   | nodeRethrow err = just (local (edit w f (bodyExited (syncException err)) s))
...   | _ = nothing
choose (rethrow w) s | nothing = nothing
choose (enterFinalizer w) s with lookup w (exits s)
... | just f with phase f | currentCapture w f s
...   | bodyExited result | true = just (machine (O.inbound (Machine.handlerExit w)) (edit w f (finalizing result) s))
...   | _ | _ = nothing
choose (enterFinalizer w) s | nothing = nothing
choose (cleanup w action) s with lookup w (exits s)
... | just f with phase f | currentCapture w f s
...   | finalizing _ | true = just (machine (O.inbound (Machine.cleanupStep w action)) (noteCleanup w action s))
...   | _ | _ = nothing
choose (cleanup w action) s | nothing = nothing
choose (finishCleanup w) s with lookup w (exits s) | lookup w (Shared.cleanups (shared s))
... | just f | just (Shared.cleanupDone outcome) with phase f
...   | finalizing result with effectiveResult result outcome (cleanupException f)
...     | just _ = just (local (edit w f (cleanupComplete result outcome) s))
...     | nothing = nothing
choose (finishCleanup w) s | just f | just (Shared.cleanupDone outcome) | _ = nothing
choose (finishCleanup w) s | _ | _ = nothing
choose (publishAsyncResult w) s with lookup w (exits s) | lookup w (Shared.cleanups (shared s))
... | just f | just (Shared.cleanupDone outcome) with phase f
...   | cleanupComplete result observed with sameCleanup observed outcome
...     | true = just (local (edit w f (resultAvailable result outcome) s))
...     | false = nothing
choose (publishAsyncResult w) s | just f | just (Shared.cleanupDone outcome) | _ = nothing
choose (publishAsyncResult w) s | _ | _ = nothing
choose (shutdownStep Close.acknowledgeDelivery) s = nothing
choose (shutdownStep action) s = just (coordinator action)
choose (deliverShutdownMux err) s with Close.phase (shutdown s)
... | Close.awaitDelivery e w = just (muxDelivery w err)
... | _ = nothing
choose (deliverShutdownTimeWait err) s with Close.phase (shutdown s)
... | Close.awaitDelivery e w with lookup w (exits s) | lookup w (Shared.cleanups (shared s))
...   | just f | just (Shared.cleanupWaiting _) with phase f | currentCapture w f s
...     | finalizing _ | true = just (timeWaitDelivery w err)
...     | _ | _ = nothing
choose (deliverShutdownTimeWait err) s | Close.awaitDelivery e w | _ | _ = nothing
choose (deliverShutdownTimeWait err) s | _ = nothing
choose acknowledgeFinished s with Close.phase (shutdown s)
... | Close.awaitDelivery e w with resultReady w s
...   | true = just (coordinator Close.acknowledgeDelivery)
...   | false = nothing
choose acknowledgeFinished s | _ = nothing

control : Close.Action → State → Maybe State
control action s with Close.step (Shared.cm (shared s)) (λ w → resultReady w s) action (shutdown s)
... | nothing = nothing
... | just next = just (setShutdown next s)
enact : Plan → State → Maybe State
enact (local fs) s = just (record s { exits = fs })
enact (machine action fs) s with O.advance action (source s)
... | nothing = nothing
... | just c = just (record (setSource c s) { exits = fs })
enact (inherited action) s with G.step action (base s)
... | nothing = nothing
... | just g = just (record s { base = g })
enact (coordinator action) s = control action s
enact (muxDelivery w err) s with G.step (G.abortOwner w err) (base s)
... | nothing = nothing
... | just g = control Close.acknowledgeDelivery (record s { base = g })
enact (timeWaitDelivery w err) s with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (source s)
... | nothing = nothing
... | just c = control Close.acknowledgeDelivery (record (setSource c s) { exits = noteCleanup w (Cleanup.interruptTimeWait err) s })
step : Action → State → Maybe State
step action s with choose action s
... | nothing = nothing
... | just plan = enact plan s

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
