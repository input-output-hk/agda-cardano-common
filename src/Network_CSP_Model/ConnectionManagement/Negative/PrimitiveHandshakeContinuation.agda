{-# OPTIONS --guardedness #-}

-- G1 F4: helper ProtocolLimitFailure return, actual Left/query publication,
-- masked-interruptible query delay, and transfer to the existing outer finally.
-- These local dispatcher controls do not assert an initialized whole-system run.
module ConnectionManagement.Negative.PrimitiveHandshakeContinuation where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxHandlerSupervision as Mux
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as F
module U = Mux Types.TypedResult
module W = Exit F.bearerClosed
module G = W.G
module P = W.P
module Monitor = W.M

start : U.State
start = P.base F.p8
next : HS.Event → U.State → U.State
next e s with U.step (U.handshakeStep F.owner e) s
... | just t = t
... | nothing = s
at : U.State → Maybe HS.PC
at s with lookup F.owner (U.frames s)
... | just f with U.progress f
...   | U.handshakePending pc = just pc
...   | _ = nothing
at s | nothing = nothing

t₀ t₁ t₂ q₀ q₁ q₂ q₃ qCancel : U.State
t₀ = next (HS.limitReturned HS.deadline (errorId 4)) start
t₁ = next (HS.continue HS.publish) t₀
t₂ = next (HS.continue HS.traceReturned) t₁
q₀ = next HS.queryReturned start
q₁ = next (HS.continue HS.publish) q₀
q₂ = next (HS.continue HS.traceReturned) q₁
q₃ = next (HS.continue HS.delayElapsed) q₂
qCancel = next (HS.continue (HS.cancelDelay (errorId 8))) q₂

timeout-enabled : U.step (U.handshakeStep F.owner (HS.limitReturned HS.deadline (errorId 4))) start ≡ just t₀
timeout-enabled = refl
timeout-published : U.step (U.handshakeStep F.owner (HS.continue HS.publish)) t₀ ≡ just t₁
timeout-published = refl
timeout-result : lookup (S.handlerPromise F.captured) (S.handshakeResults (Machine.world (O.core (U.source t₁)))) ≡ just (S.handlerError S.protocolViolation (errorId 4))
timeout-result = refl
timeout-helper-returns : at t₂ ≡ just (HS.exited (HS.protocolLimit HS.deadline (errorId 4)) HS.normal)
timeout-helper-returns = refl
query-enabled : U.step (U.handshakeStep F.owner HS.queryReturned) start ≡ just q₀
query-enabled = refl
query-published : U.step (U.handshakeStep F.owner (HS.continue HS.publish)) q₀ ≡ just q₁
query-published = refl
query-result : lookup (S.handlerPromise F.captured) (S.handshakeResults (Machine.world (O.core (U.source q₁)))) ≡ just S.query
query-result = refl
query-trace-then-delay : at q₂ ≡ just HS.sleeping
query-trace-then-delay = refl
query-delay-elapses : at q₃ ≡ just (HS.exited HS.query HS.normal)
query-delay-elapses = refl
query-delay-cancelled : at qCancel ≡ just (HS.exited HS.query (HS.async (errorId 8)))
query-delay-cancelled = refl
query-kept-on-cancel : lookup (S.handlerPromise F.captured) (S.handshakeResults (Machine.world (O.core (U.source qCancel)))) ≡ just S.query
query-kept-on-cancel = refl
no-delay-before-publication : U.step (U.handshakeStep F.owner (HS.continue HS.delayElapsed)) q₀ ≡ nothing
no-delay-before-publication = refl
no-cancel-before-delay : U.step (U.handshakeStep F.owner (HS.continue (HS.cancelDelay (errorId 8)))) q₁ ≡ nothing
no-cancel-before-delay = refl
no-duplicate-publication : U.step (U.handshakeStep F.owner (HS.continue HS.publish)) q₁ ≡ nothing
no-duplicate-publication = refl
no-duplicate-return : U.step (U.handshakeStep F.owner (HS.limitReturned HS.deadline (errorId 4))) q₀ ≡ nothing
no-duplicate-return = refl
no-timeout-before-helper : U.step (U.handshakeStep F.owner (HS.limitReturned HS.deadline (errorId 4))) (P.base F.p7) ≡ nothing
no-timeout-before-helper = refl
no-outbound-query-delay : U.step (U.handshakeStep F.owner HS.queryReturned) (record start { origins = (F.owner , outbound) ∷ [] }) ≡ nothing
no-outbound-query-delay = refl
raw-handshake-sealed : U.handlerAllowed (H.deliverHandshakeCancellation F.owner (errorId 8)) q₂ ≡ false
raw-handshake-sealed = refl
no-negotiated-allocation : U.step (U.allocateHandle F.owner (ident 0) (ident 0)) q₂ ≡ nothing
no-negotiated-allocation = refl
no-success-reentry : U.step (U.negotiate F.owner [] duplex) q₂ ≡ nothing
no-success-reentry = refl
no-negotiated-resources : IG.handles (IG.execution (Machine.inboundGovernor (O.core (U.source q₃)))) ≡ [] ×
 IG.muxes (IG.execution (Machine.inboundGovernor (O.core (U.source q₃)))) ≡ []
no-negotiated-resources = refl , refl
startup-pool-not-entered : U.startupAt F.owner q₃ ≡ U.Startup.initial
startup-pool-not-entered = refl

wrap : U.State → W.State
wrap u = W.handlerExitState (G.shutdownState (Monitor.monitorState (P.protocolState u [] []) []) []) []
no-premature-finish : W.step (W.finishHandshake F.owner) (wrap q₂) ≡ nothing
no-premature-finish = refl
normal-finally-ready : W.choose (W.finishHandshake F.owner) (wrap q₃) ≡ just
 (W.local ((F.owner , W.exitFrame F.captured (W.bodyExited W.returned) nothing) ∷ []))
normal-finally-ready = refl
cancel-finally-ready : W.choose (W.finishHandshake F.owner) (wrap qCancel) ≡ just
 (W.local ((F.owner , W.exitFrame F.captured (W.bodyExited (W.asyncException (errorId 8))) nothing) ∷ []))
cancel-finally-ready = refl
receipt-not-result : W.resultReady F.owner (wrap qCancel) ≡ false
receipt-not-result = refl

-- Receipt targets the coordinator's captured worker and advances that actual
-- throwTo cursor. It does not stand in for finalizer or Async completion.
runW : List W.Action → W.State → Maybe W.State
runW [] s = just s
runW (a ∷ as) s with W.step a s
... | nothing = nothing
... | just t = runW as t
cmActions : List W.Action
cmActions = W.shutdownStep Close.captureSnapshot ∷ W.shutdownStep Close.readEntry ∷ W.shutdownStep Close.requestCancellation ∷ []
awaitDelivery : W.State
awaitDelivery with runW cmActions (wrap q₂)
... | just t = t
... | nothing = wrap q₂
cm-send-prefix : runW cmActions (wrap q₂) ≡ just awaitDelivery
cm-send-prefix = refl
cmDelivered : W.State
cmDelivered with W.step (W.deliverShutdownHandshake HS.delayBlocked (errorId 8)) awaitDelivery
... | just t = t
... | nothing = awaitDelivery
cm-receipt-enabled : W.step (W.deliverShutdownHandshake HS.delayBlocked (errorId 8)) awaitDelivery ≡ just cmDelivered
cm-receipt-enabled = refl
cm-delay-receipt : at (P.base (G.protocolState (W.base cmDelivered))) ≡ just (HS.exited HS.query (HS.async (errorId 8)))
cm-delay-receipt = refl
cm-real-acknowledgement : Close.phase (W.shutdown cmDelivered) ≡ Close.reading
cm-real-acknowledgement = refl
cm-receipt-not-result : W.resultReady F.owner cmDelivered ≡ false
cm-receipt-not-result = refl
cm-wrong-blocking-site : W.step (W.deliverShutdownHandshake HS.traceBlocked (errorId 8)) awaitDelivery ≡ nothing
cm-wrong-blocking-site = refl
cm-no-pending-send : W.step (W.deliverShutdownHandshake HS.delayBlocked (errorId 8)) (wrap q₂) ≡ nothing
cm-no-pending-send = refl

-- A finite observed suffix executes the actual outer finally/close/results.
-- It supplies successful IO outcomes; it is not a termination guarantee.
finallyActions : List W.Action
finallyActions = W.finishHandshake F.owner ∷ W.enterFinalizer F.owner ∷
 W.cleanup F.owner Cleanup.takeCleanupMap ∷ W.cleanup F.owner Cleanup.selectCleanupEntry ∷
 W.cleanup F.owner Cleanup.closeHandlerSocket ∷ W.cleanup F.owner Cleanup.publishCleanupMap ∷
 W.cleanup F.owner Cleanup.readCleanupCounters ∷ W.finishCleanup F.owner ∷ W.publishAsyncResult F.owner ∷ []
query-normal-result : map (W.resultOf F.owner) (runW finallyActions (wrap q₃)) ≡ just (just W.returned)
query-normal-result = refl
timeout-normal-result : map (W.resultOf F.owner) (runW finallyActions (wrap t₂)) ≡ just (just W.returned)
timeout-normal-result = refl
cancel-async-result : map (W.resultOf F.owner) (runW finallyActions (wrap qCancel)) ≡ just (just (W.asyncException (errorId 8)))
cancel-async-result = refl
query-finally-closes-socket : map (λ s → lookup (S.handlerSocket F.captured) (S.sockets (W.shared s)))
 (runW finallyActions (wrap q₃)) ≡ just (just S.closed)
query-finally-closes-socket = refl
query-promise-retained-after-finally : map (λ s → lookup (S.handlerPromise F.captured) (S.handshakeResults (W.shared s)))
 (runW finallyActions (wrap q₃)) ≡ just (just S.query)
query-promise-retained-after-finally = refl

-- Size and timer limits use the same actual helper Left publication, retaining
-- the kind of supplied driver observation in the local continuation.
size-limit-enabled : U.step (U.handshakeStep F.owner (HS.limitReturned HS.sizeBound (errorId 5))) start ≡
 just (next (HS.limitReturned HS.sizeBound (errorId 5)) start)
size-limit-enabled = refl

-- The SDU bearer timeout follows the catch/publish/rethrow continuation.
b₀ b₁ b₂ : U.State
b₀ = next (HS.bearerTimedOut (errorId 6)) start
b₁ = next (HS.continue HS.publish) b₀
b₂ = next (HS.continue HS.rethrowError) b₁
sdu-timeout-enabled : U.step (U.handshakeStep F.owner (HS.bearerTimedOut (errorId 6))) start ≡ just b₀
sdu-timeout-enabled = refl
sdu-timeout-published : U.step (U.handshakeStep F.owner (HS.continue HS.publish)) b₀ ≡ just b₁
sdu-timeout-published = refl
sdu-timeout-result : lookup (S.handlerPromise F.captured) (S.handshakeResults (Machine.world (O.core (U.source b₁)))) ≡ just (S.handlerError S.protocolViolation (errorId 6))
sdu-timeout-result = refl
sdu-rethrows : U.step (U.handshakeStep F.owner (HS.continue HS.rethrowError)) b₁ ≡ just b₂
sdu-rethrows = refl
sdu-not-a-normal-helper-return : U.step (U.handshakeStep F.owner (HS.continue HS.traceReturned)) b₁ ≡ nothing
sdu-not-a-normal-helper-return = refl
sdu-enters-classifier : W.choose (W.finishHandshake F.owner) (wrap b₂) ≡ just
 (W.local ((F.owner , W.exitFrame F.captured (W.classifying (errorId 6)) nothing) ∷ []))
sdu-enters-classifier = refl
protocol-limit-not-rethrown : U.step (U.handshakeStep F.owner (HS.continue HS.rethrowError)) t₁ ≡ nothing
protocol-limit-not-rethrown = refl
