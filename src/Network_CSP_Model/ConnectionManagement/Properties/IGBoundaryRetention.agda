{-# OPTIONS --guardedness #-}

-- Decision publication and fresh installation retain existing reference chains.
-- Other IG actions, including mux execution and responder restart, are separate.
module ConnectionManagement.Properties.IGBoundaryRetention where

open import Data.Bool using (true; false)
open import Data.List using (map; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans; sym)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put; Store)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.IGTableRetention
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

data CoveredIG : IG.IGAction → Set where
  decision : CoveredIG IG.commitDecision
  install : ∀ {hid mid k ps flow} → CoveredIG (IG.installHandle hid mid k ps flow)
  installOutbound : ∀ {hid mid k ps flow} → CoveredIG (IG.installOutboundHandle hid mid k ps flow)

-- Tracer attachment does not change fresh handle/mux lookup retention.
install-retains : ∀ attachment hid mid k ps flow ig queue {ig′ queue′} →
  IG.installWith attachment hid mid k ps flow ig queue ≡ just (ig′ , queue′) → Retains ig ig′
install-retains attachment hid mid k ps flow ig queue eq
  with lookup hid (IG.handles (IG.execution ig)) in absentHandle | lookup mid (IG.muxes (IG.execution ig)) in absentMux | IG.ordered ps | IG.supported ps
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
... | nothing | nothing | true | true with just-injective eq
...   | refl = extend-retains hid _ mid _ ig absentHandle absentMux

worker-retains : ∀ a → CoveredIG a → ∀ ig queue {ig′ queue′} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Retains ig ig′
worker-retains .IG.commitDecision decision ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.publishDecision t rest old with just-injective eq
...   | refl = control-retains old _ (IG.readNext t rest) ig
worker-retains .(IG.installHandle hid mid k ps flow) (install {hid} {mid} {k} {ps} {flow}) ig queue eq =
  install-retains M.igTracer hid mid k ps flow ig queue eq
worker-retains .(IG.installOutboundHandle hid mid k ps flow) (installOutbound {hid} {mid} {k} {ps} {flow}) ig queue eq =
  install-retains (IG.outboundTracer responderMode flow) hid mid k ps flow ig queue eq

mode-retains : ∀ mode a → CoveredIG a → ∀ ig queue {ig′ queue′} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Retains ig ig′
mode-retains noResponderMode .IG.commitDecision decision ig queue ()
mode-retains noResponderMode .(IG.installHandle hid mid k ps flow) (install {hid} {mid} {k} {ps} {flow}) ig queue ()
mode-retains noResponderMode .(IG.installOutboundHandle hid mid k ps flow) (installOutbound {hid} {mid} {k} {ps} {flow}) ig queue eq =
  install-retains M.noIGTracer hid mid k ps flow ig queue eq
mode-retains responderMode a covered ig queue eq = worker-retains a covered ig queue eq
