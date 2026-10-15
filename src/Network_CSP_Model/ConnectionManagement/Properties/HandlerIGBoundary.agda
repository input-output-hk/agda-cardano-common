{-# OPTIONS --guardedness #-}

-- Decision publication and fresh installation retain existing reference chains.
-- Other IG actions, including mux execution and responder restart, are separate.
module ConnectionManagement.Properties.HandlerIGBoundary where

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
open import ConnectionManagement.Properties.HandlerReferences
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

-- Fresh allocation preserves every old lookup, without requiring unique stores.
fresh-lookup : ∀ {K V} ⦃ _ : DecEq K ⦄ (k q : K) (v old : V) xs →
  lookup k xs ≡ nothing → lookup q xs ≡ just old → lookup q (put k v xs) ≡ just old
fresh-lookup k q v old xs absent found with q ≟ k
... | yes refl = case trans (sym absent) found of λ ()
... | no neq = trans (lookup-put-other k q v xs neq) found

-- This helper describes only table growth; the actual rule enforces freshness.
extend-chain : ∀ hid hd mid m {q captured s ig} →
  lookup hid (IG.handles (IG.execution ig)) ≡ nothing →
  lookup mid (IG.muxes (IG.execution ig)) ≡ nothing → Chain q captured s ig →
  Chain q captured s (record ig { execution = record (IG.execution ig)
    { handles = put hid hd (IG.handles (IG.execution ig)); muxes = put mid m (IG.muxes (IG.execution ig)) } })
extend-chain hid hd mid m {ig = ig} noHandle noMux chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = fresh-lookup hid _ hd _ (IG.handles (IG.execution ig)) noHandle (handleFound chain)
  ; handleMux = handleMux chain
  ; muxFound = fresh-lookup mid _ m _ (IG.muxes (IG.execution ig)) noMux (muxFound chain)
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

-- Publication may replace all governor membership, but leaves the engine intact.
control-chain : ∀ old n pc {q mid s ig} → Chain q mid s ig →
  Chain q mid s (IG.runtimeState old n pc (IG.execution ig))
control-chain old n pc chain = anchors-preserve-chain
  (record { handlesSame = refl; muxesRetained = λ mid m found → m , found , refl }) chain

-- Queue updates do not alter handler resources or negotiation results.
queue-chain : ∀ queue {q mid s ig} → Chain q mid s ig →
  Chain q mid (record s { inboundInfo = queue }) ig
queue-chain queue chain = record
  { originalHandler = originalHandler chain; publishedHandle = publishedHandle chain
  ; negotiatedFlow = negotiatedFlow chain; handleValue = handleValue chain; muxValue = muxValue chain
  ; handlerFound = handlerFound chain; promiseFound = promiseFound chain
  ; handleFound = handleFound chain; handleMux = handleMux chain; muxFound = muxFound chain
  ; keyMatches = keyMatches chain; entryPresent = entryPresent chain; socketPresent = socketPresent chain }

data CoveredIG : IG.IGAction → Set where
  decision : CoveredIG IG.commitDecision
  install : ∀ {hid mid k ps flow} → CoveredIG (IG.installHandle hid mid k ps flow)

worker-chain : ∀ a → CoveredIG a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain .IG.commitDecision decision ig queue s eq chain with IG.continuation ig
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
...   | refl = control-chain old _ (IG.readNext t rest) chain
worker-chain .(IG.installHandle hid mid k ps flow) (install {hid} {mid} {k} {ps} {flow}) ig queue s eq chain
  with lookup hid (IG.handles (IG.execution ig)) in absentHandle | lookup mid (IG.muxes (IG.execution ig)) in absentMux | IG.ordered ps | IG.supported ps
... | just _ | _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ | _ = case eq of λ ()
... | nothing | nothing | false | _ = case eq of λ ()
... | nothing | nothing | true | false = case eq of λ ()
... | nothing | nothing | true | true with just-injective eq
...   | refl = extend-chain hid _ mid _ absentHandle absentMux chain

mode-chain : ∀ mode a → CoveredIG a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain noResponderMode a covered ig queue s () chain
mode-chain responderMode a covered ig queue s eq chain = worker-chain a covered ig queue s eq chain

step-preserves : ∀ a → CoveredIG a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)
