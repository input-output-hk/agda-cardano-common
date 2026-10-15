{-# OPTIONS --guardedness #-}

-- Existing reference chains survive handler lifecycle actions. Creation of a
-- coherent chain and preservation by the other dispatcher families are separate.
module ConnectionManagement.Properties.HandlerReferences where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Data.Maybe.Properties using (just-injective)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.HandlerAnchors
open import ConnectionManagement.Properties.HandlerCapture using (step-retains)
open import ConnectionManagement.Properties.HandlerEvolution using (step-anchors)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

-- Entry and socket existence deliberately do not mean current map membership,
-- an open socket, or registration in the inbound governor.
record Chain (w : WorkerId) (mid : MuxId) (s : State) (ig : IG.Runtime) : Set where
  field
    originalHandler : HandlerStart
    publishedHandle : HandleId
    negotiatedFlow : DataFlow
    handleValue : M.Handle
    muxValue : M.Mux
    handlerFound : lookup w (handlers s) ≡ just originalHandler
    promiseFound : lookup (handlerPromise originalHandler) (handshakeResults s) ≡
      just (negotiated publishedHandle negotiatedFlow)
    handleFound : lookup publishedHandle (IG.handles (IG.execution ig)) ≡ just handleValue
    handleMux : M.muxRef handleValue ≡ mid
    muxFound : lookup mid (IG.muxes (IG.execution ig)) ≡ just muxValue
    keyMatches : M.key muxValue ≡ handlerKey originalHandler
    entryPresent : Present (handlerEntry originalHandler) (entries (cm s))
    socketPresent : Present (handlerSocket originalHandler) (sockets s)
open Chain public

anchors-preserve-chain : ∀ {w mid s ig ig′} → Anchors ig ig′ →
  Chain w mid s ig → Chain w mid s ig′
anchors-preserve-chain {mid = mid} anchors chain with
  muxesRetained anchors mid (muxValue chain) (muxFound chain)
... | m′ , found , same = record
  { originalHandler = originalHandler chain
  ; publishedHandle = publishedHandle chain; negotiatedFlow = negotiatedFlow chain
  ; handleValue = handleValue chain; handlerFound = handlerFound chain
  ; promiseFound = promiseFound chain; handleMux = handleMux chain
  ; entryPresent = entryPresent chain; socketPresent = socketPresent chain
  ; handleFound = trans (cong (lookup (publishedHandle chain)) (handlesSame anchors)) (handleFound chain)
  ; muxValue = m′; muxFound = found; keyMatches = trans same (keyMatches chain) }

TrackedChain : WorkerId → Configuration → Set
TrackedChain w c = Σ L.Frame (λ f → lookup w (handlerLifecycles c) ≡ just f ×
  Chain w (L.capturedMux f) (world c) (inboundGovernor c))

-- The actor and the worker whose references are protected need not coincide.
handler-step-preserves : ∀ w a c {c′} → advance (handlerStep w a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
handler-step-preserves w a c eq q (f , found , chain) with
  L.step w a (handlerLifecycles c) (inboundGovernor c) (world c) in stepped | eq
... | nothing | ()
... | just (rt′ , ig′) | equation with just-injective equation
...   | refl with step-retains w a (handlerLifecycles c) (inboundGovernor c) (world c) stepped q f found
...     | g , retained , same = g , retained ,
  subst (λ mid → Chain q mid (world c) ig′) (sym same)
    (anchors-preserve-chain (step-anchors w a (handlerLifecycles c) (inboundGovernor c) (world c) stepped) chain)

-- Restrict the action list, not the executable machine: every listed step is
-- still checked using the unmodified dispatcher and its normal CSP renderer.
data LifecycleOnly : List Action → Set where
  empty : LifecycleOnly []
  more : ∀ {w a as} → LifecycleOnly as → LifecycleOnly (handlerStep w a ∷ as)

exec-preserves : ∀ {c as c′} → LifecycleOnly as → Executes c as c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
exec-preserves empty done q chain = chain
exec-preserves (more {w} {a} only) (next {c = c} eq rest) q chain =
  exec-preserves only rest q (handler-step-preserves w a c eq q chain)
