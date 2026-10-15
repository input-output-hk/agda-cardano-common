{-# OPTIONS --guardedness #-}

-- Successful attachment supplies the lookup chain; only unchecked resource and
-- key coherence facts are premises. This does not establish them from allocation.
module ConnectionManagement.Properties.HandlerAttachment where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.Maybe.Properties using (just-injective)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M

-- These facts are deliberately conditional on the actual lookup results.
record CreationPremises (w : WorkerId) (s : State) (ig : IG.Runtime) : Set where
  field
    resources : ∀ h → lookup w (handlers s) ≡ just h →
      Present (handlerEntry h) (entries (cm s)) × Present (handlerSocket h) (sockets s)
    coherent : ∀ h hid flow hd m → lookup w (handlers s) ≡ just h →
      lookup (handlerPromise h) (handshakeResults s) ≡ just (negotiated hid flow) →
      lookup hid (IG.handles (IG.execution ig)) ≡ just hd →
      lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) ≡ just m →
      M.key m ≡ handlerKey h
open CreationPremises public

attach-creates : ∀ w err rt ig s {rt′ ig′} →
  CreationPremises w s ig → L.attachMux w err rt ig s ≡ just (rt′ , ig′) →
  Σ L.Frame (λ f → lookup w rt′ ≡ just f × Chain w (L.capturedMux f) s ig′)
attach-creates w err rt ig s premises eq with lookup w rt in absent | lookup w (handlers s) in handlerFound | lookup w (cleanups s)
... | nothing | just h | nothing with lookup (handlerPromise h) (handshakeResults s) in promiseFound
...   | just (negotiated hid flow) with lookup hid (IG.handles (IG.execution ig)) in handleFound
...     | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) in muxFound | L.hasMux (M.muxRef hd) rt in unused
...       | just m | false with M.status m | M.callback m
...         | M.ready | M.returned = subst
  (λ pair → Σ L.Frame (λ f → lookup w (proj₁ pair) ≡ just f × Chain w (L.capturedMux f) s (proj₂ pair)))
  (just-injective eq)
  (L.frame (M.muxRef hd) err L.monitoring , lookup-put w _ rt , record
    { originalHandler = h; publishedHandle = hid; negotiatedFlow = flow
    ; handleValue = hd; muxValue = m; handlerFound = handlerFound
    ; promiseFound = promiseFound; handleFound = handleFound; handleMux = refl
    ; muxFound = muxFound
    ; keyMatches = coherent premises h hid flow hd m handlerFound promiseFound handleFound muxFound
    ; entryPresent = proj₁ (resources premises h handlerFound)
    ; socketPresent = proj₂ (resources premises h handlerFound) })
...         | M.stopping | _ = case eq of λ ()
...         | M.stopped | _ = case eq of λ ()
...         | M.failed _ | _ = case eq of λ ()
...         | M.ready | M.readActive _ = case eq of λ ()
...         | M.ready | M.commitTrace _ _ = case eq of λ ()
...         | M.ready | M.afterStart _ = case eq of λ ()
...         | M.ready | M.forkPending _ = case eq of λ ()
...         | M.ready | M.afterFailure = case eq of λ ()
...         | M.ready | M.tracerFailed _ = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | just (negotiated hid flow) | just hd | nothing | _ = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | just (negotiated hid flow) | just hd | just _ | true = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | just (negotiated hid flow) | nothing = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | nothing = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | just query = case eq of λ ()
attach-creates w err rt ig s premises eq | nothing | just h | nothing | just (handlerError _ _) = case eq of λ ()
attach-creates _ _ _ _ _ premises eq | just _ | _ | _ = case eq of λ ()
attach-creates _ _ _ _ _ premises eq | nothing | nothing | _ = case eq of λ ()
attach-creates _ _ _ _ _ premises eq | nothing | just _ | just _ = case eq of λ ()

-- Lift attachment's result through the unchanged machine dispatcher.
advance-creates : ∀ w err c {c′} → CreationPremises w (world c) (inboundGovernor c) →
  advance (handlerStep w (L.attach err)) c ≡ just c′ → TrackedChain w c′
advance-creates w err c premises eq with
  L.attachMux w err (handlerLifecycles c) (inboundGovernor c) (world c) in attached | eq
... | nothing | ()
... | just (rt′ , ig′) | equation with just-injective equation
...   | refl = attach-creates w err (handlerLifecycles c) (inboundGovernor c) (world c) premises attached
