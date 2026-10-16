{-# OPTIONS --guardedness #-}

-- A publication ticket fixes the mux captured by later successful attachment.
module ConnectionManagement.Properties.RegistryAttachment where

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated; handlerPromise; handshakeResults)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Rules.OriginMonitor using (Ticket; muxId; protocols)
open import ConnectionManagement.Rules.AttributedOrigin using (dispatch; erase)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Properties.RegistryPublication using (Sound; publication; reachable-publication)
import ConnectionManagement.Properties.OriginRegistry as Registry
open import ConnectionManagement.Properties.HandlerOrigin using (Origin; prepared; origin-exec)
open import ConnectionManagement.Properties.HandlerReferences using (Chain; TrackedChain)
open import ConnectionManagement.Properties.HandlerEstablishment using (publication-creates; attach-established)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Dispatcher
import ConnectionManagement.Properties.HandlerManagement as Management

-- Functional handler/promise/handle lookups force two chains to name one mux.
negotiated-handle : ∀ {h h′ f f′} → negotiated h f ≡ negotiated h′ f′ → h ≡ h′
negotiated-handle refl = refl
chain-mux : ∀ {w mid mid′ s ig} → Chain w mid s ig → Chain w mid′ s ig → mid ≡ mid′
chain-mux {s = s} {ig} left right =
  trans (sym (Chain.handleMux left)) (trans (cong M.muxRef sameHandle) (Chain.handleMux right))
  where
  sameHandler = just-injective (trans (sym (Chain.handlerFound left)) (Chain.handlerFound right))
  leftPromise = subst (λ h → lookup (handlerPromise h) (handshakeResults s) ≡
    just (negotiated (Chain.publishedHandle left) (Chain.negotiatedFlow left))) sameHandler (Chain.promiseFound left)
  sameId = negotiated-handle (just-injective (trans (sym leftPromise) (Chain.promiseFound right)))
  leftHandle = subst (λ hid → lookup hid (IG.handles (IG.execution ig)) ≡ just (Chain.handleValue left))
    sameId (Chain.handleFound left)
  sameHandle = just-injective (trans (sym leftHandle) (Chain.handleFound right))

record Attached (w : WorkerId) (hid : HandleId) (tk : Ticket) (f : DataFlow) (c : Open.Configuration) : Set where
  field
    frame : L.Frame
    frameFound : lookup w (Open.handlerLifecycles c) ≡ just frame
    captured : L.capturedMux frame ≡ muxId tk
    chain : Chain w (muxId tk) (Open.world c) (Open.inboundGovernor c)
    origin : Origin w hid (muxId tk) (protocols tk) f c

-- TrackedChain alone existentially chooses a mux; the retained publication chain
-- identifies it with the ticket's mux, even after further lifecycle transitions.
identify : ∀ {w hid tk f c} → TrackedChain w c →
  Chain w (muxId tk) (Open.world c) (Open.inboundGovernor c) →
  Origin w hid (muxId tk) (protocols tk) f c → Attached w hid tk f c
identify (fr , found , tracked) chain origin = record
  { frame = fr; frameFound = found; captured = chain-mux tracked chain
  ; chain = chain; origin = origin }

attachment : WorkerId → ErrorId → ConnectionManagement.Rules.AttributedOrigin.Action
attachment w err = dispatch (Open.handlerStep w (L.attach err))

-- Every interleaving still passes the unmodified registry and machine guards.
-- This theorem assumes a successful attachment; it does not assert readiness.
publication-attachment : ∀ {c prefix before after s sPub sReady sAttached sEnd}
  w hid f err (path : Executes (start c) prefix s) → Registry.Supported path →
  step (publication w hid f) s ≡ just sPub → Executes sPub before sReady →
  step (attachment w err) sReady ≡ just sAttached → Executes sAttached after sEnd →
  Σ (Sound w hid f s sPub) (λ certificate → Attached w hid (Sound.ticket certificate) f (machine sEnd))
publication-attachment {s = s} {sPub} {sReady} {sAttached} {sEnd} w hid f err path supported published before attached after =
  certificate , identify finalTracked finalChain finalOrigin
  where
  certificate = reachable-publication w hid f path supported published
  publicationChain = publication-creates w hid (muxId (Sound.ticket certificate)) f (machine s)
    (prepared (Sound.originBefore certificate)) (Registry.step-projects (publication w hid f) s published)
  readyChain = Dispatcher.all-chain (Registry.exec-projects before) publicationChain
  attachedStep = Registry.step-projects (attachment w err) sReady attached
  tracked = attach-established w err (machine sReady) readyChain attachedStep
  finalTracked = Management.all-exec-preserves (Registry.exec-projects after) w tracked
  remaining = Open.next {c = machine sReady} {a = Open.handlerStep w (L.attach err)} attachedStep (Registry.exec-projects after)
  finalChain = Dispatcher.all-chain remaining readyChain
  finalOrigin = origin-exec remaining (origin-exec (Registry.exec-projects before) (Sound.originAfter certificate))
