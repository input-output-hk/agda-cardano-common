{-# OPTIONS --guardedness #-}

-- G1 permission and refusal controls for the startup delivery-site classifier.
-- Provider/tracer blocking is a supplied observation, not derived from its PC.
-- Local equations do not add initialized reachability or full mask semantics.
module ConnectionManagement.Negative.PrimitiveStartupSites where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; map)
open import Data.Product using (_,_ )
open import ConnectionManagement.Domain using (errorId; ident)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Negative.MuxPublicationFixtures as F
module R = Unwind F.bearerClosed
module N = Publication F.bearerClosed
module S = F.S
module Pool = S.Pool

-- Exercise actual delivery dispatch at the two previously unpaired sites.
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false
wrap : N.P.State → R.State
wrap p = R.unwinding (N.W.handlerExitState (N.G.shutdownState (N.M.monitorState p []) []) []) []
buffer-delivery : isJust (R.step (R.observeCancellation F.owner R.blockedBufferAcquire (errorId 1))
  (wrap F.b15)) ≡ true
buffer-delivery = refl
bearerState : N.P.State
bearerState = record F.b15 { base = record (N.P.base F.b15)
  { frames = map (λ { (w , f) → w , record f { startup = S.startupState S.bufferReady Pool.initial } })
      (N.U.frames (N.P.base F.b15)) } }
bearer-delivery : isJust (R.step (R.observeCancellation F.owner R.blockedBearer (errorId 1))
  (wrap bearerState)) ≡ true
bearer-delivery = refl
buffer-after-acquire-refused : R.step (R.observeCancellation F.owner R.blockedBufferAcquire (errorId 1))
  (wrap bearerState) ≡ nothing
buffer-after-acquire-refused = refl
bearer-before-acquire-refused : R.step (R.observeCancellation F.owner R.blockedBearer (errorId 1))
  (wrap F.b15) ≡ nothing
bearer-before-acquire-refused = refl

-- Every admitted unmasked startup phase and the masked parent gap.
run-entry : R.asyncRoute R.unmaskedStartup S.runEntered ≡ just R.bufferOnly
run-entry = refl
starting : R.asyncRoute R.unmaskedStartup S.startingTraced ≡ just R.bufferOnly
starting = refl
egress : R.asyncRoute R.unmaskedStartup S.egressReady ≡ just R.bufferOnly
egress = refl
pool : R.asyncRoute R.unmaskedStartup S.poolReady ≡ just R.poolBody
pool = refl
muxer : ∀ j → R.asyncRoute R.unmaskedStartup (S.muxerRegistered j) ≡ just R.poolBody
muxer j = refl
demuxer : ∀ j k → R.asyncRoute R.unmaskedStartup (S.demuxerRegistered j k) ≡ just R.poolBody
demuxer j k = refl
mature : ∀ j k → R.asyncRoute R.unmaskedStartup (S.matureTraced j k) ≡ just R.poolBody
mature j k = refl
masked-fork-refused : ∀ j → R.asyncRoute R.unmaskedStartup (S.muxerForked j) ≡ nothing
masked-fork-refused j = refl
configured-not-covered : ∀ f → R.asyncRoute R.unmaskedStartup (S.configured f) ≡ nothing
configured-not-covered f = refl

-- Unmasked mux callbacks admit receipt; the fork callback is protected.
read-active : ∀ tr → M.interruptibleCallback (M.readActive tr) ≡ true
read-active tr = refl
commit-trace : ∀ active tr → M.interruptibleCallback (M.commitTrace active tr) ≡ true
commit-trace active tr = refl
after-start : ∀ n → M.interruptibleCallback (M.afterStart n) ≡ true
after-start n = refl
after-failure : M.interruptibleCallback M.afterFailure ≡ true
after-failure = refl
returned-refused : M.interruptibleCallback M.returned ≡ false
returned-refused = refl

-- Pure allocation/strict-handle evaluation cannot observe an async exception;
-- a potentially blocking supplied setup action can. Readiness is separate.
allocation-async-refused : ∀ e → N.deliveryReady N.muxAllocation (R.async e) ≡ false
allocation-async-refused e = refl
strict-async-refused : ∀ e → N.deliveryReady N.strictHandle (R.async e) ≡ false
strict-async-refused e = refl
setup-rule-async : ∀ e → N.deliveryReady N.egressRule (R.async e) ≡ true
setup-rule-async e = refl
install-async : ∀ e → N.deliveryReady N.rankInstall (R.async e) ≡ true
install-async e = refl
rank-trace-async : ∀ e → N.deliveryReady N.rankTrace (R.async e) ≡ true
rank-trace-async e = refl
