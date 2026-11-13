{-# OPTIONS --guardedness #-}

-- G1 F2: local configured-startup dispatch, preserving partial pool state.
-- States below replace only the startup continuation of a published owner;
-- these controls do not assert initialized configured reachability.
module ConnectionManagement.Negative.PrimitiveConfiguredStartup where

open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; map)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (errorId; ident)
import ConnectionManagement.Negative.PrimitiveStartupSites as Old
import ConnectionManagement.Negative.MuxPublicationFixtures as F
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.MuxJobTypes as T
module R = Unwind F.bearerClosed
module S = F.S
module Pool = S.Pool

frame : S.ConfiguredStage → S.ConfiguredFrame
frame stage = S.configuredFrame (E.scheduledLayout true) 0 [] stage
at : S.ConfiguredStage → R.State
at stage = Old.wrap (record F.b15 { base = record (F.P.base F.b15)
  { frames = map (λ { (w , f) → w , record f
      { startup = S.startupState (S.configured (frame stage)) Pool.initial } })
      (F.U.frames (F.P.base F.b15)) } })
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false
receipt : S.ConfiguredStage → Maybe R.State
receipt stage = R.step (R.observeCancellation F.owner R.unmaskedConfiguredStartup (errorId 1)) (at stage)

before-pool-needs-earlier-site : receipt S.cfgBeforePool ≡ nothing
before-pool-needs-earlier-site = refl
ready : isJust (receipt S.cfgReady) ≡ true
ready = refl
mature : isJust (receipt S.cfgMature) ≡ true
mature = refl
masked-gap-refused : receipt (S.cfgRegistering T.demuxer (ident 3)) ≡ nothing
masked-gap-refused = refl
monitor-needs-callback-site : receipt S.cfgMonitoring ≡ nothing
monitor-needs-callback-site = refl
before-pool-scope : R.asyncRoute R.unmaskedConfiguredStartup (S.configured (frame S.cfgBeforePool)) ≡ nothing
before-pool-scope = refl
ready-scope : R.asyncRoute R.unmaskedConfiguredStartup (S.configured (frame S.cfgReady)) ≡ just R.poolBody
ready-scope = refl
plain-wrong-site : R.asyncRoute R.unmaskedConfiguredStartup S.poolReady ≡ nothing
plain-wrong-site = refl

-- Receipt captures the exact configured PC and leaves the existing pool intact.
afterReady : R.State
afterReady with receipt S.cfgReady
... | just t = t
... | nothing = at S.cfgReady
pool-retained : R.poolAt F.owner afterReady ≡ R.poolAt F.owner (at S.cfgReady)
pool-retained = refl
controller-sealed : R.allowedP (F.P.run (F.U.startupStep F.owner S.traceConfiguredMature)) afterReady ≡ false
controller-sealed = refl
