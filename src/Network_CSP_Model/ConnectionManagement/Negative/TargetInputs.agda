{-# OPTIONS --guardedness #-}

-- A4 ordinary-peer target controls. External writes are distinct from the
-- governor transaction that selects a changed sane value. Timer/selection
-- snapshots below are conditional; no new source-reachability claim is made.
module ConnectionManagement.Negative.TargetInputs where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.CSP.GovernorLifecycle as Fixture

-- Natural-valued targets need no separate nonnegativity premise. These are the
-- projected ordinary-peer caps; root/big-ledger targets are outside this profile.
zero-targets-sane : G.sane (G.targets 0 0 0) ≡ true
zero-targets-sane = refl
all-upper-bounds-sane : G.sane (G.targets 10000 1000 100) ≡ true
all-upper-bounds-sane = refl
active-bound-plus-one-insane : G.sane (G.targets 10000 1000 101) ≡ false
active-bound-plus-one-insane = refl
established-bound-plus-one-insane : G.sane (G.targets 10000 1001 100) ≡ false
established-bound-plus-one-insane = refl
known-bound-plus-one-insane : G.sane (G.targets 10001 1000 100) ≡ false
known-bound-plus-one-insane = refl
active-order-insane : G.sane (G.targets 3 1 2) ≡ false
active-order-insane = refl
established-order-insane : G.sane (G.targets 2 3 1) ≡ false
established-order-insane = refl

-- The real existing selection fixture has a ready establishment policy.
-- Distinct small sane updates avoid making priority checks vacuous at a cap.
firstTarget latestTarget invalidTarget : G.Targets
firstTarget = G.targets 2 1 1
latestTarget = G.targets 3 2 1
invalidTarget = G.targets 1 0 1
base : Sub.Configuration
base = Fixture.c3
firstWritten invalidWritten latestWritten : Sub.Configuration
firstWritten = record base { targetInput = firstTarget }
invalidWritten = record base { targetInput = invalidTarget }
latestWritten = record base { targetInput = latestTarget }
sane-input-write : Sub.advance (Sub.setTargets firstTarget) base ≡ just firstWritten
sane-input-write = refl
invalid-overwrites-sane : Sub.advance (Sub.setTargets invalidTarget) firstWritten ≡ just invalidWritten
invalid-overwrites-sane = refl
invalid-stored-value : Sub.targetInput invalidWritten ≡ invalidTarget
invalid-stored-value = refl
invalid-update-not-selected : Sub.advance Sub.selectTargets invalidWritten ≡ nothing
invalid-update-not-selected = refl

-- The earlier sane value was overwritten before the selection transaction;
-- it is not retained in a separate pending target-update queue.
sane-then-invalid : Sub.Executes base
  (Sub.setTargets firstTarget ∷ Sub.setTargets invalidTarget ∷ []) invalidWritten
sane-then-invalid = Sub.next {c₁ = firstWritten} sane-input-write
  (Sub.next invalid-overwrites-sane Sub.done)
invalid-does-not-change-private-target : G.target (Sub.privateState invalidWritten) ≡ G.targets 1 1 1
invalid-does-not-change-private-target = refl

-- A later sane write replaces the invalid TVar value and is then selectable.
valid-overwrites-invalid : Sub.advance (Sub.setTargets latestTarget) invalidWritten ≡ just latestWritten
valid-overwrites-invalid = refl
latestSelected : Sub.Configuration
latestSelected = record latestWritten { pc = Sub.apply (Sub.targets latestTarget) }
latest-valid-selected : Sub.advance Sub.selectTargets latestWritten ≡ just latestSelected
latest-valid-selected = refl
invalid-then-valid : Sub.Executes base
  (Sub.setTargets invalidTarget ∷ Sub.setTargets latestTarget ∷ Sub.selectTargets ∷ []) latestSelected
invalid-then-valid = Sub.next {c₁ = invalidWritten} refl
  (Sub.next {c₁ = latestWritten} valid-overwrites-invalid (Sub.next latest-valid-selected Sub.done))

-- An unchanged external write succeeds, but does not create a ready update.
unchanged-write-accepted : Sub.advance (Sub.setTargets (G.targets 1 1 1)) base ≡ just base
unchanged-write-accepted = refl
unchanged-update-not-selected : Sub.advance Sub.selectTargets base ≡ nothing
unchanged-update-not-selected = refl

-- Policy readiness is witnessed positively, then checked under invalid/valid
-- target inputs. Invalid values must not block the lower-priority alternative.
policy-ready : Sub.advance (Sub.selectPolicy (Fixture.peerAddr ∷ [])) base ≡ just Fixture.c4
policy-ready = Fixture.step4
invalid-input-keeps-policy-ready : Sub.advance (Sub.selectPolicy (Fixture.peerAddr ∷ [])) invalidWritten ≡
  just (record Fixture.c4 { targetInput = invalidTarget })
invalid-input-keeps-policy-ready = refl
valid-input-preempts-policy : Sub.advance (Sub.selectPolicy (Fixture.peerAddr ∷ [])) firstWritten ≡ nothing
valid-input-preempts-policy = refl

-- A future retry blocks all policies at sampled time zero. The separate ready
-- timer lets the governor select its captured deadline before the next time read.
quietState : G.State
quietState = record Fixture.settings
  { knownPeers = (Fixture.peerAddr , G.known 0 5 nothing false false) ∷ [] }
quiet-has-no-ready-policy : G.firstReady 0 quietState ≡ nothing
quiet-has-no-ready-policy = refl
wakeBase wakeInvalid wakeValid : Sub.Configuration
wakeBase = record base
  { privateState = quietState; publicState = quietState
  ; wakeupAt = just 5; wakeupReady = true }
wakeInvalid = record wakeBase { targetInput = invalidTarget }
wakeValid = record wakeBase { targetInput = firstTarget }
wakeup-ready : Sub.advance Sub.selectWakeup wakeBase ≡
  just (record wakeBase { pc = Sub.cancelTimer (Sub.wakeup 5) })
wakeup-ready = refl
invalid-input-keeps-wakeup-ready : Sub.advance Sub.selectWakeup wakeInvalid ≡
  just (record wakeInvalid { pc = Sub.cancelTimer (Sub.wakeup 5) })
invalid-input-keeps-wakeup-ready = refl
valid-input-preempts-wakeup : Sub.advance Sub.selectWakeup wakeValid ≡ nothing
valid-input-preempts-wakeup = refl
valid-input-selected-before-wakeup : Sub.advance Sub.selectTargets wakeValid ≡
  just (record wakeValid { pc = Sub.cancelTimer (Sub.targets firstTarget) })
valid-input-selected-before-wakeup = refl

-- Once the selection transaction captured a sane update, later external writes
-- do not replace its continuation. Applying that already-selected value remains
-- valid even when the current external target input is now insane.
firstSelected overwrittenSelection capturedApplied : Sub.Configuration
firstSelected = record firstWritten { pc = Sub.apply (Sub.targets firstTarget) }
overwrittenSelection = record firstSelected { targetInput = invalidTarget }
capturedApplied = record overwrittenSelection
  { now = 0; privateState = record Fixture.settings { target = firstTarget }
  ; pc = Sub.publishView [] }
first-valid-selected : Sub.advance Sub.selectTargets firstWritten ≡ just firstSelected
first-valid-selected = refl
external-overwrite-after-selection : Sub.advance (Sub.setTargets invalidTarget) firstSelected ≡ just overwrittenSelection
external-overwrite-after-selection = refl
captured-sane-update-applied : Sub.advance (Sub.applyAt 0) overwrittenSelection ≡ just capturedApplied
captured-sane-update-applied = refl
captured-target-retained : G.target (Sub.privateState capturedApplied) ≡ firstTarget
captured-target-retained = refl
new-external-value-retained : Sub.targetInput capturedApplied ≡ invalidTarget
new-external-value-retained = refl

-- A selected target can also be suspended on cancellation of an older wakeup
-- timer. External writes during that cancellation must not replace its capture.
wakeSelected wakeOverwritten wakeCancelled wakeCapturedApplied : Sub.Configuration
wakeSelected = record wakeValid { pc = Sub.cancelTimer (Sub.targets firstTarget) }
wakeOverwritten = record wakeSelected { targetInput = invalidTarget }
wakeCancelled = record wakeOverwritten
  { pc = Sub.apply (Sub.targets firstTarget); wakeupAt = nothing; wakeupReady = false }
wakeCapturedApplied = record wakeCancelled
  { now = 0; privateState = record quietState { target = firstTarget }; pc = Sub.publishView [] }
external-overwrite-during-cancellation : Sub.advance (Sub.setTargets invalidTarget) wakeSelected ≡ just wakeOverwritten
external-overwrite-during-cancellation = refl
selected-target-survives-cancellation : Sub.advance Sub.cancelWakeup wakeOverwritten ≡ just wakeCancelled
selected-target-survives-cancellation = refl
cancelled-captured-target-applied : Sub.advance (Sub.applyAt 0) wakeCancelled ≡ just wakeCapturedApplied
cancelled-captured-target-applied = refl
