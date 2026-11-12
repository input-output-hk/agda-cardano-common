{-# OPTIONS --guardedness #-}

-- G1 selected winner/untimed-delay controls. Expiry is an observation input,
-- not a clock, deadline or scheduler-fairness theorem. All checks use real rules.
module ConnectionManagement.Negative.PrimitiveTimers where

open import Data.Bool using (false; true)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀)

-- The ready timer loses to a changed entry (Negative/Outbound); here it wins
-- only on the captured idle entry, and selection has no premature entry write.
idle : S.State → S.State
idle s = record s { cm = S.cmStore (S.full [])
  ((ident 0 , S.outboundIdle key₀ child₀ (ident 0) duplex) Data.List.∷ []) 1 }
waiting : R.Frame
waiting = R.frame key₀ (R.waitIdle (ident 0) child₀) false
armed : R.Frame
armed = record waiting { timerReady = true }
timer-not-ready : ∀ s → R.step 10 R.selectWakeup waiting (idle s) ≡ nothing
timer-not-ready s = refl
expiry-enabled : ∀ s → R.step 10 R.expireTimer waiting (idle s) ≡ just (armed , idle s)
expiry-enabled s = refl
duplicate-expiry-refused : ∀ s → R.step 10 R.expireTimer armed (idle s) ≡ nothing
duplicate-expiry-refused s = refl
timer-wins-idle : ∀ s → R.step 10 R.selectWakeup armed (idle s) ≡
  just (record armed { pc = R.timeoutWrite (ident 0) child₀ } , idle s)
timer-wins-idle s = refl

-- The outer Cold wait and establishment failure sleep have distinct PCs.
cold-timeout-enabled : ∀ f w → J.step J.demotionTimeout
  (record f { pc = J.awaitCold G.failed }) w ≡
  just (record f { pc = J.complete G.demotionTimedOut } , w)
cold-timeout-enabled f w = refl
cold-timeout-before-wait-refused : ∀ f w → J.step J.demotionTimeout
  (record f { pc = J.awaitHot }) w ≡ nothing
cold-timeout-before-wait-refused f w = refl
delay-enabled : ∀ f w → J.step J.failureDelayElapsed
  (record f { pc = J.delayFailure }) w ≡
  just (record f { pc = J.complete G.failed } , w)
delay-enabled f w = refl
delay-wrong-wait-refused : ∀ f w → J.step J.failureDelayElapsed
  (record f { pc = J.awaitCold G.failed }) w ≡ nothing
delay-wrong-wait-refused f w = refl
operation-timeout-before-wait-refused : ∀ f w → J.step J.operationTimeout
  (record f { pc = J.begin }) w ≡ nothing
operation-timeout-before-wait-refused f w = refl
