{-# OPTIONS --guardedness #-}

-- A peer job or followup waiting on its own CM call cannot step until the
-- call's result is written: every action other than the matching collect
-- needs another control point, and the collect needs that result.
module ConnectionManagement.Properties.AwaitStuck where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain using (WorkerId)
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.PeerJobs as J

acquire-stuck : ∀ a work caller child sock ref w → lookup caller (CM.acquired (J.cm w)) ≡ nothing →
  J.step a (J.frame work caller child sock ref J.awaitAcquire) w ≡ nothing
acquire-stuck J.enter work caller child sock ref w none = refl
acquire-stuck J.collectAcquire work caller child sock ref w none rewrite none = refl
acquire-stuck J.runNext work caller child sock ref w none = refl
acquire-stuck J.publishStarted work caller child sock ref w none = refl
acquire-stuck J.markEstablished work caller child sock ref w none = refl
acquire-stuck J.launchMonitor work caller child sock ref w none = refl
acquire-stuck (J.finishHotAt t) work caller child sock ref w none = refl
acquire-stuck J.observeHot work caller child sock ref w none = refl
acquire-stuck J.observeAll work caller child sock ref w none = refl
acquire-stuck J.requestRelease work caller child sock ref w none = refl
acquire-stuck J.collectRelease work caller child sock ref w none = refl
acquire-stuck J.observeCold work caller child sock ref w none = refl
acquire-stuck J.operationTimeout work caller child sock ref w none = refl
acquire-stuck J.demotionTimeout work caller child sock ref w none = refl
acquire-stuck J.failureDelayElapsed work caller child sock ref w none = refl
acquire-stuck (J.startFailed e) work caller child sock ref w none = refl
acquire-stuck J.choosePeerPolicy work caller child sock ref w none = refl
acquire-stuck J.chooseNodePolicy work caller child sock ref w none = refl
acquire-stuck J.deliverNodeException work caller child sock ref w none = refl
acquire-stuck J.rethrowNodeException work caller child sock ref w none = refl
release-stuck : ∀ a work caller child sock ref w → lookup caller (CM.released (J.cm w)) ≡ nothing →
  J.step a (J.frame work caller child sock ref J.awaitRelease) w ≡ nothing
release-stuck J.enter work caller child sock ref w none = refl
release-stuck J.collectAcquire work caller child sock ref w none = refl
release-stuck J.runNext work caller child sock ref w none = refl
release-stuck J.publishStarted work caller child sock ref w none = refl
release-stuck J.markEstablished work caller child sock ref w none = refl
release-stuck J.launchMonitor work caller child sock ref w none = refl
release-stuck (J.finishHotAt t) work caller child sock ref w none = refl
release-stuck J.observeHot work caller child sock ref w none = refl
release-stuck J.observeAll work caller child sock ref w none = refl
release-stuck J.requestRelease work caller child sock ref w none = refl
release-stuck J.collectRelease work caller child sock ref w none rewrite none = refl
release-stuck J.observeCold work caller child sock ref w none = refl
release-stuck J.operationTimeout work caller child sock ref w none = refl
release-stuck J.demotionTimeout work caller child sock ref w none = refl
release-stuck J.failureDelayElapsed work caller child sock ref w none = refl
release-stuck (J.startFailed e) work caller child sock ref w none = refl
release-stuck J.choosePeerPolicy work caller child sock ref w none = refl
release-stuck J.chooseNodePolicy work caller child sock ref w none = refl
release-stuck J.deliverNodeException work caller child sock ref w none = refl
release-stuck J.rethrowNodeException work caller child sock ref w none = refl
