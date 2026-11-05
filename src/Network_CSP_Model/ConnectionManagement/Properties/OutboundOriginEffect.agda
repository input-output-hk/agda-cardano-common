{-# OPTIONS --guardedness #-}

-- Small framing interface for one actual active-acquisition write per event.
module ConnectionManagement.Properties.OutboundOriginEffect where

open import Data.Maybe using (just)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.OutboundOriginCore as Core
open Core public using (Effect)

same : ∀ {before after} → O.acquiring after ≡ O.acquiring before → Effect before after
same = Core.same
reframe : ∀ {before after nextBefore nextAfter} → nextBefore ≡ before → nextAfter ≡ after →
  Effect before after → Effect nextBefore nextAfter
reframe refl refl observed = observed
outbound-effect : ∀ action before {after} → O.advance action before ≡ just after → Effect before after
outbound-effect = Core.advance-effect
