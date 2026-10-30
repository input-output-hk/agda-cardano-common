{-# OPTIONS --guardedness #-}

-- The IG unwind changes only active call cursors; published/committed state
-- and existing capture/supply/resource premises retain their old meanings.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerIGExitInvariants (isBearerClosed : ErrorId → Bool) where

open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.State as Shared
open import ConnectionManagement.Domain using (WorkerId)
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as Proof
import ConnectionManagement.Properties.ServerAdmissionInvariants as Old
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.HandlerResourceFacts as Facts
open import ConnectionManagement.Properties.HandlerResources using (Resources; original)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
private
  module E = Exit isBearerClosed
  module L = Proof isBearerClosed

clear-captures : ∀ c → Capture.Captures c → Capture.Captures (E.clearPending c)
clear-captures c valid = valid
clear-supply : ∀ c → Supply.Valid c → Supply.Valid (E.clearPending c)
clear-supply c valid = valid
private
  module C = L.Lift Capture.Captures (Old.captures-step isBearerClosed) clear-captures
  module B = L.Lift Supply.Valid (Old.supply-step isBearerClosed) clear-supply

captures-step : ∀ a s {t} → E.step a s ≡ just t → Capture.Captures (E.source s) → Capture.Captures (E.source t)
captures-step = C.step-preserves
captures-exec : ∀ {s as t} → E.Executes s as t → Capture.Captures (E.source s) → Capture.Captures (E.source t)
captures-exec = C.exec-preserves
from-initial-captures : ∀ {c start as t} → E.initial (O.initial c) ≡ just start → E.Executes start as t → Capture.Captures (E.source t)
from-initial-captures {c} initialized path = C.from-initial initialized path (Capture.initial-valid c)
supply-step : ∀ a s {t} → E.step a s ≡ just t → Supply.Valid (E.source s) → Supply.Valid (E.source t)
supply-step = B.step-preserves
supply-exec : ∀ {s as t} → E.Executes s as t → Supply.Valid (E.source s) → Supply.Valid (E.source t)
supply-exec = B.exec-preserves
from-initial-supply : ∀ {c start as t} → E.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) → E.Executes start as t → Supply.Valid (E.source t)
from-initial-supply {c} initialized bounds path = B.from-initial initialized path (Capture.initial-valid c , bounds)

-- Keep the exact descriptor, including records whose socket is already closed.
module For (q : WorkerId) (captured : Shared.HandlerStart) where
  Valid : O.Configuration → Set
  Valid c = Facts.Facts q captured (Machine.world (O.core c))
  clear-resources : ∀ c → Valid c → Valid (E.clearPending c)
  clear-resources c valid = valid
  open L.Lift Valid (Old.For.step-preserves isBearerClosed q captured) clear-resources
    public using (step-preserves; exec-preserves)
resources-step : ∀ a s {t q} → E.step a s ≡ just t → Resources q (Machine.world (O.core (E.source s))) → Resources q (Machine.world (O.core (E.source t)))
resources-step a s {q = q} eq resources = Facts.to-resources
  (For.step-preserves q (original resources) a s eq (Facts.from-resources resources))
resources-exec : ∀ {s as t q} → E.Executes s as t → Resources q (Machine.world (O.core (E.source s))) → Resources q (Machine.world (O.core (E.source t)))
resources-exec {q = q} path resources = Facts.to-resources
  (For.exec-preserves q (original resources) path (Facts.from-resources resources))
