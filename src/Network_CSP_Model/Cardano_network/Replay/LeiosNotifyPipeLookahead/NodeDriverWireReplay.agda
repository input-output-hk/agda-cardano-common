{-# OPTIONS --safe #-}

-- The full node core instantiates existing generic weak-trace and decision machinery.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverWireReplay
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Level using (0ℓ)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (Dec; yes; no)
import Semantics.Replay as R
import Semantics.Replay.Decide as Decide
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBasis Notification basis as B
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreExecution Notification notificationEq basis as Menu
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecutionReplay Notification notificationEq basis as Existing

-- Actor/direction/control/payload equality is shared with the existing typed driver alphabet.
eventEq : DecidableEquality D.Event
eventEq = Existing.eventEq

-- Every successor is backed by the independent source relation and complete finite menus.
replay : R.Replay 0ℓ Core.State D.Event
replay = record
  { _-[_]→_ = B.Visible
  ; _-τ→_ = B.Tau
  ; _≟E_ = eventEq
  ; after = Menu.after
  ; taus = Menu.taus
  ; after-sound = Menu.after-sound
  ; taus-sound = Menu.taus-sound
  ; after-complete = Menu.after-complete
  ; taus-complete = Menu.taus-complete
  }

-- The shared weak-trace relation retains exactly the restricted core state and labels.
module Trace = R.Traces replay

-- No custom search loop is introduced for the full node policy.
module Decision = Decide.Decider replay

-- Generic replay witnesses recover the original restricted source run without loss.
to-run : ∀ {s rows t} → Trace._⇒⟨_⟩_ s rows t → B.Run s rows t
to-run Trace.done = B.stop
to-run (Trace.tau proof rest) = B.internal proof (to-run rest)
to-run (Trace.vis proof rest) = B.visible proof (to-run rest)

-- Every independent restricted source run is a generic weak trace with the same endpoint.
from-run : ∀ {s rows t} → B.Run s rows t → Trace._⇒⟨_⟩_ s rows t
from-run B.stop = Trace.done
from-run (B.internal proof rest) = Trace.tau proof (from-run rest)
from-run (B.visible proof rest) = Trace.vis proof (from-run rest)

-- Standard accessibility translates to the generic decider's own hidden certificate.
from-accessible : ∀ {s} → Acc (λ t s → B.Tau s t) s → Decision.τAcc s
from-accessible (acc smaller) = Decision.acc λ step → from-accessible (smaller step)

-- The previously proved core measure supplies hidden termination at every state.
tau-accessible : ∀ s → Decision.τAcc s
tau-accessible s = from-accessible (B.tau-accessible s)

-- This decision concerns the declared finite-offer basis; full-source adequacy is separate.
decide-run : (s : Core.State) (rows : List D.Event) → Dec (Σ[ target ∈ Core.State ] B.Run s rows target)
decide-run s rows with Decision.hasTrace? (Decision.τAccReach-all tau-accessible s) rows
... | yes (target , witness) = yes (target , to-run witness)
... | no absent = no λ { (target , source) → absent (target , from-run source) }
