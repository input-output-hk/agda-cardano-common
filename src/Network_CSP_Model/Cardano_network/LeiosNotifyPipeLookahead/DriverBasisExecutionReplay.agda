{-# OPTIONS --safe #-}

-- Generic weak replay over the finite basis menu, with inherited hidden termination.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.List using (List)
module Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecutionReplay
  (Notification : Set) (notificationEq : DecidableEquality Notification)
  (basis : List Notification) where

open import Level using (0ℓ)
open import Data.Unit using (⊤)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Induction.WellFounded using (Acc; acc)
import Semantics.Replay as R
import Semantics.Replay.Decide as Decide
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification ⊤ basis as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ⊤ notificationEq as DX
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Notification notificationEq basis as Menu
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification ⊤ as Rank

-- Event equality preserves roles, directions, cancellation/Done and exact normal payloads.
eventEq : DecidableEquality D.Event
eventEq (D.clientSend m) (D.clientSend n) with DX.clientMessageEq m n
... | yes refl = yes refl
... | no unequal = no λ { refl → unequal refl }
eventEq (D.clientSend _) (D.serverSend _) = no λ ()
eventEq (D.clientSend _) (D.clientRecv _) = no λ ()
eventEq (D.clientSend _) (D.serverRecv _) = no λ ()
eventEq (D.serverSend _) (D.clientSend _) = no λ ()
eventEq (D.serverSend m) (D.serverSend n) with DX.serverMessageEq m n
... | yes refl = yes refl
... | no unequal = no λ { refl → unequal refl }
eventEq (D.serverSend _) (D.clientRecv _) = no λ ()
eventEq (D.serverSend _) (D.serverRecv _) = no λ ()
eventEq (D.clientRecv _) (D.clientSend _) = no λ ()
eventEq (D.clientRecv _) (D.serverSend _) = no λ ()
eventEq (D.clientRecv m) (D.clientRecv n) with DX.serverMessageEq m n
... | yes refl = yes refl
... | no unequal = no λ { refl → unequal refl }
eventEq (D.clientRecv _) (D.serverRecv _) = no λ ()
eventEq (D.serverRecv _) (D.clientSend _) = no λ ()
eventEq (D.serverRecv _) (D.serverSend _) = no λ ()
eventEq (D.serverRecv _) (D.clientRecv _) = no λ ()
eventEq (D.serverRecv m) (D.serverRecv n) with DX.clientMessageEq m n
... | yes refl = yes refl
... | no unequal = no λ { refl → unequal refl }

-- Certified visible lookup has zero or one target and never changes packet transport twice.
after : S.Contract → D.State → D.Event → List D.State
after p s e with DX.lookup p e s
... | just (next , pr) = next ∷ []
... | nothing = []

-- Every listed visible successor retains the original independent DriverModel.Step.
after-sound : ∀ {p s e t} → t ∈ after p s e → B.Step p s e t
after-sound {p} {s} {e} with DX.lookup p e s
... | just (next , pr) = λ { (here refl) → pr ; (there ()) }
... | nothing = λ ()

-- The singleton visible menu omits no actual exact source record target.
after-complete : ∀ {p s e t} → B.Step p s e t → t ∈ after p s e
after-complete {p} {s} {e} pr with DX.lookup p e s | DX.next-complete pr
... | just (_ , _) | refl = here refl

-- Both successor families are finite, sound and complete for this explicit basis relation.
replay : S.Contract → R.Replay 0ℓ D.State D.Event
replay p = record
  { _-[_]→_ = B.Step p
  ; _-τ→_ = B.Tau p
  ; _≟E_ = eventEq
  ; after = after p
  ; taus = Menu.targets p
  ; after-sound = after-sound
  ; taus-sound = Menu.target-sound
  ; after-complete = after-complete
  ; taus-complete = Menu.target-complete
  }

-- All certificates below retain their exact contract rather than silently fixing node policy.
module For (p : S.Contract) where
  module Trace = R.Traces (replay p)
  module Decision = Decide.Decider (replay p)

  -- Generic replay witnesses transcribe to the explicit restricted driver run unchanged.
  to-run : ∀ {s es t} → Trace._⇒⟨_⟩_ s es t → B.Run p s es t
  to-run Trace.done = B.stop
  to-run (Trace.tau step rest) = B.internal step (to-run rest)
  to-run (Trace.vis step rest) = B.visible step (to-run rest)

  -- Every restricted driver prefix is represented by the generic weak-trace semantics.
  from-run : ∀ {s es t} → B.Run p s es t → Trace._⇒⟨_⟩_ s es t
  from-run B.stop = Trace.done
  from-run (B.internal step rest) = Trace.tau step (from-run rest)
  from-run (B.visible step rest) = Trace.vis step (from-run rest)

  -- Restricting server callback values preserves the existing raw hidden accessibility proof.
  from-accessible : ∀ {s} → Acc (λ t s → D.Tau p s t) s → Decision.τAcc s
  from-accessible (acc smaller) = Decision.acc λ step →
    from-accessible (smaller (B.sound-tau step))

  -- All states have terminating hidden closure, independently of a search budget or planner cap.
  tau-accessible : ∀ s → Decision.τAcc s
  tau-accessible s = from-accessible (Rank.tau-accessible p s)

  -- Every reachable state inherits its certificate; no additional capture premise is invented.
  tau-reachable : ∀ s → Decision.τAccReach s
  tau-reachable = Decision.τAccReach-all tau-accessible
