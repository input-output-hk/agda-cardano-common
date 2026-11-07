{-# OPTIONS --safe #-}

-- Hidden descent after wire-language normalization; no payload finiteness or
-- finite global state graph is assumed by this accessibility theorem.
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreScheduling
  (Notification : Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _<_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Product using (_×_; _,_)
open import Data.Product.Relation.Binary.Lex.Strict using (×-Lex; ×-wellFounded)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeScheduling Notification as Scheduling
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification ⊤ as Rank

-- Only actual local failure consumes this last binary scheduling credit.
aliveBit : Bool → ℕ
aliveBit true = 1
aliveBit false = 0

-- Protocol scheduling, unused admission credit and failure remain separate components.
Measure : Set
Measure = ℕ × (ℕ × ℕ)

-- A primary decrease permits arbitrary later components, including admitted credits.
_≺_ : Measure → Measure → Set
_≺_ = ×-Lex _≡_ _<_ (×-Lex _≡_ _<_ _<_)

-- Existing protocol potential is reused without changing control or packet accounting.
rank : Core.State → Measure
rank state = Cost.rank (Core.driverState state) ,
  (Q.free (Core.queueState state) , aliveBit (Core.clientAlive state))

-- Successful normal handling is one existing generic driver callback step.
handler-driver : ∀ {s t message} → Node.Step s (Node.handledNormal message) t →
  D.Tau S.nodeNext (Node.driverState s) (Node.driverState t)
handler-driver (Node.normalHandler {raw = D.pair _ _ _ _ _ _ _ _} (Client.handled proof)) =
  D.clientCallback D.handled proof

-- Every nonstuttering reduced hidden transition strictly consumes the combined measure.
decreases : ∀ {s t} → Core.Tau s t → rank t ≺ rank s
decreases (Core.operational proof) = inj₁ (Scheduling.decreases proof)
decreases (Core.offered (Node.applicationInput (Server.applicationOffer active Q.enqueued)) nonzero) =
  inj₂ (refl , inj₁ ≤-refl)
decreases (Core.offered (Node.applicationInput (Server.applicationOffer active Q.dropped)) nonzero) =
  ⊥-elim (nonzero refl)
decreases (Core.handled proof) = inj₁ (Rank.decreases (handler-driver proof))
decreases (Core.rejected (Node.canceledHandlerExit _)) =
  inj₂ (refl , inj₂ (refl , ≤-refl))

-- Natural well-foundedness is closed under the two nested lexicographic products.
rank-wellFounded : WellFounded _≺_
rank-wellFounded = ×-wellFounded <-wellFounded (×-wellFounded <-wellFounded <-wellFounded)

-- Strict measure descent lifts to the actual reduced hidden-transition relation.
from-rank : ∀ s → Acc _≺_ (rank s) → Acc (λ t s → Core.Tau s t) s
from-rank s (acc smaller) = acc λ {t} transition → from-rank t (smaller (decreases transition))

-- Every reduced state has finite hidden paths, including arbitrary stored queues and credits.
tau-accessible : ∀ s → Acc (λ t s → Core.Tau s t) s
tau-accessible s = from-rank s (rank-wellFounded (rank s))
