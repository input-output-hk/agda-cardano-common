{-# OPTIONS --guardedness #-}

-- Actual native scheduler paths inherit constructive accessibility and shutdown step bounds.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingBridge (p : Params) (Return : Set) where

open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s; z≤n)
open import Data.List using (List)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded using (Acc; acc)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as Native
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification Return as Cost
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingRank Notification Return as Rank
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Shutdown
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge p Return as Bridge
import Semantics.TauAcc {E = Native.Events} {I = Native.Branches} as Tau

-- The native callback contract and endpoint tags stay fixed throughout every path.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- The existing model supplies the unchanged native transitions.
  module Tree = Native.At contract cl sl cd sd
  -- Actual native steps are inverted with their exact source target equality.
  module Proof = Bridge.At contract cl sl cd sd
  open Native using (module LTS; module Traces)

  -- Every actual hidden native step has a strictly smaller source potential.
  hidden-decreases : ∀ {s} {P : Native.Proc} → Tree.tree s LTS.─[ LTS.τ ]─► P →
    Σ[ t ∈ D.State ] (P ≡ Tree.tree t × Cost.rank t < Cost.rank s)
  hidden-decreases step with Proof.hidden-elim step
  ... | t , source , same = t , same , Rank.decreases source

  -- Source accessibility constructs native accessibility without tree-injectivity assumptions.
  from-source : ∀ s → Acc (λ t s → D.Tau contract s t) s → Tau.τ-Acc (Tree.tree s)
  from-source s (acc smaller) = Tau.acc next
    where
    -- Inversion supplies the actual continuation before recurring on smaller source work.
    next : ∀ {P : Native.Proc} → Tree.tree s LTS.─[ LTS.τ ]─► P → Tau.τ-Acc P
    next step with Proof.hidden-elim step
    ... | t , source , refl = from-source t (smaller source)

  -- All native paired source states have finite hidden paths.
  tau-accessible : ∀ s → Tau.τ-Acc (Tree.tree s)
  tau-accessible s = from-source s (Rank.tau-accessible contract s)

  -- The existing semantic bridge turns this constructive certificate into divergence exclusion.
  no-hidden-divergence : ∀ s → ¬ LTS.Diverges (Tree.tree s)
  no-hidden-divergence s = Tau.τ-Acc→¬Div (tau-accessible s)

  -- Actual finite native prefixes also end at a process with no hidden divergence.
  reachable-no-hidden-divergence : ∀ {s es} {P : Native.Proc} →
    Tree.tree s Traces.⟹∖√⟨ es ⟩ P → ¬ LTS.Diverges P
  reachable-no-hidden-divergence trace with Proof.sound trace
  ... | rows , t , matching , source , refl = no-hidden-divergence t

  -- Count actual native hidden and visible transitions, including delayed trace hooks.
  steps : ∀ {P Q : Native.Proc} {es : List LTS.Event} → P Traces.⟹∖√⟨ es ⟩ Q → ℕ
  steps Traces.∖√-refl = 0
  steps (Traces.∖√-τ _ trace) = suc (steps trace)
  steps (Traces.∖√-ev _ trace) = suc (steps trace)

  -- Native shutdown continuations satisfy the same quantitative bound as source executions.
  shutdown-bounded : ∀ {s es P} (trace : Tree.tree s Traces.⟹∖√⟨ es ⟩ P) →
    Shutdown.BothStopping s → steps trace ≤ Cost.rank s
  shutdown-bounded Traces.∖√-refl _ = z≤n
  shutdown-bounded (Traces.∖√-τ step trace) both with Proof.hidden-elim step
  ... | t , source , refl =
    ≤-trans (s≤s (shutdown-bounded trace (Shutdown.tau-stays source both))) (Rank.decreases source)
  shutdown-bounded (Traces.∖√-ev step trace) both with Proof.visible-elim step
  ... | row , t , decoded , source , refl =
    ≤-trans (s≤s (shutdown-bounded trace (Shutdown.step-stays source both))) (Shutdown.visible-decreases source both)
