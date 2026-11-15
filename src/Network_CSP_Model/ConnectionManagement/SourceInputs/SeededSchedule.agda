{-# OPTIONS --guardedness #-}

-- Replaces every actual policy decision in the full configured schedule by
-- its committed STM observation. No supplied selected set bypasses the reader.
module ConnectionManagement.SourceInputs.SeededSchedule where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.Negative.FullConfiguredWitness as Reduced
import ConnectionManagement.SourceInputs.PolicyHistory as H
open import ConnectionManagement.SourceInputs.Schedule using (at; replace; replace-same)
import ConnectionManagement.Subsystem as Sub
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

input : List PeerAddr → B.Action
input ps′ = B.run (ps (Sub.selectPolicy ps′))

-- Zero-based wrapper positions, verified against the entire 381-input run.
position-initial : at 3 Reduced.schedule ≡ just (input (H.expected H.establish))
position-initial = refl
position-activate : at 78 Reduced.schedule ≡ just (input (H.expected H.activate))
position-activate = refl
position-deactivate : at 152 Reduced.schedule ≡ just (input (H.expected H.deactivate))
position-deactivate = refl
position-close : at 293 Reduced.schedule ≡ just (input (H.expected H.close))
position-close = refl

-- Replacements are performed at their original positions (length unchanged).
schedule : List (List PeerAddr) → List B.Action
schedule (a ∷ b ∷ c ∷ d ∷ []) = replace 293 (input d)
  (replace 152 (input c) (replace 78 (input b) (replace 3 (input a) Reduced.schedule)))
schedule _ = []

canonical-schedule : schedule (H.visible H.establish) ≡ Reduced.schedule
canonical-schedule
  rewrite replace-same 3 (input (H.expected H.establish)) Reduced.schedule position-initial
        | replace-same 78 (input (H.expected H.activate)) Reduced.schedule position-activate
        | replace-same 152 (input (H.expected H.deactivate)) Reduced.schedule position-deactivate
        | replace-same 293 (input (H.expected H.close)) Reduced.schedule position-close = refl

-- Any split algorithm, initial seed, metric ranking and finite rollback/retry
-- history at these reached eligible sets yields the identical full schedule.
module Seeded (Seed : Set)
  (split : Seed → Seed × Seed)
  (ranking : H.Stage → Seed → PeerAddr → PeerAddr → Bool) where
  module Tx = H.Transactions Seed split ranking
  history-schedule : ∀ {s xs t} → Tx.History H.establish s xs t → schedule xs ≡ Reduced.schedule
  history-schedule h = trans (cong schedule (Tx.history-independent h)) canonical-schedule
