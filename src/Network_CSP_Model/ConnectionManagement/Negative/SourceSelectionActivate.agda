{-# OPTIONS --guardedness #-}

-- Actual eligible set/quota at this reached full-profile selection boundary.
module ConnectionManagement.Negative.SourceSelectionActivate where
open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.Negative.FullConfiguredPromote as Prefix
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.SourceInputs.Ranking as Rank
import ConnectionManagement.Scenarios.Admission as A
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
current : Sub.Configuration
current = PS.machine (K.peers (V.base (B.runtime Prefix.s14)))
selectionInputs : List PeerAddr × ℕ
selectionInputs = G.eligible (Sub.now current) G.activate (Sub.privateState current) ,
  G.quota G.activate (Sub.privateState current)
source-inputs : selectionInputs ≡ (remote A.key₀ ∷ [] , 1)
source-inputs = refl

-- Selected list equals the fixture input for every policy ranking.
ranking-independent : ∀ less → Rank.pick less 1 (remote A.key₀ ∷ []) ≡ (remote A.key₀ ∷ [])
ranking-independent less = Rank.singleton less (remote A.key₀)

-- Therefore the real governor decision, not just set cardinality, is equal.
decision-independent : ∀ less →
  G.choose (Sub.now current) (Rank.pick less 1 (remote A.key₀ ∷ [])) (Sub.privateState current) ≡
  G.choose (Sub.now current) (remote A.key₀ ∷ []) (Sub.privateState current)
decision-independent less = cong (λ ps → G.choose (Sub.now current) ps (Sub.privateState current))
  (ranking-independent less)

-- The reached successful activation reads the initializer's policy delay.
-- Policies.hs:171 supplies 120; Subsystem.initial currently supplies 60.
open import ConnectionManagement.Store using (lookup)
open import Data.Maybe using (map)
open import Relation.Binary.PropositionalEquality using (_≢_)
model-delay : Sub.clearFailDelay current ≡ 60
model-delay = refl
completion : G.Completion
completion = G.completion (G.job G.activate (remote A.key₀) (just (ident 0))) G.succeeded 0
deadline : ℕ → Maybe (Maybe ℕ)
deadline delay = map G.clearFailuresAt (lookup (remote A.key₀)
  (G.knownPeers (G.complete 5 delay 0 completion (Sub.privateState current))))
model-deadline : deadline (Sub.clearFailDelay current) ≡ just (just 60)
model-deadline = refl
source-deadline : deadline 120 ≡ just (just 120)
source-deadline = refl
deadlines-differ : deadline (Sub.clearFailDelay current) ≢ deadline 120
deadlines-differ ()
