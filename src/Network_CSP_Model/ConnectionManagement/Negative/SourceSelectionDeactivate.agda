{-# OPTIONS --guardedness #-}

-- Actual eligible set/quota at this reached full-profile selection boundary.
module ConnectionManagement.Negative.SourceSelectionDeactivate where
open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.Negative.FullConfiguredDemote as Prefix
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.SourceInputs.Ranking as Rank
import ConnectionManagement.Scenarios.Admission as A
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
current : Sub.Configuration
current = PS.machine (K.peers (V.base (B.runtime Prefix.s11)))
selectionInputs : List PeerAddr × ℕ
selectionInputs = G.eligible (Sub.now current) G.deactivate (Sub.privateState current) ,
  G.quota G.deactivate (Sub.privateState current)
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
