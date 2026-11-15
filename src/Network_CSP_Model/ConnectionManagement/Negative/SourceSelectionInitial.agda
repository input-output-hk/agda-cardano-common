{-# OPTIONS --guardedness #-}

-- Actual eligible set/quota at this reached full-profile selection boundary.
module ConnectionManagement.Negative.SourceSelectionInitial where
open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.Negative.FullConfiguredAcquire as Prefix
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.SourceInputs.Ranking as Rank
import ConnectionManagement.Scenarios.Admission as A
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

current : Sub.Configuration
current = PS.machine (K.peers (V.base Prefix.s3))
selectionInputs : List PeerAddr × ℕ
selectionInputs = G.eligible (Sub.now current) G.establish (Sub.privateState current) ,
  G.quota G.establish (Sub.privateState current)
source-inputs : selectionInputs ≡ (Rank.firstPeers , 2)
source-inputs = refl

-- Selected list equals the fixture input for every policy ranking.
ranking-independent : ∀ less → Rank.pick less 2 (Rank.firstPeers) ≡ (Rank.firstPeers)
ranking-independent less = Rank.all-two less

-- Therefore the real governor decision, not just set cardinality, is equal.
decision-independent : ∀ less →
  G.choose (Sub.now current) (Rank.pick less 2 (Rank.firstPeers)) (Sub.privateState current) ≡
  G.choose (Sub.now current) (Rank.firstPeers) (Sub.privateState current)
decision-independent less = cong (λ ps → G.choose (Sub.now current) ps (Sub.privateState current))
  (ranking-independent less)

-- The unrestricted model also admits a strict subset when quota is two.
-- This excludes a global two-way source-policy erasure theorem for G.choose.
open import Data.Bool using (true; false)
open import Data.List using (length)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≢_; subst; sym; trans)
chosen : Maybe G.Decision → Bool
chosen nothing = false
chosen (just _) = true
abstract-proper-subset-enabled : chosen (G.choose 0 (remote A.key₀ ∷ []) settings) ≡ true
abstract-proper-subset-enabled = refl
source-proper-subset-impossible : ∀ less → Rank.pick less 2 Rank.firstPeers ≢ (remote A.key₀ ∷ [])
source-proper-subset-impossible less eq with trans (sym (Rank.all-two less)) eq
... | ()
