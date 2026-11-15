{-# OPTIONS --guardedness #-}

-- Reached decision sets and the source clearing deadline in the source run.
module ConnectionManagement.SourceInputs.SourcePolicyBoundaries where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.Policy as Policy
import ConnectionManagement.Negative.FullConfiguredAcquire as Acquire
import ConnectionManagement.Negative.FullConfiguredPromote as Promote
import ConnectionManagement.Negative.FullConfiguredDemote as Demote
import ConnectionManagement.Negative.FullConfiguredHot as Hot
import ConnectionManagement.Negative.FullConfiguredCloseBudget4 as Close
import ConnectionManagement.Negative.SourceSelectionActivate as Activation
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.State as Shared
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (map)
import ConnectionManagement.SourceInputs.Ranking as Rank
import ConnectionManagement.Scenarios.Admission as A

machine : V.Runtime → Sub.Configuration
machine s = PS.machine (K.peers (V.base (Policy.runtime s)))
inputs : Governor.Kind → Sub.Configuration → List PeerAddr × ℕ
inputs k c = Governor.eligible (Sub.now c) k (Sub.privateState c) , Governor.quota k (Sub.privateState c)
initial-inputs : inputs Governor.establish (machine Acquire.s3) ≡ (Rank.firstPeers , 2)
initial-inputs = refl
activate-inputs : inputs Governor.activate (machine (B.runtime Promote.s14)) ≡ (remote A.key₀ ∷ [] , 1)
activate-inputs = refl
deactivate-inputs : inputs Governor.deactivate (machine (B.runtime Demote.s11)) ≡ (remote A.key₀ ∷ [] , 1)
deactivate-inputs = refl
close-inputs : inputs Governor.close (machine (B.runtime Close.s0)) ≡ (remote A.key₀ ∷ [] , 1)
close-inputs = refl

-- Source CM acquisition is reached with an actually empty map, before its
-- reservation. The source's consumed split is covered by DiffusionSeeds.
acquire-empty : Shared.mapCell (Shared.cm (shared (Policy.runtime Acquire.s10))) ≡ Shared.full []
acquire-empty = refl

activated : Sub.Configuration
activated = machine (B.runtime Hot.s12)
source-stored-deadline : map Governor.clearFailuresAt
  (lookup (remote A.key₀) (Governor.knownPeers (Sub.privateState activated))) ≡ just (just 123)
source-stored-deadline = refl
