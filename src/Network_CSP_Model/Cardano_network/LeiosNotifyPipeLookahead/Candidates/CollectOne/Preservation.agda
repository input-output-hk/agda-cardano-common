{-# OPTIONS --safe #-}

-- Fresh finite source-action languages, and therefore exact local wire languages, coincide.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Preservation
  (Notification : Set) where

open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Contract Notification as W
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Forward Notification as F
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Backward Notification as R

-- Membership quantifies the target state, not a preselected favorable continuation.
CandidateSource : C.Contract → List C.Action → Set
CandidateSource p actions = Σ[ target ∈ C.State ] C.Run p C.initial actions target

-- The baseline uses exactly the same source-action datatype and callback contract.
BaselineSource : C.Contract → List C.Action → Set
BaselineSource p actions = Σ[ target ∈ B.State ] B.Run p B.initial actions target

-- Every fresh candidate source trace is allowed by the unchanged baseline.
candidate-in-baseline : ∀ {p actions} → CandidateSource p actions → BaselineSource p actions
candidate-in-baseline (target , execution) with F.from-initial execution
... | extra , compatible , baseline = F.lift extra target , baseline

-- Every fresh baseline source trace has a candidate realization with identical actions.
baseline-in-candidate : ∀ {p actions} → BaselineSource p actions → CandidateSource p actions
baseline-in-candidate (target , execution) with R.from-initial execution
... | final , candidate , relation = final , candidate

-- Both inclusions preserve reply-selection values as well as wire observations.
source-equivalence : ∀ p actions →
  (CandidateSource p actions → BaselineSource p actions) ×
  (BaselineSource p actions → CandidateSource p actions)
source-equivalence p actions = candidate-in-baseline , baseline-in-candidate

-- Exact local wire membership erases only selection and hides all internal steps.
CandidateWire : C.Contract → List W.Wire → Set
CandidateWire p rows = Σ[ actions ∈ List C.Action ] Σ[ target ∈ C.State ]
  (C.Run p C.initial actions target × W.wire actions ≡ rows)

-- The shared wire map also applies to baseline actions without any payload coercion.
BaselineWire : C.Contract → List W.Wire → Set
BaselineWire p rows = Σ[ actions ∈ List C.Action ] Σ[ target ∈ B.State ]
  (B.Run p B.initial actions target × W.wire actions ≡ rows)

-- Candidate-to-baseline wire inclusion has no range, resource or readiness premise.
candidate-wire-in-baseline : ∀ {p rows} → CandidateWire p rows → BaselineWire p rows
candidate-wire-in-baseline (actions , target , execution , observed) with F.from-initial execution
... | extra , compatible , baseline = actions , F.lift extra target , baseline , observed

-- The reverse direction realizes the same wire trace, not a weakened observation.
baseline-wire-in-candidate : ∀ {p rows} → BaselineWire p rows → CandidateWire p rows
baseline-wire-in-candidate (actions , target , execution , observed) with R.from-initial execution
... | final , candidate , relation = actions , final , candidate , observed

-- This equivalence concerns finite source/wire traces, not ticks, failures or runtime behavior.
wire-equivalence : ∀ p rows →
  (CandidateWire p rows → BaselineWire p rows) ×
  (BaselineWire p rows → CandidateWire p rows)
wire-equivalence p rows = candidate-wire-in-baseline , baseline-wire-in-candidate
