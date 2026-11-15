{-# OPTIONS --guardedness #-}

-- Whole configured outbound execution for every committed policy history;
-- includes the separate diffusion split topology and CM empty-bucket reader.
module ConnectionManagement.SourceInputs.SeededConfigured where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.SourceInputs.SourcePolicyOutbound as Source
import ConnectionManagement.SourceInputs.SeededSchedule as Schedule
import ConnectionManagement.SourceInputs.PolicyHistory as H
import ConnectionManagement.SourceInputs.DiffusionSeeds as D
import ConnectionManagement.SourceInputs.Policy as Policy
import ConnectionManagement.SourceInputs.SourcePolicyBoundaries as Boundaries
import ConnectionManagement.SourceInputs.Negotiation as Negotiation
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.SourceNegotiationOutbound as Offers
open import ConnectionManagement.SourceInputs.Schedule using (at; replace; replace-same)
import ConnectionManagement.Rules.OutboundAcquire as Acquire
open import Data.Product using (_×_; proj₁)
open import ConnectionManagement.Store using (Store)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong)

module AllSeeds (Seed : Set) (split : Seed → Seed × Seed)
  (ranking : H.Stage → Seed → PeerAddr → PeerAddr → Bool)
  (randomMember : Seed → Store LocalKey EntryId → Maybe EntryId) where
  module Seeds = D.Seeds Seed split
  module CM = Seeds.Lookup randomMember
  module Reader = Schedule.Seeded Seed split ranking

  -- The source split topology chooses the remote-CM generator. The source
  -- acquisition uses and commits its split, yet every diRng yields nothing
  -- on the reached empty bucket (Boundaries.acquire-empty). No later random
  -- CM/pruning/failure/fuzz read occurs in this selected successful schedule.
  diffusion-acquire : ∀ di → proj₁ (CM.acquire (Seeds.remoteCM2 (Seeds.diffusion di))
    (remote A.key₀) []) ≡ nothing
  diffusion-acquire di = refl

  -- The independent policy TVar is read by History, never identified with a
  -- residual diffusion child. Retry/restart draws affect later policy reads,
  -- which are all covered by history-independent, not treated as unread.
  abstract
    initialized-contracts : ∀ {policySeed xs finalSeed} →
      Reader.Tx.History H.establish policySeed xs finalSeed →
      B.Runs Source.start (Schedule.schedule xs) Source.endpoint
    initialized-contracts h = subst (λ as → B.Runs Source.start as Source.endpoint)
      (sym (Reader.history-schedule h)) Source.initialized-contracts

    initialized-frontend : ∀ {policySeed xs finalSeed} →
      Reader.Tx.History H.establish policySeed xs finalSeed →
      V.Runs Policy.source120 (B.erase (Schedule.schedule xs)) (B.runtime Source.endpoint)
    initialized-frontend h = B.project (initialized-contracts h)

    -- Converse existence: every initial policy seed admits the full run.
    every-policy-seed : (seed : Seed) → B.Runs Source.start
      (Schedule.schedule (H.visible H.establish)) Source.endpoint
    every-policy-seed seed = initialized-contracts (Reader.Tx.canonical H.establish seed)

  -- Derive the actual CM acquisition input from diRng, then replace its
  -- real wrapper position as well as the four committed policy decisions.
  acquire-input : Seed → B.Action
  acquire-input di = B.run (acquire (Acquire.select (proj₁
    (CM.acquire (Seeds.remoteCM2 (Seeds.diffusion di)) (remote A.key₀) []))))
  acquire-position : ∀ di → at 10 Source.schedule ≡ just (acquire-input di)
  acquire-position di = refl
  source-schedule : Seed → List (List PeerAddr) → List B.Action
  source-schedule di xs = replace 10 (acquire-input di) (Schedule.schedule xs)
  source-schedule-exact : ∀ di {policySeed xs finalSeed} →
    Reader.Tx.History H.establish policySeed xs finalSeed →
    source-schedule di xs ≡ Source.schedule
  source-schedule-exact di h = trans
    (cong (replace 10 (acquire-input di)) (Reader.history-schedule h))
    (replace-same 10 (acquire-input di) Source.schedule (acquire-position di))

  abstract
    initialized-source-contracts : ∀ di {policySeed xs finalSeed} →
      Reader.Tx.History H.establish policySeed xs finalSeed →
      B.Runs Source.start (source-schedule di xs) Source.endpoint
    initialized-source-contracts di h = subst
      (λ as → B.Runs Source.start as Source.endpoint)
      (sym (source-schedule-exact di h)) Source.initialized-contracts
    initialized-source-frontend : ∀ di {policySeed xs finalSeed} →
      Reader.Tx.History H.establish policySeed xs finalSeed →
      V.Runs Policy.source120 (B.erase (source-schedule di xs)) (B.runtime Source.endpoint)
    initialized-source-frontend di h = B.project (initialized-source-contracts di h)
    every-source-seed : (di policySeed : Seed) → B.Runs Source.start
      (source-schedule di (H.visible H.establish)) Source.endpoint
    every-source-seed di policySeed = initialized-source-contracts di
      (Reader.Tx.canonical H.establish policySeed)

-- Source V15/data/flow/layout remains the actual negotiation input in the
-- source-120 run. Offers.schedule-exact is independent of runtime fields.
negotiated-schedule : Offers.schedule ≡ Source.schedule
negotiated-schedule = Offers.schedule-exact
