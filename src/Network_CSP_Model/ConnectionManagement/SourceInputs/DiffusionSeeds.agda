{-# OPTIONS --guardedness #-}

-- Diffusion.hs:301-308 and Core.hs:1278-1279 / ConnMap.hs:198-210,
-- pinned network 2f1c154. The policy TVar is an independent caller input.
module ConnectionManagement.SourceInputs.DiffusionSeeds where
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (PeerAddr; LocalKey; unknownLocal; EntryId; DecEq-PeerAddr; DecEq-LocalKey)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as S

module Seeds (Seed : Set) (split : Seed → Seed × Seed) where
  record Layout : Set where
    constructor layout
    field ledger churn fuzz localCM remoteCM1 remoteCM2 egress actions : Seed
  open Layout public

  -- Exact source split topology, independent of the random package algorithm.
  diffusion : Seed → Layout
  diffusion di with split di
  ... | ledger , r1 with split r1
  ... | churn , r2 with split r2
  ... | fuzz , r3 with split r3
  ... | localCM , r4 with split r4
  ... | cm1 , r5 with split r5
  ... | cm2 , r6 with split r6
  ... | egress , actions = layout ledger churn fuzz localCM cm1 cm2 egress actions

  -- Only the nonempty known-local branch reads a random index. Keeping that
  -- function arbitrary covers every valid source uniformR implementation.
  module Lookup (randomMember : Seed → Store LocalKey EntryId → Maybe EntryId) where
    remote : Seed → PeerAddr → S.ConnMap → Maybe EntryId
    remote seed peer m with lookup peer m
    ... | nothing = nothing
    ... | just inner with lookup unknownLocal inner
    ... | just e = just e
    ... | nothing with inner
    ... | [] = nothing
    ... | _ ∷ _ = randomMember seed inner

    -- The right child remains committed even though this lookup is empty.
    acquire : Seed → PeerAddr → S.ConnMap → Maybe EntryId × Seed
    acquire seed peer m = remote (proj₁ (split seed)) peer m , proj₂ (split seed)
    empty-result : ∀ seed peer → proj₁ (acquire seed peer []) ≡ nothing
    empty-result seed peer = refl
    retained-child : ∀ seed peer m → proj₂ (acquire seed peer m) ≡ proj₂ (split seed)
    retained-child seed peer m = refl
    all-diffusion-seeds : ∀ di peer →
      proj₁ (acquire (remoteCM2 (diffusion di)) peer []) ≡ nothing
    all-diffusion-seeds di peer = refl
