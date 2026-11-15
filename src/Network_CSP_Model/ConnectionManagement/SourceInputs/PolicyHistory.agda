{-# OPTIONS --guardedness #-}

-- Policies.hs:126-142,179-221,260-267 at network 2f1c154.
-- A source-policy transaction reads a seed, splits it, ranks the available
-- set using the left child and commits the right child; aborted attempts
-- restore the original TVar. No random algorithm/distribution is assumed.
module ConnectionManagement.SourceInputs.PolicyHistory where
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import ConnectionManagement.Domain using (PeerAddr; remote)
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.SourceInputs.Ranking as Rank

data Stage : Set where
  establish activate deactivate close finished : Stage
next : Stage → Stage
next establish = activate
next activate = deactivate
next deactivate = close
next close = finished
next finished = finished
expected : Stage → List PeerAddr
expected establish = Rank.firstPeers
expected finished = []
expected _ = remote A.key₀ ∷ []
visible : Stage → List (List PeerAddr)
visible establish = Rank.firstPeers ∷ (remote A.key₀ ∷ []) ∷ (remote A.key₀ ∷ []) ∷ (remote A.key₀ ∷ []) ∷ []
visible activate = (remote A.key₀ ∷ []) ∷ (remote A.key₀ ∷ []) ∷ (remote A.key₀ ∷ []) ∷ []
visible deactivate = (remote A.key₀ ∷ []) ∷ (remote A.key₀ ∷ []) ∷ []
visible close = (remote A.key₀ ∷ []) ∷ []
visible finished = []

-- Seed can be StdGen, a tuple of all diffusion children and an independent
-- policy TVar, or any other carrier. This quantifies over EVERY split function
-- and EVERY seed-dependent comparison, including arbitrary metric/tie inputs.
module Transactions (Seed : Set) (split : Seed → Seed × Seed)
  (ranking : Stage → Seed → PeerAddr → PeerAddr → Bool) where

  picked : Stage → Seed → List PeerAddr
  picked establish s = Rank.pick (ranking establish (proj₁ (split s))) 2 Rank.firstPeers
  picked finished s = []
  picked k s = Rank.pick (ranking k (proj₁ (split s))) 1 (remote A.key₀ ∷ [])

  seed-independent : ∀ k s → picked k s ≡ expected k
  seed-independent establish s = Rank.all-two (ranking establish (proj₁ (split s)))
  seed-independent activate s = refl
  seed-independent deactivate s = refl
  seed-independent close s = refl
  seed-independent finished s = refl

  -- Histories include any finite number of STM retries/rollbacks, with their
  -- actual speculative ranking evaluated but no visible publication. A restart
  -- permits an arbitrary changed seed after conflicting transactions. Only
  -- successful commits publish a set and retain the right split child.
  data History : Stage → Seed → List (List PeerAddr) → Seed → Set where
    done : ∀ {s} → History finished s [] s
    rollback : ∀ {k s xs t} → History k s xs t → History k s xs t
    restart : ∀ {k s s′ xs t} → History k s′ xs t → History k s xs t
    commit-establish : ∀ {s xs t} → History (next establish) (proj₂ (split s)) xs t →
      History establish s (picked establish s ∷ xs) t
    commit-activate : ∀ {s xs t} → History (next activate) (proj₂ (split s)) xs t →
      History activate s (picked activate s ∷ xs) t
    commit-deactivate : ∀ {s xs t} → History (next deactivate) (proj₂ (split s)) xs t →
      History deactivate s (picked deactivate s ∷ xs) t
    commit-close : ∀ {s xs t} → History (next close) (proj₂ (split s)) xs t →
      History close s (picked close s ∷ xs) t

  -- Erasing speculative work yields exactly the same committed observations.
  history-independent : ∀ {k s xs t} → History k s xs t → xs ≡ visible k
  history-independent done = refl
  history-independent (rollback h) = history-independent h
  history-independent (restart h) = history-independent h
  history-independent (commit-establish {s = s} h)
    rewrite seed-independent establish s | history-independent h = refl
  history-independent (commit-activate {s = s} h)
    rewrite seed-independent activate s | history-independent h = refl
  history-independent (commit-deactivate {s = s} h)
    rewrite seed-independent deactivate s | history-independent h = refl
  history-independent (commit-close {s = s} h)
    rewrite seed-independent close s | history-independent h = refl

  advanceSeed : Seed → Seed
  advanceSeed s = proj₂ (split s)
  finalSeed : Stage → Seed → Seed
  finalSeed establish s = advanceSeed (advanceSeed (advanceSeed (advanceSeed s)))
  finalSeed activate s = advanceSeed (advanceSeed (advanceSeed s))
  finalSeed deactivate s = advanceSeed (advanceSeed s)
  finalSeed close s = advanceSeed s
  finalSeed finished s = s

  -- Converse: every initial seed has a complete canonical committed history.
  canonical : ∀ k s → History k s (visible k) (finalSeed k s)
  canonical establish s = subst
    (λ ps → History establish s (ps ∷ visible activate) (finalSeed establish s))
    (seed-independent establish s)
    (commit-establish (commit-activate (commit-deactivate (commit-close done))))
  canonical activate s = commit-activate (commit-deactivate (commit-close done))
  canonical deactivate s = commit-deactivate (commit-close done)
  canonical close s = commit-close done
  canonical finished s = done
