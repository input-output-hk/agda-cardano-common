{-# OPTIONS --guardedness #-}

-- Starting protocols changes jobs/status, never the mux's connection key.
module ConnectionManagement.Properties.MuxStartReferences where

open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.MuxRuntime as M

-- Both successful and exceptional outcomes carry the updated mux.
resultMux : M.StartResult → M.Mux
resultMux (M.startedAll m) = m
resultMux (M.startFailed _ _ m) = m

one-key : ∀ p m → M.key (resultMux (M.startOne p m)) ≡ M.key m
one-key p m with lookup (number p) (M.protocols m)
... | nothing = refl
... | just st with M.status m
...   | M.stopping = refl
...   | M.stopped = refl
...   | M.failed _ = refl
...   | M.ready with st
...     | M.idle = refl
...     | M.demand = refl
...     | M.demandAny = refl
...     | M.running = refl

bundle-key : ∀ ps m → M.key (resultMux (M.startBundle ps m)) ≡ M.key m
bundle-key [] m = refl
bundle-key (p ∷ ps) m with M.startOne p m | one-key p m
... | M.startFailed n err updated | same = same
... | M.startedAll updated | same = trans (bundle-key ps updated) same
