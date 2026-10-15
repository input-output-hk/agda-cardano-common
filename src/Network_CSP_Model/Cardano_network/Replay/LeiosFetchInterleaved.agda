{-# OPTIONS --safe #-}

-- One finite product model for an ordered log of independent sessions.
-- A manifest fixes the role of each zero-based session generation.
module Cardano_network.Replay.LeiosFetchInterleaved where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (Dec)
open import Semantics.Replay
import Semantics.Replay.Empty as Empty
open import Semantics.Replay.Interleave using (module Product)
open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.LeiosFetchDecide using (module Cert)
open import Cardano_network.Replay.Parse using (Role; client; server)

-- Nested products retain every session's state independently.
States : ℕ → Set
States zero = ⊤
States (suc n) = St × States n

-- Tags route an event to exactly one of the finitely many sessions.
Events : ℕ → Set
Events zero = ⊥
Events (suc n) = E ⊎ Events n

-- Fold generic heterogeneous interleaving over the session count.
model : (k n : ℕ) → Replay 0ℓ (States n) (Events n)
model k zero = Empty.empty
model k (suc n) = Product.interleave (Spec.leiosFetch k) (model k n)

-- The role fixes a session's initial state.
start : Role → St
start client = client₀
start server = server₀

-- The manifest fixes the product's initial state.
initial : (rs : List Role) → States (length rs)
initial [] = tt
initial (r ∷ rs) = start r , initial rs

-- Decide one component with its existing accessibility certificate.
local? : (k : ℕ) (r : Role) (es : List E) → Dec (Traces.HasTrace (Spec.leiosFetch k) (start r) es)
local? k client = Cert.hasTrace? k (Cert.client-cert k)
local? k server = Cert.hasTrace? k (Cert.server-cert k)

-- A positive answer carries a run of the single product model; a negative
-- answer refutes one projection and therefore every possible global run.
check : (k : ℕ) (rs : List Role) (es : List (Events (length rs))) →
        Dec (Traces.HasTrace (model k (length rs)) (initial rs) es)
check k [] = Empty.empty?
check k (r ∷ rs) = Product.decide (Spec.leiosFetch k) (model k (length rs)) (local? k r) (check k rs)
