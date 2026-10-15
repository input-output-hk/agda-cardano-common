{-# OPTIONS --safe #-}

-- Format: `sessions client server ...`, then `<zero-based id> <event>`.
-- Each id denotes a distinct session generation, even on a reused connection.
module Cardano_network.Replay.ParseInterleaved where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; words; lines; intersperse; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Cardano_network.Replay.Parse
open import Cardano_network.Replay.LeiosFetchSession using (E)
open import Cardano_network.Replay.LeiosFetchInterleaved using (Events; States)

-- Parse a manifest role keyword.
role : String → Maybe Role
role "client" = just client
role "server" = just server
role _ = nothing

-- Parse all manifest roles in session-id order.
roles : List String → Maybe (List Role)
roles [] = just []
roles (r ∷ rs) = role r >>= λ r′ → roles rs >>= λ rs′ → just (r′ ∷ rs′)

-- Bounds-check a numerical tag and inject the event into its component.
tag : (n : ℕ) → ℕ → E → Maybe (Events n)
tag zero i e = nothing
tag (suc n) zero e = just (inj₁ e)
tag (suc n) (suc i) e = tag n i e >>= λ e′ → just (inj₂ e′)

-- Parse an event and reject undeclared session ids.
event : (n : ℕ) → String → Maybe (Events n)
event n l with words l
... | i ∷ ws = dec i >>= λ i′ → parseEvent (intersperse " " ws) >>= tag n i′
... | [] = nothing

-- Parse tagged events with original normalized-file line numbers.
events : (n : ℕ) → ℕ → List String → (ℕ × String) ⊎ List (Events n)
events n i [] = inj₂ []
events n i (l ∷ ls) with event n l
... | nothing = inj₁ (i , l)
... | just e = map₂ (e ∷_) (events n (suc i) ls)

-- A manifest and an ordered event stream, or the first malformed line.
parse : String → (ℕ × String) ⊎ Σ (List Role) (λ rs → List (Events (length rs)))
parse s with lines s
... | [] = inj₁ (1 , "")
... | h ∷ ls with words h
...   | "sessions" ∷ ws with roles ws
...     | nothing = inj₁ (1 , h)
...     | just rs = map₂ (rs ,_) (events (length rs) 2 ls)
parse s | h ∷ ls | _ = inj₁ (1 , h)

-- Recover the numerical tag for diagnostics.
index : ∀ {n} → Events n → ℕ
index {suc n} (inj₁ e) = zero
index {suc n} (inj₂ e) = suc (index e)

-- Recover the local event for diagnostics.
localEvent : ∀ {n} → Events n → E
localEvent {suc n} (inj₁ e) = e
localEvent {suc n} (inj₂ e) = localEvent e

-- Print the state of the component targeted by a rejected event.
componentState : ∀ {n} → States n → Events n → String
componentState {suc n} (s , ss) (inj₁ e) = showSt s
componentState {suc n} (s , ss) (inj₂ e) = componentState ss e
