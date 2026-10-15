{-# OPTIONS --safe #-}

-- Typed session manifests; bare client/server remain aliases for Fetch.
module Cardano_network.Replay.ParseSessions where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.String using (String; words; lines; intersperse)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Cardano_network.Replay.Sessions
import Cardano_network.Replay.Parse as F
import Cardano_network.Replay.ParseNotify as N
import Cardano_network.Replay.LeiosNotifyPipeline as NP
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String using (_++_)

-- Each token fixes both protocol and role for a session generation.
session : String → Maybe Session
session "client" = just (fetch client)
session "server" = just (fetch server)
session "fetch:client" = just (fetch client)
session "fetch:server" = just (fetch server)
session "notify:client" = just (notify client)
session "notify:server" = just (notify server)
session _ = nothing

-- Parse the manifest once, preserving id order.
sessions : List String → Maybe (List Session)
sessions [] = just []
sessions (s ∷ ss) = session s >>= λ s′ → sessions ss >>= λ ss′ → just (s′ ∷ ss′)

-- Parse exactly the event type named by a manifest entry.
localEvent : (s : Session) → String → Maybe (LocalEvent s)
localEvent (fetch _) = F.parseEvent
localEvent (notify _) = N.parseEvent

-- Bounds-check the tag and parse its component's message language.
tagged : (ss : List Session) → ℕ → String → Maybe (Events ss)
tagged [] _ _ = nothing
tagged (s ∷ ss) zero txt = localEvent s txt >>= λ e → just (inj₁ e)
tagged (s ∷ ss) (suc i) txt = tagged ss i txt >>= λ e → just (inj₂ e)

-- One globally ordered event, with a numerical session tag.
event : (ss : List Session) → String → Maybe (Events ss)
event ss txt with words txt
... | i ∷ ws = F.dec i >>= λ i′ → tagged ss i′ (intersperse " " ws)
... | [] = nothing

-- Parse a whole stream with normalized-file line numbers on errors.
events : (ss : List Session) → ℕ → List String → (ℕ × String) ⊎ List (Events ss)
events ss i [] = inj₂ []
events ss i (l ∷ ls) with event ss l
... | nothing = inj₁ (i , l)
... | just e = map₂ (e ∷_) (events ss (suc i) ls)

-- Parse a typed manifest plus its dependent event list.
parse : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parse txt with lines txt
... | [] = inj₁ (1 , "")
... | h ∷ ls with words h
...   | "sessions" ∷ ws with sessions ws
...     | nothing = inj₁ (1 , h)
...     | just ss = map₂ (ss ,_) (events ss 2 ls)
parse txt | h ∷ ls | _ = inj₁ (1 , h)

-- A single Notify session uses the existing role-header convention.
parseNotify : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseNotify txt with lines txt
... | [] = inj₁ (1 , "")
... | h ∷ ls with F.parseRole h
...   | nothing = inj₁ (1 , h)
...   | just r = map₂ ((notify r ∷ []) ,_) (go r 2 ls)
  where
  -- Parse untagged local lines into the one-component product.
  go : (r : Role) → ℕ → List String → (ℕ × String) ⊎ List (Events (notify r ∷ []))
  go r i [] = inj₂ []
  go r i (l ∷ ls) with N.parseEvent l
  ... | nothing = inj₁ (i , l)
  ... | just e = map₂ (inj₁ e ∷_) (go r (suc i) ls)

-- Recover the numerical id for diagnostics.
index : ∀ {ss} → Events ss → ℕ
index {s ∷ ss} (inj₁ _) = zero
index {s ∷ ss} (inj₂ e) = suc (index e)

-- A role label used in component diagnostics.
roleName : Role → String
roleName client = "client"
roleName server = "server"

-- Report the outstanding credit count for a pipelined Notify component.
showNotifyState : Role → NP.St → String
showNotifyState r (NP.openN n) = "notify " ++ roleName r ++ " open, outstanding " ++ showℕ n
showNotifyState _ NP.closed = "notify closed after Done (accepts nothing)"

-- Print a local event with its protocol's canonical syntax.
showLocal : (s : Session) → LocalEvent s → String
showLocal (fetch _) = F.showEvent
showLocal (notify _) = N.showEvent

-- Print the event at its selected component.
showEvent : ∀ {ss} → Events ss → String
showEvent {s ∷ ss} (inj₁ e) = showLocal s e
showEvent {s ∷ ss} (inj₂ e) = showEvent e

-- Explain a component's current agency and pending work.
showState : (s : Session) → LocalState s → String
showState (fetch _) = F.showSt
showState (notify r) = showNotifyState r

-- Select only the failing event's component for diagnostics.
componentState : ∀ {ss} → States ss → Events ss → String
componentState {s ∷ ss} (st , rest) (inj₁ e) = showState s st
componentState {s ∷ ss} (st , rest) (inj₂ e) = componentState rest e
