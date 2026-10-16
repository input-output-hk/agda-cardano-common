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
import Cardano_network.Replay.LeiosFetchParse as F
import Cardano_network.Replay.LeiosNotifyParse as N
import Cardano_network.Replay.LeiosNotifyPipeline as NP
import Cardano_network.Replay.ChainSyncParse as C
import Cardano_network.Replay.TxSubmission2Parse as T
import Cardano_network.Replay.BlockFetchReport as B
import Cardano_network.Replay.BlockFetchServerReport as BS
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
session "blockfetch:client" = just (blockfetch client)
session "blockfetch:server" = just (blockfetch server)
session "chainsync:client" = just (chainsync client)
session "chainsync:server" = just (chainsync server)
session "txsubmission2:client" = just (txsubmission2 client)
session "txsubmission2:server" = just (txsubmission2 server)
session _ = nothing

-- Parse the manifest once, preserving id order.
sessions : List String → Maybe (List Session)
sessions [] = just []
sessions (s ∷ ss) = session s >>= λ s′ → sessions ss >>= λ ss′ → just (s′ ∷ ss′)

-- Parse exactly the event type named by a manifest entry.
localEvent : (s : Session) → String → Maybe (LocalEvent s)
localEvent (fetch _) = F.parseEvent
localEvent (notify _) = N.parseEvent
localEvent (blockfetch _) = B.parseEvent
localEvent (chainsync _) = C.parseEvent
localEvent (txsubmission2 _) = T.parseEvent

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

-- Parse one role-selected session into the same one-component product.
parseSingle : (protocol : Role → Session) → String →
  (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseSingle protocol txt with lines txt
... | [] = inj₁ (1 , "")
... | h ∷ ls with F.parseRole h
...   | nothing = inj₁ (1 , h)
...   | just r = map₂ ((protocol r ∷ []) ,_) (go r 2 ls)
  where
  -- Preserve line numbers while tagging each local event with session zero.
  go : (r : Role) → ℕ → List String → (ℕ × String) ⊎ List (Events (protocol r ∷ []))
  go r i [] = inj₂ []
  go r i (l ∷ ls) with localEvent (protocol r) l
  ... | nothing = inj₁ (i , l)
  ... | just e = map₂ (inj₁ e ∷_) (go r (suc i) ls)

-- Preserve the standalone Notify role-header convention.
parseNotify : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseNotify = parseSingle notify

-- Both BlockFetch roles use one parser and select distinct component models.
parseBlockFetch : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseBlockFetch = parseSingle blockfetch

-- Both ChainSync roles share the same strict wire-control parser.
parseChainSync : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseChainSync = parseSingle chainsync

-- Select the submitter/client or requester/server from the role header.
parseTxSubmission2 : String → (ℕ × String) ⊎ Σ (List Session) (λ ss → List (Events ss))
parseTxSubmission2 = parseSingle txsubmission2

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
showLocal (blockfetch _) = B.showEvent
showLocal (chainsync _) = C.showEvent
showLocal (txsubmission2 _) = T.showEvent

-- Print the event at its selected component.
showEvent : ∀ {ss} → Events ss → String
showEvent {s ∷ ss} (inj₁ e) = showLocal s e
showEvent {s ∷ ss} (inj₂ e) = showEvent e

-- Explain a component's current agency and pending work.
showState : (s : Session) → LocalState s → String
showState (fetch _) = F.showSt
showState (notify r) = showNotifyState r
showState (blockfetch client) st = "blockfetch client " ++ B.showState st
showState (blockfetch server) st = "blockfetch server " ++ BS.showState st

showState (chainsync r) st = "chainsync " ++ roleName r ++ " " ++ C.showState st

showState (txsubmission2 r) st = "txsubmission2 " ++ roleName r ++ " " ++ T.showState st

-- Select only the failing event's component for diagnostics.
componentState : ∀ {ss} → States ss → Events ss → String
componentState {s ∷ ss} (st , rest) (inj₁ e) = showState s st
componentState {s ∷ ss} (st , rest) (inj₂ e) = componentState rest e
