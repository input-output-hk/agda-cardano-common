{-# OPTIONS --safe #-}

-- Normalized LeiosNotifyP messages, with real logged fields retained.
-- Announcements use '-' or hash/slot/body-size; votes use hash:voter pairs.
module Cardano_network.Replay.LeiosNotifyParse where

import Cardano_network.Replay.Namespaces as Namespaces

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Effectful using (module TraversableA)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Effectful as MaybeEff
open import Data.Product using (_,_)
open import Data.String using (String; words; intersperse; _++_; _≟_)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.LeiosNotifySession
open import Cardano_network.Replay.LeiosFetchParse using (dec; hex; hexPad; splitOn; direction; showDir)

-- One vote's RB hash and voter id, with no signature or weight claim.
vote : String → Maybe (Data.Product._×_ ℕ ℕ)
vote s with splitOn ':' s
... | h ∷ v ∷ [] with s ≟ (h ++ ":" ++ v)
...   | yes _ = hex h >>= λ h′ → dec v >>= λ v′ → just (h′ , v′)
...   | no _ = nothing
vote s | _ = nothing

-- Empty or comma-separated vote metadata, retaining order and duplicates.
parseVotes : String → Maybe (List (Data.Product._×_ ℕ ℕ))
parseVotes "-" = just []
parseVotes s with splitOn ',' s
... | [] = nothing
... | xs@(_ ∷ _) with s ≟ intersperse "," xs
...   | yes _ = TraversableA.mapA MaybeEff.applicative vote xs
...   | no _ = nothing

-- Parse exactly one prototype message form.
msg : List String → Maybe Msg
msg ("RequestNext" ∷ []) = just RequestNext
msg ("Done" ∷ []) = just Done
msg ("BlockAnnouncement" ∷ "-" ∷ []) = just (BlockAnnouncement nothing)
msg ("BlockAnnouncement" ∷ h ∷ s ∷ z ∷ []) =
  hex h >>= λ h′ → dec s >>= λ s′ → dec z >>= λ z′ → just (BlockAnnouncement (just (h′ , s′ , z′)))
msg ("BlockOffer" ∷ h ∷ s ∷ z ∷ []) =
  hex h >>= λ h′ → dec s >>= λ s′ → dec z >>= λ z′ → just (BlockOffer h′ s′ z′)
msg ("BlockTxsOffer" ∷ h ∷ s ∷ []) =
  hex h >>= λ h′ → dec s >>= λ s′ → just (BlockTxsOffer h′ s′)
msg ("Votes" ∷ vs ∷ []) = parseVotes vs >>= λ vs′ → just (Votes vs′)
msg _ = nothing

-- Direction plus a protocol-specific payload; Fetch syntax is not accepted.
parseEvent : String → Maybe E
parseEvent s with Namespaces.notify (words s)
... | d ∷ ws = direction d >>= λ d′ → msg ws >>= λ m → just (d′ , m)
... | [] = nothing

-- Display retained payload fields in canonical normalized syntax.
showMsg : Msg → String
showMsg RequestNext = "RequestNext"
showMsg Done = "Done"
showMsg (BlockAnnouncement nothing) = "BlockAnnouncement -"
showMsg (BlockAnnouncement (just (h , s , z))) = "BlockAnnouncement " ++ hexPad 64 h ++ " " ++ showℕ s ++ " " ++ showℕ z
showMsg (BlockOffer h s z) = "BlockOffer " ++ hexPad 64 h ++ " " ++ showℕ s ++ " " ++ showℕ z
showMsg (BlockTxsOffer h s) = "BlockTxsOffer " ++ hexPad 64 h ++ " " ++ showℕ s
showMsg (Votes []) = "Votes -"
showMsg (Votes vs@(_ ∷ _)) = "Votes " ++ intersperse "," (map (λ (h , v) → hexPad 64 h ++ ":" ++ showℕ v) vs)

-- Display the wire event for rejection diagnostics.
showEvent : E → String
showEvent (d , m) = showDir d ++ " " ++ showMsg m

-- Explain the exact agency of a residual session state.
showSt : Role → St → String
showSt client idle = "notify client idle (accepts: Send RequestNext or Done)"
showSt client busy = "notify client busy (accepts: one Recv notification)"
showSt server idle = "notify server idle (accepts: Recv RequestNext or Done)"
showSt server busy = "notify server busy (accepts: one Send notification)"
showSt _ closed = "notify closed after Done (accepts nothing)"
