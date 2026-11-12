{-# OPTIONS --safe #-}

-- Parsing and printing of normalized LeiosFetch session files
-- (trace-replay Phase 6). Pure; the IO driver is Cardano_network.Replay.Main.
--
-- Normalized session file (written by src/Cardano_network/Replay/LogProcessing/normalize_logs.py --fetch-only):
--   line 1      : `role client` or `role server`
--   lines 2 ... : one event per line, fields separated by single spaces
--     <Dir> BlockRequest    <hash> <slot>
--     <Dir> Block           <hash> <bytes>
--     <Dir> BlockTxsRequest <hash> <slot> <numTxs> <bitmaps>
--     <Dir> BlockTxs        <numTxs> <txsBytesSize>
--     <Dir> Done
--   <Dir>     = Send | Recv (from the logging node's viewpoint)
--   <hash>    = ebHash, lowercase hex without `0x` (parsed to ℕ, as in Phase 3)
--   <slot>, <bytes>, <numTxs> = decimal
--   <bitmaps> = `-` (none) or `idx:word,idx:word,...`, idx decimal, word
--               lowercase hex without `0x`
-- No blank lines, no comments. Line numbers are 1-based and count the header.
module Cardano_network.Replay.LeiosFetchParse where

import Cardano_network.Replay.Namespaces as Namespaces

import Data.Char.Base as Char
open import Data.List using (List; []; _∷_; map)
open import Data.List.Effectful using (module TraversableA)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
import Data.Maybe.Effectful as MaybeEff
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using (readMaybe; showInBase) renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_; lines; words; wordsByᵇ; padLeft;
                               intersperse)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Function.Strict using (force′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Cardano_network.Replay.LeiosFetchSession

------------------------------------------------------------------------
-- Parsing

open import Cardano_network.Replay.Common using (Role; client; server) public

-- Evaluate a parsed numeral before exposing `just`. The stdlib parser returns
-- `just` around an unevaluated fold that retains the digit list, and replay
-- never inspects payload values, so without this every row's digits stay live.
strict : Maybe ℕ → Maybe ℕ
strict nothing  = nothing
strict (just n) = force′ n just

-- A decimal numeral.
dec : String → Maybe ℕ
dec s = strict (readMaybe 10 s)

-- A lowercase hexadecimal numeral (no `0x`).
hex : String → Maybe ℕ
hex s = strict (readMaybe 16 s)

-- Split a string at a separator character (empty pieces dropped).
splitOn : Char.Char → String → List String
splitOn c = wordsByᵇ (c Char.≈ᵇ_)

-- One bitmap entry `idx:word`.
bitmap : String → Maybe (ℕ × ℕ)
bitmap s with splitOn ':' s
... | i ∷ w ∷ [] = dec i >>= λ i′ → hex w >>= λ w′ → just (i′ , w′)
... | _          = nothing

-- A bitmap list: `-` for none, else comma-separated entries.
bitmaps : String → Maybe (List (ℕ × ℕ))
bitmaps "-" = just []
bitmaps s   = TraversableA.mapA MaybeEff.applicative bitmap (splitOn ',' s)

-- A direction keyword.
direction : String → Maybe Direction
direction "Send" = just Send
direction "Recv" = just Recv
direction _      = nothing

-- A message from the words after the direction.
msg : List String → Maybe Msg
msg ("BlockRequest" ∷ h ∷ s ∷ []) =
  hex h >>= λ h′ → dec s >>= λ s′ → just (MsgLeiosBlockRequest h′ s′)
msg ("Block" ∷ h ∷ z ∷ []) =
  hex h >>= λ h′ → dec z >>= λ z′ → just (MsgLeiosBlock h′ z′)
msg ("BlockTxsRequest" ∷ h ∷ s ∷ n ∷ b ∷ []) =
  hex h >>= λ h′ → dec s >>= λ s′ → dec n >>= λ n′ → bitmaps b >>= λ b′ →
  just (MsgLeiosBlockTxsRequest h′ s′ n′ b′)
msg ("BlockTxs" ∷ n ∷ z ∷ []) =
  dec n >>= λ n′ → dec z >>= λ z′ → just (MsgLeiosBlockTxs n′ z′)
msg ("Done" ∷ []) = just MsgLeiosDone
msg _ = nothing

-- One event line.
parseEvent : String → Maybe E
parseEvent l with Namespaces.fetch (words l)
... | d ∷ ws = direction d >>= λ d′ → msg ws >>= λ m → just (d′ , m)
... | []     = nothing

-- The header line.
parseRole : String → Maybe Role
parseRole l with words l
... | "role" ∷ "client" ∷ [] = just client
... | "role" ∷ "server" ∷ [] = just server
... | _                      = nothing

-- Event lines numbered from n: the first unparsable line (number, text),
-- or all events.
parseEvents : ℕ → List String → (ℕ × String) ⊎ List E
parseEvents _ []       = inj₂ []
parseEvents n (l ∷ ls) with parseEvent l
... | just e  = map₂ (e ∷_) (parseEvents (suc n) ls)
... | nothing = inj₁ (n , l)

-- A whole session file: the first unparsable line, or the role and events.
parseFile : String → (ℕ × String) ⊎ (Role × List E)
parseFile s with lines s
... | []     = inj₁ (1 , "")
... | h ∷ ls with parseRole h
...   | just r  = map₂ (r ,_) (parseEvents 2 ls)
...   | nothing = inj₁ (1 , h)

------------------------------------------------------------------------
-- Printing (inverse of parsing on canonical lines)

-- A hexadecimal numeral left-padded with zeros to n digits.
hexPad : ℕ → ℕ → String
hexPad n x = padLeft '0' n (showInBase 16 x)

-- A bitmap list in the file syntax (words padded to 16 hex digits).
showBitmaps : List (ℕ × ℕ) → String
showBitmaps [] = "-"
showBitmaps bs = intersperse "," (map (λ (i , w) → showℕ i ++ ":" ++ hexPad 16 w) bs)

-- A direction keyword.
showDir : Direction → String
showDir Send = "Send"
showDir Recv = "Recv"

-- A message in the file syntax (hashes padded to 64 hex digits).
showMsg : Msg → String
showMsg (MsgLeiosBlockRequest h s) =
  "BlockRequest " ++ hexPad 64 h ++ " " ++ showℕ s
showMsg (MsgLeiosBlock h z) =
  "Block " ++ hexPad 64 h ++ " " ++ showℕ z
showMsg (MsgLeiosBlockTxsRequest h s n b) =
  "BlockTxsRequest " ++ hexPad 64 h ++ " " ++ showℕ s ++ " " ++ showℕ n ++
  " " ++ showBitmaps b
showMsg (MsgLeiosBlockTxs n z) =
  "BlockTxs " ++ showℕ n ++ " " ++ showℕ z
showMsg MsgLeiosDone = "Done"

-- An event in the file syntax.
showEvent : E → String
showEvent (d , m) = showDir d ++ " " ++ showMsg m

-- An outstanding request.
showReq : Req → String
showReq (blockReq h s)    = "BlockRequest " ++ hexPad 64 h ++ " " ++ showℕ s
showReq (blockTxsReq h s n) = "BlockTxsRequest " ++ hexPad 64 h ++ " " ++ showℕ s ++ " " ++ showℕ n

-- A session state, phrased as what the model accepts next.
showSt : St → String
showSt (cOpen []) =
  "client open, nothing outstanding (accepts: Send BlockRequest/BlockTxsRequest/Done)"
showSt (cOpen q@(_ ∷ _)) =
  "client open, outstanding oldest first [" ++ intersperse "; " (map showReq q) ++
  "] (accepts: a response to the FIRST of these, or a new request if fewer than k are outstanding)"
showSt (cDrain q) =
  "client draining, outstanding oldest first [" ++ intersperse "; " (map showReq q) ++
  "] (accepts: replies by kind, then Send Done; no new requests)"
showSt cClosed = "client closed after Send Done (accepts nothing)"
showSt sIdle = "server idle (accepts: Recv BlockRequest/BlockTxsRequest/Done)"
showSt (sBusy r) =
  "server holding " ++ showReq r ++ " (accepts: the matching Send response only)"
showSt (sReady r) =
  "server ready to answer " ++ showReq r ++ " (accepts: the matching Send response only)"
showSt sThrown = "server thrown (accepts nothing)"
showSt sClosed = "server closed after Recv Done (accepts nothing)"

------------------------------------------------------------------------
-- Typecheck-time checks

-- A header and a pipelined request parse.
_ : parseFile "role client\nSend BlockRequest 2a 7\nSend BlockTxsRequest ff 7 3 0:1,1:a\n"
    ≡ inj₂ (client , (Send , MsgLeiosBlockRequest 42 7)
                   ∷ (Send , MsgLeiosBlockTxsRequest 255 7 3 ((0 , 1) ∷ (1 , 10) ∷ []))
                   ∷ [])
_ = refl

-- A bad line is reported with its 1-based line number.
_ : parseFile "role server\nRecv Done\nRecv Block 2a\n" ≡ inj₁ (3 , "Recv Block 2a")
_ = refl

-- A bad header is reported at line 1.
_ : parseFile "role peer\nRecv Done\n" ≡ inj₁ (1 , "role peer")
_ = refl

-- Printing a canonical line and parsing it back is the identity.
_ : parseEvent (showEvent (Recv , MsgLeiosBlockTxs 190 52440))
    ≡ just (Recv , MsgLeiosBlockTxs 190 52440)
_ = refl

-- The obsolete hash/slot/bitmap reply grammar is rejected.
_ : parseEvent "Recv BlockTxs ab 3 2 80 -" ≡ nothing
_ = refl
