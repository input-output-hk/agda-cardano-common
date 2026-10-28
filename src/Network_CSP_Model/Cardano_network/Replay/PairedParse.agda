{-# OPTIONS --safe #-}

-- Explicit fresh-session pairing; input rows retain endpoint and source line.
open import Data.String.Base using (String)
open import Data.Maybe.Base using (Maybe)
module Cardano_network.Replay.PairedParse
  (E : Set) (protocol : String) (parseEvent : String → Maybe E) where

open import Data.Nat using (ℕ; suc; _<ᵇ_)
open import Data.Nat.Show using (readMaybe)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; lines; words; intersperse)
open import Data.String.Properties using (_≟_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)

-- Evidence is supplied by the caller; identifiers do not authenticate a log.
record Endpoint : Set where
  constructor endpoint
  field
    node connection generation source : String
open Endpoint public

-- Original source-file line numbers accompany normalized wire events.
Row : Set
Row = ℕ × E

-- Explicit correspondence of two local sessions to one shared pair identity.
record Input : Set where
  constructor input
  field
    connectionKey sessionKey : String
    clientInfo serverInfo : Endpoint
    clientRows serverRows : List Row
open Input public

-- Input errors include manifest evidence and the numbered paired-file row.
Error : Set
Error = ℕ × String

-- A role-fixed endpoint declaration must attest a fresh session capture.
parseEndpoint : String → String → Maybe Endpoint
parseEndpoint "client" text with words text
... | "client" ∷ n ∷ c ∷ g ∷ "fresh" ∷ f ∷ [] = just (endpoint n c g f)
... | _ = nothing
parseEndpoint "server" text with words text
... | "server" ∷ n ∷ c ∷ g ∷ "fresh" ∷ f ∷ [] = just (endpoint n c g f)
... | _ = nothing
parseEndpoint _ _ = nothing

-- Parse one endpoint's row, requiring strictly increasing positive source lines.
parseRow : ℕ → List String → Maybe Row
parseRow previous (position ∷ eventWords) with readMaybe 10 position
... | nothing = nothing
... | just n with previous <ᵇ n
...   | false = nothing
...   | true with parseEvent (intersperse " " eventWords)
...     | just e = just (n , e)
...     | nothing = nothing
parseRow _ [] = nothing

-- Separate the endpoint orders; cross-endpoint file order is not imposed.
parseRows : ℕ → ℕ → ℕ → List String → Error ⊎ (List Row × List Row)
parseRows _ _ _ [] = inj₂ ([] , [])
parseRows line pc ps (text ∷ rest) with words text
... | "client" ∷ ws with parseRow pc ws
...   | nothing = inj₁ (line , "expected client <increasing-source-line> <protocol-event>")
...   | just row@(n , e) with parseRows (suc line) n ps rest
...     | inj₁ err = inj₁ err
...     | inj₂ (cs , ss) = inj₂ (row ∷ cs , ss)
parseRows line pc ps (text ∷ rest) | "server" ∷ ws with parseRow ps ws
... | nothing = inj₁ (line , "expected server <increasing-source-line> <protocol-event>")
... | just row@(n , e) with parseRows (suc line) pc n rest
...   | inj₁ err = inj₁ err
...   | inj₂ (cs , ss) = inj₂ (cs , row ∷ ss)
parseRows line pc ps (text ∷ rest) | _ = inj₁ (line , "expected endpoint-tagged protocol row")

-- Validate distinct endpoint identities and retain the caller's local mapping.
parseEndpoints : String → String → String → String → List String → Error ⊎ Input
parseEndpoints conn session ctext stext rest with parseEndpoint "client" ctext
... | nothing = inj₁ (2 , "expected client <node> <local-connection> <generation> fresh <source>")
... | just ci with parseEndpoint "server" stext
...   | nothing = inj₁ (3 , "expected server <node> <local-connection> <generation> fresh <source>")
...   | just si with node ci ≟ node si
...     | yes _ = inj₁ (3 , "client and server node identities must differ")
...     | no _ with parseRows 4 0 0 rest
...       | inj₁ err = inj₁ err
...       | inj₂ (cs , ss) = inj₂ (input conn session ci si cs ss)

-- One file declares one connection/session pair and the two ordered inputs.
parseFile : String → Error ⊎ Input
parseFile text with lines text
... | h ∷ ch ∷ sh ∷ rest with words h
...   | "pair" ∷ name ∷ conn ∷ session ∷ [] with name ≟ protocol
...     | yes _ = parseEndpoints conn session ch sh rest
...     | no _ = inj₁ (1 , "unexpected paired protocol")
parseFile text | h ∷ ch ∷ sh ∷ rest | _ = inj₁ (1 , "expected pair <protocol> <connection-key> <session-key>")
parseFile text | _ = inj₁ (1 , "pair header and two fresh endpoint declarations are required")
