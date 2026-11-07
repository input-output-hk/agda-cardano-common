{-# OPTIONS --guardedness #-}

-- Reports consume total normalized adapters; raw capture assumptions remain external declarations.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_,_; proj₂)
open import Data.String using (String; _++_; lines)
open import Data.Sum using (inj₁; inj₂)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyParse as Parse
open import Cardano_network.Replay.LeiosFetchParse using (parseRole)
import Cardano_network.Replay.PairedParse as PairedParse
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as Paired
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.SilencedAdapter as Silenced
open Silenced public using (showRole; serverReason; clientReason)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as Source
module PairFile = PairedParse Log.E "LeiosNotifyP" Parse.parseEvent

-- Protocol rejection and malformed input have separate stable machine statuses.
-- `undetermined` is inconclusive: a canonical reconstruction failed, which refutes nothing.
data Status : Set where
  acceptedPrefix protocolRejected invalidInput undetermined : Status

-- The report carries its exit-status class independently of the diagnostic text.
record Result : Set where
  constructor result
  field
    status : Status
    detail : String
open Result public

-- Stable first-line status tags let an external runner preserve inconclusive failures separately.
showStatus : Status → String
showStatus acceptedPrefix = "accepted-prefix"
showStatus protocolRejected = "protocol-rejected"
showStatus invalidInput = "invalid-input"
showStatus undetermined = "undetermined"

-- Render one model verdict; this does not attest the deployed binary or capture completeness.
render : Result → String
render report = showStatus (status report) ++ "\n" ++ detail report

-- Server callback contracts are explicit; the local client does not use this parameter.
parseContract : String → Maybe Source.Contract
parseContract "generic-next" = just Source.genericNext
parseContract "node-next" = just Source.nodeNext
parseContract _ = nothing

-- The displayed contract names match the exact supported command-line profiles.
showContract : Source.Contract → String
showContract Source.genericNext = "generic-next"
showContract Source.nodeNext = "node-next"

-- A declared local role must agree with the file header before model checking starts.
sameRole : Log.Role → Log.Role → Bool
sameRole Log.client Log.client = true
sameRole Log.server Log.server = true
sameRole _ _ = false

-- Every output names the conditional model profile and its finite-prefix scope.
profile : Source.Contract → String
profile contract = "observation=driver-log; client=generic-successful; return=unit; server-contract=" ++
  showContract contract ++ "\ninitial=fresh (asserted); eof=prefix; fields=normalized summaries"

-- Local adaptation preserves all lines, including failed parse outcomes, after the role header.
localRows : Source.Contract → Log.Role → List (Maybe Log.E) → Result
localRows contract Log.client input with Client.check Log.client input
... | Client.invalidInput failure _ = result invalidInput
  (profile contract ++ "\ninput line " ++ showℕ (suc (suc (Client.position failure))) ++ ": " ++ clientReason (Client.reason failure))
... | Client.protocolRejected _ _ _ _ = result protocolRejected
  (profile contract ++ "\nno compatible local client prefix (" ++ showℕ (length input) ++ " events); server contract unused by local client")
... | Client.accepted _ = result acceptedPrefix
  (profile contract ++ "\nlocal client prefix (" ++ showℕ (length input) ++ " events); server contract unused by local client")
localRows contract Log.server input with Server.check contract Log.server input
... | Server.invalidInput failure _ = result invalidInput
  (profile contract ++ "\ninput line " ++ showℕ (suc (suc (Server.position failure))) ++ ": " ++ serverReason (Server.reason failure))
... | Server.protocolRejected _ _ _ _ = result protocolRejected
  (profile contract ++ "\nno compatible local server prefix (" ++ showℕ (length input) ++ " events)")
... | Server.accepted _ = result acceptedPrefix
  (profile contract ++ "\nlocal server prefix (" ++ showℕ (length input) ++ " events)")

-- The header is validated separately so a role error refers to line one rather than an event index.
withHeader : Log.Role → String → (List (Maybe Log.E) → Result) → Result
withHeader expected text check with lines text
... | [] = result invalidInput "input line 1: missing role header"
... | header ∷ rest with parseRole header
...   | nothing = result invalidInput "input line 1: expected role client or role server"
...   | just actual with sameRole expected actual
...     | false = result invalidInput ("input line 1: role differs from declared " ++ showRole expected)
...     | true = check (map Parse.parseEvent rest)

-- Full driver-log local mode: the role header, then the exact local adapters.
local : Source.Contract → Log.Role → String → Result
local contract expected text = withHeader expected text (localRows contract expected)

-- Successful paired parsing already retains positive increasing original source line coordinates.
sourceAt : ℕ → List PairFile.Row → String
sourceAt zero ((line , _) ∷ _) = showℕ line
sourceAt (suc index) (_ ∷ rows) = sourceAt index rows
sourceAt _ [] = "unavailable"

-- Located paired validation errors retain the declared endpoint source and its original row coordinate.
pairFailure : PairFile.Input → Paired.Failure → String
pairFailure capture (Paired.at Paired.clientInput position reason) =
  "client source " ++ PairFile.source (PairFile.clientInfo capture) ++ " line " ++
  sourceAt position (PairFile.clientRows capture) ++ ": " ++ serverReason reason
pairFailure capture (Paired.at Paired.serverInput position reason) =
  "server source " ++ PairFile.source (PairFile.serverInfo capture) ++ " line " ++
  sourceAt position (PairFile.serverRows capture) ++ ": " ++ serverReason reason

-- Pair identities are declarations from the capture, not authenticated network or NAT mappings.
pairContext : PairFile.Input → String
pairContext capture = "connection=" ++ PairFile.connectionKey capture ++ "; session=" ++ PairFile.sessionKey capture

-- Exact normalized pair checking searches every merge; a whole-prefix rejection claims no minimal failure index.
pairedInput : Source.Contract → PairFile.Input → Result
pairedInput contract capture with Paired.check-normalized contract Log.client
  (map proj₂ (PairFile.clientRows capture)) Log.server
  (map proj₂ (PairFile.serverRows capture))
... | Paired.invalidInput failure _ = result invalidInput
  (profile contract ++ "\n" ++ pairContext capture ++ "\n" ++ pairFailure capture failure)
... | Paired.protocolRejected _ _ _ _ _ = result protocolRejected
  (profile contract ++ "\n" ++ pairContext capture ++ "\nno compatible paired execution for the supplied endpoint prefixes")
... | Paired.accepted _ = result acceptedPrefix
  (profile contract ++ "\n" ++ pairContext capture ++ "\npaired prefixes (client " ++
    showℕ (length (PairFile.clientRows capture)) ++ ", server " ++ showℕ (length (PairFile.serverRows capture)) ++ " events)")

-- Existing paired syntax validates normalized fields and preserves per-endpoint order before adaptation.
paired : Source.Contract → String → Result
paired contract text with PairFile.parseFile text
... | inj₁ (line , message) = result invalidInput ("paired input line " ++ showℕ line ++ ": " ++ message)
... | inj₂ capture = pairedInput contract capture

-- The silenced profile states which kinds the logger erased; acceptance is about that observation only.
silencedProfile : Source.Contract → String
silencedProfile contract = "observation=driver-log-no-request-votes; hidden=RequestNext,Votes; client=generic-successful; return=unit; server-contract=" ++
  showContract contract ++ "\ninitial=fresh (asserted); eof=prefix; fields=normalized summaries"

-- Local silenced verdicts; a present hidden-kind row is invalid input at its normalized line.
localSilencedRows : Source.Contract → Log.Role → List (Maybe Log.E) → Result
localSilencedRows contract Log.client input with Silenced.client input
... | Silenced.invalid position reason = result invalidInput
  (silencedProfile contract ++ "\ninput line " ++ showℕ (suc (suc position)) ++ ": " ++ reason)
... | Silenced.rejected _ _ _ = result protocolRejected
  (silencedProfile contract ++ "\nno compatible silenced local client prefix (" ++ showℕ (length input) ++ " events); server contract unused by local client")
... | Silenced.accepted _ _ _ = result acceptedPrefix
  (silencedProfile contract ++ "\nsilenced local client prefix (" ++ showℕ (length input) ++ " events); server contract unused by local client")
localSilencedRows contract Log.server input with Silenced.server contract input
... | Silenced.invalid position reason = result invalidInput
  (silencedProfile contract ++ "\ninput line " ++ showℕ (suc (suc position)) ++ ": " ++ reason)
... | Silenced.rejected _ _ _ = result protocolRejected
  (silencedProfile contract ++ "\nno compatible silenced local server prefix (" ++ showℕ (length input) ++ " events)")
... | Silenced.accepted _ _ _ = result acceptedPrefix
  (silencedProfile contract ++ "\nsilenced local server prefix (" ++ showℕ (length input) ++ " events)")

-- Local silenced mode with the same role-header validation as the full driver-log mode.
localSilenced : Source.Contract → Log.Role → String → Result
localSilenced contract expected text = withHeader expected text (localSilencedRows contract expected)

-- The paired silenced verdict for the translated rows of both inputs.
pairedSilencedRows : (contract : Source.Contract) → PairFile.Input → ∀ {c s} → Silenced.PS.Outcome contract c s → Result
pairedSilencedRows contract capture (Silenced.PS.accepted _) = result acceptedPrefix
  (silencedProfile contract ++ "\n" ++ pairContext capture ++ "\nsilenced paired prefixes (client " ++
    showℕ (length (PairFile.clientRows capture)) ++ ", server " ++ showℕ (length (PairFile.serverRows capture)) ++ " events)")
pairedSilencedRows contract capture (Silenced.PS.rejected _) = result protocolRejected
  (silencedProfile contract ++ "\n" ++ pairContext capture ++ "\na local silenced endpoint check refutes every paired execution")
pairedSilencedRows contract capture (Silenced.PS.undetermined _ _ _) = result undetermined
  (silencedProfile contract ++ "\n" ++ pairContext capture ++ "\nboth local silenced checks pass; the canonical hidden-request reconstruction is refuted; no protocol verdict")

-- The input-level paired silenced adapter: hidden-kind rows are invalid input with the local
-- precedence (client first), and every verdict is about the unique translations of both inputs.
pairedSilencedInput : Source.Contract → PairFile.Input → Result
pairedSilencedInput contract capture
  with Silenced.paired contract (Paired.present (map proj₂ (PairFile.clientRows capture)))
         (Paired.present (map proj₂ (PairFile.serverRows capture)))
... | Silenced.invalidClient position reason = result invalidInput
  (silencedProfile contract ++ "\n" ++ pairContext capture ++ "\nclient source " ++ PairFile.source (PairFile.clientInfo capture) ++
    " line " ++ sourceAt position (PairFile.clientRows capture) ++ ": " ++ reason)
... | Silenced.invalidServer position reason = result invalidInput
  (silencedProfile contract ++ "\n" ++ pairContext capture ++ "\nserver source " ++ PairFile.source (PairFile.serverInfo capture) ++
    " line " ++ sourceAt position (PairFile.serverRows capture) ++ ": " ++ reason)
... | Silenced.checked _ _ _ _ outcome = pairedSilencedRows contract capture outcome

-- Paired silenced mode reuses the existing paired file syntax and source coordinates.
pairedSilenced : Source.Contract → String → Result
pairedSilenced contract text with PairFile.parseFile text
... | inj₁ (line , message) = result invalidInput ("paired input line " ++ showℕ line ++ ": " ++ message)
... | inj₂ capture = pairedSilencedInput contract capture
