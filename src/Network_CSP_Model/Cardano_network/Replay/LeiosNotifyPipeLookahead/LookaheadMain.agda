{-# OPTIONS --guardedness #-}

-- Standalone lookahead dispatch preserves legacy Main modes and requires an explicit fresh-state assertion.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadMain where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Integer using (+_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; Main; run; putStrLn; readFiniteFile; _>>=_; _>>_)
open import System.Environment using (getArgs)
open import System.Exit using (exitWith; ExitCode; ExitSuccess; ExitFailure)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Report
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeClientReport as NodeClient
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverReport as FullNode

-- Accepted prefixes, exhaustive protocol rejection, invalid input and undetermined have distinct exit codes.
emit : Report.Result → IO {0ℓ} (⊤ {0ℓ})
emit report = putStrLn (Report.render report) >> exitWith
  (caseCode (Report.status report))
  where
  -- The process-status class is derived from the structured report, never parsed from diagnostic prose.
  caseCode : Report.Status → ExitCode
  caseCode Report.acceptedPrefix = ExitSuccess
  caseCode Report.protocolRejected = ExitFailure (+ 1)
  caseCode Report.invalidInput = ExitFailure (+ 2)
  caseCode Report.undetermined = ExitFailure (+ 3)

-- Unsupported contracts and forms are explicit input failures.
usage : IO {0ℓ} (⊤ {0ℓ})
usage = emit (Report.result Report.invalidInput
  "usage: LookaheadMain --notify-lookahead FILE --role client|server --next-contract generic-next|node-next --observation driver-log --assume-fresh | LookaheadMain --paired-notify-lookahead PAIR --next-contract generic-next|node-next --observation driver-log --assume-fresh | LookaheadMain --notify-lookahead FILE --role client --client-policy node-client-control --observation driver-log --assume-fresh | LookaheadMain --paired-notify-lookahead PAIR --node-policy full-node --observation driver-log --assume-fresh")

-- Local mode validates both the explicit expected role and normalized file header.
localFile : String → Log.Role → String → IO {0ℓ} (⊤ {0ℓ})
localFile path role contract with Report.parseContract contract
... | nothing = usage
... | just selected = readFiniteFile path >>= λ text → emit (Report.local selected role text)

-- Paired input supplies source coordinates and two independently ordered endpoint lists.
pairedFile : String → String → IO {0ℓ} (⊤ {0ℓ})
pairedFile path contract with Report.parseContract contract
... | nothing = usage
... | just selected = readFiniteFile path >>= λ text → emit (Report.paired selected text)

-- Silenced local mode: RequestNext/Votes were erased by the logger; present ones are invalid input.
localSilencedFile : String → Log.Role → String → IO {0ℓ} (⊤ {0ℓ})
localSilencedFile path role contract with Report.parseContract contract
... | nothing = usage
... | just selected = readFiniteFile path >>= λ text → emit (Report.localSilenced selected role text)

-- Silenced paired mode may report undetermined when only the canonical reconstruction fails.
pairedSilencedFile : String → String → IO {0ℓ} (⊤ {0ℓ})
pairedSilencedFile path contract with Report.parseContract contract
... | nothing = usage
... | just selected = readFiniteFile path >>= λ text → emit (Report.pairedSilenced selected text)

-- The fixed-depth control policy is selected explicitly rather than inferred from a server contract.
nodeClientFile : String → IO {0ℓ} (⊤ {0ℓ})
nodeClientFile path = readFiniteFile path >>= λ text → emit (NodeClient.local text)

-- Full paired policy includes the exact client controls, application queue and fault branch.
fullNodeFile : String → IO {0ℓ} (⊤ {0ℓ})
fullNodeFile path = readFiniteFile path >>= λ text → emit (FullNode.paired text)

-- Only completed driver-log (full or silenced) profiles are dispatched; no depth or node-policy fallback is inferred.
dispatch : List String → IO {0ℓ} (⊤ {0ℓ})
dispatch ("--notify-lookahead" ∷ path ∷ "--role" ∷ "client" ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = localFile path Log.client contract
dispatch ("--notify-lookahead" ∷ path ∷ "--role" ∷ "server" ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = localFile path Log.server contract
dispatch ("--paired-notify-lookahead" ∷ path ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = pairedFile path contract
dispatch ("--notify-lookahead" ∷ path ∷ "--role" ∷ "client" ∷ "--client-policy" ∷ "node-client-control" ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = nodeClientFile path
dispatch ("--paired-notify-lookahead" ∷ path ∷ "--node-policy" ∷ "full-node" ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = fullNodeFile path
dispatch ("--notify-lookahead" ∷ path ∷ "--role" ∷ "client" ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log-no-request-votes" ∷ "--assume-fresh" ∷ []) = localSilencedFile path Log.client contract
dispatch ("--notify-lookahead" ∷ path ∷ "--role" ∷ "server" ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log-no-request-votes" ∷ "--assume-fresh" ∷ []) = localSilencedFile path Log.server contract
dispatch ("--paired-notify-lookahead" ∷ path ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log-no-request-votes" ∷ "--assume-fresh" ∷ []) = pairedSilencedFile path contract
dispatch _ = usage

-- The only new non-safe module is the ordinary stdlib IO/environment/exit boundary.
main : Main
main = run (getArgs >>= dispatch)
