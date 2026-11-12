{-# OPTIONS --guardedness #-}

-- Standalone lookahead dispatch preserves legacy Main modes and requires an explicit fresh-state assertion.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadMain where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String; _++_)
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

-- Complete standalone reference shared by explicit help and invalid-argument reports.
usageText : String
usageText =
  "usage: LookaheadMain MODE FILE OPTIONS\n" ++
  "Check implementation-lookahead LeiosNotify normalized traces, not raw JSON.\n" ++
  "Options are positional: use exactly the order below. ROLE = client or server;\n" ++
  "CONTRACT = generic-next or node-next; OBS = one of the observations below.\n" ++
  "\n" ++
  "Generic successful client callbacks, local or paired:\n" ++
  "  LookaheadMain --notify-lookahead FILE --role ROLE\n" ++
  "    --next-contract CONTRACT --observation OBS --assume-fresh\n" ++
  "  LookaheadMain --paired-notify-lookahead PAIR\n" ++
  "    --next-contract CONTRACT --observation OBS --assume-fresh\n" ++
  "  Wrapped command lines above must be joined into one shell command.\n" ++
  "\n" ++
  "Explicit node-policy modes (full observation only):\n" ++
  "  LookaheadMain --notify-lookahead FILE --role client\n" ++
  "    --client-policy node-client-control --observation driver-log --assume-fresh\n" ++
  "  LookaheadMain --paired-notify-lookahead PAIR\n" ++
  "    --node-policy full-node --observation driver-log --assume-fresh\n" ++
  "\n" ++
  "Contracts and policies:\n" ++
  "  generic-next: server callback may select Canceled at any time.\n" ++
  "  node-next: server callback uses normal-only selection.\n" ++
  "  Both generic forms use generic successful client callbacks. node-next alone\n" ++
  "  does NOT select the node client policy. A local client ignores the contract.\n" ++
  "  node-client-control: fixed depth-1000 client control policy.\n" ++
  "  full-node: paired node policy with client controls and application credit/FIFO\n" ++
  "  queue. These policies retain existential external inputs; they do not certify\n" ++
  "  actual forecast/governor truth or deployed implementation conformance.\n" ++
  "\n" ++
  "Observations (no default; choose from the actual tracer configuration):\n" ++
  "  driver-log: RequestNext and Votes are logged, as well as other Notify messages.\n" ++
  "  driver-log-no-request-votes: both kinds were silenced by the logger.\n" ++
  "  Silenced mode supports generic forms only. Present RequestNext/Votes rows are\n" ++
  "  invalid input; do not erase logged rows to obtain acceptance.\n" ++
  "  No user depth option is supported. Use Main --notify for bounded prototype\n" ++
  "  Notify replay; that is a different model.\n" ++
  "\n" ++
  "Inputs:\n" ++
  "  Local FILE: 'role client' or 'role server', then Send/Recv message rows, e.g.\n" ++
  "    role client\n" ++
  "    Send RequestNext\n" ++
  "    Recv Votes -\n" ++
  "  Exact LeiosNotify.Remote.Send/Receive namespaces are also accepted.\n" ++
  "  PAIR: paired_sessions.py output with two declared fresh endpoints and original\n" ++
  "  source coordinates, not concatenated raw logs. Preserve each endpoint's order.\n" ++
  "  --assume-fresh asserts the trace starts at the initial protocol state; it does\n" ++
  "  not infer freshness or repair a mid-session capture. EOF is always a prefix.\n" ++
  "  Session identity is node/connection/generation/protocol/role. Both local roles\n" ++
  "  and both endpoint logs count separately. Connection cleanup needs no Quit/Done.\n" ++
  "\n" ++
  "Raw Notify batch (from repository root; OUT must be new):\n" ++
  "  TOOLS=src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools\n" ++
  "  python3 -I -B \"$TOOLS/capture_batch.py\" --raw node.log --checker /tmp/leiosnotify-replay-build/LookaheadMain --out /tmp/notify-results --observation driver-log --timeout 60 --heap 512M\n" ++
  "  Batch writes summary.json, results.jsonl, sessions/ and any matched pairs/.\n" ++
  "  It uses NewMux/Done boundaries and requires host fields. For handshake/cleanup\n" ++
  "  captures use normalize_logs.py --connection-lifecycle and check selected files.\n" ++
  "  Batch pairs literal reversed addresses at different hosts with matching local\n" ++
  "  generation labels; verify those labels denote the same real connection.\n" ++
  "  It runs generic callbacks (servers under both contracts), not node-policy modes.\n" ++
  "\n" ++
  "Normalized example (one shell command):\n" ++
  "  LookaheadMain --notify-lookahead /tmp/client.txt --role client --next-contract generic-next --observation driver-log --assume-fresh\n" ++
  "  Bounded manifest runner (validates capture declarations and artifact hashes):\n" ++
  "  python3 -I -B \"$TOOLS/replay_lookahead.py\" --checker /tmp/leiosnotify-replay-build/LookaheadMain --manifest /work/manifest.json\n" ++
  "  For raw correspondence use replay_raw_lookahead.py with --manifest and\n" ++
  "  --raw-bindings. Profile examples: tools/profiles/ relative to this module.\n" ++
  "\n" ++
  "Verdict tag and exit code must agree:\n" ++
  "  0 accepted-prefix: some model run explains this prefix, not completed delivery.\n" ++
  "  1 protocol-rejected: no run explains it under the selected profile/assumptions.\n" ++
  "  2 invalid-input: malformed input, agency error or unsupported arguments.\n" ++
  "  3 undetermined: silenced paired search has no verdict; not a rejection.\n" ++
  "  Untagged IO failure, timeout or heap exhaustion is inconclusive.\n" ++
  "  Manifest runners use different exits: 0 accepted, 1 rejected, 2 invalid input,\n" ++
  "  3 missing capture declarations, 4 inconclusive (including undetermined).\n" ++
  "\n" ++
  "Help: LookaheadMain --help | LookaheadMain -h (exit 0; no verdict tag).\n" ++
  "No arguments or invalid arguments print invalid-input plus this help (exit 2).\n" ++
  "Build with GHC -rtsopts for runner heap caps (+RTS -M512M -RTS).\n" ++
  "Full examples, builds and pairing: src/Cardano_network/Replay/USAGE.md\n"

-- Unsupported contracts and forms retain the tagged invalid-input exit.
usage : IO {0ℓ} (⊤ {0ℓ})
usage = emit (Report.result Report.invalidInput usageText)

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
dispatch ("--help" ∷ []) = putStrLn usageText
dispatch ("-h" ∷ []) = putStrLn usageText
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
