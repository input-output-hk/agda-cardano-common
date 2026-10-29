{-# OPTIONS --guardedness #-}

-- Trace replay: Fetch, Notify, BlockFetch, ChainSync and TxSubmission2, standalone or interleaved.
-- Each component uses its certified session decider. The only replay module
-- without --safe (it imports the stdlib IO and System.Environment bindings);
-- no postulates or pragmas of its own.
--
--   Main FILE [K]      K = Fetch client pipelining bound, default 4
--   Main --blockfetch FILE [K_BF]         role-selected; client depth default 100
--   Main --blockfetch-client FILE [K_BF]  control-only, default 100
--   Main --blockfetch-server FILE        sequential server, no depth argument
--   Main --txsubmission2 FILE [K_TS]   server/requester depth default 4
--   Main --paired-notify FILE [K_NOTIFY]  explicit fresh pair, default 1
--   Main --paired-fetch FILE [K_FETCH]    explicit fresh pair, default 4
--   Main --paired-chainsync FILE [K_CS]  explicit fresh pair, default 300
--   Main --paired-blockfetch FILE [K_BF]  fresh pair; client depth default 100
--   Main --paired-txsubmission2 FILE [K_TS]  fresh pair; server depth default 4
--   Main --chainsync FILE [K_CS]      role-selected; client depth default 300
--   Main --notify FILE [K_NOTIFY]   Notify credit bound, default 1
--   Main --interleaved FILE [K_FETCH [K_NOTIFY [K_BF [K_CS [K_TS]]]]]   independent bounds
--
-- Single-session mode prints one of
--   accepted (<n> events)
--   rejected at index <i>: <event>          (i = 1-based event index,
--   model state after <i-1> events: <st>     event i is on file line i+1)
--   parse error at line <l>: <line>
-- Interleaved mode also prints the session count on acceptance, and the
-- session id and its state at a global rejection index.
-- There is no `unknown`: `hasTrace?` is a decision procedure (client-cert /
-- server-cert discharge its τ-accessibility hypothesis).
--
-- Fetch-only mode decides the whole trace first; on `no`, prefixes of length
-- 1, 2, … decided in turn (O(n²)) to find the first rejected event. By prefix
-- closure (`HasTrace-prefix`) every longer prefix is then rejected too. The
-- model state printed is the end state of the `yes` witness for the longest
-- accepted prefix, taken right after its last visible event. Notify and mixed
-- modes use SessionReport's binary prefix search instead.
module Cardano_network.Replay.Main where

open import Data.List using (List; []; _∷_; take; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show using (readMaybe) renaming (show to showℕ)
open import Data.Product using (Σ; _,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; Main; run; putStrLn; readFiniteFile; _>>=_)
open import Relation.Nullary using (yes; no)
open import System.Environment using (getArgs)

open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.LeiosFetchDecide
open import Cardano_network.Replay.LeiosFetchParse
import Cardano_network.Replay.SessionReport as Interleaved
import Cardano_network.Replay.BlockFetchReport as BlockFetch
import Cardano_network.Replay.BlockFetchServerReport as BlockFetchServer
import Cardano_network.Replay.ChainSyncPairedReport as ChainSyncPaired
import Cardano_network.Replay.LeiosNotifyPairedReport as LeiosNotifyPaired
import Cardano_network.Replay.LeiosFetchPairedReport as LeiosFetchPaired
import Cardano_network.Replay.BlockFetchPairedReport as BlockFetchPaired
import Cardano_network.Replay.TxSubmission2PairedReport as TxSubmission2Paired

-- Checking with client pipelining bound k.
module Check (k : ℕ) where
  open Cert k

  -- Initial state and its τ-accessibility certificate, per role.
  start : Role → Σ St τAccReach
  start client = client₀ , client-cert
  start server = server₀ , server-cert

  -- Decide the prefixes of es of length i + 1, i + 2, …; st is the state
  -- reached by the (accepted) prefix of length i, rest the events after it.
  scan : ∀ {s₀} → τAccReach s₀ → List E → ℕ → St → List E → String
  scan h es i st [] = "accepted (" ++ showℕ i ++ " events)"
  scan h es i st (e ∷ rest) with hasTrace? h (take (suc i) es)
  ... | yes (st′ , _) = scan h es (suc i) st′ rest
  ... | no _ = "rejected at index " ++ showℕ (suc i) ++ ": " ++ showEvent e ++
               "\nmodel state after " ++ showℕ i ++ " events: " ++ showSt st

  -- The verdict for a parsed session.
  verdict : Role → List E → String
  verdict r es with start r
  ... | s₀ , h with hasTrace? h es
  ...   | yes _ = "accepted (" ++ showℕ (length es) ++ " events)"
  ...   | no _  = scan h es 0 s₀ es

-- The report for one session file's contents.
report : ℕ → String → String
report k s with parseFile s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (r , es)  = Check.verdict k r es

-- Usage line.
usage : String
usage = "usage: Main FILE [K_FETCH] | Main --paired-notify FILE [K_NOTIFY] | Main --paired-fetch FILE [K_FETCH] | Main --paired-chainsync FILE [K_CS] | Main --paired-blockfetch FILE [K_BF] | Main --paired-txsubmission2 FILE [K_TS] | Main --blockfetch FILE [K_BF] | Main --blockfetch-client FILE [K_BF] | Main --blockfetch-server FILE | Main --txsubmission2 FILE [K_TS] | Main --chainsync FILE [K_CS] | Main --notify FILE [K_NOTIFY] | Main --interleaved FILE [K_FETCH [K_NOTIFY [K_BF [K_CS [K_TS]]]]]   (defaults: Fetch 4, Notify 1, BlockFetch 100, ChainSync 300, TxSubmission2 4)"

-- Read, check and print one file.
checkFile : ℕ → String → IO ⊤
checkFile k path = readFiniteFile path >>= λ s → putStrLn (report k s)

-- Read and decide one globally ordered interleaved-session file.
checkInterleaved : ℕ → ℕ → String → IO ⊤
checkInterleaved k depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportWithDepth k depth s)

-- Read an interleaving with a separately configured BlockFetch client bound.
checkInterleavedWithDepths : ℕ → ℕ → ℕ → String → IO ⊤
checkInterleavedWithDepths k depth bfDepth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportWithDepths k depth bfDepth s)

-- Read a role-selected BlockFetch session through the same product checker.
checkBlockFetchRole : ℕ → String → IO ⊤
checkBlockFetchRole bfDepth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportBlockFetch bfDepth s)

-- Read one bounded Notify session with a role header.
checkNotify : ℕ → String → IO ⊤
checkNotify depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportNotifyWithDepth depth s)

-- Read one pipelined BlockFetch client control trace.
checkBlockFetch : ℕ → String → IO ⊤
checkBlockFetch depth path = readFiniteFile path >>= λ s → putStrLn (BlockFetch.report depth s)

-- Read one sequential BlockFetch server control trace.
checkBlockFetchServer : String → IO ⊤
checkBlockFetchServer path = readFiniteFile path >>= λ s → putStrLn (BlockFetchServer.report s)

-- Check a role-selected ChainSync session; only clients use the bound.
checkChainSync : ℕ → String → IO ⊤
checkChainSync depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportChainSync depth s)

-- Check an interleaving with all four independent protocol bounds.
checkInterleavedWithAllDepths : ℕ → ℕ → ℕ → ℕ → String → IO ⊤
checkInterleavedWithAllDepths k n b c path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportWithAllDepths k n b c s)

-- Check a TxSubmission2 submitter/client or requester/server session.
checkTxSubmission2 : ℕ → String → IO ⊤
checkTxSubmission2 depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportTxSubmission2 depth s)

-- Read all five protocol bounds for heterogeneous replay.
checkInterleavedWithProtocolDepths : ℕ → ℕ → ℕ → ℕ → ℕ → String → IO ⊤
checkInterleavedWithProtocolDepths k n b c t path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportWithProtocolDepths k n b c t s)

-- Decide compatibility of two explicitly paired fresh ChainSync inputs.
checkPairedChainSync : ℕ → String → IO ⊤
checkPairedChainSync depth path = readFiniteFile path >>= λ s → putStrLn (ChainSyncPaired.report depth s)

-- Decide an explicitly declared fresh prototype Notify pair.
checkPairedNotify : ℕ → String → IO ⊤
checkPairedNotify depth path = readFiniteFile path >>= λ s → putStrLn (LeiosNotifyPaired.report depth s)

-- Decide an explicitly declared fresh prototype Fetch pair.
checkPairedFetch : ℕ → String → IO ⊤
checkPairedFetch depth path = readFiniteFile path >>= λ s → putStrLn (LeiosFetchPaired.report depth s)

-- Decide a fresh BlockFetch pair with a bounded client and sequential server.
checkPairedBlockFetch : ℕ → String → IO ⊤
checkPairedBlockFetch depth path = readFiniteFile path >>= λ s → putStrLn (BlockFetchPaired.report depth s)

-- Decide a fresh TxSubmission2 pair; the bound belongs to the requester/server.
checkPairedTxSubmission2 : ℕ → String → IO ⊤
checkPairedTxSubmission2 depth path = readFiniteFile path >>= λ s → putStrLn (TxSubmission2Paired.report depth s)

-- Dispatch on the command-line arguments.
dispatch : List String → IO ⊤
dispatch ("--paired-blockfetch" ∷ f ∷ []) = checkPairedBlockFetch 100 f
dispatch ("--paired-blockfetch" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkPairedBlockFetch depth f
... | nothing = putStrLn usage
dispatch ("--paired-blockfetch" ∷ _) = putStrLn usage
dispatch ("--paired-txsubmission2" ∷ f ∷ []) = checkPairedTxSubmission2 4 f
dispatch ("--paired-txsubmission2" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkPairedTxSubmission2 depth f
... | nothing = putStrLn usage
dispatch ("--paired-txsubmission2" ∷ _) = putStrLn usage
dispatch ("--paired-notify" ∷ f ∷ []) = checkPairedNotify 1 f
dispatch ("--paired-notify" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkPairedNotify depth f
... | nothing = putStrLn usage
dispatch ("--paired-fetch" ∷ f ∷ []) = checkPairedFetch 4 f
dispatch ("--paired-fetch" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkPairedFetch depth f
... | nothing = putStrLn usage
dispatch ("--paired-chainsync" ∷ f ∷ []) = checkPairedChainSync 300 f
dispatch ("--paired-chainsync" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkPairedChainSync depth f
... | nothing = putStrLn usage
dispatch ("--paired-chainsync" ∷ _) = putStrLn usage
dispatch ("--txsubmission2" ∷ f ∷ []) = checkTxSubmission2 4 f
dispatch ("--txsubmission2" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkTxSubmission2 depth f
... | nothing = putStrLn usage
dispatch ("--txsubmission2" ∷ _) = putStrLn usage
dispatch ("--chainsync" ∷ f ∷ []) = checkChainSync 300 f
dispatch ("--chainsync" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkChainSync depth f
... | nothing = putStrLn usage
dispatch ("--chainsync" ∷ _) = putStrLn usage
dispatch ("--blockfetch" ∷ f ∷ []) = checkBlockFetchRole 100 f
dispatch ("--blockfetch" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkBlockFetchRole depth f
... | nothing = putStrLn usage
dispatch ("--blockfetch" ∷ _) = putStrLn usage
dispatch ("--blockfetch-server" ∷ f ∷ []) = checkBlockFetchServer f
dispatch ("--blockfetch-server" ∷ _) = putStrLn usage
dispatch ("--blockfetch-client" ∷ f ∷ []) = checkBlockFetch 100 f
dispatch ("--blockfetch-client" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkBlockFetch depth f
... | nothing = putStrLn usage
dispatch ("--blockfetch-client" ∷ _) = putStrLn usage
dispatch ("--notify" ∷ f ∷ []) = checkNotify 1 f
dispatch ("--notify" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just depth = checkNotify depth f
... | nothing = putStrLn usage
dispatch ("--notify" ∷ _) = putStrLn usage
dispatch ("--interleaved" ∷ f ∷ []) = checkInterleaved 4 1 f
dispatch ("--interleaved" ∷ f ∷ k ∷ []) with readMaybe 10 k
... | just k′ = checkInterleaved k′ 1 f
... | nothing = putStrLn usage
dispatch ("--interleaved" ∷ f ∷ k ∷ n ∷ []) with readMaybe 10 k | readMaybe 10 n
... | just k′ | just n′ = checkInterleaved k′ n′ f
... | _ | _ = putStrLn usage
dispatch ("--interleaved" ∷ f ∷ k ∷ n ∷ b ∷ []) with readMaybe 10 k | readMaybe 10 n | readMaybe 10 b
... | just k′ | just n′ | just b′ = checkInterleavedWithDepths k′ n′ b′ f
... | _ | _ | _ = putStrLn usage
dispatch ("--interleaved" ∷ f ∷ k ∷ n ∷ b ∷ c ∷ []) with readMaybe 10 k | readMaybe 10 n | readMaybe 10 b | readMaybe 10 c
... | just k′ | just n′ | just b′ | just c′ = checkInterleavedWithAllDepths k′ n′ b′ c′ f
... | _ | _ | _ | _ = putStrLn usage
dispatch ("--interleaved" ∷ f ∷ k ∷ n ∷ b ∷ c ∷ t ∷ []) with readMaybe 10 k | readMaybe 10 n | readMaybe 10 b | readMaybe 10 c | readMaybe 10 t
... | just k′ | just n′ | just b′ | just c′ | just t′ = checkInterleavedWithProtocolDepths k′ n′ b′ c′ t′ f
... | _ | _ | _ | _ | _ = putStrLn usage
dispatch ("--interleaved" ∷ _) = putStrLn usage
dispatch (f ∷ []) = checkFile 4 f
dispatch (f ∷ k ∷ []) with readMaybe 10 k
... | just k′  = checkFile k′ f
... | nothing  = putStrLn usage
dispatch _ = putStrLn usage

-- Entry point.
main : Main
main = run (getArgs >>= dispatch)
