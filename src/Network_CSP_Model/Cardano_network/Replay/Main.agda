{-# OPTIONS --guardedness #-}

-- Trace replay: Fetch, Notify, or one heterogeneous interleaved stream.
-- Each component uses its certified session decider. The only replay module
-- without --safe (it imports the stdlib IO and System.Environment bindings);
-- no postulates or pragmas of its own.
--
--   Main FILE [K]      K = Fetch client pipelining bound, default 4
--   Main --notify FILE [K_NOTIFY]   Notify credit bound, default 1
--   Main --interleaved FILE [K_FETCH [K_NOTIFY]]   independent bounds
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
open import Cardano_network.Replay.Parse
import Cardano_network.Replay.SessionReport as Interleaved

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
usage = "usage: Main FILE [K_FETCH] | Main --notify FILE [K_NOTIFY] | Main --interleaved FILE [K_FETCH [K_NOTIFY]]   (defaults: Fetch 4, Notify 1)"

-- Read, check and print one file.
checkFile : ℕ → String → IO ⊤
checkFile k path = readFiniteFile path >>= λ s → putStrLn (report k s)

-- Read and decide one globally ordered interleaved-session file.
checkInterleaved : ℕ → ℕ → String → IO ⊤
checkInterleaved k depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportWithDepth k depth s)

-- Read one bounded Notify session with a role header.
checkNotify : ℕ → String → IO ⊤
checkNotify depth path = readFiniteFile path >>= λ s → putStrLn (Interleaved.reportNotifyWithDepth depth s)

-- Dispatch on the command-line arguments.
dispatch : List String → IO ⊤
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
dispatch ("--interleaved" ∷ _) = putStrLn usage
dispatch (f ∷ []) = checkFile 4 f
dispatch (f ∷ k ∷ []) with readMaybe 10 k
... | just k′  = checkFile k′ f
... | nothing  = putStrLn usage
dispatch _ = putStrLn usage

-- Entry point.
main : Main
main = run (getArgs >>= dispatch)
