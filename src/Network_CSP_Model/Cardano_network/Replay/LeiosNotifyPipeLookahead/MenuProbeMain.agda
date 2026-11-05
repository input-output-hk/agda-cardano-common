{-# OPTIONS --guardedness #-}

-- Standalone diagnostic IO boundary; production replay flags and decisions are unchanged.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.MenuProbeMain where

open import Level using (0ℓ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Nat.Show using (readMaybe)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Integer using (+_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; Main; run; putStrLn; readFiniteFile; _>>=_; _>>_)
open import System.Environment using (getArgs)
open import System.Exit using (exitWith; ExitCode; ExitSuccess; ExitFailure)
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Report
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.MenuProbe as Probe

-- Invalid diagnostic arguments/input stay separate from protocol verdicts.
invalid : String → IO {0ℓ} (⊤ {0ℓ})
invalid message = putStrLn ("invalid-input\n" ++ message) >> exitWith (ExitFailure (+ 2))

-- A runtime constructor-pattern helper shares one prepared basis across readiness and iteration.
-- A source-level let alone was elaborated into repeated prepare applications in the first build.
emitPrepared : Probe.Mode → Probe.Snapshot → ℕ → Cost.Contract → Probe.Prepared → IO {0ℓ} (⊤ {0ℓ})
emitPrepared mode snapshot repetitions contract preparedInput@(Probe.prepared pair basis) =
  putStrLn (Cost.ready pair) >>
  putStrLn (Probe.basisReady preparedInput) >>
  putStrLn (Probe.report mode contract snapshot repetitions preparedInput) >> exitWith ExitSuccess

-- Preparation is supplied once as the explicit runtime argument, not substituted into two projections.
decoded : Probe.Mode → Probe.Snapshot → ℕ → Cost.Contract → String → IO {0ℓ} (⊤ {0ℓ})
decoded mode snapshot repetitions contract text with Cost.decode contract text
... | inj₁ message = invalid message
... | inj₂ pair = emitPrepared mode snapshot repetitions contract (Probe.prepare pair)

-- All modes reuse the same explicit contract, shared decoder and fresh-input assertion.
probeFile : Probe.Mode → Probe.Snapshot → ℕ → String → String → IO {0ℓ} (⊤ {0ℓ})
probeFile mode snapshot repetitions path contract with Report.parseContract contract
... | nothing = invalid "expected generic-next or node-next"
... | just selected = readFiniteFile path >>= decoded mode snapshot repetitions selected

-- Bounded repetitions prevent unbounded diagnostic loops through a CLI argument.
iterationsFile : Probe.Mode → Probe.Snapshot → String → String → String → IO {0ℓ} (⊤ {0ℓ})
iterationsFile mode snapshot text path contract with readMaybe 10 text
... | nothing = invalid "iterations must be decimal in 1..4096"
... | just zero = invalid "iterations must be decimal in 1..4096"
... | just n@(suc _) with n ≤ᵇ 4096
...   | false = invalid "iterations must be decimal in 1..4096"
...   | true = probeFile mode snapshot n path contract

-- Unknown stage/snapshot names do not acquire a default raw state or another measured function.
select : String → String → String → String → String → IO {0ℓ} (⊤ {0ℓ})
select mode snapshot repetitions path contract with Probe.parseMode mode | Probe.parseSnapshot snapshot
... | nothing | _ = invalid "unsupported diagnostic stage"
... | just _ | nothing = invalid "unsupported diagnostic snapshot"
... | just selectedMode | just selectedSnapshot = iterationsFile selectedMode selectedSnapshot repetitions path contract

-- Diagnostic calls have a separate fixed grammar and never emit accepted-prefix.
dispatch : List String → IO {0ℓ} (⊤ {0ℓ})
dispatch ("--stage" ∷ mode ∷ "--snapshot" ∷ snapshot ∷ "--iterations" ∷ repetitions ∷ path ∷
  "--next-contract" ∷ contract ∷ "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) =
  select mode snapshot repetitions path contract
dispatch _ = invalid "usage: MenuProbeMain --stage basis-only|raw-ready|ready-gated|raw-menu|menu-gated|ordered-old|ordered-gated --snapshot initial|claimed|selected|after-quit|closed|inactive-reader-claimed --iterations N FILE --next-contract generic-next|node-next --observation driver-log --assume-fresh"

-- Stdlib IO/environment/exit is typechecked/compiled separately from safe diagnostic proofs.
main : Main
main = run (getArgs >>= dispatch)
