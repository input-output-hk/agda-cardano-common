{-# OPTIONS --guardedness #-}

-- Separate IO entry point for diagnostic stage costs, with no production CLI changes.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbeMain where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.String using (String)
open import Data.Sum using (inj₁; inj₂)
open import Data.Integer using (+_)
open import Data.Unit.Polymorphic using (⊤)
open import IO using (IO; Main; run; putStrLn; readFiniteFile; _>>=_; _>>_)
open import System.Environment using (getArgs)
open import System.Exit using (exitWith; ExitCode; ExitSuccess; ExitFailure)
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Report
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe as Probe

-- Stage tags and exit codes agree; only full backend/public modes decide SourceTrace.
caseCode : Probe.Status → ExitCode
caseCode Probe.decodeComplete = ExitSuccess
caseCode Probe.preconditionsPassed = ExitSuccess
caseCode Probe.preconditionsFailed = ExitFailure (+ 1)
caseCode Probe.backendAccepted = ExitSuccess
caseCode Probe.backendRejected = ExitFailure (+ 1)
caseCode Probe.completeAccepted = ExitSuccess
caseCode Probe.completeRejected = ExitFailure (+ 1)
caseCode Probe.invalidInput = ExitFailure (+ 2)

-- Final reporting preserves the separate diagnostic tag vocabulary.
emit : Probe.Result → IO {0ℓ} (⊤ {0ℓ})
emit answer = putStrLn (Probe.render answer) >> exitWith (caseCode (Probe.status answer))

-- Every mode has exactly the same parsed typed pair and performs the same forcing output first.
decoded : Probe.Mode → Probe.Contract → String → IO {0ℓ} (⊤ {0ℓ})
decoded mode contract text with Probe.decode contract text
... | inj₁ message = emit (Probe.result Probe.invalidInput message)
... | inj₂ pair = putStrLn (Probe.ready pair) >>= λ _ → emit (Probe.runMode mode contract pair)

-- Parsing and stage selection retain an explicit contract and fresh driver-log assumption.
probeFile : Probe.Mode → String → String → IO {0ℓ} (⊤ {0ℓ})
probeFile mode path contract with Report.parseContract contract
... | nothing = emit (Probe.result Probe.invalidInput "expected generic-next or node-next")
... | just selected = readFiniteFile path >>= decoded mode selected

-- Diagnostic stages must be requested explicitly; no verifier success is implied by decode/guards.
select : String → String → String → IO {0ℓ} (⊤ {0ℓ})
select "decode-only" = probeFile Probe.decodeOnly
select "prechecks-only" = probeFile Probe.prechecksOnly
select "backend-only" = probeFile Probe.backendOnly
select "public-decide" = probeFile Probe.publicDecide
select _ = λ _ _ → emit (Probe.result Probe.invalidInput "unsupported diagnostic stage")

-- This separate grammar intentionally introduces no flags on the production verifier.
dispatch : List String → IO {0ℓ} (⊤ {0ℓ})
dispatch ("--stage" ∷ mode ∷ path ∷ "--next-contract" ∷ contract ∷
  "--observation" ∷ "driver-log" ∷ "--assume-fresh" ∷ []) = select mode path contract
dispatch _ = emit (Probe.result Probe.invalidInput
  "usage: CostProbeMain --stage decode-only|prechecks-only|backend-only|public-decide FILE --next-contract generic-next|node-next --observation driver-log --assume-fresh")

-- The stdlib IO/environment/exit boundary is checked and compiled separately from the pure module.
main : Main
main = run (getArgs >>= dispatch)
