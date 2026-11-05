{-# OPTIONS --guardedness #-}

-- Diagnostic stage calls reuse exact production parsing, adaptation and decisions.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as Report
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as Paired
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (notificationEq)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Payloads.Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide
  Payloads.Notification notificationEq (Payloads.votes []) as Check
module PairFile = Report.PairFile

-- Every diagnostic mode uses the same explicit production callback contract.
Contract : Set
Contract = Source.Contract

-- These are precisely the two typed lists consumed by the actual paired decision.
record TypedPair : Set where
  constructor typed
  field
    clientRows : List Rows.ClientRow
    serverRows : List Rows.ServerRow
open TypedPair public

-- Parsing and agency adaptation are production functions; failures retain production diagnostics.
decode : Contract → String → String ⊎ TypedPair
decode contract text with PairFile.parseFile text
... | inj₁ (line , message) = inj₁ ("paired input line " ++ showℕ line ++ ": " ++ message)
... | inj₂ capture with Paired.translate Log.client
  (Paired.present (map proj₂ (PairFile.clientRows capture))) Log.server
  (Paired.present (map proj₂ (PairFile.serverRows capture)))
...   | inj₁ (failure , _) = inj₁ (Report.profile contract ++ "\n" ++
  Report.pairContext capture ++ "\n" ++ Report.pairFailure capture failure)
...   | inj₂ (client , server , _) = inj₂ (typed client server)

-- A diagnostic fold visits each vote pair and both arbitrary-precision natural fields.
touchVotes : List (ℕ × ℕ) → ℕ
touchVotes [] = 0
touchVotes ((hash , voter) ∷ rest) = 1 + hash + voter + touchVotes rest

-- This forcing sum covers every constructor, optional branch and retained summary field.
touchMessage : Log.Msg → ℕ
touchMessage Log.RequestNext = 1
touchMessage Log.Quit = 2
touchMessage Log.Canceled = 3
touchMessage Log.Done = 4
touchMessage (Log.BlockAnnouncement nothing) = 5
touchMessage (Log.BlockAnnouncement (just (hash , slot , size))) = 6 + hash + slot + size
touchMessage (Log.BlockOffer hash slot size) = 7 + hash + slot + size
touchMessage (Log.BlockTxsOffer hash slot) = 8 + hash + slot
touchMessage (Log.Votes votes) = 9 + touchVotes votes

-- Direction is forced as well as every summary payload field; this is not an identity hash.
touchEvent : Log.E → ℕ
touchEvent (Log.Send , message) = 1 + touchMessage message
touchEvent (Log.Recv , message) = 2 + touchMessage message

-- Re-encoding uses the existing exact adapter rather than a copied payload mapping.
touchClient : List Rows.ClientRow → ℕ
touchClient [] = 0
touchClient (row ∷ rest) = touchEvent (Client.encode (Paired.clientWire row)) + touchClient rest

-- The server uses the same existing summary mapping in its actual role agency.
touchServer : List Rows.ServerRow → ℕ
touchServer [] = 0
touchServer (row ∷ rest) = touchEvent (Server.encode (Paired.serverWire row)) + touchServer rest

-- Printing this complete sum before the selected stage forces list spines and all natural fields.
ready : TypedPair → String
ready pair = "typed-input-ready\nclient-events=" ++ showℕ (length (clientRows pair)) ++
  ";server-events=" ++ showℕ (length (serverRows pair)) ++
  ";forcing-sum=" ++ showℕ (touchClient (clientRows pair) + touchServer (serverRows pair))

-- Guard success is a necessary-condition result, never a source trace acceptance certificate.
preconditions : (contract : Contract) (pair : TypedPair) →
  Dec (Check.AllPrechecks contract (clientRows pair) (serverRows pair))
preconditions contract pair = Check.all-prechecks? contract (clientRows pair) (serverRows pair)

-- The unchanged full backend retains its original unrestricted SourceTrace proposition.
backend : (contract : Contract) (pair : TypedPair) →
  Dec (Check.SourceTrace contract (clientRows pair) (serverRows pair))
backend contract pair = Check.For.check contract (clientRows pair) (serverRows pair)

-- This invokes the actual public typed decision, including its currently implemented guards.
complete : (contract : Contract) (pair : TypedPair) →
  Dec (Check.SourceTrace contract (clientRows pair) (serverRows pair))
complete contract pair = Check.decide contract (clientRows pair) (serverRows pair)

-- Each mode runs after the same parser, adapter and explicit forcing output.
data Mode : Set where
  decodeOnly prechecksOnly backendOnly publicDecide : Mode

-- Stable diagnostic tags distinguish guard success from full source membership decisions.
data Status : Set where
  decodeComplete preconditionsPassed preconditionsFailed backendAccepted backendRejected
    completeAccepted completeRejected invalidInput : Status

-- Diagnostic reports do not use production accepted-prefix for a precondition-only result.
record Result : Set where
  constructor result
  field
    status : Status
    detail : String
open Result public

-- Each tag has one explicit meaning understood by the profiling harness.
showStatus : Status → String
showStatus decodeComplete = "decode-complete"
showStatus preconditionsPassed = "preconditions-passed"
showStatus preconditionsFailed = "preconditions-failed"
showStatus backendAccepted = "backend-accepted"
showStatus backendRejected = "backend-rejected"
showStatus completeAccepted = "complete-accepted"
showStatus completeRejected = "complete-rejected"
showStatus invalidInput = "invalid-input"

-- The selected production function supplies the diagnostic outcome without another checker.
runMode : Mode → Contract → TypedPair → Result
runMode decodeOnly contract pair = result decodeComplete "typed decoding and common forcing only"
runMode prechecksOnly contract pair with preconditions contract pair
... | yes _ = result preconditionsPassed "AllPrechecks passed; full verification was not run"
... | no _ = result preconditionsFailed "a necessary condition failed; no acceptance is claimed"
runMode backendOnly contract pair with backend contract pair
... | yes _ = result backendAccepted "unchanged For.check constructs unrestricted SourceTrace"
... | no _ = result backendRejected "unchanged For.check refutes unrestricted SourceTrace"
runMode publicDecide contract pair with complete contract pair
... | yes _ = result completeAccepted "public decide constructs unrestricted SourceTrace"
... | no _ = result completeRejected "public decide refutes unrestricted SourceTrace"

-- Render final stage output after the distinct typed-input-ready marker and forcing sum.
render : Result → String
render answer = showStatus (status answer) ++ "\n" ++ detail answer
