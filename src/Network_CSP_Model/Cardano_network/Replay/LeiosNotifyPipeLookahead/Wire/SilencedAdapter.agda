{-# OPTIONS --guardedness #-}

-- Local verdicts under the silenced profile: present RequestNext/Votes rows are invalid input,
-- other rows go through the existing per-event translations, then the exact silenced decision.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.SilencedAdapter where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; take; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.String using (String; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_; yes; no)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyParse as Parse
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (notificationEq)
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as SW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Payloads.Notification as CW
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.Silenced exactParams using (isVotes; hiddenKind)
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ServerSilenced Payloads.Notification isVotes as SS
import Cardano_network.LeiosNotifyPipeLookahead.Wire.ClientSilenced Payloads.Notification isVotes as CS
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as PA
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedSilenced as PairedSilenced

-- Paired silenced replay at the instance of the lookahead CLI and of PairedSilencedNative.
module PS = PairedSilenced Payloads.Notification notificationEq (Payloads.votes []) isVotes

-- Invalid input (0-based position), or certified rejection/acceptance of rows proved by `Valid`
-- to be the row-by-row translation of the given input.
data Outcome (W : Set) (Valid P : List W → Set) : Set where
  invalid : (position : ℕ) (reason : String) → Outcome W Valid P
  rejected : (rows : List W) → Valid rows → ¬ P rows → Outcome W Valid P
  accepted : (rows : List W) → Valid rows → P rows → Outcome W Valid P

-- Reason for a row whose kind the profile declares silenced.
silencedReason : String
silencedReason = "silenced kind present: RequestNext/Votes"

-- First 0-based position of a silenced-kind row, if any.
firstHidden : List (Maybe Log.E) → Maybe ℕ
firstHidden [] = nothing
firstHidden (nothing ∷ input) = Maybe.map suc (firstHidden input)
firstHidden (just event ∷ input) = if hiddenKind event then just 0 else Maybe.map suc (firstHidden input)

-- Role names as the lookahead report prints them.
showRole : Log.Role → String
showRole Log.client = "client"
showRole Log.server = "server"

-- The existing server failure texts of the lookahead report.
serverReason : Server.Reason → String
serverReason (Server.wrongRole role) = "unsupported role " ++ showRole role
serverReason (Server.wrongAgency event) = "wrong agency: " ++ Parse.showEvent event
serverReason Server.unparsedOrUnsupported = "unparsed or unsupported event"

-- The existing client failure texts of the lookahead report.
clientReason : Client.Reason → String
clientReason (Client.wrongRole role) = "unsupported role " ++ showRole role
clientReason (Client.wrongAgency event) = "wrong agency: " ++ Parse.showEvent event
clientReason Client.unparsedOrUnsupported = "unparsed or unsupported event"

-- Rows before a silenced row: an earlier translation failure wins, else the silenced row is reported.
serverCut : ∀ {Valid P} → ℕ → (input : List (Maybe Log.E)) → Server.Walk input →
  Outcome SW.Wire Valid P
serverCut _ _ (inj₁ (failure , _)) = invalid (Server.position failure) (serverReason (Server.reason failure))
serverCut position _ (inj₂ _) = invalid position silencedReason

-- No silenced row: translate every row, then decide the server silenced language.
serverRun : (contract : S.Contract) (input : List (Maybe Log.E)) → Server.Walk input →
  Outcome SW.Wire (Server.Rows input) (SS.Silenced contract)
serverRun _ _ (inj₁ (failure , _)) = invalid (Server.position failure) (serverReason (Server.reason failure))
serverRun contract _ (inj₂ (rows , valid)) with SS.decide-silenced contract rows
... | yes witness = accepted rows valid witness
... | no absent = rejected rows valid absent

-- Local server verdict under the silenced profile and an explicit callback contract.
server : (contract : S.Contract) (input : List (Maybe Log.E)) →
  Outcome SW.Wire (Server.Rows input) (SS.Silenced contract)
server contract input with firstHidden input
... | just position = serverCut position (take position input) (Server.walk (take position input))
... | nothing = serverRun contract input (Server.walk input)

-- Rows before a silenced row: an earlier translation failure wins, else the silenced row is reported.
clientCut : ∀ {Valid P} → ℕ → (input : List (Maybe Log.E)) → Client.Walk input → Outcome CW.Wire Valid P
clientCut _ _ (inj₁ (failure , _)) = invalid (Client.position failure) (clientReason (Client.reason failure))
clientCut position _ (inj₂ _) = invalid position silencedReason

-- No silenced row: translate every row, then decide the client silenced language.
clientRun : (input : List (Maybe Log.E)) → Client.Walk input → Outcome CW.Wire (Client.Rows input) CS.Silenced
clientRun _ (inj₁ (failure , _)) = invalid (Client.position failure) (clientReason (Client.reason failure))
clientRun _ (inj₂ (rows , valid)) with CS.decide-silenced rows
... | yes witness = accepted rows valid witness
... | no absent = rejected rows valid absent

-- Local client verdict under the silenced profile (generic successful client, unit return).
client : (input : List (Maybe Log.E)) → Outcome CW.Wire (Client.Rows input) CS.Silenced
client input with firstHidden input
... | just position = clientCut position (take position input) (Client.walk (take position input))
... | nothing = clientRun input (Client.walk input)

-- The translated rows of a local outcome with their input evidence, or its invalid position and reason.
rowsOf : ∀ {W : Set} {Valid P : List W → Set} → Outcome W Valid P → (ℕ × String) ⊎ Σ (List W) Valid
rowsOf (invalid position reason) = inj₁ (position , reason)
rowsOf (rejected rows valid _) = inj₂ (rows , valid)
rowsOf (accepted rows valid _) = inj₂ (rows , valid)

-- Some lossless translation of both endpoint inputs is the silenced erasure of a source paired run.
PairedAccepted : S.Contract → Client.Input → Server.Input → Set
PairedAccepted contract ci si = Σ[ c ∈ List CW.Wire ] Σ[ s ∈ List SW.Wire ]
  (Client.Rows ci c × Server.Rows si s × PS.SilencedSourceTrace contract (map PA.clientRow c) (map PA.serverRow s))

-- Translation uniqueness lifts a refutation at the translated rows to every valid translation of the inputs.
exclude : ∀ {contract ci si c s} → Client.Rows ci c → Server.Rows si s →
  ¬ PS.SilencedSourceTrace contract (map PA.clientRow c) (map PA.serverRow s) → ¬ PairedAccepted contract ci si
exclude cv sv absent (_ , _ , cv′ , sv′ , trace) with Client.rows-unique cv cv′ | Server.rows-unique sv sv′
... | refl | refl = absent trace

-- Input-level paired silenced verdict: a local invalid input (client reported first), or the paired
-- outcome on the translations of both inputs; `exclude` makes its rejection input-level.
data PairedOutcome (contract : S.Contract) (ci : Client.Input) (si : Server.Input) : Set where
  invalidClient invalidServer : (position : ℕ) (reason : String) → PairedOutcome contract ci si
  checked : (c : List CW.Wire) (s : List SW.Wire) → Client.Rows ci c → Server.Rows si s →
    PS.Outcome contract (map PA.clientRow c) (map PA.serverRow s) → PairedOutcome contract ci si

-- Both local silenced adapters (hidden-kind precedence kept), then the paired check on their rows.
paired : (contract : S.Contract) (ci : Client.Input) (si : Server.Input) → PairedOutcome contract ci si
paired contract ci si with rowsOf (client ci) | rowsOf (server contract si)
... | inj₁ (position , reason) | _ = invalidClient position reason
... | inj₂ _ | inj₁ (position , reason) = invalidServer position reason
... | inj₂ (c , cv) | inj₂ (s , sv) = checked c s cv sv (PS.check contract (map PA.clientRow c) (map PA.serverRow s))
