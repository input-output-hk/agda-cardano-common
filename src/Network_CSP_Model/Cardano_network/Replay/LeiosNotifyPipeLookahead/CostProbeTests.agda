{-# OPTIONS --guardedness #-}

-- Small diagnostic gates protect tag semantics, shared parser errors and forcing scope.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbeTests where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe as Probe
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (notificationEq)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as Source
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Payloads.Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Payloads.Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide
  Payloads.Notification notificationEq (Payloads.votes []) as Check

-- Guard success has a distinct diagnostic tag and does not claim full acceptance.
empty-preconditions-tag : Probe.showStatus (Probe.status
  (Probe.runMode Probe.prechecksOnly Source.nodeNext (Probe.typed [] []))) ≡ "preconditions-passed"
empty-preconditions-tag = refl

-- A validly typed but phase-invalid client event fails the actual production preconditions.
bad-phase : Probe.TypedPair
bad-phase = Probe.typed (Rows.receiveResponse D.done ∷ []) []

-- This diagnostic failure cannot accidentally be rendered as an acceptance tag.
bad-phase-tag : Probe.showStatus (Probe.status
  (Probe.runMode Probe.prechecksOnly Source.nodeNext bad-phase)) ≡ "preconditions-failed"
bad-phase-tag = refl

-- The backend entry retains exactly the unrestricted source proposition used by production.
same-backend-proposition : Dec (Check.SourceTrace Source.nodeNext [] [])
same-backend-proposition = Probe.backend Source.nodeNext (Probe.typed [] [])

-- Optional metadata is traversed in the common forcing output rather than left as an opaque thunk.
optional-fields-touched : Probe.touchMessage (Log.BlockAnnouncement (just (1 , 2 , 3))) ≡ 12
optional-fields-touched = refl

-- Vote duplicates contribute independently and every hash/voter natural is forced.
duplicate-vote-fields-touched : Probe.touchMessage
  (Log.Votes ((1 , 2) ∷ (3 , 4) ∷ (1 , 2) ∷ [])) ≡ 25
duplicate-vote-fields-touched = refl

-- The forcing sum is deliberately not an identity hash: reordered equal-field votes can collide.
forcing-is-not-an-identity : Probe.touchMessage (Log.Votes ((1 , 2) ∷ (3 , 4) ∷ [])) ≡
  Probe.touchMessage (Log.Votes ((3 , 4) ∷ (1 , 2) ∷ []))
forcing-is-not-an-identity = refl

-- The existing paired header syntax is reused verbatim in every diagnostic mode.
header : String
header = "pair LeiosNotifyP probe-connection probe-session\n" ++
  "client client-node client-connection 0 fresh client-source.log\n" ++
  "server server-node server-connection 0 fresh server-source.log\n"

-- An invalid final field must be detected even after a preceding valid request row.
late-invalid : String
late-invalid = header ++ "client 11 Send RequestNext\nclient 12 Recv Votes invalid\n"

-- Error position and wording are supplied by the same production parser, not a probe grammar.
same-parser-error : Probe.decode Source.nodeNext late-invalid ≡
  inj₁ "paired input line 5: expected client <increasing-source-line> <protocol-event>"
same-parser-error = refl
