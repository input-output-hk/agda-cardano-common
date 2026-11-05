{-# OPTIONS --safe #-}

-- Additional credit necessity preserves real Lead traces and leaves a genuine full-search fallback.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverCreditPrecheckTests where

open import Data.Bool using (Bool; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheck Bool ⊤ as Credit
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideTests as Existing

-- Both pending Sends may remain unrecorded after their packet Receives.
lead-client : List Rows.ClientRow
lead-client = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- The recorded Request Receive has already enabled the actual server reply.
lead-server : List Rows.ServerRow
lead-server = Rows.receiveCommand D.request ∷ []

-- Necessity is applied to an independently constructed source execution, not to guard success.
lead-necessary : Check.FullPrechecks S.genericNext lead-client lead-server
lead-necessary = Check.full-precheck-necessary Existing.delayed-source

-- The public decision still accepts that actual pending-hook prefix.
lead-accepted : Check.SourceTrace S.genericNext lead-client lead-server
lead-accepted = toWitness {a? = Check.decide S.genericNext lead-client lead-server} tt

-- An initial unsolicited normal reply passed the original local/prefix/count predicates.
unsolicited-three-pass : ∀ contract → Check.Prechecks contract lead-client []
unsolicited-three-pass contract = toWitness {a? = Check.prechecks? contract lead-client []} tt

-- With no recorded server Request, the new condition directly refutes this history.
unsolicited-credit-fails : Credit.Pass lead-client [] → ⊥
unsolicited-credit-fails = toWitnessFalse {a? = Credit.decide lead-client []} tt

-- Rejection still concerns the unrestricted original source predicate.
unsolicited-rejected : Check.SourceTrace S.nodeNext lead-client [] → ⊥
unsolicited-rejected = toWitnessFalse {a? = Check.decide S.nodeNext lead-client []} tt

-- Closing has no reply credit: Quit and Done cannot be counted as Request and Reply.
close-client : List Rows.ClientRow
close-client = Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []

-- All four necessary predicates pass while no server Quit Receive has been recorded.
close-four-pass : ∀ contract → Check.FullPrechecks contract close-client []
close-four-pass contract = toWitness {a? = Check.full-prechecks? contract close-client []} tt

-- The complete backend independently excludes a Done without the server's recorded Quit.
close-backend-rejected : Check.SourceTrace S.nodeNext close-client [] → ⊥
close-backend-rejected = toWitnessFalse {a? = Check.For.check S.nodeNext close-client []} tt

-- The later shutdown guard now refutes this original four-guard counterexample before full search.
close-public-rejected : Check.SourceTrace S.nodeNext close-client [] → ⊥
close-public-rejected = toWitnessFalse {a? = Check.decide S.nodeNext close-client []} tt
