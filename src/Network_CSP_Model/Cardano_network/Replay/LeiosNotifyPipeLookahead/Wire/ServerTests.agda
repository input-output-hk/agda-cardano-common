{-# OPTIONS --safe #-}

-- Fresh source-witness acceptance and exhaustive rejection at the exact local server wire profile.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Bool as Q
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient Bool as Proof

-- An exact normal value may remain pending across the Quit Receive boundary.
late-normal : Proof.SourceTrace S.nodeNext (Q.request ∷ Q.quit ∷ Q.reply (S.normal true) ∷ Q.done ∷ [])
late-normal = toWitness {a? = Proof.decide-source S.nodeNext _} tt

-- A blocked next cancels and closes without supplying any normal notification.
cancel-drain : Proof.SourceTrace S.nodeNext (Q.request ∷ Q.quit ∷ Q.reply S.canceled ∷ Q.done ∷ [])
cancel-drain = toWitness {a? = Proof.decide-source S.nodeNext _} tt

-- Delayed publication permits several exact, distinct normal values after the Quit record.
two-late-normals : Proof.SourceTrace S.nodeNext
  (Q.request ∷ Q.request ∷ Q.quit ∷ Q.reply (S.normal true) ∷ Q.reply (S.normal false) ∷ Q.done ∷ [])
two-late-normals = toWitness {a? = Proof.decide-source S.nodeNext _} tt

-- Generic next can select Canceled before flag publication and later select a normal value.
generic-canceled-then-normal : Proof.SourceTrace S.genericNext
  (Q.request ∷ Q.request ∷ Q.quit ∷ Q.reply S.canceled ∷ Q.reply (S.normal false) ∷ Q.done ∷ [])
generic-canceled-then-normal = toWitness {a? = Proof.decide-source S.genericNext _} tt

-- The same order is impossible for the node callback contract, regardless of hidden scheduling.
node-canceled-then-normal : Proof.SourceTrace S.nodeNext
  (Q.request ∷ Q.request ∷ Q.quit ∷ Q.reply S.canceled ∷ Q.reply (S.normal false) ∷ Q.done ∷ []) → ⊥
node-canceled-then-normal = toWitnessFalse {a? = Proof.decide-source S.nodeNext _} tt

-- Generic application cancellation need not wait for a Quit.
generic-before-quit : Proof.SourceTrace S.genericNext (Q.request ∷ Q.reply S.canceled ∷ [])
generic-before-quit = toWitness {a? = Proof.decide-source S.genericNext _} tt

-- Node application next never selects Canceled before shutdown publication.
node-before-quit : Proof.SourceTrace S.nodeNext (Q.request ∷ Q.reply S.canceled ∷ []) → ⊥
node-before-quit = toWitnessFalse {a? = Proof.decide-source S.nodeNext _} tt

-- Initial Quit has its real zero-job source realization.
idle-close : Proof.SourceTrace S.nodeNext (Q.quit ∷ Q.done ∷ [])
idle-close = toWitness {a? = Proof.decide-source S.nodeNext _} tt

-- A cancellation cannot discharge a request that was never received.
unsolicited-cancel : Proof.SourceTrace S.genericNext (Q.quit ∷ Q.reply S.canceled ∷ Q.done ∷ []) → ⊥
unsolicited-cancel = toWitnessFalse {a? = Proof.decide-source S.genericNext _} tt

-- Done cannot bypass the outstanding response obligation.
premature-done : Proof.SourceTrace S.nodeNext (Q.request ∷ Q.quit ∷ Q.done ∷ []) → ⊥
premature-done = toWitnessFalse {a? = Proof.decide-source S.nodeNext _} tt

-- Once the reader has received Quit it cannot receive another request.
request-after-quit : Proof.SourceTrace S.genericNext (Q.request ∷ Q.quit ∷ Q.request ∷ []) → ⊥
request-after-quit = toWitnessFalse {a? = Proof.decide-source S.genericNext _} tt

-- Repeated Quit is excluded independently of whether any response is pending.
repeated-quit : Proof.SourceTrace S.genericNext (Q.request ∷ Q.quit ∷ Q.quit ∷ []) → ⊥
repeated-quit = toWitnessFalse {a? = Proof.decide-source S.genericNext _} tt

-- A first normal Send has no fresh source witness.
missing-request : Proof.SourceTrace S.nodeNext (Q.reply (S.normal true) ∷ []) → ⊥
missing-request = toWitnessFalse {a? = Proof.decide-source S.nodeNext _} tt

-- Done cannot stand in for the missing Quit precondition.
missing-quit : Proof.SourceTrace S.nodeNext (Q.done ∷ []) → ⊥
missing-quit = toWitnessFalse {a? = Proof.decide-source S.nodeNext _} tt

-- EOF remains a permitted prefix even with a response still owed.
unfinished-prefix : Proof.SourceTrace S.nodeNext (Q.request ∷ Q.quit ∷ [])
unfinished-prefix = toWitness {a? = Proof.decide-source S.nodeNext _} tt

-- Acceptance of this EOF prefix constructs an unclosed source endpoint, not a successful return.
prefix-not-success : S.reader (proj₁ (proj₂ unfinished-prefix)) ≡ S.closed → ⊥
prefix-not-success ()
