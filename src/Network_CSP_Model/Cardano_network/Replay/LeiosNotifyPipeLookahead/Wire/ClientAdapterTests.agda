{-# OPTIONS --guardedness #-}

-- Exact summary fields, every invalid-input class and local generic client prefix decisions.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapterTests where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipe exactParams as P
import Cardano_network.LeiosNotifyPipeLookahead.Model P.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client P.Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as A

-- The complete schema includes both optional announcement shapes and ordered repeated votes.
payloads : List W.Wire
payloads = W.request ∷ W.quit ∷ W.done ∷ W.reply S.canceled ∷
  W.reply (S.normal (P.announcement (header nothing))) ∷
  W.reply (S.normal (P.announcement (header (just (17 , 23 , 31))))) ∷
  W.reply (S.normal (P.offer (37 , 41) 43)) ∷
  W.reply (S.normal (P.txsOffer (47 , 53))) ∷
  W.reply (S.normal (P.votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []))) ∷ []

-- Schema reuse reverses only agency and preserves every selected exact field.
all-payload-roundtrips : map A.decode (map A.encode payloads) ≡ map just payloads
all-payload-roundtrips = refl

-- Every encoded list has a complete position-by-position validation witness.
encoded-rows : ∀ rows → A.Rows (A.present (map A.encode rows)) rows
encoded-rows [] = A.empty
encoded-rows (row ∷ rows) = A.linked refl (encoded-rows rows)

-- Re-encoding retains the complete typed parser-outcome list, including duplicate entries.
all-input-roundtrip : map (λ row → just (A.encode row)) payloads ≡ A.present (map A.encode payloads)
all-input-roundtrip = A.roundtrip (encoded-rows payloads)

-- A small tag inspects diagnostics without dropping any adapter evidence.
data Kind : Set where
  invalid rejected accepted : Kind

-- All callers can distinguish schema/agency failures from actual source-language rejection.
kind : ∀ {role input} → A.Verdict role input → Kind
kind (A.invalidInput _ _) = invalid
kind (A.protocolRejected _ _ _ _) = rejected
kind (A.accepted _) = accepted

-- Explicitly wrong endpoint role remains invalid even with no rows.
wrong-role-empty : kind (A.check-normalized Log.server []) ≡ invalid
wrong-role-empty = refl

-- Client commands must be Send records rather than the server's receive agency.
wrong-command-agency : kind (A.check-normalized Log.client ((Log.Recv , Log.RequestNext) ∷ [])) ≡ invalid
wrong-command-agency = refl

-- Client notification records must use Receive agency.
wrong-response-agency : kind (A.check-normalized Log.client ((Log.Send , Log.Votes []) ∷ [])) ≡ invalid
wrong-response-agency = refl

-- An unparsed second row remains explicit rather than disappearing behind a valid first record.
unparsed-position : ∀ {role input} → A.Verdict role input → ℕ
unparsed-position (A.invalidInput failure _) = A.position failure
unparsed-position _ = 99

-- Reported coordinates are zero-based normalized-input indices.
second-row-retained : unparsed-position (A.check Log.client
  (just (Log.Send , Log.RequestNext) ∷ nothing ∷ [])) ≡ 1
second-row-retained = refl

-- Early reply EOF is admitted with its client Request Send hook still pending.
receive-ahead-eof : A.Accepted Log.client (A.present ((Log.Recv , Log.BlockAnnouncement nothing) ∷ []))
receive-ahead-eof = toWitness {a? = A.decide Log.client _} tt

-- A leading reply cannot be followed by Quit until the outstanding Send hook finishes.
lead-cannot-quit : A.Accepted Log.client (A.present
  ((Log.Recv , Log.Canceled) ∷ (Log.Send , Log.Quit) ∷ [])) → ⊥
lead-cannot-quit = toWitnessFalse {a? = A.decide Log.client _} tt

-- Idle shutdown uses the generic unit-return source and accepts genuine Done after Quit.
idle-close : A.Accepted Log.client (A.present ((Log.Send , Log.Quit) ∷ (Log.Recv , Log.Done) ∷ []))
idle-close = toWitness {a? = A.decide Log.client _} tt

-- A well-directed initial Done is a protocol rejection, not invalid input.
missing-quit : kind (A.check-normalized Log.client ((Log.Recv , Log.Done) ∷ [])) ≡ rejected
missing-quit = refl
