{-# OPTIONS --guardedness #-}

-- Exact normalized-field, agency, parser-outcome and callback-contract regression witnesses.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapterTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyParse as Parse
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Payloads.Notification as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as A

-- A small observable tag distinguishes schema/agency failure from exhaustive protocol rejection.
data Kind : Set where
  invalid rejected accepted : Kind

-- Only the verdict category is inspected; no proof evidence is discarded by the adapter itself.
kind : ∀ {contract role input} → A.Verdict contract role input → Kind
kind (A.invalidInput _ _) = invalid
kind (A.protocolRejected _ _ _ _) = rejected
kind (A.accepted _) = accepted

-- Exact field checks cover all message forms, including optional and ordered duplicate metadata.
payloads : List W.Wire
payloads = W.request ∷ W.quit ∷ W.done ∷ W.reply S.canceled ∷
  W.reply (S.normal (Payloads.announcement (header nothing))) ∷
  W.reply (S.normal (Payloads.announcement (header (just (17 , 23 , 31))))) ∷
  W.reply (S.normal (Payloads.offer (37 , 41) 43)) ∷
  W.reply (S.normal (Payloads.txsOffer (47 , 53))) ∷
  W.reply (S.normal (Payloads.votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []))) ∷ []

-- Re-encoding retains every concrete selected field with no deduplication or ordering change.
payload-roundtrips : map A.decode (map A.encode payloads) ≡ map just payloads
payload-roundtrips = refl

-- Empty announcement is a valid payload rather than a failed row parse.
empty-announcement : A.decode (Log.Send , Log.BlockAnnouncement nothing) ≡
  just (W.reply (S.normal (Payloads.announcement (header nothing))))
empty-announcement = refl

-- The existing lexical parser rejects a malformed present vote pair before the adapter is called.
malformed-vote : Parse.parseEvent "Send Votes ab::2" ≡ nothing
malformed-vote = refl

-- Exact parsing preserves duplicate pairs and their source order.
parsed-votes : Parse.parseEvent "Send Votes 43:71,49:79,43:71" ≡
  just (Log.Send , Log.Votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []))
parsed-votes = refl

-- A parser failure in the second row stays an explicit located input failure.
malformed-retained : kind (A.check S.nodeNext Log.server
  (just (Log.Recv , Log.RequestNext) ∷ Parse.parseEvent "Send Votes ab::2" ∷ [])) ≡ invalid
malformed-retained = refl

-- Extract only an invalid-input location for this concrete diagnostic regression.
invalid-position : ∀ {contract role input} → A.Verdict contract role input → ℕ
invalid-position (A.invalidInput failure _) = A.position failure
invalid-position _ = 99

-- The failed row retains its zero-based normalized-input position.
failure-index : invalid-position (A.check S.nodeNext Log.server
  (just (Log.Recv , Log.RequestNext) ∷ nothing ∷ [])) ≡ 1
failure-index = refl

-- Server input refuses the opposite request agency.
wrong-request-agency : kind (A.check-normalized S.nodeNext Log.server ((Log.Send , Log.RequestNext) ∷ [])) ≡ invalid
wrong-request-agency = refl

-- Server input refuses the opposite reply agency even when a request is outstanding.
wrong-reply-agency : kind (A.check-normalized S.nodeNext Log.server
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Canceled) ∷ [])) ≡ invalid
wrong-reply-agency = refl

-- An explicit client role is rejected even for an empty capture.
wrong-role-empty : kind (A.check-normalized S.nodeNext Log.client []) ≡ invalid
wrong-role-empty = refl

-- The optional empty announcement follows the normal response path and then closes.
announcement-close : A.Accepted S.nodeNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
   (Log.Send , Log.BlockAnnouncement nothing) ∷ (Log.Send , Log.Done) ∷ []))
announcement-close = toWitness {a? = A.decide S.nodeNext Log.server _} tt

-- EOF after RequestNext is an admitted unfinished prefix, not evidence of completion.
unfinished-prefix : A.Accepted S.nodeNext Log.server (A.present ((Log.Recv , Log.RequestNext) ∷ []))
unfinished-prefix = toWitness {a? = A.decide S.nodeNext Log.server _} tt

-- The source endpoint chosen by that EOF acceptance witness has not closed successfully.
unfinished-not-closed : S.reader (proj₁ (proj₂ (proj₂ (proj₂ unfinished-prefix)))) ≡ S.closed → ⊥
unfinished-not-closed ()

-- A callback reply sent before Quit may cancel only under the generic callback contract.
generic-before-quit : A.Accepted S.genericNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.Canceled) ∷ []))
generic-before-quit = toWitness {a? = A.decide S.genericNext Log.server _} tt

-- The node contract rejects all matching hidden callback schedules for that same cancellation.
node-before-quit : A.Accepted S.nodeNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Send , Log.Canceled) ∷ [])) → ⊥
node-before-quit = toWitnessFalse {a? = A.decide S.nodeNext Log.server _} tt

-- Normal callbacks already selected before shutdown can still produce wire replies after Recv Quit.
normal-after-quit : A.Accepted S.nodeNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
   (Log.Send , Log.BlockOffer 17 23 31) ∷ (Log.Send , Log.Done) ∷ []))
normal-after-quit = toWitness {a? = A.decide S.nodeNext Log.server _} tt

-- Node next forbids a normal response after the first cancellation, regardless of hidden scheduling.
node-after-cancel : A.Accepted S.nodeNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
   (Log.Send , Log.Canceled) ∷ (Log.Send , Log.BlockTxsOffer 17 23) ∷ (Log.Send , Log.Done) ∷ [])) → ⊥
node-after-cancel = toWitnessFalse {a? = A.decide S.nodeNext Log.server _} tt

-- Generic next permits that same order by selecting Canceled before flag publication.
generic-after-cancel : A.Accepted S.genericNext Log.server (A.present
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
   (Log.Send , Log.Canceled) ∷ (Log.Send , Log.BlockTxsOffer 17 23) ∷ (Log.Send , Log.Done) ∷ []))
generic-after-cancel = toWitness {a? = A.decide S.genericNext Log.server _} tt

-- Done with a pending obligation is a protocol rejection, not a direction/schema failure.
premature-done : kind (A.check-normalized S.nodeNext Log.server
  ((Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷ (Log.Send , Log.Done) ∷ [])) ≡ rejected
premature-done = refl

-- A well-directed Done without Quit likewise refutes the source language exhaustively.
missing-quit : kind (A.check-normalized S.nodeNext Log.server ((Log.Send , Log.Done) ∷ [])) ≡ rejected
missing-quit = refl
