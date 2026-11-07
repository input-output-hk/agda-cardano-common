{-# OPTIONS --guardedness #-}

-- Explicit node-control reports preserve exact rows, diagnostics and prefix scope.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeClientReportTests where

open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.String using (_++_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
import Cardano_network.LeiosNotifyPipe exactParams as P
import Cardano_network.LeiosNotifyPipeLookahead.Model P.Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client P.Notification as W
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeClientReport as R
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientAdapter as A

-- A tag exposes status classes without erasing any refutation carried by the adapter.
data Kind : Set where
  invalid rejected accepted : Kind

-- Invalid input remains distinct from failure of every matching source policy schedule.
kind : ∀ {role input} → A.Verdict role input → Kind
kind (A.invalidInput _ _) = invalid
kind (A.protocolRejected _ _ _ _) = rejected
kind (A.accepted _) = accepted

-- Wrong endpoint role is invalid even when the trace contains no events.
wrong-role-adapter : kind (A.check-normalized Log.server []) ≡ invalid
wrong-role-adapter = refl

-- Opposite command agency cannot become an erased callback.
wrong-agency-adapter : kind (A.check-normalized Log.client ((Log.Recv , Log.RequestNext) ∷ [])) ≡ invalid
wrong-agency-adapter = refl

-- A correctly directed initial Done fails the policy rather than schema validation.
missing-quit-adapter : kind (A.check-normalized Log.client ((Log.Recv , Log.Done) ∷ [])) ≡ rejected
missing-quit-adapter = refl

-- Reusing the existing row schema retains exact optional fields and repeated vote entries.
payloads : List W.Wire
payloads = W.request ∷ W.quit ∷ W.done ∷ W.reply S.canceled ∷
  W.reply (S.normal (P.announcement (header nothing))) ∷
  W.reply (S.normal (P.announcement (header (just (17 , 23 , 31))))) ∷
  W.reply (S.normal (P.offer (37 , 41) 43)) ∷
  W.reply (S.normal (P.txsOffer (47 , 53))) ∷
  W.reply (S.normal (P.votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ []))) ∷ []

-- No new payload codec is introduced by the policy-specific adapter.
payload-roundtrips : map A.decode (map A.encode payloads) ≡ map just payloads
payload-roundtrips = refl

-- Each encoded row retains its independent exact encoding equation in order.
encoded-rows : ∀ rows → A.Rows (A.present (map A.encode rows)) rows
encoded-rows [] = A.empty
encoded-rows (row ∷ rows) = A.linked refl (encoded-rows rows)

-- Duplicated payload values remain separate retained input positions.
payload-count : length payloads ≡ length (A.present (map A.encode payloads))
payload-count = A.no-row-loss (encoded-rows payloads)

-- Re-encoding returns the original complete typed parser-outcome input.
payload-input-roundtrip : map (λ row → just (A.encode row)) payloads ≡ A.present (map A.encode payloads)
payload-input-roundtrip = A.roundtrip (encoded-rows payloads)

-- Empty EOF is a prefix witness rather than proof of successful wire completion.
empty-prefix : R.status (R.local "role client\n") ≡ R.acceptedPrefix
empty-prefix = refl

-- Idle shutdown is permitted by an actual unit-return stop decision.
idle-close : R.status (R.local "role client\nSend Quit\nRecv Done\n") ≡ R.acceptedPrefix
idle-close = refl

-- A reply can precede its pending Request Send hook in this source model as well.
receive-ahead : R.status (R.local "role client\nRecv BlockOffer 2a 7 3\n") ≡ R.acceptedPrefix
receive-ahead = refl

-- EOF at Cancel reception does not force the pending flag read or abnormal handler.
pending-cancel : R.status (R.local "role client\nRecv Canceled\n") ≡ R.acceptedPrefix
pending-cancel = refl

-- A pending Request Send cannot be replaced by Quit after the early reply.
lead-cannot-quit : R.status (R.local "role client\nRecv Canceled\nSend Quit\n") ≡ R.protocolRejected
lead-cannot-quit = refl

-- A correctly encoded Done before Quit is an exhaustive source-language rejection.
missing-quit-report : R.status (R.local "role client\nRecv Done\n") ≡ R.protocolRejected
missing-quit-report = refl

-- Wrong role is rejected before checking any node-control steps.
wrong-role-report : R.status (R.local "role server\n") ≡ R.invalidInput
wrong-role-report = refl

-- A malformed number stays an explicit parse failure rather than disappearing.
malformed-number : R.status (R.local "role client\nRecv BlockOffer xyz 7 3\n") ≡ R.invalidInput
malformed-number = refl

-- The reported line offset includes the role header and every preceding input row.
retained-error-line : R.detail (R.local "role client\nSend RequestNext\ninvalid row\n") ≡
  R.profile ++ "\ninput line 3: unparsed or unsupported event"
retained-error-line = refl

-- Agency diagnostics use the original direction rather than the reversed server codec.
agency-error-line : R.detail (R.local "role client\nRecv RequestNext\n") ≡
  R.profile ++ "\ninput line 2: wrong agency: Recv RequestNext"
agency-error-line = refl

-- Acceptance is also available as a full normalized-input and source policy witness.
accepted-witness : A.Accepted Log.client (A.present ((Log.Send , Log.Quit) ∷ (Log.Recv , Log.Done) ∷ []))
accepted-witness = toWitness {a? = A.decide Log.client _} tt
