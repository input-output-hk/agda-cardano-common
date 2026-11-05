{-# OPTIONS --guardedness #-}

-- Typed schema regressions; these do not execute or prove JSON/Python/logger fidelity.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.LoggerObservationTests where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.Replay.LeiosNotifySession as Log
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as C
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Srv
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as P
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.LoggerObservation as O

-- Every message shape includes exact optional values and an ordered duplicate vote.
summaries : List Log.E
summaries = (Log.Send , Log.RequestNext) ∷ (Log.Send , Log.Quit) ∷
  (Log.Recv , Log.BlockAnnouncement nothing) ∷
  (Log.Recv , Log.BlockAnnouncement (just (17 , 23 , 31))) ∷
  (Log.Recv , Log.BlockOffer 37 41 43) ∷ (Log.Recv , Log.BlockTxsOffer 47 53) ∷
  (Log.Recv , Log.Votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ [])) ∷
  (Log.Recv , Log.Votes []) ∷ (Log.Recv , Log.Canceled) ∷ (Log.Recv , Log.Done) ∷ []

-- The independent typed hook representation computes to the entire exact normalized list.
all-schema-values : O.input (map O.representative summaries) ≡ C.present summaries
all-schema-values = refl

-- A reusable pointwise witness retains one output occurrence per selected input hook.
all-schema-witnesses : O.Observation (map O.representative summaries) summaries
all-schema-witnesses = O.representative-list summaries

-- Length preservation concerns supplied selected hooks, including repeated field values.
no-selected-row-loss : length summaries ≡ length (map O.representative summaries)
no-selected-row-loss = O.mapped-length all-schema-witnesses

-- The alternative RequestNext namespace spelling remains accepted without changing the message.
request-alias : O.normalize (O.hook O.sendHook O.notificationRequestTag O.sendData O.requestMessage) ≡ just (Log.Send , Log.RequestNext)
request-alias = refl

-- Namespace/data direction contradictions are explicit failed outcomes.
direction-mismatch : O.normalize (O.hook O.sendHook O.requestTag O.recvData O.requestMessage) ≡ nothing
direction-mismatch = refl

-- The independent namespace and message tags cannot be silently repaired.
message-tag-mismatch : O.normalize (O.hook O.sendHook O.quitTag O.sendData O.doneMessage) ≡ nothing
message-tag-mismatch = refl

-- Unsupported namespace tags remain invalid rather than being hidden callbacks.
unsupported-namespace : O.normalize (O.hook O.sendHook O.unsupportedTag O.sendData O.requestMessage) ≡ nothing
unsupported-namespace = refl

-- Unsupported data.kind has an explicit failed normalization outcome.
unsupported-data-direction : O.normalize (O.hook O.sendHook O.requestTag O.unsupportedData O.requestMessage) ≡ nothing
unsupported-data-direction = refl

-- The actual namespace table derives client role from a Send RequestNext command.
request-namespace-role : O.observedRole (O.hook O.sendHook O.requestTag O.sendData O.requestMessage) ≡ just Log.client
request-namespace-role = refl

-- A Send Done has server agency even though its typed fields are otherwise valid.
done-namespace-role : O.observedRole (O.hook O.sendHook O.doneTag O.sendData O.doneMessage) ≡ just Log.server
done-namespace-role = refl

-- A valid hook with the wrong selected endpoint agency is rejected by the client adapter.
wrong-role-client : C.Adapted Log.client (O.input
  (O.hook O.sendHook O.doneTag O.sendData O.doneMessage ∷ [])) → ⊥
wrong-role-client (_ , _ , C.linked {row = row} same _) = C.decode-missing {row = row} refl same

-- Sending RequestNext similarly cannot be adapted as a server-side selected hook.
wrong-role-server : Srv.Adapted Log.server (O.input
  (O.hook O.sendHook O.requestTag O.sendData O.requestMessage ∷ [])) → ⊥
wrong-role-server (_ , _ , Srv.linked {row = row} same _) = Srv.decode-missing {row = row} refl same

-- Missing one retained announcement field differs from all-absent metadata.
partial-announcement : ∀ hash slot → O.normalize
  (O.hook O.receiveHook O.announcementTag O.recvData (O.announcementMessage (just hash) (just slot) nothing)) ≡ nothing
partial-announcement hash slot = refl

-- Exact payload reconstruction is independent of arbitrary wire-language acceptance.
exact-vote-fields : O.messageRepresentative (Log.Votes ((67 , 71) ∷ (73 , 79) ∷ (67 , 71) ∷ [])) ≡
  O.votesMessage (O.voteFields 67 71 ∷ O.voteFields 73 79 ∷ O.voteFields 67 71 ∷ [])
exact-vote-fields = refl

-- Invalid selected hooks keep their positions in front of later valid input.
bad-hook : O.Hook
bad-hook = O.hook O.sendHook O.quitTag O.sendData O.doneMessage

-- Mapping uses map, so a failure cannot disappear through a mapMaybe projection.
bad-position-retained : O.input (bad-hook ∷ O.representative (Log.Send , Log.Quit) ∷ []) ≡
  nothing ∷ just (Log.Send , Log.Quit) ∷ []
bad-position-retained = refl

-- The existing client validator cannot adapt an input containing that invalid hook.
bad-client-unadaptable : C.Adapted Log.client (O.input (bad-hook ∷ [])) → ⊥
bad-client-unadaptable (_ , _ , ())

-- The same malformed selected hook cannot be adapted on the server side either.
bad-server-unadaptable : Srv.Adapted Log.server (O.input (bad-hook ∷ [])) → ⊥
bad-server-unadaptable (_ , _ , ())

-- Ordinary idle shutdown gives an inhabited generic client source acceptance.
client-close : List Log.E
client-close = (Log.Send , Log.Quit) ∷ (Log.Recv , Log.Done) ∷ []

-- The raw-like typed hook list is validated before reaching the existing client checker.
typed-client-close : C.Accepted Log.client (O.input (map O.representative client-close))
typed-client-close = proj₂ (O.client-transport (O.representative-list client-close))
  (toWitness {a? = C.decide Log.client (C.present client-close)} tt)

-- The corresponding server hook directions are Receive Quit and Send Done.
server-close : List Log.E
server-close = (Log.Recv , Log.Quit) ∷ (Log.Send , Log.Done) ∷ []

-- Existing generic server acceptance transports through the typed schema boundary.
typed-server-close : Srv.Accepted S.genericNext Log.server (O.input (map O.representative server-close))
typed-server-close = proj₂ (O.server-transport S.genericNext (O.representative-list server-close))
  (toWitness {a? = Srv.decide S.genericNext Log.server (Srv.present server-close)} tt)

-- The paired checker retains both complete local orders without imposing a timestamp merge.
typed-paired-close : P.Accepted S.genericNext Log.client (O.input (map O.representative client-close))
  Log.server (O.input (map O.representative server-close))
typed-paired-close = proj₂ (O.paired-transport S.genericNext (O.representative-list client-close) (O.representative-list server-close))
  (toWitness {a? = P.decide S.genericNext Log.client (P.present client-close) Log.server (P.present server-close)} tt)
