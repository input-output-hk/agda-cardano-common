{-# OPTIONS --safe #-}

-- Non-vacuity and negative controls for strict Notify and mixed replay.
module Cardano_network.Replay.NotifyTests where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Semantics.Replay using (module Traces)
open import Cardano_network.Replay.LeiosNotifySession
import Cardano_network.Replay.Sessions as S
import Cardano_network.Replay.ParseNotify as P
open import Cardano_network.Replay.SessionReport using (report; reportNotify)

-- One consumer session receives each kind, including both announcement encodings.
rounds : List E
rounds = (Send , RequestNext) ∷ (Recv , BlockAnnouncement nothing)
       ∷ (Send , RequestNext) ∷ (Recv , BlockAnnouncement (just (7 , 2 , 10)))
       ∷ (Send , RequestNext) ∷ (Recv , BlockOffer 8 3 20)
       ∷ (Send , RequestNext) ∷ (Recv , BlockTxsOffer 9 4)
       ∷ (Send , RequestNext) ∷ (Recv , Votes ((42 , 1) ∷ (43 , 2) ∷ []))
       ∷ (Send , Done) ∷ []

-- The decision reduces to yes on all six message forms.
rounds-ok : True (Spec.check client rounds)
rounds-ok = tt

-- Acceptance supplies an explicit initial-state run witness.
rounds-run : Spec.HasTrace client idle rounds
rounds-run = toWitness {a? = Spec.check client rounds} rounds-ok

-- An unsolicited notification has no original depth-one protocol run.
unsolicited : False (Spec.check client ((Recv , BlockOffer 7 0 10) ∷ []))
unsolicited = tt

-- Rejection supplies a refutation, not merely a false boolean.
unsolicited-refuted : ¬ Spec.HasTrace client idle ((Recv , BlockOffer 7 0 10) ∷ [])
unsolicited-refuted = toWitnessFalse {a? = Spec.check client ((Recv , BlockOffer 7 0 10) ∷ [])} unsolicited

-- A second outstanding request exceeds the exact LeiosNotifyP language.
pipelined : False (Spec.check client ((Send , RequestNext) ∷ (Send , RequestNext) ∷ []))
pipelined = tt

-- Done is available only from idle, never while awaiting a notification.
busy-done : False (Spec.check server ((Recv , RequestNext) ∷ (Recv , Done) ∷ []))
busy-done = tt

-- The responder cannot request work from the initiator.
wrong-agency : False (Spec.check server ((Send , RequestNext) ∷ []))
wrong-agency = tt

-- A generation stays closed after Done.
after-done : False (Spec.check client ((Send , Done) ∷ (Send , RequestNext) ∷ []))
after-done = tt

-- Long polling need not finish for an observed finite prefix to be legal.
waiting : True (Spec.check server ((Recv , RequestNext) ∷ []))
waiting = tt

-- Votes can be empty; they still consume exactly one request.
empty-votes : True (Spec.check server ((Recv , RequestNext) ∷ (Send , Votes []) ∷ []))
empty-votes = tt

-- Notify requests identify no hash; the notification is application-selected.
unconstrained-offer : True (Spec.check client ((Send , RequestNext) ∷ (Recv , BlockOffer 999 88 10) ∷ []))
unconstrained-offer = tt

-- Independent Notify peers each hold their own outstanding request.
interleaved-notify : report 1 "sessions notify:client notify:server\n0 Send RequestNext\n1 Recv RequestNext\n1 Send Votes -\n0 Recv BlockOffer ab 7 20\n" ≡ "accepted (4 events, 2 sessions)"
interleaved-notify = refl

-- Fetch and Notify share one product trace with protocol-specific event types.
mixed : report 1 "sessions notify:client fetch:client notify:server\n0 Send RequestNext\n1 Send BlockRequest ab 7\n2 Recv RequestNext\n0 Recv BlockOffer cd 8 20\n2 Send BlockAnnouncement -\n1 Recv Block ab 20\n" ≡ "accepted (6 events, 3 sessions)"
mixed = refl

-- A notification on an idle session cannot consume another session's request.
isolation : False (S.check 4 (S.notify client ∷ S.notify client ∷ [])
            (inj₁ (Send , RequestNext) ∷ inj₂ (inj₁ (Recv , Votes [])) ∷ []))
isolation = tt

-- Cross-protocol payloads are parse errors, not accidentally routed events.
wrong-protocol : report 4 "sessions fetch:client notify:client\n1 Send BlockRequest ab 7\n" ≡ "parse error at line 2: 1 Send BlockRequest ab 7"
wrong-protocol = refl

-- Undeclared numerical ids cannot escape the finite manifest.
unknown-tag : report 4 "sessions notify:client\n1 Send RequestNext\n" ≡ "parse error at line 2: 1 Send RequestNext"
unknown-tag = refl

-- The legacy bare-role manifest retains its Fetch interpretation.
legacy : report 4 "sessions client\n0 Send BlockRequest ab 7\n" ≡ "accepted (1 events, 1 sessions)"
legacy = refl

-- Standalone Notify input uses the established role-header format.
standalone : reportNotify "role client\nSend RequestNext\nRecv Votes -\nSend Done\n" ≡ "accepted (3 events, 1 sessions)"
standalone = refl

-- The first rejected GLOBAL event reports its own generation and prior state.
first-rejection : report 4 "sessions notify:client fetch:client\n0 Send RequestNext\n1 Send Done\n0 Send Done\n" ≡
  "rejected at index 3 (session 0): Send Done\nmodel session state after 2 events: notify client open, outstanding 1"
first-rejection = refl

-- Exact parsing retains vote metadata and announcement fields.
parse-votes : P.parseEvent "Recv Votes ab:2,cd:4" ≡ just (Recv , Votes ((171 , 2) ∷ (205 , 4) ∷ []))
parse-votes = refl

-- Announcement logs may omit EB metadata only as a complete absence.
parse-announcement : P.parseEvent "Recv BlockAnnouncement ab 4 10" ≡ just (Recv , BlockAnnouncement (just (171 , 4 , 10)))
parse-announcement = refl

-- Incomplete metadata is rejected, rather than silently discarded.
malformed : P.parseEvent "Recv BlockAnnouncement ab 4" ≡ nothing
malformed = refl

-- Delimiters may not silently discard missing vote entries or fields.
malformed-votes : P.parseEvent "Recv Votes ab::2" ≡ nothing
malformed-votes = refl

-- An empty vote item is not the explicit empty-list marker.
missing-vote : P.parseEvent "Recv Votes ab:2,,cd:4" ≡ nothing
missing-vote = refl

-- Original namespaces identify protocol, direction and kind on every row.
namespaced-mixed : report 4 "sessions notify:client fetch:client\n0 LeiosNotify.Remote.Send.NotificationRequestNext\n1 LeiosFetch.Remote.Send.BlockRequest ab 3\n0 LeiosNotify.Remote.Receive.Votes -\n1 LeiosFetch.Remote.Receive.Block ab 20\n" ≡ "accepted (4 events, 2 sessions)"
namespaced-mixed = refl

-- A namespace cannot contradict the manifest protocol, even for shared Done.
namespace-mismatch : report 4 "sessions notify:client\n0 LeiosFetch.Remote.Send.Done\n" ≡ "parse error at line 2: 0 LeiosFetch.Remote.Send.Done"
namespace-mismatch = refl
