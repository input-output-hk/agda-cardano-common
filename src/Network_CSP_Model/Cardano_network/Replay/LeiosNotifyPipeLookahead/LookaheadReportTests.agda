{-# OPTIONS --guardedness #-}

-- User-facing reports distinguish protocol, grammar, agency and source-coordinate failures.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReportTests where

open import Data.String using (String; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LookaheadReport as R
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
import Cardano_network.LeiosNotifyPipe exactParams as Payloads
import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification as S

-- An early local reply is legal as a prefix because its Request Send hook may be pending.
early-client : R.status (R.local S.nodeNext Log.client "role client\nRecv BlockOffer 2a 7 3\n") ≡ R.acceptedPrefix
early-client = refl

-- Node-next does not permit a pre-Quit Canceled callback on the server.
node-cancel : R.status (R.local S.nodeNext Log.server "role server\nRecv RequestNext\nSend Canceled\n") ≡ R.protocolRejected
node-cancel = refl

-- The explicit generic server contract admits that same finite prefix.
generic-cancel : R.status (R.local S.genericNext Log.server "role server\nRecv RequestNext\nSend Canceled\n") ≡ R.acceptedPrefix
generic-cancel = refl

-- Malformed retained numbers cannot be erased and reinterpreted as protocol events.
malformed-number : R.status (R.local S.nodeNext Log.server "role server\nSend BlockOffer xyz 7 3\n") ≡ R.invalidInput
malformed-number = refl

-- Declared mode and role header disagreement fails before checking any trace.
wrong-role : R.status (R.local S.nodeNext Log.client "role server\n") ≡ R.invalidInput
wrong-role = refl

-- The existing paired syntax retains original positive line numbers and distinct endpoint identities.
pairHeader : String
pairHeader = "pair LeiosNotifyP AB session0\nclient A clientConn 0 fresh client.log\nserver B serverConn 0 fresh server.log\n"

-- Empty supplied endpoint prefixes need no fabricated request or successful-close claim.
empty-pair : R.status (R.paired S.nodeNext pairHeader) ≡ R.acceptedPrefix
empty-pair = refl

-- Both local role validators remain active when pairing otherwise well-formed summaries.
wrong-paired-agency : R.status (R.paired S.nodeNext (pairHeader ++ "client 123 Recv RequestNext\n")) ≡ R.invalidInput
wrong-paired-agency = refl

-- Agency failure reports the original endpoint line, not the normalized pair-file row.
original-coordinate : R.detail (R.paired S.nodeNext (pairHeader ++ "client 123 Recv RequestNext\n")) ≡
  R.profile S.nodeNext ++ "\nconnection=AB; session=session0\nclient source client.log line 123: wrong agency: Recv RequestNext"
original-coordinate = refl

-- A missing paired endpoint declaration is an input failure rather than protocol rejection.
missing-endpoint : R.status (R.paired S.nodeNext "pair LeiosNotifyP AB session0\n") ≡ R.invalidInput
missing-endpoint = refl
