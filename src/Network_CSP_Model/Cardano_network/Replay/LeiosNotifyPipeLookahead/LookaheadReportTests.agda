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

-- The new inconclusive tag is printed exactly as the external runner expects.
undetermined-tag : R.showStatus R.undetermined ≡ "undetermined"
undetermined-tag = refl

-- Graceful node-next server shutdown with every RequestNext row silenced, in the normalized grammar.
silencedServer : String
silencedServer = "role server\nSend BlockAnnouncement -\nRecv Quit\nSend Canceled\nSend Done\n"

-- The silenced local server language accepts the graceful shutdown prefix.
silenced-server-graceful : R.status (R.localSilenced S.nodeNext Log.server silencedServer) ≡ R.acceptedPrefix
silenced-server-graceful = refl

-- The silenced verdict names its own observation profile, not the full driver-log profile.
silenced-server-detail : R.detail (R.localSilenced S.nodeNext Log.server silencedServer) ≡
  "observation=driver-log-no-request-votes; hidden=RequestNext,Votes; client=generic-successful; return=unit; server-contract=node-next\ninitial=fresh (asserted); eof=prefix; fields=normalized summaries\nsilenced local server prefix (4 events)"
silenced-server-detail = refl

-- The same rows with a present RequestNext are invalid input under the silenced profile.
silencedServerWithRequest : String
silencedServerWithRequest = "role server\nRecv RequestNext\nSend BlockAnnouncement -\nRecv Quit\nSend Canceled\nSend Done\n"

-- A present hidden-kind row is never erased: it is reported as invalid input.
silenced-request-present : R.status (R.localSilenced S.nodeNext Log.server silencedServerWithRequest) ≡ R.invalidInput
silenced-request-present = refl

-- The invalid row is located at its normalized input line with the silenced reason.
silenced-request-detail : R.detail (R.localSilenced S.nodeNext Log.server silencedServerWithRequest) ≡
  R.silencedProfile S.nodeNext ++ "\ninput line 2: silenced kind present: RequestNext/Votes"
silenced-request-detail = refl

-- A present server Votes row is invalid input at its normalized line, through the full report path.
silenced-votes-present : R.detail (R.localSilenced S.genericNext Log.server "role server\nSend Canceled\nSend Votes -\n") ≡
  R.silencedProfile S.genericNext ++ "\ninput line 3: silenced kind present: RequestNext/Votes"
silenced-votes-present = refl

-- Done before Quit is outside the client's silenced language.
silenced-client-rejected : R.status (R.localSilenced S.nodeNext Log.client "role client\nRecv Done\n") ≡ R.protocolRejected
silenced-client-rejected = refl

-- The silenced mode keeps the existing role-header validation.
silenced-wrong-role : R.status (R.localSilenced S.nodeNext Log.client "role server\n") ≡ R.invalidInput
silenced-wrong-role = refl

-- Visible replies in opposite FIFO orders: each endpoint alone is a generic-next silenced log.
fifoSwap : String
fifoSwap = pairHeader ++ "client 11 Recv BlockAnnouncement -\nclient 13 Recv Canceled\n" ++
  "server 17 Send Canceled\nserver 19 Send BlockAnnouncement -\n"

-- Both locals accept but the canonical reconstruction is refuted: undetermined, never a rejection.
silenced-paired-fifo-swap : R.status (R.pairedSilenced S.genericNext fifoSwap) ≡ R.undetermined
silenced-paired-fifo-swap = refl

-- A graceful silenced pair is accepted.
silenced-paired-graceful : R.status (R.pairedSilenced S.nodeNext (pairHeader ++
  "client 11 Recv BlockAnnouncement -\nclient 13 Send Quit\nclient 15 Recv Canceled\nclient 17 Recv Done\n" ++
  "server 21 Send BlockAnnouncement -\nserver 23 Recv Quit\nserver 25 Send Canceled\nserver 27 Send Done\n")) ≡ R.acceptedPrefix
silenced-paired-graceful = refl

-- A local silenced failure is a certified paired rejection.
silenced-paired-rejected : R.status (R.pairedSilenced S.nodeNext (pairHeader ++ "client 11 Recv Done\n")) ≡ R.protocolRejected
silenced-paired-rejected = refl

-- A present server RequestNext keeps its original source coordinate in the diagnostic.
silenced-paired-request-present : R.detail (R.pairedSilenced S.nodeNext (pairHeader ++ "server 123 Recv RequestNext\n")) ≡
  R.silencedProfile S.nodeNext ++ "\nconnection=AB; session=session0\nserver source server.log line 123: silenced kind present: RequestNext/Votes"
silenced-paired-request-present = refl
