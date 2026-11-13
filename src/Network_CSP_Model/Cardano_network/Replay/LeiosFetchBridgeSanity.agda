{-# OPTIONS --guardedness #-}

-- Positive derivations by explicit LTS steps (trace-replay Phase 5,
-- Increment 0): one server cycle of `serverModel [7]` and a depth-2 client
-- pipeline of `pipe 2`, plus stop-and-drain and counted-observation tests.
-- Non-vacuity checks for the model bridge statements, not upstream conformance.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchBridgeSanity where

import Data.Bool
import Cardano_network.Replay.LeiosFetchWords

open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (_≤?_)
open import Data.Empty using (⊥-elim)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Data.Unit using (⊤; tt)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; mapMaybe; length; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; Σ-syntax; ∃-syntax)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Data.List.Properties using (length-replicate)

open import Process_Trees using (PTree; ExtI; fin)
open import Level using (lift)
open import Cardano_network.Base using (lo; N2N_LeiosFetch; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using ( Net_Api; Net_Api-≟; input; output; apiLP
        ; lfpSendBlockRequest; lfpRecvBlock; lfpReqBlockRequest; lfpSendBlock
        ; lfpSendBlockTxsRequest; lfpReqBlockTxsRequest; lfpRecvBlockTxs )
open import Cardano_network.Data replayParams
  using (Payload; leiosFetchP; MsgLFPBlockRequest; MsgLFPBlock; MsgLFPBlockTxsRequest; MsgLFPBlockTxs)
import Cardano_network.LeiosFetchP replayParams as LFP
open import Cardano_network.LeiosFetchPipe replayParams using (pipe; pipeV; txs; drainTxsV)
open import Cardano_network.Replay.LeiosFetchServerModel
  using (Proc; nS; lS; dS; serverModel; getBodyEvS; storeES)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireOK; WireMsg; accepted-wire)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Cardano_network.Replay.LeiosFetchObs using (ObsS; ObsC; clsS; clsC; txsReq♭; txs♭; _≈♭_)
open import Cardano_network.Replay.LeiosFetchSession
  using (E; Send; Recv; client₀; server₀; MsgLeiosBlockRequest; MsgLeiosBlock
        ; MsgLeiosBlockTxsRequest; MsgLeiosBlockTxs; MsgLeiosDone; module Spec)

import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as LS
import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DS
import Semantics.LTS {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as LC
import Semantics.Deadlock {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as DC
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload}) using (Par-τ-L)
open import Cardano_network.ApiAlphabet replayParams using (apiES)

import Cardano_network.Replay.LeiosFetchServerSound 2 as SS
import Cardano_network.Replay.LeiosFetchServerComplete 2 as SB
import Cardano_network.Replay.LeiosFetchClientBridge 2 fzero lo as CB
open import Cardano_network.Replay.LeiosFetchDecide using (module Cert)
open Cert 2 using (hasTrace?; client-cert; server-cert; rejectionReason)
open import Semantics.Replay using (module Traces)
open Spec 2 using (leiosFetch)
open Traces leiosFetch using (HasTrace)

------------------------------------------------------------------------
-- Server: Recv BlockRequest 7 1, serve from the store, Send Block 7
------------------------------------------------------------------------

-- the server's model trace: wire request, api report, store read, api reply, wire reply
srvTrace : List LS.Event
srvTrace =
    LS.evLabel Payload (output lS dS N2N_LeiosFetch)
      (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockRequest (7 , 1)))
  ∷ LS.evLabel (ℕ × ℕ) (apiLP lS dS lfpReqBlockRequest) (7 , 1)
  ∷ LS.evLabel ℕ (getBodyEvS 7) 7
  ∷ LS.evLabel ℕ (apiLP lS dS lfpSendBlock) 7
  ∷ LS.evLabel Payload (input lS dS N2N_LeiosFetch)
      (tt , FromResponder , tt , leiosFetchP (MsgLFPBlock 7))
  ∷ []

-- the log-level trace it should be observed as
srvLog : List E
srvLog = (Recv , MsgLeiosBlockRequest 7 1) ∷ (Send , MsgLeiosBlock 7 0) ∷ []

-- the run: two visible steps, the producer's loop-back τ, three visible steps
srvRun : Σ[ M ∈ Proc ] serverModel (7 ∷ []) DS.⟹∖√⟨ srvTrace ⟩ M
srvRun = _ ,
  DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-τ (Par-τ-L storeES _ _ _ (Par-τ-L apiES _ _ _ (LS.sSil refl)))
  (DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl)
   DS.∖√-refl)))))

-- what the log sees of that run
srvObs : ObsS srvTrace srvLog
srvObs = refl

------------------------------------------------------------------------
-- Client: two pipelined BlockRequests, then the two Blocks in order
------------------------------------------------------------------------

-- the application asks for `(h , 0)`
cAsk : ℕ → LC.Event
cAsk h = LC.evLabel (ℕ × ℕ) (LFP.apiLPev fzero lo lfpSendBlockRequest) (h , 0)

-- the client sends BlockRequest `(h , 0)`
cReq : ℕ → LC.Event
cReq h = LC.evLabel Payload (LFP.sendLFP fzero lo)
           (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockRequest (h , 0)))

-- the client receives Block `h`
cBlk : ℕ → LC.Event
cBlk h = LC.evLabel Payload (LFP.receiveLFP fzero lo)
           (tt , FromResponder , tt , leiosFetchP (MsgLFPBlock h))

-- the client hands Block `h` to the application
cDel : ℕ → LC.Event
cDel h = LC.evLabel ℕ (LFP.apiLPev fzero lo lfpRecvBlock) h

-- the client's model trace
cliTrace : List LC.Event
cliTrace = cAsk 1 ∷ cReq 1 ∷ cAsk 2 ∷ cReq 2 ∷ cBlk 1 ∷ cDel 1 ∷ cBlk 2 ∷ cDel 2 ∷ []

-- the log-level trace it should be observed as
cliLog : List E
cliLog = (Send , MsgLeiosBlockRequest 1 0) ∷ (Send , MsgLeiosBlockRequest 2 0)
       ∷ (Recv , MsgLeiosBlock 1 0) ∷ (Recv , MsgLeiosBlock 2 0) ∷ []

-- the run: each round is two visible steps then the loop-back τ
cliRun : Σ[ M ∈ PTree LFP.LFPEv (ExtI LFP.LFPEv) LFP.Rr ] pipe 2 fzero lo DC.⟹∖√⟨ cliTrace ⟩ M
cliRun = _ ,
  DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl)
   DC.∖√-refl))))))))))

-- what the log sees of that run
cliObs : ObsC cliTrace cliLog
cliObs = refl

------------------------------------------------------------------------
-- Stop-and-drain: the replay skips the hash check after a silent stop.
------------------------------------------------------------------------

-- A draining client receives a mismatching Block and does not deliver it to the application.
drainTrace : List LC.Event
drainTrace = cAsk 1 ∷ cReq 1 ∷ cBlk 2 ∷ []

-- The mismatch is retained by the observation; completeness must reproduce it.
drainLog : List E
drainLog = (Send , MsgLeiosBlockRequest 1 0) ∷ (Recv , MsgLeiosBlock 2 0) ∷ []

-- A silent stop after the request enables draining the mismatching Block.
drainRun : Σ[ M ∈ PTree LFP.LFPEv (ExtI LFP.LFPEv) LFP.Rr ] pipe 2 fzero lo DC.⟹∖√⟨ drainTrace ⟩ M
drainRun = _ ,
  DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl)
  (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-τ (LC.sTau {i = _ , fin {n = 1}} {a = lift fzero} refl refl)
  (DC.∖√-ev (LC.sVis refl refl) DC.∖√-refl))))

-- Draining preserves the received Block's actual hash in the log.
drainObs : ObsC drainTrace drainLog
drainObs = refl

-- Soundness accepts this particular counted, wire-admissible server log.
srvSound : HasTrace server₀ srvLog
srvSound with srvRun
... | M , run = SS.server-sound (7 ∷ []) run srvObs (tt ∷ tt ∷ [])

-- The same conditional soundness holds for the client log.
cliSound : HasTrace client₀ cliLog
cliSound with cliRun
... | M , run = CB.client-sound run cliObs (tt ∷ tt ∷ Data.Nat.z≤n ∷ Data.Nat.z≤n ∷ [])

-- Draining's wrong-hash log is accepted by the replay, as required for completeness.
drainAccepted : HasTrace client₀ drainLog
drainAccepted = toWitness {a? = hasTrace? client-cert drainLog} tt

-- A transaction cycle with one requested bit exercises nonzero spec counts.
txClientLog : List E
txClientLog = (Send , MsgLeiosBlockTxsRequest 7 1 1 ((0 , 1) ∷ []))
            ∷ (Recv , MsgLeiosBlockTxs 1 0) ∷ (Send , MsgLeiosDone) ∷ []

-- Both the bitmap validity and the nonzero reply count are checked in this trace.
txClientAccepted : HasTrace client₀ txClientLog
txClientAccepted = toWitness {a? = hasTrace? client-cert txClientLog} tt

-- Completeness realizes the nonzero count in the model observation.
txClientModel : ∃[ t ] ∃[ M ] (pipe 2 fzero lo DC.⟹∖√⟨ t ⟩ M × ObsC t txClientLog)
txClientModel = CB.client-complete txClientAccepted

-- The same nonzero transaction exchange, observed from the server side.
txServerLog : List E
txServerLog = (Recv , MsgLeiosBlockTxsRequest 7 1 1 ((0 , 1) ∷ []))
            ∷ (Send , MsgLeiosBlockTxs 1 0) ∷ (Recv , MsgLeiosDone) ∷ []

-- The server trace checks the request bitmap and positional reply count.
txServerAccepted : HasTrace server₀ txServerLog
txServerAccepted = toWitness {a? = hasTrace? server-cert txServerLog} tt

-- The existential-store bridge realizes a nonzero-count server trace.
txServerModel : ∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs DS.⟹∖√⟨ t ⟩ M × ObsS t txServerLog)
txServerModel = Data.Product.proj₂ (Equivalence.to (SB.server-bridge {es = txServerLog}) txServerAccepted)

-- An inconsistent request count is representable as a log, but is rejected by the spec.
badCountLog : List E
badCountLog = (Send , MsgLeiosBlockTxsRequest 7 1 2 [])
            ∷ (Recv , MsgLeiosBlockTxs 2 0) ∷ (Send , MsgLeiosDone) ∷ []

-- The replay rejects a request count inconsistent with its empty bitmap.
badCountRejected : ¬ HasTrace client₀ badCountLog
badCountRejected = toWitnessFalse {a? = hasTrace? client-cert badCountLog} tt

-- Distinct transaction counts now produce distinct observations.
badCountDifferentObservation : ¬ (txClientLog ≈♭ badCountLog)
badCountDifferentObservation ()

------------------------------------------------------------------------
-- Positional transaction replies: check counts before delivering offsets.
------------------------------------------------------------------------

-- The application requests the exact two offsets used by the count regressions.
pipeTxAsk : LC.Event
pipeTxAsk = LC.evLabel _ (LFP.apiLPev fzero lo lfpSendBlockTxsRequest)
  ((7 , 1) , 3 ∷ 5 ∷ [])

-- The pipe sends the stored point and bitmap on the wire.
pipeTxReq : LC.Event
pipeTxReq = LC.evLabel Payload (LFP.sendLFP fzero lo)
  (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockTxsRequest (7 , 1) (3 ∷ 5 ∷ [])))

-- A positional wire reply contains transactions alone.
pipeTxReply : List ⊤ → LC.Event
pipeTxReply ts = LC.evLabel Payload (LFP.receiveLFP fzero lo)
  (tt , FromResponder , tt , leiosFetchP (MsgLFPBlockTxs ts))

-- Matching counts deliver the transactions paired with the stored offsets.
pipeCountTrace : List LC.Event
pipeCountTrace = pipeTxAsk ∷ pipeTxReq ∷ pipeTxReply (tt ∷ tt ∷ []) ∷
  LC.evLabel _ (LFP.apiLPev fzero lo lfpRecvBlockTxs)
    ((7 , 1) , (3 , tt) ∷ (5 , tt) ∷ []) ∷ []

-- The actual checking run and its observation retain the request point and reply kind.
pipeCountMatch : (Σ[ M ∈ PTree LFP.LFPEv (ExtI LFP.LFPEv) LFP.Rr ]
  pipe 2 fzero lo DC.⟹∖√⟨ pipeCountTrace ⟩ M) ×
  (mapMaybe clsC pipeCountTrace ≡ (Send , txsReq♭ 7 1 2 (3 ∷ 5 ∷ []) Data.Bool.true) ∷ (Recv , txs♭ 2) ∷ [])
pipeCountMatch = (_ ,
  DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl)
  (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl) DC.∖√-refl))))) , refl

-- A one-transaction reply is absent from the checking head's visible map.
pipeCountMismatchRefused : pipeV 2 fzero lo (txs (7 , 1) (3 ∷ 5 ∷ []) ∷ [])
  (_ , LFP.receiveLFP fzero lo)
  (tt , FromResponder , tt , leiosFetchP (MsgLFPBlockTxs (tt ∷ []))) ≡ nothing
pipeCountMismatchRefused = refl

-- The same two-offset request can drain a reply with seven transactions after stop.
drainAnyCount : Σ[ M ∈ PTree LFP.LFPEv (ExtI LFP.LFPEv) LFP.Rr ]
  pipe 2 fzero lo DC.⟹∖√⟨ pipeTxAsk ∷ pipeTxReq ∷
    pipeTxReply (tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ tt ∷ []) ∷ [] ⟩ M
drainAnyCount = _ ,
  DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl)
  (DC.∖√-τ (LC.sSil refl)
  (DC.∖√-τ (LC.sTau {i = _ , fin {n = 1}} {a = lift fzero} refl refl)
  (DC.∖√-ev (LC.sVis refl refl) DC.∖√-refl))))

------------------------------------------------------------------------
-- Unknown EB: the negative read stops the serving thread.
------------------------------------------------------------------------

import Cardano_network.Replay.LeiosFetchServerParts as SP
import Cardano_network.Replay.LeiosFetchServerRel 2 as SR
import CSP.Operators (Net_Api-≟ {Payload}) as Op
open import Cardano_network.Net replayParams using (store; stLacksBody)
open import Cardano_network.Replay.LeiosFetchSession using (sThrown)

-- The unheld body is requested, reported, then rejected by the store.
unknownTrace : List LS.Event
unknownTrace =
    LS.evLabel Payload (output lS dS N2N_LeiosFetch)
      (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockRequest (7 , 1)))
  ∷ LS.evLabel (ℕ × ℕ) (apiLP lS dS lfpReqBlockRequest) (7 , 1)
  ∷ LS.evLabel ⊤ (store lS lo (stLacksBody 7)) tt
  ∷ []

-- The concrete model reaches a visibly stuck state related to the spec's throw.
unknownEBThrows : Σ[ M ∈ Proc ]
  (serverModel [] DS.⟹∖√⟨ unknownTrace ⟩ M ×
   (∀ {e M′} → ¬ (M LS.─[ LS.ev (LS.evl e) ]─► M′)) × SR.Rel [] M sThrown)
unknownEBThrows = _ ,
  DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl) DS.∖√-refl)) ,
  SR.thrownB-no-ev SP.pBack SP.eHead (SP.sMid SP.drains-ret) ,
  SR.rThrownB SP.pBack SP.eHead (SP.sMid SP.drains-ret)

-- A held EB's nonempty request now proceeds to the transaction-store read.
heldOffsetTrace : List LS.Event
heldOffsetTrace =
    LS.evLabel Payload (output lS dS N2N_LeiosFetch)
      (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockTxsRequest (7 , 1) (0 ∷ [])))
  ∷ LS.evLabel _ (apiLP lS dS lfpReqBlockTxsRequest) ((7 , 1) , 0 ∷ [])
  ∷ LS.evLabel ℕ (getBodyEvS 7) 7 ∷ []

-- The decoder-sized table and held unit tx keep the counted service reachable.
heldOffsetRun : Σ[ M ∈ Proc ] serverModel (7 ∷ []) DS.⟹∖√⟨ heldOffsetTrace ⟩ M
heldOffsetRun = _ , DS.∖√-ev (LS.sVis refl refl)
  (DS.∖√-ev (LS.sVis refl refl) (DS.∖√-ev (LS.sVis refl refl) DS.∖√-refl))

-- The pipe refuses a duplicate-offset request before putting it on the wire.
pipeRefusesNonCanonical : pipeV 2 fzero lo []
  (_ , LFP.apiLPev fzero lo lfpSendBlockTxsRequest) ((7 , 1) , 3 ∷ 3 ∷ []) ≡ nothing
pipeRefusesNonCanonical = refl

-- The pipe also refuses descending offsets before sending a request.
pipeRefusesDescending : pipeV 2 fzero lo []
  (_ , LFP.apiLPev fzero lo lfpSendBlockTxsRequest) ((7 , 1) , 5 ∷ 3 ∷ []) ≡ nothing
pipeRefusesDescending = refl

-- The first offset beyond the honest client cap is unavailable to the pipe sender.
pipeRefusesOutOfRange : pipeV 2 fzero lo []
  (_ , LFP.apiLPev fzero lo lfpSendBlockTxsRequest) ((7 , 1) , 17142 ∷ []) ≡ nothing
pipeRefusesOutOfRange = refl

import CSP.Operators {E = LFP.LFPEv} LFP.LFPEv-≟ as POp

-- State the overflow test by length to avoid reducing the replicated reply.
drainOverflow : ∀ ts → length ts ≡ 17143 → drainTxsV fzero lo POp.Stop
  (_ , LFP.receiveLFP fzero lo)
  (tt , FromResponder , tt , leiosFetchP (MsgLFPBlockTxs ts)) ≡ nothing
drainOverflow ts len with length ts ≤? maxTxs
... | Relation.Nullary.no _ = refl
... | Relation.Nullary.yes cap = ⊥-elim
  (toWitnessFalse {a? = 17143 ≤? maxTxs} tt (subst (_≤ maxTxs) len cap))

-- A draining pipe cannot consume an oversized wire reply either.
pipeDrainRefusesOverCap : drainTxsV fzero lo POp.Stop
  (_ , LFP.receiveLFP fzero lo)
  (tt , FromResponder , tt , leiosFetchP (MsgLFPBlockTxs (replicate 17143 tt))) ≡ nothing
pipeDrainRefusesOverCap = drainOverflow (replicate 17143 tt) (length-replicate {A = ⊤} 17143 {x = tt})

-- Counted observation retains both transactions in the pipe regression.
countedTwo : mapMaybe clsC pipeCountTrace ≡
  (Send , txsReq♭ 7 1 2 (3 ∷ 5 ∷ []) Data.Bool.true) ∷ (Recv , txs♭ 2) ∷ []
countedTwo = refl

-- Two requested offsets and two reply transactions are accepted with their counts.
countedTwoLog : List E
countedTwoLog = (Send , MsgLeiosBlockTxsRequest 7 1 2 (Cardano_network.Replay.LeiosFetchWords.toWords (3 ∷ 5 ∷ []))) ∷
  (Recv , MsgLeiosBlockTxs 2 0) ∷ []

-- The explicit pipe run realizes this accepted counted exchange.
countedTwoObservation : ObsC pipeCountTrace countedTwoLog
countedTwoObservation = refl

-- The replay checks the same two request and reply counts.
countedTwoAccepted : HasTrace client₀ countedTwoLog
countedTwoAccepted = toWitness {a? = hasTrace? client-cert countedTwoLog} tt

-- The empty request and reply retain zero counts rather than erasing them.
emptyCountLog : List E
emptyCountLog = (Send , MsgLeiosBlockTxsRequest 7 1 0 []) ∷ (Recv , MsgLeiosBlockTxs 0 0) ∷ []

-- Empty exchanges remain accepted under the counted spec.
emptyCountAccepted : HasTrace client₀ emptyCountLog
emptyCountAccepted = toWitness {a? = hasTrace? client-cert emptyCountLog} tt

-- A different reply count cannot describe the concrete two-transaction run.
wrongReplyNotObservation : ¬ ObsC pipeCountTrace
  ((Send , MsgLeiosBlockTxsRequest 7 1 2 (Cardano_network.Replay.LeiosFetchWords.toWords (3 ∷ 5 ∷ []))) ∷ (Recv , MsgLeiosBlockTxs 1 0) ∷ [])
wrongReplyNotObservation ()

-- Server encoding may produce a Block above the client's receive-side limit.
oversizedBlockLog : List E
oversizedBlockLog = (Recv , MsgLeiosBlockRequest 7 1) ∷ (Send , MsgLeiosBlock 7 660001) ∷ []

-- The counted server observation permits the oversized send.
oversizedBlockObservation : ObsS srvTrace oversizedBlockLog
oversizedBlockObservation = refl

-- D11 admits the server send without a decoder-size premise.
oversizedBlockAccepted : HasTrace server₀ oversizedBlockLog
oversizedBlockAccepted = toWitness {a? = hasTrace? server-cert oversizedBlockLog} tt

-- Received Blocks still require a byte limit in the bridge premise.
oversizedBlockNotWireOK : ¬ WireOK
  ((Send , MsgLeiosBlockRequest 7 1) ∷ (Recv , MsgLeiosBlock 7 660001) ∷ [])
oversizedBlockNotWireOK (_ ∷ cap ∷ []) = toWitnessFalse {a? = 660001 ≤? 660000} tt cap

import Cardano_network.Replay.LeiosFetchDecideTests as DTests
open import Data.Bool using (T)
open import Cardano_network.Replay.LeiosFetchWire using (validᵇ; popcount)
open Traces leiosFetch using (vis; done)
open Spec 2 using (sRecvTxsReq)

-- The decoder-valid 17150-count request is accepted independently of the client cap.
overCapRequestLog : List E
overCapRequestLog = (Recv , MsgLeiosBlockTxsRequest 1 10 17150 DTests.overCapBitmap) ∷ []

-- Reuse the frozen valid-bitmap and popcount computation gates.
overCapRequestAccepted : HasTrace server₀ overCapRequestLog
overCapRequestAccepted = _ , vis (sRecvTxsReq
  (subst T (Relation.Binary.PropositionalEquality.sym DTests.over-cap-bitmap-valid) tt)
  (Relation.Binary.PropositionalEquality.sym DTests.over-cap-bitmap-count)) done

-- Counted completeness now supplies a model run observing all 17150 requested bits.
overCapRequestObserved : ∃[ bs ] ∃[ t ] ∃[ M ] (serverModel bs DS.⟹∖√⟨ t ⟩ M × ObsS t overCapRequestLog)
overCapRequestObserved = Data.Product.proj₂ (Equivalence.to SB.server-bridge overCapRequestAccepted)

-- The empty exchange's application/wire trace retains both zero counts.
emptyCountTrace : List LC.Event
emptyCountTrace =
  LC.evLabel _ (LFP.apiLPev fzero lo lfpSendBlockTxsRequest) ((7 , 1) , []) ∷
  LC.evLabel Payload (LFP.sendLFP fzero lo)
    (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockTxsRequest (7 , 1) [])) ∷
  pipeTxReply [] ∷ []

-- This is an inhabited checking run, including its request loop-back.
emptyCountRun : ∃[ M ] pipe 2 fzero lo DC.⟹∖√⟨ emptyCountTrace ⟩ M
emptyCountRun = _ , DC.∖√-ev (LC.sVis refl refl) (DC.∖√-ev (LC.sVis refl refl)
  (DC.∖√-τ (LC.sSil refl) (DC.∖√-ev (LC.sVis refl refl) DC.∖√-refl)))

-- Empty observations carry zeros on both messages.
emptyCountObservation : ObsC emptyCountTrace emptyCountLog
emptyCountObservation = refl

-- The same two-transaction exchange is a valid server-role trace.
countedTwoServerLog : List E
countedTwoServerLog = (Recv , MsgLeiosBlockTxsRequest 7 1 2 (Cardano_network.Replay.LeiosFetchWords.toWords (3 ∷ 5 ∷ []))) ∷
  (Send , MsgLeiosBlockTxs 2 0) ∷ []

-- The frozen replay accepts the counted server exchange.
countedTwoServerAccepted : HasTrace server₀ countedTwoServerLog
countedTwoServerAccepted = toWitness {a? = hasTrace? server-cert countedTwoServerLog} tt

-- The extended replay table and store realize a two-transaction server reply.
countedTwoServerObserved : ∃[ bs ] ∃[ t ] ∃[ M ]
  (serverModel bs DS.⟹∖√⟨ t ⟩ M × ObsS t countedTwoServerLog)
countedTwoServerObserved = Data.Product.proj₂ (Equivalence.to SB.server-bridge countedTwoServerAccepted)

-- Decoder-failing receives are dropped before the upstream logging point.
decoderFailureUnlogged : clsS (LS.evLabel Payload (output lS dS N2N_LeiosFetch)
  (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockTxsRequest (7 , 1) (17152 ∷ [])))) ≡ nothing
decoderFailureUnlogged = refl

-- Padding offsets beyond the honest cap remain logged after successful decoding.
decoderPaddingLogged : clsS (LS.evLabel Payload (output lS dS N2N_LeiosFetch)
  (tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockTxsRequest (7 , 1) (17142 ∷ [])))) ≡
  just (Recv , txsReq♭ 7 1 1 (17142 ∷ []) Data.Bool.true)
decoderPaddingLogged = refl

-- Equal counts with different offsets cannot observe the concrete request.
wrongBitmapNotObserved : ¬ ObsC pipeCountTrace
  ((Send , MsgLeiosBlockTxsRequest 7 1 2 ((0 , 3) ∷ [])) ∷
   (Recv , MsgLeiosBlockTxs 2 0) ∷ [])
wrongBitmapNotObserved ()

-- The final decoder padding bit is a valid bitmap but cannot be sent by a client.
paddingClientLog : List E
paddingClientLog = (Send , MsgLeiosBlockTxsRequest 7 1 1 ((267 , 1) ∷ [])) ∷ []

-- Replay rejects padding offsets, matching the pipe's outgoing domain.
paddingClientRejected : ¬ HasTrace client₀ paddingClientLog
paddingClientRejected = toWitnessFalse {a? = hasTrace? client-cert paddingClientLog} tt

-- The rejection identifies the offset cap even though the count is only one.
paddingClientReason : rejectionReason client₀ client₀ paddingClientLog ≡
  "client: request offset exceeds maxTxs at index 1"
paddingClientReason = refl
