{-# OPTIONS --guardedness #-}

-- Two positive derivations by explicit LTS steps (trace-replay Phase 5,
-- Increment 0): one server cycle of `serverModel [7]` and a depth-2 client
-- pipeline of `pipe 2`, each with the `Obs` equation against its log-level
-- trace.  Non-vacuity checks for the bridge statements, nothing more.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.BridgeSanity where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees using (PTree; ExtI)
open import Cardano_network.Base using (lo; N2N_LeiosFetch; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Net replayParams
  using ( Net_Api; Net_Api-≟; input; output; apiLP
        ; lfpSendBlockRequest; lfpRecvBlock; lfpReqBlockRequest; lfpSendBlock )
open import Cardano_network.Data replayParams
  using (Payload; leiosFetchP; MsgLFPBlockRequest; MsgLFPBlock)
import Cardano_network.LeiosFetchP replayParams as LFP
open import Cardano_network.LeiosFetchPipe replayParams using (pipe)
open import Cardano_network.Replay.BridgeServer
  using (Proc; nS; lS; dS; serverModel; getBodyEvS; storeES)
open import Cardano_network.Replay.Obs using (ObsS; ObsC)
open import Cardano_network.Replay.LeiosFetchSession
  using (E; Send; Recv; MsgLeiosBlockRequest; MsgLeiosBlock)

import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as LS
import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} as DS
import Semantics.LTS {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as LC
import Semantics.Deadlock {E = LFP.LFPEv} {I = ExtI LFP.LFPEv} as DC
open import CSP.Laws.Traces.TraceLawsParallel (Net_Api-≟ {Payload}) using (Par-τ-L)
open import Cardano_network.ApiAlphabet replayParams using (apiES)

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
