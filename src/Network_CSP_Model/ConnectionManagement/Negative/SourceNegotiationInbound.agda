{-# OPTIONS --guardedness #-}

-- Concrete V15 offers and explicit mkHandlers TxSubmissionLogicV2 argument.
module ConnectionManagement.Negative.SourceNegotiationInbound where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Negative.InboundConfiguredWitness as Run
import ConnectionManagement.SourceInputs.Negotiation as Source
open import ConnectionManagement.SourceInputs.Schedule using (at; replace; replace-same)
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.ProtocolContracts2 as C2
open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong)

accepted-data : Source.negotiate Source.localOffer Source.localOffer ≡ just Source.localData
accepted-data = Source.inbound-accepted
input : B.Action
input = B.run (server (E.run (mux (U.negotiate A.child₀ Source.layout
  (Source.flow Source.localData)))))
input-position : at 9 Run.schedule ≡ just input
input-position = refl
negotiatedSchedule : List B.Action
negotiatedSchedule = replace 9 input Run.schedule
negotiated-exact : negotiatedSchedule ≡ Run.schedule
negotiated-exact = replace-same 9 input Run.schedule input-position

-- Source mkHandlers logicV2 takes the Right/API branch, not the V1 reader.
txInput : B.Action
txInput = B.contract2 (C2.start (Source.serverEndpoint Source.configuredLogic))
tx-position : at 141 negotiatedSchedule ≡ just txInput
tx-position = refl
schedule : List B.Action
schedule = replace 141 txInput negotiatedSchedule
schedule-exact : schedule ≡ Run.schedule
schedule-exact = trans (replace-same 141 txInput negotiatedSchedule tx-position) negotiated-exact

abstract
  initialized-contracts : B.Runs (B.initial initial A.child₀ (ident 0)) schedule Run.endpoint
  initialized-contracts = subst (λ xs → B.Runs (B.initial initial A.child₀ (ident 0)) xs Run.endpoint)
    (sym schedule-exact) Run.initialized-contracts
  initialized-frontend : V.Runs initial (B.erase schedule) (B.runtime Run.endpoint)
  initialized-frontend = B.project initialized-contracts
