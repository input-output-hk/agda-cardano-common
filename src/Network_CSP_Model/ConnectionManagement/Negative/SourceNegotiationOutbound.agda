{-# OPTIONS --guardedness #-}

-- The full initialized outbound run with a source-valid concrete V15 offer.
module ConnectionManagement.Negative.SourceNegotiationOutbound where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.Negative.FullConfiguredWitness as Run
import ConnectionManagement.SourceInputs.Negotiation as Source
open import ConnectionManagement.SourceInputs.Schedule using (at; replace; replace-same)
import ConnectionManagement.CSP.GovernorLifecycle as L
open import Relation.Binary.PropositionalEquality using (subst; sym)

-- Accepted data is obtained from the two explicit offers; the equality checks
-- the source acceptance branch, including magic/query/features and flow.
accepted-data : Source.negotiate Source.localOffer Source.outboundOffer ≡ just Source.remoteOutboundData
accepted-data = Source.outbound-accepted
input : B.Action
input = B.run (server (E.run (mux (U.negotiate L.child Source.layout
  (Source.flow Source.remoteOutboundData)))))
input-position : at 23 Run.schedule ≡ just input
input-position = refl
schedule : List B.Action
schedule = replace 23 input Run.schedule
schedule-exact : schedule ≡ Run.schedule
schedule-exact = replace-same 23 input Run.schedule input-position

abstract
  initialized-contracts : B.Runs Run.start schedule Run.endpoint
  initialized-contracts = subst (λ xs → B.Runs Run.start xs Run.endpoint)
    (sym schedule-exact) Run.initialized-contracts
  initialized-frontend : V.Runs initial (B.erase schedule) (B.runtime Run.endpoint)
  initialized-frontend = B.project initialized-contracts
