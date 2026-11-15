{-# OPTIONS --guardedness #-}

-- Complete source-policy execution; existing reduced-60 statements are unchanged.
module ConnectionManagement.SourceInputs.SourcePolicyInbound where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport using (module B)
import ConnectionManagement.Negative.InboundConfiguredWitness as Reduced
import ConnectionManagement.SourceInputs.Policy as Policy
import ConnectionManagement.SourceInputs.SourcePolicyInbound0 as P0
import ConnectionManagement.SourceInputs.SourcePolicyInbound1 as P1
import ConnectionManagement.SourceInputs.SourcePolicyInbound2 as P2
import ConnectionManagement.SourceInputs.SourcePolicyInbound3 as P3
import ConnectionManagement.SourceInputs.SourcePolicyInbound4 as P4
import ConnectionManagement.SourceInputs.SourcePolicyInbound5 as P5
import ConnectionManagement.SourceInputs.SourcePolicyInbound6 as P6
import ConnectionManagement.SourceInputs.SourcePolicyInbound7 as P7
import ConnectionManagement.SourceInputs.SourcePolicyInbound8 as P8
import ConnectionManagement.SourceInputs.SourcePolicyInbound9 as P9
import ConnectionManagement.SourceInputs.SourcePolicyInbound10 as P10
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
schedule : List B.Action
schedule = Reduced.schedule
import ConnectionManagement.Scenarios.Admission as A
start : B.State
start = B.initial Policy.source120 A.child₀ (ident 0)
endpoint : B.State
endpoint = configure Reduced.endpoint

abstract
  initialized-contracts : B.Runs start schedule endpoint
  initialized-contracts = B.append P0.path0 (B.append P0.path1 (B.append P0.path2 (B.append P0.path3 (B.append P0.path4 (B.append P0.path5 (B.append P0.path6 (B.append P0.path7 (B.append P1.path8 (B.append P1.path9 (B.append P1.path10 (B.append P1.path11 (B.append P1.path12 (B.append P1.path13 (B.append P1.path14 (B.append P1.path15 (B.append P2.path16 (B.append P2.path17 (B.append P2.path18 (B.append P2.path19 (B.append P2.path20 (B.append P2.path21 (B.append P2.path22 (B.append P2.path23 (B.append P3.path24 (B.append P3.path25 (B.append P3.path26 (B.append P3.path27 (B.append P3.path28 (B.append P3.path29 (B.append P3.path30 (B.append P3.path31 (B.append P3.path32 (B.append P4.path33 (B.append P4.path34 (B.append P4.path35 (B.append P4.path36 (B.append P4.path37 (B.append P4.path38 (B.append P4.path39 (B.append P4.path40 (B.append P4.path41 (B.append P5.path42 (B.append P5.path43 (B.append P5.path44 (B.append P5.path45 (B.append P5.path46 (B.append P5.path47 (B.append P5.path48 (B.append P5.path49 (B.append P6.path50 (B.append P6.path51 (B.append P6.path52 (B.append P6.path53 (B.append P6.path54 (B.append P6.path55 (B.append P6.path56 (B.append P6.path57 (B.append P6.path58 (B.append P7.path59 (B.append P7.path60 (B.append P7.path61 (B.append P7.path62 (B.append P7.path63 (B.append P7.path64 (B.append P7.path65 (B.append P7.path66 (B.append P8.path67 (B.append P8.path68 (B.append P8.path69 (B.append P8.path70 (B.append P8.path71 (B.append P8.path72 (B.append P8.path73 (B.append P8.path74 (B.append P9.path75 (B.append P9.path76 (B.append P9.path77 (B.append P9.path78 (B.append P9.path79 (B.append P9.path80 (B.append P9.path81 (B.append P9.path82 (B.append P10.path83 (P10.path84))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  initialized-frontend : V.Runs Policy.source120 (B.erase schedule) (B.runtime endpoint)
  initialized-frontend = B.project initialized-contracts

-- The derived V15 duplex input and independently selected Tx V2 caller input
-- remain the actual inputs of the source-120 responder execution.
import ConnectionManagement.Negative.SourceNegotiationInbound as Offers
negotiated-schedule : Offers.schedule ≡ schedule
negotiated-schedule = Offers.schedule-exact
