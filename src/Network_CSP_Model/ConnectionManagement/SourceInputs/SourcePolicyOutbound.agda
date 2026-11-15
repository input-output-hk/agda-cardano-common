{-# OPTIONS --guardedness #-}

-- Complete source-policy execution; existing reduced-60 statements are unchanged.
module ConnectionManagement.SourceInputs.SourcePolicyOutbound where
open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.Negative.FullConfiguredWitness as Reduced
import ConnectionManagement.SourceInputs.Policy as Policy
import ConnectionManagement.SourceInputs.SourcePolicyOutbound0 as P0
import ConnectionManagement.SourceInputs.SourcePolicyOutbound1 as P1
import ConnectionManagement.SourceInputs.SourcePolicyOutbound2 as P2
import ConnectionManagement.SourceInputs.SourcePolicyOutbound3 as P3
import ConnectionManagement.SourceInputs.SourcePolicyOutbound4 as P4
import ConnectionManagement.SourceInputs.SourcePolicyOutbound5 as P5
import ConnectionManagement.SourceInputs.SourcePolicyOutbound6 as P6
import ConnectionManagement.SourceInputs.SourcePolicyOutbound7 as P7
import ConnectionManagement.SourceInputs.SourcePolicyOutbound8 as P8
import ConnectionManagement.SourceInputs.SourcePolicyOutbound9 as P9
import ConnectionManagement.SourceInputs.SourcePolicyOutbound10 as P10
import ConnectionManagement.SourceInputs.SourcePolicyOutbound11 as P11
import ConnectionManagement.SourceInputs.SourcePolicyOutbound12 as P12
import ConnectionManagement.SourceInputs.SourcePolicyOutbound13 as P13
import ConnectionManagement.SourceInputs.SourcePolicyOutbound14 as P14
import ConnectionManagement.SourceInputs.SourcePolicyOutbound15 as P15
import ConnectionManagement.SourceInputs.SourcePolicyOutbound16 as P16
import ConnectionManagement.SourceInputs.SourcePolicyOutbound17 as P17
configure : B.State → B.State
configure s = record s { runtime = Policy.runtime (B.runtime s) }
schedule : List B.Action
schedule = Reduced.schedule
start : B.State
start = configure Reduced.start
endpoint : B.State
endpoint = configure Reduced.endpoint

abstract
  initialized-contracts : B.Runs start schedule endpoint
  initialized-contracts = B.append P0.path0 ( B.append P1.path1 ( B.append P2.path2 ( B.append P3.path3 ( B.append P4.path4 ( B.append P4.path5 ( B.append P4.path6 ( B.append P5.path7 ( B.append P5.path8 ( B.append P6.path9 ( B.append P7.path10 ( B.append P8.path11 ( B.append P8.path12 ( B.append P9.path13 ( B.append P9.path14 ( B.append P10.path15 ( B.append P10.path16 ( B.append P10.path17 ( B.append P11.path18 ( B.append P11.path19 ( B.append P11.path20 ( B.append P11.path21 ( B.append P11.path22 ( B.append P11.path23 ( B.append P11.path24 ( B.append P12.path25 ( B.append P12.path26 ( B.append P12.path27 ( B.append P12.path28 ( B.append P12.path29 ( B.append P12.path30 ( B.append P12.path31 ( B.append P12.path32 ( B.append P12.path33 ( B.append P12.path34 ( B.append P12.path35 ( B.append P12.path36 ( B.append P12.path37 ( B.append P12.path38 ( B.append P12.path39 ( B.append P12.path40 ( B.append P12.path41 ( B.append P12.path42 ( B.append P12.path43 ( B.append P12.path44 ( B.append P13.path45 ( B.append P13.path46 ( B.append P13.path47 ( B.append P13.path48 ( B.append P13.path49 ( B.append P13.path50 ( B.append P13.path51 ( B.append P13.path52 ( B.append P13.path53 ( B.append P13.path54 ( B.append P13.path55 ( B.append P13.path56 ( B.append P13.path57 ( B.append P13.path58 ( B.append P13.path59 ( B.append P13.path60 ( B.append P13.path61 ( B.append P13.path62 ( B.append P13.path63 ( B.append P13.path64 ( B.append P13.path65 ( B.append P13.path66 ( B.append P13.path67 ( B.append P13.path68 ( B.append P13.path69 ( B.append P14.path70 ( B.append P14.path71 ( B.append P14.path72 ( B.append P14.path73 ( B.append P14.path74 ( B.append P14.path75 ( B.append P14.path76 ( B.append P14.path77 ( B.append P14.path78 ( B.append P14.path79 ( B.append P14.path80 ( B.append P14.path81 ( B.append P14.path82 ( B.append P14.path83 ( B.append P14.path84 ( B.append P14.path85 ( B.append P14.path86 ( B.append P14.path87 ( B.append P14.path88 ( B.append P14.path89 ( B.append P14.path90 ( B.append P14.path91 ( B.append P14.path92 ( B.append P14.path93 ( B.append P14.path94 ( B.append P15.path95 ( B.append P15.path96 ( B.append P15.path97 ( B.append P15.path98 ( B.append P15.path99 ( B.append P15.path100 ( B.append P15.path101 ( B.append P15.path102 ( B.append P15.path103 ( B.append P15.path104 ( B.append P15.path105 ( B.append P15.path106 ( B.append P15.path107 ( B.append P15.path108 ( B.append P15.path109 ( B.append P15.path110 ( B.append P15.path111 ( B.append P15.path112 ( B.append P15.path113 ( B.append P15.path114 ( B.append P15.path115 ( B.append P15.path116 ( B.append P15.path117 ( B.append P15.path118 ( B.append P15.path119 ( B.append P16.path120 ( B.append P16.path121 ( B.append P16.path122 ( B.append P16.path123 ( B.append P16.path124 ( B.append P16.path125 ( B.append P16.path126 ( B.append P16.path127 ( B.append P16.path128 ( B.append P16.path129 ( B.append P16.path130 ( B.append P16.path131 ( B.append P16.path132 ( B.append P16.path133 ( B.append P16.path134 ( B.append P16.path135 ( B.append P16.path136 ( B.append P16.path137 ( B.append P16.path138 ( B.append P16.path139 ( B.append P16.path140 ( B.append P16.path141 ( B.append P16.path142 ( B.append P16.path143 ( B.append P16.path144 ( B.append P17.path145 ( B.append P17.path146 ( B.append P17.path147 ( B.append P17.path148 ( B.append P17.path149 ( B.append P17.path150 ( B.append P17.path151 ( B.append P17.path152 ( B.append P17.path153 ( B.append P17.path154 ( B.append P17.path155 (P17.path156))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  initialized-frontend : V.Runs Policy.source120 (B.erase schedule) (B.runtime endpoint)
  initialized-frontend = B.project initialized-contracts
