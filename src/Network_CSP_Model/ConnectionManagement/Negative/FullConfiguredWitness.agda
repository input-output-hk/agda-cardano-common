{-# OPTIONS --guardedness #-}

-- Full initialized normal protocol lifecycle, with actual CM cancellation
-- at release TIME_WAIT. This is an existence witness, not universal progress.
module ConnectionManagement.Negative.FullConfiguredWitness where

open import ConnectionManagement.Negative.FullConfiguredProfile
import ConnectionManagement.ConfiguredProtocols as Contracts
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.CSP.GovernorLifecycle as L
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as Governor
import ConnectionManagement.Rules.OutboundAcquire as Acquire
import ConnectionManagement.Rules.OutboundRelease as OutRelease
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.MuxJobTypes as JobTypes
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
open import ConnectionManagement.Negative.FullConfiguredContractProfile using (module B)
import ConnectionManagement.Negative.FullConfiguredContractAcquire as S0
import ConnectionManagement.Negative.FullConfiguredStartup as S1
import ConnectionManagement.Negative.FullConfiguredEstablished as S2
import ConnectionManagement.Negative.FullConfiguredPromote as S3
import ConnectionManagement.Negative.FullConfiguredHot2 as S4
import ConnectionManagement.Negative.FullConfiguredHot3 as S5
import ConnectionManagement.Negative.FullConfiguredHot4 as S6
import ConnectionManagement.Negative.FullConfiguredHot18 as S7
import ConnectionManagement.Negative.FullConfiguredHot19 as S8
import ConnectionManagement.Negative.FullConfiguredHot as S9
import ConnectionManagement.Negative.FullConfiguredDemote as S10
import ConnectionManagement.Negative.FullConfiguredBodies as S11
import ConnectionManagement.Negative.FullConfiguredChain as S12
import ConnectionManagement.Negative.FullConfiguredFetchTx as S13
import ConnectionManagement.Negative.FullConfiguredNotify as S14
import ConnectionManagement.Negative.FullConfiguredLeiosFetch as S15
import ConnectionManagement.Negative.FullConfiguredResult2Body as S16
import ConnectionManagement.Negative.FullConfiguredResult2 as S17
import ConnectionManagement.Negative.FullConfiguredResult3Body as S18
import ConnectionManagement.Negative.FullConfiguredResult3Select as S19
import ConnectionManagement.Negative.FullConfiguredResult3 as S20
import ConnectionManagement.Negative.FullConfiguredResult4Return as S21
import ConnectionManagement.Negative.FullConfiguredResult4Body as S22
import ConnectionManagement.Negative.FullConfiguredResult4Select as S23
import ConnectionManagement.Negative.FullConfiguredResult4 as S24
import ConnectionManagement.Negative.FullConfiguredResult18Return as S25
import ConnectionManagement.Negative.FullConfiguredResult18BodyPart0 as S26
import ConnectionManagement.Negative.FullConfiguredResult18BodyPart1 as S27
import ConnectionManagement.Negative.FullConfiguredResult18Body as S28
import ConnectionManagement.Negative.FullConfiguredResult18SelectBudget0 as S29
import ConnectionManagement.Negative.FullConfiguredResult18Select as S30
import ConnectionManagement.Negative.FullConfiguredResult18Budget0 as S31
import ConnectionManagement.Negative.FullConfiguredResult18 as S32
import ConnectionManagement.Negative.FullConfiguredResult19ReturnBudget0 as S33
import ConnectionManagement.Negative.FullConfiguredResult19Return as S34
import ConnectionManagement.Negative.FullConfiguredResult19BodyPart0 as S35
import ConnectionManagement.Negative.FullConfiguredResult19BodyPart1 as S36
import ConnectionManagement.Negative.FullConfiguredResult19Body as S37
import ConnectionManagement.Negative.FullConfiguredResult19SelectBudget0Edge0 as S38
import ConnectionManagement.Negative.FullConfiguredResult19SelectBudget0 as S39
import ConnectionManagement.Negative.FullConfiguredResult19Select as S40
import ConnectionManagement.Negative.FullConfiguredResult19Budget0Edge0 as S41
import ConnectionManagement.Negative.FullConfiguredResult19Budget0 as S42
import ConnectionManagement.Negative.FullConfiguredResult19 as S43
import ConnectionManagement.Negative.FullConfiguredWarmBudget0Edge0 as S44
import ConnectionManagement.Negative.FullConfiguredWarmBudget0 as S45
import ConnectionManagement.Negative.FullConfiguredWarmBudget1Edge0 as S46
import ConnectionManagement.Negative.FullConfiguredWarmBudget1 as S47
import ConnectionManagement.Negative.FullConfiguredWarmBudget2Edge0 as S48
import ConnectionManagement.Negative.FullConfiguredWarmBudget2 as S49
import ConnectionManagement.Negative.FullConfiguredWarmBudget3Edge0 as S50
import ConnectionManagement.Negative.FullConfiguredWarmBudget3 as S51
import ConnectionManagement.Negative.FullConfiguredWarmBudget4Edge0 as S52
import ConnectionManagement.Negative.FullConfiguredWarmBudget4 as S53
import ConnectionManagement.Negative.FullConfiguredWarmBudget5Edge0 as S54
import ConnectionManagement.Negative.FullConfiguredWarmBudget5 as S55
import ConnectionManagement.Negative.FullConfiguredWarmBudget6Edge0 as S56
import ConnectionManagement.Negative.FullConfiguredWarmBudget6 as S57
import ConnectionManagement.Negative.FullConfiguredWarmEdge0 as S58
import ConnectionManagement.Negative.FullConfiguredWarm as S59
import ConnectionManagement.Negative.FullConfiguredCloseBudget0Edge0 as S60
import ConnectionManagement.Negative.FullConfiguredCloseBudget0 as S61
import ConnectionManagement.Negative.FullConfiguredCloseBudget1Edge0 as S62
import ConnectionManagement.Negative.FullConfiguredCloseBudget1 as S63
import ConnectionManagement.Negative.FullConfiguredCloseBudget2Edge0 as S64
import ConnectionManagement.Negative.FullConfiguredCloseBudget2 as S65
import ConnectionManagement.Negative.FullConfiguredCloseBudget3Edge0 as S66
import ConnectionManagement.Negative.FullConfiguredCloseBudget3 as S67
import ConnectionManagement.Negative.FullConfiguredCloseBudget4Edge0 as S68
import ConnectionManagement.Negative.FullConfiguredCloseBudget4 as S69
import ConnectionManagement.Negative.FullConfiguredCloseBudget5Edge0 as S70
import ConnectionManagement.Negative.FullConfiguredCloseBudget5 as S71
import ConnectionManagement.Negative.FullConfiguredCloseBudget6Edge0 as S72
import ConnectionManagement.Negative.FullConfiguredCloseBudget6 as S73
import ConnectionManagement.Negative.FullConfiguredCloseEdge0 as S74
import ConnectionManagement.Negative.FullConfiguredClose as S75
import ConnectionManagement.Negative.FullConfiguredKeepAliveContractEdge0 as S76
import ConnectionManagement.Negative.FullConfiguredKeepAliveContractEdge1 as S77
import ConnectionManagement.Negative.FullConfiguredKeepAliveContract as S78
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturnBudget0Edge0 as S79
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturnBudget0 as S80
import ConnectionManagement.Negative.FullConfiguredKeepAliveReturn as S81
import ConnectionManagement.Negative.FullConfiguredKeepAlivePublish as S82
import ConnectionManagement.Negative.FullConfiguredKeepAliveDeregister as S83
import ConnectionManagement.Negative.FullConfiguredKeepAliveBody as S84
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelectBudget0Edge0 as S85
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelectBudget0 as S86
import ConnectionManagement.Negative.FullConfiguredKeepAliveSelect as S87
import ConnectionManagement.Negative.FullConfiguredKeepAliveBudget0Edge0 as S88
import ConnectionManagement.Negative.FullConfiguredKeepAliveBudget0 as S89
import ConnectionManagement.Negative.FullConfiguredKeepAlive as S90
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget0Edge0 as S91
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget0 as S92
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget1Edge0 as S93
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget1 as S94
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget2Edge0 as S95
import ConnectionManagement.Negative.FullConfiguredMuxScopeBudget2 as S96
import ConnectionManagement.Negative.FullConfiguredMuxScopeEdge0 as S97
import ConnectionManagement.Negative.FullConfiguredMuxScope as S98
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget0Edge0 as S99
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget0 as S100
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget1Edge0 as S101
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget1 as S102
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget2Edge0 as S103
import ConnectionManagement.Negative.FullConfiguredMuxCloseBudget2 as S104
import ConnectionManagement.Negative.FullConfiguredMuxCloseEdge0 as S105
import ConnectionManagement.Negative.FullConfiguredMuxClose as S106
import ConnectionManagement.Negative.FullConfiguredMuxBudget0Edge0 as S107
import ConnectionManagement.Negative.FullConfiguredMuxBudget0 as S108
import ConnectionManagement.Negative.FullConfiguredMuxBudget1Edge0 as S109
import ConnectionManagement.Negative.FullConfiguredMuxBudget1 as S110
import ConnectionManagement.Negative.FullConfiguredMuxBudget2Edge0 as S111
import ConnectionManagement.Negative.FullConfiguredMuxBudget2 as S112
import ConnectionManagement.Negative.FullConfiguredMuxBudget3Edge0 as S113
import ConnectionManagement.Negative.FullConfiguredMuxBudget3 as S114
import ConnectionManagement.Negative.FullConfiguredMux as S115
import ConnectionManagement.Negative.FullConfiguredReleaseBudget0Edge0 as S116
import ConnectionManagement.Negative.FullConfiguredReleaseBudget0 as S117
import ConnectionManagement.Negative.FullConfiguredReleaseBudget1Edge0 as S118
import ConnectionManagement.Negative.FullConfiguredReleaseBudget1 as S119
import ConnectionManagement.Negative.FullConfiguredReleaseBudget2Edge0 as S120
import ConnectionManagement.Negative.FullConfiguredReleaseBudget2 as S121
import ConnectionManagement.Negative.FullConfiguredReleaseBudget3Edge0 as S122
import ConnectionManagement.Negative.FullConfiguredReleaseBudget3 as S123
import ConnectionManagement.Negative.FullConfiguredReleaseEdge0 as S124
import ConnectionManagement.Negative.FullConfiguredRelease as S125
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget0Edge0 as S126
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget0 as S127
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget1Edge0 as S128
import ConnectionManagement.Negative.FullConfiguredColdCleanupBudget1 as S129
import ConnectionManagement.Negative.FullConfiguredColdCleanupEdge0 as S130
import ConnectionManagement.Negative.FullConfiguredColdCleanup as S131
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget0Edge0 as S132
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget0 as S133
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget1Edge0 as S134
import ConnectionManagement.Negative.FullConfiguredColdReceiptBudget1 as S135
import ConnectionManagement.Negative.FullConfiguredColdReceiptEdge0 as S136
import ConnectionManagement.Negative.FullConfiguredColdReceipt as S137
import ConnectionManagement.Negative.FullConfiguredColdBudget0Edge0 as S138
import ConnectionManagement.Negative.FullConfiguredColdBudget0 as S139
import ConnectionManagement.Negative.FullConfiguredColdBudget1Edge0 as S140
import ConnectionManagement.Negative.FullConfiguredColdBudget1 as S141
import ConnectionManagement.Negative.FullConfiguredColdBudget2Edge0 as S142
import ConnectionManagement.Negative.FullConfiguredColdBudget2 as S143
import ConnectionManagement.Negative.FullConfiguredCold as S144
import ConnectionManagement.Negative.FullConfiguredCompleteBudget0Edge0 as S145
import ConnectionManagement.Negative.FullConfiguredCompleteBudget0 as S146
import ConnectionManagement.Negative.FullConfiguredCompleteBudget1Edge0 as S147
import ConnectionManagement.Negative.FullConfiguredCompleteBudget1 as S148
import ConnectionManagement.Negative.FullConfiguredCompleteBudget2Edge0 as S149
import ConnectionManagement.Negative.FullConfiguredCompleteBudget2 as S150
import ConnectionManagement.Negative.FullConfiguredCompleteBudget3Edge0 as S151
import ConnectionManagement.Negative.FullConfiguredCompleteBudget3 as S152
import ConnectionManagement.Negative.FullConfiguredCompleteBudget4Edge0 as S153
import ConnectionManagement.Negative.FullConfiguredCompleteBudget4 as S154
import ConnectionManagement.Negative.FullConfiguredCompleteEdge0 as S155
import ConnectionManagement.Negative.FullConfiguredComplete as S156

start : B.State
start = B.initial initial L.child (ident 0) (ident 0)
endpoint : B.State
endpoint = S156.s1

schedule : List B.Action
schedule = S0.actions ++ (S1.actions ++ (S2.actions ++ (S3.actions ++ (S4.actions ++ (S5.actions ++ (S6.actions ++ (S7.actions ++ (S8.actions ++ (S9.actions ++ (S10.actions ++ (S11.actions ++ (S12.actions ++ (S13.actions ++ (S14.actions ++ (S15.actions ++ (S16.actions ++ (S17.actions ++ (S18.actions ++ (S19.actions ++ (S20.actions ++ (S21.actions ++ (S22.actions ++ (S23.actions ++ (S24.actions ++ (S25.actions ++ (S26.actions ++ (S27.actions ++ (S28.actions ++ (S29.actions ++ (S30.actions ++ (S31.actions ++ (S32.actions ++ (S33.actions ++ (S34.actions ++ (S35.actions ++ (S36.actions ++ (S37.actions ++ (S38.actions ++ (S39.actions ++ (S40.actions ++ (S41.actions ++ (S42.actions ++ (S43.actions ++ (S44.actions ++ (S45.actions ++ (S46.actions ++ (S47.actions ++ (S48.actions ++ (S49.actions ++ (S50.actions ++ (S51.actions ++ (S52.actions ++ (S53.actions ++ (S54.actions ++ (S55.actions ++ (S56.actions ++ (S57.actions ++ (S58.actions ++ (S59.actions ++ (S60.actions ++ (S61.actions ++ (S62.actions ++ (S63.actions ++ (S64.actions ++ (S65.actions ++ (S66.actions ++ (S67.actions ++ (S68.actions ++ (S69.actions ++ (S70.actions ++ (S71.actions ++ (S72.actions ++ (S73.actions ++ (S74.actions ++ (S75.actions ++ (S76.actions ++ (S77.actions ++ (S78.actions ++ (S79.actions ++ (S80.actions ++ (S81.actions ++ (S82.actions ++ (S83.actions ++ (S84.actions ++ (S85.actions ++ (S86.actions ++ (S87.actions ++ (S88.actions ++ (S89.actions ++ (S90.actions ++ (S91.actions ++ (S92.actions ++ (S93.actions ++ (S94.actions ++ (S95.actions ++ (S96.actions ++ (S97.actions ++ (S98.actions ++ (S99.actions ++ (S100.actions ++ (S101.actions ++ (S102.actions ++ (S103.actions ++ (S104.actions ++ (S105.actions ++ (S106.actions ++ (S107.actions ++ (S108.actions ++ (S109.actions ++ (S110.actions ++ (S111.actions ++ (S112.actions ++ (S113.actions ++ (S114.actions ++ (S115.actions ++ (S116.actions ++ (S117.actions ++ (S118.actions ++ (S119.actions ++ (S120.actions ++ (S121.actions ++ (S122.actions ++ (S123.actions ++ (S124.actions ++ (S125.actions ++ (S126.actions ++ (S127.actions ++ (S128.actions ++ (S129.actions ++ (S130.actions ++ (S131.actions ++ (S132.actions ++ (S133.actions ++ (S134.actions ++ (S135.actions ++ (S136.actions ++ (S137.actions ++ (S138.actions ++ (S139.actions ++ (S140.actions ++ (S141.actions ++ (S142.actions ++ (S143.actions ++ (S144.actions ++ (S145.actions ++ (S146.actions ++ (S147.actions ++ (S148.actions ++ (S149.actions ++ (S150.actions ++ (S151.actions ++ (S152.actions ++ (S153.actions ++ (S154.actions ++ (S155.actions ++ (S156.actions))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abstract
  initialized-contracts : B.Runs start schedule endpoint
  initialized-contracts = B.append S0.path ( B.append S1.path ( B.append S2.path ( B.append S3.path ( B.append S4.path ( B.append S5.path ( B.append S6.path ( B.append S7.path ( B.append S8.path ( B.append S9.path ( B.append S10.path ( B.append S11.path ( B.append S12.path ( B.append S13.path ( B.append S14.path ( B.append S15.path ( B.append S16.path ( B.append S17.path ( B.append S18.path ( B.append S19.path ( B.append S20.path ( B.append S21.path ( B.append S22.path ( B.append S23.path ( B.append S24.path ( B.append S25.path ( B.append S26.path ( B.append S27.path ( B.append S28.path ( B.append S29.path ( B.append S30.path ( B.append S31.path ( B.append S32.path ( B.append S33.path ( B.append S34.path ( B.append S35.path ( B.append S36.path ( B.append S37.path ( B.append S38.path ( B.append S39.path ( B.append S40.path ( B.append S41.path ( B.append S42.path ( B.append S43.path ( B.append S44.path ( B.append S45.path ( B.append S46.path ( B.append S47.path ( B.append S48.path ( B.append S49.path ( B.append S50.path ( B.append S51.path ( B.append S52.path ( B.append S53.path ( B.append S54.path ( B.append S55.path ( B.append S56.path ( B.append S57.path ( B.append S58.path ( B.append S59.path ( B.append S60.path ( B.append S61.path ( B.append S62.path ( B.append S63.path ( B.append S64.path ( B.append S65.path ( B.append S66.path ( B.append S67.path ( B.append S68.path ( B.append S69.path ( B.append S70.path ( B.append S71.path ( B.append S72.path ( B.append S73.path ( B.append S74.path ( B.append S75.path ( B.append S76.path ( B.append S77.path ( B.append S78.path ( B.append S79.path ( B.append S80.path ( B.append S81.path ( B.append S82.path ( B.append S83.path ( B.append S84.path ( B.append S85.path ( B.append S86.path ( B.append S87.path ( B.append S88.path ( B.append S89.path ( B.append S90.path ( B.append S91.path ( B.append S92.path ( B.append S93.path ( B.append S94.path ( B.append S95.path ( B.append S96.path ( B.append S97.path ( B.append S98.path ( B.append S99.path ( B.append S100.path ( B.append S101.path ( B.append S102.path ( B.append S103.path ( B.append S104.path ( B.append S105.path ( B.append S106.path ( B.append S107.path ( B.append S108.path ( B.append S109.path ( B.append S110.path ( B.append S111.path ( B.append S112.path ( B.append S113.path ( B.append S114.path ( B.append S115.path ( B.append S116.path ( B.append S117.path ( B.append S118.path ( B.append S119.path ( B.append S120.path ( B.append S121.path ( B.append S122.path ( B.append S123.path ( B.append S124.path ( B.append S125.path ( B.append S126.path ( B.append S127.path ( B.append S128.path ( B.append S129.path ( B.append S130.path ( B.append S131.path ( B.append S132.path ( B.append S133.path ( B.append S134.path ( B.append S135.path ( B.append S136.path ( B.append S137.path ( B.append S138.path ( B.append S139.path ( B.append S140.path ( B.append S141.path ( B.append S142.path ( B.append S143.path ( B.append S144.path ( B.append S145.path ( B.append S146.path ( B.append S147.path ( B.append S148.path ( B.append S149.path ( B.append S150.path ( B.append S151.path ( B.append S152.path ( B.append S153.path ( B.append S154.path ( B.append S155.path (S156.path))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  initialized-frontend : V.Runs initial (B.erase schedule) (B.runtime endpoint)
  initialized-frontend = B.project initialized-contracts

contract-event-count : length schedule ≡ 381
contract-event-count = refl
frontend-event-count : length (B.erase schedule) ≡ 322
frontend-event-count = refl
