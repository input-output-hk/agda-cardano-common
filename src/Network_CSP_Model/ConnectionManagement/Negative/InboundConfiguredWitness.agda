{-# OPTIONS --guardedness #-}

-- Existence of the full responder lifecycle, with explicit boundary inputs.
-- This does not imply universal completion or implementation refinement.
module ConnectionManagement.Negative.InboundConfiguredWitness where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.InboundConfiguredAdmission0 as S0
import ConnectionManagement.Negative.InboundConfiguredAdmission1 as S1
import ConnectionManagement.Negative.InboundConfiguredAdmission2 as S2
import ConnectionManagement.Negative.InboundConfiguredAdmission3 as S3
import ConnectionManagement.Negative.InboundConfiguredAdmission4 as S4
import ConnectionManagement.Negative.InboundConfiguredAdmission5 as S5
import ConnectionManagement.Negative.InboundConfiguredAdmission6 as S6
import ConnectionManagement.Negative.InboundConfiguredAdmission7 as S7
import ConnectionManagement.Negative.InboundConfiguredAdmission8 as S8
import ConnectionManagement.Negative.InboundConfiguredAdmission9 as S9
import ConnectionManagement.Negative.InboundConfiguredAdmission10 as S10
import ConnectionManagement.Negative.InboundConfiguredAdmission11 as S11
import ConnectionManagement.Negative.InboundConfiguredAdmission12 as S12
import ConnectionManagement.Negative.InboundConfiguredStart0 as S13
import ConnectionManagement.Negative.InboundConfiguredStart1 as S14
import ConnectionManagement.Negative.InboundConfiguredStart2 as S15
import ConnectionManagement.Negative.InboundConfiguredStart3 as S16
import ConnectionManagement.Negative.InboundConfiguredStart4 as S17
import ConnectionManagement.Negative.InboundConfiguredStart5 as S18
import ConnectionManagement.Negative.InboundConfiguredStart6 as S19
import ConnectionManagement.Negative.InboundConfiguredStart7 as S20
import ConnectionManagement.Negative.InboundConfiguredStart8 as S21
import ConnectionManagement.Negative.InboundConfiguredStart9 as S22
import ConnectionManagement.Negative.InboundConfiguredStart10 as S23
import ConnectionManagement.Negative.InboundConfiguredStart11 as S24
import ConnectionManagement.Negative.InboundConfiguredStart12 as S25
import ConnectionManagement.Negative.InboundConfiguredStart13 as S26
import ConnectionManagement.Negative.InboundConfiguredStart14 as S27
import ConnectionManagement.Negative.InboundConfiguredStart15 as S28
import ConnectionManagement.Negative.InboundConfiguredStart16 as S29
import ConnectionManagement.Negative.InboundConfiguredStart17 as S30
import ConnectionManagement.Negative.InboundConfiguredChainContract0 as S31
import ConnectionManagement.Negative.InboundConfiguredChainContract1 as S32
import ConnectionManagement.Negative.InboundConfiguredChainResult0 as S33
import ConnectionManagement.Negative.InboundConfiguredChainResult1 as S34
import ConnectionManagement.Negative.InboundConfiguredChainResult2 as S35
import ConnectionManagement.Negative.InboundConfiguredChainResult3 as S36
import ConnectionManagement.Negative.InboundConfiguredKeepContract0 as S37
import ConnectionManagement.Negative.InboundConfiguredKeepContract1 as S38
import ConnectionManagement.Negative.InboundConfiguredKeepResult0 as S39
import ConnectionManagement.Negative.InboundConfiguredKeepResult1 as S40
import ConnectionManagement.Negative.InboundConfiguredKeepResult2 as S41
import ConnectionManagement.Negative.InboundConfiguredKeepResult3 as S42
import ConnectionManagement.Negative.InboundConfiguredFetchContract0 as S43
import ConnectionManagement.Negative.InboundConfiguredFetchContract1 as S44
import ConnectionManagement.Negative.InboundConfiguredFetchResult0 as S45
import ConnectionManagement.Negative.InboundConfiguredFetchResult1 as S46
import ConnectionManagement.Negative.InboundConfiguredFetchResult2 as S47
import ConnectionManagement.Negative.InboundConfiguredFetchResult3 as S48
import ConnectionManagement.Negative.InboundConfiguredTxContract0 as S49
import ConnectionManagement.Negative.InboundConfiguredTxContract1 as S50
import ConnectionManagement.Negative.InboundConfiguredTxContract2 as S51
import ConnectionManagement.Negative.InboundConfiguredTxResult0 as S52
import ConnectionManagement.Negative.InboundConfiguredTxResult1 as S53
import ConnectionManagement.Negative.InboundConfiguredTxResult2 as S54
import ConnectionManagement.Negative.InboundConfiguredTxResult3 as S55
import ConnectionManagement.Negative.InboundConfiguredNotifyContract0 as S56
import ConnectionManagement.Negative.InboundConfiguredNotifyContract1 as S57
import ConnectionManagement.Negative.InboundConfiguredNotifyResult0 as S58
import ConnectionManagement.Negative.InboundConfiguredNotifyResult1 as S59
import ConnectionManagement.Negative.InboundConfiguredNotifyResult2 as S60
import ConnectionManagement.Negative.InboundConfiguredNotifyResult3 as S61
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchContract0 as S62
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchContract1 as S63
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult0 as S64
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult1 as S65
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult2 as S66
import ConnectionManagement.Negative.InboundConfiguredLeiosFetchResult3 as S67
import ConnectionManagement.Negative.InboundConfiguredMux0 as S68
import ConnectionManagement.Negative.InboundConfiguredMux1 as S69
import ConnectionManagement.Negative.InboundConfiguredMux2 as S70
import ConnectionManagement.Negative.InboundConfiguredMux3 as S71
import ConnectionManagement.Negative.InboundConfiguredMux4 as S72
import ConnectionManagement.Negative.InboundConfiguredMux5 as S73
import ConnectionManagement.Negative.InboundConfiguredMux6 as S74
import ConnectionManagement.Negative.InboundConfiguredMux7 as S75
import ConnectionManagement.Negative.InboundConfiguredMux8 as S76
import ConnectionManagement.Negative.InboundConfiguredCleanup0 as S77
import ConnectionManagement.Negative.InboundConfiguredCleanup1 as S78
import ConnectionManagement.Negative.InboundConfiguredCleanup2 as S79
import ConnectionManagement.Negative.InboundConfiguredCleanup3 as S80
import ConnectionManagement.Negative.InboundConfiguredCleanup4 as S81
import ConnectionManagement.Negative.InboundConfiguredCleanup5 as S82
import ConnectionManagement.Negative.InboundConfiguredCleanup6 as S83
import ConnectionManagement.Negative.InboundConfiguredCleanup7 as S84

endpoint : B.State
endpoint = S84.s3

schedule : List B.Action
schedule = S0.actions ++ (S1.actions ++ (S2.actions ++ (S3.actions ++ (S4.actions ++ (S5.actions ++ (S6.actions ++ (S7.actions ++ (S8.actions ++ (S9.actions ++ (S10.actions ++ (S11.actions ++ (S12.actions ++ (S13.actions ++ (S14.actions ++ (S15.actions ++ (S16.actions ++ (S17.actions ++ (S18.actions ++ (S19.actions ++ (S20.actions ++ (S21.actions ++ (S22.actions ++ (S23.actions ++ (S24.actions ++ (S25.actions ++ (S26.actions ++ (S27.actions ++ (S28.actions ++ (S29.actions ++ (S30.actions ++ (S31.actions ++ (S32.actions ++ (S33.actions ++ (S34.actions ++ (S35.actions ++ (S36.actions ++ (S37.actions ++ (S38.actions ++ (S39.actions ++ (S40.actions ++ (S41.actions ++ (S42.actions ++ (S43.actions ++ (S44.actions ++ (S45.actions ++ (S46.actions ++ (S47.actions ++ (S48.actions ++ (S49.actions ++ (S50.actions ++ (S51.actions ++ (S52.actions ++ (S53.actions ++ (S54.actions ++ (S55.actions ++ (S56.actions ++ (S57.actions ++ (S58.actions ++ (S59.actions ++ (S60.actions ++ (S61.actions ++ (S62.actions ++ (S63.actions ++ (S64.actions ++ (S65.actions ++ (S66.actions ++ (S67.actions ++ (S68.actions ++ (S69.actions ++ (S70.actions ++ (S71.actions ++ (S72.actions ++ (S73.actions ++ (S74.actions ++ (S75.actions ++ (S76.actions ++ (S77.actions ++ (S78.actions ++ (S79.actions ++ (S80.actions ++ (S81.actions ++ (S82.actions ++ (S83.actions ++ (S84.actions))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

abstract
  initialized-contracts : B.Runs
    (B.initial initial A.child₀ (ident 0)) schedule endpoint
  initialized-contracts = B.append S0.path (B.append S1.path (B.append S2.path (B.append S3.path (B.append S4.path (B.append S5.path (B.append S6.path (B.append S7.path (B.append S8.path (B.append S9.path (B.append S10.path (B.append S11.path (B.append S12.path (B.append S13.path (B.append S14.path (B.append S15.path (B.append S16.path (B.append S17.path (B.append S18.path (B.append S19.path (B.append S20.path (B.append S21.path (B.append S22.path (B.append S23.path (B.append S24.path (B.append S25.path (B.append S26.path (B.append S27.path (B.append S28.path (B.append S29.path (B.append S30.path (B.append S31.path (B.append S32.path (B.append S33.path (B.append S34.path (B.append S35.path (B.append S36.path (B.append S37.path (B.append S38.path (B.append S39.path (B.append S40.path (B.append S41.path (B.append S42.path (B.append S43.path (B.append S44.path (B.append S45.path (B.append S46.path (B.append S47.path (B.append S48.path (B.append S49.path (B.append S50.path (B.append S51.path (B.append S52.path (B.append S53.path (B.append S54.path (B.append S55.path (B.append S56.path (B.append S57.path (B.append S58.path (B.append S59.path (B.append S60.path (B.append S61.path (B.append S62.path (B.append S63.path (B.append S64.path (B.append S65.path (B.append S66.path (B.append S67.path (B.append S68.path (B.append S69.path (B.append S70.path (B.append S71.path (B.append S72.path (B.append S73.path (B.append S74.path (B.append S75.path (B.append S76.path (B.append S77.path (B.append S78.path (B.append S79.path (B.append S80.path (B.append S81.path (B.append S82.path (B.append S83.path (S84.path))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  initialized-frontend : V.Runs initial (B.erase schedule) (B.runtime endpoint)
  initialized-frontend = B.project initialized-contracts

wrapper-input-count : length schedule ≡ 246
wrapper-input-count = refl
frontend-event-count : length (B.erase schedule) ≡ 208
frontend-event-count = refl
