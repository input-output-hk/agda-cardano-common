{-# OPTIONS --guardedness #-}

-- Compose only independently checked real-edge segments from the initializer.
module ConnectionManagement.Negative.OverlapInitialized where

open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
open import ConnectionManagement.Negative.InboundCleanLifecycle using (append)
import ConnectionManagement.Negative.OverlapInitializedPrefix as Prefix
import ConnectionManagement.Negative.OverlapInitialized01 as R1
import ConnectionManagement.Negative.OverlapInitialized02 as R2
import ConnectionManagement.Negative.OverlapInitialized03 as R3
import ConnectionManagement.Negative.OverlapInitialized04 as R4
import ConnectionManagement.Negative.OverlapInitialized05 as R5
import ConnectionManagement.Negative.OverlapInitialized06 as R6
import ConnectionManagement.Negative.OverlapInitialized07 as R7
import ConnectionManagement.Negative.OverlapInitialized08 as R8
import ConnectionManagement.Negative.OverlapInitialized09 as R9
import ConnectionManagement.Negative.OverlapInitialized10 as R10
import ConnectionManagement.Negative.OverlapInitialized11 as R11
import ConnectionManagement.Negative.OverlapInitialized12 as R12
import ConnectionManagement.Negative.OverlapInitialized13 as R13
import ConnectionManagement.Negative.OverlapInitialized14 as R14
import ConnectionManagement.Negative.OverlapInitialized15 as R15
import ConnectionManagement.Negative.OverlapInitialized16 as R16
import ConnectionManagement.Negative.OverlapInitialized17 as R17

final : V.Runtime
final = R17.final

schedule : List V.Event
schedule = Prefix.actions ++ (R1.actions ++ (R2.actions ++ (R3.actions ++ (R4.actions ++ (R5.actions ++ (R6.actions ++ (R7.actions ++ (R8.actions ++ (R9.actions ++ (R10.actions ++ (R11.actions ++ (R12.actions ++ (R13.actions ++ (R14.actions ++ (R15.actions ++ (R16.actions ++ (R17.actions)))))))))))))))))

abstract
  initialized-to-overlap : V.Runs initial schedule final
  initialized-to-overlap = append Prefix.path (append R1.path (append R2.path (append R3.path (append R4.path (append R5.path (append R6.path (append R7.path (append R8.path (append R9.path (append R10.path (append R11.path (append R12.path (append R13.path (append R14.path (append R15.path (append R16.path (R17.path)))))))))))))))))

step-count : length schedule ≡ 303
step-count = refl
