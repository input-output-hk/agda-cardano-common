{-# OPTIONS --guardedness #-}

-- Compose only independently checked real-edge segments from the initializer.
module ConnectionManagement.Negative.ConcurrentLifecycles where

open import ConnectionManagement.Negative.ConcurrentLifecycleSupport
import ConnectionManagement.Negative.ConcurrentLifecycle01 as R1
import ConnectionManagement.Negative.ConcurrentLifecycle02 as R2
import ConnectionManagement.Negative.ConcurrentLifecycle03 as R3
import ConnectionManagement.Negative.ConcurrentLifecycle04 as R4
import ConnectionManagement.Negative.ConcurrentLifecycle05 as R5
import ConnectionManagement.Negative.ConcurrentLifecycle06 as R6
import ConnectionManagement.Negative.ConcurrentLifecycle07 as R7
import ConnectionManagement.Negative.ConcurrentLifecycle08 as R8
import ConnectionManagement.Negative.ConcurrentLifecycle09 as R9
import ConnectionManagement.Negative.ConcurrentLifecycle10 as R10
import ConnectionManagement.Negative.ConcurrentLifecycle11 as R11
import ConnectionManagement.Negative.ConcurrentLifecycle12 as R12
import ConnectionManagement.Negative.ConcurrentLifecycle13 as R13
import ConnectionManagement.Negative.ConcurrentLifecycle14 as R14
import ConnectionManagement.Negative.ConcurrentLifecycle15 as R15
import ConnectionManagement.Negative.ConcurrentLifecycle16 as R16
import ConnectionManagement.Negative.ConcurrentLifecycle17 as R17
import ConnectionManagement.Negative.ConcurrentLifecycle18 as R18
import ConnectionManagement.Negative.ConcurrentLifecycle19 as R19

final : V.Runtime
final = R19.final

schedule : List V.Event
schedule = R1.actions ++ (R2.actions ++ (R3.actions ++ (R4.actions ++ (R5.actions ++ (R6.actions ++ (R7.actions ++ (R8.actions ++ (R9.actions ++ (R10.actions ++ (R11.actions ++ (R12.actions ++ (R13.actions ++ (R14.actions ++ (R15.actions ++ (R16.actions ++ (R17.actions ++ (R18.actions ++ (R19.actions))))))))))))))))))

abstract
  initialized-to-completion : V.Runs initial schedule final
  initialized-to-completion = append R1.path (append R2.path (append R3.path (append R4.path (append R5.path (append R6.path (append R7.path (append R8.path (append R9.path (append R10.path (append R11.path (append R12.path (append R13.path (append R14.path (append R15.path (append R16.path (append R17.path (append R18.path (R19.path))))))))))))))))))

step-count : length schedule ≡ 294
step-count = refl
