{-# OPTIONS --guardedness #-}

-- Data-only infrastructure-pool snapshots for one current-snapshot close.
-- These are not execution certificates; acceptance modules prove every step.
open import ConnectionManagement.Domain using (JobId)
module ConnectionManagement.Negative.MuxPoolCloseFixtures (first second : JobId) where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
import ConnectionManagement.Rules.MuxJobTypes as Types
module Pool = Kernel Types.TypedResult true

k0 : Pool.State
k0 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.bodyRunning) ∷ []) (second ∷ first ∷ []) nothing (Pool.openPool) ([]) ([]) ([]) []
k1 : Pool.State
k1 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.bodyRunning) ∷ []) (second ∷ first ∷ []) nothing (Pool.closing) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k2 : Pool.State
k2 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.bodyRunning) ∷ []) (second ∷ first ∷ []) nothing (Pool.cancelPending second) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k3 : Pool.State
k3 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.bodyUnwinding) ∷ []) (second ∷ first ∷ []) nothing (Pool.joinPending second) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k4 : Pool.State
k4 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.deregisterPending Pool.cancelledExit) ∷ []) (second ∷ first ∷ []) nothing (Pool.joinPending second) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k5 : Pool.State
k5 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.deregistered Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.joinPending second) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k6 : Pool.State
k6 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.joinPending second) (second ∷ first ∷ []) (second ∷ first ∷ []) ([]) []
k7 : Pool.State
k7 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.closing) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k8 : Pool.State
k8 = Pool.poolState ((first , Pool.bodyRunning) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.cancelPending first) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k9 : Pool.State
k9 = Pool.poolState ((first , Pool.bodyUnwinding) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.joinPending first) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k10 : Pool.State
k10 = Pool.poolState ((first , Pool.deregisterPending Pool.cancelledExit) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) (first ∷ []) nothing (Pool.joinPending first) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k11 : Pool.State
k11 = Pool.poolState ((first , Pool.deregistered Pool.cancelledExit) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.joinPending first) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k12 : Pool.State
k12 = Pool.poolState ((first , Pool.resultAvailable Pool.cancelledExit) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.joinPending first) (second ∷ first ∷ []) (first ∷ []) (second ∷ []) []
k13 : Pool.State
k13 = Pool.poolState ((first , Pool.resultAvailable Pool.cancelledExit) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.closing) (second ∷ first ∷ []) ([]) (second ∷ first ∷ []) []
k14 : Pool.State
k14 = Pool.poolState ((first , Pool.resultAvailable Pool.cancelledExit) ∷ (second , Pool.resultAvailable Pool.cancelledExit) ∷ []) ([]) nothing (Pool.closedPool) (second ∷ first ∷ []) ([]) (second ∷ first ∷ []) []
