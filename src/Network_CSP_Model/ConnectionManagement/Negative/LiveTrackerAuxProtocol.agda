{-# OPTIONS --guardedness #-}

-- Nonempty initialized protocol/pool application. This is deliberately split
-- from the larger scheduled-close frontend fixtures.
module ConnectionManagement.Negative.LiveTrackerAuxProtocol where
open import Data.Bool using (false)
open import Data.List.Relation.Unary.All using (All)
open import ConnectionManagement.Negative.MuxProtocolJobs using
 (r13; owner; rPayload; actual-initializer; initialized-fast-responder)
open import ConnectionManagement.Properties.LiveTrackerAuxCoreInitialized (λ _ → false) using (from-initial)
open import ConnectionManagement.Properties.LiveTrackerAuxUpdates (λ _ → false) using (Valid)
open import ConnectionManagement.Properties.LiveTrackerAuxContent (λ _ → false) using (PoolContent; Completion)
import ConnectionManagement.MuxProtocolJobs as P

-- The queue remains backed after its original child deregistered and exposed
-- its Async result; physical handle retention is part of the same certificate.
initialized-responder-content : Valid r13
initialized-responder-content = from-initial _ actual-initializer initialized-fast-responder
initialized-queued-content : All (λ item → Completion owner item r13) (P.Pool.completions (P.poolAt owner r13))
initialized-queued-content = PoolContent.queued (Valid.pools initialized-responder-content owner)
