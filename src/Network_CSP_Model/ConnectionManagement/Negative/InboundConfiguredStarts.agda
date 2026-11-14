{-# OPTIONS --guardedness #-}

-- Full-bundle waiter registration and the traffic-triggered Any responder.
module ConnectionManagement.Negative.InboundConfiguredStarts where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
open import Data.Product using (_,_)
import Data.Maybe as Maybe
import ConnectionManagement.Rules.MuxRuntime as MR
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Negative.InboundConfiguredStart1 as Waiters
import ConnectionManagement.Negative.InboundConfiguredStart5 as Any
import ConnectionManagement.Negative.InboundConfiguredStart17 as Started

six-waiters : Maybe.map (λ m → length (MR.waiting m))
  (P.muxAt (ident 0) (B.physical Waiters.s3)) ≡ just 6
six-waiters = refl
no-eager-responder : Maybe.map MR.runningJobs
  (P.muxAt (ident 0) (B.physical Waiters.s3)) ≡ just []
no-eager-responder = refl
any-follows-ordinary-demand : Maybe.map MR.runningJobs
  (P.muxAt (ident 0) (B.physical Any.s3)) ≡ just (8 ∷ 2 ∷ [])
any-follows-ordinary-demand = refl
any-captured-number-direction : Maybe.map (λ j → Types.protocolNumber j , Types.direction j)
  (P.collector (ident 11) (B.physical Any.s3)) ≡ just (8 , MR.responderJob)
any-captured-number-direction = refl
all-six-bound-before-contracts : length (B.bindings Started.s2) ≡ 6
all-six-bound-before-contracts = refl
six-running : Maybe.map (λ m → length (MR.runningJobs m))
  (P.muxAt (ident 0) (B.physical Started.s2)) ≡ just 6
six-running = refl
no-waiters-after-starts : Maybe.map MR.waiting
  (P.muxAt (ident 0) (B.physical Started.s2)) ≡ just []
no-waiters-after-starts = refl
