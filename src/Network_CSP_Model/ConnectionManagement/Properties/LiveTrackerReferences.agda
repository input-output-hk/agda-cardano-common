{-# OPTIONS --guardedness #-}

-- A necessary component of CM-I4c for the live physical registry. Existing
-- resource certificates protect captures, not current CM map ownership. The
-- initializer is deliberately the same broad initializer as C3's theorem.
module ConnectionManagement.Properties.LiveTrackerReferences where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Product using (_×_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.ServerPeers as Model

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 open Model.Protocols b io canInitiate using
   (Runtime; initialize; Runs; sourceOf; base; physical)

 -- Follow the same live physical projection used by ServerPeers.Protocols.
 physicalState : Runtime → B.State
 physicalState s = P.U.base (P.base (physical (base s)))
 shared : Runtime → S.State
 shared s = M.world (O.core (sourceOf s))

 -- Every captured registration agrees exactly, entry/socket resources exist,
 -- and the original promise is allocated (it need not have a result yet).
 PhysicalReferences : Runtime → Set
 PhysicalReferences s = ∀ w thread →
   lookup w (B.threads (physicalState s)) ≡ just thread →
   Facts w (H.captured thread) (shared s) ×
   S.handlerPromise (H.captured thread) ∈ S.promises (shared s)

 -- This quantifies over the unchanged C3 initializer, without imposing an
 -- O.initial profile or an extra invariant on supplied outbound continuations.
 Universal : Set
 Universal = ∀ c g {start events s} →
   initialize c g ≡ just start → Runs start events s → PhysicalReferences s
