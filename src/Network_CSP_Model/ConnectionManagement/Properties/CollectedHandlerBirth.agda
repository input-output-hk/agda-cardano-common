{-# OPTIONS --guardedness #-}

-- Thin composition of collected physical membership and the existing actual
-- fork inversion. Keep the large birth closure out of the frontend induction.
module ConnectionManagement.Properties.CollectedHandlerBirth where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.Maybe using (just)
open import Data.Product using (Σ; _,_)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain using (ErrorId; HandleId)
import ConnectionManagement.State as S
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Properties.HandlerAuxFrontend as Membership
import ConnectionManagement.Properties.HandlerBirthBacking as Birth

module Frontend (b io : ErrorId → Bool) (canInitiate : HandleId → ℕ → Bool) where
 private module T = SharedModel.Protocols b io canInitiate using (Runs; initialize)
 private module W = ExitModel b using (shutdown)
 private module R = UnwindModel b using (base)
 private module Member = Membership.Frontend b io canInitiate using (initialized-member; unwind)
 private module Back = Birth.Frontend b io canInitiate using (Backing; initialized-birth)
 open Member public using (initialized-member)
 initialized-birth : ∀ {c g start events current w} → T.initialize c g ≡ just start → T.Runs start events current →
   w ∈ Close.collected (W.shutdown (R.base (Member.unwind current))) →
   Σ S.HandlerStart (λ captured → Back.Backing start current events w captured)
 initialized-birth {c} {g} {start} {events} {current} {w} initialized path member with
   Member.initialized-member {c = c} {g = g} {start = start} {events = events} {current = current} {w = w} initialized path member
 ... | thread , found = H.captured thread , Back.initialized-birth
   {c = c} {g = g} {start = start} {events = events} {current = current} {w = w} {thread = thread} initialized path found
