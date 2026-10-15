{-# OPTIONS --guardedness #-}

-- Preserving an old chain neither attaches a new worker nor bypasses guards.
module ConnectionManagement.Negative.HandlerAll where

open import Data.List using (map; replicate; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (put)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.Fixtures using (binding)
open import ConnectionManagement.CSP.HandlerAll
open import ConnectionManagement.Scenarios.Admission using (w₀; w₁; child₀; child₁; r₁)
open import ConnectionManagement.Scenarios.Handshake using (info)
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- The second child was forked but never attached to the lifecycle model.
no-implicit-attachment : ¬ TrackedChain child₁ secondEnd
no-implicit-attachment (f , () , chain)

-- Reusing the old child's identity is explicitly rejected at the fork boundary.
reusedChild : Configuration
reusedChild = record second4 { world = record (world second4)
  { admissions = put w₁ (admissionWorker (record r₁ { child = child₀ })
      (forkHandler (lease w₁ binding) (ident 1) (ident 1))) (admissions (world second4)) } }
reused-child-refused : advance (admissionStep w₁ S.fork) reusedChild ≡ nothing
reused-child-refused = refl
no-reused-child-trace : ¬ traces (Process reusedChild) (map label (admissionStep w₁ S.fork ∷ []))
no-reused-child-trace = refused-extension {as = []} done reused-child-refused

-- Reading the promise is non-consuming, but the next control phase rejects replay.
repeated-read-refused : advance (handshakeStep w₀ H.readResult) consumer1 ≡ nothing
repeated-read-refused = refl
no-repeated-read-trace : ¬ traces (Process consumer1) (map label (handshakeStep w₀ H.readResult ∷ []))
no-repeated-read-trace = refused-extension {as = []} done repeated-read-refused

fullQueue : Configuration
fullQueue = record consumer3 { world = record (world consumer3)
  { inboundInfo = replicate 100 (newConnection info) } }
full-queue-refused : advance (handshakeStep w₀ H.enqueueInbound) fullQueue ≡ nothing
full-queue-refused = refl
no-full-queue-trace : ¬ traces (Process fullQueue) (map label (handshakeStep w₀ H.enqueueInbound ∷ []))
no-full-queue-trace = refused-extension {as = []} done full-queue-refused
