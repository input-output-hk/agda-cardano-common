{-# OPTIONS --safe #-}

-- Mathematical range obligations for finite counter representations, not a Haskell refinement.
module Cardano_network.LeiosNotifyPipeLookahead.Representation
  (Notification : Set) (message : Notification) where

open import Data.Bool using (false)
open import Data.Nat using (ℕ; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; <-irrefl)
open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.SequentialCompletion Notification message as Family

-- Sent work remains an outstanding deferred job until retirement and subsequent flush.
activeJob : S.Sender → ℕ
activeJob S.idle = 0
activeJob _ = 1

-- This counts registered unflushed jobs, including already completed ones.
deferred : S.State → ℕ
deferred s = S.waiting s + (activeJob (S.sender s) + S.completed s)

-- A finite nonnegative representation supplies an explicit maximum admissible value.
Fits : ℕ → ℕ → Set
Fits maximum value = value ≤ maximum

-- A proved live bound discharges a range obligation only when the target has enough room.
live-fits : ∀ {maximum value} → 1001 ≤ maximum → value ≤ 1001 → Fits maximum value
live-fits capacity bound = ≤-trans bound capacity

-- No finite maximum covers all histories, even with the pinned honest depth policy.
unbounded-deferred : (maximum : ℕ) →
  Σ[ actions ∈ List N.Action ] Σ[ t ∈ N.State ]
    (N.Run N.initial actions t ×
     (Fits maximum (deferred (D.serverState (N.driverState t))) → ⊥))
unbounded-deferred maximum = _ , Family.ready (Family.reader (suc maximum)) (suc maximum) ,
  Family.prefix (suc maximum) , λ impossible → <-irrefl refl impossible
