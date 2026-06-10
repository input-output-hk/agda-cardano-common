{-# OPTIONS --guardedness #-}
module CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_DeadlockFree where

open import Data.Nat using (ℕ; suc; _<?_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (n<1+n; <⇒≢; ≮⇒≥; ≤-antisym)
open import Data.Fin using (Fin; toℕ; fromℕ<) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Fin.Properties using (toℕ-fromℕ<; toℕ<n)
open import Data.Product using (_,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Interaction_Trees
open ITree
open import ITree_Relations.LTS
open import ITree_Relations.Deadlock

import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP            as M
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_SysStates  as SysSt
import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_SystemP_Progress   as Prog

module DF (m : ℕ) where
  open M.Sys m
    using (SYSTEM′asym; asymFirst; asymSecond; _⊕1)
  open SysSt.SysSt m
    using (SYSTEM′-valid; sysState; Config; ValidCfg)
  open Prog.Prog m
    using (asym-no-deadlock)

  -- successor-mod-n has no fixed point (n = suc (suc m) ≥ 2)
  ⊕1≢ : ∀ (i : Fin (suc (suc m))) → i ⊕1 ≢ i
  ⊕1≢ i eq with suc (toℕ i) <? suc (suc m)
  ... | yes p = <⇒≢ (n<1+n (toℕ i)) (sym lemma)
    where
      lemma : suc (toℕ i) ≡ toℕ i
      lemma = trans (sym (toℕ-fromℕ< p)) (cong toℕ eq)
  ... | no ¬p = lemma
    where
      -- i ⊕1 = fzero, so eq : fzero ≡ i, hence cong toℕ eq : 0 ≡ toℕ i.
      -- ¬p + toℕ<n force toℕ i ≡ suc m ≠ 0.
      0≡i : 0 ≡ toℕ i
      0≡i = cong toℕ eq
      sm≤i : suc m ≤ toℕ i
      sm≤i with ≮⇒≥ ¬p
      ... | s≤s h = h
      i≤sm : toℕ i ≤ suc m
      i≤sm with toℕ<n i
      ... | s≤s h = h
      i≡sm : toℕ i ≡ suc m
      i≡sm = ≤-antisym i≤sm sm≤i
      lemma : ⊥
      lemma with trans 0≡i i≡sm
      ... | ()

  asym-fs≢ : ∀ i → asymFirst i ≢ asymSecond i
  asym-fs≢ i with i Fin.≟ fzero
  ... | yes refl = ⊕1≢ fzero
  ... | no  _    = λ eq → ⊕1≢ i (sym eq)

  deadlock-free-asym : DeadlockFree SYSTEM′asym
  deadlock-free-asym bs stuck with SYSTEM′-valid asym-fs≢ bs
  ... | (cfg , refl , V) = asym-no-deadlock V stuck

module Sanity where
  open M.Sys 0 using (SYSTEM′asym)
  open DF 0    using (deadlock-free-asym)

  -- The asymmetric DP system at n = 2 is deadlock-free:
  _ : DeadlockFree SYSTEM′asym
  _ = deadlock-free-asym
