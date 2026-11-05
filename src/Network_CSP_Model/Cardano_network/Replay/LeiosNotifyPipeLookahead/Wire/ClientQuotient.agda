{-# OPTIONS --safe #-}

-- Exact generic successful-callback local client hook language and its exhaustive decision.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientQuotient
  (Notification Return : Set) where

open import Data.List using (List)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as Q
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientSound Notification Return as Sound
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientComplete Notification Return as Complete
open Q.Observation Return

-- An accepted source trace retains every callback choice and a genuine initial source run.
SourceTrace : List Q.Wire → Set
SourceTrace rows = Σ[ actions ∈ List C.Action ]
  (Σ[ target ∈ C.State ] (C.Run C.initial actions target × wire actions ≡ rows))

-- Soundness needs no inhabitance assumption on the source return carrier.
source→quotient : ∀ {rows} → SourceTrace rows → Q.HasTrace Q.initial rows
source→quotient (actions , target , run , refl) = Sound.initial-sound run

-- Terminating quotient traces are realizable when the caller supplies an actual return value.
quotient→source : Return → ∀ {rows} → Q.HasTrace Q.initial rows → SourceTrace rows
quotient→source value = Complete.initial-complete value

-- The two languages coincide for every explicitly inhabited successful-return profile.
equivalence : Return → ∀ {rows} → (SourceTrace rows → Q.HasTrace Q.initial rows) ×
  (Q.HasTrace Q.initial rows → SourceTrace rows)
equivalence value = source→quotient , quotient→source value

-- Rejection is exhaustive for the initial source language, rather than failed certificate search.
decide-source : Return → (rows : List Q.Wire) → Dec (SourceTrace rows)
decide-source value rows with Q.decide Q.initial rows
... | yes admitted = yes (quotient→source value admitted)
... | no denied = no λ source → denied (source→quotient source)
