{-# OPTIONS --safe #-}

-- Duplicate enumeration removal preserves exact rows, opaque payload contents and all source moves.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacyTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; length)
import Data.List.Properties as List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy Bool Bool as Wrapper
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverTests as Existing

-- Repeated observations and a representative collision all describe the same two normal values.
repeated : List D.Event
repeated = D.serverSend (D.reply (S.normal true)) ∷ D.clientRecv (D.reply (S.normal true)) ∷
  D.serverSend (D.reply (S.normal false)) ∷ D.clientRecv (D.reply (S.normal true)) ∷ []

module A = Wrapper.ForInput Bool._≟_ false repeated

-- The old list remains unchanged, including its original duplicate-containing computation gate.
old-basis-unchanged : A.Original.basis ≡ false ∷ true ∷ true ∷ false ∷ true ∷ []
old-basis-unchanged = refl

-- The new callback enumeration contains each complete normal value once.
unique-basis : A.basis ≡ false ∷ true ∷ []
unique-basis = refl

-- The representative is retained even when the input already contains that exact value.
representative-retained : false ∈ A.basis
representative-retained = A.representative-present

-- The standard-library proof covers uniqueness of the entire candidate list.
unique-certified : Unique A.basis
unique-certified = A.duplicate-free

-- Membership at a discarded duplicate occurrence still supplies the same allowed normal choice.
last-duplicate-retained : true ∈ A.basis
last-duplicate-retained = A.original→unique (there (there (there (there (here refl)))))

-- Every retained normal still has an original exact value membership witness.
retained-origin : true ∈ A.Original.basis
retained-origin = A.unique→original (there (here refl))

-- All-state relation transport preserves actual normal callback selection without a reachability premise.
normal-step-forward : ∀ {p c cs sc pc ps rc rs} → A.B.Tau p
  (D.pair c (S.state S.awaitNext 0 S.claimed 0 false) cs sc pc ps rc rs)
  (D.pair c (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false) cs sc pc ps rc rs)
normal-step-forward = A.tau-forward
  (A.Original.B.serverCallback (A.Original.B.allowNormal (there (here refl))) (S.choose refl refl))

-- The inverse transport returns an exact old relation certificate at the same arbitrary states.
normal-step-backward : ∀ {p c cs sc pc ps rc rs} → A.Original.B.Tau p
  (D.pair c (S.state S.awaitNext 0 S.claimed 0 false) cs sc pc ps rc rs)
  (D.pair c (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false) cs sc pc ps rc rs)
normal-step-backward = A.tau-backward normal-step-forward

-- This actual fresh run retains both receives before their delayed corresponding send records.
delayed : List D.Event
delayed = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷
  D.clientSend D.request ∷ D.serverSend (D.reply (S.normal false)) ∷ []

module Fresh = Wrapper.ForInput Bool._≟_ false delayed

-- Repeated send/receive observations of one payload do not enlarge the hidden callback menu.
fresh-unique-size : length Fresh.basis ≡ 1
fresh-unique-size = refl

-- The original candidate size is left intact for callers relying on its previous definition.
fresh-old-size : length Fresh.Original.basis ≡ 3
fresh-old-size = refl

-- The same actual source witness now has a run in the unique-basis model without deleting any row.
fresh-source-adequacy : Fresh.BasisTrace S.nodeNext
fresh-source-adequacy = _ , Fresh.adequate Existing.delayed-send-records

-- Reversing the unique-basis transformation gives an original unrestricted run of the same full input.
fresh-source-roundtrip : Fresh.SourceTrace S.nodeNext
fresh-source-roundtrip = Fresh.basis→source fresh-source-adequacy

import Cardano_network.LeiosNotifyPipeLookahead.Model (List ℕ) as Lists
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel (List ℕ) ⊥ as ListDriver
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy (List ℕ) ⊥ as ListWrapper

-- The opaque normal payload may itself contain ordered duplicate entries.
ordered-payload : List ℕ
ordered-payload = 1 ∷ 2 ∷ 1 ∷ []

-- Repetition of whole notifications is independent of repeated entries inside each notification.
list-input : List ListDriver.Event
list-input = ListDriver.serverSend (ListDriver.reply (Lists.normal ordered-payload)) ∷
  ListDriver.clientRecv (ListDriver.reply (Lists.normal ordered-payload)) ∷ []

module Payload = ListWrapper.ForInput (List.≡-dec Nat._≟_) [] list-input

-- Enumeration deduplication preserves every internal payload entry, order and duplicate exactly.
internal-duplicates-preserved : Payload.basis ≡ [] ∷ (1 ∷ 2 ∷ 1 ∷ []) ∷ []
internal-duplicates-preserved = refl

-- The visible source list is untouched, including its two complete payload occurrences.
visible-occurrences-preserved : list-input ≡
  ListDriver.serverSend (ListDriver.reply (Lists.normal (1 ∷ 2 ∷ 1 ∷ []))) ∷
  ListDriver.clientRecv (ListDriver.reply (Lists.normal (1 ∷ 2 ∷ 1 ∷ []))) ∷ []
visible-occurrences-preserved = refl

module Empty = ListWrapper.ForInput (List.≡-dec Nat._≟_) [] []

-- Transforming existing runs requires no inhabited Return carrier, even after deduplication.
empty-return-prefix : Empty.B.Run Lists.genericNext ListDriver.initial [] ListDriver.initial
empty-return-prefix = Empty.adequate ListDriver.stop
