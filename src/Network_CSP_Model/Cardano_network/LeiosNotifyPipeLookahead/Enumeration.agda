{-# OPTIONS --safe #-}

-- Hidden enumeration is proved complete for the independent source-model rules.
module Cardano_network.LeiosNotifyPipeLookahead.Enumeration
  (Notification : Set) where

open import Data.Bool using (true)
import Data.Bool.Properties as Bool
open import Data.List using (List; map; _++_)
import Data.List.Properties as List
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- Erasing certificates gives precisely the executable hidden target list.
targets : State → List State
targets s = map proj₁ (internalMoves s)

-- Every target retains a proof of the independent hidden relation.
target-sound : ∀ {s t} → t ∈ targets s → Tau s t
target-sound {s} mem with ∈-map⁻ proj₁ mem
... | (u , pr) , member , refl = pr

-- Reader targets embed in the combined independent scheduling menu.
reader-listed : ∀ {s t} → t ∈ map proj₁ (readerMoves s) → t ∈ targets s
reader-listed {s} {t} mem =
  subst (t ∈_) (sym (List.map-++ proj₁ (readerMoves s) (senderMoves s))) (∈-++⁺ˡ mem)

-- Sender targets embed without giving the reader artificial priority.
sender-listed : ∀ {s t} → t ∈ map proj₁ (senderMoves s) → t ∈ targets s
sender-listed {s} {t} mem =
  subst (t ∈_) (sym (List.map-++ proj₁ (readerMoves s) (senderMoves s)))
    (∈-++⁺ʳ (map proj₁ (readerMoves s)) mem)

-- A successful guard includes its target independently of proof identity.
guarded-listed : ∀ {s t} {P : Set} (dec : Dec P) {build : P → Tau s t} →
  P → t ∈ map proj₁ (internalWhen dec build)
guarded-listed (yes _) _ = here refl
guarded-listed (no noP) pr = ⊥-elim (noP pr)

-- No independent source-model scheduling step is lost by enumeration.
target-complete : ∀ {s t} → Tau s t → t ∈ targets s
target-complete {s = s} admitted = reader-listed {s = s} (here refl)
target-complete {s = s} excessive = reader-listed {s = s} (there (here refl))
target-complete {s = s} registered = reader-listed {s = s} (here refl)
target-complete {s = s} setQuit = reader-listed {s = s} (here refl)
target-complete {s = s} (claim {r = r} pr) = sender-listed {s = s} (guarded-listed (active r Bool.≟ true) pr)
target-complete {s = s} (cancel {r = r} pr) = sender-listed {s = s} (guarded-listed (active r Bool.≟ true) pr)
target-complete {s = s} (retire {r = r} pr) = sender-listed {s = s} (guarded-listed (active r Bool.≟ true) pr)
target-complete {s = s} flush = reader-listed {s = s} (here refl)
target-complete {s = s} drained = reader-listed {s = s} (here refl)
target-complete {s = s} abort = reader-listed {s = s} (here refl)
