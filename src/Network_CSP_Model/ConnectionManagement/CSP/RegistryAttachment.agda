{-# OPTIONS --guardedness #-}

-- Visible publication-to-attachment schedules retain the certified mux identity.
module ConnectionManagement.CSP.RegistryAttachment where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action)
open import ConnectionManagement.Properties.RegistryPublication using (Sound; publication)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; attachment; publication-attachment)
import ConnectionManagement.Properties.OriginRegistry as Registry
open import ConnectionManagement.CSP.OriginRegistry using (Process; exec-inv)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Split a checked registry execution at an explicit visible-action boundary.
split-exec : ∀ xs {ys s end} → Executes s (xs ++ ys) end →
  Σ State (λ middle → Executes s xs middle × Executes middle ys end)
split-exec [] path = _ , done , path
split-exec (x ∷ xs) (next eq path) with split-exec xs path
... | middle , before , after = middle , next eq before , after

-- Both interleaving lists may contain any actions accepted by the registry.
-- The recovered prefix, not just its labels, carries the resource obligation.
raw-attachment : ∀ {c P Q} prefix before after w hid f err →
  Process (start c) ⟹⟨ map label prefix ⟩ P →
  P ⟹⟨ map label (publication w hid f ∷ (before ++ (attachment w err ∷ after))) ⟩ Q →
  Σ State (λ s → Σ State (λ sPub → Σ State (λ sEnd →
    P ≡ Process s × Q ≡ Process sEnd ×
    Σ (Executes (start c) prefix s) (λ path → Registry.Supported path →
      Σ (Sound w hid f s sPub) (λ certificate → Attached w hid (Sound.ticket certificate) f (machine sEnd))))))
raw-attachment prefix before after w hid f err reached continuation with exec-inv reached
... | s , refl , prefixPath with exec-inv continuation
...   | sEnd , endpoint , next {s₁ = sPub} published rest with split-exec before rest
...     | sReady , waiting , next attached suffix =
  s , sPub , sEnd , refl , endpoint , prefixPath , λ supported →
    publication-attachment w hid f err prefixPath supported published waiting attached suffix
