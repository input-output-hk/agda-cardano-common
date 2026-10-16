{-# OPTIONS --guardedness #-}

-- Publication soundness for an actual visible CSP step after a raw prefix.
module ConnectionManagement.CSP.RegistryPublication where

open import Data.List using (List; map)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action)
open import ConnectionManagement.Properties.RegistryPublication using (publication; Sound; reachable-publication)
import ConnectionManagement.Properties.OriginRegistry as Registry
open import ConnectionManagement.CSP.OriginRegistry using (Process; all-exec-inv; step-inv)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (_⟹⟨_⟩_)

-- Keep both actual process endpoints. Resource evidence belongs to the recovered
-- prefix; it is not inferred merely from the existence of a visible trace.
raw-publication : ∀ {c es P Q} w hid f →
  Process (start c) ⟹⟨ es ⟩ P → P ─[ ev (label (publication w hid f)) ]─► Q →
  Σ (List Action) (λ as → Σ State (λ s → Σ State (λ s′ →
    es ≡ map label as × P ≡ Process s × Q ≡ Process s′ ×
    Σ (Executes (start c) as s) (λ path → Registry.Supported path → Sound w hid f s s′))))
raw-publication w hid f prefix published with all-exec-inv prefix
... | as , s , labels , refl , path with step-inv published
...   | s′ , accepted , endpoint =
  as , s , s′ , labels , refl , endpoint , path , λ supported → reachable-publication w hid f path supported accepted
