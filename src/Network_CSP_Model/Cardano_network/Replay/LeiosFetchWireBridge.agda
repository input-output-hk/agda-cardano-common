{-# OPTIONS --guardedness #-}

-- Observation-guided simulation: decoder premises are spent at logged steps.
module Cardano_network.Replay.LeiosFetchWireBridge
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open import Data.Nat using (ℕ)
open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; map; mapMaybe)
import Data.List.Properties
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Process_Trees using (PTree)
open import Semantics.LTS {E = E} {I = I} using (Event; _─[_]─►_; τ; ev; evl)
open import Semantics.Deadlock {E = E} {I = I} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Cardano_network.Replay.LeiosFetchSession using (St) renaming (E to LogEvent)
open import Cardano_network.Replay.LeiosFetchObs using (E♭; forget)
open import Cardano_network.Replay.LeiosFetchWireOK using (WireMsg; WireOK)
open import Semantics.Replay using (module Traces)
import Cardano_network.Replay.LeiosFetchSession as S

module _ {ℓr ℓρ : Level} {R : Set ℓr} (k : ℕ)
  (cls : Event → Maybe E♭) (Rel : PTree E I R → St → Set ℓρ) where
  open S.Spec k using (leiosFetch)
  open Traces leiosFetch using (_⇒⟨_⟩_; done; ⇒-++)

  -- An unlogged event advances silently; a logged event consumes its wire premise.
  data Match (P′ : PTree E I R) (s : St) (v : Maybe E♭) : Set (ℓr ⊔ ℓρ ⊔ ℓ ⊔ ℓe ⊔ ℓi) where
    -- An unlogged event uses only silent session transitions.
    silent : ∀ {s′} → v ≡ nothing → s ⇒⟨ [] ⟩ s′ → Rel P′ s′ → Match P′ s v
    -- An observed message is matched after checking its receive-side summary fields.
    logged : ∀ {a} → v ≡ just a → ((e : LogEvent) → forget e ≡ a → WireMsg e →
      Σ[ s′ ∈ St ] (s ⇒⟨ e ∷ [] ⟩ s′ × Rel P′ s′)) → Match P′ s v

  -- Conditional simulation keeps the original session semantics unchanged.
  record Sim : Set (lsuc (ℓr ⊔ ℓρ ⊔ ℓ ⊔ ℓe ⊔ ℓi)) where
    field
      -- Internal transitions do not consume a logged event.
      sim-τ : ∀ {P P′ s} → Rel P s → P ─[ τ ]─► P′ →
        Σ[ s′ ∈ St ] (s ⇒⟨ [] ⟩ s′ × Rel P′ s′)
      -- Visible transitions are matched with decoder evidence when logged.
      sim-ev : ∀ {P P′ s e} → Rel P s → P ─[ ev (evl e) ]─► P′ → Match P′ s (cls e)

  -- A complete observed run is legal whenever all receive-side summary fields are legal.
  sound : Sim → ∀ {P P′ s t es} → Rel P s → P ⟹∖√⟨ t ⟩ P′ →
    mapMaybe cls t ≡ map forget es → WireOK es → Σ[ s′ ∈ St ] (s ⇒⟨ es ⟩ s′ × Rel P′ s′)
  sound sm {es = []} r ∖√-refl o [] = _ , done , r
  sound sm {es = _ ∷ _} r ∖√-refl () w
  sound sm r (∖√-τ step run) o w with Sim.sim-τ sm r step
  ... | s₁ , p , r₁ with sound sm r₁ run o w
  ... | s′ , q , r′ = s′ , ⇒-++ p q , r′
  sound sm r (∖√-ev {e = e} step run) o w with Sim.sim-ev sm r step
  ... | silent eq p r₁ rewrite eq with sound sm r₁ run o w
  ... | s′ , q , r′ = s′ , ⇒-++ p q , r′
  sound sm {es = []} r (∖√-ev step run) o [] | logged eq f rewrite eq with o
  ... | ()
  sound sm {es = e ∷ es} r (∖√-ev step run) o (w ∷ ws) | logged eq f rewrite eq
    with Data.List.Properties.∷-injective o
  ... | same , rest with f e (sym same) w
  ... | s₁ , p , r₁ with sound sm r₁ run rest ws
  ... | s′ , q , r′ = s′ , ⇒-++ p q , r′
