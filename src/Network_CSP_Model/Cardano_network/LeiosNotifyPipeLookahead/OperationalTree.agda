{-# OPTIONS --guardedness #-}

-- Local source-operation tree compiler; no Haskell or wire-field lifting is assumed.
-- Internal selectors are data, not externally supplied transition proofs.
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module Cardano_network.LeiosNotifyPipeLookahead.OperationalTree
  (State Action Choice Result : Set)
  (Step : State → Action → State → Set)
  (Tau : State → State → Set)
  (visible : (s : State) (a : Action) → Maybe (Σ[ t ∈ State ] Step s a t))
  (hidden : (s : State) (c : Choice) → Maybe (Σ[ t ∈ State ] Tau s t))
  (visible-complete : ∀ {s a t} → Step s a t → map proj₁ (visible s a) ≡ just t)
  (hidden-complete : ∀ {s t} → Tau s t → Σ[ c ∈ Choice ] map proj₁ (hidden s c) ≡ just t)
  (outcome : State → Maybe Result)
  (step-live : ∀ {s a t} → Step s a t → outcome s ≡ nothing)
  (tau-live : ∀ {s t} → Tau s t → outcome s ≡ nothing) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Process_Trees using (PTree; AnyTypes; ContinueType; react; ret)
import Semantics.LTS
import Semantics.Deadlock
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)

-- A single operation channel retains the whole source action as its payload.
data Events : Set → Set where
  operation : Events Action

-- A single scheduler channel retains the complete executable selector.
data Branches : Set → Set where
  schedule : Branches Choice

-- Source-level trees have explicit successful or abnormal result values.
Proc : Set₁
Proc = PTree Events Branches Result

-- This LTS uses operation payloads rather than claiming native network metadata.
module LTS = Semantics.LTS {E = Events} {I = Branches}

-- Trace transport excludes the separate CSP termination tick.
module Traces = Semantics.Deadlock {E = Events} {I = Branches}

-- Forward declarations keep both visible and hidden recursion productive.
tree : State → Proc
offers : (s : State) (at : AnyTypes Events) → ContinueType at (Maybe Proc)
branches : (s : State) (at : AnyTypes Branches) → ContinueType at (Maybe Proc)

-- Successful outcomes terminate; otherwise simultaneous source offers remain enabled.
PTree.force (tree s) with outcome s
... | just r = ret r
... | nothing = react (offers s) (branches s)

-- Every visible offer is backed by a checked operational transition.
offers s (_ , operation) a with visible s a
... | nothing = nothing
... | just (t , _) = just (tree t)

-- Every silent branch is backed by a checked operational transition.
branches s (_ , schedule) c with hidden s c
... | nothing = nothing
... | just (t , _) = just (tree t)

-- Canonical source-operation events have no lossy payload projection.
event : Action → LTS.Event
event a = LTS.evLabel Action operation a

-- A live state unfolds to its simultaneous visible/internal node.
force-live : ∀ {s} → outcome s ≡ nothing →
  PTree.force (tree s) ≡ react (offers s) (branches s)
force-live {s} pr rewrite pr = refl

-- A finished state exposes exactly its recorded result.
force-result : ∀ {s r} → outcome s ≡ just r → PTree.force (tree s) ≡ ret r
force-result {s} pr rewrite pr = refl

-- Every independent visible rule is realized as an actual PTree visible move.
offer-target : ∀ {s a t} {pr : Step s a t} → visible s a ≡ just (t , pr) →
  offers s (Action , operation) a ≡ just (tree t)
offer-target {s} {a} eq rewrite eq = refl

-- A checked selector exposes precisely its target tree.
branch-target : ∀ {s c t} {pr : Tau s t} → hidden s c ≡ just (t , pr) →
  branches s (Choice , schedule) c ≡ just (tree t)
branch-target {s} {c} eq rewrite eq = refl

-- Every independent visible rule is realized as an actual PTree visible move.
visible-intro : ∀ {s a t} → Step s a t →
  tree s LTS.─[ LTS.ev (LTS.evl (event a)) ]─► tree t
visible-intro {s} {a} pr with visible s a in eq | visible-complete pr
... | nothing | ()
... | just (t , _) | refl = LTS.sVis (force-live (step-live pr)) (offer-target eq)

-- Every independent hidden rule is realized using a data-only scheduler choice.
hidden-intro : ∀ {s t} → Tau s t → tree s LTS.─[ LTS.τ ]─► tree t
hidden-intro {s} pr with hidden-complete pr
... | c , eq with hidden s c in chosen | eq
...   | nothing | ()
...   | just (t , _) | refl =
  LTS.sTau {i = (Choice , schedule)} {a = c} (force-live (tau-live pr)) (branch-target chosen)

-- A missing checked action offers no visible continuation.
offer-empty : ∀ {s a} → visible s a ≡ nothing → offers s (Action , operation) a ≡ nothing
offer-empty {s} {a} eq rewrite eq = refl

-- A missing scheduler action offers no silent continuation.
branch-empty : ∀ {s c} → hidden s c ≡ nothing → branches s (Choice , schedule) c ≡ nothing
branch-empty {s} {c} eq rewrite eq = refl

-- Invert an offer without assuming that the coinductive tree map is injective.
offer-elim : ∀ {s a P} → offers s (Action , operation) a ≡ just P →
  Σ[ t ∈ State ] (Step s a t × P ≡ tree t)
offer-elim {s} {a} eq with visible s a in selected
... | nothing with eq
...   | ()
offer-elim {s} {a} eq | just (t , pr) =
  t , pr , sym (just-injective eq)

-- Invert a scheduler offer with the same explicit continuation equality.
branch-elim : ∀ {s at} {c : proj₁ at} {P} → branches s at c ≡ just P →
  Σ[ t ∈ State ] (Tau s t × P ≡ tree t)
branch-elim {s} {(_ , schedule)} {c} eq with hidden s c in selected
... | nothing with eq
...   | ()
branch-elim {s} {(_ , schedule)} {c} eq | just (t , pr) =
  t , pr , sym (just-injective eq)

-- A returned node cannot perform a nontermination visible event.
no-visible-return : ∀ {s r a P} → PTree.force (tree s) ≡ ret r →
  tree s LTS.─[ LTS.ev (LTS.evl (event a)) ]─► P → ⊥
no-visible-return final (LTS.sVis eq _) with trans (sym final) eq
... | ()

-- A returned node cannot perform a silent step of either LTS kind.
no-hidden-return : ∀ {s r P} → PTree.force (tree s) ≡ ret r →
  tree s LTS.─[ LTS.τ ]─► P → ⊥
no-hidden-return final (LTS.sSil eq) with trans (sym final) eq
... | ()
no-hidden-return final (LTS.sTau eq _) with trans (sym final) eq
... | ()

-- All actual visible PTree steps arise from the independent operational rules.
visible-elim : ∀ {s a P} → tree s LTS.─[ LTS.ev (LTS.evl (event a)) ]─► P →
  Σ[ t ∈ State ] (Step s a t × P ≡ tree t)
visible-elim {s} st with outcome s in status
... | just r = ⊥-elim (no-visible-return (force-result status) st)
... | nothing with st
...   | LTS.sVis eq br with trans (sym (force-live status)) eq
...     | refl = offer-elim br

-- All actual silent PTree steps arise from the independent operational rules.
hidden-elim : ∀ {s P} → tree s LTS.─[ LTS.τ ]─► P →
  Σ[ t ∈ State ] (Tau s t × P ≡ tree t)
hidden-elim {s} st with outcome s in status
... | just r = ⊥-elim (no-hidden-return (force-result status) st)
... | nothing with st
...   | LTS.sSil eq with trans (sym (force-live status)) eq
...     | ()
hidden-elim {s} st | nothing | LTS.sTau {i = i} {a = c} eq br
  with trans (sym (force-live status)) eq
... | refl = branch-elim {at = i} {c = c} br

-- Independent finite source runs, including arbitrarily interleaved hidden work.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u es} → Tau s t → Run t es u → Run s es u
  visibleStep : ∀ {s t u a es} → Step s a t → Run t es u → Run s (a ∷ es) u

-- Every finite source execution is realized by the actual coinductive tree.
run-intro : ∀ {s es t} → Run s es t → tree s Traces.⟹∖√⟨ Data.List.map event es ⟩ tree t
run-intro stop = Traces.∖√-refl
run-intro (internal pr run) = Traces.∖√-τ (hidden-intro pr) (run-intro run)
run-intro (visibleStep pr run) = Traces.∖√-ev (visible-intro pr) (run-intro run)

-- Conversely every finite tree execution reconstructs a source run and exact endpoint.
run-elim : ∀ {s es P} → tree s Traces.⟹∖√⟨ Data.List.map event es ⟩ P →
  Σ[ t ∈ State ] (Run s es t × P ≡ tree t)
run-elim {es = []} Traces.∖√-refl = _ , stop , refl
run-elim (Traces.∖√-τ pr run) with hidden-elim pr
... | t , hiddenStep , refl with run-elim run
...   | u , source , eq = u , internal hiddenStep source , eq
run-elim {es = a ∷ es} (Traces.∖√-ev pr run) with visible-elim pr
... | t , visibleRule , refl with run-elim run
...   | u , source , eq = u , visibleStep visibleRule source , eq
