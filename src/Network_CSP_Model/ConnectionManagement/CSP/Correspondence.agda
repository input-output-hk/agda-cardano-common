{-# OPTIONS --guardedness #-}

-- Exact step and finite-trace correspondence for the diagnostic process.
-- This relates the two model representations, not the Haskell source and model.
module ConnectionManagement.CSP.Correspondence where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Process_Trees
open PTree
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import CSP.Operators channel-≟ using (viewV)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

step-intro : ∀ {c c′ a} → advance a c ≡ just c′ →
  Process c ─[ ev (label a) ]─► Process c′
step-intro {c} {c′} {a} eq = sVis refl branch
  where
  branch : viewV (force (Process c)) (Action , action) a ≡ just (Process c′)
  branch rewrite eq = refl

step-inv : ∀ {c a P} → Process c ─[ ev (label a) ]─► P →
  Σ Configuration (λ c′ → advance a c ≡ just c′ × P ≡ Process c′)
step-inv {c} {a} (sVis refl br) with advance a c | br
... | just c′ | refl = c′ , refl , refl

-- These facts apply only BEFORE hiding; they are not subsystem liveness results.
no-τ : ∀ {c P} → ¬ (Process c ─[ τ ]─► P)
no-τ (sSil ())
no-τ (sTau refl ())

no-tick : ∀ {c P r} → ¬ (Process c ─[ ev (√ r) ]─► P)
no-tick (sRet ())

exec-intro : ∀ {c as c′} → Executes c as c′ →
  Process c ⟹⟨ map label as ⟩ Process c′
exec-intro done = ⟹-refl
exec-intro (next eq rest) = ⟹-ev (step-intro eq) (exec-intro rest)

exec-inv : ∀ {c as P} → Process c ⟹⟨ map label as ⟩ P →
  Σ Configuration (λ c′ → P ≡ Process c′ × Executes c as c′)
exec-inv {as = []} ⟹-refl = _ , refl , done
exec-inv (⟹-τ st rest) = ⊥-elim (no-τ st)
exec-inv {as = a ∷ as} (⟹-ev st rest) with step-inv st
... | c₁ , eq , refl with exec-inv {as = as} rest
...   | c′ , endpoint , path = c′ , endpoint , next eq path

trace-intro : ∀ {c as c′} → Executes c as c′ → traces (Process c) (map label as)
trace-intro path = _ , exec-intro path

trace-inv : ∀ {c as} → traces (Process c) (map label as) →
  Σ Configuration (λ c′ → Executes c as c′)
trace-inv (_ , tr) with exec-inv tr
... | c′ , _ , path = c′ , path

-- Every raw process trace is accounted for, including exclusion of tick events.
all-exec-inv : ∀ {c es P} → Process c ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ Configuration (λ c′ →
    es ≡ map label as × P ≡ Process c′ × Executes c as c′))
all-exec-inv ⟹-refl = [] , _ , refl , refl , done
all-exec-inv (⟹-τ st _) = ⊥-elim (no-τ st)
all-exec-inv (⟹-ev {e = √ _} st _) = ⊥-elim (no-tick st)
all-exec-inv (⟹-ev {e = evl (evLabel _ action a)} st rest) with step-inv st
... | c₁ , eq , refl with all-exec-inv rest
...   | as , c′ , refl , endpoint , path = a ∷ as , c′ , refl , endpoint , next eq path

-- A disabled machine action is a singleton stable refusal of the RAW process.
-- This neither classifies why advance returned nothing nor proves global deadlock.
singleton-refusal : ∀ {c a} → advance a c ≡ nothing →
  Refuses (Process c) (λ e → e ≡ label a)
singleton-refusal {c} {a} disabled = (λ _ _ → refl) , reject
  where
  impossible : ∀ {c′ : Configuration} → nothing ≡ just c′ → ⊥
  impossible ()
  reject : ∀ e → e ≡ label a → ¬ (Σ Proc (λ P → Process c ─[ ev e ]─► P))
  reject _ refl (_ , st) with step-inv st
  ... | c′ , enabled , _ = impossible (trans (sym disabled) enabled)

-- A checked prefix followed by its refused action cannot be a raw process trace.
-- Use machine determinism and splitting, avoiding concrete whole-run reduction.
refused-extension : ∀ {c as c′ a} → Executes c as c′ → advance a c′ ≡ nothing →
  ¬ traces (Process c) (map label (as ++ (a ∷ [])))
refused-extension {c} {as} prefix disabled tr with trace-inv {c = c} {as = as ++ (_ ∷ [])} tr
... | end , path with exec-split as path
...   | middle , left , next enabled done with exec-deterministic prefix left
...     | refl = impossible (trans (sym disabled) enabled)
  where
  impossible : nothing ≡ just end → ⊥
  impossible ()
