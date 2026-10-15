{-# OPTIONS --guardedness #-}

-- Worker attribution stays visible in the CSP alphabet; erasure is explicit.
module ConnectionManagement.CSP.OriginRegistry where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Process_Trees
open PTree
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; erase)
import ConnectionManagement.Properties.OriginRegistry as Projection
import ConnectionManagement.CSP.Correspondence as OpenProof
import ConnectionManagement.CSP.Process as OpenProcess
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; action; channel-≟; Proc; label)

open import CSP.Operators channel-≟ using (viewV)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

-- Check attribution and the monitor before exposing the attributed label.
Process : State → Proc
force (Process s) = react
  (λ where (_ , action) a → case step a s of λ where
    nothing → nothing
    (just s′) → just (Process s′))
  (λ _ _ → nothing)

step-intro : ∀ {c c′ a} → step a c ≡ just c′ →
  Process c ─[ ev (label a) ]─► Process c′
step-intro {c} {c′} {a} eq = sVis refl branch
  where
  branch : viewV (force (Process c)) (Action , action) a ≡ just (Process c′)
  branch rewrite eq = refl

step-inv : ∀ {c a P} → Process c ─[ ev (label a) ]─► P →
  Σ State (λ c′ → step a c ≡ just c′ × P ≡ Process c′)
step-inv {c} {a} (sVis refl br) with step a c | br
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
  Σ State (λ c′ → P ≡ Process c′ × Executes c as c′)
exec-inv {as = []} ⟹-refl = _ , refl , done
exec-inv (⟹-τ st rest) = ⊥-elim (no-τ st)
exec-inv {as = a ∷ as} (⟹-ev st rest) with step-inv st
... | c₁ , eq , refl with exec-inv {as = as} rest
...   | c′ , endpoint , path = c′ , endpoint , next eq path

trace-intro : ∀ {c as c′} → Executes c as c′ → traces (Process c) (map label as)
trace-intro path = _ , exec-intro path

trace-inv : ∀ {c as} → traces (Process c) (map label as) →
  Σ State (λ c′ → Executes c as c′)
trace-inv (_ , tr) with exec-inv tr
... | c′ , _ , path = c′ , path

-- Every raw process trace is accounted for, including exclusion of tick events.
all-exec-inv : ∀ {c es P} → Process c ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ c′ →
    es ≡ map label as × P ≡ Process c′ × Executes c as c′))
all-exec-inv ⟹-refl = [] , _ , refl , refl , done
all-exec-inv (⟹-τ st _) = ⊥-elim (no-τ st)
all-exec-inv (⟹-ev {e = √ _} st _) = ⊥-elim (no-tick st)
all-exec-inv (⟹-ev {e = evl (evLabel _ action a)} st rest) with step-inv st
... | c₁ , eq , refl with all-exec-inv rest
...   | as , c′ , refl , endpoint , path = a ∷ as , c′ , refl , endpoint , next eq path

-- Erasure gives a trace of the unchanged open machine, across alphabets.
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
trace-projects : ∀ {c es} → traces (Process c) es →
  Σ (List Action) (λ as → es ≡ map label as ×
    open-traces (OpenProcess.Process (machine c)) (map OpenProcess.label (map erase as)))
trace-projects (_ , tr) with all-exec-inv tr
... | as , c′ , refl , same , path = as , refl , OpenProof.trace-intro (Projection.exec-projects path)

-- Evidence must cover each allocation in this very execution, not another trace.
raw-invariant : ∀ {c es P} → Process (start c) ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ s →
    es ≡ map label as × P ≡ Process s ×
    Σ (Executes (start c) as s) (λ path → Projection.Supported path → Projection.Invariant s)))
raw-invariant execution with all-exec-inv execution
... | as , s , labels , endpoint , path =
  as , s , labels , endpoint , path , Projection.reachable path

open import Data.Maybe.Properties using (just-injective)

-- Deterministic monitor prefixes cannot be extended by a refused action.
reject-execution : ∀ {c as c′ a end} → Executes c as c′ → step a c′ ≡ nothing →
  ¬ Executes c (as ++ (a ∷ [])) end
reject-execution done disabled (next enabled done) = impossible (trans (sym disabled) enabled)
  where
  impossible : ∀ {s : State} → nothing ≡ just s → ⊥
  impossible ()
reject-execution (next eq prefix) disabled (next enabled rest)
  with just-injective (trans (sym eq) enabled)
... | refl = reject-execution prefix disabled rest
refused-extension : ∀ {c as c′ a} → Executes c as c′ → step a c′ ≡ nothing →
  ¬ traces (Process c) (map label (as ++ (a ∷ [])))
refused-extension prefix disabled tr with trace-inv tr
... | end , path = reject-execution prefix disabled path
