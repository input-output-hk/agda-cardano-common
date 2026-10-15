{-# OPTIONS --guardedness #-}

-- Worker attribution stays visible in the CSP alphabet; erasure is explicit.
module ConnectionManagement.CSP.AttributedOrigin where

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
open import ConnectionManagement.Rules.OriginMonitor using (Target; State; start; workerId)
open import ConnectionManagement.Rules.AttributedOrigin
import ConnectionManagement.Properties.AttributedOrigin as Projection
import ConnectionManagement.CSP.OriginMonitor as Single
import ConnectionManagement.CSP.Process as OpenProcess
open import Relation.Nullary using (Dec; yes)

data Channel : Set → Set where
  action : Channel Action
channel-≟ : (x y : AnyTypes Channel) → Dec (x ≡ y)
channel-≟ (_ , action) (_ , action) = yes refl
Proc : Set₁
Proc = PTree Channel (ExtI Channel) ⊤

open import CSP.Operators channel-≟ using (viewV)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

-- Attribution is a visible payload; it is not hidden as a silent action.
label : Action → Event√ ⊤
label a = evl (evLabel Action action a)

-- Check attribution and the monitor before exposing the attributed label.
Process : Target → State → Proc
force (Process t s) = react
  (λ where (_ , action) a → case step t a s of λ where
    nothing → nothing
    (just s′) → just (Process t s′))
  (λ _ _ → nothing)

step-intro : ∀ {t c c′ a} → step t a c ≡ just c′ →
  Process t c ─[ ev (label a) ]─► Process t c′
step-intro {t} {c} {c′} {a} eq = sVis refl branch
  where
  branch : viewV (force (Process t c)) (Action , action) a ≡ just (Process t c′)
  branch rewrite eq = refl

step-inv : ∀ {t c a P} → Process t c ─[ ev (label a) ]─► P →
  Σ State (λ c′ → step t a c ≡ just c′ × P ≡ Process t c′)
step-inv {t} {c} {a} (sVis refl br) with step t a c | br
... | just c′ | refl = c′ , refl , refl

-- These facts apply only BEFORE hiding; they are not subsystem liveness results.
no-τ : ∀ {t c P} → ¬ (Process t c ─[ τ ]─► P)
no-τ (sSil ())
no-τ (sTau refl ())

no-tick : ∀ {t c P r} → ¬ (Process t c ─[ ev (√ r) ]─► P)
no-tick (sRet ())

exec-intro : ∀ {t c as c′} → Executes t c as c′ →
  Process t c ⟹⟨ map label as ⟩ Process t c′
exec-intro done = ⟹-refl
exec-intro (next eq rest) = ⟹-ev (step-intro eq) (exec-intro rest)

exec-inv : ∀ {t c as P} → Process t c ⟹⟨ map label as ⟩ P →
  Σ State (λ c′ → P ≡ Process t c′ × Executes t c as c′)
exec-inv {as = []} ⟹-refl = _ , refl , done
exec-inv (⟹-τ st rest) = ⊥-elim (no-τ st)
exec-inv {as = a ∷ as} (⟹-ev st rest) with step-inv st
... | c₁ , eq , refl with exec-inv {as = as} rest
...   | c′ , endpoint , path = c′ , endpoint , next eq path

trace-intro : ∀ {t c as c′} → Executes t c as c′ → traces (Process t c) (map label as)
trace-intro path = _ , exec-intro path

trace-inv : ∀ {t c as} → traces (Process t c) (map label as) →
  Σ State (λ c′ → Executes t c as c′)
trace-inv (_ , tr) with exec-inv tr
... | c′ , _ , path = c′ , path

-- Every raw process trace is accounted for, including exclusion of tick events.
all-exec-inv : ∀ {t c es P} → Process t c ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ c′ →
    es ≡ map label as × P ≡ Process t c′ × Executes t c as c′))
all-exec-inv ⟹-refl = [] , _ , refl , refl , done
all-exec-inv (⟹-τ st _) = ⊥-elim (no-τ st)
all-exec-inv (⟹-ev {e = √ _} st _) = ⊥-elim (no-tick st)
all-exec-inv (⟹-ev {e = evl (evLabel _ action a)} st rest) with step-inv st
... | c₁ , eq , refl with all-exec-inv rest
...   | as , c′ , refl , endpoint , path = a ∷ as , c′ , refl , endpoint , next eq path

-- Every raw attributed trace has an explicit erased trace in the old monitor.
-- This is a cross-alphabet projection, not same-alphabet trace inclusion.
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to single-traces)
trace-projects : ∀ {t c es} → traces (Process t c) es →
  Σ (List Action) (λ as → es ≡ map label as ×
    single-traces (Single.Process t c) (map OpenProcess.label (map erase as)))
trace-projects (_ , tr) with all-exec-inv tr
... | as , c′ , refl , same , path = as , refl , Single.trace-intro (Projection.exec-projects path)

import ConnectionManagement.Machine as Open
open import ConnectionManagement.Properties.HandlerResources using (Resources)
open import ConnectionManagement.Properties.OriginMonitorInvariant using (Invariant)

-- The exact reached process still has a resource-backed ticket invariant.
raw-invariant : ∀ {t c es P} → Resources (workerId t) (Open.world c) →
  Process t (start c) ⟹⟨ es ⟩ P →
  Σ (List Action) (λ as → Σ State (λ s →
    es ≡ map label as × P ≡ Process t s × Executes t (start c) as s × Invariant t s))
raw-invariant resources execution with all-exec-inv execution
... | as , s , labels , endpoint , path =
  as , s , labels , endpoint , path , Projection.reachable path resources

open import Data.Maybe.Properties using (just-injective)

-- Deterministic monitor prefixes cannot be extended by a refused action.
reject-execution : ∀ {t c as c′ a end} → Executes t c as c′ → step t a c′ ≡ nothing →
  ¬ Executes t c (as ++ (a ∷ [])) end
reject-execution done disabled (next enabled done) = impossible (trans (sym disabled) enabled)
  where
  impossible : ∀ {s : State} → nothing ≡ just s → ⊥
  impossible ()
reject-execution (next eq prefix) disabled (next enabled rest)
  with just-injective (trans (sym eq) enabled)
... | refl = reject-execution prefix disabled rest
refused-extension : ∀ {t c as c′ a} → Executes t c as c′ → step t a c′ ≡ nothing →
  ¬ traces (Process t c) (map label (as ++ (a ∷ [])))
refused-extension prefix disabled tr with trace-inv tr
... | end , path = reject-execution prefix disabled path
