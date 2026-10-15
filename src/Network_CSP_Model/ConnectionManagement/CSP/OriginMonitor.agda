{-# OPTIONS --guardedness #-}

-- Diagnostic CSP rendering of the success monitor, with trace inclusion into
-- the open process. This is not failures refinement or source correspondence.
module ConnectionManagement.CSP.OriginMonitor where

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
open import ConnectionManagement.Machine using (Action)
open import ConnectionManagement.Rules.OriginMonitor
import ConnectionManagement.Properties.OriginMonitor as Projection
import ConnectionManagement.CSP.Correspondence as OpenProof
open import ConnectionManagement.CSP.Process using (Channel; action; Proc; label; channel-≟)
import ConnectionManagement.CSP.Process as OpenProcess
open import CSP.Operators channel-≟ using (viewV)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

-- Check the monitor before exposing each original action label.
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

-- Every finite monitored trace is also a trace of the open dispatcher.
trace-projects : ∀ {t c es} → traces (Process t c) es → traces (OpenProcess.Process (machine c)) es
trace-projects (_ , tr) with all-exec-inv tr
... | as , c′ , refl , same , path = OpenProof.trace-intro (Projection.exec-projects path)

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
