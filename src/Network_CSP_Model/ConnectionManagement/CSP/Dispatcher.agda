{-# OPTIONS --guardedness #-}

-- Reusable raw renderer: the supplied dispatcher is the only execution rule.
open import Data.Maybe using (Maybe)
module ConnectionManagement.CSP.Dispatcher
  (Configuration Action : Set)
  (advance : Action → Configuration → Maybe Configuration) where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import Process_Trees
open PTree
-- Finite paths in the supplied dispatcher; adapters retain native run types.
data Executes : Configuration → List Action → Configuration → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s t u a as} → advance a s ≡ just t → Executes t as u →
    Executes s (a ∷ as) u

data Channel : Set → Set where
  action : Channel Action
channel-≟ : (x y : AnyTypes Channel) → Dec (x ≡ y)
channel-≟ (_ , action) (_ , action) = yes refl
Proc : Set₁
Proc = PTree Channel (ExtI Channel) ⊤
open import Semantics.LTS {E = Channel} {I = ExtI Channel} using (Event√; evl; evLabel)
label : Action → Event√ ⊤
label a = evl (evLabel Action action a)

open import CSP.Operators channel-≟ using (viewV)
open import Semantics.LTS {E = Channel} {I = ExtI Channel} hiding (Event√; evl; evLabel)
open import Semantics.Failures {E = Channel} {I = ExtI Channel}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Refuses)

-- Every accepted label delegates to the combined dispatcher.
Process : Configuration → Proc
force (Process s) = react
  (λ where (_ , action) a → case advance a s of λ where
    nothing → nothing
    (just s′) → just (Process s′))
  (λ _ _ → nothing)

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

open import Data.Maybe.Properties using (just-injective)

-- Deterministic monitor prefixes cannot be extended by a refused action.
reject-execution : ∀ {c as c′ a end} → Executes c as c′ → advance a c′ ≡ nothing →
  ¬ Executes c (as ++ (a ∷ [])) end
reject-execution done disabled (next enabled done) = impossible (trans (sym disabled) enabled)
  where
  impossible : ∀ {s : Configuration} → nothing ≡ just s → ⊥
  impossible ()
reject-execution (next eq prefix) disabled (next enabled rest)
  with just-injective (trans (sym eq) enabled)
... | refl = reject-execution prefix disabled rest
refused-extension : ∀ {c as c′ a} → Executes c as c′ → advance a c′ ≡ nothing →
  ¬ traces (Process c) (map label (as ++ (a ∷ [])))
refused-extension prefix disabled tr with trace-inv tr
... | end , path = reject-execution prefix disabled path

-- The visible alphabet is exactly Action, including every nested payload.
-- Tick belongs to Event√ but is never rendered; decoding rejects it explicitly.
decode-event : Event → Action
decode-event (evLabel _ action a) = a
decode : Event√ ⊤ → Maybe Action
decode (evl e) = just (decode-event e)
decode (√ _) = nothing
encode-decode : ∀ e → label (decode-event e) ≡ evl e
encode-decode (evLabel _ action a) = refl
decode-label : ∀ a → decode (label a) ≡ just a
decode-label a = refl
label-injective : ∀ {a b} → label a ≡ label b → a ≡ b
label-injective eq = just-injective (cong decode eq)
decode-sound : ∀ {e a} → decode e ≡ just a → e ≡ label a
decode-sound {evl (evLabel _ action a)} refl = refl
-- Every visible event has one preimage, and that preimage is unique.
alphabet-complete : ∀ e → Σ Action (λ a →
  evl e ≡ label a × (∀ b → evl e ≡ label b → a ≡ b))
alphabet-complete (evLabel _ action a) = a , refl , λ b eq → label-injective eq
-- Coverage is total even for actions disabled at a particular state.
action-covered : ∀ a → Σ Event (λ e → evl e ≡ label a × decode-event e ≡ a)
action-covered a = evLabel Action action a , refl , refl

open import Level using (Level)
open import Semantics.Refusals {E = Channel} {I = ExtI Channel} using (Offers)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (failures)

-- No reachability, finiteness or equality-decision assumption is required.
-- Sets may include tick: it is automatically refused, as it has no machine action.
DisabledSet : ∀ {ℓ : Level} → Configuration → (Event√ ⊤ → Set ℓ) → Set ℓ
DisabledSet s X = ∀ a → X (label a) → advance a s ≡ nothing

not-offered-disabled : ∀ {s a} → ¬ Offers (Process s) (label a) → advance a s ≡ nothing
not-offered-disabled {s} {a} absent with advance a s in eq
... | nothing = refl
... | just t = ⊥-elim (absent (Process t , step-intro eq))
disabled-not-offered : ∀ {s a} → advance a s ≡ nothing → ¬ Offers (Process s) (label a)
disabled-not-offered disabled (_ , st) with step-inv st
... | t , enabled , _ with trans (sym disabled) enabled
...   | ()

-- Arbitrary-set refusal equivalence, over the full Event√ alphabet.
refusal-intro : ∀ {ℓ} {s} {X : Event√ ⊤ → Set ℓ} → DisabledSet s X → Refuses (Process s) X
refusal-intro {s = s} {X = X} disabled = (λ _ _ → refl) , reject
  where
  reject : ∀ e → X e → ¬ Offers (Process s) e
  reject (evl (evLabel _ action a)) member = disabled-not-offered (disabled a member)
  reject (√ r) member (_ , st) = no-tick st
refusal-inv : ∀ {ℓ} {s} {X : Event√ ⊤ → Set ℓ} → Refuses (Process s) X → DisabledSet s X
refusal-inv (_ , reject) a member = not-offered-disabled (reject (label a) member)
refusal-exact : ∀ {ℓ} {s} {X : Event√ ⊤ → Set ℓ} →
  (Refuses (Process s) X → DisabledSet s X) × (DisabledSet s X → Refuses (Process s) X)
refusal-exact = refusal-inv , refusal-intro
singleton-refusal : ∀ {s a} → advance a s ≡ nothing → Refuses (Process s) (λ e → e ≡ label a)
singleton-refusal {s = s} {a = a} disabled = refusal-intro λ b eq →
  subst (λ x → advance x s ≡ nothing) (sym (label-injective eq)) disabled
singleton-refusal-inv : ∀ {s a} → Refuses (Process s) (λ e → e ≡ label a) → advance a s ≡ nothing
singleton-refusal-inv refusal = refusal-inv refusal _ refl

-- Stable failures agree exactly with a machine run followed by disabled actions.
failure-intro : ∀ {ℓ} {s as t} {X : Event√ ⊤ → Set ℓ} →
  Executes s as t → DisabledSet t X → failures (Process s) (map label as) X
failure-intro {t = t} run disabled = Process t , exec-intro run , refusal-intro disabled
failure-inv : ∀ {ℓ} {s as} {X : Event√ ⊤ → Set ℓ} →
  failures (Process s) (map label as) X → Σ Configuration (λ t → Executes s as t × DisabledSet t X)
failure-inv (_ , path , refusal) with exec-inv path
... | t , refl , run = t , run , refusal-inv refusal
all-failure-inv : ∀ {ℓ} {s es} {X : Event√ ⊤ → Set ℓ} →
  failures (Process s) es X → Σ (List Action) (λ as → Σ Configuration (λ t →
    es ≡ map label as × Executes s as t × DisabledSet t X))
all-failure-inv (_ , path , refusal) with all-exec-inv path
... | as , t , eq , refl , run = as , t , eq , run , refusal-inv refusal
