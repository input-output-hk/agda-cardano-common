{-# OPTIONS --guardedness #-}

-- Projection and local guard guarantees for the single-target success monitor.
module ConnectionManagement.Properties.OriginMonitor where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (HandlerStart; handlers; handlerKey; negotiated)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginMonitor

-- The filter never manufactures a machine transition or an endpoint.
step-projects : ∀ t a s {s′} → step t a s ≡ just s′ →
  Open.advance a (machine s) ≡ just (machine s′)
step-projects t a s eq with check t (classify t a) s
... | nothing = case eq of λ ()
... | just ph with Open.advance a (machine s) in advanced
...   | nothing = case eq of λ ()
...   | just c′ with just-injective eq
...     | refl = refl
exec-projects : ∀ {t s as s′} → Executes t s as s′ → Open.Executes (machine s) as (machine s′)
exec-projects done = Open.done
exec-projects (next {s = s} {a = a} eq path) = Open.next (step-projects _ a s eq) (exec-projects path)

-- Successful allocation checks both invocation phase and captured connection key.
allocation-checked : ∀ t mid k ps f s {ph} → check t (allocation mid k ps f) s ≡ just ph →
  Σ HandlerStart (λ h → lookup (workerId t) (handlers (Open.world (machine s))) ≡ just h ×
    k ≡ handlerKey h × phase s ≡ awaitingAllocation × ph ≡ awaitingPublication (ticket mid ps f))
allocation-checked t mid k ps f (observed c (awaitingPublication tk)) ()
allocation-checked t mid k ps f (observed c (published tk)) ()
allocation-checked t mid k ps f (observed c awaitingAllocation) eq with lookup (workerId t) (handlers (Open.world c)) in found
... | nothing = case eq of λ ()
... | just h with k ≟ handlerKey h
...   | no _ = case eq of λ ()
...   | yes same with just-injective eq
...     | refl = h , refl , same , refl , refl

flow-checked : ∀ f g tk {ph} → match-flow f g tk ≡ just ph → f ≡ g × ph ≡ published tk
flow-checked unidirectional unidirectional tk refl = refl , refl
flow-checked duplex duplex tk refl = refl , refl
flow-checked unidirectional duplex tk ()
flow-checked duplex unidirectional tk ()

publication-checked : ∀ t hid f s {ph} → check t (publication (negotiated hid f) Open.resultWritten) s ≡ just ph →
  Σ Ticket (λ tk → phase s ≡ awaitingPublication tk × hid ≡ handleId t × f ≡ flow tk × ph ≡ published tk)
publication-checked t hid f (observed c awaitingAllocation) ()
publication-checked t hid f (observed c (published tk)) ()
publication-checked t hid f (observed c (awaitingPublication tk)) eq with hid ≟ handleId t
... | no _ = case eq of λ ()
... | yes same with flow-checked f (flow tk) tk eq
...   | flowSame , phaseSame = tk , refl , same , flowSame , phaseSame

-- Successful monitored steps also expose the precise guard transition.
step-checks : ∀ t a s {s′} → step t a s ≡ just s′ → check t (classify t a) s ≡ just (phase s′)
step-checks t a s eq with check t (classify t a) s
... | nothing = case eq of λ ()
... | just ph with Open.advance a (machine s)
...   | nothing = case eq of λ ()
...   | just c′ with just-injective eq
...     | refl = refl

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (trans; sym; subst)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Properties.HandlerResources as Resources
open import ConnectionManagement.Properties.HandlerOrigin using (Origin; install-origin; origin-exec)

-- Classification cannot treat allocation of the selected handle as unrelated.
selected-allocation : ∀ t mid k ps f →
  classify t (Open.igStep (IG.installHandle (handleId t) mid k ps f)) ≡ allocation mid k ps f
selected-allocation t mid k ps f with handleId t ≟ handleId t
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

-- Resource evidence comes from the caller (for example selection/fork), not from
-- a pre-seeded monitor phase. The checked key then yields the exact Origin.
accepted-allocation : ∀ t mid k ps f s {s′} → Resources.Resources (workerId t) (Open.world (machine s)) →
  step t (Open.igStep (IG.installHandle (handleId t) mid k ps f)) s ≡ just s′ →
  Origin (workerId t) (handleId t) mid ps f (machine s′)
accepted-allocation t mid k ps f s r eq with allocation-checked t mid k ps f s
  (subst (λ event → check t event s ≡ _) (selected-allocation t mid k ps f)
    (step-checks t (Open.igStep (IG.installHandle (handleId t) mid k ps f)) s eq))
... | h , found , keySame , before , after with just-injective (trans (sym found) (Resources.found r))
... | refl rewrite keySame = install-origin (handleId t) mid ps f (machine s) r (step-projects t (Open.igStep (IG.installHandle (handleId t) mid (handlerKey (Resources.original r)) ps f)) s eq)

-- Once checked, origin survives any accepted continuation by trace projection.
origin-retained : ∀ {t s as s′ w hid mid ps f} → Executes t s as s′ →
  Origin w hid mid ps f (machine s) → Origin w hid mid ps f (machine s′)
origin-retained path = origin-exec (exec-projects path)

selected-publication : ∀ t hid f →
  classify t (Open.handlerPublication (workerId t) (negotiated hid f) Open.resultWritten) ≡
    publication (negotiated hid f) Open.resultWritten
selected-publication t hid f with workerId t ≟ workerId t
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

-- The public step, not just the internal check, enforces matching handle/flow.
accepted-publication : ∀ t hid f s {s′} →
  step t (Open.handlerPublication (workerId t) (negotiated hid f) Open.resultWritten) s ≡ just s′ →
  Σ Ticket (λ tk → phase s ≡ awaitingPublication tk × hid ≡ handleId t × f ≡ flow tk × phase s′ ≡ published tk)
accepted-publication t hid f s eq = publication-checked t hid f s
  (subst (λ event → check t event s ≡ _) (selected-publication t hid f)
    (step-checks t (Open.handlerPublication (workerId t) (negotiated hid f) Open.resultWritten) s eq))

-- Outbound allocation is explicitly outside this inbound success-contract
-- profile rather than silently passing as unrelated dispatcher interference.
outbound-allocation-refused : ∀ t hid mid k ps f s →
  step t (Open.igStep (IG.installOutboundHandle hid mid k ps f)) s ≡ nothing
outbound-allocation-refused t hid mid k ps f s = refl
