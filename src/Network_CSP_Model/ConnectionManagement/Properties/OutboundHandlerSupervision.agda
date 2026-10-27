{-# OPTIONS --guardedness #-}

-- Actual outbound-machine and fixed-snapshot shutdown projections. Outbound
-- shared writes are retained in the execution, never erased to old H stutters.
module ConnectionManagement.Properties.OutboundHandlerSupervision where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as W
import ConnectionManagement.Properties.HandlerSupervision as Handler
import ConnectionManagement.Properties.CMShutdown as CloseProof
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

OTrace : O.Configuration → O.Configuration → Set
OTrace p q = Σ (List O.Action) (λ as → O.Executes p as q)
CTrace : Close.State → Close.State → Set
CTrace p q = Σ (List Close.Action) (λ as → Close.Executes p as q)
record Paths (before after : W.State) : Set where
  constructor paths
  field
    machine : OTrace (W.source before) (W.source after)
    coordinator : CTrace (W.shutdown before) (W.shutdown after)
    last-wait : Handler.LastValid (W.shutdown before) → Handler.LastValid (W.shutdown after)
open Paths public
idle : ∀ s → Paths s s
idle s = paths ([] , O.done) ([] , Close.done) (λ witness → witness)

-- Embed every real dispatcher step while retaining the exact caller runtimes,
-- result tables and random-generation field of this outbound configuration.
inbound-step : ∀ a c {core′} → M.advance a (O.core c) ≡ just core′ →
  O.advance (O.inbound a) c ≡ just (record c { core = core′ })
inbound-step a c eq with M.advance a (O.core c)
... | nothing = case eq of λ ()
... | just core′ = case just-injective eq of λ { refl → refl }
lift-machine : ∀ c {as core′} → M.Executes (O.core c) as core′ →
  O.Executes c (map O.inbound as) (record c { core = core′ })
lift-machine c M.done = O.done
lift-machine c (M.next {c₁ = core′} {a = a} eq path) =
  O.next (inbound-step a c eq) (lift-machine (record c { core = core′ }) path)

-- Handler paths retain their physical-result oracle and actual final-wait
-- checkpoint. Only the synchronized core is replaced in the outbound machine.
handler-projects : ∀ a s {s′} → W.handlerStep a s ≡ just s′ → Paths s s′
handler-projects a s eq with W.handlerAllowed a s
... | false = case eq of λ ()
... | true with H.step a (W.view s) in advanced
...   | nothing = case eq of λ ()
...   | just h with Handler.step-projects a (W.view s) advanced
...     | Handler.paths (as , mp) (cs , cp) wait = case just-injective eq of λ { refl →
  paths (map O.inbound as , lift-machine (W.source s) mp) (cs , cp) wait }

-- Physical outbound birth is coupled to the real forkOK writer and its
-- original request's child. The registry edit is not an extra CM transition.
fork-projects : ∀ w s {s′} → W.forkOutbound w s ≡ just s′ → Paths s s′
fork-projects w s eq with lookup w (O.acquiring (W.source s))
... | nothing = case eq of λ ()
... | just f with W.freshChild (A.child (A.req f)) s
...   | false = case eq of λ ()
...   | true with O.advance (O.acquire w A.forkOK) (W.source s) in advanced
...     | nothing = case eq of λ ()
...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
...       | nothing = case eq of λ ()
...       | just h = case just-injective eq of λ { refl →
  paths ((O.acquire w A.forkOK) ∷ [] , O.next advanced O.done) ([] , Close.done) (λ wait → wait) }
dispatch-projects : ∀ a s {s′} → W.dispatchOutbound a s ≡ just s′ → Paths s s′
dispatch-projects a s eq with W.outboundAllowed a s
... | false = case eq of λ ()
... | true with O.advance a (W.source s) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl →
  paths (a ∷ [] , O.next advanced O.done) ([] , Close.done) (λ wait → wait) }
outbound-projects : ∀ a s {s′} → W.outboundStep a s ≡ just s′ → Paths s s′
outbound-projects a s eq with W.forkCaller a
... | just w = fork-projects w s eq
... | nothing = dispatch-projects a s eq
step-projects : ∀ a s {s′} → W.step a s ≡ just s′ → Paths s s′
step-projects (W.handler a) s eq = handler-projects a s eq
step-projects (W.outbound a) s eq = outbound-projects a s eq
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose (paths (as , op) (cs , cp) wait) (paths (bs , oq) (ds , cq) next) =
  paths ((as ++ bs) , O.append op oq) ((cs ++ ds) , Handler.append-close cp cq)
    (λ valid → next (wait valid))
exec-projects : ∀ {s as s′} → W.Executes s as s′ → Paths s s′
exec-projects {s = s} W.done = idle s
exec-projects (W.next {s = s} {a = a} eq path) = compose (step-projects a s eq) (exec-projects path)

-- The initializer's H view and complete outbound source are exact: no existing
-- handler can silently become physical, nor can active caller frames disappear.
initial-view : ∀ c {s} → W.initial c ≡ just s → H.initial (O.core c) ≡ just (W.view s)
initial-view c eq with H.initial (O.core c) in initialized
... | nothing = case eq of λ ()
... | just h = case just-injective eq of λ { refl → refl }
handler-initial-source : ∀ c {h} → H.initial c ≡ just h → H.source h ≡ c
handler-initial-source c eq with S.handlers (M.world c) | S.cleanups (M.world c) |
  M.handlerLifecycles c | M.publicationFaults c
... | [] | [] | [] | [] = case just-injective eq of λ { refl → refl }
... | _ ∷ _ | _ | _ | _ = case eq of λ ()
... | [] | _ ∷ _ | _ | _ = case eq of λ ()
... | [] | [] | _ ∷ _ | _ = case eq of λ ()
... | [] | [] | [] | _ ∷ _ = case eq of λ ()
initial-source : ∀ c {s} → W.initial c ≡ just s → W.source s ≡ c
initial-source c eq with H.initial (O.core c) in initialized
... | nothing = case eq of λ ()
... | just h with handler-initial-source (O.core c) initialized
...   | refl = case just-injective eq of λ { refl → refl }
initial-coordinator : ∀ c {s} → W.initial c ≡ just s → W.shutdown s ≡ Close.initialState
initial-coordinator c eq = Handler.initial-coordinator (O.core c) (initial-view c eq)
initial-last : ∀ c {s} → W.initial c ≡ just s → Handler.LastValid (W.shutdown s)
initial-last c eq = Handler.initial-last (O.core c) (initial-view c eq)

-- The inherited wait records the exact H view/physical registry at the actual
-- handler-dispatch boundary. Later outbound writes do not change that past
-- observation into a claim about current or historical global termination.
closed-from-initial : ∀ {c start as s} → W.initial c ≡ just start →
  W.Executes start as s → Close.phase (W.shutdown s) ≡ Close.closed →
  Close.remaining (W.shutdown s) ≡ [] × Handler.PhysicalWait (W.shutdown s)
closed-from-initial {c} initialized path closed with exec-projects path
... | paths sourceTrace (as , cp) wait =
  proj₁ (CloseProof.closed-from-initial
    (subst (λ first → Close.Executes first as _) (initial-coordinator c initialized) cp) closed) ,
  wait (initial-last c initialized) closed

-- These corollaries use real O executions, including all new acquisition and
-- release writers. Bounds require ordinary runtime capture validity as before.
captures-preserves : ∀ {s as s′} → Capture.Captures (W.source s) →
  W.Executes s as s′ → Capture.Captures (W.source s′)
captures-preserves valid path = Capture.exec-preserves valid (proj₂ (machine (exec-projects path)))
runtime-supply-preserves : ∀ {s as s′} → Supply.Valid (W.source s) →
  W.Executes s as s′ → Supply.Valid (W.source s′)
runtime-supply-preserves valid path = Supply.exec-preserves valid (proj₂ (machine (exec-projects path)))
from-initial-captures : ∀ {c start as s} → W.initial (O.initial c) ≡ just start →
  W.Executes start as s → Capture.Captures (W.source s)
from-initial-captures {c} initialized path = captures-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) path
from-initial-supply : ∀ {c start as s} → W.initial (O.initial c) ≡ just start →
  SupplyBounds (M.world c) → W.Executes start as s → Supply.Valid (W.source s)
from-initial-supply {c} initialized bounded path = runtime-supply-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounded)) path
