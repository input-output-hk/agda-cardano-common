{-# OPTIONS --guardedness #-}

-- Post-close catch observations preserve source/pool traces and CM results.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxCatchUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.MuxRuntime as Mux
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import ConnectionManagement.MuxCatchUnwind as Catch
module C = Catch isBearerClosed
module D = C.D
module R = C.R
module W = C.W
module Pool = C.Pool
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
module F = DeltaFacts isBearerClosed
module L = F.Base
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
module Exit = ExitFacts isBearerClosed
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

Paths : C.State → C.State → Set
Paths s t = F.Paths (C.base s) (C.base t)
idle : ∀ s → Paths s s
idle s = F.idle (C.base s)
compose : ∀ {s t u} → Paths s t → Paths t u → Paths s u
compose {s} {t} {u} = F.compose {p = C.base s} {q = C.base t} {r = C.base u}
run-projects : ∀ action s {s′} → C.step (C.run action) s ≡ just s′ → Paths s s′
run-projects action s eq with C.allowed action
... | false = case eq of λ ()
... | true with D.step action (C.base s) in advanced
...   | nothing = case eq of λ ()
...   | just d = case just-injective eq of λ { refl → F.step-projects action (C.base s) advanced }
apply-projects : ∀ w p ack s {s′} → C.apply w p ack s ≡ just s′ → Paths s s′
apply-projects w p ack s eq with R.enact (D.delivery ack (C.action p)) (D.base (C.base s)) in advanced
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → L.enact-projects (D.delivery ack (C.action p)) (D.base (C.base s)) advanced }
observe-projects : ∀ w reason ack s {s′} → C.observe w reason ack s ≡ just s′ → Paths s s′
observe-projects w reason ack s eq with C.select w reason s
... | nothing = case eq of λ ()
... | just p = apply-projects w p ack s eq
step-projects : ∀ action s {s′} → C.step action s ≡ just s′ → Paths s s′
step-projects (C.run action) s eq = run-projects action s eq
step-projects (C.observeException w err) s eq = observe-projects w (C.synchronous err) false s eq
step-projects (C.observeCancellation w site err) s eq = observe-projects w (C.cancellation site err) false s eq
step-projects (C.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (D.base (C.base s))))
... | Close.awaitDelivery _ w = observe-projects w (C.cancellation site err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady _ _ = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
exec-projects : ∀ {s actions t} → C.Executes s actions t → Paths s t
exec-projects (C.done {s = s}) = idle s
exec-projects (C.next {s = s} {s₁ = t} {s₂ = u} {a = action} eq rest) = compose {s = s} {t = t} {u = u} (step-projects action s eq) (exec-projects rest)

-- No legacy observation is allowed to discard the caught exception metadata.
lift-step : ∀ action d {d′} → C.allowed action ≡ true → D.step action d ≡ just d′ →
  C.step (C.run action) (C.catchState d []) ≡ just (C.catchState d′ [])
lift-step action d allowed eq rewrite allowed | eq = refl
data AllowedActions : List D.Action → Set where
  empty : AllowedActions []
  more : ∀ {a as} → C.allowed a ≡ true → AllowedActions as → AllowedActions (a ∷ as)
lift : ∀ {s actions t} → D.Executes s actions t → AllowedActions actions →
  C.Executes (C.catchState s []) (map C.run actions) (C.catchState t [])
lift D.done empty = C.done
lift (D.next {s = s} {a = a} eq rest) (more allowed tags) = C.next (lift-step a s allowed eq) (lift rest tags)
append : ∀ {s as t bs u} → C.Executes s as t → C.Executes t bs u → C.Executes s (as ++ bs) u
append C.done tail = tail
append (C.next eq rest) tail = C.next eq (append rest tail)

initial-base : ∀ c {s} → C.initial c ≡ just s → D.initial c ≡ just (C.base s)
initial-base c eq with D.initial c
... | nothing = case eq of λ ()
... | just d = case just-injective eq of λ { refl → refl }
from-initial-captures : ∀ {c start actions s} → C.initial (O.initial c) ≡ just start → C.Executes start actions s → Capture.Captures (C.source s)
from-initial-captures {c} init path = Capture.exec-preserves
  (subst Capture.Captures (sym (F.initial-source (O.initial c) (initial-base (O.initial c) init))) (Capture.initial-valid c))
  (proj₂ (Exit.machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → C.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  C.Executes start actions s → Supply.Valid (C.source s)
from-initial-supply {c} init bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (F.initial-source (O.initial c) (initial-base (O.initial c) init))) (Capture.initial-valid c , bounds))
  (proj₂ (Exit.machine (exec-projects path)))

-- Peel the adapter guard at an abstract action before specializing the CM
-- call. This avoids normalizing the complete nested shutdown dispatcher.
inherited-observation : ∀ action s {s′} → C.step (C.run action) s ≡ just s′ →
  Σ D.State (λ d → D.step action (C.base s) ≡ just d × s′ ≡ record s { base = d })
inherited-observation action s eq with C.allowed action
... | false = case eq of λ ()
... | true with D.step action (C.base s) in advanced
...   | nothing = case eq of λ ()
...   | just d = d , refl , sym (just-injective eq)

-- The final collective wait still observes the actual physical handler result.
physical-wait : ∀ s {s′} → C.step (C.run (D.run (R.run (D.X.run (W.shutdownStep Close.finishClose))))) s ≡ just s′ →
  Exit.PhysicalWait (R.base (D.base (C.base s))) (R.base (D.base (C.base s′)))
physical-wait s eq with inherited-observation (D.run (R.run (D.X.run (W.shutdownStep Close.finishClose)))) s eq
... | d , advanced , refl = F.physical-wait (C.base s) advanced

-- Local selection only replaces fault metadata. Physical cleanup is already
-- complete, and the caught fault and actual pending callback are retained.
select-is-local : ∀ w reason s {p} → C.select w reason s ≡ just p →
  Σ _ (λ fs → C.action p ≡ R.local fs)
select-is-local w reason s eq with lookup w (R.faults (D.base (C.base s))) | Pool.phase (C.poolAt w s) | lookup w (W.exits (R.base (D.base (C.base s))))
... | just f | Pool.closedPool | nothing with R.phase f | R.outcome f | C.P.muxAt (R.mux f) (R.protocols (D.base (C.base s)))
...   | R.asyncDead | R.async old | just m with D.M.finishMatches (D.M.failed old) (Mux.status m) | C.canObserve reason m s
...     | true | true = case just-injective eq of λ { refl → _ , refl }
...     | true | false = case eq of λ ()
...     | false | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.async old | nothing = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.asyncDead | R.sync _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.readyBody | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.readyBuffer | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.awaitingClose | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.closing | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.poolClosed | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.asyncStatus | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | nothing | R.handedOff | _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.openPool | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closing | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.cancelPending _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.joinPending _ | _ = case eq of λ ()
select-is-local w reason s eq | just f | Pool.closedPool | just _ = case eq of λ ()
select-is-local w reason s eq | nothing | _ | _ = case eq of λ ()

observe-keeps-underlying : ∀ w reason s {s′} → C.observe w reason false s ≡ just s′ →
  R.base (D.base (C.base s′)) ≡ R.base (D.base (C.base s))
observe-keeps-underlying w reason s eq with C.select w reason s in selected
... | nothing = case eq of λ ()
... | just p with select-is-local w reason s selected
...   | fs , local rewrite local = case just-injective eq of λ { refl → refl }
