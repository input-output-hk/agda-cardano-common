{-# OPTIONS --guardedness #-}

-- Failed pre-publication handlers retain real source and physical-pool paths.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxPublicationUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import ConnectionManagement.MuxPublicationUnwind as Publication
module N = Publication isBearerClosed
module C = N.C
module D = N.D
module R = N.R
module W = N.W
import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
module F = CatchFacts isBearerClosed
module L = F.L
module Exit = F.Exit
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

Paths : N.State → N.State → Set
Paths s t = F.Paths (N.base s) (N.base t)
idle : ∀ s → Paths s s
idle s = F.idle (N.base s)
compose : ∀ {s t u} → Paths s t → Paths t u → Paths s u
compose {s} {t} {u} = F.compose {s = N.base s} {t = N.base t} {u = N.base u}
run-projects : ∀ action s {s′} → N.inherit action s ≡ just s′ → Paths s s′
run-projects action s eq with N.allowed action s
... | false = case eq of λ ()
... | true with C.step action (N.base s) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → F.step-projects action (N.base s) advanced }
apply-projects : ∀ w p ack s {s′} → N.apply w p ack s ≡ just s′ → Paths s s′
apply-projects w p ack s eq with R.enact (D.delivery ack (N.action p)) (N.raw s) in advanced
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → L.enact-projects (D.delivery ack (N.action p)) (N.raw s) advanced }
observe-projects : ∀ w site result ack s {s′} → N.observe w site result ack s ≡ just s′ → Paths s s′
observe-projects w site result ack s eq with N.select w site result s
... | nothing = case eq of λ ()
... | just p = apply-projects w p ack s eq
step-projects : ∀ action s {s′} → N.step action s ≡ just s′ → Paths s s′
step-projects (N.run action) s eq = run-projects action s eq
step-projects (N.observeFailure w site result) s eq = observe-projects w site result false s eq
step-projects (N.deliverShutdown site err) s eq with Close.phase (W.shutdown (R.base (N.raw s)))
... | Close.awaitDelivery _ w = observe-projects w site (R.async err) true s eq
... | Close.initial = case eq of λ ()
... | Close.reading = case eq of λ ()
... | Close.sendReady _ _ = case eq of λ ()
... | Close.awaitResults = case eq of λ ()
... | Close.closed = case eq of λ ()
exec-projects : ∀ {s actions t} → N.Executes s actions t → Paths s t
exec-projects (N.done {s = s}) = idle s
exec-projects (N.next {s = s} {s₁ = t} {s₂ = u} {a = action} eq rest) = compose {s = s} {t = t} {u = u}
  (step-projects action s eq) (exec-projects rest)
append : ∀ {s as t bs u} → N.Executes s as t → N.Executes t bs u → N.Executes s (as ++ bs) u
append N.done tail = tail
append (N.next eq rest) tail = N.next eq (append rest tail)
lift-step : ∀ action c {c′} → C.step action c ≡ just c′ →
  N.step (N.run action) (N.publicationState c []) ≡ just (N.publicationState c′ [])
lift-step action c eq rewrite eq = refl
lift : ∀ {s actions t} → C.Executes s actions t →
  N.Executes (N.publicationState s []) (map N.run actions) (N.publicationState t [])
lift C.done = N.done
lift (C.next {s = s} {a = a} eq rest) = N.next (lift-step a s eq) (lift rest)
initial-base : ∀ c {s} → N.initial c ≡ just s → C.initial c ≡ just (N.base s)
initial-base c eq with C.initial c
... | nothing = case eq of λ ()
... | just current = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → N.initial c ≡ just s → N.source s ≡ c
initial-source c eq = F.F.initial-source c (F.initial-base c (initial-base c eq))
from-initial-captures : ∀ {c start actions s} → N.initial (O.initial c) ≡ just start → N.Executes start actions s → Capture.Captures (N.source s)
from-initial-captures {c} init path = Capture.exec-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) init)) (Capture.initial-valid c))
  (proj₂ (Exit.machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → N.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  N.Executes start actions s → Supply.Valid (N.source s)
from-initial-supply {c} init bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) init)) (Capture.initial-valid c , bounds))
  (proj₂ (Exit.machine (exec-projects path)))

inherited-observation : ∀ action s {s′} → N.step (N.run action) s ≡ just s′ →
  Σ C.State (λ c → C.step action (N.base s) ≡ just c × s′ ≡ record s { base = c })
inherited-observation action s eq with N.allowed action s
... | false = case eq of λ ()
... | true with C.step action (N.base s) in advanced
...   | nothing = case eq of λ ()
...   | just c = c , refl , sym (just-injective eq)
physical-wait : ∀ s {s′} → N.step (N.run (C.run (D.run (R.run (D.X.run (W.shutdownStep Close.finishClose)))))) s ≡ just s′ →
  Exit.PhysicalWait (R.base (N.raw s)) (R.base (N.raw s′))
physical-wait s eq with inherited-observation (C.run (D.run (R.run (D.X.run (W.shutdownStep Close.finishClose))))) s eq
... | c , advanced , refl = F.physical-wait (N.base s) advanced
