{-# OPTIONS --guardedness #-}

-- Outbound caller interleavings over the bounded pre-handshake physical-handler
-- profile. Every new child is captured at its actual inbound/outbound fork;
-- existing handler tables are never adopted as physical Async history.
module ConnectionManagement.OutboundHandlerSupervision where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.CMShutdown as Close

record State : Set where
  constructor supervised
  field source : O.Configuration
        threads : Store WorkerId H.Thread
        shutdown : Close.State
open State public

-- O.core is the sole copy of the shared dispatcher configuration.
view : State → H.State
view s = H.supervised (O.core (source s)) (threads s) (shutdown s)
setView : H.State → State → State
setView h s = supervised (record (source s) { core = H.source h }) (H.threads h) (H.shutdown h)
initial : O.Configuration → Maybe State
initial c with H.initial (O.core c)
... | nothing = nothing
... | just h = just (supervised (record c { core = H.source h }) (H.threads h) (H.shutdown h))

-- New physical worker identities cannot collide with an active admission or
-- outbound caller, or any historical physical handler. A.step also checks the
-- source handler heap at the actual fork boundary.
freshChild : WorkerId → State → Bool
freshChild child s with lookup child (threads s) |
  lookup child (S.handlers (M.world (O.core (source s)))) |
  lookup child (S.admissions (M.world (O.core (source s)))) |
  lookup child (O.acquiring (source s)) | lookup child (O.releasing (source s))
... | nothing | nothing | nothing | nothing | nothing = true
... | _ | _ | _ | _ | _ = false
unowned : WorkerId → State → Bool
unowned w s with lookup w (threads s)
... | nothing = true
... | just _ = false

-- An inbound physical child is also fresh against outbound runtimes. Other
-- inherited handler operations retain their exact dispatcher/physical guards.
handlerAllowed : H.Action → State → Bool
handlerAllowed (H.run (M.admissionStep w Server.fork)) s with lookup w (S.admissions (M.world (O.core (source s))))
... | nothing = false
... | just a = freshChild (S.child (S.request a)) s
handlerAllowed _ s = true
outboundAllowed : O.Action → State → Bool
outboundAllowed (O.inbound _) s = false
outboundAllowed (O.release _ (R.cancellationDelivered _)) s = false
outboundAllowed (O.beginAcquire w _) s = unowned w s
outboundAllowed (O.beginRelease w _) s = unowned w s
outboundAllowed _ s = true

-- Read the original request before executing forkOK and capture the actual
-- newly installed HandlerStart afterward. No handshake/connection-map result
-- is inferred from physical creation, which precedes commitConnected.
forkOutbound : WorkerId → State → Maybe State
forkOutbound w s with lookup w (O.acquiring (source s))
... | nothing = nothing
... | just f with freshChild (A.child (A.req f)) s
...   | false = nothing
...   | true with O.advance (O.acquire w A.forkOK) (source s)
...     | nothing = nothing
...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
...       | nothing = nothing
...       | just h = just (supervised c
  (put (A.child (A.req f)) (H.handlerThread h H.maskedSetup) (threads s)) (shutdown s))

-- Dispatch helpers remain transparent for real outbound/coordinator projections.
handlerStep : H.Action → State → Maybe State
handlerStep action s with handlerAllowed action s
... | false = nothing
... | true with H.step action (view s)
...   | nothing = nothing
...   | just h = just (setView h s)
dispatchOutbound : O.Action → State → Maybe State
dispatchOutbound action s with outboundAllowed action s
... | false = nothing
... | true with O.advance action (source s)
...   | nothing = nothing
...   | just c = just (record s { source = c })
forkCaller : O.Action → Maybe WorkerId
forkCaller (O.acquire w A.forkOK) = just w
forkCaller _ = nothing
outboundStep : O.Action → State → Maybe State
outboundStep action s with forkCaller action
... | just w = forkOutbound w s
... | nothing = dispatchOutbound action s

data Action : Set where
  handler : H.Action → Action
  outbound : O.Action → Action
step : Action → State → Maybe State
step (handler action) s = handlerStep action s
step (outbound action) s = outboundStep action s

-- No caller-supplied result oracle or post-close global freeze is introduced.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
