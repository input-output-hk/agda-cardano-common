{-# OPTIONS --guardedness #-}

-- Failures after handshake return but before its promise write. The handshake
-- catch no longer applies; no pool/buffer was entered and no result is invented.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxPublicationUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (local; mux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxCatchUnwind as Catch
module C = Catch isBearerClosed
module D = C.D
module R = C.R
module W = C.W
module G = D.G
module M = D.M
module P = D.P
module U = D.U
module S = G.Startup
module Pool = C.Pool
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.State as Shared
import ConnectionManagement.Rules.CMShutdown as Close

-- Async receipt at either tracer means an observed blocking operation while
-- masked interruptibly. Handshake results were already forced by the driver;
-- strict Handle construction is retained only as a rejected observation site.
-- A lazy protocol element may fail synchronously INSIDE Mux.new before its
-- allocation returns. Private partial TVars are outside this atomic profile.
data Site : Set where
  handshakeSuccessTracer newMuxTracer muxAllocation strictHandle : Site
record Failure : Set where
  constructor failure
  field captured : U.Frame
        site : Site
        outcome : R.Exception
open Failure public
record State : Set where
  constructor publicationState
  field base : C.State
        failures : Store WorkerId Failure
open State public
initial : O.Configuration → Maybe State
initial c with C.initial c
... | nothing = nothing
... | just current = just (publicationState current [])
raw : State → R.State
raw s = D.base (C.base (base s))
source : State → O.Configuration
source s = C.source (base s)
poolAt : WorkerId → State → Pool.State
poolAt w s = C.poolAt w (base s)
siteReady : Site → U.Progress → Bool
siteReady handshakeSuccessTracer U.returnedSuccess = true
siteReady newMuxTracer U.returnedSuccess = true
siteReady muxAllocation U.returnedSuccess = true
siteReady strictHandle _ = false
siteReady _ _ = false
deliveryReady : Site → R.Exception → Bool
deliveryReady muxAllocation (R.async _) = false
deliveryReady strictHandle (R.async _) = false
deliveryReady _ _ = true
target : R.Exception → W.Phase
target (R.sync err) = W.classifying err
target (R.async err) = W.bodyExited (W.asyncException err)
record Plan : Set where
  constructor plan
  field observation : Failure
        action : R.Plan
open Plan public
select : WorkerId → Site → R.Exception → State → Maybe Plan
select w at result s with lookup w (failures s) | R.owner w (raw s) | lookup w (W.exits (R.base (raw s))) | lookup w (R.faults (raw s))
... | nothing | just f | nothing | nothing with siteReady at (U.progress f) | deliveryReady at result | S.phase (U.startup f) | Pool.handles (poolAt w s)
...   | true | true | S.awaitPublication | [] with lookup w (Shared.handlers (Machine.world (O.core (source s)))) |
    lookup (Shared.handlerPromise (U.captured f)) (Shared.handshakeResults (Machine.world (O.core (source s))))
...     | just actual | nothing with W.sameStart (U.captured f) actual
...       | true = just (plan (failure f at result) (R.transfer w (W.exitFrame (U.captured f) (target result) nothing) (R.faults (raw s))))
...       | false = nothing
select w at result s | nothing | just f | nothing | nothing | true | true | S.awaitPublication | [] | _ | _ = nothing
select w at result s | nothing | just f | nothing | nothing | _ | _ | _ | _ = nothing
select w at result s | _ | _ | _ | _ = nothing
apply : WorkerId → Plan → Bool → State → Maybe State
apply w p ack s with R.enact (D.delivery ack (action p)) (raw s)
... | nothing = nothing
... | just next = just (publicationState
  (record (base s) { base = record (C.base (base s)) { base = next } })
  (put w (observation p) (failures s)))
observe : WorkerId → Site → R.Exception → Bool → State → Maybe State
observe w at result ack s with select w at result s
... | nothing = nothing
... | just p = apply w p ack s

-- A failed owner cannot return to allocation/publication or its old controller.
-- Other owners, actual CM actions and its outer classifier/finalizer stay live.
actorU : U.Action → Maybe WorkerId
actorU (U.negotiate w _ _) = just w
actorU (U.allocateHandle w _ _) = just w
actorU (U.publishSuccess w) = just w
actorU (U.startupStep w _) = just w
actorU _ = nothing
preActor : R.Action → Maybe WorkerId
preActor (R.run (D.X.run (W.run (G.run (M.run (P.run action)))))) = actorU action
preActor _ = nothing
actor : C.Action → State → Maybe WorkerId
actor (C.run (D.run action)) s with preActor action
... | just w = just w
... | nothing = D.actor action (C.base (base s))
actor _ s = nothing
free : WorkerId → State → Bool
free w s with lookup w (failures s)
... | nothing = true
... | just _ = false
guarded : C.Action → State → Bool
guarded action s with actor action s
... | nothing = true
... | just w = free w s
allowed : C.Action → State → Bool
allowed action s with failures s
... | [] = true
... | _ ∷ _ = guarded action s
inherit : C.Action → State → Maybe State
inherit action s with allowed action s
... | false = nothing
... | true with C.step action (base s)
...   | nothing = nothing
...   | just next = just (record s { base = next })
data Action : Set where
  run : C.Action → Action
  observeFailure : WorkerId → Site → R.Exception → Action
  deliverShutdown : Site → ErrorId → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (observeFailure w at result) s = observe w at result false s
step (deliverShutdown at err) s with Close.phase (W.shutdown (R.base (raw s)))
... | Close.awaitDelivery _ w = observe w at (R.async err) true s
... | _ = nothing

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
