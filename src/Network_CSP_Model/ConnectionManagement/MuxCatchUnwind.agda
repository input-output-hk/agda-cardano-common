{-# OPTIONS --guardedness #-}

-- The post-pool async catch is masked interruptibly for IO. Only a blocking
-- caller tracer or a retrying IG Dead transaction admits async receipt here.
-- The handler cannot catch its own exception: replacement exits to the buffer.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxCatchUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (local; mux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxDeltaQ as Delta
module D = Delta isBearerClosed
module R = D.R
module W = D.W
module P = D.P
module Pool = D.Pool
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.InformationChannel as Channel
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O

data DeliverySite : Set where
  blockedCallerTracer retryingIGDead : DeliverySite
data Cause : Set where
  synchronous : ErrorId → Cause
  cancellation : DeliverySite → ErrorId → Cause
asException : Cause → R.Exception
asException (synchronous err) = R.sync err
asException (cancellation _ err) = R.async err
record Interrupted : Set where
  constructor interrupted
  field caught : R.Fault
        callback : Mux.Callback
        cause : Cause
open Interrupted public
record State : Set where
  constructor catchState
  field base : D.State
        interruptions : Store WorkerId Interrupted
open State public
initial : O.Configuration → Maybe State
initial c with D.initial c
... | nothing = nothing
... | just d = just (catchState d [])
source : State → O.Configuration
source s = D.source (base s)
poolAt : WorkerId → State → Pool.State
poolAt w s = D.poolAt w (base s)

-- A failed STM commit is a delivery site only when the actual Dead message
-- cannot fit. Pending pure/ordinary STM steps do not imply interruptibility.
canDeliver : DeliverySite → Mux.Mux → State → Bool
canDeliver blockedCallerTracer m s with Mux.tracerAttachment m | Mux.callback m
... | Mux.noIGTracer | Mux.returned = true
... | Mux.igTracer | Mux.readActive Mux.muxStopped = true
... | _ | _ = false
canDeliver retryingIGDead m s with Mux.callback m
... | Mux.commitTrace true Mux.muxStopped with Channel.writeMessage (Shared.muxFinished (Mux.key m))
    (Shared.inboundInfo (Machine.world (O.core (source s))))
...   | nothing = true
...   | just _ = false
canDeliver retryingIGDead m s | _ = false
canObserve : Cause → Mux.Mux → State → Bool
canObserve (synchronous _) m s = R.deadThrowPoint m
canObserve (cancellation site _) m s = canDeliver site m s
record Plan : Set where
  constructor plan
  field observation : Interrupted
        action : R.Plan
open Plan public
select : WorkerId → Cause → State → Maybe Plan
select w reason s with lookup w (R.faults (D.base (base s))) | Pool.phase (poolAt w s) | lookup w (W.exits (R.base (D.base (base s))))
... | just f | Pool.closedPool | nothing with R.phase f | R.outcome f | P.muxAt (R.mux f) (R.protocols (D.base (base s)))
...   | R.asyncDead | R.async old | just m with D.M.finishMatches (D.M.failed old) (Mux.status m) | canObserve reason m s
...     | true | true = just (plan (interrupted f (Mux.callback m) reason)
      (R.local (put w (record f { outcome = asException reason; phase = R.readyBuffer }) (R.faults (D.base (base s))))))
...     | _ | _ = nothing
select w reason s | just f | Pool.closedPool | nothing | _ | _ | _ = nothing
select w reason s | _ | _ | _ = nothing
apply : WorkerId → Plan → Bool → State → Maybe State
apply w p ack s with R.enact (D.delivery ack (action p)) (D.base (base s))
... | nothing = nothing
... | just r = just (catchState (record (base s) { base = r }) (put w (observation p) (interruptions s)))
observe : WorkerId → Cause → Bool → State → Maybe State
observe w reason ack s with select w reason s
... | nothing = nothing
... | just p = apply w p ack s

-- The lower adapter's legacy observation must not bypass retained catch data.
allowed : D.Action → Bool
allowed (D.run (R.observeDeadTraceException _ _)) = false
allowed _ = true
data Action : Set where
  run : D.Action → Action
  observeException : WorkerId → ErrorId → Action
  observeCancellation : WorkerId → DeliverySite → ErrorId → Action
  deliverShutdown : DeliverySite → ErrorId → Action
step : Action → State → Maybe State
step (run action) s with allowed action
... | false = nothing
... | true with D.step action (base s)
...   | nothing = nothing
...   | just d = just (record s { base = d })
step (observeException w err) s = observe w (synchronous err) false s
step (observeCancellation w site err) s = observe w (cancellation site err) false s
step (deliverShutdown site err) s with Close.phase (W.shutdown (R.base (D.base (base s))))
... | Close.awaitDelivery _ w = observe w (cancellation site err) true s
... | _ = nothing

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂
