{-# OPTIONS --guardedness #-}

-- The pool relays thread (network 2f1c154, Diffusion.hs withPoolRelays,
-- 699-722 and 888). It is the outermost withAsync of the remote diffusion
-- callback and exists only when egress is scheduled (poolAllowances = Just).
-- Its owner cancels and joins it only after the whole inner callback (sockets,
-- server, CM, peer selection scopes) has returned. Its failure is one abstract
-- cause of the inner AsyncScope.beginUnwind through waitAny; that coupling and
-- the thread body (DNS semaphore, ledger polling) are not modelled.
module ConnectionManagement.Rules.PoolRelays where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Rules.AsyncScope public
  using (ThreadPhase; running; cancelRequested; cancelDelivered; bodyUnwinding;
         bodyExited; resultAvailable; joined; requestedPhase)

-- The owner's position in withAsync: running the inner callback, cancelling
-- and waiting for the relays thread, or returned.
data Owner : Set where
  inside cancelling finished : Owner

-- `thread` is nothing when no relays thread was forked (a plain node).
record State : Set where
  constructor relaysState
  field thread : Maybe ThreadPhase
        owner : Owner
open State public

-- The Bool is whether the diffusion configuration has pool allowances.
initial : Bool → State
initial true = relaysState (just running) inside
initial false = relaysState nothing inside

-- Transitions of the thread itself; they never move the owner.
data ThreadAction : Set where
  beginFailure bodyExit publishResult deliverCancel join : ThreadAction
data Action : Set where
  threadAct : ThreadAction → Action
  requestCancel finish : Action

-- The body has type m Void, so it can exit only by unwinding an exception:
-- its own failure or the owner's delivered cancellation.
voidExit : ThreadPhase → Bool
voidExit cancelDelivered = true
voidExit bodyUnwinding = true
voidExit _ = false

-- Delivery and join belong to the owner's cancellation.
move : ThreadAction → Owner → ThreadPhase → Maybe ThreadPhase
move beginFailure o running = just bodyUnwinding
move beginFailure o cancelRequested = just bodyUnwinding
move bodyExit o p with voidExit p
... | true = just bodyExited
... | false = nothing
move publishResult o bodyExited = just resultAvailable
move deliverCancel cancelling cancelRequested = just cancelDelivered
move join cancelling resultAvailable = just joined
move _ _ _ = nothing

-- The Bool is whether the inner callback has returned. Cancellation, and the
-- owner's return without a thread, both wait for it. withAsync's cancel also
-- reaches a thread that has already exited; it then only waits for it.
step : Bool → Action → State → Maybe State
step ret a (relaysState t finished) = nothing
step ret (threadAct a) (relaysState nothing o) = nothing
step ret (threadAct a) (relaysState (just p) o) with move a o p
... | just p′ = just (relaysState (just p′) o)
... | nothing = nothing
step true requestCancel (relaysState (just p) inside) = just (relaysState (just (requestedPhase p)) cancelling)
step true finish (relaysState nothing inside) = just (relaysState nothing finished)
step ret finish (relaysState (just joined) cancelling) = just (relaysState (just joined) finished)
step _ _ _ = nothing

-- The outer layer around any inner callback. Inner steps run only while the
-- owner is inside; relays steps read whether the inner callback has returned.
module Outer {Inner InnerAction : Set}
  (innerStep : InnerAction → Inner → Maybe Inner) (returned : Inner → Bool) where

  record Outer : Set where
    constructor outer
    field inner : Inner
          relays : State
  open Outer public

  data OuterAction : Set where
    innerAct : InnerAction → OuterAction
    relaysAct : Action → OuterAction

  outerStep : OuterAction → Outer → Maybe Outer
  outerStep (innerAct a) (outer i (relaysState t inside)) with innerStep a i
  ... | just i′ = just (outer i′ (relaysState t inside))
  ... | nothing = nothing
  outerStep (innerAct a) (outer i r) = nothing
  outerStep (relaysAct a) (outer i r) with step (returned i) a r
  ... | just r′ = just (outer i r′)
  ... | nothing = nothing

  data Executes : Outer → List OuterAction → Outer → Set where
    done : ∀ {s} → Executes s [] s
    next : ∀ {s t u a as} → outerStep a s ≡ just t → Executes t as u → Executes s (a ∷ as) u
