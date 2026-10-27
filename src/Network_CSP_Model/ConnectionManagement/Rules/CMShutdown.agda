{-# OPTIONS --guardedness #-}

-- Core.hs:523-550 at network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d:
-- one current-map snapshot, late entry reads, sequential throwTo acknowledgments,
-- then one all-results STM wait. This is not a historical-handler census.
module ConnectionManagement.Rules.CMShutdown where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as S

-- Source getConnThread observes the entry at traversal time, including a
-- Terminating handler. Reserved/Terminated entries contribute no Async handle.
getConnThread : S.ConnectionState → Maybe WorkerId
getConnThread S.reservedOutbound = nothing
getConnThread (S.unnegotiated _ _ w) = just w
getConnThread (S.outboundUni _ w _) = just w
getConnThread (S.outboundDup _ w _ _) = just w
getConnThread (S.outboundIdle _ w _ _) = just w
getConnThread (S.inboundIdle _ w _ _) = just w
getConnThread (S.inboundActive _ w _ _) = just w
getConnThread (S.duplexActive _ w _) = just w
getConnThread (S.terminating _ w _) = just w
getConnThread (S.terminated _) = nothing

-- Association-store order abstracts the source nested Map traversal order.
-- Neither equal EntryIds in distinct bindings nor repeated worker handles are
-- deduplicated: each captured binding receives its own late read/send boundary.
innerEntries : Store LocalKey EntryId → List EntryId
innerEntries [] = []
innerEntries ((_ , e) ∷ rest) = e ∷ innerEntries rest
snapshotEntries : S.ConnMap → List EntryId
snapshotEntries [] = []
snapshotEntries ((_ , inner) ∷ rest) = innerEntries inner ++ snapshotEntries rest

data PC : Set where
  initial reading awaitResults closed : PC
  sendReady awaitDelivery : EntryId → WorkerId → PC

record State : Set where
  constructor shutdownState
  field
    phase : PC
    snapshot remaining : List EntryId
    collected : List WorkerId
open State public

-- The coordinator starts after the source TrShutdown trace boundary. It does
-- not itself cancel the server or forbid admission/other actors' shared writes.
initialState : State
initialState = shutdownState initial [] [] []

data Action : Set where
  captureSnapshot readEntry requestCancellation acknowledgeDelivery
    finishTraversal finishClose : Action

-- The observation oracle must mean the captured physical handler Async result
-- is available. An adapter must establish that contract; cleanupDone, registry
-- absence, or throwTo delivery alone is not such a result certificate. Inputs
-- may differ at every step; no monotonicity or eventual result is assumed here.
allAvailable : (WorkerId → Bool) → List WorkerId → Bool
allAvailable available [] = true
allAvailable available (w ∷ rest) = available w ∧ allAvailable available rest

step : S.CMStore → (WorkerId → Bool) → Action → State → Maybe State
step current available captureSnapshot s with phase s | S.mapCell current
... | initial | S.full map = just (record s
  { phase = reading; snapshot = snapshotEntries map; remaining = snapshotEntries map })
... | _ | _ = nothing
step current available readEntry s with phase s | remaining s
... | reading | e ∷ rest with lookup e (S.entries current)
...   | nothing = nothing -- malformed captured entry, not source retry
...   | just state with getConnThread state
...     | nothing = just (record s { remaining = rest })
...     | just w = just (record s { phase = sendReady e w; remaining = rest })
step current available readEntry s | _ | _ = nothing

-- Starting throwTo and its acknowledgment are distinct. Acknowledgment means
-- receipt by the target, including an already terminated target's return from
-- throwTo; it never means this coordinator has waited for handler cleanup.
step current available requestCancellation s with phase s
... | sendReady e w = just (record s { phase = awaitDelivery e w })
... | _ = nothing
step current available acknowledgeDelivery s with phase s
... | awaitDelivery e w = just (record s
  { phase = reading; collected = collected s ++ (w ∷ []) })
... | _ = nothing

-- No per-target result wait occurs during traversal. Even a target whose
-- result is ready cannot shortcut the remaining reads and throwTo deliveries.
step current available finishTraversal s with phase s | remaining s
... | reading | [] = just (record s { phase = awaitResults })
... | _ | _ = nothing
step current available finishClose s with phase s | allAvailable available (collected s)
... | awaitResults | true = just (record s { phase = closed })
... | _ | _ = nothing

-- The source finally uses uninterruptibleMask_: this coordinator has no abort
-- transition. Shared CM stores and result observations may still change between
-- its real steps; closed admits no more coordinator steps, not a global freeze.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as current available} → step current available a s ≡ just s₁ →
    Executes s₁ as s₂ → Executes s (a ∷ as) s₂
