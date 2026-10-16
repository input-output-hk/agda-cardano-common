{-# OPTIONS --guardedness #-}

-- A forged outbound continuation refutes heap-only supply preservation.
-- This is not a source-reachable execution or a counterexample to an invariant
-- that also validates captured entries. The production rules are unchanged.
module ConnectionManagement.Negative.OutboundSupply where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as G
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.OutboundGovernor as OG
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
open import ConnectionManagement.Properties.Ownership using (Ownership)
open import ConnectionManagement.Scenarios.Admission using (fixture; emptyCM; remoteAddr)

-- The initial world has no allocated entries or promises.
emptyWorld : S.State
emptyWorld = fixture emptyCM

-- Entry zero is not allocated: a forged frame nevertheless captures it.
request : A.Request
request = A.acquireRequest remoteAddr (ident 3) (ident 0) outbound nothing

-- Only the outbound frame is injected; the heap-only invariant cannot see it.
before : O.Configuration
before = record (O.initial (I.initial S.responderMode emptyWorld))
  { acquiring = (ident 10 , A.frame request (A.removeError (ident 0) C.connectionExists)) ∷ [] }

-- Removal can insert the captured entry without advancing its supply.
afterWorld : S.State
afterWorld = record emptyWorld { cm = S.cmStore (S.full [])
  ((ident 0 , S.terminated nothing) ∷ []) 0 }

-- The actual dispatcher result retains the forged capture in a counter phase.
after : O.Configuration
after = record before
  { core = I.replaceWorld (O.core before) afterWorld
  ; acquiring = (ident 10 , A.frame request (A.count (A.complete (C.raised C.connectionExists)))) ∷ [] }

-- The heap and promise list satisfy the unextended invariant initially.
before-bounded : SupplyBounds (I.world (O.core before))
before-bounded = [] , []

-- This is an enabled step, rather than an arbitrary post-state injection.
removal-step : O.advance (O.acquire (ident 10) A.removeReservation) before ≡ just after
removal-step = refl

-- Entry zero cannot be strictly below supply zero.
after-not-bounded : ¬ SupplyBounds (I.world (O.core after))
after-not-bounded (() ∷ _ , _)

-- Thus the direct analogue of the inbound one-step theorem is false.
no-heap-only-outbound-preservation : ¬ (∀ a c {c′} → O.advance a c ≡ just c′ →
  SupplyBounds (I.world (O.core c)) → SupplyBounds (I.world (O.core c′)))
no-heap-only-outbound-preservation preserve =
  after-not-bounded (preserve (O.acquire (ident 10) A.removeReservation) before removal-step before-bounded)

-- An empty ordinary governor does not repair an invalid captured CM frame.
governor : OG.State
governor = OG.governorState (OG.targets 0 0 0) [] [] [] [] [] [] [] []

-- Lift the exact same counterexample through the subsystem's core action.
subBefore : G.Configuration
subBefore = G.initial before governor

-- The subsystem changes only its embedded CM on this action.
subAfter : G.Configuration
subAfter = record subBefore { world = J.world after [] }

-- The shared-world writer is reachable in one step from the injected frame.
subsystem-step : G.advance (G.core (O.acquire (ident 10) A.removeReservation)) subBefore ≡ just subAfter
subsystem-step = refl

-- The unextended heap-only theorem fails for the combined dispatcher too.
no-heap-only-subsystem-preservation : ¬ (∀ a c {c′} → G.advance a c ≡ just c′ →
  SupplyBounds (I.world (O.core (J.cm (G.world c)))) →
  SupplyBounds (I.world (O.core (J.cm (G.world c′)))))
no-heap-only-subsystem-preservation preserve = after-not-bounded
  (preserve (G.core (O.acquire (ident 10) A.removeReservation)) subBefore subsystem-step before-bounded)

-- The defect in the proposed premise is independent of map-lock ownership.
before-owned : Ownership (I.world (O.core before))
before-owned = refl

-- Cleanup still preserves the exact lease census in this counterexample.
after-owned : Ownership (I.world (O.core after))
after-owned = refl

import ConnectionManagement.Properties.OutboundCapture as Capture

-- The stronger capture certificate rejects precisely the forged reference.
forged-capture-invalid : ¬ Capture.Valid
  (A.frame request (A.removeError (ident 0) C.connectionExists)) emptyWorld
forged-capture-invalid (_ , ())

-- No finite single-caller acquisition run from selecting reaches this frame
-- over the empty heap, even when the starting world is otherwise arbitrary.
forged-not-an-acquisition-run : ∀ caller mode req s actions →
  ¬ Capture.Runs caller mode (A.frame req A.selecting) s actions
    (A.frame request (A.removeError (ident 0) C.connectionExists)) emptyWorld
forged-not-an-acquisition-run caller mode req s actions path =
  forged-capture-invalid (Capture.from-selecting-valid path)

import ConnectionManagement.Properties.OutboundRuntimeCapture as RuntimeCapture

-- Full inbound/release/other-caller interleavings cannot create the forged
-- acquisition frame from OutboundMachine.initial either.
forged-not-an-outbound-execution : ∀ c actions →
  ¬ O.Executes (O.initial c) actions before
forged-not-an-outbound-execution c actions path with RuntimeCapture.from-initial path
... | valid ∷ rest = forged-capture-invalid valid
