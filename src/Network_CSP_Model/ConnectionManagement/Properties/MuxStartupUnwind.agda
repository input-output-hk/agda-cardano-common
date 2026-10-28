{-# OPTIONS --guardedness #-}

-- Every selected fault, partial-startup close and handoff retains the actual
-- source and same physical-pool history. Source/operation observations remain
-- explicit; no universal progress or implementation refinement is asserted.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxStartupUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain using (WorkerId; MuxId; HandleId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.MuxStartupUnwind as Unwind
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Properties.MuxExitCancellation as CancellationFacts
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.MuxGroupShutdown as GroupFacts
import ConnectionManagement.Properties.MuxProtocolJobs as ProtocolFacts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseFacts
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
private
  module R = Unwind isBearerClosed
  module X = Cancellation isBearerClosed
  module W = Exit isBearerClosed
  module G = W.G
  module U = G.U
  module P = G.P
  module Pool = G.Pool
  module Base = ExitFacts isBearerClosed
  module Cancel = CancellationFacts isBearerClosed
  module Group = GroupFacts isBearerClosed
module PoolFacts = CloseFacts Types.TypedResult true
Paths : R.State → R.State → Set
Paths before after = Base.Paths (R.base before) (R.base after)
idle : ∀ s → Paths s s
idle s = Base.idle (R.base s)
compose : ∀ {p q r} → Paths p q → Paths q r → Paths p r
compose {p} {q} {r} = Base.compose {p = R.base p} {q = R.base q} {r = R.base r}
source-step : ∀ action s {c} → O.advance action (R.source s) ≡ just c → Paths s (R.setSource c s)
source-step action s eq = Base.source-step action (R.base s) eq
pool-step : ∀ w u action s {p} → Pool.step action (R.poolAt w s) ≡ just p → Paths s (R.setPool w u p s)
pool-step w u action s eq = Base.from-base (R.base s) _ (Group.pool-step w u action (W.base (R.base s)) eq)
metadata : ∀ s fs → Paths s (record s { faults = fs })
metadata s fs = Base.idle (R.base s)
enact-projects : ∀ plan s {s′} → R.enact plan s ≡ just s′ → Paths s s′
enact-projects (R.local fs) s eq = case just-injective eq of λ { refl → metadata s fs }
enact-projects (R.machine action fs) s eq with O.advance action (R.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → Base.compose (source-step action s advanced) (metadata (R.setSource c s) fs) }
enact-projects (R.pool w u action fs) s eq with Pool.step action (R.poolAt w s) in advanced
... | nothing = case eq of λ ()
... | just p = case just-injective eq of λ { refl → Base.compose (pool-step w u action s advanced) (metadata (R.setPool w u p s) fs) }
enact-projects (R.inherited action) s eq with X.step action (R.base s) in advanced
... | nothing = case eq of λ ()
... | just x = case just-injective eq of λ { refl → Cancel.step-projects action (R.base s) advanced }
enact-projects (R.transfer w f fs) s eq = case just-injective eq of λ { refl → Base.metadata (R.base s) (put w f (W.exits (R.base s))) }
enact-projects (R.acknowledge plan) s eq with R.enact plan s in delivered
... | nothing = case eq of λ ()
... | just next with W.control Close.acknowledgeDelivery (R.base next) in acknowledged
...   | nothing = case eq of λ ()
...   | just x = case just-injective eq of λ { refl → Base.compose (enact-projects plan s delivered) (Base.control-projects Close.acknowledgeDelivery (R.base next) acknowledged) }
step-projects : ∀ action s {s′} → R.step action s ≡ just s′ → Paths s s′
step-projects action s eq with R.choose action s
... | nothing = case eq of λ ()
... | just plan = enact-projects plan s eq
exec-projects : ∀ {s actions s′} → R.Executes s actions s′ → Paths s s′
exec-projects (R.done {s = s}) = idle s
exec-projects (R.next {s = s} {a = action} eq tail) = Base.compose (step-projects action s eq) (exec-projects tail)
initial-base : ∀ c {s} → R.initial c ≡ just s → X.initial c ≡ just (R.base s)
initial-base c eq with X.initial c
... | nothing = case eq of λ ()
... | just x = case just-injective eq of λ { refl → refl }
initial-source : ∀ c {s} → R.initial c ≡ just s → R.source s ≡ c
initial-source c initialized = Base.initial-source c (initial-base c initialized)
pool-from-initial : ∀ {c start actions s} → R.initial c ≡ just start → R.Executes start actions s →
  ∀ selected → ProtocolFacts.PTrace Pool.initial (R.poolAt selected s)
pool-from-initial {c} initialized path selected = ProtocolFacts.trace-left
  (sym (Base.initial-pool c (initial-base c initialized) selected)) (Base.pools (exec-projects path) selected)
from-initial-captures : ∀ {c start actions s} → R.initial (O.initial c) ≡ just start → R.Executes start actions s → Capture.Captures (R.source s)
from-initial-captures {c} initialized path = Capture.exec-preserves
  (subst Capture.Captures (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c)) (proj₂ (Base.machine (exec-projects path)))
from-initial-supply : ∀ {c start actions s} → R.initial (O.initial c) ≡ just start → SupplyBounds (Machine.world c) →
  R.Executes start actions s → Supply.Valid (R.source s)
from-initial-supply {c} initialized bounds path = Supply.exec-preserves
  (subst Supply.Valid (sym (initial-source (O.initial c) initialized)) (Capture.initial-valid c , bounds)) (proj₂ (Base.machine (exec-projects path)))
whole-closed-from-initial : ∀ {c start actions s} → R.initial c ≡ just start → R.Executes start actions s →
  ∀ selected → Pool.phase (R.poolAt selected s) ≡ Pool.closedPool →
  ∀ j → j ∈ Pool.snapshot (R.poolAt selected s) → PoolFacts.Terminal (R.poolAt selected s) j
whole-closed-from-initial initialized path selected closed = PoolFacts.from-initial (proj₂ (pool-from-initial initialized path selected)) closed

owner-pool : ∀ w s u → R.owner w s ≡ just u → R.poolAt w s ≡ G.Startup.pool (U.startup u)
owner-pool w s u eq with lookup w (U.frames (P.base (R.protocols s)))
... | nothing = case eq of λ ()
... | just f = case just-injective eq of λ { refl → refl }

-- Exact selection evidence preserves the source callback even when it threw;
-- it does not turn failure/abandonment into a fabricated successful return.
record Selection (w : WorkerId) (result : R.Exception)
  (route : U.Frame → Mux.Mux → Maybe R.Route) (s : R.State) (plan : R.Plan) : Set where
  constructor selection
  field ownerFrame : U.Frame
        handle : HandleId
        mux : MuxId
        muxValue : Mux.Mux
        selectedRoute : R.Route
        free-before : R.free w s ≡ true
        owner-found : R.owner w s ≡ just ownerFrame
        exit-absent : lookup w (W.exits (R.base s)) ≡ nothing
        parent-settled : P.noParent (R.poolAt w s) ≡ true
        published : U.progress ownerFrame ≡ U.promisePublished handle mux
        mux-found : P.muxAt mux (R.protocols s) ≡ just muxValue
        observed-route : route ownerFrame muxValue ≡ just selectedRoute
        plan-shape : plan ≡ R.local (put w (R.fault (U.captured ownerFrame) mux
          (G.Startup.phase (U.startup ownerFrame)) (Mux.callback muxValue) selectedRoute result (R.routePC selectedRoute)) (R.faults s))
selection-observation : ∀ w result route s {plan} → R.start w result route s ≡ just plan → Selection w result route s plan
selection-observation w result route s eq with R.free w s in free | R.owner w s in found |
  lookup w (W.exits (R.base s)) in absent | P.noParent (R.poolAt w s) in settled
... | true | just u | nothing | true with U.progress u in published
...   | U.promisePublished hid mid with P.muxAt mid (R.protocols s) in muxFound
...     | nothing = case eq of λ ()
...     | just m with route u m in routed
...       | nothing = case eq of λ ()
...       | just r = selection u hid mid m r free found absent
          (subst (λ p → P.noParent p ≡ true) (sym (owner-pool w s u found)) settled) published muxFound routed (sym (just-injective eq))
selection-observation w result route s eq | true | just u | nothing | true | U.returnedSuccess = case eq of λ ()
selection-observation w result route s eq | true | just u | nothing | true | U.handleAllocated _ _ = case eq of λ ()
selection-observation w result route s eq | false | _ | _ | _ = case eq of λ ()
selection-observation w result route s eq | true | nothing | _ | _ = case eq of λ ()
selection-observation w result route s eq | true | just _ | just _ | _ = case eq of λ ()
selection-observation w result route s eq | true | just _ | nothing | false = case eq of λ ()

-- Generic initialized lifts keep concrete tests from reducing the whole
-- controller while proving inherited prefix steps. No guard is removed.
wrap : X.State → R.State
wrap x = R.unwinding x []
lift-step : ∀ action x {x′} → X.step action x ≡ just x′ → R.step (R.run action) (wrap x) ≡ just (wrap x′)
lift-step action x eq with X.step action x
... | nothing = case eq of λ ()
... | just x′ = case just-injective eq of λ { refl → refl }
lift : ∀ {s actions s′} → X.Executes s actions s′ → R.Executes (wrap s) (map R.run actions) (wrap s′)
lift X.done = R.done
lift (X.next {s = s} {a = action} eq tail) = R.next (lift-step action s eq) (lift tail)
append : ∀ {s as t bs u} → R.Executes s as t → R.Executes t bs u → R.Executes s (as ++ bs) u
append R.done tail = tail
append (R.next eq rest) tail = R.next eq (append rest tail)

-- Retain the actual nested wrapper call when the shared CM final wait uses a
-- result produced by this new startup/unwind route.
inherited-observation : ∀ action s {s′} → R.step (R.run action) s ≡ just s′ →
  Σ X.State (λ x → X.step action (R.base s) ≡ just x × s′ ≡ record s { base = x })
inherited-observation action s eq with R.allowed action s
... | false = case eq of λ ()
... | true with X.step action (R.base s) in advanced
...   | nothing = case eq of λ ()
...   | just x = x , refl , sym (just-injective eq)
physical-wait : ∀ s {s′} → R.step (R.run (X.run (W.shutdownStep Close.finishClose))) s ≡ just s′ →
  Base.PhysicalWait (R.base s) (R.base s′)
physical-wait s eq with inherited-observation (X.run (W.shutdownStep Close.finishClose)) s eq
... | x , advanced , refl = Base.physical-wait-observation (R.base s) advanced
