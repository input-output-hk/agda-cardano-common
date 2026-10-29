{-# OPTIONS --guardedness #-}

-- A real infrastructure completion and external stop interleave with invoked
-- DeltaQ. Normal return must not freeze the child FIFO or bypass its priority.
module ConnectionManagement.Negative.MuxDeltaQInterleavings where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; mux; local)
open import ConnectionManagement.IGTypes using (clean)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Negative.MuxDeltaQ as Base
import ConnectionManagement.Negative.MuxDeltaQEffects as E
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
module D = E.D
module Facts = E.Facts
module Prefix = E.Prefix
module R = E.R
module X = E.X
module W = E.W
module G = E.G
module M = E.M
module P = E.P
module Pool = E.Pool
owner : WorkerId
owner = Old.owner
p0 p1 p2 p3 : Pool.State
p0 = E.extraPool E.K.k0
p1 = record p0 { handles = (Old.j₀ , Pool.bodyReturned (T.infraMuxer Old.err)) ∷
  (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ [] }
p2 = record p0 { handles = (Old.j₀ , Pool.deregisterPending Pool.normalExit) ∷
  (Old.j₁ , Pool.bodyRunning) ∷ (Old.j₁₀ , Pool.resultAvailable Pool.normalExit) ∷ []
  ; completions = T.infraMuxer Old.err ∷ [] }
p3 = record p2 { completions = [] }
stopMux : Mux.Mux
stopMux = record (E.mux E.cleanCompletion) { commands = Mux.shutdown ∷ [] }
at : Mux.Mux → Pool.State → M.PC → D.Ticket → D.State
at m pool pc capturedTicket = D.deltaQState
  (R.unwinding (W.handlerExitState (G.shutdownState
    (M.monitorState (Old.snapshot (Old.sourceMux m (E.queue E.cleanCompletion)) pool
      ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ []))
      ((owner , pc) ∷ [])) []) []) []) ((owner , capturedTicket) ∷ [])
d0 d1 d2 d3 d4 d5 d6 : D.State
d0 = E.ready E.cleanCompletion
d1 = at (E.mux E.cleanCompletion) p1 (M.responderTracing clean) (D.ticket Base.cleanPayload D.invoked)
d2 = at stopMux p1 (M.responderTracing clean) (D.ticket Base.cleanPayload D.invoked)
d3 = at stopMux p2 (M.responderTracing clean) (D.ticket Base.cleanPayload D.invoked)
d4 = at stopMux p2 M.waiting (D.ticket Base.cleanPayload D.returned)
d5 = at stopMux p3 (M.selected (T.infraMuxer Old.err)) (D.ticket (T.infraMuxer Old.err) D.captured)
d6 = at (record stopMux { status = Mux.failed Old.err }) p3 (M.deadReady (M.failed Old.err)) (D.ticket (T.infraMuxer Old.err) D.captured)
edge1 : D.step (Base.runM (M.run (P.infrastructureReturn owner T.muxer Old.err))) d0 ≡ just d1
edge1 = refl
edge2 : D.step (D.run (R.run (X.run (W.run (G.requestShutdown owner))))) d1 ≡ just d2
edge2 = refl
edge3 : D.step (Base.runM (M.run (P.publishInfra owner T.muxer))) d2 ≡ just d3
edge3 = refl
edge4 : D.step (D.observeReturn owner) d3 ≡ just d4
edge4 = refl
edge5 : D.step (Base.runM (M.consume owner)) d4 ≡ just d5
edge5 = refl
edge6 : D.step (Base.runM (M.handleSelected owner)) d5 ≡ just d6
edge6 = refl
actions : List D.Action
actions = Base.runM (M.run (P.infrastructureReturn owner T.muxer Old.err)) ∷
  D.run (R.run (X.run (W.run (G.requestShutdown owner)))) ∷
  Base.runM (M.run (P.publishInfra owner T.muxer)) ∷ D.observeReturn owner ∷
  Base.runM (M.consume owner) ∷ Base.runM (M.handleSelected owner) ∷ []
path : D.Executes d0 actions d6
path = D.next edge1 (D.next edge2 (D.next edge3 (D.next edge4 (D.next edge5 (D.next edge6 D.done)))))
abstract
  initialized : D.Executes Base.start (E.readyActions E.cleanCompletion ++ actions) d6
  initialized = Prefix.append (E.initialized-ready E.cleanCompletion) path
physical-result-outranks-stop : D.step (D.run (R.run (X.run (W.run (G.selectShutdown owner))))) d4 ≡ nothing
physical-result-outranks-stop = refl
no-stale-protocol-ticket : lookup owner (D.tickets d5) ≡ just (D.ticket (T.infraMuxer Old.err) D.captured)
no-stale-protocol-ticket = refl
new-head-has-physical-origin : Base.Captured.CapturedHead owner d4 d5
new-head-has-physical-origin = Base.Captured.consume-captures-head owner d4 edge5
no-DeltaQ-for-new-infrastructure-result : D.step (D.beginDeltaQ owner) d6 ≡ nothing
no-DeltaQ-for-new-infrastructure-result = refl
source-and-pool-paths : Facts.Paths Base.start d6
source-and-pool-paths = Facts.exec-projects initialized

-- Positive control: with the same owner, pending stop, callback and physical
-- registry, removing only the result backlog allows shutdown selection.
emptyStop : D.State
emptyStop = at stopMux p3 M.waiting (D.ticket Base.cleanPayload D.returned)
selectedEmptyStop : D.State
selectedEmptyStop = record clear
  { base = record (D.base clear) { base = record (R.base (D.base clear))
    { base = G.setPhase owner G.shutdownSelected (W.base (R.base (D.base clear))) } } }
  where
  clear : D.State
  clear = at (E.mux E.cleanCompletion) p3 M.waiting (D.ticket Base.cleanPayload D.returned)
empty-result-backlog-allows-stop : D.step (D.run (R.run (X.run (W.run (G.selectShutdown owner))))) emptyStop ≡ just selectedEmptyStop
empty-result-backlog-allows-stop = refl

-- Conditional forged-PC controls: a callback marker is not a certificate of
-- physical startup or a still-open bracket. These are not reachable witnesses.
partialStartupGhost : D.State
partialStartupGhost = D.deltaQState
  (R.unwinding (W.handlerExitState (G.shutdownState
    (M.monitorState (Old.at (Old.sourceMux (E.mux E.cleanCompletion) (E.queue E.cleanCompletion))
      (G.Startup.startupState G.Startup.published p0)
      ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ []))
      ((owner , M.responderTracing clean) ∷ [])) []) []) [])
  ((owner , D.ticket Base.cleanPayload D.captured) ∷ [])
closedPoolGhost : D.State
closedPoolGhost = at (E.mux E.cleanCompletion) (E.extraPool E.K.k14)
  (M.responderTracing clean) (D.ticket Base.cleanPayload D.captured)
no-callback-adoption-from-partial-startup : D.step (D.beginDeltaQ owner) partialStartupGhost ≡ nothing
no-callback-adoption-from-partial-startup = refl
no-callback-adoption-after-pool-close : D.step (D.beginDeltaQ owner) closedPoolGhost ≡ nothing
no-callback-adoption-after-pool-close = refl
