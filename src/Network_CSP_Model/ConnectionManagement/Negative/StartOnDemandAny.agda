{-# OPTIONS --guardedness #-}

-- Source demand is a nonempty ingress observation on a registered waiter.
-- This local scheduler example deliberately registers in reverse Map order.
module ConnectionManagement.Negative.StartOnDemandAny where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Scenarios.Admission as A

m : M.Mux
m = M.muxState A.key₀ M.ready
  ((2 , M.demand) ∷ (8 , M.demandAny) ∷ (19 , M.demandAny) ∷ []) []
  ((19 , onDemandAny) ∷ (8 , onDemandAny) ∷ (2 , onDemand) ∷ []) [] [] []
  nothing M.returned M.noIGTracer
r : M.Mux → IG.Runtime
r value = record IG.initial { execution = record IG.emptyEngine { muxes = (ident 0 , value) ∷ [] } }
selected : M.Mux
selected = record m { demandGroup = just (just 2); pendingStarts = 8 ∷ 19 ∷ []; callback = M.afterStart 2 }
ordinary-triggers-all : IG.stepWorker (IG.startOnDemand (ident 0) 2) (r m) [] ≡ just (r selected , [])
ordinary-triggers-all = refl
any-selected : M.Mux
any-selected = record m { demandGroup = just nothing; pendingStarts = 19 ∷ []; callback = M.afterStart 8 }
any-self-trigger-in-map-order : IG.stepWorker (IG.startOnDemand (ident 0) 19) (r m) [] ≡ just (r any-selected , [])
any-self-trigger-in-map-order = refl
status-first : M.Mux
status-first = record selected { protocols = (2 , M.running) ∷ (8 , M.demandAny) ∷ (19 , M.demandAny) ∷ []; callback = M.forkPending 2 }
separate-status : IG.stepWorker (IG.finishStart (ident 0)) (r selected) [] ≡ just (r status-first , [])
separate-status = refl
next : M.Mux
next = record status-first { runningJobs = 2 ∷ []; pendingStarts = 19 ∷ []; callback = M.afterStart 8 }
separate-fork : IG.stepWorker (IG.forkResponder (ident 0)) (r status-first) [] ≡ just (r next , [])
separate-fork = refl
-- CmdShutdown arriving during a chosen group waits for its sequential starts.
queued-stop-does-not-skip-next : IG.stepWorker (IG.forkResponder (ident 0))
  (r (record status-first { commands = M.shutdown ∷ [] })) [] ≡
  just (r (record next { commands = M.shutdown ∷ [] }) , [])
queued-stop-does-not-skip-next = refl
no-command-between-group-starts : IG.stepWorker (IG.monitorCommand (ident 0)) (r next) [] ≡ nothing
no-command-between-group-starts = refl
no-double-start : IG.stepWorker (IG.startOnDemand (ident 0) 2) (r selected) [] ≡ nothing
no-double-start = refl
no-absent-waiter : IG.stepWorker (IG.startOnDemand (ident 0) 3) (r m) [] ≡ nothing
no-absent-waiter = refl
no-wrong-mux : IG.stepWorker (IG.startOnDemand (ident 1) 8) (r m) [] ≡ nothing
no-wrong-mux = refl
shutdown-wins : IG.stepWorker (IG.startOnDemand (ident 0) 8) (r (record m { commands = M.shutdown ∷ [] })) [] ≡ nothing
shutdown-wins = refl
result-wins : IG.stepWorker (IG.startOnDemand (ident 0) 8)
  (r (record m { completions = M.jobResult M.initiatorJob 2 clean ∷ [] })) [] ≡ nothing
result-wins = refl
no-stopped-demand : IG.stepWorker (IG.startOnDemand (ident 0) 8) (r (record m { status = M.stopped })) [] ≡ nothing
no-stopped-demand = refl
no-premature-fork : IG.stepWorker (IG.forkResponder (ident 0)) (r selected) [] ≡ nothing
no-premature-fork = refl
no-premature-result : IG.stepWorker (IG.finishProtocol (ident 0) 8 clean) (r next) [] ≡ nothing
no-premature-result = refl
no-restart-after-clean : IG.stepWorker (IG.startOnDemand (ident 0) 8)
  (r (record m { waiting = []; protocols = (8 , M.idle) ∷ [] })) [] ≡ nothing
no-restart-after-clean = refl

second-status : M.Mux
second-status = record next { protocols = (2 , M.running) ∷ (8 , M.running) ∷ (19 , M.demandAny) ∷ []; callback = M.forkPending 8 }
second-status-edge : IG.stepWorker (IG.finishStart (ident 0)) (r next) [] ≡ just (r second-status , [])
second-status-edge = refl
third : M.Mux
third = record second-status { runningJobs = 8 ∷ 2 ∷ []; pendingStarts = []; callback = M.afterStart 19 }
second-fork-edge : IG.stepWorker (IG.forkResponder (ident 0)) (r second-status) [] ≡ just (r third , [])
second-fork-edge = refl
third-status : M.Mux
third-status = record third { protocols = (2 , M.running) ∷ (8 , M.running) ∷ (19 , M.running) ∷ []; callback = M.forkPending 19 }
third-status-edge : IG.stepWorker (IG.finishStart (ident 0)) (r third) [] ≡ just (r third-status , [])
third-status-edge = refl
finished : M.Mux
finished = record third-status { waiting = []; demandGroup = nothing; runningJobs = 19 ∷ 8 ∷ 2 ∷ []; callback = M.returned }
final-fork-clears-group : IG.stepWorker (IG.forkResponder (ident 0)) (r third-status) [] ≡ just (r finished , [])
final-fork-clears-group = refl
no-second-start-of-group : IG.stepWorker (IG.startOnDemand (ident 0) 19) (r finished) [] ≡ nothing
no-second-start-of-group = refl
no-later-fork-through-blocked-tracer : IG.stepWorker (IG.forkResponder (ident 0))
  (r (record next { tracerAttachment = M.igTracer; callback = M.readActive (M.started 8) })) [] ≡ nothing
no-later-fork-through-blocked-tracer = refl

-- Registration sets readiness and queues a command; it does not fork a child.
idle8 : M.Mux
idle8 = record m { protocols = (8 , M.idle) ∷ []; waiting = [] }
registered8 : M.Mux
registered8 = record idle8 { protocols = (8 , M.demandAny) ∷ [];
  commands = M.startCommand (protocol 8 established onDemandAny) ∷ [] }
any-registers-before-demand : M.startOne (protocol 8 established onDemandAny) idle8 ≡ M.startedAll registered8
any-registers-before-demand = refl
any-command-parks : IG.stepWorker (IG.monitorCommand (ident 0)) (r registered8) [] ≡
  just (r (record registered8 { commands = []; waiting = (8 , onDemandAny) ∷ [] }) , [])
any-command-parks = refl

-- Accepting Any does not relax the installer's distinct ordered-number guard.
duplicate-any-install-refused : IG.stepWorker
  (IG.installHandle (ident 0) (ident 0) A.key₀
    (protocol 8 established onDemandAny ∷ protocol 8 established onDemandAny ∷ []) duplex)
  IG.initial [] ≡ nothing
duplicate-any-install-refused = refl
