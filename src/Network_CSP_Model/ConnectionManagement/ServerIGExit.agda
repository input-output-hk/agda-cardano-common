{-# OPTIONS --guardedness #-}

-- Pinned IG catch: interrupt a caller-run CM operation, deactivate, drain,
-- snapshot published remote states, trace to Nothing, then rethrow. Selected
-- masked receipts require observed blocking reads/throwTo, not just a PC.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.ServerIGExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.ConnectionOrder as Order
private
  module S = Server isBearerClosed

-- These are observation sites, not assumptions that every call must block.
data Site : Set where
  loopBoundary batchWait releaseRead releaseCounters releaseSend
    promoteRead promoteCounters promoteSend demoteBoundary : Site
data Pending : Set where
  releaseCall : Release.Frame → Pending
  remoteCall : Remote.Frame → Pending
record Receipt : Set where
  constructor receipt
  field site : Site
        exception : ErrorId
        interrupted : Maybe Pending
open Receipt public
data RemoteView : Set where
  idle cold warm hot : RemoteView
Row = ConnectionKey × RemoteView
view : IG.RemoteState → RemoteView
view (IG.remoteIdle _) = idle
view IG.remoteCold = cold
view IG.remoteWarm = warm
view IG.remoteHot = hot

-- Source Map traversal uses ConnectionId's remote-first order. The address
-- comparison remains the existing explicit abstraction, not OS address order.
insertRow : Row → List Row → List Row
insertRow row [] = row ∷ []
insertRow row (head ∷ rest) with Order.keyLess (proj₁ row) (proj₁ head)
... | true = row ∷ head ∷ rest
... | false = head ∷ insertRow row rest
sortRows : List Row → List Row
sortRows [] = []
sortRows (row ∷ rest) = insertRow row (sortRows rest)
snapshotRows : Store ConnectionKey IG.Registration → List Row
snapshotRows regs = sortRows (map (λ { (key , reg) → key , view (IG.remoteState reg) }) regs)
unique : Store ConnectionKey IG.Registration → Bool
unique [] = true
unique ((key , reg) ∷ rest) with lookup key rest
... | just _ = false
... | nothing = unique rest

data Phase : Set where
  live caught traversing invoked failed bodyDone : Phase
record Exit : Set where
  constructor exitState
  field phase : Phase
        received : Maybe Receipt
        snapshot remaining returned : List Row
        outcome result : Maybe S.Fault
open Exit public
emptyExit : Exit
emptyExit = exitState live nothing [] [] [] nothing nothing
record State : Set where
  constructor igExitState
  field base : S.State
        exit : Exit
open State public
source : State → O.Configuration
source s = S.source (base s)
governor : State → IG.Runtime
governor s = Machine.inboundGovernor (O.core (source s))
initial : O.Configuration → Maybe State
initial c with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c
... | nothing | nothing | just server = just (igExitState server emptyExit)
... | _ | _ | _ = nothing

-- readTMVar does not take a map lease. Unwinding these local call frames has
-- no map restoration or handler delivery; all already committed writes remain.
clearPending : O.Configuration → O.Configuration
clearPending c = record c { core = record (O.core c) { inboundRelease = nothing; remoteCall = nothing } }
blockedMap : State → Bool
blockedMap s with Shared.mapCell (Shared.cm (S.shared (base s)))
... | Shared.taken _ = true
... | Shared.full _ = false
bodyReady : Site → IG.PC → Bool
bodyReady loopBoundary IG.sampleTime = true
bodyReady batchWait (IG.awaitBatch _ _) = true
bodyReady _ _ = false
releaseReady : Site → Release.Frame → State → Bool
releaseReady releaseRead f s with Release.pc f
... | Release.transaction = blockedMap s
... | _ = false
releaseReady releaseCounters f s with Release.pc f
... | Release.counters = blockedMap s
... | _ = false
releaseReady releaseSend f s with Release.pc f
... | Release.delivering _ = true
... | _ = false
releaseReady _ _ _ = false
unmaskedDemote : Remote.PC → Bool
unmaskedDemote Remote.transaction = true
unmaskedDemote Remote.assertion = true
unmaskedDemote Remote.counters = true
unmaskedDemote Remote.returning = true
unmaskedDemote _ = false
remoteReady : Site → Remote.Frame → State → Bool
remoteReady demoteBoundary f s with Remote.operation f
... | Remote.demote = unmaskedDemote (Remote.pc f)
... | Remote.promote = false
remoteReady promoteRead f s with Remote.operation f | Remote.pc f
... | Remote.promote | Remote.transaction = blockedMap s
... | _ | _ = false
remoteReady promoteCounters f s with Remote.operation f | Remote.pc f
... | Remote.promote | Remote.counters = blockedMap s
... | _ | _ = false
remoteReady promoteSend f s with Remote.operation f | Remote.pc f
... | Remote.promote | Remote.awaitDelivery _ _ = true
... | _ | _ = false
remoteReady _ _ _ = false

-- Receipt is coupled to the exact active continuation; ambiguous dual frames
-- and masked nonblocking sites are refused. Send sites observe a blocked throwTo
-- before target receipt, not an acknowledgment or a join of that target.
receptionOpen : State → Bool
receptionOpen s with phase (exit s) | received (exit s) | S.stage (base s) | IG.active (IG.execution (governor s))
... | live | nothing | S.igCancelRequested | true = true
... | _ | _ | _ | _ = false
inCM : IG.PC → Bool
inCM IG.inCM = true
inCM _ = false
selectReceipt : Site → ErrorId → State → Maybe Receipt
selectReceipt at err s with receptionOpen s
... | false = nothing
... | true with Machine.inboundRelease (O.core (source s)) | Machine.remoteCall (O.core (source s))
...   | nothing | nothing with bodyReady at (IG.continuation (governor s))
...     | true = just (receipt at err nothing)
...     | false = nothing
selectReceipt at err s | true | just f | nothing with inCM (IG.continuation (governor s)) | releaseReady at f s
... | true | true = just (receipt at err (just (releaseCall f)))
... | false | _ = nothing
... | true | false = nothing
selectReceipt at err s | true | nothing | just f with inCM (IG.continuation (governor s)) | remoteReady at f s
... | true | true = just (receipt at err (just (remoteCall f)))
... | false | _ = nothing
... | true | false = nothing
selectReceipt at err s | true | just _ | just _ = nothing
caughtExit : Receipt → Exit
caughtExit r = exitState caught (just r) [] [] [] (just (S.async (exception r))) nothing

-- Other actors keep their lower permissions. The IG cannot resume its own
-- abandoned loop/call; raw catch-entry/body-exit shortcuts are not admitted.
igProgress : Machine.Action → Bool
igProgress (Machine.releaseStep _) = true
igProgress (Machine.remoteStep _) = true
igProgress (Machine.igStep a) = S.igBodyAction a
igProgress _ = false
runAllowed : S.Action → State → Bool
runAllowed (S.scope S.deliverIGBody) s = false
runAllowed (S.scope S.finishIGBody) s = false
runAllowed (S.run a) s with phase (exit s) | S.machineAction a
... | live | _ = true
... | _ | just a with igProgress a
...   | true = false
...   | false = true
runAllowed (S.run a) s | _ | nothing = true
runAllowed _ _ = true
delegateExit : S.Action → Exit → Maybe Exit
delegateExit (S.scope S.publishIGResult) e with phase e | outcome e | result e
... | bodyDone | just err | nothing = just (record e { result = just err })
... | _ | _ | _ = nothing
delegateExit _ e = just e

-- Plans distinguish real base steps, local bookkeeping, local-call unwind and
-- IG body exit. This keeps invariant proofs independent of full normalization.
data Plan : Set where
  delegate : S.Action → Exit → Plan
  local : Exit → Plan
  abandon : Receipt → Plan
  finish : Exit → Plan
data Action : Set where
  run : S.Action → Action
  receive : Site → ErrorId → Action
  captureSnapshot invokeFinal returnFinal finishFinal : Action
  failFinal : S.Fault → Action
choose : Action → State → Maybe Plan
choose (run a) s with runAllowed a s
... | false = nothing
... | true with delegateExit a (exit s)
...   | nothing = nothing
...   | just e = just (delegate a e)
choose (receive at err) s with selectReceipt at err s
... | nothing = nothing
... | just r = just (abandon r)
choose captureSnapshot s with phase (exit s) | S.stage (base s) | IG.active (IG.execution (governor s)) |
  IG.continuation (governor s) | Machine.inboundRelease (O.core (source s)) | Machine.remoteCall (O.core (source s)) |
  unique (IG.connections (IG.publishedState (governor s)))
... | caught | S.igFlushed | false | IG.exited | nothing | nothing | true = just (local (record (exit s)
  { phase = traversing; snapshot = rows; remaining = rows; returned = [] }))
  where rows = snapshotRows (IG.connections (IG.publishedState (governor s)))
... | _ | _ | _ | _ | _ | _ | _ = nothing
choose invokeFinal s with phase (exit s) | remaining (exit s)
... | traversing | row ∷ rest = just (local (record (exit s) { phase = invoked }))
... | _ | _ = nothing
choose returnFinal s with phase (exit s) | remaining (exit s)
... | invoked | row ∷ rest = just (local (record (exit s)
  { phase = traversing; remaining = rest; returned = returned (exit s) ++ (row ∷ []) }))
... | _ | _ = nothing
-- An async failure here observes an interruptible blocking tracer operation in
-- the masked catch handler. Invocation alone implies no callback completion.
choose (failFinal err) s with phase (exit s) | remaining (exit s)
... | invoked | row ∷ rest = just (local (record (exit s) { phase = failed; outcome = just err }))
... | _ | _ = nothing
choose finishFinal s with phase (exit s) | remaining (exit s) | outcome (exit s) | S.stage (base s)
... | traversing | [] | just err | S.igFlushed = just (finish (record (exit s) { phase = bodyDone }))
... | failed | _ | just err | S.igFlushed = just (finish (record (exit s) { phase = bodyDone }))
... | _ | _ | _ | _ = nothing
enact : Plan → State → Maybe State
enact (delegate a e) s with S.step a (base s)
... | nothing = nothing
... | just server = just (igExitState server e)
enact (local e) s = just (record s { exit = e })
enact (abandon r) s = just (igExitState
  (record (S.setSource (clearPending (source s)) (base s)) { stage = S.igCancelDelivered }) (caughtExit r))
enact (finish e) s = just (igExitState (record (base s) { stage = S.igBodyExited }) e)
step : Action → State → Maybe State
step a s with choose a s
... | nothing = nothing
... | just p = enact p s
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s t u a as} → step a s ≡ just t → Executes t as u → Executes s (a ∷ as) u
