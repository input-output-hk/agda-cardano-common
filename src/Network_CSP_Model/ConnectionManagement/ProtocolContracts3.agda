{-# OPTIONS --guardedness #-}

-- One captured connection, fixed invocations; actual STM/driver/DB returns are
-- source-certified observations. Shared presence is deliberately not a refcount.
module ConnectionManagement.ProtocolContracts3 where
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import ConnectionManagement.Domain using (ErrorId)
open import ConnectionManagement.ProtocolContracts using (Exit; normal; synchronous; cancelled)

data Endpoint : Set where
  notifyClient notifyServer fetchClient fetchServer chainClient : Endpoint
data Wait : Set where
  channel forecast arrival command callback database : Wait
data Phase : Set where
  fresh idle checking fetchCollect : Phase
  blocked : Wait → Phase
  quitting draining donePending : Phase
  innerRelease deleting refunding outerRelease : Exit → Phase
  finished : Exit → Phase
record State : Set where
  constructor state
  field nc ns fc fs cs : Phase
        nd sd fd : ℕ
        present charged : Bool
open State public
initial : State
initial = state fresh fresh fresh fresh fresh 0 0 0 false false
at : Endpoint → State → Phase
at notifyClient = nc
at notifyServer = ns
at fetchClient = fc
at fetchServer = fs
at chainClient = cs
set : Endpoint → Phase → State → State
set notifyClient p s = record s { nc = p }
set notifyServer p s = record s { ns = p }
set fetchClient p s = record s { fc = p }
set fetchServer p s = record s { fs = p }
set chainClient p s = record s { cs = p }
shared : Endpoint → Bool
shared notifyClient = true
shared fetchClient = true
shared chainClient = true
shared _ = false
body : Phase → Bool
body idle = true
body checking = true
body fetchCollect = true
body (blocked _) = true
body quitting = true
body draining = true
body donePending = true
body _ = false
-- Notify server's inner scope is the linked pump; Fetch owns writer/reader.
-- ChainSync has outer candidate/sync brackets, released AFTER shared refund.
leave : Endpoint → Exit → State → State
leave ep e s = set ep (innerRelease e) s

-- Shared cleanup is nested inside ChainSync's candidate and sync brackets.
terminal : Endpoint → Exit → State → State
terminal chainClient e s = set chainClient (outerRelease e) s
terminal ep e s = set ep (finished e) s

-- A nested writer/driver release fault still runs the enclosing shared bracket.
innerFault : Endpoint → Exit → State → State
innerFault ep e s with shared ep
... | true = set ep (deleting e) s
... | false = set ep (finished e) s

data Action : Set where
  start : Endpoint → Action
  acquisitionFailed : Endpoint → Exit → Action
  checkControl : Endpoint → Action
  await : Endpoint → Wait → Action
  ready : Endpoint → Action
  continue terminate : Endpoint → Action
  issue collect : Endpoint → Action
  noCommand : Action
  quitSent : Action
  peerDone doneSent : Endpoint → Action
  chainExited outerClosed : Action
  fail : Endpoint → ErrorId → Action
  receiveCancel : Endpoint → Action
  innerClosed deletePeer refundPeer : Endpoint → Action
  cleanupError : Endpoint → ErrorId → Action
  releaseCancelled : Endpoint → Action
  account : Action

waitAllowed : Endpoint → Wait → Bool
waitAllowed notifyClient channel = true
waitAllowed notifyClient callback = true
waitAllowed notifyServer channel = true
waitAllowed notifyServer command = true
waitAllowed fetchClient callback = true
waitAllowed fetchClient database = true
waitAllowed fetchServer channel = true
waitAllowed fetchServer database = true
waitAllowed _ _ = false
exit : Endpoint → Exit → State → Maybe State
exit ep e s with body (at ep s)
... | true = just (leave ep e s)
... | false = nothing

step : Action → State → Maybe State
step (start ep) s with at ep s | shared ep
... | fresh | true = just (record (set ep idle s) { present = true })
... | fresh | false = just (set ep idle s)
... | _ | _ = nothing
step (acquisitionFailed ep normal) s = nothing
step (acquisitionFailed ep e) s with at ep s
... | fresh = just (terminal ep e s)
... | _ = nothing
step (checkControl notifyClient) s with nc s
... | idle = just (set notifyClient checking s)
... | _ = nothing
step (checkControl fetchClient) s with fc s
... | idle = just (set fetchClient checking s)
... | _ = nothing
step (checkControl _) s = nothing
step (await notifyClient forecast) s with nc s
... | checking = just (set notifyClient (blocked forecast) s)
... | _ = nothing
step (await notifyClient arrival) s with nc s
... | checking = just (set notifyClient (blocked arrival) s)
... | _ = nothing
step (await fetchClient command) s with fc s | fd s
... | checking | zero = just (set fetchClient (blocked command) s)
... | _ | _ = nothing
step (await ep w) s with at ep s | waitAllowed ep w
... | idle | true = just (set ep (blocked w) s)
... | _ | _ = nothing
-- These waits re-run their control transaction; readiness does not invent work.
step (ready notifyClient) s with nc s
... | blocked forecast = just (set notifyClient checking s)
... | blocked arrival = just (set notifyClient checking s)
... | blocked channel = just (set notifyClient idle s)
... | blocked callback = just (set notifyClient idle s)
... | _ = nothing
step (ready fetchClient) s with fc s
... | blocked command = just (set fetchClient checking s)
... | blocked callback = just (set fetchClient idle s)
... | blocked database = just (set fetchClient idle s)
... | _ = nothing
step (ready ep) s with at ep s
... | blocked _ = just (set ep idle s)
... | _ = nothing
step (continue ep) s with at ep s
... | checking = just (set ep idle s)
... | _ = nothing
step (terminate notifyClient) s with nc s
... | checking = just (set notifyClient quitting s)
... | blocked forecast = just (set notifyClient quitting s)
... | blocked arrival = just (set notifyClient quitting s)
... | _ = nothing
step (terminate fetchClient) s with fc s
... | checking = just (set fetchClient draining s)
... | blocked command = just (set fetchClient draining s)
... | _ = nothing
step (terminate _) s = nothing
-- issue certifies the actual depth/credit branch and send (not arbitrary work).
step (issue notifyClient) s with nc s
... | idle = just (record s { nd = suc (nd s) })
... | _ = nothing
step (issue notifyServer) s with ns s
... | idle = just (record s { sd = suc (sd s) })
... | _ = nothing
step (issue fetchClient) s with fc s
... | idle = just (record s { fd = suc (fd s) })
... | _ = nothing
step (issue _) s = nothing
step noCommand s with fc s | fd s
... | checking | suc n = just (set fetchClient fetchCollect s)
... | _ | _ = nothing
step quitSent s with nc s
... | quitting = just (set notifyClient draining s)
... | _ = nothing
step (collect notifyClient) s with nc s | nd s
... | idle | suc n = just (record s { nd = n })
... | draining | suc n = just (record s { nd = n })
... | _ | _ = nothing
step (collect notifyServer) s with ns s | sd s
... | idle | suc n = just (record s { sd = n })
... | draining | suc n = just (record s { sd = n })
... | _ | _ = nothing
step (collect fetchClient) s with fc s | fd s
... | idle | suc n = just (record s { fd = n })
... | fetchCollect | suc n = just (record s { fc = idle ; fd = n })
... | draining | suc n = just (record s { fd = n })
... | _ | _ = nothing
step (collect _) s = nothing
step (peerDone notifyClient) s with nc s | nd s
... | draining | zero = just (leave notifyClient normal s)
... | _ | _ = nothing
-- This input observes received Quit, setting quitVar before any sender flush.
step (peerDone notifyServer) s with ns s
... | idle = just (set notifyServer draining s)
... | blocked command = just (set notifyServer draining s)
... | blocked channel = just (set notifyServer draining s)
... | _ = nothing
step (peerDone fetchServer) s with fs s
... | idle = just (leave fetchServer normal s)
... | blocked channel = just (leave fetchServer normal s)
... | _ = nothing
step (peerDone _) s = nothing
step (doneSent notifyServer) s with ns s | sd s
... | draining | zero = just (leave notifyServer normal s)
... | _ | _ = nothing
step (doneSent fetchClient) s with fc s | fd s
... | draining | zero = just (leave fetchClient normal s)
... | _ | _ = nothing
step (doneSent _) s = nothing
step outerClosed s with cs s
... | outerRelease e = just (set chainClient (finished e) s)
... | _ = nothing
step chainExited s with cs s
... | idle = just (leave chainClient normal s)
... | _ = nothing
step (fail ep e) s = exit ep (synchronous e) s
step (receiveCancel ep) s = exit ep cancelled s
-- innerClosed observes writer/reader close, pump cancel/join+finally, or the
-- ChainSync driver return. Its enclosing candidate/sync cleanup comes later.
step (innerClosed ep) s with at ep s | shared ep
... | innerRelease e | true = just (set ep (deleting e) s)
... | innerRelease e | false = just (set ep (finished e) s)
... | _ | _ = nothing
step (deletePeer ep) s with at ep s
... | deleting e = just (record (set ep (refunding e) s) { present = false })
... | _ = nothing
step (refundPeer ep) s with at ep s
... | refunding e = just (record (terminal ep e s) { charged = false })
... | _ = nothing
-- Abstract decision-loop increment: live-map re-read under outstanding MVar.
step account s with present s
... | true = just (record s { charged = true })
... | false = nothing
step (cleanupError ep err) s with at ep s
... | innerRelease _ = just (innerFault ep (synchronous err) s)
... | deleting _ = just (terminal ep (synchronous err) s)
... | refunding _ = just (terminal ep (synchronous err) s)
... | outerRelease _ = just (set ep (finished (synchronous err)) s)
... | _ = nothing
-- Ordinary bracket masks permit observed interruption at blocking release ops;
-- the pure atomic delete does not itself offer a delivery site.
step (releaseCancelled fetchClient) s with fc s
... | innerRelease _ = just (set fetchClient (deleting cancelled) s)
... | refunding _ = just (set fetchClient (finished cancelled) s)
... | _ = nothing
step (releaseCancelled fetchServer) s with fs s
... | innerRelease _ = just (set fetchServer (finished cancelled) s)
... | _ = nothing
step (releaseCancelled chainClient) s with cs s
... | refunding _ = just (terminal chainClient cancelled s)
... | outerRelease _ = just (set chainClient (finished cancelled) s)
... | _ = nothing
step (releaseCancelled ep) s with at ep s
... | refunding _ = just (terminal ep cancelled s)
... | _ = nothing
