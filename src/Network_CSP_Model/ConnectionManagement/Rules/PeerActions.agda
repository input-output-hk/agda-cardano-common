{-# OPTIONS --guardedness #-}

-- PeerStateActions.hs at the fixed network pin: per-peer status/control state.
-- Initiator result cells are distinct from the IG responder job/result tables.
module ConnectionManagement.Rules.PeerActions where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Nat using (ℕ; _<?_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Rules.Pruning using (sortBy)

data Status : Set where
  peerCold peerCooling peerWarm peerHot : Status
data Control : Set where
  continue quiesce terminate : Control
data Cell : Set where
  notStarted running : Cell
  returned notRunning : RunResult → Cell
record ProtocolRun : Set where
  constructor protocolRun
  field descriptor : Protocol
        -- The source stores an STM result action only after the start traversal.
        actual : Cell
        published : Cell
open ProtocolRun public

record Peer : Set where
  constructor peerState
  field key : ConnectionKey
        handleRef : HandleId
        muxRef : MuxId
        status : Status
        hotControl warmControl establishedControl : Control
        runs : List ProtocolRun
        monitorStarted : Bool
        promotedAt : Maybe ℕ
open Peer public
Runtime = Store PeerConnectionId Peer

sameTemperature : Temperature → Temperature → Bool
sameTemperature hot hot = true
sameTemperature warm warm = true
sameTemperature established established = true
sameTemperature _ _ = false
belongs : Temperature → ProtocolRun → Bool
belongs t r = sameTemperature t (temperature (descriptor r))

-- Polling the public STM action observes current results only for published runs.
observe : ProtocolRun → Cell
observe r with published r
... | running = actual r
... | cell = cell

firstOrdered : Temperature → List ProtocolRun → Maybe RunResult
firstOrdered t [] = nothing
firstOrdered t (r ∷ rs) with belongs t r | observe r
... | true | returned result = just result
... | true | notRunning result = nothing
... | true | notStarted = nothing
... | _ | _ = firstOrdered t rs

first : Temperature → List ProtocolRun → Maybe RunResult
first t rs = firstOrdered t (sortBy (λ a b → does (number (descriptor a) <? number (descriptor b))) rs)

-- Last-to-finish waits for every started run; errors dominate successful values.
combine : RunResult → RunResult → RunResult
combine (errored e) _ = errored e
combine clean result = result
all : Temperature → List ProtocolRun → Maybe RunResult
all t [] = just clean
all t (r ∷ rs) with belongs t r
... | false = all t rs
... | true with observe r | all t rs
...   | returned result | just rest = just (combine result rest)
...   | notRunning result | just rest = just (combine result rest)
...   | notStarted | rest = rest
...   | _ | _ = nothing

-- No outbound demotion is inferred from socket closure or handler completion.
demoted : ConnectionKey → S.State → Bool
demoted k s with S.mapCell (S.cm s)
... | S.taken _ = false
... | S.full m with S.lookupConnection k m
...   | nothing = true
...   | just e with lookup e (S.entries (S.cm s))
...     | nothing = false
...     | just (S.inboundIdle _ _ _ _) = true
...     | just (S.inboundActive _ _ _ _) = true
...     | just (S.unnegotiated inbound _ _) = true
...     | just (S.terminated _) = true
...     | just _ = false

-- Updating status never resurrects cooling/cold peers.
cool : Peer → Peer
cool p with status p
... | peerCold = p
... | _ = record p { status = peerCooling }

initialPeer : ConnectionKey → HandleId → M.Handle → Peer
initialPeer k h hd = peerState k h (M.muxRef hd) peerCold terminate continue continue
  (map (λ protocol → protocolRun protocol notStarted notStarted) (M.bundle hd)) false nothing

-- Traversal starts one protocol at a time; publication is a later transaction.
startRun : Temperature → ℕ → List ProtocolRun → Maybe (List ProtocolRun)
startRun t n [] = nothing
startRun t n (r ∷ rs) with number (descriptor r) ≟ n | belongs t r
... | yes _ | true with actual r
...   | running = nothing
...   | _ = just (record r { actual = running; published = observe r } ∷ rs)
startRun t n (r ∷ rs) | _ | _ with startRun t n rs
... | nothing = nothing
... | just rest = just (r ∷ rest)
finishRun : ℕ → RunResult → List ProtocolRun → Maybe (List ProtocolRun)
finishRun n result [] = nothing
finishRun n result (r ∷ rs) with number (descriptor r) ≟ n | actual r
... | yes _ | running = just (record r { actual = returned result } ∷ rs)
... | yes _ | _ = nothing
... | no _ | _ with finishRun n result rs
...   | nothing = nothing
...   | just rest = just (r ∷ rest)
started : Temperature → List ProtocolRun → Bool
started t [] = true
started t (r ∷ rs) with belongs t r | actual r
... | true | notStarted = false
... | true | notRunning _ = false
... | _ | _ = started t rs
publishRuns : Temperature → List ProtocolRun → List ProtocolRun
publishRuns t = map (λ r → update r)
  where
  update : ProtocolRun → ProtocolRun
  update r with belongs t r
  ... | true = record r { published = running }
  ... | false = r
retireHot : List ProtocolRun → List ProtocolRun
retireHot = map update
  where
  update : ProtocolRun → ProtocolRun
  update r with belongs hot r | observe r
  ... | true | returned result = record r { actual = notRunning result; published = notRunning result }
  ... | _ | _ = r

-- These operations are source STM commits; IO traversals/timeout ownership are
-- sequenced by the job and monitor continuations in the combined subsystem.
data Action : Set where
  activate deactivate close : Action
  startProtocol : Temperature → ℕ → Action
  publishProtocols : Temperature → Action
  protocolResult : ℕ → RunResult → Action
  markWarm forkMonitor finishDeactivate timeoutDeactivate timeoutClose : Action
  markPromoted : ℕ → Action
  monitorCooling monitorError : Action

step : Action → Peer → IG.Runtime → S.State → Maybe (Peer × IG.Runtime)
step activate p ig s with status p
... | peerWarm = just (record p { status = peerHot; hotControl = continue; warmControl = quiesce } , ig)
... | _ = nothing -- caller maps this case to ColdActivationException
step deactivate p ig s with status p
... | peerHot = just (record p { hotControl = terminate; warmControl = continue } , ig)
... | peerWarm = just (p , ig)
... | _ = nothing -- caller maps this case to ColdDeactivationException
step close p ig s = just (record (cool p)
  { hotControl = terminate; warmControl = terminate; establishedControl = terminate } , ig)
step (startProtocol t n) p ig s with lookup (muxRef p) (IG.muxes (IG.execution ig))
... | nothing = nothing
... | just m with M.status m
...   | M.ready with startRun t n (runs p)
...     | nothing = nothing
...     | just rs = just (record p { runs = rs } , ig)
step (startProtocol t n) p ig s | just m | _ = nothing
step (publishProtocols t) p ig s with started t (runs p)
... | false = nothing
... | true = just (record p { runs = publishRuns t (runs p) } , ig)
step (protocolResult n result) p ig s with finishRun n result (runs p)
... | nothing = nothing
... | just rs = just (record p { runs = rs } , ig)
step markWarm p ig s = just (record p { status = peerWarm } , ig)
step forkMonitor p ig s with monitorStarted p
... | true = nothing
... | false = just (record p { monitorStarted = true } , ig)
step (markPromoted time) p ig s = just (record p { promotedAt = just time } , ig)
step finishDeactivate p ig s with all hot (runs p)
... | nothing = nothing
... | just (errored _) = just (cool p , ig)
... | just clean with status p
...   | peerHot = just (record p { status = peerWarm; runs = retireHot (runs p) } , ig)
...   | _ = just (record p { runs = retireHot (runs p) } , ig)
step timeoutDeactivate p ig s with lookup (muxRef p) (IG.muxes (IG.execution ig))
... | nothing = nothing
... | just m = just (cool p , IG.setMux (muxRef p) (record m { commands = M.commands m ++ (M.shutdown ∷ []) }) ig)
step timeoutClose p ig s = step timeoutDeactivate p ig s
step monitorCooling p ig s with status p | demoted (key p) s
... | peerCooling | true = just (record p { status = peerCold; monitorStarted = false; promotedAt = nothing } , ig)
... | peerCold | _ = just (record p { monitorStarted = false; promotedAt = nothing } , ig)
... | _ | _ = nothing
step monitorError p ig s = just (cool p , ig)

-- An initiator error is consumed by the shared mux monitor separately from
-- publication of its result to peer-state waiters.
firstFailure : List ProtocolRun → Maybe ErrorId
firstFailure [] = nothing
firstFailure (r ∷ rs) with actual r
... | returned (errored err) = just err
... | _ = firstFailure rs
