{-# OPTIONS --guardedness #-}

-- Governor.hs and Governor/{EstablishedPeers,ActivePeers,Monitor}.hs, fixed pin.
-- Ordinary known-peer profile: discovery/root/ledger hooks are not enabled.
module ConnectionManagement.Rules.OutboundGovernor where

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_; _≤?_; _<?_; _⊓_)
open import Data.List using (List; []; _∷_; _++_; map; length; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Rules.PeerActions as P
open import ConnectionManagement.Rules.Pruning using (sortBy)
open import ConnectionManagement.ConnectionOrder using (lexLess; addressCode)

member : PeerAddr → List PeerAddr → Bool
member p [] = false
member p (q ∷ qs) with p ≟ q
... | yes _ = true
... | no _ = member p qs
without : List PeerAddr → List PeerAddr → List PeerAddr
without xs ys = filterᵇ (λ p → not (member p ys)) xs
union : List PeerAddr → List PeerAddr → List PeerAddr
union xs ys = xs ++ without ys xs
intersection : List PeerAddr → List PeerAddr → List PeerAddr
intersection xs ys = filterᵇ (λ p → member p ys) xs
remove : PeerAddr → List PeerAddr → List PeerAddr
remove p xs = without xs (p ∷ [])
keys : ∀ {A : Set} → Store PeerAddr A → List PeerAddr
keys = map proj₁

record Targets : Set where
  constructor targets
  field knownTarget establishedTarget activeTarget : ℕ
open Targets public
sane : Targets → Bool
sane t = does (activeTarget t ≤? establishedTarget t) ∧ does (establishedTarget t ≤? knownTarget t)
record Known : Set where
  constructor known
  field failures connectAt : ℕ
        clearFailuresAt : Maybe ℕ
        tepid successful : Bool
open Known public
record Established : Set where
  constructor established
  field connectionRef : PeerConnectionId
        activateAt : ℕ
open Established public
record State : Set where
  constructor governorState
  field target : Targets
        knownPeers : Store PeerAddr Known
        establishedPeers : Store PeerAddr Established
        activePeers promotingCold promotingWarm demotingWarm demotingHot coolingPeers : List PeerAddr
open State public

-- Four independent source in-progress sets; a cooling peer stays established.
data Kind : Set where
  forget establish activate close deactivate : Kind
record Job : Set where
  constructor job
  field kind : Kind
        peer : PeerAddr
        captured : Maybe PeerConnectionId
open Job public

record Decision : Set where
  constructor decision
  field nextState : State
        launches : List Job
open Decision public

-- Derive eligibility and quotas from current private state, not caller wishes.
quota : Kind → State → ℕ
quota forget s = length (knownPeers s) ∸ knownTarget (target s)
quota establish s = establishedTarget (target s) ∸ (length (establishedPeers s) + length (promotingCold s))
quota close s = ((length (establishedPeers s) ∸ establishedTarget (target s)) ⊓
  (length (establishedPeers s) ∸ length (activePeers s))) ∸
  (length (demotingWarm s) + length (promotingWarm s) +
   length (intersection (without (keys (establishedPeers s)) (activePeers s)) (coolingPeers s)))
quota activate s = activeTarget (target s) ∸ (length (activePeers s) + length (promotingWarm s))
quota deactivate s = length (activePeers s) ∸
  (activeTarget (target s) + length (demotingHot s) + length (intersection (activePeers s) (coolingPeers s)))
eligible : ℕ → Kind → State → List PeerAddr
eligible time forget s = without (keys (knownPeers s)) (keys (establishedPeers s) ++ promotingCold s)
eligible time establish s = without
  (keys (filterᵇ (λ kv → does (connectAt (proj₂ kv) ≤? time)) (knownPeers s)))
  (keys (establishedPeers s) ++ promotingCold s)
eligible time close s = without (keys (establishedPeers s))
  (activePeers s ++ demotingWarm s ++ promotingWarm s ++ coolingPeers s)
eligible time activate s = without
  (keys (filterᵇ (λ kv → does (activateAt (proj₂ kv) ≤? time)) (establishedPeers s)))
  (activePeers s ++ promotingWarm s ++ demotingWarm s ++ coolingPeers s)
eligible time deactivate s = without (activePeers s) (demotingHot s ++ coolingPeers s)
ready : ℕ → Kind → State → Bool
ready time kind s with quota kind s | eligible time kind s
... | zero | _ = false
... | _ | [] = false
... | suc _ | _ ∷ _ = true

-- Preserve the ordinary-peer alternative order after monitor/job/target guards.
firstReady : ℕ → State → Maybe Kind
firstReady time s with ready time forget s
... | true = just forget
... | false with ready time establish s
...   | true = just establish
...   | false with ready time close s
...     | true = just close
...     | false with ready time activate s
...       | true = just activate
...       | false with ready time deactivate s
...         | true = just deactivate
...         | false = nothing

validPick : List PeerAddr → List PeerAddr → Bool
validPick [] available = true
validPick (p ∷ ps) available = member p available ∧ not (member p ps) ∧ validPick ps available
capture : Kind → State → PeerAddr → Job
capture establish s p = job establish p nothing
capture kind s p with lookup p (establishedPeers s)
... | nothing = job kind p nothing
... | just e = job kind p (just (connectionRef e))
mark : Kind → List PeerAddr → State → State
mark forget ps s = record s { knownPeers = filterᵇ (λ kv → not (member (proj₁ kv) ps)) (knownPeers s) }
mark establish ps s = record s { promotingCold = union (promotingCold s) ps }
mark activate ps s = record s { promotingWarm = union (promotingWarm s) ps }
mark close ps s = record s { demotingWarm = union (demotingWarm s) ps }
mark deactivate ps s = record s { demotingHot = union (demotingHot s) ps }
choose : ℕ → List PeerAddr → State → Maybe Decision
choose time [] s = nothing
choose time picked@(_ ∷ _) s with firstReady time s
... | nothing = nothing
... | just kind with validPick picked (eligible time kind s) ∧ does (length picked ≤? quota kind s)
...   | false = nothing
...   | true = just (decision (mark kind picked s) (jobsFor kind))
  where
  jobsFor : Kind → List Job
  jobsFor forget = []
  jobsFor kind = map (capture kind s) (sortBy (λ p q → lexLess (addressCode p) (addressCode q)) picked)

-- Completion data is defunctionalized, then interpreted against CURRENT state.
data Outcome : Set where
  establishedOK : PeerConnectionId → Outcome
  succeeded failed demotionTimedOut : Outcome
record Completion : Set where
  constructor completion
  field work : Job
        outcome : Outcome
        -- Policy delay/jitter input; never a replacement governor-state snapshot.
        retryDelay : ℕ
open Completion public

-- ActivePeers.jobDemoteActivePeer asserts membership when applying a successful
-- completion, not when the job finishes. Retain this source failure boundary.
completionAssertion : Completion → State → Bool
completionAssertion c s with kind (work c) | outcome c
... | deactivate | succeeded = member (peer (work c)) (keys (establishedPeers s))
... | _ | _ = true

reportFailure : ℕ → ℕ → ℕ → PeerAddr → Store PeerAddr Known → Store PeerAddr Known
reportFailure maxRetries now delay p ks with lookup p ks
... | nothing = ks
... | just k with suc (failures k) ≤? maxRetries
...   | no _ = delete p ks
...   | yes _ = put p (record k { failures = suc (failures k); connectAt = now + delay; clearFailuresAt = nothing }) ks
setTepid : PeerAddr → Store PeerAddr Known → Store PeerAddr Known
setTepid p ks with lookup p ks
... | nothing = ks
... | just k = put p (record k { tepid = true }) ks
-- Cold establishment uses the source exponential backoff based on the CURRENT
-- failure count. The input 0..4 represents integral jitter -2..2 in this profile.
coldRetry : PeerAddr → ℕ → State → ℕ
coldRetry p jitter s with lookup p (knownPeers s)
... | nothing = 0
... | just k = (5 * (2 ^ (failures k ⊓ 5)) + jitter) ∸ 2

complete : ℕ → ℕ → ℕ → Completion → State → State
complete maxRetries clearDelay now c s with kind (work c) | outcome c
... | forget | _ = s
... | establish | establishedOK ref = record s
  { establishedPeers = put (peer (work c)) (established ref now) (establishedPeers s)
  ; promotingCold = remove (peer (work c)) (promotingCold s)
  ; knownPeers = put (peer (work c)) (successfulKnown (lookup (peer (work c)) (knownPeers s))) (knownPeers s) }
  where
  successfulKnown : Maybe Known → Known
  successfulKnown nothing = known 0 now nothing false true
  successfulKnown (just k) = record k { successful = true; tepid = false }
complete maxRetries clearDelay now c s | establish | _ = record s
  { promotingCold = remove (peer (work c)) (promotingCold s)
  ; knownPeers = reportFailure maxRetries now (coldRetry (peer (work c)) (retryDelay c) s) (peer (work c)) (knownPeers s) }
complete maxRetries clearDelay now c s | activate | succeeded with lookup (peer (work c)) (establishedPeers s)
... | nothing = s -- source aborted completion leaves private state unchanged
... | just _ = record s
  { activePeers = union (activePeers s) (peer (work c) ∷ [])
  ; promotingWarm = remove (peer (work c)) (promotingWarm s)
  ; knownPeers = clearAt (peer (work c)) (knownPeers s) }
  where
  clearAt : PeerAddr → Store PeerAddr Known → Store PeerAddr Known
  clearAt p ks with lookup p ks
  ... | nothing = ks
  ... | just k = put p (record k { clearFailuresAt = just (now + clearDelay) }) ks
complete maxRetries clearDelay now c s | activate | _ with member (peer (work c)) (promotingWarm s)
... | false = s
... | true = record s
  { establishedPeers = delete (peer (work c)) (establishedPeers s)
  ; promotingWarm = remove (peer (work c)) (promotingWarm s)
  ; knownPeers = reportFailure maxRetries now (retryDelay c) (peer (work c)) (knownPeers s) }
complete maxRetries clearDelay now c s | close | demotionTimedOut = record s
  { demotingWarm = remove (peer (work c)) (demotingWarm s) }
complete maxRetries clearDelay now c s | close | _ = record s
  { establishedPeers = delete (peer (work c)) (establishedPeers s)
  ; demotingWarm = remove (peer (work c)) (demotingWarm s) }
complete maxRetries clearDelay now c s | deactivate | demotionTimedOut = record s
  { demotingHot = remove (peer (work c)) (demotingHot s) }
complete maxRetries clearDelay now c s | deactivate | succeeded = record s
  { activePeers = remove (peer (work c)) (activePeers s)
  ; knownPeers = setTepid (peer (work c)) (knownPeers s)
  ; demotingHot = remove (peer (work c)) (demotingHot s) }
complete maxRetries clearDelay now c s | deactivate | _ = record s
  { activePeers = remove (peer (work c)) (activePeers s)
  ; establishedPeers = delete (peer (work c)) (establishedPeers s)
  ; knownPeers = setTepid (peer (work c)) (knownPeers s)
  ; demotingHot = remove (peer (work c)) (demotingHot s) }

-- Monitor.connections ignores synchronous demotions owned by governor jobs.
asyncDemotion : PeerAddr → P.Status → State → Bool
asyncDemotion p P.peerHot s = false
asyncDemotion p P.peerWarm s = member p (activePeers s) ∧ not (member p (demotingHot s))
asyncDemotion p P.peerCooling s = not (member p (coolingPeers s)) ∧
  ((member p (activePeers s) ∧ not (member p (demotingHot s))) ∨
   (not (member p (activePeers s)) ∧ member p (keys (establishedPeers s)) ∧ not (member p (demotingWarm s))))
asyncDemotion p P.peerCold s = (member p (activePeers s) ∨ member p (keys (establishedPeers s))) ∧
  not (member p (demotingWarm s)) ∧ not (member p (demotingHot s))
monitored : P.Runtime → State → List (PeerAddr × P.Status)
monitored rt s = collect (establishedPeers s)
  where
  collect : Store PeerAddr Established → List (PeerAddr × P.Status)
  collect [] = []
  collect ((p , e) ∷ es) with lookup (connectionRef e) rt
  ... | nothing = collect es
  ... | just observedPeer with asyncDemotion p (P.status observedPeer) s
  ...   | false = collect es
  ...   | true = (p , P.status observedPeer) ∷ collect es
applyMonitor : ℕ → ℕ → ℕ → List (PeerAddr × P.Status) → State → State
applyMonitor maxRetries now delay [] s = s
applyMonitor maxRetries now delay ((p , status) ∷ rest) s = applyMonitor maxRetries now delay rest (update status)
  where
  baseState = record s { activePeers = remove p (activePeers s) }
  update : P.Status → State
  update P.peerHot = s
  update P.peerWarm with lookup p (establishedPeers s)
  ... | nothing = baseState
  ... | just e = record baseState { establishedPeers = put p (record e { activateAt = now + delay }) (establishedPeers s) }
  update P.peerCooling = record baseState
    { coolingPeers = union (coolingPeers s) (p ∷ []); promotingWarm = remove p (promotingWarm s) }
  update P.peerCold = record baseState
    { establishedPeers = delete p (establishedPeers s); coolingPeers = remove p (coolingPeers s)
    ; promotingWarm = remove p (promotingWarm s)
    ; knownPeers = reportFailure maxRetries now delay p (knownPeers s) }

-- Earliest delayed guard retained by GuardedSkip; an expired deadline is ready
-- rather than a new future wakeup. Only deficits contribute deadlines.
minimum : Maybe ℕ → Maybe ℕ → Maybe ℕ
minimum nothing b = b
minimum a nothing = a
minimum (just a) (just b) = just (a ⊓ b)
futureMinimum : ℕ → List ℕ → Maybe ℕ
futureMinimum now [] = nothing
futureMinimum now (t ∷ ts) with now <? t
... | yes _ = minimum (just t) (futureMinimum now ts)
... | no _ = futureMinimum now ts
nextWakeup : ℕ → State → Maybe ℕ
nextWakeup now s = minimum coldWake warmWake
  where
  coldWake : Maybe ℕ
  coldWake with quota establish s
  ... | zero = nothing
  ... | suc _ = futureMinimum now (map (λ kv → connectAt (proj₂ kv)) (knownPeers s))
  warmWake : Maybe ℕ
  warmWake with quota activate s
  ... | zero = nothing
  ... | suc _ = futureMinimum now (map (λ kv → activateAt (proj₂ kv)) (establishedPeers s))

-- Time advancement also clears scheduled failure counters, as KnownPeers does.
advanceTime : ℕ → State → State
advanceTime time s = record s { knownPeers = map update (knownPeers s) }
  where
  update : PeerAddr × Known → PeerAddr × Known
  update (p , k) with clearFailuresAt k
  ... | nothing = p , k
  ... | just deadline with deadline ≤? time
  ...   | no _ = p , k
  ...   | yes _ = p , record k { failures = 0; clearFailuresAt = nothing }

-- Each peer carries its own exit-policy/fuzz delay; mixed batches need not use
-- one common delay. Missing observations are rejected by the dispatcher.
applyMonitorDelays : ℕ → ℕ → Store PeerAddr ℕ → List (PeerAddr × P.Status) → State → State
applyMonitorDelays maxRetries now delays [] s = s
applyMonitorDelays maxRetries now delays ((p , status) ∷ rest) s with lookup p delays
... | nothing = s
... | just delay = applyMonitorDelays maxRetries now delays rest
  (applyMonitor maxRetries now delay ((p , status) ∷ []) s)
