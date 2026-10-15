{-# OPTIONS --guardedness #-}

-- Source-policy regression witnesses. Over-limit fixtures are local, not claims
-- of reachability from the accepted-socket start (outbound acquisition is absent).
module ConnectionManagement.CSP.Pruning where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ; +_; -[1+_])
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (put; lookup)
open import ConnectionManagement.ConnectionOrder using (keyLess)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.InboundRelease using (after; lock; replaceEntry)
open import ConnectionManagement.CSP.RemoteState using (entered; p₀; p₁)
open import ConnectionManagement.CSP.IGRegistration using (registeredState)
open import ConnectionManagement.CSP.IGRuntime using (expiredEngine)
open import ConnectionManagement.Scenarios.Admission using (key₀; key₁; child₀; child₁)
open import ConnectionManagement.Scenarios.Handshake using (info)
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.RemoteState as R
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

key₂ key₃ : ConnectionKey
key₂ = connection (local key₀) (addr ipv4 3 3001)
key₃ = connection (local key₀) (addr ipv4 4 3001)
worker₂ worker₃ : WorkerId
worker₂ = ident 4
worker₃ = ident 5

-- Insertion order differs from source Map order. Two downstream candidates and
-- one existing duplex compete with the prospective duplex. Need two victims.
multi : Configuration
multi = record (replaceEntry (outboundDup key₀ child₀ (ident 0) expired) entered)
  { promotionHardLimit = 2
  ; world = record (world entered) { cm = record (cm (world entered))
    { mapCell = full (insertConnection key₃ (ident 3)
                     (insertConnection key₂ (ident 2)
                     (insertConnection key₁ (ident 1)
                     (insertConnection key₀ (ident 0) []))))
    ; entries = (ident 3 , duplexActive key₃ worker₃ (ident 3)) ∷
                (ident 2 , inboundActive key₂ worker₂ (ident 2) duplex) ∷
                (ident 1 , inboundIdle key₁ child₁ (ident 1) duplex) ∷
                (ident 0 , outboundDup key₀ child₀ (ident 0) expired) ∷ []
    ; nextEntry = 4 } } }
-- Scores follow key₀,key₁,key₂,key₃. Negative upstream scores cannot displace
-- downstream candidates. Policy-score order is key₂,key₁, unlike delivery order.
draws : List ℤ
draws = -[1+ 99 ] ∷ + 50 ∷ -[1+ 4 ] ∷ -[1+ 199 ] ∷ []

committed checked requested₁ delivered₁ requested₂ delivered₂ cancellationsDone counted returned published : Configuration
committed = after (remoteStep (R.transactPruning 0 draws)) multi
checked = after (remoteStep R.checkAssertion) committed
requested₁ = after (remoteStep R.requestPruneCancellation) checked
delivered₁ = after (remoteStep (R.pruneCancellationDelivered child₁)) requested₁
requested₂ = after (remoteStep R.requestPruneCancellation) delivered₁
delivered₂ = after (remoteStep (R.pruneCancellationDelivered worker₂)) requested₂
cancellationsDone = after (remoteStep R.requestPruneCancellation) delivered₂
counted = after (remoteStep R.readCounters) cancellationsDone
returned = after (remoteStep R.returnToIG) counted
published = after (igStep IG.commitDecision) returned

actions : List Action
actions = remoteStep (R.transactPruning 0 draws) ∷ remoteStep R.checkAssertion ∷
  remoteStep R.requestPruneCancellation ∷ remoteStep (R.pruneCancellationDelivered child₁) ∷
  remoteStep R.requestPruneCancellation ∷ remoteStep (R.pruneCancellationDelivered worker₂) ∷
  remoteStep R.requestPruneCancellation ∷ remoteStep R.readCounters ∷
  remoteStep R.returnToIG ∷ igStep IG.commitDecision ∷ []
prune-path : Executes multi actions published
prune-path = next {c₁ = committed} refl (next {c₁ = checked} refl
  (next {c₁ = requested₁} refl (next {c₁ = delivered₁} refl
  (next {c₁ = requested₂} refl (next {c₁ = delivered₂} refl
  (next {c₁ = cancellationsDone} refl (next {c₁ = counted} refl
  (next {c₁ = returned} refl (next refl done)))))))))
prune-trace : traces (Process multi) (map label actions)
prune-trace = trace-intro prune-path
prune-hidden-trace : traces (HiddenProcess multi) (map label (project actions))
prune-hidden-trace = hidden-trace prune-path

-- Both terminations and the surviving promotion are visible at the same endpoint.
first-victim-written : lookup (ident 1) (entries (cm (world committed))) ≡ just (terminated nothing)
first-victim-written = refl
second-victim-written : lookup (ident 2) (entries (cm (world committed))) ≡ just (terminated nothing)
second-victim-written = refl
self-promoted : lookup (ident 0) (entries (cm (world committed))) ≡ just (duplexActive key₀ child₀ (ident 0))
self-promoted = refl
other-upstream-retained : lookup (ident 3) (entries (cm (world committed))) ≡ just (duplexActive key₃ worker₃ (ident 3))
other-upstream-retained = refl
one-committed-draw : pruningGeneration committed ≡ 1
one-committed-draw = refl
no-more-draws : pruningGeneration published ≡ 1
no-more-draws = refl
wrong-delivery-order : advance (remoteStep (R.pruneCancellationDelivered worker₂)) requested₁ ≡ nothing
wrong-delivery-order = refl
no-wrong-delivery-trace : ¬ traces (Process requested₁)
  (map label (remoteStep (R.pruneCancellationDelivered worker₂) ∷ []))
no-wrong-delivery-trace = refused-extension done wrong-delivery-order
no-counters-before-deliveries : advance (remoteStep R.readCounters) checked ≡ nothing
no-counters-before-deliveries = refl
no-early-return : advance (remoteStep R.returnToIG) requested₂ ≡ nothing
no-early-return = refl
later-counter-can-block : advance (remoteStep R.readCounters) (lock cancellationsDone) ≡ nothing
later-counter-can-block = refl
no-ig-publication-yet : IG.publishedState (inboundGovernor returned) ≡ registeredState
no-ig-publication-yet = refl
published-warm : IG.publishedState (inboundGovernor published) ≡ IG.setRemote key₀ IG.remoteWarm registeredState
published-warm = refl
no-cleanup-join : cleanups (world published) ≡ []
no-cleanup-join = refl

-- Bad/stale entropy inputs cannot publish a transaction prefix or consume a draw.
wrong-generation : advance (remoteStep (R.transactPruning 1 draws)) multi ≡ nothing
wrong-generation = refl
missing-score : advance (remoteStep (R.transactPruning 0 [])) multi ≡ nothing
missing-score = refl
map-lock-blocks-pruning : advance (remoteStep (R.transactPruning 0 draws)) (lock multi) ≡ nothing
map-lock-blocks-pruning = refl
no-unscored-over-limit-success : advance (remoteStep R.transact) multi ≡ nothing
no-unscored-over-limit-success = refl

replacement : Configuration
replacement = record requested₁ { world = record (world requested₁)
  { cm = record (cm (world requested₁)) { entries = put (ident 1)
    (inboundIdle key₁ (ident 9) (ident 9) duplex) (entries (cm (world requested₁))) } } }
replacement-does-not-retarget : advance (remoteStep (R.pruneCancellationDelivered (ident 9))) replacement ≡ nothing
replacement-does-not-retarget = refl
old-target-delivers : advance (remoteStep (R.pruneCancellationDelivered child₁)) replacement ≡
  just (after (remoteStep (R.pruneCancellationDelivered child₁)) replacement)
old-target-delivers = refl

-- Self-pruning still returns success to AwakeRemote, after delivery and counters.
s₀ s₁ s₂ s₃ s₄ s₅ s₆ : Configuration
s₀ = after (remoteStep R.checkAssertion) p₁
s₁ = after (remoteStep R.requestPruneCancellation) s₀
s₂ = after (remoteStep (R.pruneCancellationDelivered child₀)) s₁
s₃ = after (remoteStep R.requestPruneCancellation) s₂
s₄ = after (remoteStep R.readCounters) s₃
s₅ = after (remoteStep R.returnToIG) s₄
s₆ = after (igStep IG.commitDecision) s₅
self-path : Executes p₁
  (remoteStep R.checkAssertion ∷ remoteStep R.requestPruneCancellation ∷
   remoteStep (R.pruneCancellationDelivered child₀) ∷ remoteStep R.requestPruneCancellation ∷
   remoteStep R.readCounters ∷ remoteStep R.returnToIG ∷ igStep IG.commitDecision ∷ []) s₆
self-path = next {c₁ = s₀} refl (next {c₁ = s₁} refl (next {c₁ = s₂} refl
  (next {c₁ = s₃} refl (next {c₁ = s₄} refl (next {c₁ = s₅} refl (next refl done))))))
self-not-overwritten : lookup (ident 0) (entries (cm (world s₆))) ≡ just (terminated nothing)
self-not-overwritten = refl
self-still-publishes-warm : IG.publishedState (inboundGovernor s₆) ≡ IG.setRemote key₀ IG.remoteWarm registeredState
self-still-publishes-warm = refl

-- Regression for the old local-first comparison: remote order wins even when
-- local order is opposite. The same order drives IG expiry and prune Map.assocs.
remoteFirst localFirst : ConnectionKey
remoteFirst = connection (addr ipv4 9 3001) (addr ipv4 1 3001)
localFirst = connection (addr ipv4 0 3001) (addr ipv4 2 3001)
remote-before-local : keyLess remoteFirst localFirst ≡ true
remote-before-local = refl
ig-expiry-uses-source-order : IG.firstCommit expiredEngine
  ((localFirst , IG.registered info (ident 1)) ∷ (remoteFirst , IG.registered info (ident 1)) ∷ []) ≡ just remoteFirst
ig-expiry-uses-source-order = refl

-- Equal scores: type order, then stable Map order. Random scores outrank type.
c₀ c₁ : P.Candidate
c₀ = P.candidate remoteFirst (ident 0) child₀ 4 false
c₁ = P.candidate localFirst (ident 1) child₁ 1 false
victimKeys : Maybe P.Plan → List ConnectionKey
victimKeys nothing = []
victimKeys (just selectedPlan) = map P.connectionKey (P.victims selectedPlan)
type-tiebreak : victimKeys (P.makePlan 1 c₀ (inboundActive remoteFirst child₀ (ident 0) duplex)
  (c₁ ∷ []) (+ 0 ∷ + 0 ∷ [])) ≡ localFirst ∷ []
type-tiebreak = refl
score-before-type : victimKeys (P.makePlan 1 c₀ (inboundActive remoteFirst child₀ (ident 0) duplex)
  (c₁ ∷ []) (-[1+ 0 ] ∷ + 0 ∷ [])) ≡ remoteFirst ∷ []
score-before-type = refl
stable-key-tiebreak : victimKeys (P.makePlan 1 c₀ (inboundActive remoteFirst child₀ (ident 0) duplex)
  ((record c₁ { typeRank = 4 }) ∷ []) (+ 0 ∷ + 0 ∷ [])) ≡ remoteFirst ∷ []
stable-key-tiebreak = refl

-- Unknown-local entries are omitted by State.toMap, not assigned random scores.
unknown-local-omitted : P.candidates
  ((remote key₀ , (unknownLocal , ident 8) ∷ []) ∷ []) [] ≡ just []
unknown-local-omitted = refl

-- The other source promotion branch uses the prospective inbound-active type,
-- so it competes with downstream peers rather than receiving duplex priority.
idleInput idlePruned idleRetained : Configuration
idleInput = replaceEntry (outboundIdle key₀ child₀ (ident 0) duplex) multi
idlePruned = after (remoteStep (R.transactPruning 0 draws)) idleInput
idleRetained = after (remoteStep (R.transactPruning 0 (+ 100 ∷ + 0 ∷ + 1 ∷ -[1+ 99 ] ∷ []))) idleInput
idle-pruning-path : Executes idleInput (remoteStep (R.transactPruning 0 draws) ∷ []) idlePruned
idle-pruning-path = next refl done
idle-self-is-downstream : lookup (ident 0) (entries (cm (world idlePruned))) ≡ just (terminated nothing)
idle-self-is-downstream = refl
idle-other-survives : lookup (ident 1) (entries (cm (world idlePruned))) ≡ just (inboundIdle key₁ child₁ (ident 1) duplex)
idle-other-survives = refl
idle-surviving-path : Executes idleInput
  (remoteStep (R.transactPruning 0 (+ 100 ∷ + 0 ∷ + 1 ∷ -[1+ 99 ] ∷ [])) ∷ []) idleRetained
idle-surviving-path = next refl done
idle-survivor-promotes : lookup (ident 0) (entries (cm (world idleRetained))) ≡ just (inboundActive key₀ child₀ (ident 0) duplex)
idle-survivor-promotes = refl

-- The generation is a draw occurrence token, not a concrete seed or entropy test.
nextGeneration nextCommitted : Configuration
nextGeneration = record multi { pruningGeneration = 1 }
nextCommitted = after (remoteStep (R.transactPruning 1 draws)) nextGeneration
old-ticket-refused : advance (remoteStep (R.transactPruning 0 draws)) nextGeneration ≡ nothing
old-ticket-refused = refl
next-generation-path : Executes nextGeneration (remoteStep (R.transactPruning 1 draws) ∷ []) nextCommitted
next-generation-path = next refl done
next-generation-advances : pruningGeneration nextCommitted ≡ 2
next-generation-advances = refl
