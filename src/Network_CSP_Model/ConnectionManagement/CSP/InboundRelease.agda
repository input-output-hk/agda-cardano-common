{-# OPTIONS --guardedness #-}

-- Finite source-boundary witnesses; cancellation delivery remains an input.
module ConnectionManagement.CSP.InboundRelease where

open import Data.Bool using (false; true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.IGRegistration using (registered; registeredState; lifecycle; lifecycle-path)
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.Scenarios.Admission using (key₀; child₀; w₀)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.CSP.OwnershipInvariant
import ConnectionManagement.CSP.SupplyInvariant
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Snapshot helper only: each transition below is independently checked by next.
-- Failed actions return the old snapshot here but CANNOT prove a next step.
after : Action → Configuration → Configuration
after a c with advance a c
... | nothing = c
... | just c′ = c′

b₀ b₁ b₂ b₃ b₄ b₅ b₆ : Configuration
b₀ = after (igStep IG.finishBatch) registered
b₁ = after (igStep (IG.captureTime 11)) b₀
b₂ = after (igStep IG.registerInactivity) b₁
b₃ = after (igStep (IG.expireTimer (ident 1))) b₂
b₄ = after (igStep IG.selectBatch) b₃
b₅ = after (igStep IG.readEvent) b₄
b₆ = after (releaseStep R.enter) b₅

batchActions : List Action
batchActions = igStep IG.finishBatch ∷ igStep (IG.captureTime 11) ∷
  igStep IG.registerInactivity ∷ igStep (IG.expireTimer (ident 1)) ∷
  igStep IG.selectBatch ∷ igStep IG.readEvent ∷ releaseStep R.enter ∷ []
batch-path : Executes registered batchActions b₆
batch-path = next {c₁ = b₀} refl (next {c₁ = b₁} refl (next {c₁ = b₂} refl
  (next {c₁ = b₃} refl (next {c₁ = b₄} refl (next {c₁ = b₅} refl (next refl done))))))

written counted requested delivered checked returned published : Configuration
written = after (releaseStep R.transact) b₆
counted = after (releaseStep R.readCounters) written
requested = after (releaseStep R.requestCancellation) counted
delivered = after (releaseStep (R.cancellationDelivered child₀)) requested
checked = after (releaseStep R.checkAssertion) delivered
returned = after (releaseStep R.returnToIG) checked
published = after (igStep IG.commitDecision) returned

releaseActions : List Action
releaseActions = releaseStep R.transact ∷ releaseStep R.readCounters ∷
  releaseStep R.requestCancellation ∷ releaseStep (R.cancellationDelivered child₀) ∷
  releaseStep R.checkAssertion ∷ releaseStep R.returnToIG ∷ igStep IG.commitDecision ∷ []
release-path : Executes b₆ releaseActions published
release-path = next {c₁ = written} refl (next {c₁ = counted} refl
  (next {c₁ = requested} refl (next {c₁ = delivered} refl
  (next {c₁ = checked} refl (next {c₁ = returned} refl (next refl done))))))

-- Full accepted-socket-to-release trace, conditional on the existing publication,
-- handle-allocation, timer-readiness and cancellation-delivery inputs.
release-trace : traces (Process start) (map label (lifecycle ++ (batchActions ++ releaseActions)))
release-trace = trace-intro (exec-append lifecycle-path (exec-append batch-path release-path))
release-hidden-trace : traces (HiddenProcess b₆) (map label (project releaseActions))
release-hidden-trace = hidden-trace release-path

written-before-cancellation : lookup (ident 0) (entries (cm (world written))) ≡
  just (terminating key₀ child₀ nothing)
written-before-cancellation = refl
registration-retained : IG.publishedState (inboundGovernor requested) ≡ registeredState
registration-retained = refl
return-does-not-publish : IG.publishedState (inboundGovernor returned) ≡ registeredState
return-does-not-publish = refl
publication-removes-registration : IG.connections (IG.publishedState (inboundGovernor published)) ≡ []
publication-removes-registration = refl
no-cleanup-wait : cleanups (world published) ≡ []
no-cleanup-wait = refl
premature-return-refused : advance (releaseStep R.returnToIG) requested ≡ nothing
premature-return-refused = refl
no-premature-return-trace : ¬ traces (Process requested) (map label (releaseStep R.returnToIG ∷ []))
no-premature-return-trace = refused-extension done premature-return-refused
wrong-target-refused : advance (releaseStep (R.cancellationDelivered w₀)) requested ≡ nothing
wrong-target-refused = refl
next-batch-refused : advance (igStep IG.finishBatch) requested ≡ nothing
next-batch-refused = refl

-- Local interleaving/branch fixtures, not further reachability claims.
lock : Configuration → Configuration
lock c = record c { world = record (world c) { cm = record (cm (world c)) { mapCell = taken w₀ } } }
locked-transaction : advance (releaseStep R.transact) (lock b₆) ≡ nothing
locked-transaction = refl
locked-counter-read : advance (releaseStep R.readCounters) (lock written) ≡ nothing
locked-counter-read = refl

replaceEntry : ConnectionState → Configuration → Configuration
replaceEntry st c = record c { world = record (world c) { cm = record (cm (world c))
  { entries = put (ident 0) st (entries (cm (world c))) } } }

keepStart keepWritten : Configuration
keepStart = replaceEntry (outboundDup key₀ child₀ (ident 0) ticking) b₆
keepWritten = after (releaseStep R.transact) keepStart
keep-write : lookup (ident 0) (entries (cm (world keepWritten))) ≡
  just (outboundDup key₀ child₀ (ident 0) expired)
keep-write = refl

inlineFailed : Configuration
inlineFailed = after (releaseStep R.transact)
  (replaceEntry (outboundDup key₀ child₀ (ident 0) expired) b₆)
inline-does-not-read-counters : advance (releaseStep R.readCounters) inlineFailed ≡ nothing
inline-does-not-read-counters = refl

activeStart activeWritten activeCounted activeRequested activeDelivered activeFailed : Configuration
activeStart = replaceEntry (inboundActive key₀ child₀ (ident 0) duplex) b₆
activeWritten = after (releaseStep R.transact) activeStart
activeCounted = after (releaseStep R.readCounters) activeWritten
activeRequested = after (releaseStep R.requestCancellation) activeCounted
activeDelivered = after (releaseStep (R.cancellationDelivered child₀)) activeRequested
activeFailed = after (releaseStep R.checkAssertion) activeDelivered
active-failure-path : Executes activeStart
  (releaseStep R.transact ∷ releaseStep R.readCounters ∷ releaseStep R.requestCancellation ∷
   releaseStep (R.cancellationDelivered child₀) ∷ releaseStep R.checkAssertion ∷ []) activeFailed
active-failure-path = next {c₁ = activeWritten} refl (next {c₁ = activeCounted} refl
  (next {c₁ = activeRequested} refl (next {c₁ = activeDelivered} refl (next refl done))))
deferred-failure-keeps-write : lookup (ident 0) (entries (cm (world activeFailed))) ≡
  just (terminating key₀ child₀ nothing)
deferred-failure-keeps-write = refl
assertion-prevents-return : advance (releaseStep R.returnToIG) activeFailed ≡ nothing
assertion-prevents-return = refl

-- The callback's captured worker survives replacement of the live map entry.
replacement : Configuration
replacement = replaceEntry (inboundIdle key₀ w₀ (ident 1) duplex) requested
captured-target-still-delivers : advance (releaseStep (R.cancellationDelivered child₀)) replacement ≡
  just (after (releaseStep (R.cancellationDelivered child₀)) replacement)
captured-target-still-delivers = refl
replacement-target-refused : advance (releaseStep (R.cancellationDelivered w₀)) replacement ≡ nothing
replacement-target-refused = refl

releasePC : Configuration → Data.Maybe.Maybe R.PC
releasePC c with inboundRelease c
... | nothing = nothing
... | just f = just (R.pc f)
inline-assertion-observed : releasePC inlineFailed ≡ just R.assertionRaised
inline-assertion-observed = refl
deferred-assertion-observed : releasePC activeFailed ≡ just R.assertionRaised
deferred-assertion-observed = refl

keepCounted keepRequested keepChecked keepReturned keepPublished : Configuration
keepCounted = after (releaseStep R.readCounters) keepWritten
keepRequested = after (releaseStep R.requestCancellation) keepCounted
keepChecked = after (releaseStep R.checkAssertion) keepRequested
keepReturned = after (releaseStep R.returnToIG) keepChecked
keepPublished = after (igStep IG.commitDecision) keepReturned
keep-path : Executes keepStart
  (releaseStep R.transact ∷ releaseStep R.readCounters ∷ releaseStep R.requestCancellation ∷
   releaseStep R.checkAssertion ∷ releaseStep R.returnToIG ∷ igStep IG.commitDecision ∷ []) keepPublished
keep-path = next {c₁ = keepWritten} refl (next {c₁ = keepCounted} refl
  (next {c₁ = keepRequested} refl (next {c₁ = keepChecked} refl
  (next {c₁ = keepReturned} refl (next refl done)))))
keep-retains-cold-registration : IG.publishedState (inboundGovernor keepPublished) ≡
  IG.setRemote key₀ IG.remoteCold registeredState
keep-retains-cold-registration = refl

unsupportedStart unsupportedWritten unsupportedCounted unsupportedRequested unsupportedChecked unsupportedReturned : Configuration
unsupportedStart = replaceEntry reservedOutbound b₆
unsupportedWritten = after (releaseStep R.transact) unsupportedStart
unsupportedCounted = after (releaseStep R.readCounters) unsupportedWritten
unsupportedRequested = after (releaseStep R.requestCancellation) unsupportedCounted
unsupportedChecked = after (releaseStep R.checkAssertion) unsupportedRequested
unsupportedReturned = after (releaseStep R.returnToIG) unsupportedChecked
unsupported-path : Executes unsupportedStart
  (releaseStep R.transact ∷ releaseStep R.readCounters ∷ releaseStep R.requestCancellation ∷
   releaseStep R.checkAssertion ∷ releaseStep R.returnToIG ∷ []) unsupportedReturned
unsupported-path = next {c₁ = unsupportedWritten} refl (next {c₁ = unsupportedCounted} refl
  (next {c₁ = unsupportedRequested} refl (next {c₁ = unsupportedChecked} refl (next refl done))))
unsupported-skips-publication : IG.continuation (inboundGovernor unsupportedReturned) ≡ IG.readNext 11 []
unsupported-skips-publication = refl

-- Missing bindings select CommitTr; malformed dangling entries stay unavailable.
missingStart missingWritten : Configuration
missingStart = record b₆ { world = record (world b₆) { cm = record (cm (world b₆)) { mapCell = full [] } } }
missingWritten = after (releaseStep R.transact) missingStart
missing-lookup-path : Executes missingStart (releaseStep R.transact ∷ []) missingWritten
missing-lookup-path = next refl done
missing-still-reads-counters : releasePC missingWritten ≡ just R.counters
missing-still-reads-counters = refl
