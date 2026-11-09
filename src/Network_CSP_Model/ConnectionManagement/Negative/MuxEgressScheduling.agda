{-# OPTIONS --guardedness #-}

-- M4 controls for the node-wide egress buckets (Bucket.hs awaitGrantWith,
-- waitQueued, cancel at network 2f1c154). A ranked batch on the configured
-- Scheduled lane queues, arms its refresh timer, is granted and charged once,
-- and disarms; cancellation leaves the queue and cancels the timer without a
-- refund; a fast grant needs its bucket's queue empty. Grant order and token
-- arithmetic are abstract, so these are bookkeeping, not fairness, results.
module ConnectionManagement.Negative.MuxEgressScheduling where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Negative.MuxConfiguredTraffic as T

mid other : MuxId
mid = ident 0
other = ident 1
-- The configured profile's initiator key rides the Scheduled (ranked) lane.
ready : Mux.Egress.State
ready = T.estep (Mux.Egress.selectDemand 0) (T.estep (Mux.Egress.takeFirst E.scheduledLane)
  (T.estep (Mux.Egress.appendPayload 7 5) (T.estep (Mux.Egress.createWanton 7 (1 , Mux.initiatorJob)) T.configuredEgress)))
adv : E.Advance → Mux.Egress.Action
adv = Mux.Egress.advance 0
gated : Mux.Egress.State
gated = T.estep (adv E.openGate) ready
-- One step of a mux's egress together with its bucket effect, as stepWorker.
both : MuxId → Mux.Egress.Action → Mux.Egress.State → IG.Buckets → Maybe IG.Buckets
both m a e bs with Mux.Egress.step a e
... | just _ = IG.bucketStep m a e bs
... | nothing = nothing
after : MuxId → Mux.Egress.Action → Mux.Egress.State → IG.Buckets → IG.Buckets
after m a e bs with both m a e bs
... | just t = t
... | nothing = bs

queued armed granted disarmed : Mux.Egress.State
queued = T.estep (adv E.queueRequest) gated
armed = T.estep (adv E.armTimer) queued
granted = T.estep (adv E.grantQueued) armed
disarmed = T.estep (adv E.disarmTimer) granted
b1 b2 b3 b4 : IG.Buckets
b1 = after mid (adv E.queueRequest) gated IG.emptyBuckets
b2 = after mid (adv E.armTimer) queued b1
b3 = after mid (adv E.grantQueued) armed b2
b4 = after mid (adv E.disarmTimer) granted b3

-- Queue, arm, grant, disarm: the request and its timer are gone, one charge.
request-queued : IG.waiting b1 ≡ ((mid , 0) , IG.budgetBucket) ∷ []
request-queued = refl
timer-armed : IG.armed b2 ≡ ((mid , 0) , true) ∷ []
timer-armed = refl
grant-dequeues-and-charges : IG.waiting b3 ≡ [] × IG.charges b3 ≡ (IG.rankedGrant , mid , 0 , 13) ∷ []
grant-dequeues-and-charges = refl , refl
grant-leaves-timer-armed : IG.armed b3 ≡ ((mid , 0) , true) ∷ []
grant-leaves-timer-armed = refl
no-stale-request-or-timer : IG.waiting b4 ≡ [] × IG.armed b4 ≡ []
no-stale-request-or-timer = refl , refl
no-double-grant : both mid (adv E.grantQueued) granted b3 ≡ nothing
no-double-grant = refl

-- Fast path: only with nobody queued at that bucket, and charged once.
fast-grant : both mid (adv E.grantFast) gated IG.emptyBuckets ≡
  just (record IG.emptyBuckets { charges = (IG.rankedGrant , mid , 0 , 13) ∷ [] })
fast-grant = refl
-- Another mux's queued request on the shared budget blocks the fast path.
othersQueued : IG.Buckets
othersQueued = record IG.emptyBuckets { waiting = ((other , 4) , IG.budgetBucket) ∷ [] }
fast-grant-behind-queue-refused : both mid (adv E.grantFast) gated othersQueued ≡ nothing
fast-grant-behind-queue-refused = refl
-- A slice request is a different bucket's queue.
sliceQueued : IG.Buckets
sliceQueued = record IG.emptyBuckets { waiting = ((other , 4) , IG.sliceBucket) ∷ [] }
fast-grant-beside-slice-queue : both mid (adv E.grantFast) gated sliceQueued ≡
  just (record sliceQueued { charges = (IG.rankedGrant , mid , 0 , 13) ∷ [] })
fast-grant-beside-slice-queue = refl
-- A grant of a request not in the queue is refused.
unqueued-grant-refused : IG.bucketStep mid (adv E.grantQueued) armed IG.emptyBuckets ≡ nothing
unqueued-grant-refused = refl

-- Cancellation while queued and armed: leave the queue, cancel the timer, no charge.
cancel-armed : after mid (Mux.Egress.writeFailed 0) armed b2 ≡ IG.emptyBuckets
cancel-armed = refl
cancel-armed-keeps-held : Mux.Egress.runHeld (T.estep (Mux.Egress.writeFailed 0) armed) ≡ Mux.Egress.runHeld armed
cancel-armed-keeps-held = refl
-- Cancellation before the timer: the masked enqueue is undone by onException.
cancel-queued : after mid (Mux.Egress.writeFailed 0) queued b1 ≡ IG.emptyBuckets
cancel-queued = refl
-- Cancellation after the grant transaction: the timer goes, the charge stays.
cancel-after-grant : after mid (Mux.Egress.writeFailed 0) granted b3 ≡
  record IG.emptyBuckets { charges = (IG.rankedGrant , mid , 0 , 13) ∷ [] }
cancel-after-grant = refl
-- A cancelled request cannot be granted later.
cancelled = T.estep (Mux.Egress.writeFailed 0) armed
granted-after-cancel-refused : both mid (adv E.grantQueued) cancelled (after mid (Mux.Egress.writeFailed 0) armed b2) ≡ nothing
granted-after-cancel-refused = refl
