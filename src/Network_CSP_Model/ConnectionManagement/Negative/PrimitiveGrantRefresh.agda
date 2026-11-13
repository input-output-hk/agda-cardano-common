{-# OPTIONS --guardedness #-}

-- G1 F3: repeated refresh winners in the existing abstract rank/token profile.
-- Expiry is the observed timer-winning alternative of awaitOr (ready did not
-- commit); no timestamp or fairness theorem is inferred. These are local
-- coupled kernel/bucket controls, using the same dispatcher as the mux worker.
module ConnectionManagement.Negative.PrimitiveGrantRefresh where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Negative.MuxEgressScheduling as F
import ConnectionManagement.Negative.MuxConfiguredTraffic as T

expired rearmed expiredAgain granted cancelled : M.Egress.State
expired = T.estep (F.adv E.refreshExpired) F.armed
rearmed = T.estep (F.adv E.rearmRefresh) expired
expiredAgain = T.estep (F.adv E.refreshExpired) rearmed
granted = T.estep (F.adv E.grantQueued) rearmed
cancelled = T.estep (M.Egress.writeFailed 0) expired
bExpired bRearmed bAgain bGrant : IG.Buckets
bExpired = F.after F.mid (F.adv E.refreshExpired) F.armed F.b2
bRearmed = F.after F.mid (F.adv E.rearmRefresh) expired bExpired
bAgain = F.after F.mid (F.adv E.refreshExpired) rearmed bRearmed
bGrant = F.after F.mid (F.adv E.grantQueued) rearmed bRearmed

expiry-consumes-timer-keeps-request : IG.armed bExpired ≡ [] × IG.waiting bExpired ≡ IG.waiting F.b1
expiry-consumes-timer-keeps-request = refl , refl
expiry-enabled : F.both F.mid (F.adv E.refreshExpired) F.armed F.b2 ≡ just bExpired
expiry-enabled = refl
rearm-enabled : F.both F.mid (F.adv E.rearmRefresh) expired bExpired ≡ just F.b2
rearm-enabled = refl
repeat-refresh : F.both F.mid (F.adv E.refreshExpired) rearmed bRearmed ≡ just bExpired
repeat-refresh = refl
no-premature-refresh : F.both F.mid (F.adv E.refreshExpired) F.queued F.b1 ≡ nothing
no-premature-refresh = refl
no-duplicate-expiry : F.both F.mid (F.adv E.refreshExpired) expired bExpired ≡ nothing
no-duplicate-expiry = refl
no-double-rearm : F.both F.mid (F.adv E.rearmRefresh) rearmed bRearmed ≡ nothing
no-double-rearm = refl
no-grant-before-rearm : F.both F.mid (F.adv E.grantQueued) expired bExpired ≡ nothing
no-grant-before-rearm = refl
refresh-does-not-charge : IG.charges bAgain ≡ []
refresh-does-not-charge = refl
grant-after-refresh : IG.waiting bGrant ≡ [] × IG.charges bGrant ≡ (IG.rankedGrant , F.mid , 0 , 13) ∷ []
grant-after-refresh = refl , refl
no-expiry-after-grant : F.both F.mid (F.adv E.refreshExpired) granted bGrant ≡ nothing
no-expiry-after-grant = refl
cancel-spent-timer : F.both F.mid (M.Egress.writeFailed 0) expired bExpired ≡ just IG.emptyBuckets
cancel-spent-timer = refl
cancel-rearmed : F.both F.mid (M.Egress.writeFailed 0) rearmed bRearmed ≡ just IG.emptyBuckets
cancel-rearmed = refl
no-rearm-after-cancel : F.both F.mid (F.adv E.rearmRefresh) cancelled IG.emptyBuckets ≡ nothing
no-rearm-after-cancel = refl
cancel-after-grant-keeps-charge : F.after F.mid (M.Egress.writeFailed 0) granted bGrant ≡
  record IG.emptyBuckets { charges = (IG.rankedGrant , F.mid , 0 , 13) ∷ [] }
cancel-after-grant-keeps-charge = refl

-- Shared-resource guards still apply when a malformed local continuation
-- names a missing timer/request; neither half can commit a successor.
missing-active-timer-refused : F.both F.mid (F.adv E.refreshExpired) F.armed F.b1 ≡ nothing
missing-active-timer-refused = refl
missing-request-rearm-refused : F.both F.mid (F.adv E.rearmRefresh) expired IG.emptyBuckets ≡ nothing
missing-request-rearm-refused = refl
refresh-keeps-held : M.Egress.runHeld rearmed ≡ M.Egress.runHeld F.armed
refresh-keeps-held = refl
refresh-keeps-request : IG.waiting bAgain ≡ IG.waiting F.b1
refresh-keeps-request = refl


-- A refresh belongs to grant-waiting modes, with an actual queued request.
credit-has-no-refresh : E.nextWait E.credit (just E.armed) E.refreshExpired ≡ nothing
credit-has-no-refresh = refl
slice-refresh-enabled : E.nextWait E.reserved (just E.armed) E.refreshExpired ≡ just E.refreshDue
slice-refresh-enabled = refl
slice-rearm-enabled : E.nextWait E.reserved (just E.refreshDue) E.rearmRefresh ≡ just E.armed
slice-rearm-enabled = refl
missing-request-expiry-refused : F.both F.mid (F.adv E.refreshExpired) F.armed
  (record F.b2 { waiting = [] }) ≡ nothing
missing-request-expiry-refused = refl
