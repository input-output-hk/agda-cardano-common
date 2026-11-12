{-# OPTIONS --guardedness #-}

-- G1 local IG receipt-permission controls. Masked reads require an actually
-- taken map, sends observe blocking throwTo, and demotion is restored/unmasked.
-- These generic snapshots are not additional initialized execution witnesses.
module ConnectionManagement.Negative.PrimitiveIGSites where

open import Data.Bool using (true; false)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ident)
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.State as Shared
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as L
import ConnectionManagement.Rules.RemoteState as R
module E = Exit (λ _ → false)
module S = Server (λ _ → false)

-- Alter only map occupancy to distinguish a retrying read from a ready read.
withMap : Shared.MapCell → E.State → E.State
withMap cell s = record s { base = S.setSource
  (record (E.source s) { core = record (O.core (E.source s))
    { world = record (M.world (O.core (E.source s)))
      { cm = record (Shared.cm (M.world (O.core (E.source s)))) { mapCell = cell } } } }) (E.base s) }
held free : E.State → E.State
held = withMap (Shared.taken (ident 0))
free = withMap (Shared.full [])

loop-enabled : E.bodyReady E.loopBoundary IG.sampleTime ≡ true
loop-enabled = refl
loop-wrong-pc-refused : E.bodyReady E.loopBoundary IG.inCM ≡ false
loop-wrong-pc-refused = refl
batch-enabled : ∀ t token → E.bodyReady E.batchWait (IG.awaitBatch t token) ≡ true
batch-enabled t token = refl
batch-wrong-pc-refused : E.bodyReady E.batchWait IG.sampleTime ≡ false
batch-wrong-pc-refused = refl
release-read-enabled : ∀ f s → E.releaseReady E.releaseRead (record f { pc = L.transaction }) (held s) ≡ true
release-read-enabled f s = refl
release-read-ready-refused : ∀ f s → E.releaseReady E.releaseRead (record f { pc = L.transaction }) (free s) ≡ false
release-read-ready-refused f s = refl
release-counters-enabled : ∀ f s → E.releaseReady E.releaseCounters (record f { pc = L.counters }) (held s) ≡ true
release-counters-enabled f s = refl
release-counters-ready-refused : ∀ f s → E.releaseReady E.releaseCounters (record f { pc = L.counters }) (free s) ≡ false
release-counters-ready-refused f s = refl
release-send-enabled : ∀ f s w → E.releaseReady E.releaseSend (record f { pc = L.delivering w }) s ≡ true
release-send-enabled f s w = refl
release-send-before-request-refused : ∀ f s → E.releaseReady E.releaseSend (record f { pc = L.cancellation }) s ≡ false
release-send-before-request-refused f s = refl
promote-read-enabled : ∀ f s → E.remoteReady E.promoteRead (record f { operation = R.promote; pc = R.transaction }) (held s) ≡ true
promote-read-enabled f s = refl
promote-read-ready-refused : ∀ f s → E.remoteReady E.promoteRead (record f { operation = R.promote; pc = R.transaction }) (free s) ≡ false
promote-read-ready-refused f s = refl
promote-counters-enabled : ∀ f s → E.remoteReady E.promoteCounters (record f { operation = R.promote; pc = R.counters }) (held s) ≡ true
promote-counters-enabled f s = refl
promote-counters-ready-refused : ∀ f s → E.remoteReady E.promoteCounters (record f { operation = R.promote; pc = R.counters }) (free s) ≡ false
promote-counters-ready-refused f s = refl
promote-send-enabled : ∀ f s v rest → E.remoteReady E.promoteSend
  (record f { operation = R.promote; pc = R.awaitDelivery v rest }) s ≡ true
promote-send-enabled f s v rest = refl
promote-send-before-request-refused : ∀ f s → E.remoteReady E.promoteSend
  (record f { operation = R.promote; pc = R.counters }) s ≡ false
promote-send-before-request-refused f s = refl
demote-transaction : E.unmaskedDemote R.transaction ≡ true
demote-transaction = refl
demote-assertion : E.unmaskedDemote R.assertion ≡ true
demote-assertion = refl
demote-counters : E.unmaskedDemote R.counters ≡ true
demote-counters = refl
demote-return : E.unmaskedDemote R.returning ≡ true
demote-return = refl
promote-is-not-unmasked-demote : ∀ f s → E.remoteReady E.demoteBoundary
  (record f { operation = R.promote; pc = R.assertion }) s ≡ false
promote-is-not-unmasked-demote f s = refl
