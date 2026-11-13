{-# OPTIONS --guardedness #-}

-- The adapter's enabled witness is conditional on a real generic typed job
-- edge. It neither adopts protocol 1 as LeiosNotify nor injects a configured run.
module ConnectionManagement.Negative.ProtocolContractJobs3 where
open import Data.Bool using (true)
open import ConnectionManagement.Domain using (JobId)
import ConnectionManagement.Negative.ProtocolContracts3 as Examples
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ident; errorId)
import ConnectionManagement.ProtocolContracts3 as C
open import ConnectionManagement.ProtocolContracts using (normal; synchronous; cancelled)
open import ConnectionManagement.ProtocolContractJobs3
import ConnectionManagement.MuxProtocolJobs as W

normal-selection : completion (C.finished normal) (ident 10) ≡ just (W.protocolReturned (ident 10))
normal-selection = refl
error-selection : completion (C.finished (synchronous (errorId 7))) (ident 10) ≡ just (W.protocolException (ident 10) (errorId 7))
error-selection = refl
cancelled-is-not-clean-or-sync-error : completion (C.finished cancelled) (ident 10) ≡ nothing
cancelled-is-not-clean-or-sync-error = refl
blocked-is-not-complete : completion (C.blocked C.command) (ident 10) ≡ nothing
blocked-is-not-complete = refl
cleanup-is-not-complete : completion (C.refunding normal) (ident 10) ≡ nothing
cleanup-is-not-complete = refl
join-is-not-complete : completion (C.innerRelease normal) (ident 10) ≡ nothing
join-is-not-complete = refl


-- Positive adapter example, explicitly retaining the real child/egress premises.
-- The complete peer registry/cleanup path to closed is independently enabled.
notify-client-enabled : ∀ j core next → matches C.notifyClient j core ≡ true →
  W.step (W.protocolReturned j) core ≡ just next →
  complete C.notifyClient j (attached core Examples.notifyClosed) ≡ just (attached next Examples.notifyClosed)
notify-client-enabled j core next matched edge =
  complete-enabled C.notifyClient j (attached core Examples.notifyClosed) next (W.protocolReturned j) matched refl edge

fetch-clean-enabled : ∀ j core next → matches C.fetchClient j core ≡ true →
  W.step (W.protocolReturned j) core ≡ just next →
  complete C.fetchClient j (attached core Examples.fetchClosed) ≡ just (attached next Examples.fetchClosed)
fetch-clean-enabled j core next matched edge =
  complete-enabled C.fetchClient j (attached core Examples.fetchClosed) next (W.protocolReturned j) matched refl edge

notify-number : number C.notifyClient ≡ 18
notify-number = refl
fetch-number : number C.fetchServer ≡ 19
fetch-number = refl

outer-cs-is-not-complete : completion (C.outerRelease normal) (ident 10) ≡ nothing
outer-cs-is-not-complete = refl
