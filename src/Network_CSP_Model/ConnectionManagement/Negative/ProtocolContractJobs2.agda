{-# OPTIONS --guardedness #-}

-- The adapter's enabled witness is conditional on a real generic typed job
-- edge. It neither adopts protocol 1 as TxSubmission2 nor injects a configured run.
module ConnectionManagement.Negative.ProtocolContractJobs2 where
open import Data.Bool using (true)
open import ConnectionManagement.Domain using (JobId)
import ConnectionManagement.Negative.ProtocolContracts2 as Examples
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ident; errorId)
import ConnectionManagement.ProtocolContracts2 as C
open import ConnectionManagement.ProtocolContracts using (normal; synchronous; cancelled)
open import ConnectionManagement.ProtocolContractJobs2
import ConnectionManagement.MuxProtocolJobs as W

normal-selection : completion (C.finished normal) (ident 10) ≡ just (W.protocolReturned (ident 10))
normal-selection = refl
error-selection : completion (C.finished (synchronous (errorId 7))) (ident 10) ≡ just (W.protocolException (ident 10) (errorId 7))
error-selection = refl
cancelled-is-not-clean-or-sync-error : completion (C.finished cancelled) (ident 10) ≡ nothing
cancelled-is-not-clean-or-sync-error = refl
blocked-is-not-complete : completion (C.blocked C.sharedChange) (ident 10) ≡ nothing
blocked-is-not-complete = refl
cleanup-is-not-complete : completion (C.cleaning normal) (ident 10) ≡ nothing
cleanup-is-not-complete = refl
join-is-not-complete : completion (C.keepJoin normal) (ident 10) ≡ nothing
join-is-not-complete = refl


-- Positive adapter example, explicitly retaining the real child/egress premises.
-- The complete peer registry/cleanup path to closed is independently enabled.
clean-client-enabled : ∀ j core next → matches C.txClient j core ≡ true →
  W.step (W.protocolReturned j) core ≡ just next →
  complete C.txClient j (attached core Examples.txClosed) ≡ just (attached next Examples.txClosed)
clean-client-enabled j core next matched edge =
  complete-enabled C.txClient j (attached core Examples.txClosed) next (W.protocolReturned j) matched refl edge

keep-clean-enabled : ∀ j core next → matches C.keepClient j core ≡ true →
  W.step (W.protocolReturned j) core ≡ just next →
  complete C.keepClient j (attached core Examples.keepClosed) ≡ just (attached next Examples.keepClosed)
keep-clean-enabled j core next matched edge =
  complete-enabled C.keepClient j (attached core Examples.keepClosed) next (W.protocolReturned j) matched refl edge

tx-number : number C.txClient ≡ 4
tx-number = refl
keep-number : number C.keepServer ≡ 8
keep-number = refl
