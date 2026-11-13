{-# OPTIONS --guardedness #-}

-- The adapter's enabled witness is conditional on a real generic typed job
-- edge. It neither adopts protocol 1 as ChainSync nor injects a configured run.
module ConnectionManagement.Negative.ProtocolContractJobs where
open import Data.Bool using (true)
open import ConnectionManagement.Domain using (JobId)
import ConnectionManagement.Negative.ProtocolContracts as Examples
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (ident; errorId)
import ConnectionManagement.ProtocolContracts as C
open import ConnectionManagement.ProtocolContractJobs
import ConnectionManagement.MuxProtocolJobs as W

normal-selection : completion (C.finished C.normal) (ident 10) ≡ just (W.protocolReturned (ident 10))
normal-selection = refl
error-selection : completion (C.finished (C.synchronous (errorId 7))) (ident 10) ≡ just (W.protocolException (ident 10) (errorId 7))
error-selection = refl
cancelled-is-not-clean-or-sync-error : completion (C.finished C.cancelled) (ident 10) ≡ nothing
cancelled-is-not-clean-or-sync-error = refl
blocked-is-not-complete : completion (C.blocked C.ledger) (ident 10) ≡ nothing
blocked-is-not-complete = refl
cleanup-is-not-complete : completion (C.cleaning C.normal) (ident 10) ≡ nothing
cleanup-is-not-complete = refl
registered-is-not-complete : completion C.registered (ident 10) ≡ nothing
registered-is-not-complete = refl


-- Positive adapter example, explicitly retaining the real child/egress premises.
-- The complete peer registry/cleanup path to closed is independently enabled.
clean-client-enabled : ∀ j core next → matches C.chainClient j core ≡ true →
  W.step (W.protocolReturned j) core ≡ just next →
  complete C.chainClient j (attached core Examples.closed) ≡ just (attached next Examples.closed)
clean-client-enabled j core next matched edge =
  complete-enabled C.chainClient j (attached core Examples.closed) next (W.protocolReturned j) matched refl edge
