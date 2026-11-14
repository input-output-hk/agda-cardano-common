{-# OPTIONS --guardedness #-}

-- Enabled captured responder observations and direct physical-pool controls.
-- Mutated pool fixtures below test guards, not initialized reachability.
module ConnectionManagement.Negative.ConfiguredResponders where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
open import ConnectionManagement.Store using (put)
open import Data.Maybe using (Maybe)
open import Data.Product using (_×_; _,_)
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Negative.InboundConfiguredStart4 as Started
import ConnectionManagement.Negative.InboundConfiguredStart17 as FullStarted
import ConnectionManagement.Negative.InboundConfiguredChainContract1 as Clean
import ConnectionManagement.Negative.InboundConfiguredChainResult0 as Return
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts as C1
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as MR

capture-enabled : B.attach 2 (ident 10) Started.s1 ≡ just Started.s2
capture-enabled = refl
normal-return-enabled : B.frontend (protocol (P.protocolReturned (ident 10))) Clean.s2 ≡ just Return.s1
normal-return-enabled = refl
premature-return : B.frontend (protocol (P.protocolReturned (ident 10))) Started.s2 ≡ nothing
premature-return = refl
premature-publication : B.frontend (protocol (P.commitClean (ident 10))) Started.s2 ≡ nothing
premature-publication = refl
exception-bypass : B.frontend (protocol (P.protocolException (ident 10) (errorId 7))) Started.s2 ≡ nothing
exception-bypass = refl
no-rebinding : B.attach 2 (ident 10) Started.s2 ≡ nothing
no-rebinding = refl
wrong-number : B.attach 3 (ident 10) Started.s1 ≡ nothing
wrong-number = refl
missing-job : B.attach 2 (ident 99) Started.s1 ≡ nothing
missing-job = refl
client-cannot-use-server-binding : B.observe1 C1.registerSync Started.s2 ≡ nothing
client-cannot-use-server-binding = refl

raw-v1-kernel-enabled : C2.step (C2.start C2.txServerV1) (B.batch2 FullStarted.s2) ≡
  just (C2.set C2.txServerV1 C2.idle (B.batch2 FullStarted.s2))
raw-v1-kernel-enabled = refl
unselected-tx-v1-refused : B.observe2 (C2.start C2.txServerV1) FullStarted.s2 ≡ nothing
unselected-tx-v1-refused = refl

-- Change only the physical pool handle, retaining the captured typed job.
withHandle : Maybe Pool.ThreadPhase → B.State → B.State
withHandle value s with lookup A.child₀ (U.frames (P.base (B.physical s)))
... | nothing = s
... | just f = record s { runtime = record (B.runtime s)
  { base = V.setPhysical (P.setPool A.child₀ f pool (B.physical s)) (V.base (B.runtime s)) } }
  where
  pool : Pool.State
  pool = record (P.poolAt A.child₀ (B.physical s))
    { handles = table value }
    where
    table : Maybe Pool.ThreadPhase → List (JobId × Pool.ThreadPhase)
    table nothing = []
    table (just phase) = put (ident 10) phase (Pool.handles (P.poolAt A.child₀ (B.physical s)))

job : Types.ProtocolJob
job = Types.protocolJob A.child₀ (ident 0) MR.responderJob 2 (ident 10) Types.executing
running-pool-enabled : B.poolGate (ident 10) job (B.runtime Started.s2) Started.s2 ≡ true
running-pool-enabled = refl
unwound-pool-refused : B.poolGate (ident 10) job
  (B.runtime (withHandle (just Pool.bodyUnwinding) Clean.s2)) Clean.s2 ≡ false
unwound-pool-refused = refl
cancelled-pool-refused : B.poolGate (ident 10) job
  (B.runtime (withHandle (just (Pool.resultAvailable Pool.cancelledExit)) Clean.s2)) Clean.s2 ≡ false
cancelled-pool-refused = refl
missing-pool-refused : B.poolGate (ident 10) job
  (B.runtime (withHandle nothing Clean.s2)) Clean.s2 ≡ false
missing-pool-refused = refl
wrong-owner-refused : B.attach 2 (ident 10) (record Started.s1 { owner = ident 99 }) ≡ nothing
wrong-owner-refused = refl
wrong-mux-refused : B.attach 2 (ident 10) (record Started.s1 { mux = ident 99 }) ≡ nothing
wrong-mux-refused = refl
withJob : Types.ProtocolJob → B.State → B.State
withJob replacement s = record s { runtime = record (B.runtime s)
  { base = V.setPhysical (record (B.physical s)
      { jobs = put (ident 10) replacement (P.jobs (B.physical s)) }) (V.base (B.runtime s)) } }
initiator-capture-refused : B.attach 2 (ident 10)
  (withJob (record job { direction = MR.initiatorJob }) Started.s1) ≡ nothing
initiator-capture-refused = refl
stale-generation-refused : B.backed 2 (ident 10)
  (withJob (record job { generation = ident 99 }) Started.s2) ≡ false
stale-generation-refused = refl
