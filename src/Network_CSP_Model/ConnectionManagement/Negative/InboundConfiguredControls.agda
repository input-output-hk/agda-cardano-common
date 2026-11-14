{-# OPTIONS --guardedness #-}

-- Premature scheduler/body/finalizer operations at actual initialized states.
module ConnectionManagement.Negative.InboundConfiguredControls where

open import ConnectionManagement.Negative.FullConfiguredProfile
open import ConnectionManagement.Negative.InboundConfiguredSupport
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.ProtocolContracts2 as C2
import ConnectionManagement.ProtocolContracts3 as C3
import ConnectionManagement.Negative.InboundConfiguredAdmission12 as Admission
import ConnectionManagement.Negative.InboundConfiguredStart0 as Waiters
import ConnectionManagement.Negative.InboundConfiguredStart4 as Chain
import ConnectionManagement.Negative.InboundConfiguredStart5 as Any
import ConnectionManagement.Negative.InboundConfiguredStart17 as Started
import ConnectionManagement.Negative.InboundConfiguredNotifyContract0 as Notify
import ConnectionManagement.Negative.InboundConfiguredTxContract1 as Tx
import ConnectionManagement.Negative.InboundConfiguredCleanup2 as Pending
import ConnectionManagement.Negative.InboundConfiguredCleanup5 as Receipt

no-demand-before-registration : B.frontend (protocol (P.control A.child₀ (P.demand 2))) Admission.s2 ≡ nothing
no-demand-before-registration = refl
no-fork-before-demand : B.frontend (protocol (P.forkResponder A.child₀ (ident 10) (ident 10))) Waiters.s3 ≡ nothing
no-fork-before-demand = refl
no-command-between-group-starts : B.frontend (protocol (P.control A.child₀ P.selectCommand)) Chain.s2 ≡ nothing
no-command-between-group-starts = refl
no-second-demand-for-any : B.frontend (protocol (P.control A.child₀ (P.demand 8))) Any.s3 ≡ nothing
no-second-demand-for-any = refl
no-result-before-contract : B.frontend (protocol (P.protocolReturned (ident 15))) Started.s2 ≡ nothing
no-result-before-contract = refl
notify-cannot-finish-with-pending-send : B.observe3 (C3.doneSent C3.notifyServer) Notify.s3 ≡ nothing
notify-cannot-finish-with-pending-send = refl
no-tx-cleanup-before-retire : B.observe2 (C2.cleanup C2.txServerV2) Tx.s2 ≡ nothing
no-tx-cleanup-before-retire = refl
no-release-return-before-receipt : B.frontend (release Release.returnToIG) Pending.s3 ≡ nothing
no-release-return-before-receipt = refl
no-handler-result-before-cleanup : B.frontend (exit (W.publishAsyncResult A.child₀)) Pending.s3 ≡ nothing
no-handler-result-before-cleanup = refl
no-receipt-before-delay : B.frontend (exit (W.deliverInboundReleaseTimeWait (errorId 42))) Pending.s3 ≡ nothing
no-receipt-before-delay = refl
no-duplicate-receipt : B.frontend (exit (W.deliverInboundReleaseTimeWait (errorId 42))) Receipt.s2 ≡ nothing
no-duplicate-receipt = refl
no-result-before-timewait-finally : B.frontend (exit (W.publishAsyncResult A.child₀)) Receipt.s2 ≡ nothing
no-result-before-timewait-finally = refl
