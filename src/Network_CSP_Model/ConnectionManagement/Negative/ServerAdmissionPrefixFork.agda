{-# OPTIONS --guardedness #-}

-- Initialized finite prefix exits, with real births and successful-step proofs.
-- Duplicate-key input is abstract; unresolved mfix references are not evaluated.
module ConnectionManagement.Negative.ServerAdmissionPrefixFork where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Fixtures
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
private
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module U = N.U

open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using
  (physicalThreads; append; admit; consume; mux; handler)

import ConnectionManagement.Negative.ServerAdmissionPrefixHardLimit as Limits
private
  module HardLimit = Limits.HardLimit

-- No physical handler is born when the first fresh-entry fork fails.
module ForkFailure where
  module F = HardLimit.F
  failedFork1 : S.step (admit A.w₀ Admission.failFork) (F.p4) ≡ just (F.f1)
  failedFork1 = refl
  failedFork2 : S.step (admit A.w₀ Admission.restore) (F.f1) ≡ just (F.f2)
  failedFork2 = refl
  failedFork3 : S.step (S.workerPrefixException A.w₀ F.err) (F.f2) ≡ just (F.f3)
  failedFork3 = refl
  failedFork4 : S.step (S.workerClose A.w₀ nothing) (F.f3) ≡ just (F.f4)
  failedFork4 = refl
  failedFork5 : S.step (S.workerResult A.w₀) (F.f4) ≡ just (F.f5)
  failedFork5 = refl
  failedForkActions : List S.Action
  failedForkActions = (admit A.w₀ Admission.failFork) ∷ (admit A.w₀ Admission.restore) ∷ (S.workerPrefixException A.w₀ F.err) ∷ (S.workerClose A.w₀ nothing) ∷ (S.workerResult A.w₀) ∷ []
  abstract
    failedForkPath : S.Executes (F.p4) failedForkActions (F.f5)
    failedForkPath = S.next failedFork1 (S.next failedFork2 (S.next failedFork3 (S.next failedFork4 (S.next failedFork5 (S.done)))))

  actions : List S.Action
  actions = HardLimit.birthActions ++ failedForkActions
  abstract
    initialized : S.Executes F.start actions F.f5
    initialized = append HardLimit.birthPath failedForkPath
  restored-empty-map : Shared.mapCell (Shared.cm (S.shared F.f5)) ≡ Shared.full []
  restored-empty-map = refl
  committed-entry-retained : Shared.entries (Shared.cm (S.shared F.f5)) ≡
    (ident 0 , Shared.unnegotiated inbound A.key₀ A.child₀) ∷ []
  committed-entry-retained = refl
  entry-supply-retained : Shared.nextEntry (Shared.cm (S.shared F.f5)) ≡ 1
  entry-supply-retained = refl
  promise-supply-retained : Shared.nextPromise (S.shared F.f5) ≡ 1
  promise-supply-retained = refl
  allocated-promise-retained : Shared.promises (S.shared F.f5) ≡ ident 0 ∷ []
  allocated-promise-retained = refl
  no-handler-created : Shared.handlers (S.shared F.f5) ≡ []
  no-handler-created = refl
  no-physical-handler-created : physicalThreads F.f5 ≡ []
  no-physical-handler-created = refl
  no-fabricated-handler-result : W.resultReady A.child₀ (R.base (N.raw (S.base F.f5))) ≡ false
  no-fabricated-handler-result = refl
  empty-promise : Shared.handshakeResults (S.shared F.f5) ≡ []
  empty-promise = refl
  raised-after-one-close : lookup A.w₀ (S.workers F.f5) ≡
    just (S.rawWorker F.r₀ (S.resultAvailable (S.raised (S.sync F.err))) 1)
  raised-after-one-close = refl
  socket-closed : lookup (ident 0) (Shared.sockets (S.shared F.f5)) ≡ just Shared.closed
  socket-closed = refl
  no-exception-before-restore : S.step (S.workerPrefixException A.w₀ F.err) F.f1 ≡ nothing
  no-exception-before-restore = refl
  no-normal-prefix-return : S.step (S.workerPrefixReturned A.w₀) F.f2 ≡ nothing
  no-normal-prefix-return = refl
  no-close-before-restore : S.step (S.workerClose A.w₀ nothing) F.f1 ≡ nothing
  no-close-before-restore = refl
  no-result-before-close : S.step (S.workerResult A.w₀) F.f3 ≡ nothing
  no-result-before-close = refl
  no-lower-close-bypass : S.step (admit A.w₀ Admission.close) F.f3 ≡ nothing
  no-lower-close-bypass = refl
  replaced replacedResult : S.State
  replaced = F.physicalClose A.w₀ F.r₀ (Shared.closeUncertain F.replacement)
    (S.bodyExited (S.raised (S.sync F.replacement))) 1 F.f3
  replacedResult = S.setPC A.w₀ (S.rawWorker F.r₀ (S.bodyExited (S.raised (S.sync F.replacement))) 1)
    (S.resultAvailable (S.raised (S.sync F.replacement))) replaced
  cleanupFailure1 : S.step (S.workerClose A.w₀ (just (S.sync F.replacement))) (F.f3) ≡ just (replaced)
  cleanupFailure1 = refl
  cleanupFailure2 : S.step (S.workerResult A.w₀) (replaced) ≡ just (replacedResult)
  cleanupFailure2 = refl
  cleanupFailureActions : List S.Action
  cleanupFailureActions = (S.workerClose A.w₀ (just (S.sync F.replacement))) ∷ (S.workerResult A.w₀) ∷ []
  abstract
    cleanupFailurePath : S.Executes (F.f3) cleanupFailureActions (replacedResult)
    cleanupFailurePath = S.next cleanupFailure1 (S.next cleanupFailure2 (S.done))

  abstract
    initialized-cleanup-failure : S.Executes F.start
      (HardLimit.birthActions ++ (admit A.w₀ Admission.failFork ∷ admit A.w₀ Admission.restore ∷
        S.workerPrefixException A.w₀ F.err ∷ cleanupFailureActions)) replacedResult
    initialized-cleanup-failure = append HardLimit.birthPath
      (S.next failedFork1 (S.next failedFork2 (S.next failedFork3 cleanupFailurePath)))
  replacement-result : S.resultOf A.w₀ replacedResult ≡ just (S.raised (S.sync F.replacement))
  replacement-result = refl
  no-cleanup-retry : S.step (S.workerClose A.w₀ nothing) replaced ≡ nothing
  no-cleanup-retry = refl
  failed-close-retains-logical-pc : lookup A.w₀ (Shared.admissions (S.shared replaced)) ≡
    just (Shared.admissionWorker F.r₀ (Shared.closeSocket Shared.forkFailed))
  failed-close-retains-logical-pc = refl
