{-# OPTIONS --guardedness #-}

-- Initialized finite prefix exits, with real births and successful-step proofs.
-- Duplicate-key input is abstract; unresolved mfix references are not evaluated.
module ConnectionManagement.Negative.ServerAdmissionPrefixHardLimit where

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

-- Both accepted sockets can race ahead of the first CM count. The fixed limit
-- is 1 for both requests, so the installed first handler rejects the second.
module HardLimit where
  module F = Fixtures 1 A.key₁
  actual-initializer : S.initial (O.initial (Machine.initial Shared.responderMode F.empty)) ≡ just F.start
  actual-initializer = refl
  birth1 : S.step (S.acceptedFork A.w₀ F.r₀) (F.start) ≡ just (F.one)
  birth1 = refl
  birth2 : S.step (S.acceptedFork A.w₁ F.r₁) (F.one) ≡ just (F.two)
  birth2 = refl
  birth3 : S.step (admit A.w₀ Admission.take) (F.two) ≡ just (F.p1)
  birth3 = refl
  birth4 : S.step (admit A.w₀ Admission.countLimit) (F.p1) ≡ just (F.p2)
  birth4 = refl
  birth5 : S.step (admit A.w₀ Admission.allocatePromise) (F.p2) ≡ just (F.p3)
  birth5 = refl
  birth6 : S.step (admit A.w₀ Admission.chooseEntry) (F.p3) ≡ just (F.p4)
  birth6 = refl
  birthActions : List S.Action
  birthActions = (S.acceptedFork A.w₀ F.r₀) ∷ (S.acceptedFork A.w₁ F.r₁) ∷ (admit A.w₀ Admission.take) ∷ (admit A.w₀ Admission.countLimit) ∷ (admit A.w₀ Admission.allocatePromise) ∷ (admit A.w₀ Admission.chooseEntry) ∷ []
  abstract
    birthPath : S.Executes (F.start) birthActions (F.p4)
    birthPath = S.next birth1 (S.next birth2 (S.next birth3 (S.next birth4 (S.next birth5 (S.next birth6 (S.done))))))
  installed1 : S.step (admit A.w₀ Admission.fork) (F.p4) ≡ just (F.p5)
  installed1 = refl
  installed2 : S.step (admit A.w₀ Admission.putMapBack) (F.p5) ≡ just (F.p6)
  installed2 = refl
  installed3 : S.step (admit A.w₀ Admission.readCounters) (F.p6) ≡ just (F.p7)
  installed3 = refl
  installedActions : List S.Action
  installedActions = (admit A.w₀ Admission.fork) ∷ (admit A.w₀ Admission.putMapBack) ∷ (admit A.w₀ Admission.readCounters) ∷ []
  abstract
    installedPath : S.Executes (F.p4) installedActions (F.p7)
    installedPath = S.next installed1 (S.next installed2 (S.next installed3 (S.done)))
  reject1 : S.step (admit A.w₁ Admission.take) (F.p7) ≡ just (F.h1)
  reject1 = refl
  reject2 : S.step (admit A.w₁ Admission.countLimit) (F.h1) ≡ just (F.h2)
  reject2 = refl
  reject3 : S.step (admit A.w₁ Admission.putMapBack) (F.h2) ≡ just (F.h3)
  reject3 = refl
  reject4 : S.step (S.workerPrefixReturned A.w₁) (F.h3) ≡ just (F.h4)
  reject4 = refl
  reject5 : S.step (S.workerClose A.w₁ nothing) (F.h4) ≡ just (F.h5)
  reject5 = refl
  reject6 : S.step (S.workerResult A.w₁) (F.h5) ≡ just (F.h6)
  reject6 = refl
  rejectActions : List S.Action
  rejectActions = (admit A.w₁ Admission.take) ∷ (admit A.w₁ Admission.countLimit) ∷ (admit A.w₁ Admission.putMapBack) ∷ (S.workerPrefixReturned A.w₁) ∷ (S.workerClose A.w₁ nothing) ∷ (S.workerResult A.w₁) ∷ []
  abstract
    rejectPath : S.Executes (F.p7) rejectActions (F.h6)
    rejectPath = S.next reject1 (S.next reject2 (S.next reject3 (S.next reject4 (S.next reject5 (S.next reject6 (S.done))))))

  actions : List S.Action
  actions = birthActions ++ (installedActions ++ rejectActions)
  abstract
    initialized : S.Executes F.start actions F.h6
    initialized = append birthPath (append installedPath rejectPath)
  restored-before-close : Shared.mapCell (Shared.cm (S.shared F.h3)) ≡ Shared.full F.binding
  restored-before-close = refl
  restored-is-still-open : lookup (ident 1) (Shared.sockets (S.shared F.h3)) ≡ just (Shared.admitting A.w₁)
  restored-is-still-open = refl
  one-close-normal-result : lookup A.w₁ (S.workers F.h6) ≡ just (S.rawWorker F.r₁ (S.resultAvailable S.returned) 1)
  one-close-normal-result = refl
  socket-closed : lookup (ident 1) (Shared.sockets (S.shared F.h6)) ≡ just Shared.closed
  socket-closed = refl
  first-handler-preserved : Shared.handlers (S.shared F.h6) ≡ (A.child₀ , I.captured) ∷ []
  first-handler-preserved = refl
  first-physical-birth-preserved : lookup A.child₀ (physicalThreads F.h6) ≡
    just (H.handlerThread I.captured H.maskedSetup)
  first-physical-birth-preserved = refl
  no-second-physical-birth : lookup A.child₁ (physicalThreads F.h6) ≡ nothing
  no-second-physical-birth = refl
  no-second-promise-allocation : Shared.nextPromise (S.shared F.h6) ≡ 1
  no-second-promise-allocation = refl
  preserved-first-entry : lookup (ident 0) (Shared.entries (Shared.cm (S.shared F.h6))) ≡
    just (Shared.unnegotiated inbound A.key₀ A.child₀)
  preserved-first-entry = refl
  no-close-before-restore : S.step (S.workerClose A.w₁ nothing) F.h2 ≡ nothing
  no-close-before-restore = refl
  no-return-before-restore : S.step (S.workerPrefixReturned A.w₁) F.h2 ≡ nothing
  no-return-before-restore = refl
  no-exception-for-normal-limit : S.step (S.workerPrefixException A.w₁ F.err) F.h3 ≡ nothing
  no-exception-for-normal-limit = refl
  no-result-before-close : S.step (S.workerResult A.w₁) F.h4 ≡ nothing
  no-result-before-close = refl
  no-lower-close-bypass : S.step (admit A.w₁ Admission.close) F.h4 ≡ nothing
  no-lower-close-bypass = refl
  differentLimit : Shared.Admission
  differentLimit = record F.r₁ { hardLimit = 2 }
  no-mismatched-limit : S.step (S.acceptedFork A.w₁ differentLimit) F.one ≡ nothing
  no-mismatched-limit = refl

  -- A failed normal close enters onException, which attempts one cleanup close.
  failed retryOK retryOKResult retryFailed retryResult : S.State
  failed = F.physicalClose A.w₁ F.r₁ (Shared.closeUncertain F.closeErr)
    (S.closeException (S.sync F.closeErr)) 1 F.h4
  retryOK = F.physicalClose A.w₁ F.r₁ Shared.closed
    (S.bodyExited (S.raised (S.sync F.closeErr))) 2 failed
  retryOKResult = S.setPC A.w₁ (S.rawWorker F.r₁ (S.bodyExited (S.raised (S.sync F.closeErr))) 2)
    (S.resultAvailable (S.raised (S.sync F.closeErr))) retryOK
  retryFailed = F.physicalClose A.w₁ F.r₁ (Shared.closeUncertain F.replacement)
    (S.bodyExited (S.raised (S.async F.replacement))) 2 failed
  retryResult = S.setPC A.w₁ (S.rawWorker F.r₁ (S.bodyExited (S.raised (S.async F.replacement))) 2)
    (S.resultAvailable (S.raised (S.async F.replacement))) retryFailed
  failedClose1 : S.step (S.workerClose A.w₁ (just (S.sync F.closeErr))) (F.h4) ≡ just (failed)
  failedClose1 = refl
  failedCloseActions : List S.Action
  failedCloseActions = (S.workerClose A.w₁ (just (S.sync F.closeErr))) ∷ []
  abstract
    failedClosePath : S.Executes (F.h4) failedCloseActions (failed)
    failedClosePath = S.next failedClose1 (S.done)
  successfulRetry1 : S.step (S.workerClose A.w₁ nothing) (failed) ≡ just (retryOK)
  successfulRetry1 = refl
  successfulRetry2 : S.step (S.workerResult A.w₁) retryOK ≡ just retryOKResult
  successfulRetry2 = refl
  successfulRetryActions : List S.Action
  successfulRetryActions = (S.workerClose A.w₁ nothing) ∷ S.workerResult A.w₁ ∷ []
  abstract
    successfulRetryPath : S.Executes (failed) successfulRetryActions retryOKResult
    successfulRetryPath = S.next successfulRetry1 (S.next successfulRetry2 S.done)
  failedRetry1 : S.step (S.workerClose A.w₁ (just (S.async F.replacement))) (failed) ≡ just (retryFailed)
  failedRetry1 = refl
  failedRetry2 : S.step (S.workerResult A.w₁) (retryFailed) ≡ just (retryResult)
  failedRetry2 = refl
  failedRetryActions : List S.Action
  failedRetryActions = (S.workerClose A.w₁ (just (S.async F.replacement))) ∷ (S.workerResult A.w₁) ∷ []
  abstract
    failedRetryPath : S.Executes (failed) failedRetryActions (retryResult)
    failedRetryPath = S.next failedRetry1 (S.next failedRetry2 (S.done))

  abstract
    initialized-retry-success : S.Executes F.start
      (birthActions ++ (installedActions ++
        (admit A.w₁ Admission.take ∷ admit A.w₁ Admission.countLimit ∷ admit A.w₁ Admission.putMapBack ∷
         S.workerPrefixReturned A.w₁ ∷ (failedCloseActions ++ successfulRetryActions)))) retryOKResult
    initialized-retry-success = append birthPath (append installedPath
      (S.next reject1 (S.next reject2 (S.next reject3 (S.next reject4 (append failedClosePath successfulRetryPath))))))
    initialized-retry-failure : S.Executes F.start
      (birthActions ++ (installedActions ++
        (admit A.w₁ Admission.take ∷ admit A.w₁ Admission.countLimit ∷ admit A.w₁ Admission.putMapBack ∷
         S.workerPrefixReturned A.w₁ ∷ (failedCloseActions ++ failedRetryActions)))) retryResult
    initialized-retry-failure = append birthPath (append installedPath
      (S.next reject1 (S.next reject2 (S.next reject3 (S.next reject4 (append failedClosePath failedRetryPath))))))
  failed-close-does-not-finish-logical-admission : lookup A.w₁ (Shared.admissions (S.shared failed)) ≡
    just (Shared.admissionWorker F.r₁ (Shared.closeSocket Shared.hardLimitReached))
  failed-close-does-not-finish-logical-admission = refl
  cleanup-success-preserves-error : S.resultOf A.w₁ retryOKResult ≡ just (S.raised (S.sync F.closeErr))
  cleanup-success-preserves-error = refl
  cleanup-success-body : lookup A.w₁ (S.workers retryOK) ≡
    just (S.rawWorker F.r₁ (S.bodyExited (S.raised (S.sync F.closeErr))) 2)
  cleanup-success-body = refl
  replacement-result : S.resultOf A.w₁ retryResult ≡ just (S.raised (S.async F.replacement))
  replacement-result = refl
  no-third-close : S.step (S.workerClose A.w₁ nothing) retryFailed ≡ nothing
  no-third-close = refl
  no-premature-result-on-retry : S.step (S.workerResult A.w₁) failed ≡ nothing
  no-premature-result-on-retry = refl
