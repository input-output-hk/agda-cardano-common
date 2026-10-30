{-# OPTIONS --guardedness #-}

-- Initialized finite prefix exits, with real births and successful-step proofs.
-- Duplicate-key input is abstract; unresolved mfix references are not evaluated.
module ConnectionManagement.Negative.ServerAdmissionPrefixForbidden where

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

-- Limit 2 permits the second count. A real first handshake/caller completion
-- establishes inboundIdle before same-key selection throws ForbiddenOperation.
module Forbidden where
  module F = Fixtures 2 A.key₀
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
  handshake1 : S.step (handler (H.enterHandshake A.child₀)) (F.p7) ≡ just (F.s1)
  handshake1 = refl
  handshake2 : S.step (mux (U.negotiate A.child₀ I.ps duplex)) (F.s1) ≡ just (F.s2)
  handshake2 = refl
  handshake3 : S.step (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))) (F.s2) ≡ just (F.s3)
  handshake3 = refl
  handshake4 : S.step (mux (U.publishSuccess A.child₀)) (F.s3) ≡ just (F.s4)
  handshake4 = refl
  handshake5 : S.step (consume Handshake.readResult) (F.s4) ≡ just (F.s5)
  handshake5 = refl
  handshake6 : S.step (consume Handshake.commitResult) (F.s5) ≡ just (F.s6)
  handshake6 = refl
  handshake7 : S.step (consume Handshake.readResultCounters) (F.s6) ≡ just (F.s7)
  handshake7 = refl
  handshake8 : S.step (consume Handshake.enqueueInbound) (F.s7) ≡ just (F.s8)
  handshake8 = refl
  handshake9 : S.step (consume Handshake.returnResult) (F.s8) ≡ just (F.s9)
  handshake9 = refl
  handshake10 : S.step (S.workerReturned A.w₀) (F.s9) ≡ just (F.s10)
  handshake10 = refl
  handshake11 : S.step (S.workerResult A.w₀) (F.s10) ≡ just (F.s11)
  handshake11 = refl
  handshakeActions : List S.Action
  handshakeActions = (handler (H.enterHandshake A.child₀)) ∷ (mux (U.negotiate A.child₀ I.ps duplex)) ∷ (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))) ∷ (mux (U.publishSuccess A.child₀)) ∷ (consume Handshake.readResult) ∷ (consume Handshake.commitResult) ∷ (consume Handshake.readResultCounters) ∷ (consume Handshake.enqueueInbound) ∷ (consume Handshake.returnResult) ∷ (S.workerReturned A.w₀) ∷ (S.workerResult A.w₀) ∷ []
  abstract
    handshakePath : S.Executes (F.p7) handshakeActions (F.s11)
    handshakePath = S.next handshake1 (S.next handshake2 (S.next handshake3 (S.next handshake4 (S.next handshake5 (S.next handshake6 (S.next handshake7 (S.next handshake8 (S.next handshake9 (S.next handshake10 (S.next handshake11 (S.done)))))))))))
  reject1 : S.step (admit A.w₁ Admission.take) (F.s11) ≡ just (F.b1)
  reject1 = refl
  reject2 : S.step (admit A.w₁ Admission.countLimit) (F.b1) ≡ just (F.b2)
  reject2 = refl
  reject3 : S.step (admit A.w₁ Admission.allocatePromise) (F.b2) ≡ just (F.b3)
  reject3 = refl
  reject4 : S.step (admit A.w₁ Admission.chooseEntry) (F.b3) ≡ just (F.b4)
  reject4 = refl
  reject5 : S.step (admit A.w₁ Admission.restore) (F.b4) ≡ just (F.b5)
  reject5 = refl
  reject6 : S.step (S.workerPrefixException A.w₁ F.err) (F.b5) ≡ just (F.b6)
  reject6 = refl
  reject7 : S.step (S.workerClose A.w₁ nothing) (F.b6) ≡ just (F.b7)
  reject7 = refl
  reject8 : S.step (S.workerResult A.w₁) (F.b7) ≡ just (F.b8)
  reject8 = refl
  rejectActions : List S.Action
  rejectActions = (admit A.w₁ Admission.take) ∷ (admit A.w₁ Admission.countLimit) ∷ (admit A.w₁ Admission.allocatePromise) ∷ (admit A.w₁ Admission.chooseEntry) ∷ (admit A.w₁ Admission.restore) ∷ (S.workerPrefixException A.w₁ F.err) ∷ (S.workerClose A.w₁ nothing) ∷ (S.workerResult A.w₁) ∷ []
  abstract
    rejectPath : S.Executes (F.s11) rejectActions (F.b8)
    rejectPath = S.next reject1 (S.next reject2 (S.next reject3 (S.next reject4 (S.next reject5 (S.next reject6 (S.next reject7 (S.next reject8 (S.done))))))))

  actions : List S.Action
  actions = birthActions ++ (installedActions ++ (handshakeActions ++ rejectActions))
  abstract
    initialized : S.Executes F.start actions F.b8
    initialized = append birthPath (append installedPath (append handshakePath rejectPath))
  first-caller-completed : S.resultOf A.w₀ F.b8 ≡ just S.returned
  first-caller-completed = refl
  restored-map : Shared.mapCell (Shared.cm (S.shared F.b8)) ≡ Shared.full F.binding
  restored-map = refl
  old-entry-preserved : Shared.entries (Shared.cm (S.shared F.b8)) ≡
    (ident 0 , Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) ∷ []
  old-entry-preserved = refl
  old-handler-preserved : Shared.handlers (S.shared F.b8) ≡ (A.child₀ , I.captured) ∷ []
  old-handler-preserved = refl
  old-socket-preserved : lookup (ident 0) (Shared.sockets (S.shared F.b8)) ≡ just (Shared.handling A.child₀)
  old-socket-preserved = refl
  second-socket-closed : lookup (ident 1) (Shared.sockets (S.shared F.b8)) ≡ just Shared.closed
  second-socket-closed = refl
  no-second-physical-handler : lookup A.child₁ (physicalThreads F.b8) ≡ nothing
  no-second-physical-handler = refl
  raised-after-one-close : lookup A.w₁ (S.workers F.b8) ≡
    just (S.rawWorker F.r₁ (S.resultAvailable (S.raised (S.sync F.err))) 1)
  raised-after-one-close = refl
  no-exception-before-restore : S.step (S.workerPrefixException A.w₁ F.err) F.b4 ≡ nothing
  no-exception-before-restore = refl
  no-normal-prefix-return : S.step (S.workerPrefixReturned A.w₁) F.b5 ≡ nothing
  no-normal-prefix-return = refl
  no-close-before-restore : S.step (S.workerClose A.w₁ nothing) F.b4 ≡ nothing
  no-close-before-restore = refl
  no-result-before-close : S.step (S.workerResult A.w₁) F.b6 ≡ nothing
  no-result-before-close = refl
  no-lower-close-bypass : S.step (admit A.w₁ Admission.close) F.b6 ≡ nothing
  no-lower-close-bypass = refl
  replaced replacedResult : S.State
  replaced = F.physicalClose A.w₁ F.r₁ (Shared.closeUncertain F.replacement)
    (S.bodyExited (S.raised (S.async F.replacement))) 1 F.b6
  replacedResult = S.setPC A.w₁ (S.rawWorker F.r₁ (S.bodyExited (S.raised (S.async F.replacement))) 1)
    (S.resultAvailable (S.raised (S.async F.replacement))) replaced
  cleanupFailure1 : S.step (S.workerClose A.w₁ (just (S.async F.replacement))) (F.b6) ≡ just (replaced)
  cleanupFailure1 = refl
  cleanupFailure2 : S.step (S.workerResult A.w₁) (replaced) ≡ just (replacedResult)
  cleanupFailure2 = refl
  cleanupFailureActions : List S.Action
  cleanupFailureActions = (S.workerClose A.w₁ (just (S.async F.replacement))) ∷ (S.workerResult A.w₁) ∷ []
  abstract
    cleanupFailurePath : S.Executes (F.b6) cleanupFailureActions (replacedResult)
    cleanupFailurePath = S.next cleanupFailure1 (S.next cleanupFailure2 (S.done))

  abstract
    initialized-cleanup-failure : S.Executes F.start
      (birthActions ++ (installedActions ++ (handshakeActions ++
        (admit A.w₁ Admission.take ∷ admit A.w₁ Admission.countLimit ∷ admit A.w₁ Admission.allocatePromise ∷
         admit A.w₁ Admission.chooseEntry ∷ admit A.w₁ Admission.restore ∷ S.workerPrefixException A.w₁ F.err ∷
         cleanupFailureActions)))) replacedResult
    initialized-cleanup-failure = append birthPath (append installedPath (append handshakePath
      (S.next reject1 (S.next reject2 (S.next reject3 (S.next reject4 (S.next reject5 (S.next reject6 cleanupFailurePath))))))))
  replacement-result : S.resultOf A.w₁ replacedResult ≡ just (S.raised (S.async F.replacement))
  replacement-result = refl
  no-cleanup-retry : S.step (S.workerClose A.w₁ nothing) replaced ≡ nothing
  no-cleanup-retry = refl
