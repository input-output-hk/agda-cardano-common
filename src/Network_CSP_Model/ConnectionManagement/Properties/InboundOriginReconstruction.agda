{-# OPTIONS --guardedness #-}

-- The concrete frontend adapter derives all continuation fields from an actual
-- successful primitive fork; the generic engine retains the original labels.
module ConnectionManagement.Properties.InboundOriginReconstruction where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId; PromiseId; EntryId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.InboundOriginFrontend as Generic
import ConnectionManagement.Properties.InboundOriginEffect as Effects

-- No positive PC premise is supplied: every other primitive branch is disabled.
fork-PC : ∀ worker before {after} → M.advance (M.admissionStep worker Admission.fork) before ≡ just after →
 Σ S.Admission (λ request → Σ S.Lease (λ saved → Σ PromiseId (λ promise → Σ EntryId (λ entry →
 lookup worker (S.admissions (M.world before)) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry))))))
fork-PC worker before actual with lookup worker (S.admissions (M.world before)) in owned
... | nothing = case actual of λ ()
... | just (S.admissionWorker request pc) with pc
fork-PC worker before actual | just (S.admissionWorker request pc) | S.acquireMap = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.count saved = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.prepare saved = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.selectEntry saved promise = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.forkHandler saved promise entry = request , saved , promise , entry , refl
fork-PC worker before actual | just (S.admissionWorker request pc) | S.publish saved promise entry = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.reject saved failure = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.closeSocket failure = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.finished failure = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.countPublished promise entry = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.awaitHandshake promise entry = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.commitHandshake entry result = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.countHandshake completion = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.notifyInbound info = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.returnHandshake completion = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.completedHandshake completion = case actual of λ ()
fork-PC worker before actual | just (S.admissionWorker request pc) | S.impossibleHandshake = case actual of λ ()

module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private
  module T = Combined.Protocols b io capability using (Runtime; Event; advance; Runs; stop; more; initialize; base)
  module K = Combined b io using (source)
  module ServerModel = Server b using (initial)
  module ExitModel = Exit b using (initial)
  module PublicationModel = Publication b using (initial)
 core : T.Runtime → M.Configuration
 core s = O.core (K.source (T.base s))
 shared : T.Runtime → S.State
 shared s = M.world (core s)
 initialized-source : ∀ c g {start} → T.initialize c g ≡ just start → K.source (T.base start) ≡ c
 initialized-source c g actual with ExitModel.initial c in lower
 ... | nothing = case actual of λ ()
 ... | just e = case just-injective actual of λ { refl → ExitFacts.initial-source b c lower }

 -- Initialization's successful Server guard excludes preloaded continuations.
 server-empty : ∀ c {s} → ServerModel.initial c ≡ just s → S.admissions (M.world (O.core c)) ≡ []
 server-empty c actual with S.admissions (M.world (O.core c)) | S.sockets (M.world (O.core c)) | PublicationModel.initial c
 ... | [] | [] | just _ = refl
 ... | _ ∷ _ | _ | _ = case actual of λ ()
 ... | [] | _ ∷ _ | _ = case actual of λ ()
 ... | [] | [] | nothing = case actual of λ ()
 exit-empty : ∀ c {s} → ExitModel.initial c ≡ just s → S.admissions (M.world (O.core c)) ≡ []
 exit-empty c actual with M.inboundRelease (O.core c) | M.remoteCall (O.core c) | ServerModel.initial c in lower
 ... | nothing | nothing | just _ = server-empty c lower
 ... | just _ | _ | _ = case actual of λ ()
 ... | nothing | just _ | _ = case actual of λ ()
 ... | nothing | nothing | nothing = case actual of λ ()
 input-empty : ∀ c g {start} → T.initialize c g ≡ just start → S.admissions (M.world (O.core c)) ≡ []
 input-empty c g actual with ExitModel.initial c in lower
 ... | nothing = case actual of λ ()
 ... | just _ = exit-empty c lower
 initialized-empty : ∀ c g {start} → T.initialize c g ≡ just start → S.admissions (shared start) ≡ []
 initialized-empty c g actual = trans
   (cong (λ source → S.admissions (M.world (O.core source))) (initialized-source c g actual))
   (input-empty c g actual)

 module Proof (observe : ∀ action before {after} → T.advance action before ≡ just after → Effects.Effect (core before) (core after)) where
  module History = Generic.Engine T.Runtime T.Event T.advance core observe
  to-runs : ∀ {before events after} → T.Runs before events after → History.Runs before events after
  to-runs T.stop = History.done
  to-runs (T.more actual rest) = History.next actual (to-runs rest)
  from-runs : ∀ {before events after} → History.Runs before events after → T.Runs before events after
  from-runs History.done = T.stop
  from-runs (History.next actual rest) = T.more actual (from-runs rest)

  initialized-selected-origin : ∀ c g {start observed before parent request saved promise entry} →
    T.initialize c g ≡ just start → T.Runs start observed before →
    lookup parent (S.admissions (shared before)) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) →
    History.SelectedOrigin start observed before parent request saved promise entry
  initialized-selected-origin c g initialized path found = History.selected-origin (initialized-empty c g initialized) (to-runs path) found

  record ForkOrigin (start : T.Runtime) (observed : List T.Event) (before born : T.Runtime) (parent : WorkerId) (label : T.Event) : Set where
   field
    request : S.Admission
    heldLease : S.Lease
    promise : PromiseId
    entry : EntryId
    selection : History.SelectedOrigin start observed before parent request heldLease promise entry
    fork-event : T.advance label before ≡ just born
    fork-source : M.advance (M.admissionStep parent Admission.fork) (core before) ≡ just (core born)

  -- The actual label is retained verbatim, including core-dispatch aliases.
  initialized-fork-origin : ∀ c g {start observed before born parent label} →
    T.initialize c g ≡ just start → T.Runs start observed before →
    T.advance label before ≡ just born →
    M.advance (M.admissionStep parent Admission.fork) (core before) ≡ just (core born) →
    ForkOrigin start observed before born parent label
  initialized-fork-origin c g {before = before} {parent = parent} initialized path actual source with fork-PC parent (core before) source
  ... | request , saved , promise , entry , found = record
    { request = request; heldLease = saved; promise = promise; entry = entry
    ; selection = initialized-selected-origin c g initialized path found
    ; fork-event = actual; fork-source = source }
