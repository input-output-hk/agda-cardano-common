{-# OPTIONS --guardedness #-}

-- Witness for the late-admission residue. Continue the initialized run of
-- Negative/ServerAdmission past its end: the Server has returned and the CM
-- shutdown coordinator has closed (over an empty snapshot). The second raw
-- admission worker, forked by the accept loop before the close and never
-- joined, still takes the map, allocates a promise, selects an entry and forks
-- a physical connection handler. That handler is in neither the coordinator's
-- snapshot nor its collected list. The model admits this without any forged
-- state; see SourceReplay/README.md for the source evidence.
module ConnectionManagement.Negative.ServerLateAdmission where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing; fromMaybe; is-just)
open import Data.Bool using (true)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerAdmission as Run
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CMShutdown as Close
open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (physicalThreads; append; admit)
private
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module R = N.R
  module W = N.W

-- Run a list of actions; the witness states are computed, not forged.
run : List S.Action → S.State → Maybe S.State
run [] s = just s
run (a ∷ as) s with S.step a s
... | nothing = nothing
... | just t = run as t
runs : ∀ as s {t} → run as s ≡ just t → S.Executes s as t
runs [] s refl = S.done
runs (a ∷ as) s eq with S.step a s in stepped
... | nothing = case eq of λ ()
... | just t = S.next stepped (runs as t eq)

coordinator : S.State → Close.State
coordinator s = W.shutdown (R.base (N.raw (S.base s)))

lateActions : List S.Action
lateActions = admit A.w₁ Admission.take ∷ admit A.w₁ Admission.countLimit ∷
  admit A.w₁ Admission.allocatePromise ∷ admit A.w₁ Admission.chooseEntry ∷
  admit A.w₁ Admission.fork ∷ []

late : S.State
late = fromMaybe Run.returnedServer (run lateActions Run.returnedServer)

late-run : run lateActions Run.returnedServer ≡ just late
late-run = refl

-- One initialized run: the Server's own scope chain, CM close and return,
-- then the late admission steps.
abstract
  initialized : S.Executes Run.start (Run.allActions ++ lateActions) late
  initialized = append Run.initialized (runs lateActions Run.returnedServer late-run)

-- Before the late steps: the Server has returned and the coordinator closed.
returned-before : S.stage Run.returnedServer ≡ S.serverReturned
returned-before = refl
closed-before : coordinator Run.returnedServer ≡ Close.shutdownState Close.closed [] [] []
closed-before = refl
no-handler-before : lookup A.child₁ (physicalThreads Run.returnedServer) ≡ nothing
no-handler-before = refl

-- After them: still returned and closed, and a new physical handler exists.
returned-after : S.stage late ≡ S.serverReturned
returned-after = refl
closed-after : coordinator late ≡ Close.shutdownState Close.closed [] [] []
closed-after = refl
late-handler : is-just (lookup A.child₁ (physicalThreads late)) ≡ true
late-handler = refl
-- The late handler is outside the coordinator's snapshot and collected list.
late-not-collected : Close.collected (coordinator late) ≡ []
late-not-collected = refl
