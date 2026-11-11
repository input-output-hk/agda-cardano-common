{-# OPTIONS --guardedness #-}

-- Full strengthened predicate with initialization and source-side preservation.
-- OwnedFramesExecution assembles all peer cases and the execution induction.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesReach
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCore as Core
import ConnectionManagement.Properties.OwnedFramesUnique as Tables
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob; aux-initial)
private
  module E = Exit isBearerClosed
  module U = Tables isBearerClosed isIOManagerError
  module B = Core isBearerClosed isIOManagerError

-- Region bookkeeping leaves every followup witness intact.
note-follow : ∀ a c k ref f → FollowThread ref f k → FollowThread ref f (K.noteCore a c k)
note-follow a c k ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- A detached governor caller and its handle are unchanged by region notes.
note-unwind : ∀ a c k j f → UnwindJob j f k → UnwindJob j f (K.noteCore a c k)
note-unwind a c k j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old
  ; caller = UnwindJob.caller old; phase = UnwindJob.phase old
  ; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- The complete metadata predicate therefore survives every core note.
note-aux : ∀ a c k → Aux k → Aux (K.noteCore a c k)
note-aux a c k old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old
  ; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → note-follow a c k ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → note-unwind a c k j f (Aux.unwindingJobs old j f found) }

-- A/R remain an unchanged projection of the full requested predicate.
Reach : K.State → Set
Reach s = Owned s × Unique (K.source s) × Aux (K.context s)

-- Both source and peer tables satisfy their invariant at accepted initialization.
initial-reach : ∀ c g {s} → K.initial (O.initial c) g ≡ just s → Reach s
initial-reach c g initialized = initial c g initialized , U.initial-unique c g initialized , metadata initialized
  where
  metadata : ∀ {s} → K.initial (O.initial c) g ≡ just s → Aux (K.context s)
  metadata initialized with E.initial (O.initial c)
  ... | nothing = case initialized of λ ()
  ... | just e = case just-injective initialized of λ { refl → aux-initial (O.initial c) g }

-- Server contexts are unchanged, so their source proof preserves the full Reach.
server-reach : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → Reach s → Reach t
server-reach a s {t} stepped (owned , unique , aux) =
  server-preserves a s stepped owned , U.server-unique a s stepped unique ,
  subst Aux (sym context) aux
  where
  import ConnectionManagement.Properties.SourceKeysShared as SharedKeys
  module Keys = SharedKeys isBearerClosed isIOManagerError
  context = proj₂ (Keys.server-keys a s stepped)

-- Core preservation now obtains the uniqueness premise from Reach itself.
core-reach : ∀ a s {t} → K.step (K.coreStep a) s ≡ just t → Reach s → Reach t
core-reach a s {t} stepped (owned , unique , aux) =
  B.core-preserves a s stepped unique owned , U.core-unique a s stepped unique ,
  subst Aux (sym context) (note-aux a (K.source t) (K.context s) aux)
  where
  import ConnectionManagement.Properties.SourceKeysShared as SharedKeys
  module Keys = SharedKeys isBearerClosed isIOManagerError
  context = proj₂ (Keys.core-keys a s stepped)

-- Explicit projection: neither ownership clause has been weakened.
reach-owned : ∀ {s} → Reach s → Owned s
reach-owned = proj₁
