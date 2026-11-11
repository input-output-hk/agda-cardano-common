{-# OPTIONS --guardedness #-}

-- Actual governor job fork, with freshness obtained from the K-level guard.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesForkJob
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (suc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Domain using (ident; WorkerId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesCore as Core
import ConnectionManagement.Properties.OwnedFramesFresh as Fresh
import ConnectionManagement.Properties.OwnedFramesJobBirth as Birth
import ConnectionManagement.Properties.OwnedFramesJobNames as Names
import ConnectionManagement.Properties.OwnedFramesPoolTransport as PoolFacts
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module B = Birth isBearerClosed isIOManagerError
  module F = Fresh isBearerClosed isIOManagerError
  module N = Names isBearerClosed isIOManagerError
  module P = PoolFacts isBearerClosed isIOManagerError
  module V = Observation isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError
  module Cores = Core isBearerClosed isIOManagerError

-- The actual raw fork creates exactly one begin frame at the old job supply.
record Born (caller : WorkerId) (c d : Sub.Configuration) : Set where
  field
    frame : Sub.JobFrame
    callerSame : J.caller (Sub.execution frame) ≡ caller
    beginning : J.pc (Sub.execution frame) ≡ J.begin
    rows : Sub.jobs d ≡ put (ident (Sub.nextJob c)) frame (Sub.jobs c)
    source : J.cm (Sub.world d) ≡ J.cm (Sub.world c)
    follows : Sub.monitors d ≡ Sub.monitors c

-- Invert the source fork's current-PC, worker-free and capture branches.
fork-shape : ∀ caller child sock c {d} → Sub.advance (Sub.forkJob caller child sock) c ≡ just d → Born caller c d
fork-shape caller child sock c eq with Sub.pc c | Sub.workerFree caller c
... | Sub.launch (work ∷ rest) | true with G.captured work
...   | nothing = case just-injective eq of λ { refl → record
  { frame = Sub.jobFrame (J.frame work caller child sock (ident (Sub.nextPeer c)) J.begin) false false
  ; callerSame = refl; beginning = refl; rows = refl; source = refl; follows = refl } }
...   | just ref = case just-injective eq of λ { refl → record
  { frame = Sub.jobFrame (J.frame work caller child sock ref J.begin) false false
  ; callerSame = refl; beginning = refl; rows = refl; source = refl; follows = refl } }
fork-shape caller child sock c eq | Sub.launch (work ∷ rest) | false = case eq of λ ()
fork-shape caller child sock c eq | Sub.publishPublic | free = case eq of λ ()
fork-shape caller child sock c eq | Sub.sampleInputs | free = case eq of λ ()
fork-shape caller child sock c eq | Sub.prepareWait | free = case eq of λ ()
fork-shape caller child sock c eq | Sub.selecting | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.cancelTimer selected) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.apply selected) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.publishView work) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.traceDecision work) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.register j rest) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.completionAssertionFailed result) | free = case eq of λ ()
fork-shape caller child sock c eq | (Sub.launch []) | free = case eq of λ ()

-- The captured physical handle can be forked only once.
pool-fresh : ∀ j p {p′} → GP.Pool.step (GP.Pool.fork j) p ≡ just p′ → lookup j (GP.Pool.handles p) ≡ nothing
pool-fresh j p eq with GP.Pool.phase p | GP.Pool.parentFork p | lookup j (GP.Pool.handles p)
... | GP.Pool.openPool | nothing | nothing = refl
... | GP.Pool.openPool | just parent | handle = case eq of λ ()
... | GP.Pool.openPool | nothing | just phase = case eq of λ ()
... | GP.Pool.closing | parent | handle = case eq of λ ()
... | GP.Pool.closedPool | parent | handle = case eq of λ ()
... | GP.Pool.cancelPending tid | parent | handle = case eq of λ ()
... | GP.Pool.joinPending tid | parent | handle = case eq of λ ()

-- Logical birth and physical fork compose before registration, with all caller
-- separation facts carried into the same returned context.
governor-fork : ∀ caller child sock s {g′} → B.Free caller (PS.cm s) (C.capture s) →
  GP.step (GP.run (Sub.forkJob caller child sock)) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-fork caller child sock s free eq (inv , unique , aux) with GP.ownerOpen (GP.pool (PS.governor s))
... | false = case eq of λ ()
... | true with GP.Pool.step (GP.Pool.fork (ident (Sub.nextJob (PS.machine s)))) (GP.pool (PS.governor s)) in forked |
  GP.Production.step (Policy.dispatch (Sub.forkJob caller child sock)) (GP.source (PS.governor s)) in dispatched
...   | just p′ | just source′ with GP.Production.step-projects (Policy.dispatch (Sub.forkJob caller child sock)) (GP.source (PS.governor s)) dispatched
...     | Sub.next advanced Sub.done = case just-injective eq of λ { refl →
  subst (λ cm → Inv cm (C.capture target)) (sym (Born.source shape)) (proj₁ carried) ,
  subst Unique (sym (Born.source shape)) unique , proj₂ carried }
  where
  shape = fork-shape caller child sock (PS.machine s) advanced
  j = ident (Sub.nextJob (PS.machine s))
  next = Born.frame shape
  free-next = subst (λ w → B.Free w (PS.cm s) (C.capture s)) (sym (Born.callerSame shape)) free
  fresh = pool-fresh j (GP.pool (PS.governor s)) forked
  stable = P.G.step-stable (GP.Pool.fork j) (GP.pool (PS.governor s)) refl forked
  born-context = N.job-context (C.capture s) (put j next (Sub.jobs (PS.machine s)))
  after-context = P.gov-context born-context p′
  born-inv = B.born-inv (PS.cm s) (C.capture s) j next free-next fresh inv
  born-aux = B.born-aux (PS.cm s) (C.capture s) j next free-next fresh aux
  target = record s { governor = GP.supervised source′ p′ (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) }
  same = V.observed-equal after-context (C.capture target) (Born.rows shape) (Born.follows shape) refl refl refl refl
  carried = V.observed-preserves (PS.cm s) after-context (C.capture target) same
    (P.gov-inv (PS.cm s) born-context p′ stable born-inv) (P.gov-aux born-context p′ stable born-aux)
governor-fork caller child sock s free eq held | true | nothing | source = case eq of λ ()
governor-fork caller child sock s free eq held | true | just pool | nothing = case eq of λ ()

-- PSA keeps its real owner/scope permissions for the fork.
ps-fork : ∀ caller child sock s {t} → B.Free caller (PS.cm s) (C.capture s) →
  PS.step (PS.run (GP.run (Sub.forkJob caller child sock))) s ≡ just t → D.Held s → D.Held t
ps-fork caller child sock s free = L.governor-lift (GP.run (Sub.forkJob caller child sock)) s (governor-fork caller child sock s free) (λ after → refl)

-- The shared K permission supplies freshness; no caller-separation premise is
-- added to the actual K theorem.
k-fork : ∀ caller child sock s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.forkJob caller child sock)))) s ≡ just t → R.Reach s → R.Reach t
k-fork caller child sock s eq held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.run (Sub.forkJob caller child sock))) s in permitted
... | false = case eq of λ ()
... | true with PS.step (PS.run (GP.run (Sub.forkJob caller child sock))) (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → ps-fork caller child sock (K.peers s)
  (F.fork-free caller child sock s (proj₂ (Cores.and-true (K.peerOpen s) (K.peerAllowed (PS.run (GP.run (Sub.forkJob caller child sock))) s) permitted))) advanced held }
