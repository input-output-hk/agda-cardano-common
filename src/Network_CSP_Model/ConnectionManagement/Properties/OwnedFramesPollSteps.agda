{-# OPTIONS --guardedness #-}

-- Raw poll, governor permissions, and notePoll compose without an extra premise.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPollSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFramesFollowStep as FollowFacts
import ConnectionManagement.Properties.OwnedFramesFollowBirth as FollowBirth
import ConnectionManagement.Properties.OwnedFramesPollSource as Source
import ConnectionManagement.Properties.OwnedFramesPollAllowed as Permissions
import ConnectionManagement.Properties.OwnedFramesNotePoll as NotePoll
import ConnectionManagement.Properties.OwnedFramesThreads as ThreadRows
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module V = Observation isBearerClosed isIOManagerError
  module F = FollowFacts isBearerClosed isIOManagerError
  module B = FollowBirth isBearerClosed isIOManagerError
  module A = Permissions isBearerClosed isIOManagerError
  module N = NotePoll isBearerClosed isIOManagerError
  module Rows = ThreadRows isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Attach the new logical followup to the precise selected physical observer.
new-follow : ∀ ref caller s f → A.Allowed ref caller s → J.caller f ≡ caller → X.FollowThread ref f (C.capture s)
new-follow ref caller s f allowed same = record
  { tid = A.Allowed.tid allowed; thread = A.Allowed.thread allowed
  ; found = A.Allowed.selected allowed
  ; caller = trans same (A.Allowed.callerSame allowed)
  ; running = A.Allowed.running allowed; observing = A.Allowed.observing allowed }

-- Production policies can change ignored peer metadata while raw poll changes
-- at most one logical followup and retains the entire source CM.
raw-poll : ∀ ref caller s next stage → A.Allowed ref caller s →
  Source.Effect ref caller (PS.machine s) next → D.Held s →
  D.Held (record s { governor = GP.supervised (Policy.observed next stage)
    (GP.pool (PS.governor s)) (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) })
raw-poll ref caller s next stage allowed effect (inv , unique , aux) with Source.Effect.follows effect
... | Source.unchanged follows = subst (λ cm → Inv cm (C.capture target)) (sym (Source.Effect.source effect)) (proj₁ carried) ,
  subst Unique (sym (Source.Effect.source effect)) unique , proj₂ carried
  where
  target = record s { governor = GP.supervised (Policy.observed next stage)
    (GP.pool (PS.governor s)) (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) }
  same = V.observed-equal (C.capture s) (C.capture target) (Source.Effect.jobs effect) follows refl refl refl refl
  carried = V.observed-preserves (PS.cm s) (C.capture s) (C.capture target) same inv aux
... | Source.started f empty caller-same follows = subst (λ cm → Inv cm (C.capture target)) (sym (Source.Effect.source effect)) (proj₁ carried) ,
  subst Unique (sym (Source.Effect.source effect)) unique , proj₂ carried
  where
  formal = F.follow-context (C.capture s) ref f
  target = record s { governor = GP.supervised (Policy.observed next stage)
    (GP.pool (PS.governor s)) (GP.regions (PS.governor s)) (GP.unwinding (PS.governor s)) }
  same = V.observed-equal formal (C.capture target) (Source.Effect.jobs effect) follows refl refl refl refl
  carried = V.observed-preserves (PS.cm s) formal (C.capture target) same
    (B.born-inv (PS.cm s) (C.capture s) ref f empty inv)
    (B.born-aux (C.capture s) ref f (new-follow ref caller s f allowed caller-same) aux)

-- The physical governor pool is unchanged by poll; source erasure supplies its
-- raw successful transition rather than normalising the composed step.
governor-poll : ∀ ref caller s {g′} → A.Allowed ref caller s →
  GP.step (GP.run (Sub.pollPeer ref caller)) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-poll ref caller s allowed eq held with GP.ownerOpen (GP.pool (PS.governor s)) |
  GP.Production.step (Policy.dispatch (Sub.pollPeer ref caller)) (GP.source (PS.governor s)) in dispatched
... | opened | nothing = case eq of λ ()
... | opened | just (Policy.observed next stage) with
  GP.Production.step-projects (Policy.dispatch (Sub.pollPeer ref caller)) (GP.source (PS.governor s)) dispatched
...   | Sub.next advanced Sub.done = case just-injective eq of λ { refl →
  raw-poll ref caller s next stage allowed (Source.poll-effect ref caller (PS.machine s) advanced) held }

-- The real PSA permission guard supplies the selected running/observing thread;
-- notePoll may finish only after its logical followup has disappeared.
poll-step : ∀ ref caller s {t} → PS.step (PS.run (GP.run (Sub.pollPeer ref caller))) s ≡ just t → D.Held s → D.Held t
poll-step ref caller s stepped held with PS.governorAllowed (GP.run (Sub.pollPeer ref caller)) s in permit
... | false = case stepped of λ ()
... | true with GP.step (GP.run (Sub.pollPeer ref caller)) (PS.governor s) in advanced
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl →
  N.note-poll ref s (record s { governor = g′ }) (A.Allowed.tid allowed) (A.Allowed.thread allowed)
    (A.Allowed.selected allowed) (A.Allowed.observing allowed) saved (governor-poll ref caller s allowed advanced held) }
  where
  allowed = A.allowed-poll ref caller s permit
  saved = Rows.byPeer-lookup ref (PS.monitors s) (X.Aux.monitorKeys (proj₂ (proj₂ held))) (A.Allowed.tid allowed) (A.Allowed.thread allowed)
    (A.Allowed.selected allowed)

-- The K constructor retains every actual source and peer permission check.
k-poll : ∀ ref caller s {t} → K.step (K.peerStep (PS.run (GP.run (Sub.pollPeer ref caller)))) s ≡ just t → R.Reach s → R.Reach t
k-poll ref caller = L.peer-lift (PS.run (GP.run (Sub.pollPeer ref caller))) (poll-step ref caller)
