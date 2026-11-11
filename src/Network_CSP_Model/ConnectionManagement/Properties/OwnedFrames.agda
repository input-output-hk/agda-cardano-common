{-# OPTIONS --guardedness #-}

-- Frame ownership at the shared Server/peer boundary. Frame presence, rather
-- than the payload of its continuation, is the premise of each ownership clause.
-- This module proves initialization and Server preservation. The companion
-- Core module requires incoming table uniqueness. OwnedFramesExecution proves
-- the full strengthened invariant for all steps and initialized executions.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFrames
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import ConnectionManagement.Domain using (WorkerId; JobId; PeerConnectionId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.SourceKeysShared as SharedKeys
open import ConnectionManagement.Properties.OutboundKeys using (KeySame; acquiringKeys; releasingKeys; acquiredSame; releasedSame)

module K = Combined isBearerClosed isIOManagerError
module PS = Supervision isIOManagerError
module GP = PS.GP
module C = Context isIOManagerError
private
  module E = Exit isBearerClosed
  module Keys = SharedKeys isBearerClosed isIOManagerError

-- A foreign caller is owned by neither historical peer-job nor monitor table.
Foreign : WorkerId → C.Context → Set
Foreign w k = GP.unowned w (C.SubContext.jobs (C.subsystem k)) ≡ true ×
  PS.byWorker w (C.monitors k) ≡ nothing

-- A job witness includes the physical running-body phase, not just its PC.
record JobAwait (w : WorkerId) (pc : J.PC) (k : C.Context) : Set where
  constructor job-await
  field
    job : JobId
    frame : Sub.JobFrame
    found : lookup job (C.SubContext.jobs (C.subsystem k)) ≡ just frame
    caller : J.caller (Sub.execution frame) ≡ w
    waiting : J.pc (Sub.execution frame) ≡ pc
    running : lookup job (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning

-- A monitor followup awaits the matching frame kind on its observing thread.
record FollowAwait (w : WorkerId) (pc : J.PC) (k : C.Context) : Set where
  constructor follow-await
  field
    ref : PeerConnectionId
    frame : J.Frame
    found : lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just frame
    caller : J.caller frame ≡ w
    waiting : J.pc frame ≡ pc
    tid : JobId
    thread : PS.Thread
    byPeer : PS.byPeer ref (C.monitors k) ≡ just (tid , thread)
    worker : PS.worker thread ≡ w
    running : lookup tid (PS.Pool.handles (C.monitorPool k)) ≡ just PS.Pool.bodyRunning
    observing : PS.pc thread ≡ PS.observing

-- The requested owner alternatives are stated independently of CM payloads.
Owner : WorkerId → J.PC → C.Context → Set
Owner w pc k = Foreign w k ⊎ (JobAwait w pc k ⊎ FollowAwait w pc k)

-- These are exactly clauses A and R. Supporting preservation invariants can
-- imply this predicate without changing either final ownership consequence.
record Inv (c : O.Configuration) (k : C.Context) : Set where
  constructor owned-frames
  field
    acquiring : ∀ w → is-just (lookup w (O.acquiring c)) ≡ true →
      lookup w (O.acquired c) ≡ nothing × Owner w J.awaitAcquire k
    releasing : ∀ w → is-just (lookup w (O.releasing c)) ≡ true →
      lookup w (O.released c) ≡ nothing × Owner w J.awaitRelease k
open Inv public

-- The K-state predicate observes its single source and CM-free context.
Owned : K.State → Set
Owned s = Inv (K.source s) (K.context s)

-- Frame-free CM initialization satisfies both clauses for any peer context.
empty : ∀ c k → Inv (O.initial c) k
empty c k = owned-frames (λ w ()) (λ w ())

-- Key-preserving source changes transport the complete requested predicate.
same-source : ∀ {c d k} → KeySame c d → Inv c k → Inv d k
same-source {c} {d} same inv = owned-frames
  (λ w present → let old = acquiring inv w (trans (sym (acquiringKeys same w)) present)
    in trans (cong (lookup w) (acquiredSame same)) (proj₁ old) , proj₂ old)
  (λ w present → let old = releasing inv w (trans (sym (releasingKeys same w)) present)
    in trans (cong (lookup w) (releasedSame same)) (proj₁ old) , proj₂ old)

-- Every allowed Server step preserves A and R through server-keys.
server-preserves : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → Owned s → Owned t
server-preserves a s {t} stepped inv with Keys.server-keys a s stepped
... | same , context = subst (Inv (K.source t)) (sym context) (same-source same inv)

-- Initialization uses the outer runtime's O.initial profile. K.initial alone
-- also accepts supplied CM state and does not promise empty outbound frames.
initial : ∀ c g {s} → K.initial (O.initial c) g ≡ just s → Owned s
initial c g initialized with E.initial (O.initial c) in server
... | nothing = case initialized of λ ()
... | just e = case just-injective initialized of λ { refl → subst
  (λ source → Inv source (C.capture (PS.initial (O.initial c) g)))
  (sym (ExitFacts.initial-source isBearerClosed (O.initial c) server))
  (empty c (C.capture (PS.initial (O.initial c) g))) }

-- Lookup-shaped consumers recover the exact acquiring-frame consequence.
acquire-owner : ∀ s → Owned s → ∀ w f → lookup w (O.acquiring (K.source s)) ≡ just f →
  lookup w (O.acquired (K.source s)) ≡ nothing × Owner w J.awaitAcquire (K.context s)
acquire-owner s inv w f found = acquiring inv w (cong is-just found)

-- The same consequence is available for every releasing frame.
release-owner : ∀ s → Owned s → ∀ w f → lookup w (O.releasing (K.source s)) ≡ just f →
  lookup w (O.released (K.source s)) ≡ nothing × Owner w J.awaitRelease (K.context s)
release-owner s inv w f found = releasing inv w (cong is-just found)

-- Region bookkeeping does not change any ownership witness or its handle.
note-owner : ∀ a c k w pc → Owner w pc k → Owner w pc (K.noteCore a c k)
note-owner a c k w pc (inj₁ foreign) = inj₁ foreign
note-owner a c k w pc (inj₂ (inj₁ j)) = inj₂ (inj₁ (job-await
  (JobAwait.job j) (JobAwait.frame j) (JobAwait.found j)
  (JobAwait.caller j) (JobAwait.waiting j) (JobAwait.running j)))
note-owner a c k w pc (inj₂ (inj₂ f)) = inj₂ (inj₂ (follow-await
  (FollowAwait.ref f) (FollowAwait.frame f) (FollowAwait.found f)
  (FollowAwait.caller f) (FollowAwait.waiting f)
  (FollowAwait.tid f) (FollowAwait.thread f) (FollowAwait.byPeer f)
  (FollowAwait.worker f) (FollowAwait.running f) (FollowAwait.observing f)))

-- Both clauses therefore survive a core action's noteRegions write.
note-inv : ∀ a d c k → Inv c k → Inv c (K.noteCore a d k)
note-inv a d c k inv = owned-frames
  (λ w present → let old = acquiring inv w present
    in proj₁ old , note-owner a d k w J.awaitAcquire (proj₂ old))
  (λ w present → let old = releasing inv w present
    in proj₁ old , note-owner a d k w J.awaitRelease (proj₂ old))
