{-# OPTIONS --guardedness #-}

-- Registry shutdown from a certified lifecycle fixture, not an admission prefix.
module ConnectionManagement.Negative.RegistryCleanup where

open import Data.List using (List; []; _∷_; _++_; map; drop)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.OriginMonitor using (Ticket; ticket; target; published)
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; attachment)
open import ConnectionManagement.Properties.RegistryCleanup using (registry-preserves)
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.RegistryCleanup
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
import ConnectionManagement.Negative.RegistryAttachment

tk : Ticket
tk = ticket G.mid (G.proto ∷ []) duplex
wrap : Open.Configuration → State
wrap c = registry c (entry (target child₀ (ident 0)) (published tk) ∷ [])

-- This fixture's lookups are checked explicitly. No start-reachability claim is
-- made for its pre-seeded registry; the preservation theorem takes a certificate.
initial-certificate : Attached child₀ (ident 0) tk duplex Life.attached
initial-certificate = record
  { frame = L.frame G.mid Life.cancelError L.monitoring; frameFound = refl; captured = refl
  ; chain = record
    { originalHandler = _; publishedHandle = ident 0; negotiatedFlow = duplex
    ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
    ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
    ; entryPresent = _ , refl; socketPresent = _ , refl }
  ; origin = record
    { prepared = record
      { resources = record { original = _; found = refl; entryExists = _ , refl; socketExists = _ , refl }
      ; hd = _; mx = _; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl }
    ; descriptor = refl } }

schedule : List Action
schedule = map dispatch (drop 1 Life.unwindActions ++ Life.cleanupActions)
path : Executes (wrap Life.attached) schedule (wrap Life.doneCleanup)
path = next {s₁ = wrap Life.received} refl (next {s₁ = wrap Life.joined} refl
  (next {s₁ = wrap Life.failed} refl (next {s₁ = wrap Life.sampled} refl
  (next {s₁ = wrap Life.traced} refl (next {s₁ = wrap Life.exited} refl
  (next {s₁ = wrap Life.cleanupEntered} refl (next {s₁ = wrap Life.mapTaken} refl
  (next {s₁ = wrap Life.selected} refl (next {s₁ = wrap Life.socketClosed} refl
  (next {s₁ = wrap Life.waiting} refl (next {s₁ = wrap Life.ready} refl
  (next {s₁ = wrap Life.finalized} refl (next refl done)))))))))))))
final-certificate : Attached child₀ (ident 0) tk duplex Life.doneCleanup
final-certificate = registry-preserves path initial-certificate
accepted : traces (Process (wrap Life.attached)) (map label schedule)
accepted = trace-intro path

-- These facts hold simultaneously with the retained attachment certificate.
closed-socket : lookup (ident 0) (S.sockets (Open.world Life.doneCleanup)) ≡ just S.closed
closed-socket = refl
empty-map : S.mapCell (S.cm (Open.world Life.doneCleanup)) ≡ S.full []
empty-map = refl
terminated-entry : lookup (ident 0) (S.entries (S.cm (Open.world Life.doneCleanup))) ≡ just (S.terminated nothing)
terminated-entry = refl
failed-mux : Life.muxStatus Life.doneCleanup ≡ just (M.failed Life.cancelError)
failed-mux = refl
cleanup-complete : lookup child₀ (S.cleanups (Open.world Life.doneCleanup)) ≡ just (S.cleanupDone S.cleanupNormal)
cleanup-complete = refl
retained-finalizing-frame : lookup child₀ (Open.handlerLifecycles Life.doneCleanup) ≡ just (L.frame G.mid Life.cancelError L.finalizing)
retained-finalizing-frame = refl

-- Valid retained references do not enable another attachment or another exit.
reattach-refused : step (attachment child₀ Life.cancelError) (wrap Life.doneCleanup) ≡ nothing
reattach-refused = refl
reexit-refused : step (dispatch (Open.handlerExit child₀)) (wrap Life.doneCleanup) ≡ nothing
reexit-refused = refl

not-ready : ¬ (Life.muxStatus Life.doneCleanup ≡ just M.ready)
not-ready ()
not-handling : ¬ (lookup (ident 0) (S.sockets (Open.world Life.doneCleanup)) ≡ just (S.handling child₀))
not-handling ()
