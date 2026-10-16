{-# OPTIONS --guardedness #-}

-- Release returns and IG unregisters before the handler closes its pool.
module ConnectionManagement.CSP.RegistryReturn where

open import Data.List using (List; []; _∷_; _++_; map; drop; length)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch; erase)
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Properties.RegistryPublication using (Sound; publication)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; attachment; publication-attachment)
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryShutdown using
  (wrap; installed; prefix; prefix-path; prefix-supported; waiting; waiting-path; append-path)
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.Correspondence as OpenProof
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Replace only the caller/IG publication fields in explicit unwind snapshots.
-- Each resulting transition is checked below; this is not a commutation law.
returnedState : Open.Configuration → Open.Configuration
returnedState c = record c
  { inboundRelease = nothing
  ; inboundGovernor = record (Open.inboundGovernor c)
      { publishedState = IG.publishedState (Open.inboundGovernor Life.callerPublished)
      ; continuation = IG.continuation (Open.inboundGovernor Life.callerPublished)
      }
  }

caller : List Action
caller = dispatch (Open.releaseStep R.checkAssertion) ∷
  dispatch (Open.releaseStep R.returnToIG) ∷ dispatch (Open.igStep IG.commitDecision) ∷ []
caller-path : Executes (wrap Life.received) caller (wrap Life.callerPublished)
caller-path = next {s₁ = wrap Life.callerChecked} refl
  (next {s₁ = wrap Life.callerReturned} refl (next refl done))

suffix : List Action
suffix = map dispatch (drop 2 Life.unwindActions ++ Life.cleanupActions)
suffix-path : Executes (wrap Life.callerPublished) suffix (wrap (returnedState Life.doneCleanup))
suffix-path = next {s₁ = wrap (returnedState Life.joined)} refl
  (next {s₁ = wrap (returnedState Life.failed)} refl
  (next {s₁ = wrap (returnedState Life.sampled)} refl
  (next {s₁ = wrap (returnedState Life.traced)} refl
  (next {s₁ = wrap (returnedState Life.exited)} refl
  (next {s₁ = wrap (returnedState Life.cleanupEntered)} refl
  (next {s₁ = wrap (returnedState Life.mapTaken)} refl
  (next {s₁ = wrap (returnedState Life.selected)} refl
  (next {s₁ = wrap (returnedState Life.socketClosed)} refl
  (next {s₁ = wrap (returnedState Life.waiting)} refl
  (next {s₁ = wrap (returnedState Life.ready)} refl
  (next {s₁ = wrap (returnedState Life.finalized)} refl
  (next refl done))))))))))))

-- The caller interleaving is inside the same supported publication/attachment proof.
completion : List Action
completion = dispatch (Open.releaseStep (R.cancellationDelivered child₀)) ∷ (caller ++ suffix)
completion-path : Executes (wrap Life.attached) completion (wrap (returnedState Life.doneCleanup))
completion-path = next {s₁ = wrap Life.received} refl (append-path caller-path suffix-path)
result : Σ (Sound child₀ (ident 0) duplex installed (wrap E.published))
  (λ certificate → Attached child₀ (ident 0) (Sound.ticket certificate) duplex (returnedState Life.doneCleanup))
result = publication-attachment child₀ (ident 0) duplex Life.cancelError
  prefix-path prefix-supported refl waiting-path refl completion-path

schedule : List Action
schedule = prefix ++ (publication child₀ (ident 0) duplex ∷
  (waiting ++ (attachment child₀ Life.cancelError ∷ completion)))
path : Executes (start F.start) schedule (wrap (returnedState Life.doneCleanup))
path = append-path prefix-path (next {s₁ = wrap E.published} refl
  (append-path waiting-path (next {s₁ = wrap Life.attached} refl completion-path)))
accepted : traces (Process (start F.start)) (map label schedule)
accepted = trace-intro path
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
projected : open-traces (OpenProcess.Process F.start) (map OpenProcess.label (map erase schedule))
projected = OpenProof.trace-intro (Proof.exec-projects path)
step-count : length schedule ≡ 48
step-count = refl
