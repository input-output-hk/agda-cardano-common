{-# OPTIONS --guardedness #-}

-- Allocation-first admission through IG release and completed CM cleanup.
-- This is one finite model schedule from the accepted-socket fixture.
module ConnectionManagement.CSP.RegistryShutdown where

open import Data.List using (List; []; _∷_; _++_; map; drop; length)
open import Data.Product using (Σ; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.OriginMonitor using (Ticket; ticket; target; awaitingPublication; published)
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch; erase)
open import ConnectionManagement.Properties.RegistryPublication using (Sound; publication)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; attachment; publication-attachment)
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.Correspondence as OpenProof
import ConnectionManagement.CSP.RegistryAdmission as Admission
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.InboundRelease as Release
import ConnectionManagement.CSP.HandlerLifecycle as Life
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Compose checked registry paths without normalizing a computed long replay.
append-path : ∀ {s xs middle ys end} → Executes s xs middle → Executes middle ys end → Executes s (xs ++ ys) end
append-path done right = right
append-path (next eq left) right = next eq (append-path left right)

tk : Ticket
tk = ticket G.mid (G.proto ∷ []) duplex
wrap : Open.Configuration → State
wrap c = registry c (entry (target child₀ (ident 0)) (published tk) ∷ [])
installed : State
installed = registry E.installed (entry (target child₀ (ident 0)) (awaitingPublication tk) ∷ [])
allocation : Action
allocation = allocate child₀ (ident 0) G.mid key₀ (G.proto ∷ []) duplex
prefix : List Action
prefix = map dispatch E.prefix ++ (allocation ∷ [])
prefix-path : Executes (start F.start) prefix installed
prefix-path = next {s₁ = Admission.s1} refl (next {s₁ = Admission.s2} refl
  (next {s₁ = Admission.s3} refl (next {s₁ = Admission.s4} refl
  (next {s₁ = Admission.s5} refl (next refl done)))))
prefix-supported : Proof.Supported prefix-path
prefix-supported = Proof.next tt (Proof.next tt (Proof.next tt (Proof.next tt
  (Proof.next tt (Proof.next E.forked-resources Proof.done)))))

-- Reuse explicit CM snapshots but defer attachment until release is requested.
-- Each transformed transition is checked below; no generic erasure is assumed.
untracked : Open.Configuration → Open.Configuration
untracked c = record c { handlerLifecycles = [] }
consumer : List Action
consumer = map dispatch E.suffix
consumer-path : Executes (wrap E.published) consumer (wrap G.installed)
consumer-path = next {s₁ = wrap (untracked E.mapPublished)} refl
  (next {s₁ = wrap (untracked E.waiting)} refl (next {s₁ = wrap (untracked E.readResult)} refl
  (next {s₁ = wrap (untracked E.committed)} refl (next {s₁ = wrap (untracked E.counted)} refl
  (next {s₁ = wrap (untracked E.enqueued)} refl (next refl done))))))

-- Allocation already happened before publication, so omit only that first event
-- from the older registration fixture; the six remaining steps are rechecked.
registration : List Action
registration = map dispatch (drop 1 G.register)
registration-path : Executes (wrap G.installed) registration (wrap G.registered)
registration-path = next {s₁ = wrap G.timeRead} refl (next {s₁ = wrap G.timerArmed} refl
  (next {s₁ = wrap G.drained} refl (next {s₁ = wrap G.eventRead} refl
  (next {s₁ = wrap G.prepared} refl (next refl done)))))
batch : List Action
batch = map dispatch Release.batchActions
batch-path : Executes (wrap G.registered) batch (wrap Release.b₆)
batch-path = next {s₁ = wrap Release.b₀} refl (next {s₁ = wrap Release.b₁} refl
  (next {s₁ = wrap Release.b₂} refl (next {s₁ = wrap Release.b₃} refl
  (next {s₁ = wrap Release.b₄} refl (next {s₁ = wrap Release.b₅} refl (next refl done))))))
request : List Action
request = map dispatch Life.requestActions
request-path : Executes (wrap Release.b₆) request (wrap Release.requested)
request-path = next {s₁ = wrap Release.written} refl (next {s₁ = wrap Release.counted} refl (next refl done))
waiting : List Action
waiting = consumer ++ (registration ++ (batch ++ request))
waiting-path : Executes (wrap E.published) waiting (wrap Release.requested)
waiting-path = append-path consumer-path (append-path registration-path (append-path batch-path request-path))

-- Recheck cancellation, unwind and finalization in the same registry execution.
cleanup : List Action
cleanup = map dispatch (drop 1 Life.unwindActions ++ Life.cleanupActions)
cleanup-path : Executes (wrap Life.attached) cleanup (wrap Life.doneCleanup)
cleanup-path = next {s₁ = wrap Life.received} refl (next {s₁ = wrap Life.joined} refl
  (next {s₁ = wrap Life.failed} refl (next {s₁ = wrap Life.sampled} refl
  (next {s₁ = wrap Life.traced} refl (next {s₁ = wrap Life.exited} refl
  (next {s₁ = wrap Life.cleanupEntered} refl (next {s₁ = wrap Life.mapTaken} refl
  (next {s₁ = wrap Life.selected} refl (next {s₁ = wrap Life.socketClosed} refl
  (next {s₁ = wrap Life.waiting} refl (next {s₁ = wrap Life.ready} refl
  (next {s₁ = wrap Life.finalized} refl (next refl done)))))))))))))

-- The final certificate is derived from allocation-first admission, publication
-- and successful attachment; no pre-seeded certificate is supplied.
result : Σ (Sound child₀ (ident 0) duplex installed (wrap E.published))
  (λ certificate → Attached child₀ (ident 0) (Sound.ticket certificate) duplex Life.doneCleanup)
result = publication-attachment child₀ (ident 0) duplex Life.cancelError
  prefix-path prefix-supported refl waiting-path refl cleanup-path

schedule : List Action
schedule = prefix ++ (publication child₀ (ident 0) duplex ∷
  (waiting ++ (attachment child₀ Life.cancelError ∷ cleanup)))
path : Executes (start F.start) schedule (wrap Life.doneCleanup)
path = append-path prefix-path (next {s₁ = wrap E.published} refl
  (append-path waiting-path (next {s₁ = wrap Life.attached} refl cleanup-path)))
accepted : traces (Process (start F.start)) (map label schedule)
accepted = trace-intro path
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
projected : open-traces (OpenProcess.Process F.start) (map OpenProcess.label (map erase schedule))
projected = OpenProof.trace-intro (Proof.exec-projects path)
step-count : length schedule ≡ 45
step-count = refl
