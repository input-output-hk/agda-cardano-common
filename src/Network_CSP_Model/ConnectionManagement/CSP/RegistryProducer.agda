{-# OPTIONS --guardedness #-}

-- Admission-derived synchronous failure, preserving startup notification order.
module ConnectionManagement.CSP.RegistryProducer where

open import Data.List using (List; []; _∷_; _++_; map; drop; take; length)
open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch; erase)
open import ConnectionManagement.Properties.RegistryPublication using (Sound; publication)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached; attachment; publication-attachment)
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryShutdown using
  (wrap; installed; prefix; prefix-path; prefix-supported; consumer; consumer-path;
   registration; registration-path; append-path)
import ConnectionManagement.CSP.IGRuntime as Run
import ConnectionManagement.CSP.RemoteState as Remote
import ConnectionManagement.CSP.HandlerOutcomes as Out
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.HandlerEstablishment as E
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.Correspondence as OpenProof
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

startup-path : Executes (wrap G.registered) (map dispatch Run.startActions) (wrap Run.jobRunning)
startup-path = next {s₁ = wrap Run.commandRead} refl (next {s₁ = wrap Run.callbackEntered} refl (next {s₁ = wrap Run.activeSampled} refl (next {s₁ = wrap Run.traceCommitted} refl (next {s₁ = wrap Run.statusRunning} refl (next refl done)))))
promotion-path : Executes (wrap Run.jobRunning)
  (map dispatch (Remote.batchActions ++ Remote.promotionActions)) (wrap Remote.hotPublished)
promotion-path = next {s₁ = wrap Remote.b₀} refl (next {s₁ = wrap Remote.b₁} refl (next {s₁ = wrap Remote.b₂} refl (next {s₁ = wrap Remote.b₃} refl (next {s₁ = wrap Remote.b₄} refl (next {s₁ = wrap Remote.entered} refl (next {s₁ = wrap Remote.written} refl (next {s₁ = wrap Remote.checked} refl (next {s₁ = wrap Remote.counted} refl (next {s₁ = wrap Remote.returned} refl (next {s₁ = wrap Remote.warmPublished} refl (next {s₁ = wrap Remote.hotRead} refl (next refl done))))))))))))
before : List Action
before = consumer ++ (registration ++ (map dispatch Run.startActions ++
  map dispatch (Remote.batchActions ++ Remote.promotionActions)))
before-path : Executes (wrap E.published) before (wrap Remote.hotPublished)
before-path = append-path consumer-path (append-path registration-path
  (append-path startup-path promotion-path))

-- Startup messages have actually been consumed by promotion-path. Rebase the
-- failure snapshots on that CM/IG state; all transitions below are rechecked.
rebase : Open.Configuration → Open.Configuration
rebase c = record c
  { world = record (Open.world c)
      { cm = S.cm (Open.world Remote.hotPublished)
      ; inboundInfo = drop 2 (S.inboundInfo (Open.world c)) }
  ; inboundGovernor = record (Open.inboundGovernor c)
      { publishedState = IG.publishedState (Open.inboundGovernor Remote.hotPublished)
      ; continuation = IG.continuation (Open.inboundGovernor Remote.hotPublished)
      ; nextTimer = IG.nextTimer (Open.inboundGovernor Remote.hotPublished)
      ; execution = record (IG.execution (Open.inboundGovernor c))
          { timers = IG.timers (IG.execution (Open.inboundGovernor Remote.hotPublished))
          ; lastTime = IG.lastTime (IG.execution (Open.inboundGovernor Remote.hotPublished)) } }
  }
failure : List Action
failure = map dispatch (take 8 (drop 1 Out.syncActions))
failure-path : Executes (wrap (rebase Out.s₀)) failure (wrap (rebase Out.s₈))
failure-path = next {s₁ = wrap (rebase Out.s₁)} refl (next {s₁ = wrap (rebase Out.s₂)} refl (next {s₁ = wrap (rebase Out.s₃)} refl (next {s₁ = wrap (rebase Out.s₄)} refl (next {s₁ = wrap (rebase Out.s₅)} refl (next {s₁ = wrap (rebase Out.s₆)} refl (next {s₁ = wrap (rebase Out.s₇)} refl (next refl done)))))))

failureState : Open.Configuration
failureState = rebase Out.s₈
runtime : IG.Runtime
runtime = Open.inboundGovernor failureState
sampled : IG.Runtime
sampled = record (IG.setPC (IG.armInactivity 12) runtime)
  { execution = record (IG.execution runtime) { lastTime = 12 } }
armed : IG.Runtime
armed = IG.allocateTimer (IG.awaitBatch 12 (ident (IG.nextTimer sampled))) sampled
snapshot : IG.Runtime → List S.IGEvent → State
snapshot r queue = wrap (record failureState
  { inboundGovernor = r; world = record (Open.world failureState) { inboundInfo = queue } })
notifications : List S.IGEvent
notifications = S.inboundInfo (Open.world failureState)
finished timed registered selected errorRead muxRead polled removed ready : State
finished = snapshot (IG.setPC IG.sampleTime runtime) notifications
timed = snapshot sampled notifications
registered = snapshot armed notifications
selected = snapshot (IG.setPC (IG.readNext 12 notifications) armed) []
errorRead = snapshot (IG.setPC (IG.readNext 12 (S.muxFinished key₀ ∷ [])) armed) []
muxRead = snapshot (IG.setPC (IG.waitStopped 12 [] key₀ G.mid (IG.publishedState armed)) armed) []
polled = snapshot (IG.setPC (IG.publishDecision 12 [] (IG.unregister key₀ (IG.publishedState armed))) armed) []
removedRuntime : IG.Runtime
removedRuntime = record (IG.setPC (IG.readNext 12 []) armed)
  { publishedState = IG.unregister key₀ (IG.publishedState armed) }
removed = snapshot removedRuntime []
ready = snapshot (IG.setPC IG.sampleTime removedRuntime) []
batch : List Action
batch = map (λ a → dispatch (Open.igStep a))
  (IG.finishBatch ∷ IG.captureTime 12 ∷ IG.registerInactivity ∷ IG.selectBatch ∷
   IG.readEvent ∷ IG.readEvent ∷ IG.pollStopped ∷ IG.commitDecision ∷ IG.finishBatch ∷ [])
batch-path : Executes (wrap failureState) batch ready
batch-path = next {s₁ = finished} refl (next {s₁ = timed} refl (next {s₁ = registered} refl (next {s₁ = selected} refl (next {s₁ = errorRead} refl (next {s₁ = muxRead} refl (next {s₁ = polled} refl (next {s₁ = removed} refl (next refl done))))))))
result : Σ (Sound child₀ (ident 0) duplex installed (wrap E.published))
  (λ certificate → Attached child₀ (ident 0) (Sound.ticket certificate) duplex (machine ready))
result = publication-attachment child₀ (ident 0) duplex Life.cancelError
  prefix-path prefix-supported refl before-path refl (append-path failure-path batch-path)
schedule : List Action
schedule = prefix ++ (publication child₀ (ident 0) duplex ∷
  (before ++ (attachment child₀ Life.cancelError ∷ (failure ++ batch))))
path : Executes (start F.start) schedule ready
path = append-path prefix-path (next {s₁ = wrap E.published} refl
  (append-path before-path (next {s₁ = wrap (rebase Out.s₀)} refl
    (append-path failure-path batch-path))))
accepted : traces (Process (start F.start)) (map label schedule)
accepted = trace-intro path
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
projected : open-traces (OpenProcess.Process F.start) (map OpenProcess.label (map erase schedule))
projected = OpenProof.trace-intro (Proof.exec-projects path)
step-count : length schedule ≡ 57
step-count = refl
