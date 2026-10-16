{-# OPTIONS --guardedness #-}

-- Consume the late mux-finished notification after IG has unregistered its key.
module ConnectionManagement.CSP.RegistryBatch where

open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch; erase)
open import ConnectionManagement.Properties.RegistryAttachment using (Attached)
open import ConnectionManagement.Properties.RegistryPublication using (Sound)
open import ConnectionManagement.Properties.RegistryCleanup using (registry-preserves)
import ConnectionManagement.Properties.OriginRegistry as Proof
open import ConnectionManagement.CSP.OriginRegistry using (Process; trace-intro)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryShutdown using (wrap; append-path)
import ConnectionManagement.CSP.RegistryReturn as Return
import ConnectionManagement.CSP.HandlerLifecycle as Life
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.CSP.Process as OpenProcess
import ConnectionManagement.CSP.Correspondence as OpenProof
open import ConnectionManagement.Scenarios.Admission using (child₀; key₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

initial : Open.Configuration
initial = Return.returnedState Life.doneCleanup
runtime : IG.Runtime
runtime = Open.inboundGovernor initial

-- Explicit snapshots bound elaboration; every transition is checked below.
withRuntime : IG.Runtime → Open.Configuration
withRuntime r = record initial { inboundGovernor = r }
sampled : IG.Runtime
sampled = record (IG.setPC (IG.armInactivity 12) runtime)
  { execution = record (IG.execution runtime) { lastTime = 12 } }
armed : IG.Runtime
armed = IG.allocateTimer (IG.awaitBatch 12 (ident (IG.nextTimer sampled))) sampled
withEmptyQueue : IG.Runtime → Open.Configuration
withEmptyQueue r = record (withRuntime r)
  { world = record (Open.world initial) { inboundInfo = [] } }
finished timed registered selected consumed ready : State
finished = wrap (withRuntime (IG.setPC IG.sampleTime runtime))
timed = wrap (withRuntime sampled)
registered = wrap (withRuntime armed)
selected = wrap (withEmptyQueue (IG.setPC (IG.readNext 12 (S.muxFinished key₀ ∷ [])) armed))
consumed = wrap (withEmptyQueue (IG.setPC (IG.readNext 12 []) armed))
ready = wrap (withEmptyQueue (IG.setPC IG.sampleTime armed))

batch : List Action
batch = map (λ a → dispatch (Open.igStep a))
  (IG.finishBatch ∷ IG.captureTime 12 ∷ IG.registerInactivity ∷
    IG.selectBatch ∷ IG.readEvent ∷ IG.finishBatch ∷ [])
batch-path : Executes (wrap initial) batch ready
batch-path = next {s₁ = finished} refl (next {s₁ = timed} refl
  (next {s₁ = registered} refl (next {s₁ = selected} refl
  (next {s₁ = consumed} refl (next refl done)))))
schedule : List Action
schedule = Return.schedule ++ batch
path : Executes (start F.start) schedule ready
path = append-path Return.path batch-path
accepted : traces (Process (start F.start)) (map label schedule)
accepted = trace-intro path
open import Semantics.Failures {E = OpenProcess.Channel} {I = ExtI OpenProcess.Channel}
  using () renaming (traces to open-traces)
projected : open-traces (OpenProcess.Process F.start) (map OpenProcess.label (map erase schedule))
projected = OpenProof.trace-intro (Proof.exec-projects path)
result : Attached child₀ (ident 0) (Sound.ticket (proj₁ Return.result)) duplex (machine ready)
result = registry-preserves batch-path (proj₂ Return.result)
step-count : length schedule ≡ 54
step-count = refl
