{-# OPTIONS --guardedness #-}

-- Valid references do not imply callback progress or bypass job-pool ordering.
module ConnectionManagement.Negative.HandlerIGMux where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.State using (clean)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
open import ConnectionManagement.CSP.IGRegistration using (mid)
open import ConnectionManagement.Scenarios.Admission using (child₀)
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

blocked expired notForked unpublished : Configuration
blocked = tracked L.monitoring Runtime.blocked
expired = tracked L.monitoring Runtime.expiredStart
notForked = tracked L.monitoring Runtime.statusRunning
unpublished = tracked L.monitoring Runtime.jobFinished
blocked-chain : TrackedChain child₀ blocked
blocked-chain = _ , refl , record
  { originalHandler = _; publishedHandle = _; negotiatedFlow = _
  ; handleValue = _; muxValue = _; handlerFound = refl; promiseFound = refl
  ; handleFound = refl; handleMux = refl; muxFound = refl; keyMatches = refl
  ; entryPresent = _ , refl; socketPresent = _ , refl }

queue-blocks-tracer : advance (igStep (IG.commitTracer mid)) blocked ≡ nothing
queue-blocks-tracer = refl
expired-idle-blocks-tracer : advance (igStep (IG.commitTracer mid)) expired ≡ nothing
expired-idle-blocks-tracer = refl
job-must-be-forked : advance (igStep (IG.finishProtocol mid 1 clean)) notForked ≡ nothing
job-must-be-forked = refl
result-must-be-published : advance (igStep (IG.monitorCompletion mid)) unpublished ≡ nothing
result-must-be-published = refl

no-partial-burst : ¬ traces (Process blocked) (map label (igStep (IG.commitTracer mid) ∷ []))
no-partial-burst = refused-extension {as = []} done queue-blocks-tracer
no-expired-start-trace : ¬ traces (Process expired) (map label (igStep (IG.commitTracer mid) ∷ []))
no-expired-start-trace = refused-extension {as = []} done expired-idle-blocks-tracer
no-unforked-job-trace : ¬ traces (Process notForked) (map label (igStep (IG.finishProtocol mid 1 clean) ∷ []))
no-unforked-job-trace = refused-extension {as = []} done job-must-be-forked
no-unpublished-result-trace : ¬ traces (Process unpublished) (map label (igStep (IG.monitorCompletion mid) ∷ []))
no-unpublished-result-trace = refused-extension {as = []} done result-must-be-published
