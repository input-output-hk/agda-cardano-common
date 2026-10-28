{-# OPTIONS --guardedness #-}

-- Conditional helper controls; adapter stages supply group/whole-pool ordering.
module ConnectionManagement.Negative.MuxGroupEffects where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (responderMode; noResponderMode; clean; errored)
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
module Q = Kernel ℕ true
module N = Kernel ℕ false

j : JobId
j = ident 8
openChild : Q.State
openChild = record Q.initial
  { handles = (j , Q.bodyRunning) ∷ []; registered = j ∷ []; completions = 7 ∷ [] }
external-interrupt-only-unwinds-body : Q.step (Q.interruptJob j) openChild ≡ just
  (record openChild { handles = (j , Q.bodyUnwinding) ∷ [] })
external-interrupt-only-unwinds-body = refl
no-interrupt-closing-pool : Q.step (Q.interruptJob j) (record openChild { phase = Q.closing }) ≡ nothing
no-interrupt-closing-pool = refl
no-interrupt-post-body-masked-gap : Q.step (Q.interruptJob j)
  (record openChild { handles = (j , Q.bodyReturned 3) ∷ [] }) ≡ nothing
no-interrupt-post-body-masked-gap = refl
no-interrupt-twice : Q.step (Q.interruptJob j)
  (record openChild { handles = (j , Q.bodyUnwinding) ∷ [] }) ≡ nothing
no-interrupt-twice = refl
queuefree-external-interrupt : N.step (N.interruptJob j)
  (record N.initial { handles = (j , N.bodyRunning) ∷ [] }) ≡ just
  (record N.initial { handles = (j , N.bodyUnwinding) ∷ [] })
queuefree-external-interrupt = refl

mid : MuxId
mid = ident 0
err : ErrorId
err = errorId 8
ready selected stopping stopped : M.Mux
ready = M.muxState key₀ M.ready [] (M.shutdown ∷ []) [] []
  ((1 , clean) ∷ (1 , errored err) ∷ []) [] nothing M.returned M.igTracer
selected = record ready { commands = [] }
stopping = record selected { status = M.stopping }
stopped = record stopping { status = M.stopped }
at : M.Mux → IG.Runtime
at m = IG.setMux mid m IG.initial
shutdown-selection-is-pop-only : IG.step noResponderMode (IG.takeShutdownCommand mid) (at ready) [] ≡ just (at selected , [])
shutdown-selection-is-pop-only = refl
stopping-status-is-separate : IG.step responderMode (IG.recordMuxStopping mid) (at selected) [] ≡ just (at stopping , [])
stopping-status-is-separate = refl
graceful-completion-has-no-Dead-callback : IG.step noResponderMode (IG.completeMuxStopping mid) (at stopping) [] ≡ just (at stopped , [])
graceful-completion-has-no-Dead-callback = refl
old-demux-helper-remains-ready-only : IG.step responderMode (IG.recordMuxStopped mid) (at stopping) [] ≡ nothing
old-demux-helper-remains-ready-only = refl
ready-is-not-graceful-completion : IG.step responderMode (IG.completeMuxStopping mid) (at selected) [] ≡ nothing
ready-is-not-graceful-completion = refl
pending-discard-is-not-error-publication : IG.step responderMode (IG.discardJobOccurrence mid 1) (at ready) [] ≡ just
  (at (record ready { finishedJobs = (1 , clean) ∷ [] }) , [])
pending-discard-is-not-error-publication = refl
discard-out-of-range-refused : IG.step responderMode (IG.discardJobOccurrence mid 2) (at ready) [] ≡ nothing
discard-out-of-range-refused = refl
async-failure-may-replace-stopping : IG.step noResponderMode (IG.recordAsyncMuxFailure mid err) (at stopping) [] ≡ just
  (at (record stopping { status = M.failed err }) , [])
async-failure-may-replace-stopping = refl
async-failure-may-replace-stopped : IG.step responderMode (IG.recordAsyncMuxFailure mid err) (at stopped) [] ≡ just
  (at (record stopped { status = M.failed err }) , [])
async-failure-may-replace-stopped = refl
async-write-cannot-cross-pending-callback : IG.step responderMode (IG.recordAsyncMuxFailure mid err)
  (at (record stopping { callback = M.readActive M.muxStopped })) [] ≡ nothing
async-write-cannot-cross-pending-callback = refl
legacy-result-has-priority-over-shutdown : IG.step responderMode (IG.takeShutdownCommand mid)
  (at (record ready { completions = M.jobResult M.responderJob 1 clean ∷ [] })) [] ≡ nothing
legacy-result-has-priority-over-shutdown = refl

-- External Mux.stop is independent of the monitor callback/status.
caller-stop-appends-during-held-stopping : IG.step noResponderMode (IG.enqueueMuxStop mid)
  (at (record stopping { callback = M.readActive M.muxStopped })) [] ≡ just
  (at (record stopping { commands = M.shutdown ∷ []; callback = M.readActive M.muxStopped }) , [])
caller-stop-appends-during-held-stopping = refl
caller-stop-keeps-existing-command : IG.step responderMode (IG.enqueueMuxStop mid) (at ready) [] ≡ just
  (at (record ready { commands = M.shutdown ∷ M.shutdown ∷ [] }) , [])
caller-stop-keeps-existing-command = refl
caller-stop-needs-existing-mux : IG.step responderMode (IG.enqueueMuxStop mid) IG.initial [] ≡ nothing
caller-stop-needs-existing-mux = refl
