{-# OPTIONS --guardedness #-}

-- Conditional controls for typed-monitor source effects and FIFO consumption.
module ConnectionManagement.Negative.MuxMonitorEffects where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (noResponderMode; responderMode)
open import ConnectionManagement.Scenarios.Admission using (key₀)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Q = Kernel ℕ true
module N = Kernel ℕ false

mid : MuxId
mid = ident 0
err : ErrorId
err = errorId 7
ready : M.Mux
ready = M.muxState key₀ M.ready [] [] [] [] [] [] nothing M.returned M.noIGTracer
r : IG.Runtime
r = IG.setMux mid ready IG.initial
failed : IG.Runtime
failed = IG.setMux mid (record ready { status = M.failed err }) r
stopped : IG.Runtime
stopped = IG.setMux mid (record ready { status = M.stopped }) r
failure-before-tracer : IG.step noResponderMode (IG.recordMuxFailure mid err) r [] ≡ just (failed , [])
failure-before-tracer = refl
stopped-before-tracer : IG.step responderMode (IG.recordMuxStopped mid) r [] ≡ just (stopped , [])
stopped-before-tracer = refl
ready-cannot-trace-dead : IG.step noResponderMode (IG.traceMuxDead mid) r [] ≡ nothing
ready-cannot-trace-dead = refl
failure-traces-after-write : IG.step noResponderMode (IG.traceMuxDead mid) failed [] ≡ just (failed , [])
failure-traces-after-write = refl
stopped-traces-after-write : IG.step responderMode (IG.traceMuxDead mid) stopped [] ≡ just (stopped , [])
stopped-traces-after-write = refl
cannot-overwrite-failure : IG.step responderMode (IG.recordMuxStopped mid) failed [] ≡ nothing
cannot-overwrite-failure = refl

fifo : Q.State
fifo = record Q.initial { completions = 3 ∷ 4 ∷ [] }
consume-only-head : Q.step Q.consumeCompletion fifo ≡ just (record fifo { completions = 4 ∷ [] })
consume-only-head = refl
empty-refused : Q.step Q.consumeCompletion Q.initial ≡ nothing
empty-refused = refl
closing-refused : Q.step Q.consumeCompletion (record fifo { phase = Q.closing }) ≡ nothing
closing-refused = refl
without-queue-refused : N.step N.consumeCompletion (record N.initial { completions = 3 ∷ [] }) ≡ nothing
without-queue-refused = refl

-- Existing close certificates retain precisely their original assumptions.
import ConnectionManagement.Properties.JobPoolCloseKernel as Certificates
module C = Certificates ℕ true
consume-preserves-captured-obligations : C.Covered fifo →
  C.Covered (record fifo { completions = 4 ∷ [] })
consume-preserves-captured-obligations = C.step-preserves Q.consumeCompletion fifo consume-only-head
consume-preserves-empty-cursor : C.ClosedEmpty fifo →
  C.ClosedEmpty (record fifo { completions = 4 ∷ [] })
consume-preserves-empty-cursor = C.step-empty Q.consumeCompletion fifo consume-only-head

attached : M.Mux
attached = record ready { tracerAttachment = M.igTracer }
attachedReady attachedFailed attachedDead : IG.Runtime
attachedReady = IG.setMux mid attached IG.initial
attachedFailed = IG.setMux mid (record attached { status = M.failed err }) attachedReady
attachedDead = IG.setMux mid (record attached
  { status = M.failed err; callback = M.readActive M.muxStopped }) attachedFailed
attached-write-leaves-callback-returned : IG.step responderMode (IG.recordMuxFailure mid err)
  attachedReady [] ≡ just (attachedFailed , [])
attached-write-leaves-callback-returned = refl
attached-dead-reads-tracer-after-write : IG.step responderMode (IG.traceMuxDead mid)
  attachedFailed [] ≡ just (attachedDead , [])
attached-dead-reads-tracer-after-write = refl
blocked-callback-refuses-status-write : IG.step responderMode (IG.recordMuxFailure mid err)
  (IG.setMux mid (record attached { callback = M.readActive M.muxStopped }) attachedReady) [] ≡ nothing
blocked-callback-refuses-status-write = refl
