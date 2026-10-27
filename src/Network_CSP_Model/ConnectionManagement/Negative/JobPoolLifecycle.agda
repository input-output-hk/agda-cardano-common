{-# OPTIONS --guardedness #-}

-- One selected WithQueue owner scope. Explicit child/close interleavings are
-- witnesses of this primitive, not CM cleanup or whole-node shutdown proofs.
module ConnectionManagement.Negative.JobPoolLifecycle where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (put; lookup)
import ConnectionManagement.Rules.JobPoolLifecycle as Lifecycle
import ConnectionManagement.Properties.JobPoolClose as CloseProof
module Pool = Lifecycle ℕ
module Close = CloseProof ℕ

j₀ j₁ j₂ : JobId
j₀ = ident 0
j₁ = ident 1
j₂ = ident 2

-- Only the selected child's historical handle changes in these snapshots.
at : JobId → Pool.ThreadPhase → Pool.State → Pool.State
at j phase c = record c { handles = put j phase (Pool.handles c) }

-- A child can return and publish before its masked parent registers it. Normal
-- deregistration waits for the parent and publication precedes deregistration.
n₁ n₂ n₃ n₄ n₅ n₆ n₇ n₈ n₉ n₁₀ : Pool.State
n₁ = record Pool.initial { handles = (j₀ , Pool.bodyRunning) ∷ []; parentFork = just j₀ }
n₂ = at j₀ (Pool.bodyReturned 7) n₁
n₃ = record (at j₀ (Pool.deregisterPending Pool.normalExit) n₂) { completions = 7 ∷ [] }
n₄ = record n₃ { registered = j₀ ∷ []; parentFork = nothing }
n₅ = record n₄ { phase = Pool.closing; snapshot = j₀ ∷ []; remaining = j₀ ∷ []; joined = [] }
n₆ = record n₅ { phase = Pool.cancelPending j₀ }
n₇ = record (at j₀ (Pool.deregistered Pool.normalExit) n₆) { registered = [] }
n₈ = at j₀ (Pool.resultAvailable Pool.normalExit) n₇
n₉ = record n₈ { phase = Pool.closing; remaining = []; joined = j₀ ∷ [] }
n₁₀ = record n₉ { phase = Pool.closedPool }
normal₁ : Pool.step (Pool.fork j₀) Pool.initial ≡ just n₁
normal₁ = refl
normal₂ : Pool.step (Pool.bodyReturnedWith j₀ 7) n₁ ≡ just n₂
normal₂ = refl
normal₃ : Pool.step (Pool.publishCompletion j₀) n₂ ≡ just n₃
normal₃ = refl
normal₄ : Pool.step Pool.register n₃ ≡ just n₄
normal₄ = refl
normal₅ : Pool.step (Pool.beginClose (j₀ ∷ [])) n₄ ≡ just n₅
normal₅ = refl
normal₆ : Pool.step Pool.requestCancel n₅ ≡ just n₆
normal₆ = refl
normal₇ : Pool.step (Pool.deregister j₀) n₆ ≡ just n₇
normal₇ = refl
normal₈ : Pool.step (Pool.publishAsyncResult j₀) n₇ ≡ just n₈
normal₈ = refl
normal₉ : Pool.step Pool.join n₈ ≡ just n₉
normal₉ = refl
normal₁₀ : Pool.step Pool.finishClose n₉ ≡ just n₁₀
normal₁₀ = refl
normalActions : List Pool.Action
normalActions = Pool.fork j₀ ∷ Pool.bodyReturnedWith j₀ 7 ∷ Pool.publishCompletion j₀ ∷ Pool.register ∷
  Pool.beginClose (j₀ ∷ []) ∷ Pool.requestCancel ∷ Pool.deregister j₀ ∷ Pool.publishAsyncResult j₀ ∷
  Pool.join ∷ Pool.finishClose ∷ []
normalPath : Pool.Executes Pool.initial normalActions n₁₀
normalPath = Pool.next normal₁ (Pool.next normal₂ (Pool.next normal₃ (Pool.next normal₄ (Pool.next normal₅ (Pool.next normal₆ (Pool.next normal₇ (Pool.next normal₈ (Pool.next normal₉ (Pool.next normal₁₀ (Pool.done))))))))))

-- Parent masking prevents owner close in the fork/registration gap; the child's
-- early exit cannot remove a registry entry that the parent has not inserted.
fork-gap-blocks-owner-close : Pool.step (Pool.beginClose []) n₃ ≡ nothing
fork-gap-blocks-owner-close = refl
fork-gap-blocks-second-owner-fork : Pool.step (Pool.fork j₁) n₁ ≡ nothing
fork-gap-blocks-second-owner-fork = refl
early-child-deregister-retries : Pool.step (Pool.deregister j₀) n₃ ≡ nothing
early-child-deregister-retries = refl
registeredBeforePublish : Pool.State
registeredBeforePublish = record n₂ { registered = j₀ ∷ []; parentFork = nothing }
parent-can-register-returned-child : Pool.step Pool.register n₂ ≡ just registeredBeforePublish
parent-can-register-returned-child = refl
normal-deregister-before-publication-refused : Pool.step (Pool.deregister j₀) registeredBeforePublish ≡ nothing
normal-deregister-before-publication-refused = refl

-- Masked post-return work finishes normally despite a pending cancel request.
-- It is not assigned a fictitious asynchronous exception or failed queue value.
queued-normal-does-not-accept-fake-cancel : Pool.step Pool.deliverCancel n₆ ≡ nothing
queued-normal-does-not-accept-fake-cancel = refl
deregistered-is-not-async-terminal : lookup j₀ (Pool.handles n₇) ≡ just (Pool.deregistered Pool.normalExit)
deregistered-is-not-async-terminal = refl
join-before-async-result-refused : Pool.step Pool.join n₇ ≡ nothing
join-before-async-result-refused = refl
terminal-before-join-does-not-finish-close : Pool.step Pool.finishClose n₈ ≡ nothing
terminal-before-join-does-not-finish-close = refl
queued-result-survives-close : Pool.completions n₁₀ ≡ 7 ∷ []
queued-result-survives-close = refl
queued-thread-still-exits-normally : lookup j₀ (Pool.handles n₁₀) ≡ just (Pool.resultAvailable Pool.normalExit)
queued-thread-still-exits-normally = refl

-- Two running children are registered in reverse order. The chosen source-map
-- traversal is an exact permutation, fixed once at beginClose.
c₁ c₂ c₃ c₄ c₅ c₆ c₇ c₈ c₉ c₁₀ c₁₁ c₁₂ c₁₃ c₁₄ c₁₅ c₁₆ c₁₇ c₁₈ : Pool.State
c₁ = n₁
c₂ = record c₁ { registered = j₀ ∷ []; parentFork = nothing }
c₃ = record (at j₁ Pool.bodyRunning c₂) { parentFork = just j₁ }
c₄ = record c₃ { registered = j₁ ∷ j₀ ∷ []; parentFork = nothing }
c₅ = record c₄ { phase = Pool.closing; snapshot = j₀ ∷ j₁ ∷ []; remaining = j₀ ∷ j₁ ∷ []; joined = [] }
c₆ = record c₅ { phase = Pool.cancelPending j₀ }
c₇ = record (at j₀ Pool.bodyUnwinding c₆) { phase = Pool.joinPending j₀ }
c₈ = at j₀ (Pool.deregisterPending Pool.cancelledExit) c₇
c₉ = record (at j₀ (Pool.deregistered Pool.cancelledExit) c₈) { registered = j₁ ∷ [] }
c₁₀ = at j₀ (Pool.resultAvailable Pool.cancelledExit) c₉
c₁₁ = record c₁₀ { phase = Pool.closing; remaining = j₁ ∷ []; joined = j₀ ∷ [] }
c₁₂ = record c₁₁ { phase = Pool.cancelPending j₁ }
c₁₃ = record (at j₁ Pool.bodyUnwinding c₁₂) { phase = Pool.joinPending j₁ }
c₁₄ = at j₁ (Pool.deregisterPending Pool.cancelledExit) c₁₃
c₁₅ = record (at j₁ (Pool.deregistered Pool.cancelledExit) c₁₄) { registered = [] }
c₁₆ = at j₁ (Pool.resultAvailable Pool.cancelledExit) c₁₅
c₁₇ = record c₁₆ { phase = Pool.closing; remaining = []; joined = j₀ ∷ j₁ ∷ [] }
c₁₈ = record c₁₇ { phase = Pool.closedPool }
cancel₁ : Pool.step (Pool.fork j₀) Pool.initial ≡ just c₁
cancel₁ = refl
cancel₂ : Pool.step (Pool.register) c₁ ≡ just c₂
cancel₂ = refl
cancel₃ : Pool.step (Pool.fork j₁) c₂ ≡ just c₃
cancel₃ = refl
cancel₄ : Pool.step (Pool.register) c₃ ≡ just c₄
cancel₄ = refl
cancel₅ : Pool.step (Pool.beginClose (j₀ ∷ j₁ ∷ [])) c₄ ≡ just c₅
cancel₅ = refl
cancel₆ : Pool.step (Pool.requestCancel) c₅ ≡ just c₆
cancel₆ = refl
cancel₇ : Pool.step (Pool.deliverCancel) c₆ ≡ just c₇
cancel₇ = refl
cancel₈ : Pool.step (Pool.bodyUnwound j₀) c₇ ≡ just c₈
cancel₈ = refl
cancel₉ : Pool.step (Pool.deregister j₀) c₈ ≡ just c₉
cancel₉ = refl
cancel₁₀ : Pool.step (Pool.publishAsyncResult j₀) c₉ ≡ just c₁₀
cancel₁₀ = refl
cancel₁₁ : Pool.step (Pool.join) c₁₀ ≡ just c₁₁
cancel₁₁ = refl
cancel₁₂ : Pool.step (Pool.requestCancel) c₁₁ ≡ just c₁₂
cancel₁₂ = refl
cancel₁₃ : Pool.step (Pool.deliverCancel) c₁₂ ≡ just c₁₃
cancel₁₃ = refl
cancel₁₄ : Pool.step (Pool.bodyUnwound j₁) c₁₃ ≡ just c₁₄
cancel₁₄ = refl
cancel₁₅ : Pool.step (Pool.deregister j₁) c₁₄ ≡ just c₁₅
cancel₁₅ = refl
cancel₁₆ : Pool.step (Pool.publishAsyncResult j₁) c₁₅ ≡ just c₁₆
cancel₁₆ = refl
cancel₁₇ : Pool.step (Pool.join) c₁₆ ≡ just c₁₇
cancel₁₇ = refl
cancel₁₈ : Pool.step (Pool.finishClose) c₁₇ ≡ just c₁₈
cancel₁₈ = refl
cancelActions : List Pool.Action
cancelActions = (Pool.fork j₀) ∷ (Pool.register) ∷ (Pool.fork j₁) ∷ (Pool.register) ∷ (Pool.beginClose (j₀ ∷ j₁ ∷ [])) ∷ (Pool.requestCancel) ∷ (Pool.deliverCancel) ∷ (Pool.bodyUnwound j₀) ∷ (Pool.deregister j₀) ∷ (Pool.publishAsyncResult j₀) ∷ (Pool.join) ∷ (Pool.requestCancel) ∷ (Pool.deliverCancel) ∷ (Pool.bodyUnwound j₁) ∷ (Pool.deregister j₁) ∷ (Pool.publishAsyncResult j₁) ∷ (Pool.join) ∷ (Pool.finishClose) ∷ []
cancelPath : Pool.Executes Pool.initial cancelActions c₁₈
cancelPath = Pool.next cancel₁ (Pool.next cancel₂ (Pool.next cancel₃ (Pool.next cancel₄ (Pool.next cancel₅ (Pool.next cancel₆ (Pool.next cancel₇ (Pool.next cancel₈ (Pool.next cancel₉ (Pool.next cancel₁₀ (Pool.next cancel₁₁ (Pool.next cancel₁₂ (Pool.next cancel₁₃ (Pool.next cancel₁₄ (Pool.next cancel₁₅ (Pool.next cancel₁₆ (Pool.next cancel₁₇ (Pool.next cancel₁₈ (Pool.done))))))))))))))))))

-- Partial, duplicate and extra snapshots are rejected, as is taking a second
-- snapshot or forking more owner jobs after close traversal has started.
partial-snapshot-refused : Pool.step (Pool.beginClose (j₀ ∷ [])) c₄ ≡ nothing
partial-snapshot-refused = refl
duplicate-snapshot-refused : Pool.step (Pool.beginClose (j₀ ∷ j₀ ∷ [])) c₄ ≡ nothing
duplicate-snapshot-refused = refl
extra-snapshot-refused : Pool.step (Pool.beginClose (j₀ ∷ j₁ ∷ j₂ ∷ [])) c₄ ≡ nothing
extra-snapshot-refused = refl
exact-permutation-accepted : Pool.sameSnapshot (j₀ ∷ j₁ ∷ []) (j₁ ∷ j₀ ∷ []) ≡ true
exact-permutation-accepted = refl
second-snapshot-refused : Pool.step (Pool.beginClose (j₀ ∷ j₁ ∷ [])) c₅ ≡ nothing
second-snapshot-refused = refl
fork-during-close-refused : Pool.step (Pool.fork j₂) c₅ ≡ nothing
fork-during-close-refused = refl

-- mapM_ uninterruptibleCancel does not cancel all children in advance: its
-- current captured handle must produce an Async result and be joined first.
next-cancel-before-delivery-refused : Pool.step Pool.requestCancel c₆ ≡ nothing
next-cancel-before-delivery-refused = refl
next-cancel-during-first-join-refused : Pool.step Pool.requestCancel c₇ ≡ nothing
next-cancel-during-first-join-refused = refl
next-cancel-before-head-join-refused : Pool.step Pool.requestCancel c₁₀ ≡ nothing
next-cancel-before-head-join-refused = refl
cancelled-deregister-still-needs-async-result : Pool.step Pool.join c₉ ≡ nothing
cancelled-deregister-still-needs-async-result = refl
first-job-absent-from-registry : Pool.member j₀ (Pool.registered c₁₀) ≡ false
first-job-absent-from-registry = refl
first-captured-handle-still-joins : Pool.step Pool.join c₁₀ ≡ just c₁₁
first-captured-handle-still-joins = refl
close-with-second-unjoined-refused : Pool.step Pool.finishClose c₁₁ ≡ nothing
close-with-second-unjoined-refused = refl
cancelled-body-does-not-publish-fake-failure : Pool.step (Pool.publishCompletion j₀) c₈ ≡ nothing
cancelled-body-does-not-publish-fake-failure = refl
cancelled-close-has-no-job-results : Pool.completions c₁₈ ≡ []
cancelled-close-has-no-job-results = refl
all-snapshot-handles-joined : Pool.joined c₁₈ ≡ j₀ ∷ j₁ ∷ []
all-snapshot-handles-joined = refl

-- A historical child that deregistered before the snapshot is excluded even
-- while its Async result is unavailable. Empty scope close says nothing about it.
h₁ h₂ h₃ h₄ h₅ h₆ h₇ : Pool.State
h₁ = record Pool.initial { handles = (j₂ , Pool.bodyRunning) ∷ []; parentFork = just j₂ }
h₂ = record h₁ { registered = j₂ ∷ []; parentFork = nothing }
h₃ = at j₂ (Pool.bodyReturned 9) h₂
h₄ = record (at j₂ (Pool.deregisterPending Pool.normalExit) h₃) { completions = 9 ∷ [] }
h₅ = record (at j₂ (Pool.deregistered Pool.normalExit) h₄) { registered = [] }
h₆ = record h₅ { phase = Pool.closing; snapshot = []; remaining = []; joined = [] }
h₇ = record h₆ { phase = Pool.closedPool }
history₁ : Pool.step (Pool.fork j₂) Pool.initial ≡ just h₁
history₁ = refl
history₂ : Pool.step Pool.register h₁ ≡ just h₂
history₂ = refl
history₃ : Pool.step (Pool.bodyReturnedWith j₂ 9) h₂ ≡ just h₃
history₃ = refl
history₄ : Pool.step (Pool.publishCompletion j₂) h₃ ≡ just h₄
history₄ = refl
history₅ : Pool.step (Pool.deregister j₂) h₄ ≡ just h₅
history₅ = refl
history₆ : Pool.step (Pool.beginClose []) h₅ ≡ just h₆
history₆ = refl
history₇ : Pool.step Pool.finishClose h₆ ≡ just h₇
history₇ = refl
historyActions : List Pool.Action
historyActions = Pool.fork j₂ ∷ Pool.register ∷ Pool.bodyReturnedWith j₂ 9 ∷ Pool.publishCompletion j₂ ∷
  Pool.deregister j₂ ∷ Pool.beginClose [] ∷ Pool.finishClose ∷ []
historyPath : Pool.Executes Pool.initial historyActions h₇
historyPath = Pool.next history₁ (Pool.next history₂ (Pool.next history₃ (Pool.next history₄ (Pool.next history₅ (Pool.next history₆ (Pool.next history₇ (Pool.done)))))))
removed-job-not-recaptured : Pool.snapshot h₇ ≡ []
removed-job-not-recaptured = refl
historical-result-still-unavailable : ¬ Close.Terminal h₇ j₂
historical-result-still-unavailable (exit , ())
-- Closing this owner does not freeze a removed child's residual Async wrapper.
historical-result-can-appear-after-close : Pool.step (Pool.publishAsyncResult j₂) h₇ ≡
  just (at j₂ (Pool.resultAvailable Pool.normalExit) h₇)
historical-result-can-appear-after-close = refl
removed-job-cannot-be-added-to-snapshot : Pool.step (Pool.beginClose (j₂ ∷ [])) h₅ ≡ nothing
removed-job-cannot-be-added-to-snapshot = refl

-- Apply the generic close certificate to full executions, not just final-state
-- inspection. It certifies captured snapshot members only, not all handles.
normal-close-certified : ∀ j → j ∈ Pool.snapshot n₁₀ → Close.Terminal n₁₀ j
normal-close-certified = Close.from-initial normalPath refl
cancelled-close-certified : ∀ j → j ∈ Pool.snapshot c₁₈ → Close.Terminal c₁₈ j
cancelled-close-certified = Close.from-initial cancelPath refl
first-cancelled-handle-certified : Close.Terminal c₁₈ j₀
first-cancelled-handle-certified = cancelled-close-certified j₀ (here refl)
second-cancelled-handle-certified : Close.Terminal c₁₈ j₁
second-cancelled-handle-certified = cancelled-close-certified j₁ (there (here refl))
