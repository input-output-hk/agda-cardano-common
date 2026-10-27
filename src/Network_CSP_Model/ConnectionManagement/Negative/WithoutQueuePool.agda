{-# OPTIONS --guardedness #-}

-- WithoutQueue specialization prerequisite for SI3. These are initialized
-- primitive executions, not an integration of the outer PSA thread registry,
-- CM cleanup, transport scopes or whole-node supervision.
module ConnectionManagement.Negative.WithoutQueuePool where

open import Data.Bool using (false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
import ConnectionManagement.Rules.JobPoolKernel as Kernel
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseKernel
module Pool = Kernel ℕ false
module Close = CloseKernel ℕ false

j₀ : JobId
j₀ = ident 0

-- The child can finish before its masked parent registers its Async handle.
-- WithoutQueue discards the returned value and immediately tries deregister.
n1 n2 n3 n4 n5 n6 n7 n8 n9 : Pool.State
n1 = record Pool.initial
  { handles = (j₀ , Pool.bodyRunning) ∷ []; parentFork = just j₀ }
n2 = record n1 { handles = (j₀ , Pool.deregisterPending Pool.normalExit) ∷ [] }
n3 = record n2 { registered = j₀ ∷ []; parentFork = nothing }
n4 = record n3 { phase = Pool.closing; snapshot = j₀ ∷ []; remaining = j₀ ∷ [] }
n5 = record n4 { phase = Pool.cancelPending j₀ }
n6 = record n5 { handles = (j₀ , Pool.deregistered Pool.normalExit) ∷ []; registered = [] }
n7 = record n6 { handles = (j₀ , Pool.resultAvailable Pool.normalExit) ∷ [] }
n8 = record n7 { phase = Pool.closing; remaining = []; joined = j₀ ∷ [] }
n9 = record n8 { phase = Pool.closedPool }
normal-step1 : Pool.step (Pool.fork j₀) Pool.initial ≡ just n1
normal-step1 = refl
normal-step2 : Pool.step (Pool.bodyReturnedWith j₀ 42) n1 ≡ just n2
normal-step2 = refl
normal-step3 : Pool.step (Pool.register) n2 ≡ just n3
normal-step3 = refl
normal-step4 : Pool.step (Pool.beginClose (j₀ ∷ [])) n3 ≡ just n4
normal-step4 = refl
normal-step5 : Pool.step (Pool.requestCancel) n4 ≡ just n5
normal-step5 = refl
normal-step6 : Pool.step (Pool.deregister j₀) n5 ≡ just n6
normal-step6 = refl
normal-step7 : Pool.step (Pool.publishAsyncResult j₀) n6 ≡ just n7
normal-step7 = refl
normal-step8 : Pool.step (Pool.join) n7 ≡ just n8
normal-step8 = refl
normal-step9 : Pool.step (Pool.finishClose) n8 ≡ just n9
normal-step9 = refl
early-deregistration-retries : Pool.step (Pool.deregister j₀) n2 ≡ nothing
early-deregistration-retries = refl
masked-parent-gap-blocks-close : Pool.step (Pool.beginClose []) n2 ≡ nothing
masked-parent-gap-blocks-close = refl
returned-child-cannot-receive-cancel : Pool.step Pool.deliverCancel n5 ≡ nothing
returned-child-cannot-receive-cancel = refl
no-publication-operation : Pool.step (Pool.publishCompletion j₀) n2 ≡ nothing
no-publication-operation = refl
-- Conditional malformed snapshot: even a manually injected bodyReturned value
-- cannot turn on the disabled queue operation.
forged-publication-still-refused : Pool.step (Pool.publishCompletion j₀)
  (record n3 { handles = (j₀ , Pool.bodyReturned 42) ∷ [] }) ≡ nothing
forged-publication-still-refused = refl
normalActions : List Pool.Action
normalActions = (Pool.fork j₀) ∷ (Pool.bodyReturnedWith j₀ 42) ∷ Pool.register ∷ (Pool.beginClose (j₀ ∷ [])) ∷ Pool.requestCancel ∷ (Pool.deregister j₀) ∷ (Pool.publishAsyncResult j₀) ∷ Pool.join ∷ Pool.finishClose ∷ []
normal-path : Pool.Executes Pool.initial normalActions n9
normal-path = Pool.next normal-step1 (Pool.next normal-step2 (Pool.next normal-step3 (Pool.next normal-step4 (Pool.next normal-step5 (Pool.next normal-step6 (Pool.next normal-step7 (Pool.next normal-step8 (Pool.next normal-step9 (Pool.done)))))))))

-- A cancelled child has no returned body value and no completion publication.
c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 : Pool.State
c1 = n1
c2 = record c1 { registered = j₀ ∷ []; parentFork = nothing }
c3 = record c2 { phase = Pool.closing; snapshot = j₀ ∷ []; remaining = j₀ ∷ [] }
c4 = record c3 { phase = Pool.cancelPending j₀ }
c5 = record c4 { phase = Pool.joinPending j₀; handles = (j₀ , Pool.bodyUnwinding) ∷ [] }
c6 = record c5 { handles = (j₀ , Pool.deregisterPending Pool.cancelledExit) ∷ [] }
c7 = record c6 { handles = (j₀ , Pool.deregistered Pool.cancelledExit) ∷ []; registered = [] }
c8 = record c7 { handles = (j₀ , Pool.resultAvailable Pool.cancelledExit) ∷ [] }
c9 = record c8 { phase = Pool.closing; remaining = []; joined = j₀ ∷ [] }
c10 = record c9 { phase = Pool.closedPool }
cancelled-step1 : Pool.step (Pool.fork j₀) Pool.initial ≡ just c1
cancelled-step1 = refl
cancelled-step2 : Pool.step (Pool.register) c1 ≡ just c2
cancelled-step2 = refl
cancelled-step3 : Pool.step (Pool.beginClose (j₀ ∷ [])) c2 ≡ just c3
cancelled-step3 = refl
cancelled-step4 : Pool.step (Pool.requestCancel) c3 ≡ just c4
cancelled-step4 = refl
cancelled-step5 : Pool.step (Pool.deliverCancel) c4 ≡ just c5
cancelled-step5 = refl
cancelled-step6 : Pool.step (Pool.bodyUnwound j₀) c5 ≡ just c6
cancelled-step6 = refl
cancelled-step7 : Pool.step (Pool.deregister j₀) c6 ≡ just c7
cancelled-step7 = refl
cancelled-step8 : Pool.step (Pool.publishAsyncResult j₀) c7 ≡ just c8
cancelled-step8 = refl
cancelled-step9 : Pool.step (Pool.join) c8 ≡ just c9
cancelled-step9 = refl
cancelled-step10 : Pool.step (Pool.finishClose) c9 ≡ just c10
cancelled-step10 = refl
cancelledActions : List Pool.Action
cancelledActions = (Pool.fork j₀) ∷ Pool.register ∷ (Pool.beginClose (j₀ ∷ [])) ∷ Pool.requestCancel ∷ Pool.deliverCancel ∷ (Pool.bodyUnwound j₀) ∷ (Pool.deregister j₀) ∷ (Pool.publishAsyncResult j₀) ∷ Pool.join ∷ Pool.finishClose ∷ []
cancelled-path : Pool.Executes Pool.initial cancelledActions c10
cancelled-path = Pool.next cancelled-step1 (Pool.next cancelled-step2 (Pool.next cancelled-step3 (Pool.next cancelled-step4 (Pool.next cancelled-step5 (Pool.next cancelled-step6 (Pool.next cancelled-step7 (Pool.next cancelled-step8 (Pool.next cancelled-step9 (Pool.next cancelled-step10 (Pool.done))))))))))

-- Both actual executions retain an empty queue. Closing certifies only their
-- captured handle; it supplies no fairness or outer-scope cleanup theorem.
both-queues-empty : (Pool.completions n9 ≡ []) × (Pool.completions c10 ≡ [])
both-queues-empty = refl , refl
normal-terminal : ∀ j → j ∈ Pool.snapshot n9 → Close.Terminal n9 j
normal-terminal = Close.from-initial normal-path refl
cancelled-terminal : ∀ j → j ∈ Pool.snapshot c10 → Close.Terminal c10 j
cancelled-terminal = Close.from-initial cancelled-path refl
