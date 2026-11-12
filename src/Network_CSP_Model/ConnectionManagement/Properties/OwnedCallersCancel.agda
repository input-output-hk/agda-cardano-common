{-# OPTIONS --guardedness #-}

-- Cancellation can delete caller frames but cannot introduce a foreign one.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersCancel
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup; delete)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.OwnedCallersBase as Base
open Base isBearerClosed isIOManagerError using
  (NoForeign; delete-empty; no-present; not-present)

-- Deleting either frame table preserves NoForeign without key uniqueness.
delete-acquire : ∀ c k q → NoForeign c k → NoForeign (record c { acquiring = delete q (O.acquiring c) }) k
delete-acquire c k q held w present foreign = no-present (record c { acquiring = delete q (O.acquiring c) }) w (delete-empty w q (O.acquiring c) (proj₁ old)) (proj₂ old) present
  where old = not-present c w (λ p → held w p foreign)

-- Release cancellation is the corresponding other-table deletion.
delete-release : ∀ c k q → NoForeign c k → NoForeign (record c { releasing = delete q (O.releasing c) }) k
delete-release c k q held w present foreign = no-present (record c { releasing = delete q (O.releasing c) }) w (proj₁ old) (delete-empty w q (O.releasing c) (proj₂ old)) present
  where old = not-present c w (λ p → held w p foreign)

-- Mirror the actual cancellation-start tree, retaining every refusal branch.
start-nf : ∀ w err context c {f d} → Cancel.start w err context c ≡ just (f , d) →
  ∀ k → NoForeign c k → NoForeign d k
start-nf w err Cancel.protectedCleanup c stepped k held = case stepped of λ ()
start-nf w err Cancel.ordinary c stepped k held with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → delete-acquire c k w held }
start-nf w err Cancel.ordinary c stepped k held | nothing | just active =
  case just-injective stepped of λ { refl → delete-release c k w held }
start-nf w err Cancel.ordinary c stepped k held | nothing | nothing =
  case just-injective stepped of λ { refl → held }
start-nf w err Cancel.ordinary c stepped k held | just _ | just _ = case stepped of λ ()
start-nf w err Cancel.forkedBeforeHandoff c stepped k held with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → delete-acquire c k w held }
start-nf w err Cancel.forkedBeforeHandoff c stepped k held | nothing | nothing = case stepped of λ ()
start-nf w err Cancel.forkedBeforeHandoff c stepped k held | nothing | just _ = case stepped of λ ()
start-nf w err Cancel.forkedBeforeHandoff c stepped k held | just _ | just _ = case stepped of λ ()
start-nf w err Cancel.interruptibleOpen c stepped k held with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → delete-acquire c k w held }
start-nf w err Cancel.interruptibleOpen c stepped k held | nothing | nothing = case stepped of λ ()
start-nf w err Cancel.interruptibleOpen c stepped k held | nothing | just _ = case stepped of λ ()
start-nf w err Cancel.interruptibleOpen c stepped k held | just _ | just _ = case stepped of λ ()

