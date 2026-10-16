{-# OPTIONS --guardedness #-}

-- Shared CM/mux world with concurrent outbound callers. Old-machine proofs
-- retain their original scope; no preservation across new writes is assumed.
module ConnectionManagement.OutboundMachine where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.State as S
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.HandlerLifecycle as Life

record Configuration : Set where
  constructor configuration
  field core : Inbound.Configuration
        acquiring : A.Runtime
        releasing : R.Runtime
        acquired : Store WorkerId Cases.Result
        released : Store WorkerId R.Result
        randomGeneration : ℕ
open Configuration public
initial : Inbound.Configuration → Configuration
initial c = configuration c [] [] [] [] 0

data Action : Set where
  inbound : Inbound.Action → Action
  beginAcquire : WorkerId → A.Request → Action
  acquire : WorkerId → A.Action → Action
  beginRelease : WorkerId → ConnectionKey → Action
  release : WorkerId → R.Action → Action

-- Completed operations return separately from their last counter transaction.
advanceAcquire : WorkerId → A.Action → Configuration → Maybe Configuration
advanceAcquire w A.returnResult c with lookup w (acquiring c)
... | nothing = nothing
... | just f with A.pc f
...   | A.complete result = just (record c
  { acquiring = delete w (acquiring c); acquired = put w result (acquired c) })
...   | _ = nothing
advanceAcquire w action c with lookup w (acquiring c)
... | nothing = nothing
... | just f with A.step w (Inbound.responder (core c)) action f (Inbound.world (core c))
...   | nothing = nothing
...   | just (f′ , world′) = just (record c
  { core = Inbound.replaceWorld (core c) world′; acquiring = put w f′ (acquiring c)
  ; randomGeneration = generation action })
  where
  generation : A.Action → ℕ
  generation (A.select _) = suc (randomGeneration c)
  generation _ = randomGeneration c

-- Deliveries use the same opt-in lifecycle/masking profile as inbound release.
canDeliver : R.Action → Configuration → Data.Bool.Bool
canDeliver (R.cancellationDelivered w) c = Life.mayDeliver w
  (Inbound.handlerLifecycles (core c)) (Inbound.world (core c))
canDeliver _ c = true
noteDelivery : R.Action → Life.Runtime → Life.Runtime
noteDelivery (R.cancellationDelivered w) = Life.noteDelivery w
noteDelivery _ = λ rt → rt
advanceRelease : WorkerId → R.Action → Configuration → Maybe Configuration
advanceRelease w R.returnResult c with lookup w (releasing c)
... | nothing = nothing
... | just f with R.pc f
...   | R.complete result = just (record c
  { releasing = delete w (releasing c); released = put w result (released c) })
...   | _ = nothing
advanceRelease w action c with lookup w (releasing c) | canDeliver action c
... | just f | true with R.step (Inbound.promotionHardLimit (core c)) action f (Inbound.world (core c))
...   | nothing = nothing
...   | just (f′ , world′) = just (record c
  { core = record (Inbound.replaceWorld (core c) world′)
      { handlerLifecycles = noteDelivery action (Inbound.handlerLifecycles (core c)) }
  ; releasing = put w f′ (releasing c); randomGeneration = generation action })
  where
  generation : R.Action → ℕ
  generation (R.transactionPruning _) = suc (randomGeneration c)
  generation _ = randomGeneration c
advanceRelease w action c | _ | _ = nothing

advance : Action → Configuration → Maybe Configuration
advance (inbound action) c with Inbound.advance action (core c)
... | nothing = nothing
... | just c′ = just (record c { core = c′ })
advance (beginAcquire w req) c with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = just (record c
  { acquiring = put w (A.frame req A.selecting) (acquiring c); acquired = delete w (acquired c) })
... | _ | _ = nothing
advance (acquire w action) c = advanceAcquire w action c
advance (beginRelease w key) c with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = just (record c
  { releasing = put w (R.frame key R.transaction false) (releasing c); released = delete w (released c) })
... | _ | _ = nothing
advance (release w action) c = advanceRelease w action c

data Executes : Configuration → List Action → Configuration → Set where
  done : ∀ {c} → Executes c [] c
  next : ∀ {c c₁ c₂ a as} → advance a c ≡ just c₁ → Executes c₁ as c₂ → Executes c (a ∷ as) c₂
append : ∀ {c c₁ c₂ as bs} → Executes c as c₁ → Executes c₁ bs c₂ → Executes c (as ++ bs) c₂
append done right = right
append (next eq left) right = next eq (append left right)
