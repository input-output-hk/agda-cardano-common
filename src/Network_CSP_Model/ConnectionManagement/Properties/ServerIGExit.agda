{-# OPTIONS --guardedness #-}

-- Exact interrupted-frame observations and a cheap source-invariant lift.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerIGExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; map; _++_)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Function using (case_of_)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerAdmissionInvariants as Old
private
  module S = Server isBearerClosed
  module E = Exit isBearerClosed

-- This checks the WHOLE active frame, including its captures and pending sends.
Captured : E.Receipt → E.State → Set
Captured r s with E.interrupted r
... | nothing = Machine.inboundRelease (O.core (E.source s)) ≡ nothing × Machine.remoteCall (O.core (E.source s)) ≡ nothing
... | just (E.releaseCall f) = Machine.inboundRelease (O.core (E.source s)) ≡ just f × Machine.remoteCall (O.core (E.source s)) ≡ nothing
... | just (E.remoteCall f) = Machine.inboundRelease (O.core (E.source s)) ≡ nothing × Machine.remoteCall (O.core (E.source s)) ≡ just f
select-captures : ∀ at err s {r} → E.selectReceipt at err s ≡ just r → Captured r s
select-captures at err s eq with E.receptionOpen s
... | false = case eq of λ ()
... | true with Machine.inboundRelease (O.core (E.source s)) in released | Machine.remoteCall (O.core (E.source s)) in remote
...   | nothing | nothing with E.bodyReady at (IG.continuation (E.governor s))
...     | true = case just-injective eq of λ { refl → released , remote }
...     | false = case eq of λ ()
select-captures at err s eq | true | just f | nothing with E.inCM (IG.continuation (E.governor s)) | E.releaseReady at f s
... | true | true = case just-injective eq of λ { refl → released , remote }
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
select-captures at err s eq | true | nothing | just f with E.inCM (IG.continuation (E.governor s)) | E.remoteReady at f s
... | true | true = case just-injective eq of λ { refl → released , remote }
... | false | _ = case eq of λ ()
... | true | false = case eq of λ ()
select-captures at err s eq | true | just _ | just _ = case eq of λ ()

-- Receipt archives the actual frame and preserves committed shared state.
receive-observation : ∀ at err s {t} → E.step (E.receive at err) s ≡ just t →
  Σ E.Receipt (λ r → Captured r s × E.received (E.exit t) ≡ just r ×
    Machine.world (O.core (E.source t)) ≡ Machine.world (O.core (E.source s)) ×
    Machine.inboundRelease (O.core (E.source t)) ≡ nothing × Machine.remoteCall (O.core (E.source t)) ≡ nothing)
receive-observation at err s eq with E.selectReceipt at err s in selected
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → r , select-captures at err s selected , refl , refl , refl , refl }

-- IG receipt cannot supply an admission-worker completion or registry join.
receive-workers : ∀ at err s {t} → E.step (E.receive at err) s ≡ just t →
  S.workers (E.base t) ≡ S.workers (E.base s)
receive-workers at err s eq with E.selectReceipt at err s
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → refl }

-- The only source change is retirement of the two local call-cursor fields.
receive-source : ∀ at err s {t} → E.step (E.receive at err) s ≡ just t → E.source t ≡ E.clearPending (E.source s)
receive-source at err s eq with E.selectReceipt at err s
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → refl }

-- The initializer observes no pre-existing active call; its source is exact.
initial-source : ∀ c {s} → E.initial c ≡ just s → E.source s ≡ c
initial-source c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c in initialized
... | nothing | nothing | just server = case just-injective eq of λ { refl → Old.initial-source isBearerClosed c initialized }
... | just _ | _ | _ = case eq of λ ()
... | nothing | just _ | _ = case eq of λ ()
... | nothing | nothing | nothing = case eq of λ ()

module Lift (Valid : O.Configuration → Set)
  (base-preserves : ∀ a s {t} → S.step a s ≡ just t → Valid (S.source s) → Valid (S.source t))
  (clear-preserves : ∀ c → Valid c → Valid (E.clearPending c)) where
  enact-preserves : ∀ p s {t} → E.enact p s ≡ just t → Valid (E.source s) → Valid (E.source t)
  enact-preserves (E.delegate a e) s eq valid with S.step a (E.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just server = case just-injective eq of λ { refl → base-preserves a (E.base s) advanced valid }
  enact-preserves (E.local e) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (E.abandon r) s eq valid = case just-injective eq of λ { refl → clear-preserves (E.source s) valid }
  enact-preserves (E.finish e) s eq valid = case just-injective eq of λ { refl → valid }
  step-preserves : ∀ a s {t} → E.step a s ≡ just t → Valid (E.source s) → Valid (E.source t)
  step-preserves a s eq valid with E.choose a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-preserves p s eq valid
  exec-preserves : ∀ {s as t} → E.Executes s as t → Valid (E.source s) → Valid (E.source t)
  exec-preserves E.done valid = valid
  exec-preserves (E.next {s = s} {a = a} eq rest) valid = exec-preserves rest (step-preserves a s eq valid)
  from-initial : ∀ {c start as t} → E.initial c ≡ just start → E.Executes start as t → Valid c → Valid (E.source t)
  from-initial {c} initialized path valid = exec-preserves path (subst Valid (sym (initial-source c initialized)) valid)

-- Existing birth traces lift with explicit permission proofs, without replaying
-- their full operational terms. Metadata stays empty until the new receipt.
Live : S.Action → Set
Live a = (∀ server → E.runAllowed a (E.igExitState server E.emptyExit) ≡ true) ×
  E.delegateExit a E.emptyExit ≡ just E.emptyExit
lift-step : ∀ a server {next} → Live a → S.step a server ≡ just next →
  E.step (E.run a) (E.igExitState server E.emptyExit) ≡ just (E.igExitState next E.emptyExit)
lift-step a server (allowed , metadata) advanced rewrite allowed server | metadata | advanced = refl
lift : ∀ {s as t} → All.All Live as → S.Executes s as t →
  E.Executes (E.igExitState s E.emptyExit) (map E.run as) (E.igExitState t E.emptyExit)
lift All.[] S.done = E.done
lift ((allowed , metadata) All.∷ permissions) (S.next {s = s} {a = a} eq rest) =
  E.next (lift-step a s (allowed , metadata) eq) (lift permissions rest)
append : ∀ {s as t bs u} → E.Executes s as t → E.Executes t bs u → E.Executes s (as ++ bs) u
append E.done rest = rest
append (E.next eq path) rest = E.next eq (append path rest)
