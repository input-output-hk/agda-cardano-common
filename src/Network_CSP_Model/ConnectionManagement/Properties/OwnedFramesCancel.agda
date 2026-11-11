{-# OPTIONS --guardedness #-}

-- Local cancellation facts needed by the unwinding-frame invariant. They do
-- not assume that cleanup later succeeds or that a physical body has returned.
module ConnectionManagement.Properties.OwnedFramesCancel where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Properties.Stores using (UniqueKeys)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self)
open import ConnectionManagement.Properties.OutboundKeys using (KeySame; fields-same)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as I
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel

-- Detaching a call removes its caller's frame and retains the exact caller.
start-clears : ∀ w err context c {f d} → Cancel.start w err context c ≡ just (f , d) →
  UniqueKeys (O.acquiring c) → UniqueKeys (O.releasing c) →
  Cancel.caller f ≡ w × lookup w (O.acquiring d) ≡ nothing × lookup w (O.releasing d) ≡ nothing
start-clears w err Cancel.protectedCleanup c stepped au ru = case stepped of λ ()
start-clears w err Cancel.ordinary c stepped au ru with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → refl , delete-self w (O.acquiring c) au , released }
start-clears w err Cancel.ordinary c stepped au ru | nothing | just active =
  case just-injective stepped of λ { refl → refl , acquired , delete-self w (O.releasing c) ru }
start-clears w err Cancel.ordinary c stepped au ru | nothing | nothing =
  case just-injective stepped of λ { refl → refl , acquired , released }
start-clears w err Cancel.ordinary c stepped au ru | just _ | just _ = case stepped of λ ()
start-clears w err Cancel.forkedBeforeHandoff c stepped au ru with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → refl , delete-self w (O.acquiring c) au , released }
start-clears w err Cancel.forkedBeforeHandoff c stepped au ru | nothing | nothing = case stepped of λ ()
start-clears w err Cancel.forkedBeforeHandoff c stepped au ru | nothing | just _ = case stepped of λ ()
start-clears w err Cancel.forkedBeforeHandoff c stepped au ru | just _ | just _ = case stepped of λ ()
start-clears w err Cancel.interruptibleOpen c stepped au ru with lookup w (O.acquiring c) in acquired | lookup w (O.releasing c) in released
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active)
...   | nothing = case stepped of λ ()
...   | just chosen = case just-injective stepped of λ { refl → refl , delete-self w (O.acquiring c) au , released }
start-clears w err Cancel.interruptibleOpen c stepped au ru | nothing | nothing = case stepped of λ ()
start-clears w err Cancel.interruptibleOpen c stepped au ru | nothing | just _ = case stepped of λ ()
start-clears w err Cancel.interruptibleOpen c stepped au ru | just _ | just _ = case stepped of λ ()

-- Detached cleanup never changes any active caller key or either result table.
cleanup-keys : ∀ a f c {f′ d} → Cancel.step a f c ≡ just (f′ , d) → KeySame c d
cleanup-keys a f c stepped with Cancel.pc f
... | Cancel.finished _ = case stepped of λ ()
... | Cancel.cleaning active with A.step (Cancel.caller f) (I.responder (O.core c))
  (Cancel.acquireAction a) active (I.world (O.core c))
...   | nothing = case stepped of λ ()
...   | just (active′ , world′) = case just-injective stepped of λ { refl → fields-same c _ refl refl refl refl }

-- Cleanup updates the detached PC, preserving the original caller identity.
cleanup-caller : ∀ a f c {f′ d} → Cancel.step a f c ≡ just (f′ , d) → Cancel.caller f′ ≡ Cancel.caller f
cleanup-caller a f c stepped with Cancel.pc f
... | Cancel.finished _ = case stepped of λ ()
... | Cancel.cleaning active with A.step (Cancel.caller f) (I.responder (O.core c))
  (Cancel.acquireAction a) active (I.world (O.core c))
...   | nothing = case stepped of λ ()
...   | just (active′ , world′) = case just-injective stepped of λ { refl → refl }
