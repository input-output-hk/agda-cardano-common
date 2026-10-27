{-# OPTIONS --guardedness #-}

-- Certificates for the exact captured CM traversal and its final result wait.
-- Observation of the supplied result table belongs to that finish step; this
-- is not a theorem about all historical handlers or arbitrary future oracles.
module ConnectionManagement.Properties.CMShutdown where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Rules.CMShutdown as Close

-- This predicate explicitly retains the identity of the observed oracle.
Observed : (WorkerId → Bool) → Close.State → Set
Observed available s = All (λ workerId → available workerId ≡ true) (Close.collected s)

and-left : ∀ a b → a ∧ b ≡ true → a ≡ true
and-left false b ()
and-left true b eq = refl
and-right : ∀ a b → a ∧ b ≡ true → b ≡ true
and-right false b ()
and-right true b eq = eq

-- Every repeated captured handle contributes an observation; no deduplication.
all-observed : ∀ available workers → Close.allAvailable available workers ≡ true →
  All (λ workerId → available workerId ≡ true) workers
all-observed available [] eq = []
all-observed available (w ∷ rest) eq =
  and-left (available w) (Close.allAvailable available rest) eq ∷
  all-observed available rest (and-right (available w) (Close.allAvailable available rest) eq)

-- Evidence locates the successful final wait and the exact oracle it read.
-- The oracle can differ at every preceding step and in any future adapter.
record FinalWait (after : Close.State) : Set where
  constructor finalWait
  field
    before : Close.State
    current : S.CMStore
    available : WorkerId → Bool
    waiting-before : Close.phase before ≡ Close.awaitResults
    actual-wait : Close.step current available Close.finishClose before ≡ just after
    same-collected : Close.collected after ≡ Close.collected before
    observed-at-wait : Observed available after
open FinalWait public

-- Reconstruct the concrete source computation from its inspected guards.
finish-computation : ∀ current available s → Close.phase s ≡ Close.awaitResults →
  Close.allAvailable available (Close.collected s) ≡ true →
  Close.step current available Close.finishClose s ≡ just (record s { phase = Close.closed })
finish-computation current available s phase ready rewrite phase | ready = refl

-- This local observation theorem does not require initial reachability or make
-- any claim that an arbitrary injected awaitResults state has drained its list.
finish-observation : ∀ current available s {s′} →
  Close.step current available Close.finishClose s ≡ just s′ → FinalWait s′
finish-observation current available s eq with Close.phase s in phase | Close.allAvailable available (Close.collected s) in ready
... | Close.awaitResults | true = case just-injective eq of λ { refl →
  finalWait s current available phase (trans (finish-computation current available s phase ready) eq) refl (all-observed available (Close.collected s) ready) }
finish-observation current available s eq | Close.awaitResults | false = case eq of λ ()
finish-observation current available s eq | Close.initial | ready = case eq of λ ()
finish-observation current available s eq | Close.reading | ready = case eq of λ ()
finish-observation current available s eq | Close.sendReady e w | ready = case eq of λ ()
finish-observation current available s eq | Close.awaitDelivery e w | ready = case eq of λ ()
finish-observation current available s eq | Close.closed | ready = case eq of λ ()

-- Only reachable waiting/closed states are certified drained. The remaining
-- phases may retain an outstanding send acknowledgment as well as unread refs.
Drained : Close.State → Set
Drained s with Close.phase s
... | Close.awaitResults = Close.remaining s ≡ []
... | Close.closed = Close.remaining s ≡ []
... | _ = ⊤
Valid : Close.State → Set
Valid s = Drained s × (Close.phase s ≡ Close.closed → FinalWait s)

-- The induction carries a stable metadata fact and a witness of the concrete
-- last wait. It never carries a global promise that an oracle remains true.
step-preserves : ∀ current available action s {s′} →
  Close.step current available action s ≡ just s′ → Valid s → Valid s′
step-preserves current available Close.captureSnapshot (Close.shutdownState Close.initial snap rest workers) eq valid with S.mapCell current
... | S.taken owner = case eq of λ ()
... | S.full map = case just-injective eq of λ { refl → tt , λ () }
step-preserves current available Close.readEntry (Close.shutdownState Close.reading snap [] workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq valid with lookup e (S.entries current)
... | nothing = case eq of λ ()
... | just state with Close.getConnThread state
...   | nothing = case just-injective eq of λ { refl → tt , λ () }
...   | just w = case just-injective eq of λ { refl → tt , λ () }
step-preserves current available Close.requestCancellation (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid =
  case just-injective eq of λ { refl → tt , λ () }
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid =
  case just-injective eq of λ { refl → tt , λ () }
step-preserves current available Close.finishTraversal (Close.shutdownState Close.reading snap [] workers) eq valid =
  case just-injective eq of λ { refl → refl , λ () }
step-preserves current available Close.finishTraversal (Close.shutdownState Close.reading snap (e ∷ rest) workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState Close.awaitResults snap rest workers) eq valid with Close.allAvailable available workers in ready
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → proj₁ valid , λ closed →
  finish-observation current available (Close.shutdownState Close.awaitResults snap rest workers)
    (trans (finish-computation current available (Close.shutdownState Close.awaitResults snap rest workers) refl ready) eq) }
step-preserves current available Close.captureSnapshot (Close.shutdownState Close.reading snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.captureSnapshot (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.captureSnapshot (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.captureSnapshot (Close.shutdownState Close.awaitResults snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.captureSnapshot (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState Close.initial snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState Close.awaitResults snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.readEntry (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.requestCancellation (Close.shutdownState Close.initial snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.requestCancellation (Close.shutdownState Close.reading snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.requestCancellation (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.requestCancellation (Close.shutdownState Close.awaitResults snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.requestCancellation (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState Close.initial snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState Close.reading snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState Close.awaitResults snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.acknowledgeDelivery (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishTraversal (Close.shutdownState Close.initial snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishTraversal (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishTraversal (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishTraversal (Close.shutdownState Close.awaitResults snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishTraversal (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState Close.initial snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState Close.reading snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState (Close.sendReady e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState (Close.awaitDelivery e w) snap rest workers) eq valid = case eq of λ ()
step-preserves current available Close.finishClose (Close.shutdownState Close.closed snap rest workers) eq valid = case eq of λ ()

initial-valid : Valid Close.initialState
initial-valid = tt , λ ()
exec-preserves : ∀ {s actions s′} → Close.Executes s actions s′ → Valid s → Valid s′
exec-preserves Close.done valid = valid
exec-preserves (Close.next {s = s} {a = a} {current = current} {available = available} eq path) valid =
  exec-preserves path (step-preserves current available a s eq valid)
from-initial-valid : ∀ {actions s} → Close.Executes Close.initialState actions s → Valid s
from-initial-valid path = exec-preserves path initial-valid

-- No finite traversal from the initializer closes with unread refs or an
-- outstanding throwTo acknowledgment, or without a witnessed final all-result
-- wait. This certifies only its collected handles at that wait's oracle.
closed-from-initial : ∀ {actions s} → Close.Executes Close.initialState actions s →
  Close.phase s ≡ Close.closed → Close.remaining s ≡ [] × FinalWait s
closed-from-initial {s = s} path closed with s | closed | from-initial-valid path
... | Close.shutdownState Close.closed snap rest workers | refl | drained , witnessed = drained , witnessed refl
