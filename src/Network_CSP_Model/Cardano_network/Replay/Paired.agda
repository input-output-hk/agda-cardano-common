{-# OPTIONS --safe #-}

-- Two deterministic local peers connected by lossless directional FIFO queues.
open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Product using (_×_)
open import Data.Maybe using (Maybe)
open import Cardano_network.Replay.Common using (Role; Direction)
module Cardano_network.Replay.Paired
  (S M : Set) (messageEq : DecidableEquality M)
  (localNext : Role → S → Direction × M → Maybe S) where

open import Level using (0ℓ)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
import Data.Product.Properties
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst; trans)
open import Cardano_network.Replay.Common using (client; server; Send; Recv)
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)

-- Endpoint-local wire observation.
LocalEvent : Set
LocalEvent = Direction × M

-- A paired observation retains which endpoint emitted the row.
Event : Set
Event = Role × LocalEvent

-- Both local states and the sent-but-not-consumed messages in each direction.
record State : Set where
  constructor paired
  field
    clientState serverState : S
    clientToServer serverToClient : List M
open State public

-- A fresh capture starts before either peer acts and has no in-flight messages.
fresh : S → S → State
fresh c s = paired c s [] []

-- Each transition enforces both local legality and the communication queue.
data Step : State → Event → State → Set where
  clientSend : ∀ {c c′ s cs sc m} → localNext client c (Send , m) ≡ just c′ →
    Step (paired c s cs sc) (client , Send , m) (paired c′ s (cs ∷ʳ m) sc)
  clientRecv : ∀ {c c′ s cs sc m} → localNext client c (Recv , m) ≡ just c′ →
    Step (paired c s cs (m ∷ sc)) (client , Recv , m) (paired c′ s cs sc)
  serverSend : ∀ {c s s′ cs sc m} → localNext server s (Send , m) ≡ just s′ →
    Step (paired c s cs sc) (server , Send , m) (paired c s′ cs (sc ∷ʳ m))
  serverRecv : ∀ {c s s′ cs sc m} → localNext server s (Recv , m) ≡ just s′ →
    Step (paired c s (m ∷ cs) sc) (server , Recv , m) (paired c s′ cs sc)

-- A fixed paired event has at most one successor.
unique : ∀ {s e t u} → Step s e t → Step s e u → t ≡ u
unique (clientSend p) (clientSend q) with just-injective (trans (sym p) q)
... | refl = refl
unique (clientRecv p) (clientRecv q) with just-injective (trans (sym p) q)
... | refl = refl
unique (serverSend p) (serverSend q) with just-injective (trans (sym p) q)
... | refl = refl
unique (serverRecv p) (serverRecv q) with just-injective (trans (sym p) q)
... | refl = refl

-- Success or an exhaustive proof that the event has no successor.
data Outcome (s : State) (e : Event) : Set where
  enabled : ∀ t → Step s e t → Outcome s e
  disabled : (∀ {t} → ¬ Step s e t) → Outcome s e

-- A failed local update cannot witness a successful transition.
nothing≠just : ∀ {x : S} → nothing ≡ just x → ⊥
nothing≠just ()

-- Decide the exact paired transition, with no invented initial messages.
advance : ∀ s e → Outcome s e
advance (paired c s cs sc) (client , Send , m) with localNext client c (Send , m) in eq
... | just c′ = enabled _ (clientSend eq)
... | nothing = disabled λ { (clientSend p) → nothing≠just (trans (sym eq) p) }
advance (paired c s cs []) (client , Recv , m) = disabled λ ()
advance (paired c s cs (h ∷ sc)) (client , Recv , m) with messageEq h m
... | no neq = disabled λ { (clientRecv p) → neq refl }
... | yes refl with localNext client c (Recv , m) in eq
...   | just c′ = enabled _ (clientRecv eq)
...   | nothing = disabled λ { (clientRecv p) → nothing≠just (trans (sym eq) p) }
advance (paired c s cs sc) (server , Send , m) with localNext server s (Send , m) in eq
... | just s′ = enabled _ (serverSend eq)
... | nothing = disabled λ { (serverSend p) → nothing≠just (trans (sym eq) p) }
advance (paired c s [] sc) (server , Recv , m) = disabled λ ()
advance (paired c s (h ∷ cs) sc) (server , Recv , m) with messageEq h m
... | no neq = disabled λ { (serverRecv p) → neq refl }
... | yes refl with localNext server s (Recv , m) in eq
...   | just s′ = enabled _ (serverRecv eq)
...   | nothing = disabled λ { (serverRecv p) → nothing≠just (trans (sym eq) p) }

-- Endpoint equality keeps distinct peer observations distinct.
roleEq : DecidableEquality Role
roleEq client client = yes refl
roleEq server server = yes refl
roleEq client server = no λ ()
roleEq server client = no λ ()

-- Direction equality does not identify sends with receives.
dirEq : DecidableEquality Direction
dirEq Send Send = yes refl
dirEq Recv Recv = yes refl
dirEq Send Recv = no λ ()
dirEq Recv Send = no λ ()

-- Equality of endpoint-tagged wire events.
eventEq : DecidableEquality Event
eventEq = Data.Product.Properties.≡-dec roleEq
  (Data.Product.Properties.≡-dec dirEq messageEq)

-- Enumerate the unique successor if one exists.
after : State → Event → List State
after s e with advance s e
... | enabled t _ = t ∷ []
... | disabled _ = []

-- Every enumerated successor satisfies the independent transition relation.
after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
after-sound {s} {e} mem with advance s e
... | disabled _ with () ← mem
... | enabled t p with mem
...   | here refl = p
...   | there ()

-- Every legal transition appears in the successor enumeration.
after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
after-complete {s} {e} p with advance s e
... | disabled neg = ⊥-elim (neg p)
... | enabled t q with unique p q
...   | refl = here refl

-- Ordered paired replay has no silent steps at this wire abstraction.
model : Replay 0ℓ State Event
model = record
  { _-[_]→_ = Step ; _-τ→_ = λ _ _ → ⊥ ; _≟E_ = eventEq
  ; after = after ; taus = λ _ → []
  ; after-sound = after-sound ; after-complete = after-complete
  ; taus-sound = λ () ; taus-complete = λ () }

open Traces model public
open Decider model public

-- Empty internal branching gives reachable-state silent accessibility.
cert : ∀ s → τAccReach s
cert s = τAccReach-all (λ _ → acc λ ()) s

-- Check an already ordered pair trace, accepting unfinished finite prefixes.
checkOrdered : ∀ s es → Dec (HasTrace s es)
checkOrdered s = hasTrace? (cert s)

-- Project a merged trace to one endpoint without changing its row order.
project : Role → List Event → List LocalEvent
project r [] = []
project client ((client , e) ∷ es) = e ∷ project client es
project client ((server , e) ∷ es) = project client es
project server ((client , e) ∷ es) = project server es
project server ((server , e) ∷ es) = e ∷ project server es
