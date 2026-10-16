{-# OPTIONS --safe #-}

-- Wire-control replay: a bounded client and a sequential server.
module Cardano_network.Replay.ChainSyncSession where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as Pair
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)
open import Cardano_network.Replay.Common public
open import Cardano_network.Replay.BlockFetchClientSession using (dirEq)

-- Payloads are erased: the checker retains all eight control message kinds.
data Kind : Set where
  requestNext awaitReply rollForward rollBackward
    findIntersect intersectFound intersectNotFound doneK : Kind

-- Equality on the finite control alphabet.
kindEq : DecidableEquality Kind
kindEq requestNext requestNext = yes refl
kindEq requestNext awaitReply = no λ ()
kindEq requestNext rollForward = no λ ()
kindEq requestNext rollBackward = no λ ()
kindEq requestNext findIntersect = no λ ()
kindEq requestNext intersectFound = no λ ()
kindEq requestNext intersectNotFound = no λ ()
kindEq requestNext doneK = no λ ()
kindEq awaitReply requestNext = no λ ()
kindEq awaitReply awaitReply = yes refl
kindEq awaitReply rollForward = no λ ()
kindEq awaitReply rollBackward = no λ ()
kindEq awaitReply findIntersect = no λ ()
kindEq awaitReply intersectFound = no λ ()
kindEq awaitReply intersectNotFound = no λ ()
kindEq awaitReply doneK = no λ ()
kindEq rollForward requestNext = no λ ()
kindEq rollForward awaitReply = no λ ()
kindEq rollForward rollForward = yes refl
kindEq rollForward rollBackward = no λ ()
kindEq rollForward findIntersect = no λ ()
kindEq rollForward intersectFound = no λ ()
kindEq rollForward intersectNotFound = no λ ()
kindEq rollForward doneK = no λ ()
kindEq rollBackward requestNext = no λ ()
kindEq rollBackward awaitReply = no λ ()
kindEq rollBackward rollForward = no λ ()
kindEq rollBackward rollBackward = yes refl
kindEq rollBackward findIntersect = no λ ()
kindEq rollBackward intersectFound = no λ ()
kindEq rollBackward intersectNotFound = no λ ()
kindEq rollBackward doneK = no λ ()
kindEq findIntersect requestNext = no λ ()
kindEq findIntersect awaitReply = no λ ()
kindEq findIntersect rollForward = no λ ()
kindEq findIntersect rollBackward = no λ ()
kindEq findIntersect findIntersect = yes refl
kindEq findIntersect intersectFound = no λ ()
kindEq findIntersect intersectNotFound = no λ ()
kindEq findIntersect doneK = no λ ()
kindEq intersectFound requestNext = no λ ()
kindEq intersectFound awaitReply = no λ ()
kindEq intersectFound rollForward = no λ ()
kindEq intersectFound rollBackward = no λ ()
kindEq intersectFound findIntersect = no λ ()
kindEq intersectFound intersectFound = yes refl
kindEq intersectFound intersectNotFound = no λ ()
kindEq intersectFound doneK = no λ ()
kindEq intersectNotFound requestNext = no λ ()
kindEq intersectNotFound awaitReply = no λ ()
kindEq intersectNotFound rollForward = no λ ()
kindEq intersectNotFound rollBackward = no λ ()
kindEq intersectNotFound findIntersect = no λ ()
kindEq intersectNotFound intersectFound = no λ ()
kindEq intersectNotFound intersectNotFound = yes refl
kindEq intersectNotFound doneK = no λ ()
kindEq doneK requestNext = no λ ()
kindEq doneK awaitReply = no λ ()
kindEq doneK rollForward = no λ ()
kindEq doneK rollBackward = no λ ()
kindEq doneK findIntersect = no λ ()
kindEq doneK intersectFound = no λ ()
kindEq doneK intersectNotFound = no λ ()
kindEq doneK doneK = yes refl

-- Direction is always relative to the logging endpoint.
E : Set
E = Direction × Kind

-- A second AwaitReply for the same head request is illegal.
data Phase : Set where
  canAwait mustReply : Phase

-- Only RequestNext operations may coexist; intersection is exclusive.
data St : Set where
  pending : ℕ → Phase → St
  intersect closed : St

-- Initial state of every session generation.
initial : St
initial = pending 0 canAwait

-- Enforce a caller-selected bound on unanswered RequestNext messages.
issue : ℕ → ℕ → Phase → Maybe St
issue k n ph with n <ᵇ k
... | true = just (pending (suc n) ph)
... | false = nothing

-- Client wire transitions; AwaitReply keeps the head request outstanding.
nextClient : ℕ → St → E → Maybe St
nextClient k (pending n ph) (Send , requestNext) = issue k n ph
nextClient k (pending zero canAwait) (Send , findIntersect) = just intersect
nextClient k (pending zero canAwait) (Send , doneK) = just closed
nextClient k (pending (suc n) canAwait) (Recv , awaitReply) = just (pending (suc n) mustReply)
nextClient k (pending (suc n) ph) (Recv , rollForward) = just (pending n canAwait)
nextClient k (pending (suc n) ph) (Recv , rollBackward) = just (pending n canAwait)
nextClient k intersect (Recv , intersectFound) = just initial
nextClient k intersect (Recv , intersectNotFound) = just initial
nextClient _ _ _ = nothing

-- Reverse endpoint direction without changing message kind.
reverse : E → E
reverse (Send , m) = Recv , m
reverse (Recv , m) = Send , m

-- The server consumes one request at a time regardless of the client bound.
next : ℕ → Role → St → E → Maybe St
next k client s e = nextClient k s e
next k server s e = nextClient 1 s (reverse e)

-- Certified finite-state successor interface for each bound and endpoint role.
module Spec (k : ℕ) (role : Role) where
  -- A transition is precisely a successful control-state update.
  Step : St → E → St → Set
  Step s e t = next k role s e ≡ just t

  -- Enumerate the optional successor of the supplied observation.
  after : St → E → List St
  after s e with next k role s e
  ... | nothing = []
  ... | just t = t ∷ []

  -- Every enumerated successor carries a valid transition.
  after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
  after-sound {s} {e} m with next k role s e
  ... | nothing with () ← m
  ... | just t with m
  ...   | here refl = refl
  ...   | there ()

  -- Every successful control transition is enumerated.
  after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
  after-complete {s} {e} p with next k role s e
  ... | nothing with () ← p
  ... | just t with p
  ...   | refl = here refl

  -- At the wire abstraction all transitions are visible.
  model : Replay 0ℓ St E
  model = record
    { _-[_]→_ = Step ; _-τ→_ = λ _ _ → ⊥
    ; _≟E_ = Pair.≡-dec dirEq kindEq
    ; after = after ; taus = λ _ → []
    ; after-sound = after-sound ; after-complete = after-complete
    ; taus-sound = λ () ; taus-complete = λ () }

  open Traces model public
  open Decider model public

  -- No silent successors exist, including at reachable residual states.
  cert : ∀ s → τAccReach s
  cert s = τAccReach-all (λ _ → acc λ ()) s

  -- Decide membership, accepting finite unfinished prefixes.
  check : ∀ es → Dec (HasTrace initial es)
  check = hasTrace? (cert initial)
