{-# OPTIONS --safe #-}

-- TxSubmission2 control replay: sequential submitter and pipelined requester.
module Cardano_network.Replay.TxSubmission2Session where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
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

-- Retain blocking style and ID-reply emptiness; erase transaction contents.
data Kind : Set where
  init requestBlocking requestNonBlocking replyIdsEmpty replyIdsNonEmpty
    requestTxs replyTxs doneK : Kind

-- Decidable equality of the finite observable control shapes.
kindEq : DecidableEquality Kind
kindEq init init = yes refl
kindEq init requestBlocking = no λ ()
kindEq init requestNonBlocking = no λ ()
kindEq init replyIdsEmpty = no λ ()
kindEq init replyIdsNonEmpty = no λ ()
kindEq init requestTxs = no λ ()
kindEq init replyTxs = no λ ()
kindEq init doneK = no λ ()
kindEq requestBlocking init = no λ ()
kindEq requestBlocking requestBlocking = yes refl
kindEq requestBlocking requestNonBlocking = no λ ()
kindEq requestBlocking replyIdsEmpty = no λ ()
kindEq requestBlocking replyIdsNonEmpty = no λ ()
kindEq requestBlocking requestTxs = no λ ()
kindEq requestBlocking replyTxs = no λ ()
kindEq requestBlocking doneK = no λ ()
kindEq requestNonBlocking init = no λ ()
kindEq requestNonBlocking requestBlocking = no λ ()
kindEq requestNonBlocking requestNonBlocking = yes refl
kindEq requestNonBlocking replyIdsEmpty = no λ ()
kindEq requestNonBlocking replyIdsNonEmpty = no λ ()
kindEq requestNonBlocking requestTxs = no λ ()
kindEq requestNonBlocking replyTxs = no λ ()
kindEq requestNonBlocking doneK = no λ ()
kindEq replyIdsEmpty init = no λ ()
kindEq replyIdsEmpty requestBlocking = no λ ()
kindEq replyIdsEmpty requestNonBlocking = no λ ()
kindEq replyIdsEmpty replyIdsEmpty = yes refl
kindEq replyIdsEmpty replyIdsNonEmpty = no λ ()
kindEq replyIdsEmpty requestTxs = no λ ()
kindEq replyIdsEmpty replyTxs = no λ ()
kindEq replyIdsEmpty doneK = no λ ()
kindEq replyIdsNonEmpty init = no λ ()
kindEq replyIdsNonEmpty requestBlocking = no λ ()
kindEq replyIdsNonEmpty requestNonBlocking = no λ ()
kindEq replyIdsNonEmpty replyIdsEmpty = no λ ()
kindEq replyIdsNonEmpty replyIdsNonEmpty = yes refl
kindEq replyIdsNonEmpty requestTxs = no λ ()
kindEq replyIdsNonEmpty replyTxs = no λ ()
kindEq replyIdsNonEmpty doneK = no λ ()
kindEq requestTxs init = no λ ()
kindEq requestTxs requestBlocking = no λ ()
kindEq requestTxs requestNonBlocking = no λ ()
kindEq requestTxs replyIdsEmpty = no λ ()
kindEq requestTxs replyIdsNonEmpty = no λ ()
kindEq requestTxs requestTxs = yes refl
kindEq requestTxs replyTxs = no λ ()
kindEq requestTxs doneK = no λ ()
kindEq replyTxs init = no λ ()
kindEq replyTxs requestBlocking = no λ ()
kindEq replyTxs requestNonBlocking = no λ ()
kindEq replyTxs replyIdsEmpty = no λ ()
kindEq replyTxs replyIdsNonEmpty = no λ ()
kindEq replyTxs requestTxs = no λ ()
kindEq replyTxs replyTxs = yes refl
kindEq replyTxs doneK = no λ ()
kindEq doneK init = no λ ()
kindEq doneK requestBlocking = no λ ()
kindEq doneK requestNonBlocking = no λ ()
kindEq doneK replyIdsEmpty = no λ ()
kindEq doneK replyIdsNonEmpty = no λ ()
kindEq doneK requestTxs = no λ ()
kindEq doneK replyTxs = no λ ()
kindEq doneK doneK = yes refl

-- Directions are relative to the node whose session is being checked.
E : Set
E = Direction × Kind

-- FIFO entries distinguish the two response families.
data Reply : Set where
  ids txs : Reply

-- Blocking requests cannot coexist with an asynchronous request queue.
data St : Set where
  awaitingInit blocking closed : St
  pending : List Reply → St

-- Both roles start before the submitter's Init message.
initial : St
initial = awaitingInit

-- Add a pipelined operation only below the configurable message bound.
issue : ℕ → List Reply → Reply → Maybe St
issue k q r with length q <ᵇ k
... | true = just (pending (q ∷ʳ r))
... | false = nothing

-- Requester/server wire transitions; replies consume the oldest request.
nextServer : ℕ → St → E → Maybe St
nextServer k awaitingInit (Recv , init) = just (pending [])
nextServer k (pending []) (Send , requestBlocking) = just blocking
nextServer k (pending q) (Send , requestNonBlocking) = issue k q ids
nextServer k (pending q) (Send , requestTxs) = issue k q txs
nextServer k (pending (ids ∷ q)) (Recv , replyIdsEmpty) = just (pending q)
nextServer k (pending (ids ∷ q)) (Recv , replyIdsNonEmpty) = just (pending q)
nextServer k (pending (txs ∷ q)) (Recv , replyTxs) = just (pending q)
nextServer k blocking (Recv , replyIdsNonEmpty) = just (pending [])
nextServer k blocking (Recv , doneK) = just closed
nextServer _ _ _ = nothing

-- Reverse wire directions to describe the submitter's local view.
reverse : E → E
reverse (Send , m) = Recv , m
reverse (Recv , m) = Send , m

-- The submitter processes one request at a time; only the server uses k.
next : ℕ → Role → St → E → Maybe St
next k server s e = nextServer k s e
next k client s e = nextServer 1 s (reverse e)

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
