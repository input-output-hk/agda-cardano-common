{-# OPTIONS --safe #-}

-- Wire-control abstraction of the request-pipelined BlockFetch client.
-- Payloads are intentionally erased: this checks agency and batch ordering.
module Cardano_network.Replay.BlockFetchClientSession where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using ([]; _∷_; List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
import Data.Product.Properties as Pair
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Relation.Nullary using (Dec; yes; no)
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)
open import Cardano_network.Replay.Common public using (Direction; Send; Recv)

-- Equality on wire directions.
dirEq : DecidableEquality Direction
dirEq Send Send = yes refl
dirEq Recv Recv = yes refl
dirEq Send Recv = no λ ()
dirEq Recv Send = no λ ()

-- All six wire message kinds; request and block contents are unobserved.
data Kind : Set where
  request startBatch noBlocks block batchDone clientDone : Kind

-- Finite message-kind equality.
kindEq : DecidableEquality Kind
kindEq request request = yes refl
kindEq startBatch startBatch = yes refl
kindEq noBlocks noBlocks = yes refl
kindEq block block = yes refl
kindEq batchDone batchDone = yes refl
kindEq clientDone clientDone = yes refl
kindEq request startBatch = no λ ()
kindEq request noBlocks = no λ ()
kindEq request block = no λ ()
kindEq request batchDone = no λ ()
kindEq request clientDone = no λ ()
kindEq startBatch request = no λ ()
kindEq startBatch noBlocks = no λ ()
kindEq startBatch block = no λ ()
kindEq startBatch batchDone = no λ ()
kindEq startBatch clientDone = no λ ()
kindEq noBlocks request = no λ ()
kindEq noBlocks startBatch = no λ ()
kindEq noBlocks block = no λ ()
kindEq noBlocks batchDone = no λ ()
kindEq noBlocks clientDone = no λ ()
kindEq block request = no λ ()
kindEq block startBatch = no λ ()
kindEq block noBlocks = no λ ()
kindEq block batchDone = no λ ()
kindEq block clientDone = no λ ()
kindEq batchDone request = no λ ()
kindEq batchDone startBatch = no λ ()
kindEq batchDone noBlocks = no λ ()
kindEq batchDone block = no λ ()
kindEq batchDone clientDone = no λ ()
kindEq clientDone request = no λ ()
kindEq clientDone startBatch = no λ ()
kindEq clientDone noBlocks = no λ ()
kindEq clientDone block = no λ ()
kindEq clientDone batchDone = no λ ()

-- Observations retain wire direction relative to the client.
E : Set
E = Direction × Kind

-- The phase concerns the oldest unanswered range.
data Phase : Set where
  waiting streaming : Phase

-- Outstanding responses are counted; hidden collection is existential.
data St : Set where
  openS : ℕ → Phase → St
  closed : St

-- Empty initial session.
initial : St
initial = openS 0 waiting

-- A visible protocol-control transition.
data Step (k : ℕ) : St → E → St → Set where
  issue : ∀ {n ph} → n < k → Step k (openS n ph) (Send , request) (openS (suc n) ph)
  start : ∀ {n} → Step k (openS (suc n) waiting) (Recv , startBatch) (openS (suc n) streaming)
  none : ∀ {n} → Step k (openS (suc n) waiting) (Recv , noBlocks) (openS n waiting)
  body : ∀ {n} → Step k (openS (suc n) streaming) (Recv , block) (openS (suc n) streaming)
  end : ∀ {n} → Step k (openS (suc n) streaming) (Recv , batchDone) (openS n waiting)
  close : Step k initial (Send , clientDone) closed

-- Enumerate the unique possible successor of one supplied observation.
after : ℕ → St → E → List St
after k (openS n ph) (Send , request) with n <? k
... | yes _ = openS (suc n) ph ∷ []
... | no _ = []
after k (openS 0 waiting) (Send , clientDone) = closed ∷ []
after k (openS (suc n) waiting) (Recv , startBatch) = openS (suc n) streaming ∷ []
after k (openS (suc n) waiting) (Recv , noBlocks) = openS n waiting ∷ []
after k (openS (suc n) streaming) (Recv , block) = openS (suc n) streaming ∷ []
after k (openS (suc n) streaming) (Recv , batchDone) = openS n waiting ∷ []
after _ _ _ = []

-- A singleton membership identifies its sole element.
only : ∀ {A : Set} {x y : A} → x ∈ (y ∷ []) → x ≡ y
only (here refl) = refl
only (there ())

-- Every enumerated successor has its protocol transition witness.
after-sound : ∀ {k s e t} → t ∈ after k s e → Step k s e t
after-sound {k} {openS n ph} {Send , request} m with n <? k
... | yes lt with refl ← only m = issue lt
... | no _ with () ← m
after-sound {s = openS zero waiting} {Send , clientDone} m with refl ← only m = close
after-sound {s = openS (suc n) waiting} {Recv , startBatch} m with refl ← only m = start
after-sound {s = openS (suc n) waiting} {Recv , noBlocks} m with refl ← only m = none
after-sound {s = openS (suc n) streaming} {Recv , block} m with refl ← only m = body
after-sound {s = openS (suc n) streaming} {Recv , batchDone} m with refl ← only m = end
after-sound {s = closed} {Send , request} ()
after-sound {s = closed} {Send , startBatch} ()
after-sound {s = closed} {Send , noBlocks} ()
after-sound {s = closed} {Send , block} ()
after-sound {s = closed} {Send , batchDone} ()
after-sound {s = closed} {Send , clientDone} ()
after-sound {s = closed} {Recv , request} ()
after-sound {s = closed} {Recv , startBatch} ()
after-sound {s = closed} {Recv , noBlocks} ()
after-sound {s = closed} {Recv , block} ()
after-sound {s = closed} {Recv , batchDone} ()
after-sound {s = closed} {Recv , clientDone} ()
after-sound {s = openS zero waiting} {Send , startBatch} ()
after-sound {s = openS zero waiting} {Send , noBlocks} ()
after-sound {s = openS zero waiting} {Send , block} ()
after-sound {s = openS zero waiting} {Send , batchDone} ()
after-sound {s = openS zero waiting} {Recv , request} ()
after-sound {s = openS zero waiting} {Recv , startBatch} ()
after-sound {s = openS zero waiting} {Recv , noBlocks} ()
after-sound {s = openS zero waiting} {Recv , block} ()
after-sound {s = openS zero waiting} {Recv , batchDone} ()
after-sound {s = openS zero waiting} {Recv , clientDone} ()
after-sound {s = openS zero streaming} {Send , startBatch} ()
after-sound {s = openS zero streaming} {Send , noBlocks} ()
after-sound {s = openS zero streaming} {Send , block} ()
after-sound {s = openS zero streaming} {Send , batchDone} ()
after-sound {s = openS zero streaming} {Send , clientDone} ()
after-sound {s = openS zero streaming} {Recv , request} ()
after-sound {s = openS zero streaming} {Recv , startBatch} ()
after-sound {s = openS zero streaming} {Recv , noBlocks} ()
after-sound {s = openS zero streaming} {Recv , block} ()
after-sound {s = openS zero streaming} {Recv , batchDone} ()
after-sound {s = openS zero streaming} {Recv , clientDone} ()
after-sound {s = openS (suc n) waiting} {Send , startBatch} ()
after-sound {s = openS (suc n) waiting} {Send , noBlocks} ()
after-sound {s = openS (suc n) waiting} {Send , block} ()
after-sound {s = openS (suc n) waiting} {Send , batchDone} ()
after-sound {s = openS (suc n) waiting} {Send , clientDone} ()
after-sound {s = openS (suc n) waiting} {Recv , request} ()
after-sound {s = openS (suc n) waiting} {Recv , block} ()
after-sound {s = openS (suc n) waiting} {Recv , batchDone} ()
after-sound {s = openS (suc n) waiting} {Recv , clientDone} ()
after-sound {s = openS (suc n) streaming} {Send , startBatch} ()
after-sound {s = openS (suc n) streaming} {Send , noBlocks} ()
after-sound {s = openS (suc n) streaming} {Send , block} ()
after-sound {s = openS (suc n) streaming} {Send , batchDone} ()
after-sound {s = openS (suc n) streaming} {Send , clientDone} ()
after-sound {s = openS (suc n) streaming} {Recv , request} ()
after-sound {s = openS (suc n) streaming} {Recv , startBatch} ()
after-sound {s = openS (suc n) streaming} {Recv , noBlocks} ()
after-sound {s = openS (suc n) streaming} {Recv , clientDone} ()

-- Every transition is enumerated; failed bound decisions contradict its guard.
after-complete : ∀ {k s e t} → Step k s e t → t ∈ after k s e
after-complete {k} (issue {n} lt) with n <? k
... | yes _ = here refl
... | no bad = Data.Empty.⊥-elim (bad lt)
after-complete start = here refl
after-complete none = here refl
after-complete body = here refl
after-complete end = here refl
after-complete close = here refl

-- The wire abstraction has no silent transitions.
module Spec (k : ℕ) where
  -- Finite sound and complete successor enumeration for certified replay.
  model : Replay 0ℓ St E
  model = record
    { _-[_]→_ = Step k ; _-τ→_ = λ _ _ → ⊥
    ; _≟E_ = Pair.≡-dec dirEq kindEq
    ; after = after k ; taus = λ _ → []
    ; after-sound = after-sound ; after-complete = after-complete
    ; taus-sound = λ () ; taus-complete = λ () }

  open Traces model public
  open Decider model public

  -- With no silent moves, every reachable state is τ-accessible.
  cert : ∀ s → τAccReach s
  cert s = τAccReach-all (λ _ → acc λ ()) s

  -- Decide every finite control trace from the empty pipeline.
  check : ∀ es → Dec (HasTrace initial es)
  check = hasTrace? (cert initial)
