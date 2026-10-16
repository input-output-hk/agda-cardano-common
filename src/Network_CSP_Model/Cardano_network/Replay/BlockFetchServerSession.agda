{-# OPTIONS --safe #-}

-- Sequential server observations, at protocol receive/send (not mux ingress).
module Cardano_network.Replay.BlockFetchServerSession where

open import Level using (0ℓ)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
import Data.Product.Properties as Pair
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (Dec)
open import Semantics.Replay
open import Semantics.Replay.Decide using (module Decider)
open import Cardano_network.Replay.BlockFetchClientSession public
  using (E; Kind; Direction; Send; Recv; request; startBatch; noBlocks;
         block; batchDone; clientDone; dirEq; kindEq)
open import Cardano_network.Replay.BlockFetchClientSession using (only)

-- One range is processed completely before the next request is consumed.
data St : Set where
  idle busy streaming closed : St

-- Legal server wire transitions, with direction relative to the server.
data Step : St → E → St → Set where
  receive : Step idle (Recv , request) busy
  start : Step busy (Send , startBatch) streaming
  none : Step busy (Send , noBlocks) idle
  body : Step streaming (Send , block) streaming
  end : Step streaming (Send , batchDone) idle
  close : Step idle (Recv , clientDone) closed

-- Finite successor enumeration for a supplied observation.
after : St → E → List St
after idle (Recv , request) = busy ∷ []
after busy (Send , startBatch) = streaming ∷ []
after busy (Send , noBlocks) = idle ∷ []
after streaming (Send , block) = streaming ∷ []
after streaming (Send , batchDone) = idle ∷ []
after idle (Recv , clientDone) = closed ∷ []
after _ _ = []

-- Every enumerated state has a protocol transition witness.
after-sound : ∀ {s e t} → t ∈ after s e → Step s e t
after-sound {s = idle} {Recv , request} p with refl ← only p = receive
after-sound {s = busy} {Send , startBatch} p with refl ← only p = start
after-sound {s = busy} {Send , noBlocks} p with refl ← only p = none
after-sound {s = streaming} {Send , block} p with refl ← only p = body
after-sound {s = streaming} {Send , batchDone} p with refl ← only p = end
after-sound {s = idle} {Recv , clientDone} p with refl ← only p = close
after-sound {s = idle} {Send , request} ()
after-sound {s = idle} {Send , startBatch} ()
after-sound {s = idle} {Send , noBlocks} ()
after-sound {s = idle} {Send , block} ()
after-sound {s = idle} {Send , batchDone} ()
after-sound {s = idle} {Send , clientDone} ()
after-sound {s = idle} {Recv , startBatch} ()
after-sound {s = idle} {Recv , noBlocks} ()
after-sound {s = idle} {Recv , block} ()
after-sound {s = idle} {Recv , batchDone} ()
after-sound {s = busy} {Send , request} ()
after-sound {s = busy} {Send , block} ()
after-sound {s = busy} {Send , batchDone} ()
after-sound {s = busy} {Send , clientDone} ()
after-sound {s = busy} {Recv , request} ()
after-sound {s = busy} {Recv , startBatch} ()
after-sound {s = busy} {Recv , noBlocks} ()
after-sound {s = busy} {Recv , block} ()
after-sound {s = busy} {Recv , batchDone} ()
after-sound {s = busy} {Recv , clientDone} ()
after-sound {s = streaming} {Send , request} ()
after-sound {s = streaming} {Send , startBatch} ()
after-sound {s = streaming} {Send , noBlocks} ()
after-sound {s = streaming} {Send , clientDone} ()
after-sound {s = streaming} {Recv , request} ()
after-sound {s = streaming} {Recv , startBatch} ()
after-sound {s = streaming} {Recv , noBlocks} ()
after-sound {s = streaming} {Recv , block} ()
after-sound {s = streaming} {Recv , batchDone} ()
after-sound {s = streaming} {Recv , clientDone} ()
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

-- Every legal server transition is enumerated.
after-complete : ∀ {s e t} → Step s e t → t ∈ after s e
after-complete receive = here refl
after-complete start = here refl
after-complete none = here refl
after-complete body = here refl
after-complete end = here refl
after-complete close = here refl

-- The sequential server has no hidden control transitions at wire level.
model : Replay 0ℓ St E
model = record
  { _-[_]→_ = Step ; _-τ→_ = λ _ _ → ⊥
  ; _≟E_ = Pair.≡-dec dirEq kindEq
  ; after = after ; taus = λ _ → []
  ; after-sound = after-sound ; after-complete = after-complete
  ; taus-sound = λ () ; taus-complete = λ () }

open Traces model public
open Decider model public

-- No silent successors exist at any reachable state.
cert : ∀ s → τAccReach s
cert s = τAccReach-all (λ _ → acc λ ()) s

-- Decide any finite server control trace, including unfinished prefixes.
check : ∀ es → Dec (HasTrace idle es)
check = hasTrace? (cert idle)
