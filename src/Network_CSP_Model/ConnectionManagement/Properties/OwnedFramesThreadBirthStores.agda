{-# OPTIONS --guardedness #-}

-- Fresh thread insertion preserves earlier byPeer/byWorker observations.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesThreadBirthStores
  (isIOManagerError : ErrorId → Bool) where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.PeerSupervision as Supervision
private module PS = Supervision isIOManagerError

-- An absent worker differs from every looked-up historical thread's worker.
worker-absent : ∀ w rows tid t → PS.byWorker w rows ≡ nothing → lookup tid rows ≡ just t → PS.worker t ≢ w
worker-absent w [] tid t absent ()
worker-absent w ((uid , u) ∷ rows) tid t absent saved with w ≟ PS.worker u
... | yes same = case absent of λ ()
... | no apart with tid ≟ uid
...   | yes same = case just-injective saved of λ { refl → λ eq → apart (sym eq) }
...   | no other = worker-absent w rows tid t absent saved

-- Absence of a peer has the analogous structural consequence on all rows.
peer-absent : ∀ ref rows tid t → PS.byPeer ref rows ≡ nothing → lookup tid rows ≡ just t → PS.peerRef t ≢ ref
peer-absent ref [] tid t absent ()
peer-absent ref ((uid , u) ∷ rows) tid t absent saved with ref ≟ PS.peerRef u
... | yes same = case absent of λ ()
... | no apart with tid ≟ uid
...   | yes same = case just-injective saved of λ { refl → λ eq → apart (sym eq) }
...   | no other = peer-absent ref rows tid t absent saved

-- A different worker at the head preserves an absent-worker tail.
worker-cons-none : ∀ w tid t rows → w ≢ PS.worker t → PS.byWorker w rows ≡ nothing → PS.byWorker w ((tid , t) ∷ rows) ≡ nothing
worker-cons-none w tid t rows apart absent with w ≟ PS.worker t
... | yes same = ⊥-elim (apart same)
... | no other = absent

-- A fresh worker cannot change any other worker's absent observation.
worker-put-none : ∀ w rows tid next → w ≢ PS.worker next → PS.byWorker w rows ≡ nothing → PS.byWorker w (put tid next rows) ≡ nothing
worker-put-none w [] tid next apart absent = worker-cons-none w tid next [] apart refl
worker-put-none w ((uid , u) ∷ rows) tid next apart absent with w ≟ PS.worker u
... | yes same = case absent of λ ()
... | no other with tid ≟ uid
...   | yes same = worker-cons-none w tid next rows apart absent
...   | no different = worker-cons-none w uid u (put tid next rows) other (worker-put-none w rows tid next apart absent)

-- A peer-distinct head preserves the exact selected tail row.
peer-cons-skip : ∀ ref tid t rows selected old → ref ≢ PS.peerRef t → PS.byPeer ref rows ≡ just (selected , old) →
  PS.byPeer ref ((tid , t) ∷ rows) ≡ just (selected , old)
peer-cons-skip ref tid t rows selected old apart found with ref ≟ PS.peerRef t
... | yes same = ⊥-elim (apart same)
... | no other = found

-- Neither the selected handle nor its peer is overwritten by the fresh row.
peer-put-other : ∀ ref rows tid next selected old → PS.peerRef next ≢ ref → selected ≢ tid →
  PS.byPeer ref rows ≡ just (selected , old) → PS.byPeer ref (put tid next rows) ≡ just (selected , old)
peer-put-other ref [] tid next selected old peer apart ()
peer-put-other ref ((uid , u) ∷ rows) tid next selected old peer apart found with tid ≟ uid
... | yes refl with ref ≟ PS.peerRef u
...   | yes same = case just-injective found of λ { refl → ⊥-elim (apart refl) }
...   | no different = peer-cons-skip ref tid next rows selected old (λ eq → peer (sym eq)) found
peer-put-other ref ((uid , u) ∷ rows) tid next selected old peer apart found | no other with ref ≟ PS.peerRef u
... | yes same = found
... | no different = peer-put-other ref rows tid next selected old peer apart found
