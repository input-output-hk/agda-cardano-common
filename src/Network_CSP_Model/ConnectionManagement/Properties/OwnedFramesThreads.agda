{-# OPTIONS --guardedness #-}

-- Store lenses for immutable monitor peer/worker identities. These isolate
-- byPeer/byWorker reasoning from the larger supervision transition tree.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesThreads
  (isIOManagerError : ErrorId → Bool) where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; apart-lookup; lookup-head)
import ConnectionManagement.PeerSupervision as Supervision
private module PS = Supervision isIOManagerError

-- The selected thread's captured peer is exactly the requested peer key.
byPeer-ref : ∀ ref rows tid t → PS.byPeer ref rows ≡ just (tid , t) → PS.peerRef t ≡ ref
byPeer-ref ref [] tid t ()
byPeer-ref ref ((uid , u) ∷ rows) tid t found with ref ≟ PS.peerRef u
... | yes same = case just-injective found of λ { refl → sym same }
... | no apart = byPeer-ref ref rows tid t found

-- Unique thread-table keys connect byPeer selection to the ordinary key lens.
byPeer-lookup : ∀ ref rows → UniqueKeys rows → ∀ tid t → PS.byPeer ref rows ≡ just (tid , t) → lookup tid rows ≡ just t
byPeer-lookup ref [] [] tid t ()
byPeer-lookup ref ((uid , u) ∷ rows) (apart ∷ unique) tid t found with ref ≟ PS.peerRef u
... | yes same = case just-injective found of λ { refl → lookup-head uid u rows }
... | no other with tid ≟ uid
...   | yes refl = ⊥-elim (case trans (sym (apart-lookup uid rows apart)) (byPeer-lookup ref rows unique uid t found) of λ ())
...   | no different = byPeer-lookup ref rows unique tid t found

-- Replacing the selected thread with the same captured peer selects its new row.
byPeer-put-same : ∀ ref rows tid old next → lookup tid rows ≡ just old → PS.peerRef next ≡ PS.peerRef old →
  PS.byPeer ref rows ≡ just (tid , old) → PS.byPeer ref (put tid next rows) ≡ just (tid , next)
byPeer-put-same ref [] tid old next () peer found
byPeer-put-same ref ((uid , u) ∷ rows) tid old next saved peer found with tid ≟ uid
... | yes refl with just-injective saved
...   | refl with ref ≟ PS.peerRef old
...     | yes same with ref ≟ PS.peerRef next
...       | yes equal = refl
...       | no apart = ⊥-elim (apart (trans same (sym peer)))
byPeer-put-same ref ((uid , u) ∷ rows) .uid .u next saved peer found | yes refl | refl | no apart =
  ⊥-elim (apart (sym (byPeer-ref ref rows uid u found)))
byPeer-put-same ref ((uid , u) ∷ rows) tid old next saved peer found | no different with ref ≟ PS.peerRef u
... | yes same = case just-injective found of λ { refl → ⊥-elim (different refl) }
... | no apart = byPeer-put-same ref rows tid old next saved peer found

-- A different selected thread survives replacement of an existing peer identity.
byPeer-put-other : ∀ ref rows tid old next selected t → lookup tid rows ≡ just old →
  PS.peerRef next ≡ PS.peerRef old → selected ≢ tid → PS.byPeer ref rows ≡ just (selected , t) →
  PS.byPeer ref (put tid next rows) ≡ just (selected , t)
byPeer-put-other ref [] tid old next selected t () peer apart found
byPeer-put-other ref ((uid , u) ∷ rows) tid old next selected t saved peer apart found with tid ≟ uid
... | yes refl with just-injective saved
...   | refl with ref ≟ PS.peerRef old
...     | yes same = case just-injective found of λ { refl → ⊥-elim (apart refl) }
...     | no other with ref ≟ PS.peerRef next
...       | yes same = ⊥-elim (other (trans same peer))
...       | no different = found
byPeer-put-other ref ((uid , u) ∷ rows) tid old next selected t saved peer apart found | no different with ref ≟ PS.peerRef u
... | yes same = found
... | no other = byPeer-put-other ref rows tid old next selected t saved peer apart found

-- Absence from byWorker survives an existing thread's immutable-worker update.
byWorker-put-none : ∀ w rows tid old next → lookup tid rows ≡ just old → PS.worker next ≡ PS.worker old →
  PS.byWorker w rows ≡ nothing → PS.byWorker w (put tid next rows) ≡ nothing
byWorker-put-none w [] tid old next () worker absent
byWorker-put-none w ((uid , u) ∷ rows) tid old next saved worker absent with tid ≟ uid
... | yes refl with just-injective saved
...   | refl with w ≟ PS.worker old
...     | yes same = case absent of λ ()
...     | no apart with w ≟ PS.worker next
...       | yes same = ⊥-elim (apart (trans same worker))
...       | no different = absent
byWorker-put-none w ((uid , u) ∷ rows) tid old next saved worker absent | no different with w ≟ PS.worker u
... | yes same = case absent of λ ()
... | no other = byWorker-put-none w rows tid old next saved worker absent
