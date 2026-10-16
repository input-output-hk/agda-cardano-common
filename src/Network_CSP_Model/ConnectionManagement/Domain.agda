{-# OPTIONS --guardedness #-}

-- Standalone identities. Pin: network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
module ConnectionManagement.Domain where

open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Class.DecEq using (DecEq; _≟_)

-- The index prevents entry, worker, socket, and other identities from unifying.
data IdKind : Set where
  entry worker socket mux promise run timer job handle peerConnection : IdKind

record Id (kind : IdKind) : Set where
  constructor ident
  field serial : ℕ
open Id public

EntryId WorkerId SocketId MuxId PromiseId RunId TimerId JobId HandleId PeerConnectionId : Set
EntryId = Id entry
WorkerId = Id worker
SocketId = Id socket
MuxId = Id mux
PromiseId = Id promise
RunId = Id run
TimerId = Id timer
JobId = Id job
HandleId = Id handle
PeerConnectionId = Id peerConnection

instance
  DecEq-Id : ∀ {k} → DecEq (Id k)
  DecEq-Id ._≟_ (ident x) (ident y) with x Nat.≟ y
  ... | yes refl = yes refl
  ... | no neq = no (λ eq → neq (cong serial eq))

-- Addresses are abstract host numbers with explicit family and port.
data Family : Set where
  ipv4 ipv6 : Family

instance
  DecEq-Family : DecEq Family
  DecEq-Family ._≟_ ipv4 ipv4 = yes refl
  DecEq-Family ._≟_ ipv4 ipv6 = no (λ ())
  DecEq-Family ._≟_ ipv6 ipv4 = no (λ ())
  DecEq-Family ._≟_ ipv6 ipv6 = yes refl

record PeerAddr : Set where
  constructor addr
  field
    family : Family
    host port : ℕ
open PeerAddr public

instance
  DecEq-PeerAddr : DecEq PeerAddr
  DecEq-PeerAddr ._≟_ (addr f h p) (addr g i q) with f ≟ g
  ... | no neq = no (λ eq → neq (cong family eq))
  ... | yes refl with h Nat.≟ i
  ...   | no neq = no (λ eq → neq (cong host eq))
  ...   | yes refl with p Nat.≟ q
  ...     | no neq = no (λ eq → neq (cong port eq))
  ...     | yes refl = yes refl

record ConnectionKey : Set where
  constructor connection
  field local remote : PeerAddr
open ConnectionKey public

-- IG registration uses the complete local/remote tuple as its map key.
instance
  DecEq-ConnectionKey : DecEq ConnectionKey
  DecEq-ConnectionKey ._≟_ (connection l r) (connection l′ r′) with l ≟ l′
  ... | no neq = no (λ eq → neq (cong local eq))
  ... | yes refl with r ≟ r′
  ...   | no neq = no (λ eq → neq (cong remote eq))
  ...   | yes refl = yes refl

-- Unknown local addresses remain separate map keys, not wildcard matches.
data LocalKey : Set where
  unknownLocal : LocalKey
  knownLocal : PeerAddr → LocalKey

private
  known-injective : ∀ {a b} → knownLocal a ≡ knownLocal b → a ≡ b
  known-injective refl = refl

instance
  DecEq-LocalKey : DecEq LocalKey
  DecEq-LocalKey ._≟_ unknownLocal unknownLocal = yes refl
  DecEq-LocalKey ._≟_ unknownLocal (knownLocal _) = no (λ ())
  DecEq-LocalKey ._≟_ (knownLocal _) unknownLocal = no (λ ())
  DecEq-LocalKey ._≟_ (knownLocal a) (knownLocal b) with a ≟ b
  ... | yes refl = yes refl
  ... | no neq = no (λ eq → neq (known-injective eq))

-- Capability, origin, and current use are independent dimensions.
data Provenance : Set where
  inbound outbound : Provenance

data DataFlow : Set where
  unidirectional duplex : DataFlow

data TimeoutFlag : Set where
  ticking expired : TimeoutFlag

-- Abstract exception identity, rather than exception text or payload.
record ErrorId : Set where
  constructor errorId
  field errorNumber : ℕ
