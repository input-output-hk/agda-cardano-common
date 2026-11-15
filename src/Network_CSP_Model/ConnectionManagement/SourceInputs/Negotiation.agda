{-# OPTIONS --guardedness #-}

-- Source projection at network 2f1c154: Version.hs:129-157 and
-- NodeToNode.hs:250-325,536-540; consensus 2e44d98:551-578,2079-2100.
-- This is a selected singleton-V15 offer map, not a CBOR implementation.
module ConnectionManagement.SourceInputs.Negotiation where

open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain using (DataFlow; unidirectional; duplex)
open import ConnectionManagement.IGTypes using (Protocol; protocol; hot; established; onDemand; onDemandAny)
import ConnectionManagement.ProtocolContracts2 as C2

data Mode : Set where
  initiatorOnly initiatorAndResponder : Mode

-- Source min uses the declaration order InitiatorOnly < InitiatorAndResponder.
meet : Mode → Mode → Mode
meet initiatorAndResponder initiatorAndResponder = initiatorAndResponder
meet _ _ = initiatorOnly

record VersionData : Set where
  constructor versionData
  field magic : ℕ
        mode : Mode
        sharing query peras : Bool
open VersionData public

-- PeerSharing's semigroup and Peras min are both conjunction.
accept : VersionData → VersionData → Maybe VersionData
accept l r with magic l ≟ magic r
... | no _ = nothing
... | yes _ = just (versionData (magic l) (meet (mode l) (mode r))
  (sharing l ∧ sharing r) (query l ∨ query r) (peras l ∧ peras r))

flow : VersionData → DataFlow
flow d with mode d
... | initiatorOnly = unidirectional
... | initiatorAndResponder = duplex

-- Globally ordered encoding of the source temperature groups, including the
-- appended consensus Leios descriptors; filters retain source group order.
layout : List Protocol
layout = protocol 2 hot onDemand ∷ protocol 3 hot onDemand ∷
  protocol 4 hot onDemand ∷ protocol 8 established onDemandAny ∷
  protocol 18 hot onDemand ∷ protocol 19 hot onDemand ∷ []

-- Both participants offer only supported V15. Peras must be disabled before V16.
data Version : Set where
  v15 : Version
Offer : Set
Offer = Version × VersionData

negotiate : List Offer → List Offer → Maybe VersionData
negotiate ((v15 , l) ∷ []) ((v15 , r) ∷ []) with peras l | peras r
... | false | false = accept l r
... | _ | _ = nothing
negotiate _ _ = nothing

-- Project ONLY non-query negotiations with the selected disabled features.
-- Query/mismatch/unsupported-feature outcomes do not become successful handles.
project : Maybe VersionData → Maybe (List Protocol × DataFlow)
project nothing = nothing
project (just d) with sharing d | query d | peras d
... | false | false | false = just (layout , flow d)
... | _ | _ | _ = nothing

localData remoteOutboundData : VersionData
localData = versionData 42 initiatorAndResponder false false false
remoteOutboundData = versionData 42 initiatorOnly false false false
localOffer outboundOffer : List Offer
localOffer = (v15 , localData) ∷ []
outboundOffer = (v15 , remoteOutboundData) ∷ []

outbound-accepted : negotiate localOffer outboundOffer ≡ just remoteOutboundData
outbound-accepted = refl
inbound-accepted : negotiate localOffer localOffer ≡ just localData
inbound-accepted = refl
outbound-projection : project (negotiate localOffer outboundOffer) ≡ just (layout , unidirectional)
outbound-projection = refl
inbound-projection : project (negotiate localOffer localOffer) ≡ just (layout , duplex)
inbound-projection = refl
magic-mismatch : accept localData (versionData 43 initiatorOnly false false false) ≡ nothing
magic-mismatch = refl
query-not-success : project (accept localData (versionData 42 initiatorOnly false true false)) ≡ nothing
query-not-success = refl
no-common-version : negotiate localOffer [] ≡ nothing
no-common-version = refl
invalid-v15-peras : negotiate localOffer ((v15 , versionData 42 initiatorOnly false false true) ∷ []) ≡ nothing
invalid-v15-peras = refl

-- The mkHandlers argument is independent of the negotiated wire version.
data TxLogic : Set where
  logicV1 logicV2 : TxLogic
serverEndpoint : TxLogic → C2.Endpoint
serverEndpoint logicV1 = C2.txServerV1
serverEndpoint logicV2 = C2.txServerV2
configuredLogic : TxLogic
configuredLogic = logicV2
selected-v2 : serverEndpoint configuredLogic ≡ C2.txServerV2
selected-v2 = refl
