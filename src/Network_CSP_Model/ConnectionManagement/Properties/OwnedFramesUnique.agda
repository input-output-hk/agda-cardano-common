{-# OPTIONS --guardedness #-}

-- Reachable uniqueness of all four caller tables at the shared K boundary.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesUnique
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import ConnectionManagement.Properties.OutboundKeys using (Unique; unique-tables; uniqueSame; effect-unique)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.SourceKeysShared as SharedKeys
import ConnectionManagement.Properties.OwnedFramesUniquePeers as PeerFacts
import ConnectionManagement.PeerSupervision as Supervision
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module Keys = SharedKeys isBearerClosed isIOManagerError
  module Peers = PeerFacts isIOManagerError
  module PS = Supervision isIOManagerError

-- The accepted initialization profile has empty caller and result tables.
initial-unique : ∀ c g {s} → K.initial (O.initial c) g ≡ just s → Unique (K.source s)
initial-unique c g initialized with E.initial (O.initial c) in server
... | nothing = case initialized of λ ()
... | just e = case just-injective initialized of λ { refl → subst Unique
  (sym (ExitFacts.initial-source isBearerClosed (O.initial c) server))
  (unique-tables [] [] [] []) }

-- Server writes transport uniqueness through their complete KeySame relation.
server-unique : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t → Unique (K.source s) → Unique (K.source t)
server-unique a s stepped = uniqueSame (proj₁ (Keys.server-keys a s stepped))

-- Core writes use the real raw-machine effect and its later key-preserving writes.
core-unique : ∀ a s {t} → K.step (K.coreStep a) s ≡ just t → Unique (K.source s) → Unique (K.source t)
core-unique a s stepped = effect-unique _ (proj₁ (Keys.core-keys a s stepped))

-- Peer reassembly writes the single source using the checked PS preservation.
peer-unique : ∀ a s {t} → K.step (K.peerStep a) s ≡ just t → Unique (K.source s) → Unique (K.source t)
peer-unique a s stepped u with K.peerOpen s ∧ K.peerAllowed a s
... | false = case stepped of λ ()
... | true with PS.step a (K.peers s) in peer
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → Peers.peer-unique a (K.peers s) peer u }

-- No K transition kind is omitted.
step-unique : ∀ a s {t} → K.step a s ≡ just t → Unique (K.source s) → Unique (K.source t)
step-unique (K.serverStep a) = server-unique a
step-unique (K.coreStep a) = core-unique a
step-unique (K.peerStep a) = peer-unique a

-- Induction on the existing execution relation preserves caller-table uniqueness.
exec-unique : ∀ {s as t} → K.Executes s as t → Unique (K.source s) → Unique (K.source t)
exec-unique K.done u = u
exec-unique (K.next {s = s} {a = a} stepped rest) u = exec-unique rest (step-unique a s stepped u)

-- Every initialized reachable K state has unique acquisition/release and result keys.
reachable-unique : ∀ c g {s as t} → K.initial (O.initial c) g ≡ just s → K.Executes s as t → Unique (K.source t)
reachable-unique c g initialized path = exec-unique path (initial-unique c g initialized)
