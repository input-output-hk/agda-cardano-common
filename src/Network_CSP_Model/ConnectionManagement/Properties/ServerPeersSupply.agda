{-# OPTIONS --guardedness #-}

-- Closed supply/capture invariant for shared interleavings, including detached
-- governor cleanup frames. Each writer keeps its original proof premises.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeersSupply
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Function using (case_of_)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.Properties.PeerSupervisionSupply as PeerSupply
import ConnectionManagement.Properties.GovernorPoolSupply as GovernorSupply
import ConnectionManagement.Properties.ServerIGExitInvariants as ServerSupply
import ConnectionManagement.Properties.ServerIGExitEntries as Entries
import ConnectionManagement.Properties.ServerIGExit as ExitFacts
import ConnectionManagement.Properties.OutboundRuntimeSupply as Runtime
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError

Valid : K.State → Set
Valid s = PeerSupply.Valid isIOManagerError (K.peers s)
Bounded : K.State → Set
Bounded s = SupplyBounds (I.world (O.core (K.source s)))

-- Entry retention carries the detached premises through unrelated Server work.
server-preserves : ∀ a e {next} k → E.step a e ≡ just next →
  PeerSupply.Valid isIOManagerError (C.assemble (E.source e) k) →
  PeerSupply.Valid isIOManagerError (C.assemble (E.source next) k)
server-preserves a e k eq (runtime , detached) =
  ServerSupply.supply-step isBearerClosed a e eq runtime ,
  GovernorSupply.retained isIOManagerError (C.unwinding k) _ _
    (λ ref → Entries.Entry.step-preserves isBearerClosed ref a e eq) detached

-- Region bookkeeping does not alter the invariant's precise observer.
note-core : ∀ a c k →
  PeerSupply.Valid isIOManagerError (C.assemble c k) →
  PeerSupply.Valid isIOManagerError (C.assemble c (K.noteCore a c k))
note-core a c k valid = valid
step-preserves : ∀ a s {t} → K.step a s ≡ just t → Valid s → Valid t
step-preserves (K.serverStep a) s eq valid with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s) in advanced
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → server-preserves a (K.server s) (K.context s) advanced valid }
step-preserves (K.peerStep a) s eq valid with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl →
  PeerSupply.step-preserves isIOManagerError a (K.peers s) advanced valid }
step-preserves (K.coreStep a) s eq valid with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s) in advanced
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → note-core a (E.source e) (K.context s)
  (server-preserves (K.coreAction a) (K.server s) (K.context s) advanced valid) }
exec-preserves : ∀ {s as t} → K.Executes s as t → Valid s → Valid t
exec-preserves K.done valid = valid
exec-preserves (K.next {s = s} {a = a} eq rest) valid = exec-preserves rest (step-preserves a s eq valid)

-- Real initialization discharges both ordinary and detached capture stores.
initial-valid : ∀ c g {s} → K.initial (O.initial c) g ≡ just s →
  SupplyBounds (I.world c) → Valid s
initial-valid c g eq bounded with E.initial (O.initial c) in initialized
... | nothing = case eq of λ ()
... | just e = case just-injective eq of λ { refl → subst
  (λ raw → PeerSupply.Valid isIOManagerError (C.assemble raw (C.capture (PS.initial (O.initial c) g))))
  (sym (ExitFacts.initial-source isBearerClosed (O.initial c) initialized))
  (PeerSupply.initial-valid isIOManagerError c g bounded) }
from-initial-valid : ∀ {c g s as t} → K.initial (O.initial c) g ≡ just s →
  SupplyBounds (I.world c) → K.Executes s as t → Valid t
from-initial-valid {c} {g} initialized bounded path = exec-preserves path (initial-valid c g initialized bounded)
from-initial : ∀ {c g s as t} → K.initial (O.initial c) g ≡ just s →
  SupplyBounds (I.world c) → K.Executes s as t → Bounded t
from-initial initialized bounded path = proj₂ (proj₁ (from-initial-valid initialized bounded path))
