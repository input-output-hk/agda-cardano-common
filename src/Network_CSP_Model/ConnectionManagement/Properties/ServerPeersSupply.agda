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

-- The protocol frontend adds cells/commands/physical pool metadata. Its caller
-- step is an actual PSA step; completion caches alter only peer result views.
open import ConnectionManagement.Domain using (HandleId)
open import Data.Nat using (ℕ)
module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open import Data.List using ([]; _∷_)
  open import Relation.Nullary using (yes; no)
  open import Class.DecEq using (_≟_)
  open import ConnectionManagement.Store using (lookup)
  open import ConnectionManagement.IGTypes using (number)
  import ConnectionManagement.Rules.PeerActions as Peer
  private
    module T = K.Protocols canInitiate

  ProtocolValid : T.Runtime → Set
  ProtocolValid s = Valid (T.base s)
  cache-preserves : ∀ rid r result f b → Valid b → Valid (T.cacheResult rid r result f b)
  cache-preserves rid r result f b valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls f)
  ... | nothing = valid
  ... | just (current , _) with current ≟ rid
  ...   | no _ = valid
  ...   | yes _ with lookup (T.peerRef r) (C.SubContext.peers (C.subsystem (K.context b)))
  ...     | nothing = valid
  ...     | just peer with Peer.handleRef peer ≟ T.handleRef r | Peer.muxRef peer ≟ T.mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (T.descriptor r)) result (Peer.runs peer)
  ...         | nothing = valid
  ...         | just rs = valid
  cache-preserves rid r result f b valid | just (current , _) | yes _ | just peer | no _ | _ = valid
  cache-preserves rid r result f b valid | just (current , _) | yes _ | just peer | yes _ | no _ = valid
  enact-preserves : ∀ plan s {t} → T.enact plan s ≡ just t → ProtocolValid s → ProtocolValid t
  enact-preserves (T.inherit a f) s eq valid with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → step-preserves a (T.base s) advanced valid }
  enact-preserves (T.caller a f) s eq valid with PS.step a (K.peers (T.base s)) in advanced
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → PeerSupply.step-preserves isIOManagerError a (K.peers (T.base s)) advanced valid }
  enact-preserves (T.local f) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.reading r) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.traceFault w rid result fs) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.deliverTraceFault w rid result fs coordinator) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.birth w capturedFrame pool j rid r f) s eq valid = case just-injective eq of λ { refl → valid }
  enact-preserves (T.complete a rid r result) s eq valid with K.step a (T.base s) in advanced
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → cache-preserves rid r result (T.front s) b
    (step-preserves a (T.base s) advanced valid) }
  advance-preserves : ∀ a s {t} → T.advance a s ≡ just t → ProtocolValid s → ProtocolValid t
  advance-preserves a s eq valid with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just plan = enact-preserves plan s eq valid
  run-preserves : ∀ {s as t} → T.Runs s as t → ProtocolValid s → ProtocolValid t
  run-preserves T.stop valid = valid
  run-preserves (T.more {s = s} {a = a} eq rest) valid = run-preserves rest (advance-preserves a s eq valid)
  from-initial-protocols : ∀ {c g s as t} → T.initialize (O.initial c) g ≡ just s →
    SupplyBounds (I.world c) → T.Runs s as t → ProtocolValid t
  from-initial-protocols {c} {g} initialized bounded path with K.initial (O.initial c) g in started
  ... | nothing = case initialized of λ ()
  ... | just b = case just-injective initialized of λ { refl → run-preserves path (initial-valid c g started bounded) }
