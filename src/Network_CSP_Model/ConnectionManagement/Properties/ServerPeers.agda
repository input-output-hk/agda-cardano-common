{-# OPTIONS --guardedness #-}

-- Exact source/view observations and operational pool/scope certificates for
-- shared executions. Pool projections do not erase CM writes into raw stutters.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerPeers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.PeerSupervision as PeerFacts
import ConnectionManagement.Properties.JobPoolClose as GovernorClose
import ConnectionManagement.Properties.JobPoolCloseKernel as MonitorClose
import ConnectionManagement.Properties.AsyncScope as ScopeFacts
import ConnectionManagement.Rules.AsyncScope as Scope
private
  module K = Combined isBearerClosed isIOManagerError
  module E = Exit isBearerClosed
  module S = Server isBearerClosed
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError
  module P = PeerFacts isIOManagerError
  module GClose = GovernorClose PS.GP.Body
  module BClose = MonitorClose (Maybe ErrorId) false

shared-source : ∀ s → PS.cm (K.peers s) ≡ K.source s
shared-source s = refl
server-step : ∀ a s {t} → K.step (K.serverStep a) s ≡ just t →
  Σ E.State (λ e → E.step a (K.server s) ≡ just e × K.server t ≡ e × K.context t ≡ K.context s)
server-step a s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s) in advanced
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → e , refl , refl , refl }
peer-step : ∀ a s {t} → K.step (K.peerStep a) s ≡ just t →
  Σ PS.State (λ p → PS.step a (K.peers s) ≡ just p × K.peers t ≡ p × K.source t ≡ PS.cm p)
peer-step a s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → p , refl , refl , refl }

-- Server and common CM actions leave the peer pool/scope view unchanged.
view : K.State → P.View
view s = P.view (K.peers s)
step-projects : ∀ a s {t} → K.step a s ≡ just t → P.Paths (view s) (view t)
step-projects (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → P.idle (view s) }
step-projects (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s) in advanced
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → P.step-projects a (K.peers s) advanced }
step-projects (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → P.idle (view s) }
exec-projects : ∀ {s as t} → K.Executes s as t → P.Paths (view s) (view t)
exec-projects K.done = P.idle _
exec-projects (K.next {s = s} {a = a} eq rest) = P.compose (step-projects a s eq) (exec-projects rest)

-- Closure certificates refer only to real captured Async handles. They do not
-- certify raw admission workers, handlers, eventual closure or Server return.
from-initial : ∀ {c g s as t} → K.initial c g ≡ just s → K.Executes s as t →
  PS.GP.Pool.phase (C.governorPool (K.context t)) ≡ PS.GP.Pool.closedPool →
  PS.Pool.phase (C.monitorPool (K.context t)) ≡ PS.Pool.closedPool →
  Scope.cursor (C.scopes (K.context t)) ≡ Scope.finishedScope →
  (∀ j → j ∈ PS.GP.Pool.snapshot (C.governorPool (K.context t)) → GClose.Terminal (C.governorPool (K.context t)) j) ×
  (∀ tid → tid ∈ PS.Pool.snapshot (C.monitorPool (K.context t)) → BClose.Terminal (C.monitorPool (K.context t)) tid) ×
  ScopeFacts.AllJoined (C.scopes (K.context t))
from-initial {c} {g} initialized path govClosed bgClosed scopesClosed with E.initial c
... | nothing = case initialized of λ ()
... | just e with just-injective initialized
...   | refl with exec-projects path
...     | P.paths (ga , gp) (ba , bp) (sa , sp) =
  GClose.from-initial gp govClosed , BClose.from-initial bp bgClosed , ScopeFacts.from-initial sp scopesClosed

-- Callback return itself establishes the closure gates, rather than requiring
-- a caller to assert them independently after an initialized shared execution.
callback-gate : ∀ s {t} → K.step (K.serverStep (E.run (S.scope S.returnAction))) s ≡ just t →
  K.peerClosed s ≡ true
callback-gate s eq with K.peerClosed s
... | false = case eq of λ ()
... | true = refl
scope-closed : ∀ scopes → Scope.closed scopes ≡ true → Scope.cursor scopes ≡ Scope.finishedScope
scope-closed scopes eq with Scope.cursor scopes
... | Scope.finishedScope = refl
... | Scope.openScope = case eq of λ ()
... | Scope.closing actor = case eq of λ ()
... | Scope.readyToFinish = case eq of λ ()
closure-observation : ∀ s → K.peerClosed s ≡ true →
  PS.GP.Pool.phase (C.governorPool (K.context s)) ≡ PS.GP.Pool.closedPool ×
  PS.Pool.phase (C.monitorPool (K.context s)) ≡ PS.Pool.closedPool ×
  Scope.cursor (C.scopes (K.context s)) ≡ Scope.finishedScope
closure-observation s eq with PS.GP.Pool.phase (C.governorPool (K.context s)) |
  PS.Pool.phase (C.monitorPool (K.context s)) | Scope.closed (C.scopes (K.context s)) in scoped
... | PS.GP.Pool.closedPool | PS.Pool.closedPool | true = refl , refl , scope-closed (C.scopes (K.context s)) scoped
... | PS.GP.Pool.closedPool | PS.Pool.closedPool | false = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.openPool | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.closing | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.cancelPending tid | _ = case eq of λ ()
... | PS.GP.Pool.closedPool | PS.Pool.joinPending tid | _ = case eq of λ ()
... | PS.GP.Pool.openPool | _ | _ = case eq of λ ()
... | PS.GP.Pool.closing | _ | _ = case eq of λ ()
... | PS.GP.Pool.cancelPending j | _ | _ = case eq of λ ()
... | PS.GP.Pool.joinPending j | _ | _ = case eq of λ ()
Certificates : K.State → Set
Certificates s =
  (∀ j → j ∈ PS.GP.Pool.snapshot (C.governorPool (K.context s)) → GClose.Terminal (C.governorPool (K.context s)) j) ×
  (∀ tid → tid ∈ PS.Pool.snapshot (C.monitorPool (K.context s)) → BClose.Terminal (C.monitorPool (K.context s)) tid) ×
  ScopeFacts.AllJoined (C.scopes (K.context s))
callback-from-initial : ∀ {c g s as before after} → K.initial c g ≡ just s → K.Executes s as before →
  K.step (K.serverStep (E.run (S.scope S.returnAction))) before ≡ just after → Certificates before
callback-from-initial {before = before} initialized path returned with closure-observation before (callback-gate before returned)
... | gov , bg , scopes = from-initial initialized path gov bg scopes

-- Cheap trace reuse keeps existing operational proofs opaque. Permission is
-- checked for the actual pre-state; it is never inferred from a lower success.
lift-server-step : ∀ a e {next} k → K.serverAllowed a (K.combined e k) ≡ true →
  E.step a e ≡ just next →
  K.step (K.serverStep a) (K.combined e k) ≡ just (K.combined next k)
lift-server-step a e k allowed advanced rewrite allowed | advanced = refl
append : ∀ {s as t bs u} → K.Executes s as t → K.Executes t bs u → K.Executes s (as ++ bs) u
append K.done rest = rest
append (K.next eq path) rest = K.next eq (append path rest)
