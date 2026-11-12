{-# OPTIONS --guardedness #-}

-- Positive scheduled-close and negative foreign-caller controls for original c2.
-- Label checks compute only policy; all state transitions come from the existing
-- source executions and the proved allowed/guarded execution equivalence.
module ConnectionManagement.Negative.OwnedCallersFixture where

open import Data.Bool using (true; false)
open import Data.List using (map; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import ConnectionManagement.Domain using (WorkerId; DecEq-Id)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Negative.ServerPeers using (module Protocols)
open Protocols.StartTrace.ScopedCM.Completion using (serverFinished; allFinishedActions)
import ConnectionManagement.Negative.PoolRelays as Relays
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.GovernorPool as Prior
import ConnectionManagement.Negative.ForeignCallerResidue as Foreign
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Variants.OwnedCallers as Variant
import ConnectionManagement.Properties.OwnedCallers as C2
open Variant I.bearerClosed Prior.classify using (ownedOnly; module K)
open Variant.Protocols I.bearerClosed Prior.classify Protocols.capability using
  (module T; module Outer; OuterRuns′; Allowed; allowed-build; advance′; eventOnly; enact′)
open C2.Protocols I.bearerClosed Prior.classify Protocols.capability using
  (NoFrames; no-frames; everyOwned; source-policy; run-policy)

-- The c1 fixture's entire scheduled-close action list satisfies the policy.
scheduled-labels : everyOwned (map Outer.innerAct allFinishedActions ++ Relays.Initialized.closeActions) ≡ true
scheduled-labels = refl

-- In particular the original, abstract source execution satisfies plan policy.
scheduled-policy : Allowed Relays.Initialized.initialized-relays-close
scheduled-policy = source-policy scheduled-labels Relays.Initialized.initialized-relays-close

-- The same initialized outer execution is a run of the executable variant.
scheduled-run : OuterRuns′ (Outer.outer Protocols.initial (RR.initial true))
  (map Outer.innerAct allFinishedActions ++ Relays.Initialized.closeActions) Relays.Initialized.closed
scheduled-run = allowed-build Relays.Initialized.initialized-relays-close scheduled-policy

-- Both original c2 clauses follow from the universal endpoint, for all workers.
scheduled-close : NoFrames serverFinished
scheduled-close = no-frames {start = Protocols.initial} {scheduled = true} {final = serverFinished} {t = just RR.joined} Protocols.initializer scheduled-run

-- The acquisition clause is the exact requested lookup equation.
scheduled-acquiring : ∀ w → lookup w (O.acquiring (T.sourceOf serverFinished)) ≡ nothing
scheduled-acquiring = proj₁ scheduled-close

-- The release clause has the same universal worker quantification.
scheduled-releasing : ∀ w → lookup w (O.releasing (T.sourceOf serverFinished)) ≡ nothing
scheduled-releasing = proj₂ scheduled-close

-- The inserted raw begin is exactly one of the two excluded shared actions.
foreign-begin-policy : ownedOnly (K.coreStep (O.beginAcquire Foreign.foreignWorker Foreign.foreignRequest)) ≡ false
foreign-begin-policy = refl

-- The event-only policy identifies that same forbidden action in the witness.
foreign-event-policy : eventOnly Foreign.foreignEvent ≡ false
foreign-event-policy = refl

-- A denied dispatch is refused independently of its concrete runtime state.
dispatch-refused : ∀ a s → ownedOnly a ≡ false → advance′ (T.dispatch a) s ≡ nothing
dispatch-refused a s denied with T.inheritAllowed a s
... | false = refl
... | true rewrite denied = refl

-- Guarding prevents the inserted edge enabled by the original source witness.
foreign-begin-refused : advance′ Foreign.foreignEvent Foreign.start ≡ nothing
foreign-begin-refused = dispatch-refused (K.coreStep (O.beginAcquire Foreign.foreignWorker Foreign.foreignRequest)) Foreign.start refl

-- A complete wrapper cannot evade the policy even as an arbitrary supplied plan.
complete-begin-refused : ∀ rid r result s →
  enact′ (T.complete (K.coreStep (O.beginAcquire Foreign.foreignWorker Foreign.foreignRequest)) rid r result) s ≡ nothing
complete-begin-refused rid r result s = refl

-- The complete initialized counterexample action list fails the policy check.
foreign-labels : everyOwned (map Outer.innerAct Foreign.innerActions ++ Relays.Initialized.closeActions) ≡ false
foreign-labels = refl

-- No variant execution has the counterexample's actions and final state.
foreign-run-not-variant : ¬ OuterRuns′ (Outer.outer Protocols.initial (RR.initial true))
  (map Outer.innerAct Foreign.innerActions ++ Relays.Initialized.closeActions) Foreign.closed
foreign-run-not-variant path = case trans (sym foreign-labels) (run-policy path) of λ ()

-- The actual source counterexample witness fails the equivalent plan predicate.
foreign-source-policy-rejected : ¬ Allowed Foreign.initialized-close
foreign-source-policy-rejected ok = foreign-run-not-variant (allowed-build Foreign.initialized-close ok)
