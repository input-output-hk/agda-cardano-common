{-# OPTIONS --safe #-}

-- Kernel refutations use source-prefix bounds, never normalization of the paired search.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstructionTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Bool Bool._≟_ false as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstruction Bool ⊤ as Cycle
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PrefixTransport Bool ⊤ as Prefix
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverShutdownPrecheckTests as Previous

-- The generic family is definitionally the previously retained three-round counterexample input.
three-client-exact : Cycle.client false 3 ≡ Previous.cycle-client
three-client-exact = refl

-- The server family preserves all three original Request occurrences and all three exact reply Sends.
three-server-exact : Cycle.server false 3 ≡ Previous.cycle-server
three-server-exact = refl

-- All five prior necessary checks pass, without implying a source merge exists.
three-five-pass : ∀ contract → Check.AllPrechecks contract (Cycle.client false 3) (Cycle.server false 3)
three-five-pass = Previous.cycle-five-pass

-- The old semantic gap is now refuted by the kernel for both callback contracts.
three-no-source : ∀ contract → Check.SourceTrace contract Previous.cycle-client Previous.cycle-server → ⊥
three-no-source contract = Cycle.no-source contract false 3 ≤-refl

-- The next family member also passes all five guards; this gate computes only the cheap checks.
four-five-pass : ∀ contract → Check.AllPrechecks contract (Cycle.client true 4) (Cycle.server true 4)
four-five-pass contract = toWitness {a? = Check.all-prechecks? contract (Cycle.client true 4) (Cycle.server true 4)} tt

-- Four rounds are excluded by the same quantified theorem, independently of search execution.
four-no-source : ∀ contract → Check.SourceTrace contract (Cycle.client true 4) (Cycle.server true 4) → ⊥
four-no-source contract = Cycle.no-source contract true 4 (s≤s (s≤s (s≤s z≤n)))

-- Mixed messages and arbitrary tails satisfy the stronger source-prefix obstruction as well.
mixed-client : List Rows.ClientRow
mixed-client = Rows.receiveResponse (D.reply S.canceled) ∷ Rows.sendCommand D.quit ∷
  Rows.receiveResponse D.done ∷ Rows.sendCommand D.request ∷ []

-- The combinatorial cut does not need local-validity or equal-packet assumptions.
mixed-server : List Rows.ServerRow
mixed-server = Rows.receiveCommand D.quit ∷ Rows.receiveCommand D.request ∷
  Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ []

-- The exact original source proposition is rejected even when values are not the normal family.
mixed-no-source : ∀ contract → Check.SourceTrace contract mixed-client mixed-server → ⊥
mixed-no-source contract (events , merged , target , source) =
  Cycle.prefix-impossible (D.reply S.canceled) D.done D.quit D.quit D.request D.quit
    (Rows.sendCommand D.request ∷ []) (Rows.sendResponse D.done ∷ []) merged source

-- An empty Return carrier does not weaken the obstruction or require a fabricated return inhabitant.
module EmptyReturn where
  import Cardano_network.Replay.LeiosNotifyPipeLookahead.CycleObstruction Bool ⊥ as Generic

  -- This instance demonstrates that the theorem's Return parameter is genuinely unrestricted.
  no-three : ∀ contract → Generic.SourceTrace contract (Generic.client false 3) (Generic.server false 3) → ⊥
  no-three contract = Generic.no-source contract false 3 ≤-refl

-- A two-round merge remains compatible with every-prefix transport bounds.
-- This is an abstract bound control, not a claim that Bounded implies original source reachability.
two-events : List D.Event
two-events = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷
  D.clientSend D.request ∷ D.serverRecv D.request ∷ D.serverSend (D.reply (S.normal false)) ∷
  D.clientRecv (D.reply (S.normal false)) ∷ D.clientSend D.request ∷
  D.serverSend (D.reply (S.normal false)) ∷ []

-- The supplied finite merge preserves both two-round endpoint orders exactly.
two-merge : Rows.Merge (Cycle.client false 2) (Cycle.server false 2) two-events
two-merge = Rows.server (Rows.client (Rows.client (Rows.server (Rows.server
  (Rows.client (Rows.client (Rows.server Rows.empty)))))))

-- No false arithmetic obstruction is introduced at the n=2 boundary.
two-bounded : Prefix.Bounded Prefix.History.empty two-events
two-bounded =
  Prefix.next (s≤s z≤n , z≤n)
  (Prefix.next (s≤s z≤n , s≤s z≤n)
  (Prefix.next (s≤s z≤n , s≤s z≤n)
  (Prefix.next (s≤s (s≤s z≤n) , s≤s z≤n)
  (Prefix.next (s≤s (s≤s z≤n) , s≤s z≤n)
  (Prefix.next (s≤s (s≤s z≤n) , s≤s (s≤s z≤n))
  (Prefix.next (s≤s (s≤s z≤n) , s≤s (s≤s z≤n))
  (Prefix.next (s≤s (s≤s z≤n) , s≤s (s≤s z≤n)) Prefix.done)))))))
