{-# OPTIONS --safe #-}

-- Every fresh successful paired shutdown has structural progress through full clean closure.
module Cardano_network.LeiosNotifyPipeLookahead.PairedDrain
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.ClientPhase Notification Return as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification Return as Accounting
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.ServerDrain Notification Return as ServerDrain
import Cardano_network.LeiosNotifyPipeLookahead.ClientDrain Notification Return as ClientDrain
import Cardano_network.LeiosNotifyPipeLookahead.CommandFlow Notification Return as Command
import Cardano_network.LeiosNotifyPipeLookahead.ResponseFlow Notification Return as Response
import Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger Notification Return as Ledger
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as Proof
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as Runtime

-- Fresh reachability is a concrete finite source witness, not a termination or fairness premise.
Reachable : S.Contract → D.State → Set
Reachable contract s = Σ[ rows ∈ List D.Event ] D.Run contract D.initial rows s

-- Concatenation retains every original operation and wire row in its actual order.
append : ∀ {p s rows t more u} → D.Run p s rows t → D.Run p t more u → D.Run p s (rows ++ more) u
append D.stop suffix = suffix
append (D.internal pr run) suffix = D.internal pr (append run suffix)
append (D.visible pr run) suffix = D.visible pr (append run suffix)

-- Appending an actual enabled move preserves the fresh source witness constructively.
preserved : ∀ {p s t} → Proof.Move p s t → Reachable p s → Reachable p t
preserved (Proof.internal pr) (rows , prefix) = rows ++ [] , append prefix (D.internal pr D.stop)
preserved (Proof.wire {row = row} pr) (rows , prefix) = rows ++ (row ∷ []) , append prefix (D.visible pr D.stop)

-- Paired clean closure includes the server's exact closed/count/sender shape.
clean-server : ∀ {s} → Proof.Clean s → ServerDrain.Closed s
clean-server Proof.clean = Server.closed

-- Once the server is closed, fresh command/response/ledger facts supply all client progress.
when-server-closed : ∀ {p raw} → Phase.Phase (D.clientState raw) →
  Accounting.Accounted (D.clientState raw) → Command.Consistent raw → Response.Consistent raw →
  Ledger.Balanced raw → ServerDrain.Closed raw →
  Proof.Clean raw ⊎ (¬ Proof.Clean raw × Σ[ t ∈ D.State ] Proof.Move p raw t)
when-server-closed {raw = D.pair c .ClientDrain.server cs sc pc ps rc rs}
  phase inventory commands responses ledger Server.closed
  with Command.closed-commands {raw = D.pair c ClientDrain.server cs sc pc ps rc rs} commands refl
... | seal , refl , refl
  with Response.server-closed {raw = D.pair c ClientDrain.server [] sc pc ps rc nothing} responses refl
...   | refl = ClientDrain.progress phase inventory seal responses ledger

-- Every unfinished fresh shutdown state enables an actual hidden operation or wire record.
progress : ∀ {p rows s} → D.Run p D.initial rows s → Work.BothStopping s →
  Proof.Clean s ⊎ (¬ Proof.Clean s × Σ[ t ∈ D.State ] Proof.Move p s t)
progress {p} prefix both with ServerDrain.progress {p = p} (ServerDrain.fresh-region prefix both)
... | inj₂ (unfinished , next) = inj₂ ((λ clean → unfinished (clean-server clean)) , next)
... | inj₁ finished with Projection.For.client p prefix
...   | actions , client , matching = when-server-closed (Phase.initial-phase client)
    (Accounting.initial-accounted client) (Command.initial-consistent prefix)
    (Response.initial-consistent prefix) (Ledger.initial-balanced prefix) finished

-- Fresh reachability now discharges both fields of the complete structural-progress contract.
local-progress : ∀ p → Proof.LocalProgress p Proof.Clean (Reachable p)
Proof.LocalProgress.preserve (local-progress p) = preserved
Proof.LocalProgress.ready (local-progress p) (rows , prefix) both = progress prefix both

-- The existing well-founded operation bound yields general model completion without new axioms.
module Complete (p : S.Contract) = Proof.With p Proof.Clean (Reachable p) (local-progress p)

-- Every fresh paired shutdown state has a bounded actual continuation to full clean closure.
fresh-complete : ∀ {p rows s} → D.Run p D.initial rows s → Work.BothStopping s → Proof.Completion p Proof.Clean s
fresh-complete {p} {rows} prefix both = Complete.complete p (rows , prefix) both

-- Any finite maximal successful shutdown continuation from a fresh state is fully clean.
fresh-maximal-completes : ∀ {p past s rows t} → D.Run p D.initial past s → Work.BothStopping s →
  D.Run p s rows t → (∀ {u} → Proof.Move p t u → ⊥) → Proof.Clean t
fresh-maximal-completes {p} {past} prefix both run maximal =
  Complete.maximal-completes p run (past , prefix) both maximal

-- Runtime liveness keeps only actual responsiveness/failure/terminal premises and fresh reachability.
fresh-runtime-complete : ∀ {p} (ex : Runtime.Execution p) → Runtime.Responsive Proof.Clean ex →
  Runtime.NoFailure ex → Runtime.Maximal ex → ∀ n {rows} →
  D.Run p D.initial rows (Runtime.state ex n) → Work.BothStopping (Runtime.state ex n) →
  Runtime.Eventual Proof.Clean ex n
fresh-runtime-complete {p} ex responsive noFailure maximal n {rows} prefix both =
  Runtime.With.complete p Proof.Clean (Reachable p) (local-progress p) ex responsive noFailure maximal n
    (rows , prefix) both
