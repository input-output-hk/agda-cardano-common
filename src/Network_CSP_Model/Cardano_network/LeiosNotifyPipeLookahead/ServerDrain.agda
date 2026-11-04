{-# OPTIONS --safe #-}

-- Paired server progress after Quit accounts for physical commits and delayed Send hooks.
module Cardano_network.LeiosNotifyPipeLookahead.ServerDrain
  (Notification Return : Set) where

open import Data.List using (List)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.ServerPhase Notification as Phase
import Cardano_network.LeiosNotifyPipeLookahead.ServerSendSlot Notification Return as Slot
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification Return as Work
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification Return as Proof
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification Return as Runtime
open Proof using (Move; internal; wire; LocalProgress; Completion)

-- The target closes the actual server control and has no owed or unretired server work.
Closed : D.State → Set
Closed raw = Server.Closed (D.serverState raw)

-- Both fields are structural properties established by fresh runs, not liveness assumptions.
Region : D.State → Set
Region raw = Server.Stopping (D.serverState raw) × Slot.Consistent raw

-- Every visible paired record retains the server's post-Quit phase invariant.
step-stopping : ∀ {p s row t} → D.Step p s row t →
  Server.Stopping (D.serverState s) → Server.Stopping (D.serverState t)
step-stopping (D.clientSent _) stopping = stopping
step-stopping (D.clientReceived _) stopping = stopping
step-stopping (D.serverSent pr) stopping = Server.step-stays pr stopping
step-stopping (D.serverReceived pr) stopping = Server.step-stays pr stopping

-- Only actual server source scheduling/callbacks change that phase during hidden work.
tau-stopping : ∀ {p s t} → D.Tau p s t →
  Server.Stopping (D.serverState s) → Server.Stopping (D.serverState t)
tau-stopping (D.clientInternal _) stopping = stopping
tau-stopping (D.serverInternal pr) stopping = Server.tau-stays pr stopping
tau-stopping (D.clientCallback _ _) stopping = stopping
tau-stopping (D.serverCallback pr) stopping = Server.step-stays pr stopping
tau-stopping (D.commitClient _) stopping = stopping
tau-stopping (D.commitServer _) stopping = stopping
tau-stopping (D.decodeClient _) stopping = stopping
tau-stopping (D.decodeServer _) stopping = stopping

-- An unpublished reply is either committed now or recorded from its matching pending slot.
send-progress : ∀ {p msg next} (raw : D.State) →
  S.Step p (D.serverState raw) (S.sendReply msg) next → Slot.Consistent raw →
  Σ[ t ∈ D.State ] Move p raw t
send-progress (D.pair c s cs sc pc nothing rc rs) pr slot =
  _ , internal (D.commitServer pr)
send-progress (D.pair c s cs sc pc (just (D.reply msg)) rc rs) (S.send active) Slot.reply =
  _ , wire (D.serverSent (S.send active))
send-progress (D.pair c s cs sc pc (just D.done) rc rs) (S.send active) ()

-- The exact same commit/record distinction applies to the final Done send.
done-progress : ∀ {p next} (raw : D.State) →
  S.Step p (D.serverState raw) S.sendDone next → Slot.Consistent raw →
  Σ[ t ∈ D.State ] Move p raw t
done-progress (D.pair c s cs sc pc nothing rc rs) pr slot =
  _ , internal (D.commitServer pr)
done-progress (D.pair c s cs sc pc (just (D.reply msg)) rc rs) S.finish ()
done-progress (D.pair c s cs sc pc (just D.done) rc rs) S.finish Slot.done =
  _ , wire (D.serverSent S.finish)

-- Server source progress lifts to a real operation of the unchanged paired driver.
lift : ∀ {p s next} → Server.Move p (D.serverState s) next →
  Region s → Σ[ t ∈ D.State ] Move p s t
lift (Server.internal pr) region = _ , internal (D.serverInternal pr)
lift (Server.visible (S.receiveRequest S.atFirst)) (() , slot)
lift (Server.visible (S.receiveRequest S.atNext)) (() , slot)
lift (Server.visible (S.receiveQuit S.atFirst)) (() , slot)
lift (Server.visible (S.receiveQuit S.atNext)) (() , slot)
lift (Server.visible (S.choose active allowed)) region =
  _ , internal (D.serverCallback (S.choose active allowed))
lift {s = s} (Server.visible pr@(S.send _)) (stopping , slot) = send-progress s pr slot
lift {s = s} (Server.visible S.finish) (stopping , slot) = done-progress s S.finish slot

-- A closed exact server has no source operation that could masquerade as progress.
closed-terminal : ∀ {p s t} → Server.Move p s t → Server.Closed s → ⊥
closed-terminal (Server.internal ()) Server.closed
closed-terminal (Server.visible ()) Server.closed

-- Both structural fields survive every paired move, including unrelated client work.
preserved : ∀ {p s t} → Move p s t → Region s → Region t
preserved (internal pr) (stopping , slot) = tau-stopping pr stopping , Slot.tau-consistent pr slot
preserved (wire pr) (stopping , slot) = step-stopping pr stopping , Slot.step-consistent pr slot

-- No unfinished server in this region can be blocked solely by an inconsistent trace slot.
progress : ∀ {p s} → Region s → Closed s ⊎
  (¬ Closed s × Σ[ t ∈ D.State ] Move p s t)
progress (stopping , slot) with Server.progress stopping
... | inj₁ finished = inj₁ finished
... | inj₂ (next , source) = inj₂ ((closed-terminal source) , lift source (stopping , slot))

-- This local-progress contract has no unproved callback/channel/fairness field.
local-progress : ∀ p → LocalProgress p Closed Region
LocalProgress.preserve (local-progress p) = preserved
LocalProgress.ready (local-progress p) region both = progress region

-- The existing well-founded completion theorem now applies to the whole server drain.
module Complete (p : S.Contract) = Proof.With p Closed Region (local-progress p)

-- Fresh endpoint projection supplies the source phase while the slot invariant is universal.
fresh-region : ∀ {p rows s} → D.Run p D.initial rows s → Work.BothStopping s → Region s
fresh-region {p} run (clientStopping , serverStopping) with Projection.For.server p run
... | actions , source , matching =
  Phase.shutdown-shape (Phase.initial-phase source) serverStopping , Slot.initial-consistent run

-- Every fresh paired shutdown state admits a bounded actual continuation closing the server.
fresh-complete : ∀ {p rows s} → D.Run p D.initial rows s → Work.BothStopping s → Completion p Closed s
fresh-complete {p} run both = Complete.complete p (fresh-region run both) both

-- Runtime server completion no longer asks the caller for an unproved structural invariant.
fresh-runtime-complete : ∀ {p} (ex : Runtime.Execution p) → Runtime.Responsive Closed ex →
  Runtime.NoFailure ex → Runtime.Maximal ex → ∀ n {rows} →
  D.Run p D.initial rows (Runtime.state ex n) → Work.BothStopping (Runtime.state ex n) →
  Runtime.Eventual Closed ex n
fresh-runtime-complete {p} ex responsive noFailure maximal n prefix both =
  Runtime.With.complete p Closed Region (local-progress p) ex responsive noFailure maximal n
    (fresh-region prefix both) both
