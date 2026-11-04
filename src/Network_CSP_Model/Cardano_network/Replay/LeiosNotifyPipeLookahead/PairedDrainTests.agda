{-# OPTIONS --safe #-}

-- General paired completion is inhabited across cancellation, delayed Quit and a held handler.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedDrainTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.Nat using (_≤_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.PairedDrain Bool Bool as Drain
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Bool Bool as P
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Bool Bool as R
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Bool Bool as Work
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Bool Bool as Cost
import Cardano_network.LeiosNotifyPipeLookahead.ClientReplyAccounting Bool Bool as Reply
import Cardano_network.LeiosNotifyPipeLookahead.ResponseFlow Bool Bool as Response
import Cardano_network.LeiosNotifyPipeLookahead.ReplyLedger Bool Bool as Ledger
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ServerDrainTests as Example
import Cardano_network.Replay.LeiosNotifyPipeLookahead.SchedulingTests as Finish
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressTests as Controls
import Cardano_network.Replay.LeiosNotifyPipeLookahead.RunRuntime Bool Bool as Runtime

-- Fresh outstanding reply/marker work now instantiates the full general completion theorem.
completion : P.Completion S.nodeNext P.Clean Example.stopping
completion = Drain.fresh-complete Example.prefix (refl , refl)

-- The existing actual twenty-two-operation path also instantiates the maximal-execution theorem.
maximal-clean : P.Clean Finish.closed
maximal-clean = Drain.fresh-maximal-completes Example.prefix (refl , refl) Example.full-drain
  (P.clean-terminal Example.client-completion)

-- Responsiveness and no failure are constructed for this particular full successful runtime path.
runtime-completion : R.Eventual P.Clean (Runtime.execution Example.full-drain) 0
runtime-completion = Drain.fresh-runtime-complete (Runtime.execution Example.full-drain)
  (Runtime.responsive P.Clean Example.full-drain Example.client-completion)
  (Runtime.no-failure Example.full-drain) (Runtime.maximal Example.full-drain) 0 Example.prefix (refl , refl)

-- The server has received the physical Quit while its client Send record remains pending.
late-quit : D.State
late-quit = D.pair (C.client (C.writingQuit false) C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.signalQuit 0 S.idle 0 false) [] [] (just D.quit) nothing nothing nothing

-- This out-of-order cross-endpoint wire prefix is freshly reachable under the actual boundary.
late-prefix : D.Run S.nodeNext D.initial (D.serverRecv D.quit ∷ []) late-quit
late-prefix =
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopIdle) $
  D.internal (D.commitClient C.sentQuitIdle) $
  D.internal (D.decodeServer (S.receiveQuit S.atFirst)) $
  D.visible (D.serverReceived (S.receiveQuit S.atFirst)) D.stop

-- General completion accounts for the pending client Quit, not just responder work.
late-completion : P.Completion S.nodeNext P.Clean late-quit
late-completion = Drain.fresh-complete late-prefix (refl , refl)

-- The fully closed target retains the client's selected result and arrival count.
late-closed : D.State
late-closed = D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- Server Send-Done may itself precede the delayed client Send-Quit record.
late-drain : D.Run S.nodeNext late-quit
  (D.serverSend D.done ∷ D.clientSend D.quit ∷ D.clientRecv D.done ∷ []) late-closed
late-drain =
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.commitServer S.finish) $
  D.visible (D.serverSent S.finish) $
  D.visible (D.clientSent C.sentQuitIdle) $
  D.internal (D.decodeClient C.receivedDone) $
  D.visible (D.clientReceived C.receivedDone) D.stop

-- This inhabited delayed-command shutdown uses seven operations within the universal bound.
late-count : Work.steps late-drain ≡ 7
late-count = refl

-- The same initial-state potential counts the actual hidden and visible operations here.
late-bound : Work.steps late-drain ≤ Cost.rank late-quit
late-bound = Work.bounded late-drain (refl , refl)

-- A normal handler may already be running when the client accepts termination.
held-handler : D.State
held-handler = D.pair
  (C.client C.draining (C.handling (S.normal true)) (C.quitMarker ∷ []) [] 2 (+ 0) true (just true))
  (S.state S.signalQuit 0 S.sent 0 false) [] [] nothing nothing nothing nothing

-- The fresh prefix really receives the reply before holding its handler across Quit.
held-prefix : D.Run S.nodeNext D.initial
  (D.clientSend D.request ∷ D.serverRecv D.request ∷ D.serverSend (D.reply (S.normal true)) ∷
   D.clientRecv (D.reply (S.normal true)) ∷ D.clientSend D.quit ∷ D.serverRecv D.quit ∷ []) held-handler
held-prefix =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.visible (D.clientSent C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose {m = S.normal true} refl refl)) $
  D.internal (D.commitServer (S.send refl)) $
  D.visible (D.serverSent (S.send refl)) $
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) $
  D.internal (D.clientInternal (C.keepReply refl)) $
  D.internal (D.clientCallback D.terminate C.stopRequested) $
  D.internal (D.clientInternal C.setStopBusy) $
  D.internal (D.clientInternal C.registerMarker) $
  D.internal (D.commitClient C.sentQuitBusy) $
  D.visible (D.clientSent C.sentQuitBusy) $
  D.internal (D.decodeServer (S.receiveQuit S.atNext)) $
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) D.stop

-- The full theorem includes the required successful handler result in its structural work.
held-completion : P.Completion S.nodeNext P.Clean held-handler
held-completion = Drain.fresh-complete held-prefix (refl , refl)

-- A received-but-unhandled normal owes no further wire reply.
held-replies : Reply.owed (D.clientState held-handler) ≡ 0
held-replies = refl

-- The active handler nevertheless has a real remaining callback operation after Quit.
held-next : Σ[ t ∈ D.State ] P.Move S.nodeNext held-handler t
held-next = _ , P.internal (D.clientCallback D.handled (C.delivered refl))

-- The old arbitrary missing-Done deadlock violates the proved response-flow invariant.
missing-no-flow : Response.Consistent Controls.missing-done → ⊥
missing-no-flow (Response.openFlow sc ps rc sn cn) = sn refl
missing-no-flow (Response.queued () pub rc cn)
missing-no-flow (Response.received pub ())

-- It is therefore excluded from every fresh paired run, for either callback contract.
missing-unreachable : ∀ {p rows} → D.Run p D.initial rows Controls.missing-done → ⊥
missing-unreachable prefix = missing-no-flow (Response.initial-consistent prefix)

-- Dropping the Canceled reply strands an actual response receiver facing only Done.
lost-reply : D.State
lost-reply = D.pair
  (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] (D.done ∷ []) nothing nothing nothing nothing

-- The missing wire response violates the exact outstanding-obligation ledger.
lost-reply-unbalanced : Ledger.Balanced lost-reply → ⊥
lost-reply-unbalanced ()

-- No choice of hidden scheduling or callbacks can make this dropped-packet target fresh reachable.
lost-reply-unreachable : ∀ {p rows} → D.Run p D.initial rows lost-reply → ⊥
lost-reply-unreachable prefix = lost-reply-unbalanced (Ledger.initial-balanced prefix)

-- Duplicating Done preserves reply counts but violates the unique-final-packet language.
duplicate-done : D.State
duplicate-done = D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] (D.done ∷ D.done ∷ []) nothing nothing nothing nothing

-- Exact packet structure excludes duplication that a numerical reply count would miss.
duplicate-no-flow : Response.Consistent duplicate-done → ⊥
duplicate-no-flow (Response.openFlow () ps rc sn cn)
duplicate-no-flow (Response.queued () pub rc cn)

-- The duplicate-final-packet state is excluded from every fresh paired source execution.
duplicate-unreachable : ∀ {p rows} → D.Run p D.initial rows duplicate-done → ⊥
duplicate-unreachable prefix = duplicate-no-flow (Response.initial-consistent prefix)
