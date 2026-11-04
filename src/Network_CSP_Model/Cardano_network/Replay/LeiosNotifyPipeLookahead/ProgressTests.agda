{-# OPTIONS --safe #-}

-- Inhabited conditional liveness and controls for starvation, failure and premature EOF.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ProgressTests where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (+_)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool Bool as D
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Bool Bool as Work
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Bool Bool as P
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Bool Bool as R
import Cardano_network.LeiosNotifyPipeLookahead.DoneProgress Bool Bool as H
import Cardano_network.LeiosNotifyPipeLookahead.ServerProgress Bool as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownTests as Fixture

-- The invariant is inhabited at a genuinely fresh reachable delayed-hook state.
handoff : H.Handoff Fixture.idle-after-done
handoff = H.received-pending

-- A fully completed target clears the outstanding server trace publication.
closed : D.State
closed = D.pair (D.clientState Fixture.idle-after-done) (S.state S.closed 0 S.idle 0 true)
  [] [] nothing nothing nothing nothing

-- The reference runtime performs the final real hook, then waits in a completed state.
last : R.Execution S.nodeNext
R.state last zero = Fixture.idle-after-done
R.state last (suc n) = closed
R.tick last zero = R.advance (P.wire (D.serverSent S.finish))
R.tick last (suc n) = R.waiting
R.link last zero = refl
R.link last (suc n) = refl

-- Waiting in a completed state is allowed; only unfinished states require responsiveness.
last-responsive : R.Responsive P.Clean last
last-responsive zero unfinished = R.now R.advanced
last-responsive (suc n) unfinished = Data.Empty.⊥-elim (unfinished P.clean)

-- This successful reference execution has no exceptional outcomes.
last-no-failure : R.NoFailure last
last-no-failure zero fault ()
last-no-failure (suc n) fault ()

-- It contains no terminal observation, so it cannot terminate prematurely.
last-maximal : R.Maximal last
last-maximal zero ()
last-maximal (suc n) ()

-- One extra runtime wait changes neither source state nor subsequent operations.
delay : R.Execution S.nodeNext → R.Execution S.nodeNext
R.state (delay ex) zero = R.state ex zero
R.state (delay ex) (suc n) = R.state ex n
R.tick (delay ex) zero = R.waiting
R.tick (delay ex) (suc n) = R.tick ex n
R.link (delay ex) zero = refl
R.link (delay ex) (suc n) = R.link ex n

-- A finite response remains finite after shifting its runtime index by one.
shift-response : ∀ ex n → R.Response ex n → R.Response (delay ex) (suc n)
shift-response ex n (R.now returned) = R.now returned
shift-response ex n (R.later eq response) = R.later eq (shift-response ex (suc n) response)

-- Inserting a wait preserves aggregate responsiveness without a fixed latency bound.
delay-responsive : ∀ ex → R.Responsive P.Clean ex → R.Responsive P.Clean (delay ex)
delay-responsive ex responsive zero unfinished = R.later refl (shift-response ex zero (responsive zero unfinished))
delay-responsive ex responsive (suc n) unfinished = shift-response ex n (responsive n unfinished)

-- Waiting cannot introduce an operation failure.
delay-no-failure : ∀ ex → R.NoFailure ex → R.NoFailure (delay ex)
delay-no-failure ex noFailure zero fault ()
delay-no-failure ex noFailure (suc n) fault eq = noFailure n fault eq

-- Waiting cannot introduce an unjustified terminal observation.
delay-maximal : ∀ ex → R.Maximal ex → R.Maximal (delay ex)
delay-maximal ex maximal zero ()
delay-maximal ex maximal (suc n) eq = maximal n eq

-- Every finite delay has a concrete runtime schedule, not just assumed fairness evidence.
delayed : ℕ → R.Execution S.nodeNext
delayed zero = last
delayed (suc n) = delay (delayed n)

-- All these executions start at the same fresh reachable source prefix.
delayed-initial : ∀ n → R.state (delayed n) zero ≡ Fixture.idle-after-done
delayed-initial zero = refl
delayed-initial (suc n) = delayed-initial n

-- Arbitrary finite waiting still supplies the explicit responsiveness premise.
delayed-responsive : ∀ n → R.Responsive P.Clean (delayed n)
delayed-responsive zero = last-responsive
delayed-responsive (suc n) = delay-responsive (delayed n) (delayed-responsive n)

-- No hidden failure assumption is needed to construct these successful executions.
delayed-no-failure : ∀ n → R.NoFailure (delayed n)
delayed-no-failure zero = last-no-failure
delayed-no-failure (suc n) = delay-no-failure (delayed n) (delayed-no-failure n)

-- Their maximality premise is inhabited as well.
delayed-maximal : ∀ n → R.Maximal (delayed n)
delayed-maximal zero = last-maximal
delayed-maximal (suc n) = delay-maximal (delayed n) (delayed-maximal n)

-- The actual runtime liveness theorem applies for every chosen finite wait.
eventual : ∀ n → R.Eventual P.Clean (delayed n) zero
eventual n = R.With.complete S.nodeNext P.Clean H.Handoff (H.local-progress S.nodeNext)
  (delayed n) (delayed-responsive n) (delayed-no-failure n) (delayed-maximal n) zero
  invariant (H.both-stopping invariant)
  where
  -- Equality transports the established structural invariant to the delayed initial state.
  invariant : H.Handoff (R.state (delayed n) zero)
  invariant = subst H.Handoff (sym (delayed-initial n)) handoff

-- Publishing Quit gives real server progress even with a claimed reply and no next result.
cancel-without-next : Server.Move S.nodeNext (S.state S.flushing 0 S.claimed 0 true)
  (S.state S.flushing 0 (S.selected S.canceled) 0 true)
cancel-without-next = Server.internal (S.cancel refl)

-- Permanent starvation is representable, but it does not satisfy finite responsiveness.
starved : R.Execution S.nodeNext
R.state starved n = Fixture.idle-after-done
R.tick starved n = R.waiting
R.link starved n = refl

-- Inductive finite-response evidence cannot describe an infinite sequence of waits.
no-response : ∀ {n} → R.Response starved n → ⊥
no-response (R.now ())
no-response (R.later eq response) = no-response response

-- The responsiveness assumption excludes this concrete unfinished starvation schedule.
starved-not-responsive : ¬ R.Responsive P.Clean starved
starved-not-responsive responsive = no-response (responsive zero (λ ()))

-- A returned callback exception is a response, not a successful operation.
faulting : R.Execution S.nodeNext
R.state faulting n = Fixture.idle-after-done
R.tick faulting n = R.failed R.callback
R.link faulting n = refl

-- Responsiveness alone therefore cannot exclude exceptional executions.
fault-responds : R.Responsive P.Clean faulting
fault-responds n unfinished = R.now R.faulted

-- This is exactly the separate no-failure premise that such an execution violates.
fault-not-successful : ¬ R.NoFailure faulting
fault-not-successful noFailure = noFailure zero R.callback refl

-- Treating an incomplete log EOF as a halted runtime is an observable premature stop.
eof : R.Execution S.nodeNext
R.state eof n = Fixture.idle-after-done
R.tick eof n = R.halted
R.link eof n = refl

-- A terminal observation can return promptly while protocol work remains enabled.
eof-responds : R.Responsive P.Clean eof
eof-responds n unfinished = R.now R.stopped

-- Finite log EOF cannot supply the maximal-execution premise for this fresh prefix.
eof-not-maximal : ¬ R.Maximal eof
eof-not-maximal maximal = maximal zero refl (P.wire (D.serverSent S.finish))

-- Shutdown predicates alone admit malformed states missing the physical Done packet.
missing-done : D.State
missing-done = D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just true))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- Both peers are stopping, but this alone is not a structural progress invariant.
missing-done-stopping : Work.BothStopping missing-done
missing-done-stopping = refl , refl

-- This arbitrary-state control is not asserted reachable from fresh reliable peers.
missing-done-not-clean : ¬ P.Clean missing-done
missing-done-not-clean ()

-- Finite potential permits deadlock; source reachability/coherence must rule this case out.
missing-done-terminal : ∀ {p t} → P.Move p missing-done t → ⊥
missing-done-terminal (P.wire ())
missing-done-terminal (P.internal (D.clientInternal ()))
missing-done-terminal (P.internal (D.serverInternal ()))
missing-done-terminal (P.internal (D.clientCallback D.continue ()))
missing-done-terminal (P.internal (D.clientCallback D.terminate ()))
missing-done-terminal (P.internal (D.clientCallback D.handled ()))
missing-done-terminal (P.internal (D.serverCallback ()))
missing-done-terminal (P.internal (D.commitClient {m = D.request} ()))
missing-done-terminal (P.internal (D.commitClient {m = D.quit} ()))
missing-done-terminal (P.internal (D.commitServer {m = D.reply _} ()))
missing-done-terminal (P.internal (D.commitServer {m = D.done} ()))
