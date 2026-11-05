{-# OPTIONS --safe #-}

-- Finite menus preserve every hidden operation family and delayed Send-hook prefixes.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Unit using (⊤; tt)
open import Data.Integer using (+_; -[1+_])
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Bool Bool._≟_ (false ∷ []) as Menu
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecutionReplay Bool Bool._≟_ (false ∷ []) as Replay
module Generic = Replay.For S.genericNext

-- Exact source state replacement shortens tests without changing transport or source rules.
withClient : C.State → D.State
withClient c = D.pair c S.initial [] [] nothing nothing nothing nothing

-- Server-focused states keep a genuine fresh client but allow arbitrary source control.
withServer : S.State → D.State
withServer server = D.pair C.initial server [] [] nothing nothing nothing nothing

-- Every signed continuation depth is covered by the finite exact-target callback basis.
negative-depth : withClient (C.client C.issue C.idle [] [] 0 (+ 0) false nothing) ∈
  Menu.targets S.genericNext D.initial
negative-depth = Menu.target-complete {p = S.genericNext} {s = D.initial} (B.clientCallback (D.continue {k = -[1+ 100 ]}) C.continueZero)

-- Client registration remains an independent hidden choice.
client-registration : withClient (C.client C.writingRequest C.idle (C.responseJob ∷ []) [] 0 (+ 0) false nothing) ∈
  Menu.targets S.genericNext (withClient (C.client C.issue C.idle [] [] 0 (+ 0) false nothing))
client-registration = Menu.target-complete {p = S.genericNext} {s = withClient (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)} (B.clientInternal C.registerResponse)

-- Admission and its fault alternative are both retained, without introducing a capacity guard.
server-admission : withServer (S.state S.register 0 S.idle 0 false) ∈
  Menu.targets S.nodeNext (withServer (S.state S.admit 0 S.idle 0 false))
server-admission = Menu.target-complete {p = S.nodeNext} {s = withServer (S.state S.admit 0 S.idle 0 false)} (B.serverInternal S.admitted)

-- The unmodified source also exposes its independently enabled excessive-request path.
server-excessive : withServer (S.state S.raising 0 S.idle 0 false) ∈
  Menu.targets S.nodeNext (withServer (S.state S.admit 0 S.idle 0 false))
server-excessive = Menu.target-complete {p = S.nodeNext} {s = withServer (S.state S.admit 0 S.idle 0 false)} (B.serverInternal S.excessive)

-- Callback candidates include exactly the supplied normal value and generic cancellation.
ready-values : map proj₁ (Menu.readyMoves S.genericNext (withServer (S.state S.first 0 S.claimed 0 false))) ≡
  withServer (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷
  withServer (S.state S.first 0 (S.selected S.canceled) 0 false) ∷ []
ready-values = refl

-- The normal-only node callback guard removes canceled even though it is a finite candidate.
node-ready-values : map proj₁ (Menu.readyMoves S.nodeNext (withServer (S.state S.first 0 S.claimed 0 false))) ≡
  withServer (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷ []
node-ready-values = refl

-- Explicit generic cancellation is complete for the restricted source family.
server-callback : withServer (S.state S.first 0 (S.selected S.canceled) 0 false) ∈
  Menu.targets S.genericNext (withServer (S.state S.first 0 S.claimed 0 false))
server-callback = Menu.target-complete {p = S.genericNext} {s = withServer (S.state S.first 0 S.claimed 0 false)} (B.serverCallback B.allowCanceled (S.choose refl refl))

-- A committed request enters its physical FIFO and pending Send slot before the record.
client-commit : D.pair
  (C.client C.writingRequest C.idle [] [] 0 (+ 0) false nothing) S.initial
  (D.request ∷ []) [] (just D.request) nothing nothing nothing ∈
  Menu.targets S.genericNext (withClient (C.client C.writingRequest C.idle [] [] 0 (+ 0) false nothing))
client-commit = Menu.target-complete {p = S.genericNext} {s = withClient (C.client C.writingRequest C.idle [] [] 0 (+ 0) false nothing)} (B.commitClient C.sentRequest)

-- Already-selected payloads are not filtered at commit, even outside the callback basis.
server-commit-outside-basis : D.pair C.initial
  (S.state S.first 0 (S.selected (S.normal true)) 0 false)
  [] (D.reply (S.normal true) ∷ []) nothing (just (D.reply (S.normal true))) nothing nothing ∈
  Menu.targets S.nodeNext (withServer (S.state S.first 0 (S.selected (S.normal true)) 0 false))
server-commit-outside-basis = Menu.target-complete {p = S.nodeNext} {s = withServer (S.state S.first 0 (S.selected (S.normal true)) 0 false)} (B.commitServer (S.send refl))

-- FIFO-head decoding likewise preserves a concrete packet outside the callback basis.
client-decode-outside-basis : D.pair
  (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) S.initial
  [] [] nothing nothing (just (D.reply (S.normal true))) nothing ∈
  Menu.targets S.genericNext (D.pair
    (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) S.initial
    [] (D.reply (S.normal true) ∷ []) nothing nothing nothing nothing)
client-decode-outside-basis = Menu.target-complete {p = S.genericNext} {s = D.pair (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) S.initial [] (D.reply (S.normal true) ∷ []) nothing nothing nothing nothing} (B.decodeClient (C.receivedReply refl))

-- Server decoding consumes the actual command head without inventing a receive packet.
server-decode : D.pair C.initial S.initial [] [] nothing nothing nothing (just D.quit) ∈
  Menu.targets S.genericNext (D.pair C.initial S.initial (D.quit ∷ []) [] nothing nothing nothing nothing)
server-decode = Menu.target-complete {p = S.genericNext} {s = D.pair C.initial S.initial (D.quit ∷ []) [] nothing nothing nothing nothing} (B.decodeServer (S.receiveQuit S.atFirst))

-- Both collector modes survive finite enumeration; no single scheduling policy is imposed.
optional-collect : withClient (C.client C.adjustCollected C.idle [] [] 0 (+ 1) false nothing) ∈
  Menu.targets S.genericNext (withClient (C.client C.collectingMaybe C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing))
optional-collect = Menu.target-complete {p = S.genericNext} {s = withClient (C.client C.collectingMaybe C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing)} (B.clientInternal C.optionalResult)

-- Blocking collection uses its distinct unchanged source rule.
blocking-collect : withClient (C.client C.adjustCollected C.idle [] [] 0 (+ 1) false nothing) ∈
  Menu.targets S.genericNext (withClient (C.client C.collectingWait C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing))
blocking-collect = Menu.target-complete {p = S.genericNext} {s = withClient (C.client C.collectingWait C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing)} (B.clientInternal C.blockingResult)

-- The actual dummy Quit receiver consumes no wire reply and remains a hidden choice.
quit-marker : withClient (C.client C.draining (C.publish true) [] [] 1 (+ 0) true (just tt)) ∈
  Menu.targets S.genericNext (withClient (C.client C.draining C.idle (C.quitMarker ∷ []) [] 1 (+ 0) true (just tt)))
quit-marker = Menu.target-complete {p = S.genericNext} {s = withClient (C.client C.draining C.idle (C.quitMarker ∷ []) [] 1 (+ 0) true (just tt))} (B.clientInternal (C.startMarker refl))

-- EOF may retain both Send slots after both Receive records have already appeared.
delayed-state : D.State
delayed-state = D.pair
  (C.client C.writingRequest (C.inspect (S.normal false)) [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 (S.selected (S.normal false)) 0 false)
  [] [] (just D.request) (just (D.reply (S.normal false))) nothing nothing

-- This prefix is a fresh restricted source execution, not a manually assembled target only.
both-delayed : B.Run S.genericNext D.initial
  (D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ []) delayed-state
both-delayed =
  B.internal (B.clientCallback (D.continue {k = + 1}) C.continueZero) $
  B.internal (B.clientInternal C.registerResponse) $
  B.internal (B.clientInternal (C.startResponse refl)) $
  B.internal (B.commitClient C.sentRequest) $
  B.internal (B.decodeServer (S.receiveRequest S.atFirst)) $
  B.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  B.internal (B.serverInternal S.admitted) $
  B.internal (B.serverInternal S.registered) $
  B.internal (B.serverInternal (S.claim refl)) $
  B.internal (B.serverCallback (B.allowNormal (here refl)) (S.choose refl refl)) $
  B.internal (B.commitServer (S.send refl)) $
  B.internal (B.decodeClient (C.receivedReply refl)) $
  B.visible (D.clientReceived (C.receivedReply refl)) B.stop

-- The generic replay interface admits the same exact finite prefix and target.
delayed-replay : Generic.Trace._⇒⟨_⟩_ D.initial
  (D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal false)) ∷ []) delayed-state
delayed-replay = Generic.from-run both-delayed

-- Hidden accessibility is available at an unfinished pending-hook state without a guessed cap.
delayed-accessible : Generic.Decision.τAcc delayed-state
delayed-accessible = Generic.tau-accessible delayed-state
