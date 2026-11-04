{-# OPTIONS --safe #-}

-- Inhabited candidate contracts and negative guard examples; not a Haskell/CSP preservation proof.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.ContractTests where

open import Data.Bool using (Bool; false; true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (z≤n; s≤s)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Contract Bool as C

-- A first request skips the zero-index poll and registers exactly one response job.
first-registered : S.Run S.nodeNext S.initial (S.recvRequest ∷ [])
  (S.state S.awaitNext 1 S.idle 0 false)
first-registered = S.visible (S.receiveRequest S.atFirst) $
  S.internal S.admitted $ S.internal (S.inspectZero refl) $
  S.internal S.registered S.stop

-- A sent-but-unretired old job can coexist with the next admitted request at poll.
sent-at-poll : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷ [])
  (S.state S.poll 0 S.sent 0 false)
sent-at-poll = S.append first-registered $
  S.internal (S.claim refl) $ S.visible (S.choose refl refl) $
  S.visible (S.send refl) $ S.visible (S.receiveRequest S.atNext) $
  S.internal S.admitted $ S.internal (S.inspectPositive (s≤s z≤n)) S.stop

-- Before retirement the zero-completed transaction misses and leaves the active job intact.
miss-before-retire : S.Run S.nodeNext (S.state S.poll 0 S.sent 0 false) []
  (S.state S.register 0 S.idle 1 false)
miss-before-retire = S.internal (S.pollMiss (s≤s z≤n)) $
  S.internal (S.retire refl) S.stop

-- Retirement first makes a completion ready, so the same poll must consume it.
retire-before-hit : S.Run S.nodeNext (S.state S.poll 0 S.sent 0 false) []
  (S.state S.register 0 S.idle 0 false)
retire-before-hit = S.internal (S.retire refl) $ S.internal S.pollHit S.stop

-- Ready completions cannot be skipped by an unguarded optional alternative.
no-miss-when-ready : S.Tau (S.state S.poll 0 S.idle 1 false)
  (S.state S.register 0 S.idle 1 false) → ⊥
no-miss-when-ready ()

-- A positive registered index cannot take the zero-index inspection branch.
no-positive-skip : S.Tau (S.state S.inspect 0 S.sent 0 false)
  (S.state S.register 0 S.sent 0 false) → ⊥
no-positive-skip (S.inspectZero ())

-- A zero-index state does not contain an old job eligible for a poll.
no-zero-poll : S.Tau (S.state S.inspect 0 S.idle 0 false)
  (S.state S.poll 0 S.idle 0 false) → ⊥
no-zero-poll (S.inspectPositive ())

-- The current request is still owed but unregistered throughout polling.
poll-keeps-current : S.unregistered S.poll ≡ 1
poll-keeps-current = refl

-- A completed token and a held selected reply are independent resources.
hit-keeps-selected : S.Tau (S.state S.poll 0 (S.selected (S.normal true)) 1 false)
  (S.state S.register 0 (S.selected (S.normal true)) 0 false)
hit-keeps-selected = S.pollHit

-- One request witnesses the selected ordinary reply surviving true Quit publication and clean close.
normal-after-flag : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.recvQuit ∷ S.sendReply (S.normal true) ∷ S.sendDone ∷ [])
  (S.state S.closed 0 S.idle 0 true)
normal-after-flag = S.append first-registered $
  S.internal (S.claim refl) $ S.visible (S.choose refl refl) $
  S.visible (S.receiveQuit S.atNext) $ S.internal S.setQuit $
  S.visible (S.send refl) $ S.internal (S.retire refl) $
  S.internal S.flush $ S.internal S.drained $ S.visible S.finish S.stop

-- Wire projection removes only callback selection and retains the exact ordinary payload.
normal-wire : C.wire
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.recvQuit ∷ S.sendReply (S.normal true) ∷ S.sendDone ∷ []) ≡
  C.request ∷ C.quit ∷ C.reply (S.normal true) ∷ C.done ∷ []
normal-wire = refl

-- This is a model endpoint success witness, without a composed-system or Haskell claim.
normal-end : C.End S.nodeNext
normal-end = C.ended _ _ normal-after-flag C.success (C.completed refl)

-- A claimed reply with no next result can still cancel after true Quit.
blocked-next-cancels : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.recvQuit ∷ S.sendReply S.canceled ∷ S.sendDone ∷ [])
  (S.state S.closed 0 S.idle 0 true)
blocked-next-cancels = S.append first-registered $
  S.internal (S.claim refl) $ S.visible (S.receiveQuit S.atNext) $
  S.internal S.setQuit $ S.internal (S.cancel refl) $
  S.visible (S.send refl) $ S.internal (S.retire refl) $
  S.internal S.flush $ S.internal S.drained $ S.visible S.finish S.stop

-- Admission rejection never reaches inspection or registers this request.
rejected-run : S.Run S.nodeNext S.initial (S.recvRequest ∷ [])
  (S.state S.failed 0 S.idle 0 false)
rejected-run = S.visible (S.receiveRequest S.atFirst) $
  S.internal S.excessive $ S.internal S.abort S.stop

-- The rejected path has a distinct modeled endpoint result.
rejected-end : C.End S.nodeNext
rejected-end = C.ended _ _ rejected-run C.rejected (C.excessive refl)

-- External callback failure records a valid fresh prefix, not a graceful close.
callback-end : C.End S.nodeNext
callback-end = C.ended (S.recvRequest ∷ []) (S.state S.admit 0 S.idle 0 false)
  (S.visible (S.receiveRequest S.atFirst) S.stop) (C.fault C.callback) (C.reported C.callback)

-- Labeling this fault adds no synthetic Done or terminal wire event to the prefix.
callback-wire : C.wire (C.End.actions callback-end) ≡ C.request ∷ []
callback-wire = refl

-- An unfinished admission prefix cannot be relabeled as a successful endpoint return.
no-early-success : C.Permitted (S.state S.admit 0 S.idle 0 false) C.success → ⊥
no-early-success (C.completed ())

-- Both poll outcomes leave the poll phase instead of retrying optional collection.
no-repoll : ∀ {w sender c q w′ sender′ c′ q′} →
  S.Tau (S.state S.register w sender c q) (S.state S.poll w′ sender′ c′ q′) → ⊥
no-repoll ()

-- A zero old-job count after a hit does not authorize Done for the unregistered current request.
no-done-with-current : ∀ {t} →
  S.Step S.nodeNext (S.state S.register 0 S.idle 0 false) S.sendDone t → ⊥
no-done-with-current ()

-- This fresh positive-index poll hit removes only the old completed request.
hit-reachable : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷ [])
  (S.state S.register 0 S.idle 0 false)
hit-reachable = S.append sent-at-poll retire-before-hit

-- The remaining current request still registers and owes one Canceled response before Done.
hit-then-quit : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷
   S.recvQuit ∷ S.sendReply S.canceled ∷ S.sendDone ∷ [])
  (S.state S.closed 0 S.idle 0 true)
hit-then-quit = S.append hit-reachable $
  S.internal S.registered $ S.visible (S.receiveQuit S.atNext) $
  S.internal S.setQuit $ S.internal (S.claim refl) $ S.internal (S.cancel refl) $
  S.visible (S.send refl) $ S.internal (S.retire refl) $ S.internal S.flush $
  S.internal S.drained $ S.visible S.finish S.stop

-- A delayed first retirement makes a ready old token coexist freshly with the second selected payload.
selected-hit-reachable : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷
   S.nextReply (S.normal false) ∷ S.recvRequest ∷ [])
  (S.state S.poll 0 (S.selected (S.normal false)) 1 false)
selected-hit-reachable = S.append (S.append sent-at-poll miss-before-retire) $
  S.internal S.registered $ S.internal (S.claim refl) $ S.visible (S.choose refl refl) $
  S.visible (S.receiveRequest S.atNext) $ S.internal S.admitted $
  S.internal (S.inspectPositive (s≤s z≤n)) S.stop

-- Early collection leaves that exact selected reply intact across true Quit and still owes the third cancellation.
selected-hit-closes : S.Run S.nodeNext S.initial
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷
   S.nextReply (S.normal false) ∷ S.recvRequest ∷ S.recvQuit ∷
   S.sendReply (S.normal false) ∷ S.sendReply S.canceled ∷ S.sendDone ∷ [])
  (S.state S.closed 0 S.idle 0 true)
selected-hit-closes = S.append selected-hit-reachable $
  S.internal S.pollHit $ S.internal S.registered $
  S.visible (S.receiveQuit S.atNext) $ S.internal S.setQuit $
  S.visible (S.send refl) $ S.internal (S.retire refl) $
  S.internal (S.claim refl) $ S.internal (S.cancel refl) $
  S.visible (S.send refl) $ S.internal (S.retire refl) $
  S.internal S.flush $ S.internal S.flush $ S.internal S.drained $
  S.visible S.finish S.stop

-- Callback erasure preserves the differing normal payloads and the final cancellation in exact order.
selected-hit-wire : C.wire
  (S.recvRequest ∷ S.nextReply (S.normal true) ∷ S.sendReply (S.normal true) ∷ S.recvRequest ∷
   S.nextReply (S.normal false) ∷ S.recvRequest ∷ S.recvQuit ∷
   S.sendReply (S.normal false) ∷ S.sendReply S.canceled ∷ S.sendDone ∷ []) ≡
  C.request ∷ C.reply (S.normal true) ∷ C.request ∷ C.request ∷ C.quit ∷
  C.reply (S.normal false) ∷ C.reply S.canceled ∷ C.done ∷ []
selected-hit-wire = refl

-- The generic callback contract can freshly choose Canceled before any Quit.
generic-canceled-prefix : S.Run S.genericNext S.initial
  (S.recvRequest ∷ S.nextReply S.canceled ∷ S.sendReply S.canceled ∷ [])
  (S.state S.awaitNext 0 S.sent 0 false)
generic-canceled-prefix = S.visible (S.receiveRequest S.atFirst) $
  S.internal S.admitted $ S.internal (S.inspectZero refl) $ S.internal S.registered $
  S.internal (S.claim refl) $ S.visible (S.choose refl refl) $ S.visible (S.send refl) S.stop

-- The node queue contract cannot supply that canceled callback result while the flag is false.
node-no-canceled-next : ∀ {r w c t} →
  S.Step S.nodeNext (S.state r w S.claimed c false) (S.nextReply S.canceled) t → ⊥
node-no-canceled-next (S.choose _ ())

-- Once true Quit is published, neither callback contract can select a new ordinary reply.
no-normal-selection-after-flag : ∀ {p r w c t} →
  S.Step p (S.state r w S.claimed c true) (S.nextReply (S.normal true)) t → ⊥
no-normal-selection-after-flag ()
