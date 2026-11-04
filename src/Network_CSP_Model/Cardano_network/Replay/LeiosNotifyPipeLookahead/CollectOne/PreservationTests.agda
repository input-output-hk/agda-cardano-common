{-# OPTIONS --safe #-}

-- Inhabited transport in both directions and limits of stronger bookkeeping claims.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.PreservationTests where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as B
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Contract Bool as W
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Forward Bool as F
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Backward Bool as R
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Preservation Bool as P
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CollectOne.ContractTests as T
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Tests as Old

-- A fresh early hit becomes one retained ghost completion in the baseline before Quit.
one-extra-before-quit : proj₁ (F.from-initial T.hit-reachable) ≡ 1
one-extra-before-quit = refl

-- The exact three-request source action sequence is transported without dropping selection data.
selected-source-in-baseline : P.BaselineSource C.nodeNext
  (C.recvRequest ∷ C.nextReply (C.normal true) ∷ C.sendReply (C.normal true) ∷ C.recvRequest ∷
   C.nextReply (C.normal false) ∷ C.recvRequest ∷ C.recvQuit ∷
   C.sendReply (C.normal false) ∷ C.sendReply C.canceled ∷ C.sendDone ∷ [])
selected-source-in-baseline = P.candidate-in-baseline (_ , T.selected-hit-closes)

-- The exact normal values and cancellation stay in the same local wire order.
selected-wire-in-baseline : P.BaselineWire C.nodeNext
  (W.request ∷ W.reply (C.normal true) ∷ W.request ∷ W.request ∷ W.quit ∷
   W.reply (C.normal false) ∷ W.reply C.canceled ∷ W.done ∷ [])
selected-wire-in-baseline = P.candidate-wire-in-baseline (_ , _ , T.selected-hit-closes , T.selected-hit-wire)

-- Generic pre-Quit cancellation is preserved under its actual callback contract.
generic-in-baseline : P.BaselineSource C.genericNext
  (C.recvRequest ∷ C.nextReply C.canceled ∷ C.sendReply C.canceled ∷ [])
generic-in-baseline = P.candidate-in-baseline (_ , T.generic-canceled-prefix)

-- A previously checked late-normal baseline fixture has a candidate realization too.
old-late-normal-in-candidate : P.CandidateSource C.nodeNext
  (C.recvRequest ∷ C.nextReply (C.normal true) ∷ C.recvQuit ∷ C.sendReply (C.normal true) ∷ C.sendDone ∷ [])
old-late-normal-in-candidate = P.baseline-in-candidate (_ , Old.selected-before-quit)

-- A completed first baseline job remains retained when a second request is admitted.
baseline-two : B.Run B.nodeNext B.initial
  (B.recvRequest ∷ B.nextReply (B.normal true) ∷ B.sendReply (B.normal true) ∷
   B.recvRequest ∷ B.recvQuit ∷ B.sendReply B.canceled ∷ B.sendDone ∷ [])
  (B.state B.closed 0 B.idle 0 true)
baseline-two = B.visible (B.receiveRequest B.atFirst) $ B.internal B.admitted $
  B.internal B.registered $ B.internal (B.claim refl) $ B.visible (B.choose refl refl) $
  B.visible (B.send refl) $ B.internal (B.retire refl) $
  B.visible (B.receiveRequest B.atNext) $ B.internal B.admitted $ B.internal B.registered $
  B.visible (B.receiveQuit B.atNext) $ B.internal B.setQuit $ B.internal (B.claim refl) $
  B.internal (B.cancel refl) $ B.visible (B.send refl) $ B.internal (B.retire refl) $
  B.internal B.flush $ B.internal B.flush $ B.internal B.drained $ B.visible B.finish B.stop

-- Alignment with a closed zero-count baseline identifies the exact candidate closed state.
closed-target : ∀ {s} → R.Related s (B.state B.closed 0 B.idle 0 true) →
  s ≡ C.state C.closed 0 C.idle 0 true
closed-target (R.aligned z≤n) = refl

-- The reverse simulation produces a real successful candidate run for this baseline fixture.
candidate-two : C.Run C.nodeNext C.initial
  (C.recvRequest ∷ C.nextReply (C.normal true) ∷ C.sendReply (C.normal true) ∷
   C.recvRequest ∷ C.recvQuit ∷ C.sendReply C.canceled ∷ C.sendDone ∷ [])
  (C.state C.closed 0 C.idle 0 true)
candidate-two with R.from-initial baseline-two
... | target , execution , related with closed-target related
...   | refl = execution

-- Count early collections in these proof objects, not elapsed time or allocations.
early : ∀ {p s actions t} → C.Run p s actions t → ℕ
early C.stop = 0
early (C.internal C.pollHit rest) = suc (early rest)
early (C.internal _ rest) = early rest
early (C.visible _ rest) = early rest

-- Count only post-Quit candidate flushes, independently of early collection.
shutdown : ∀ {p s actions t} → C.Run p s actions t → ℕ
shutdown C.stop = 0
shutdown (C.internal C.flush rest) = suc (shutdown rest)
shutdown (C.internal _ rest) = shutdown rest
shutdown (C.visible _ rest) = shutdown rest

-- Source/wire equivalence does not require preserving the location of completion work.
one-early-one-final : early candidate-two ≡ 1 × shutdown candidate-two ≡ 1
one-early-one-final = refl , refl

-- Modeled excessive-request paths are included even though they are not graceful closes.
rejection-in-baseline : P.BaselineSource C.nodeNext (C.recvRequest ∷ [])
rejection-in-baseline = P.candidate-in-baseline (_ , T.rejected-run)

-- Baseline collection occurs only in its post-Quit flush constructors.
baseline-shutdown : ∀ {p s actions t} → B.Run p s actions t → ℕ
baseline-shutdown B.stop = 0
baseline-shutdown (B.internal B.flush rest) = suc (baseline-shutdown rest)
baseline-shutdown (B.internal _ rest) = baseline-shutdown rest
baseline-shutdown (B.visible _ rest) = baseline-shutdown rest

-- Identical visible actions coexist with two baseline shutdown flushes versus one candidate flush.
different-shutdown-work : baseline-shutdown baseline-two ≡ 2 × shutdown candidate-two ≡ 1
different-shutdown-work = refl , refl
