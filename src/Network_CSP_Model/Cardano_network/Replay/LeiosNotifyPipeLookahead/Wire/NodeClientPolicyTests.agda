{-# OPTIONS --safe #-}

-- Local fixed-node-client policy regressions; no full NodeDriver input claim.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientPolicyTests where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model ℕ as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel ℕ ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel ℕ ⊤ as N
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client ℕ as W
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodeClientPolicy ℕ Nat._≟_ as P

-- Continuing after a Canceled and a subsequent reply needs successful Canceled handling.
separation : List W.Wire
separation = W.request ∷ W.request ∷ W.reply S.canceled ∷
  W.reply (S.normal 73) ∷ W.request ∷ []

-- The generic successful-handler quotient admits this exact small sequence.
generic-separation : W.HasTrace W.initial separation
generic-separation = W.Open 1 ,
  W.step W.sendRequest (W.step W.sendRequest
    (W.step W.receiveReply (W.step W.receiveReply
      (W.step W.sendRequest W.stop))))

-- Exhaustive local policy search excludes every hidden schedule for the same rows.
node-separation : P.SourceTrace separation → ⊥
node-separation = toWitnessFalse {a? = P.decide-source separation} tt

-- Inspecting Canceled can wait until stop publication, before the delayed Quit hook.
canceled-before-quit : P.SourceTrace
  (W.reply S.canceled ∷ W.request ∷ W.quit ∷ W.done ∷ [])
canceled-before-quit = toWitness {a? = P.decide-source _} tt

-- An explicit source path ends in a real failure rather than relying on an EOF target choice.
fault-client : C.State
fault-client = C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) false nothing

-- Forecast success and handler rejection are source inputs erased from the wire prefix.
fault-actions : List N.Action
fault-actions = N.forecastAllows ∷ N.wire C.sendRequest ∷
  N.wire (C.recvReply S.canceled) ∷ N.handlerRejectedCancel ∷ []

-- Fresh request registration and a false stop snapshot lead to the explicit fault state.
fault-run : N.Run N.initial fault-actions (N.unexpectedCancel fault-client)
fault-run =
  N.visible (N.continueAtDepth C.continueZero) $
  N.internal (N.schedule C.registerResponse) $
  N.internal (N.schedule (C.startResponse refl)) $
  N.visible (N.wireRecord N.request C.sentRequest) $
  N.visible (N.wireRecord N.reply (C.receivedReply refl)) $
  N.internal (N.schedule (C.keepReply refl)) $
  N.visible (N.rejectedCancel refl refl) N.stop

-- The fault witness retains exactly the two driver rows; callbacks and the fault are erased.
fault-observation : P.wire fault-actions ≡ (W.request ∷ W.reply S.canceled ∷ [])
fault-observation = refl

-- This accepted prefix carries a chosen fault-ending witness, not successful completion.
fault-source : P.SourceTrace (W.request ∷ W.reply S.canceled ∷ [])
fault-source = fault-actions , N.unexpectedCancel fault-client , fault-run , fault-observation

-- Source/replay transport preserves this explicit abnormal endpoint independently of the decider.
fault-replay-target : P.Trace._⇒⟨_⟩_ P.initial
  (W.request ∷ W.reply S.canceled ∷ []) (N.unexpectedCancel fault-client)
fault-replay-target = P.from-source fault-run
