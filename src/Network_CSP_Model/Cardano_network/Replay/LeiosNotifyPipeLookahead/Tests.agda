{-# OPTIONS --safe #-}

-- Inhabited source schedules and negative controls for the operational server.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Tests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Bool
import Cardano_network.LeiosNotifyPipeLookahead.Properties Bool as P
open Executable Bool._≟_
open import Cardano_network.LeiosNotifyPipeLookahead.Enumeration Bool
  using (target-sound; target-complete)

-- A selected notification survives a later reader Quit and true shutdown flag.
selected-before-quit : Run nodeNext initial
  (recvRequest ∷ nextReply (normal true) ∷ recvQuit ∷ sendReply (normal true) ∷ sendDone ∷ [])
  (state closed 0 idle 0 true)
selected-before-quit =
  visible (receiveRequest atFirst) $
  internal admitted $
  internal registered $
  internal (claim refl) $
  visible (choose refl refl) $
  visible (receiveQuit atNext) $
  internal setQuit $
  visible (send refl) $
  internal (retire refl) $
  internal flush $
  internal drained $
  visible finish stop

-- More than one normal reply can follow the Quit record before the flag is set.
two-normal-after-quit : Run nodeNext initial
  (recvRequest ∷ recvRequest ∷ recvQuit ∷
   nextReply (normal true) ∷ sendReply (normal true) ∷
   nextReply (normal false) ∷ sendReply (normal false) ∷ sendDone ∷ [])
  (state closed 0 idle 0 true)
two-normal-after-quit =
  visible (receiveRequest atFirst) $
  internal admitted $
  internal registered $
  visible (receiveRequest atNext) $
  internal admitted $
  internal registered $
  visible (receiveQuit atNext) $
  internal (claim refl) $
  visible (choose refl refl) $
  visible (send refl) $
  internal (retire refl) $
  internal (claim refl) $
  visible (choose refl refl) $
  visible (send refl) $
  internal (retire refl) $
  internal setQuit $
  internal flush $
  internal flush $
  internal drained $
  visible finish stop

-- After flag publication, the responder can select cancellation without next.
canceled-drain : Run nodeNext initial
  (recvRequest ∷ recvQuit ∷ sendReply canceled ∷ sendDone ∷ [])
  (state closed 0 idle 0 true)
canceled-drain =
  visible (receiveRequest atFirst) $
  internal admitted $
  internal registered $
  visible (receiveQuit atNext) $
  internal setQuit $
  internal (claim refl) $
  internal (cancel refl) $
  visible (send refl) $
  internal (retire refl) $
  internal flush $
  internal drained $
  visible finish stop

-- The source's excessive-request path aborts rather than fabricating wire Done.
excessive-request : Run nodeNext initial (recvRequest ∷ []) (state failed 0 idle 0 false)
excessive-request = visible (receiveRequest atFirst) (internal excessive (internal abort stop))

-- Equal credit counts cannot justify replacing a previously selected payload.
wrong-selected-payload : next nodeNext (state awaitNext 0 (selected (normal true)) 0 false)
  (sendReply (normal false)) ≡ nothing
wrong-selected-payload = refl

-- Reading continues while a reply is selected and pending.
pending-receives-quit : next nodeNext (state awaitNext 0 (selected (normal true)) 0 false)
  recvQuit ≡ just (state signalQuit 0 (selected (normal true)) 0 false)
pending-receives-quit = refl

-- Done cannot precede the completion-counter flush.
early-done : next nodeNext (state flushing 0 idle 1 true) sendDone ≡ nothing
early-done = refl

-- Node next never supplies a normal application cancellation.
node-next-no-canceled : next nodeNext (state awaitNext 0 claimed 0 false)
  (nextReply canceled) ≡ nothing
node-next-no-canceled = refl

-- The generic callback type does permit cancellation before Quit.
generic-next-canceled : next genericNext (state awaitNext 0 claimed 0 false)
  (nextReply canceled) ≡ just (state awaitNext 0 (selected canceled) 0 false)
generic-next-canceled = refl

-- A true flag prevents further application selection even for normal replies.
flag-blocks-next : next nodeNext (state flushing 0 claimed 0 true)
  (nextReply (normal true)) ≡ nothing
flag-blocks-next = refl

-- New requests and repeated Quit are unavailable immediately after the Quit record.
no-request-after-quit : next nodeNext (state signalQuit 0 idle 0 false) recvRequest ≡ nothing
no-request-after-quit = refl

-- A small concrete witness already exceeds a bound of one completion token.
two-completed-with-zero-owed : Σ[ es ∈ List Action ]
  (Run nodeNext initial es (P.ready 2) × owed (P.ready 2) ≡ 0)
two-completed-with-zero-owed with P.completed-reachable true 1
... | es , run = es , run , refl

-- Even these zero-owed completions each require a separate flush at shutdown.
two-flushes : P.flushCount (P.shutdown {nodeNext} 2) ≡ 2
two-flushes = P.shutdown-count {nodeNext} 2
