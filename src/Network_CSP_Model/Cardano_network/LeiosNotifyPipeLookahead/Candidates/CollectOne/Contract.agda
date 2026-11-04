{-# OPTIONS --safe #-}

-- Exact local wire observation and explicit finite endpoint outcomes, without a Haskell refinement claim.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Contract
  (Notification : Set) where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as S

-- The target wire observation retains direction, reply kind and the exact Notification value.
data Wire : Set where
  request quit done : Wire
  reply : S.Reply → Wire

-- Reply selection is a source callback, not a recorded wire send.
observe : S.Action → Maybe Wire
observe S.recvRequest = just request
observe S.recvQuit = just quit
observe (S.nextReply _) = nothing
observe (S.sendReply m) = just (reply m)
observe S.sendDone = just done

-- Erase only selection; poll/register/retire/flush are already silent in source runs.
wire : List S.Action → List Wire
wire [] = []
wire (a ∷ actions) with observe a
... | nothing = wire actions
... | just row = row ∷ wire actions

-- External runtime failures are labels, not successful protocol transitions.
data Fault : Set where
  callback channel traceHook canceledThread arithmetic : Fault

-- Admission rejection is distinguished from both graceful completion and external failure.
data Exit : Set where
  success rejected : Exit
  fault : Fault → Exit

-- A fault reports the end of a chosen endpoint prefix and does not synthesize Done.
data Permitted (s : S.State) : Exit → Set where
  completed : S.reader s ≡ S.closed → Permitted s success
  excessive : S.reader s ≡ S.failed → Permitted s rejected
  reported : (kind : Fault) → Permitted s (fault kind)

-- The source's modeled terminal states report success or its explicit excessive-request path.
outcome : S.State → Maybe Exit
outcome s with S.reader s
... | S.closed = just success
... | S.failed = just rejected
... | _ = nothing

-- A finite endpoint result retains the exact successful source prefix and its final state.
-- reported is an abstract fault allowance, not evidence of physical fault reachability or cleanup.
record End (contract : S.Contract) : Set where
  constructor ended
  field
    actions : List S.Action
    last : S.State
    prefix : S.Run contract S.initial actions last
    result : Exit
    justified : Permitted last result
