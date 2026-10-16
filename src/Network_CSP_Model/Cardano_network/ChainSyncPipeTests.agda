{-# OPTIONS --guardedness #-}

-- Evaluate the real looped PTree, including API handoffs and collection.
module Cardano_network.ChainSyncPipeTests where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
open import Data.Fin renaming (zero to fzero) using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Base
open import Cardano_network.Data replayParams
open import Cardano_network.Net replayParams
open import Cardano_network.ChainSync replayParams using (CSEv; apiCSev; sendCS; receiveCS; Rr)
open import Cardano_network.ChainSyncPipe replayParams
open import Semantics.LTS {E = CSEv} {I = ExtI CSEv} using (Event; evLabel)

-- Issue one RequestNext via the application and wire interfaces.
request : List Event
request = evLabel _ (apiCSev fzero lo sendCSRequestNext) tt ∷
  evLabel _ (sendCS fzero lo) (tt , FromInitiator , tt , chainSync MsgCSRequestNext) ∷ []

-- Deliver a responder message to the client.
recv : MessageChainSync → Event
recv m = evLabel _ (receiveCS fzero lo) (tt , FromResponder , tt , chainSync m)

-- Complete one response, including its application handoff.
roll : List Event
roll = recv (MsgCSRollForward (header tt) (tip tt)) ∷
  evLabel _ (apiCSev fzero lo recvCSRollforward) (header tt , tip tt) ∷ []

-- Intersection is available only when all previous results are collected.
intersection : List Event
intersection = evLabel _ (apiCSev fzero lo sendCSFindIntersect) [] ∷
  evLabel _ (sendCS fzero lo) (tt , FromInitiator , tt , chainSync (MsgCSFindIntersect [])) ∷
  recv (MsgCSIntersectNotFound (tip tt)) ∷
  evLabel _ (apiCSev fzero lo recvCSIntersectNotFound) (tip tt) ∷ []

-- Close the session through both API and wire events.
finish : List Event
finish = evLabel _ (apiCSev fzero lo sendCSDone) tt ∷
  evLabel _ (sendCS fzero lo) (tt , FromInitiator , tt , chainSync MsgCSDone) ∷ []

-- Test evaluator: take the supplied event if offered, otherwise collect.
run : ℕ → PTree CSEv (ExtI CSEv) Rr → List Event → Bool
run n t [] = true
run zero t (_ ∷ _) = false
run (suc n) t es@(evLabel A e x ∷ rest) with PTree.force t
... | ret _ = false
... | sil u = run n u es
... | react v τ with v (A , e) x
...   | just u = run n u rest
...   | nothing with τ (A , base e) x
...     | just u = run n u es
...     | nothing = false

-- AwaitReply does not prevent sending a second request with available credit.
rounds : List Event
rounds = request ++ (recv MsgCSAwaitReply ∷ []) ++ request ++ roll ++ roll ++ intersection ++ finish

-- Two requests overlap in the PTree and are drained before intersection.
two-credits : run 100 (client 2 fzero lo) rounds ≡ true
two-credits = refl

-- The same overlap exceeds a one-credit bound.
one-credit : run 100 (client 1 fzero lo) rounds ≡ false
one-credit = refl

-- Completed results must be silently collected to allow a refill.
refill : run 100 (client 1 fzero lo) (request ++ roll ++ request ++ roll ++ finish) ≡ true
refill = refl

-- The same request cannot receive AwaitReply twice.
repeated-await : run 40 (client 2 fzero lo) (request ++ (recv MsgCSAwaitReply ∷ recv MsgCSAwaitReply ∷ [])) ≡ false
repeated-await = refl

-- Intersection is exclusive, even if one pipeline credit is unused.
busy-intersection : run 40 (client 2 fzero lo) (request ++ intersection) ≡ false
busy-intersection = refl

-- A zero bound still permits intersection and close.
zero-intersection : run 40 (client 0 fzero lo) (intersection ++ finish) ≡ true
zero-intersection = refl

-- A zero bound prevents RequestNext.
zero-request : run 20 (client 0 fzero lo) request ≡ false
zero-request = refl

-- Replies must carry responder agency.
wrong-agency : run 40 (client 1 fzero lo) (request ++
  (evLabel _ (receiveCS fzero lo) (tt , FromInitiator , tt , chainSync MsgCSAwaitReply) ∷ [])) ≡ false
wrong-agency = refl

-- Replies from a different endpoint direction cannot consume this request.
wrong-endpoint : run 40 (client 1 fzero lo) (request ++
  (evLabel _ (receiveCS fzero hi) (tt , FromResponder , tt , chainSync MsgCSAwaitReply) ∷ [])) ≡ false
wrong-endpoint = refl
