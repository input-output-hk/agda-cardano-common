{-# OPTIONS --guardedness #-}

-- Execute actual submitter/requester PTrees, including result collection.
module Cardano_network.TxSubmission2PipeTests where

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
open import Cardano_network.TxSubmission replayParams using (TSEv; apiTSev; sendTS; receiveTS; Rr)
open import Cardano_network.TxSubmission2Pipe replayParams
open import Semantics.LTS {E = TSEv} {I = ExtI TSEv} using (Event; evLabel)

-- Requester receives submitter-role messages.
recv : MessageTxSubmission2 → Event
recv m = evLabel _ (receiveTS fzero lo) (tt , FromInitiator , tt , txSubmission m)

-- Requester's initial handshake.
begin : List Event
begin = recv MsgTSInit ∷ []

-- Issue a nonblocking ID request through the API and then the wire.
idsRequest : List Event
idsRequest = evLabel _ (apiTSev fzero lo sendTSRequestTxIdsPipelined) (0 , 1) ∷
  evLabel _ (sendTS fzero lo) (tt , FromResponder , tt , txSubmission (MsgTSRequestTxIds NonBlocking 0 1)) ∷ []

-- Issue a transaction-body request through both interfaces.
txsRequest : List Event
txsRequest = evLabel _ (apiTSev fzero lo sendTSRequestTxsPipelined) (tt ∷ []) ∷
  evLabel _ (sendTS fzero lo) (tt , FromResponder , tt , txSubmission (MsgTSRequestTxs (tt ∷ []))) ∷ []

-- A blocking ID request uses the synchronous branch.
blockingRequest : List Event
blockingRequest = evLabel _ (apiTSev fzero lo sendTSRequestTxIdsBlocking) (0 , 1) ∷
  evLabel _ (sendTS fzero lo) (tt , FromResponder , tt , txSubmission (MsgTSRequestTxIds Blocking 0 1)) ∷ []

-- Receiving IDs includes the application handoff before loop-back.
idsReply : List Event
idsReply = recv (MsgTSReplyTxIds (tt ∷ [])) ∷
  evLabel _ (apiTSev fzero lo recvTSReplyTxIds) (tt ∷ []) ∷ []

-- A transaction reply can be empty, representing implicit discard.
txsReply : List Event
txsReply = recv (MsgTSReplyTxs []) ∷ evLabel _ (apiTSev fzero lo recvTSReplyTxs) [] ∷ []

-- Deterministic test strategy: take a visible offer, otherwise collect.
run : ℕ → PTree TSEv (ExtI TSEv) Rr → List Event → Bool
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

-- Mixed pipeline replies are consumed FIFO before entering a blocking call.
rounds : List Event
rounds = begin ++ idsRequest ++ txsRequest ++ idsReply ++ txsReply ++ blockingRequest ++ (recv MsgTSDone ∷ [])

-- Two outstanding requests with different response families execute.
two-credits : run 100 (server 2 fzero lo) rounds ≡ true
two-credits = refl

-- A single sender credit does not permit that overlap.
one-credit : run 100 (server 1 fzero lo) rounds ≡ false
one-credit = refl

-- Collection makes one sender credit reusable.
refill : run 100 (server 1 fzero lo) (begin ++ idsRequest ++ idsReply ++ txsRequest ++ txsReply) ≡ true
refill = refl

-- A later transaction response cannot overtake the oldest ID response.
fifo : run 50 (server 2 fzero lo) (begin ++ idsRequest ++ txsRequest ++ txsReply) ≡ false
fifo = refl

-- Blocking requests cannot overlap unanswered asynchronous requests.
blocking-drain : run 50 (server 2 fzero lo) (begin ++ idsRequest ++ blockingRequest) ≡ false
blocking-drain = refl

-- Zero asynchronous capacity still permits a synchronous blocking close.
zero-blocking : run 50 (server 0 fzero lo) (begin ++ blockingRequest ++ (recv MsgTSDone ∷ [])) ≡ true
zero-blocking = refl

-- An empty blocking ID reply is not a valid response.
empty-blocking : run 50 (server 1 fzero lo) (begin ++ blockingRequest ++ (recv (MsgTSReplyTxIds []) ∷ [])) ≡ false
empty-blocking = refl

-- The submitter auto-sends Init before receiving a blocking request.
clientBegin : List Event
clientBegin = evLabel _ (sendTS fzero lo) (tt , FromInitiator , tt , txSubmission MsgTSInit) ∷
  evLabel _ (receiveTS fzero lo) (tt , FromResponder , tt , txSubmission (MsgTSRequestTxIds Blocking 0 1)) ∷
  evLabel _ (apiTSev fzero lo recvTSRequestTxIds) (Blocking , 0 , 1) ∷ []

-- The stricter submitter refuses an empty blocking list from its application.
client-empty : run 50 (client fzero lo) (clientBegin ++ (evLabel _ (apiTSev fzero lo sendTSReplyTxIds) [] ∷ [])) ≡ false
client-empty = refl

-- The submitter can terminate only from the blocking request branch.
client-done : run 50 (client fzero lo) (clientBegin ++
  (evLabel _ (apiTSev fzero lo sendTSDone) tt ∷
   evLabel _ (sendTS fzero lo) (tt , FromInitiator , tt , txSubmission MsgTSDone) ∷ [])) ≡ true
client-done = refl
