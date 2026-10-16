{-# OPTIONS --guardedness #-}

-- Concrete executions of the actual PTree, plus direct refusal checks.
module Cardano_network.BlockFetchPipeTests where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Data.Unit using (tt)
import Data.Sum
open import Data.Fin renaming (zero to fzero) using ()
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Base
open import Cardano_network.Data replayParams
open import Cardano_network.Net replayParams
open import Cardano_network.BlockFetch replayParams using (BFEv; apiBFev; sendBF; receiveBF; Rr)
open import Cardano_network.BlockFetchPipe replayParams
open import Semantics.LTS {E = BFEv} {I = ExtI BFEv} using (Event; evLabel)

-- An inhabited range suffices for control tests; no chain-content claim is made.
r : ChainRange
r = chainRange (point tt) (point tt)

-- Request API and ensuing wire output must both occur.
request : List Event
request = evLabel _ (apiBFev fzero lo sendBFRequestRange) r ∷
          evLabel _ (sendBF fzero lo) (tt , FromInitiator , tt , blockFetch (MsgRequestRange r)) ∷ []

-- A responder message delivered to the client.
recv : MessageBlockFetch → Event
recv m = evLabel _ (receiveBF fzero lo) (tt , FromResponder , tt , blockFetch m)

-- Successful session close includes the emitted wire Done.
finish : List Event
finish = evLabel _ (apiBFev fzero lo sendBFClientDone) tt ∷
         evLabel _ (sendBF fzero lo) (tt , FromInitiator , tt , blockFetch MsgClientDone) ∷ []

-- Bounded execution strategy: prefer the visible event, otherwise collect.
-- This is a test evaluator, not a complete trace decision procedure.
run : ℕ → PTree BFEv (ExtI BFEv) Rr → List Event → Bool
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

-- Two outstanding requests: one streaming batch, then NoBlocks, then close.
pipeline : List Event
pipeline = request ++ (recv MsgStartBatch ∷ []) ++ request ++
  (recv (MsgBlock tt) ∷ evLabel _ (apiBFev fzero lo recvBFBlock) tt ∷
   recv MsgBatchDone ∷ recv MsgNoBlocks ∷ []) ++ finish

-- Requests really can overlap a batch in the looped PTree.
two-ranges : run 80 (client 2 fzero lo) pipeline ≡ true
two-ranges = refl

-- The same overlap is unavailable with one sender credit.
one-credit : run 80 (client 1 fzero lo) pipeline ≡ false
one-credit = refl

-- A zero-credit client can still terminate.
zero-close : run 20 (client 0 fzero lo) finish ≡ true
zero-close = refl

-- A zero-credit client cannot send a request.
zero-request : run 20 (client 0 fzero lo) request ≡ false
zero-request = refl

-- Responses require an outstanding range.
unsolicited : run 20 (client 2 fzero lo) (recv MsgStartBatch ∷ []) ≡ false
unsolicited = refl

-- Block data cannot precede StartBatch.
early-block : run 30 (client 2 fzero lo) (request ++ (recv (MsgBlock tt) ∷ [])) ≡ false
early-block = refl

-- A streaming batch cannot be replaced with NoBlocks.
wrong-phase : run 40 (client 2 fzero lo)
  (request ++ (recv MsgStartBatch ∷ recv MsgNoBlocks ∷ [])) ≡ false
wrong-phase = refl

-- Outstanding responses prevent Done.
early-done : run 30 (client 2 fzero lo) (request ++ finish) ≡ false
early-done = refl

-- An empty batch is a legal control trace.
empty-batch : run 40 (client 1 fzero lo)
  (request ++ (recv MsgStartBatch ∷ recv MsgBatchDone ∷ []) ++ finish) ≡ true
empty-batch = refl

-- Completed but uncollected results still block new sends at capacity.
collection-credit : menu 1 fzero lo (pending [] waiting 1)
  (_ , apiBFev fzero lo sendBFRequestRange) r ≡ nothing
collection-credit = refl

-- Done also waits for collection, even when no response remains on the wire.
collection-done : menu 1 fzero lo (pending [] waiting 1)
  (_ , apiBFev fzero lo sendBFClientDone) tt ≡ nothing
collection-done = refl

-- Reject a responder message with an initiator payload tag.
wrong-agency : menu 2 fzero lo (pending (r ∷ []) waiting 0)
  (_ , receiveBF fzero lo) (tt , FromInitiator , tt , blockFetch MsgStartBatch) ≡ nothing
wrong-agency = refl

-- Reject a message for the opposite protocol direction on the same link.
wrong-direction : menu 2 fzero lo (pending (r ∷ []) waiting 0)
  (_ , receiveBF fzero hi) (tt , FromResponder , tt , blockFetch MsgStartBatch) ≡ nothing
wrong-direction = refl

-- Queue updates preserve arbitrary range values in FIFO order.
append-range : ∀ r₁ r₂ → menu 2 fzero lo (pending (r₁ ∷ []) waiting 0)
  (_ , apiBFev fzero lo sendBFRequestRange) r₂ ≡
  just (send fzero lo (MsgRequestRange r₂)
    (Data.Sum.inj₁ (pending (r₁ ∷ r₂ ∷ []) waiting 0)))
append-range r₁ r₂ = refl
