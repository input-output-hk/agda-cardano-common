{-# OPTIONS --safe #-}

-- Product witnesses, role dispatch, independent bounds and session isolation.
module Cardano_network.Replay.BlockFetchInterleavedTests where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary.Decidable using (toWitness; False)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Semantics.Replay using (module Traces)
open import Cardano_network.Replay.Sessions
open import Cardano_network.Replay.SessionReport using (reportBlockFetch; reportWithDepths; reportWithDepth)
import Cardano_network.Replay.BlockFetchClientSession as B
import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosNotifySession as N

-- All three protocols and both roles coexist in one product.
manifest : List Session
manifest = blockfetch client ∷ blockfetch server ∷ fetch client ∷ fetch server ∷ notify client ∷ notify server ∷ []

-- Select the BlockFetch client component.
bc : B.E → Events manifest
bc = inj₁

-- Select the BlockFetch server component.
bs : B.E → Events manifest
bs e = inj₂ (inj₁ e)

-- Select the LeiosFetch client component.
fc : F.E → Events manifest
fc e = inj₂ (inj₂ (inj₁ e))

-- Select the LeiosFetch server component.
fs : F.E → Events manifest
fs e = inj₂ (inj₂ (inj₂ (inj₁ e)))

-- Select the Notify client component.
nc : N.E → Events manifest
nc e = inj₂ (inj₂ (inj₂ (inj₂ (inj₁ e))))

-- Select the Notify server component.
ns : N.E → Events manifest
ns e = inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ e)))))

-- Interleave two outstanding BF client ranges with a sequential BF server,
-- Fetch's two roles and Notify's two roles; all sessions remain independent.
rounds : List (Events manifest)
rounds = bc (Send , B.request) ∷ bs (Recv , B.request) ∷
  fc (Send , F.MsgLeiosBlockRequest 7 3) ∷ ns (Recv , N.RequestNext) ∷
  bc (Send , B.request) ∷ nc (Send , N.RequestNext) ∷
  fs (Recv , F.MsgLeiosBlockRequest 8 4) ∷ bs (Send , B.startBatch) ∷
  bc (Recv , B.noBlocks) ∷ ns (Send , N.Votes []) ∷
  bs (Send , B.block) ∷ fc (Recv , F.MsgLeiosBlock 7 20) ∷
  nc (Recv , N.Votes []) ∷ fs (Send , F.MsgLeiosBlock 8 20) ∷
  bc (Recv , B.startBatch) ∷ bs (Send , B.batchDone) ∷
  bc (Recv , B.batchDone) ∷ bc (Send , B.clientDone) ∷
  bs (Recv , B.clientDone) ∷ []

-- Acceptance contains an actual run of the heterogeneous product model.
rounds-run : Traces.HasTrace (modelWithDepths 1 1 2 manifest) (initial manifest) rounds
rounds-run = toWitness {a? = checkWithDepths 1 1 2 manifest rounds} tt

-- Reducing only BlockFetch's depth rejects the overlapping client requests.
too-shallow : False (checkWithDepths 1 1 1 manifest rounds)
too-shallow = tt

-- Shared dispatch selects the client from the header.
shared-client : reportBlockFetch 2 "role client\nSend RequestRange\nSend RequestRange\n" ≡ "accepted (2 events, 1 sessions)"
shared-client = refl

-- A zero client bound does not disable a sequential server.
shared-server : reportBlockFetch 0 "role server\nRecv RequestRange\nSend NoBlocks\nRecv ClientDone\n" ≡ "accepted (3 events, 1 sessions)"
shared-server = refl

-- Server requests remain sequential even with a large client bound.
server-sequential : reportBlockFetch 1000 "role server\nRecv RequestRange\nRecv RequestRange\n" ≡
  "rejected at index 2 (session 0): Recv RequestRange\nmodel session state after 1 events: blockfetch server busy (must send StartBatch or NoBlocks)"
server-sequential = refl

-- A request on one client cannot license another client's response.
isolation : reportWithDepths 1 1 2 "sessions blockfetch:client blockfetch:client\n0 Send RequestRange\n1 Recv NoBlocks\n" ≡
  "rejected at index 2 (session 1): Recv NoBlocks\nmodel session state after 1 events: blockfetch client outstanding 0, waiting for batch"
isolation = refl

-- Every protocol's bound is applied independently at its own component.
independent : reportWithDepths 0 0 2 "sessions fetch:client notify:client blockfetch:client\n2 Send RequestRange\n2 Send RequestRange\n" ≡ "accepted (2 events, 3 sessions)"
independent = refl

-- A Fetch overflow cannot borrow BlockFetch credit.
fetch-bound : reportWithDepths 0 2 2 "sessions fetch:client blockfetch:client\n0 Send BlockRequest ab 3\n" ≡
  "rejected at index 1 (session 0): Send BlockRequest 00000000000000000000000000000000000000000000000000000000000000ab 3\nmodel session state after 0 events: client open, nothing outstanding (accepts: Send BlockRequest/BlockTxsRequest/Done)"
fetch-bound = refl

-- Original namespaces are accepted at the correct protocol component only.
namespace : reportWithDepths 1 1 1 "sessions blockfetch:client blockfetch:server\n0 BlockFetch.Remote.Send.RequestRange\n1 BlockFetch.Remote.Receive.RequestRange\n1 BlockFetch.Remote.Send.NoBlocks\n0 BlockFetch.Remote.Receive.NoBlocks\n" ≡ "accepted (4 events, 2 sessions)"
namespace = refl

-- A cross-protocol namespace must not be routed by message name alone.
wrong-protocol : reportWithDepths 1 1 1 "sessions blockfetch:client\n0 LeiosFetch.Remote.Receive.Block\n" ≡ "parse error at line 2: 0 LeiosFetch.Remote.Receive.Block"
wrong-protocol = refl

-- A fresh manifest entry starts a new generation after another closes.
new-generation : reportWithDepths 1 1 1 "sessions blockfetch:client blockfetch:client\n0 Send ClientDone\n1 Send RequestRange\n" ≡ "accepted (2 events, 2 sessions)"
new-generation = refl

-- The former two-bound interface remains available for mixed manifests.
compatibility : reportWithDepth 1 1 "sessions blockfetch:server\n0 Recv RequestRange\n0 Send NoBlocks\n" ≡ "accepted (2 events, 1 sessions)"
compatibility = refl
