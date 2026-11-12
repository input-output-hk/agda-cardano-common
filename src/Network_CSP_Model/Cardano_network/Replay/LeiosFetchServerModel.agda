{-# OPTIONS --guardedness #-}

-- The server side of the trace-replay bridge (Phase 5, amendment B5):
-- node 0's renamed LeiosFetch producer, synchronised on `apiES` with its two
-- serving threads (EB bodies, tx closures), synchronised on `storeES` with
-- its EB-body store holding `bs` and a held unit-transaction read menu.  Node 0's only endpoint is `(link 0 , lo)`,
-- so its server peer sits at `hi` and the threads run at `(link 0 , opposite hi)`.
-- Definitions only (Increment 0).
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
module Cardano_network.Replay.LeiosFetchServerModel where

open import Data.Fin using (Fin) renaming (zero to fzero)
open import Process_Trees
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)

open import Cardano_network.Base using (Dir; hi)
open import Cardano_network.Parametric.Topology using (opposite)
open import Cardano_network.Replay.ReplayParams using (replayParams; replayLP; replayTopo)
open import Cardano_network.Net replayParams using (Link; Net_Api; Net_Api-≟)
open import Cardano_network.Data replayParams using (Payload)
open import Cardano_network.ApiAlphabet replayParams using (apiES)
open import Cardano_network.Parametric.Leios.PeersP replayParams using (Proc; LFPserverA) public
import Cardano_network.Parametric.NodeLogic as NL
open NL.Generic replayParams replayTopo apiES using (storeES) public
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic replayParams replayLP replayTopo apiES (λ _ → tt)
  using (Bodies; offerBodies; putBodyEv; ebServeLoop; ebTxsServeLoop; getBodyEv; getTxEv; serveTxs) public
  renaming (bodyStep to originalBodyStep)
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (_∥⇘_⇙_; _⦀_; _□_)
open import Cardano_network.Params using (module Params)
open import Class.DecEq using (DecEq)
open import Class.DecEq.Instances using (DecEq-List)

instance
  -- Resolve body-inventory equality for the replay store choice.
  replayBodyEq : DecEq ℕ
  replayBodyEq = Params.decEB replayParams

-- The replay store adds the sole unit transaction to the real EB body menu.
-- Every table entry names this hash; reads retain the original body inventory.
bodyStep : Fin 2 → Bodies → Process_Trees.PTree (Net_Api Payload) (Process_Trees.ExtI (Net_Api Payload)) Bodies
bodyStep n bs = originalBodyStep n bs □ Op.Output ⦃ Params.decTx replayParams ⦄ (getTxEv n tt) tt (Op.Ret bs)

-- A productive store loop serves both the body inventory and the held unit tx.
bodyStore : Fin 2 → Bodies → Proc
bodyStore n = Op.loop (bodyStep n)

-- the serving node
nS : Fin 2
nS = fzero

-- the link of the session
lS : Link
lS = fzero

-- the direction of node 0's LeiosFetch server peer
dS : Dir
dS = hi

-- the serving node's body-by-hash store channel
getBodyEvS : ℕ → Net_Api Payload ℕ
getBodyEvS = getBodyEv nS

-- the renamed LeiosFetch producer of the session
peerS : Proc
peerS = LFPserverA lS dS

-- the two serving threads, interleaved, driving the producer's direction
threadsS : Proc
threadsS = ebServeLoop nS (lS , opposite dS) ⦀ ebTxsServeLoop nS (lS , opposite dS)

-- the composite at any producer and thread state, over the body store holding `bs`
srvAt : Proc → Proc → Bodies → Proc
srvAt P T bs = (P ∥⇘ apiES ⇙ T) ∥⇘ storeES ⇙ bodyStore nS bs

-- B5's server model: the initial composite over the body store holding `bs`
serverModel : Bodies → Proc
serverModel bs = srvAt peerS threadsS bs
