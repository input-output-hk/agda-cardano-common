{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the SESSION-35 PHASE-1 GATE for the block-VALUE
-- invariant (`Praos.PipeValGate`).
--
-- QUESTION.  Before building anything, is
--
--     "every BlockFetch `MsgBlock` payload reachable on a pipeline leg — in a
--      medium copy cell, held by a BF peer, or handed to node D — carries the
--      block `blkA`"
--
-- actually TRUE on this model?  (Four statements in this campaign turned out
-- FALSE rather than hard — `PipeInv.Coupled`'s cell clauses, the (E) recipe, a
-- missing key pin, and `wprog` itself — so the gate is mandatory.)
--
-- VERDICT: **TRUE**, and value-TIGHT at every edge.  The facts below are the
-- machine-checked edges of the single value chain
--
--   nodeA driver `!blkA`  ⇒  A's BF server `bsWblk blkA`
--                         ⇒  cell (linkAB,hi,BF) = `MsgBlock blkA`
--                         ⇒  relay's BF client `bcAblk blkA`
--                         ⇒  relay driver `consuming blkA cp4…cp6`
--                         ⇒  relay's produce leg `produce linkBD hi blkA`
--                         ⇒  … the same five edges again on the DOWNSTREAM link
--                         ⇒  D's BF client `bcAblk blkA`
--                         ⇒  D's `recvBFBlock` api value = `blkA`.
--
-- Every edge is either a table `refl` or a `!`-pin (an `Output` node offers its
-- event at ONE value only).  NOTHING in the model can inject a second block:
--
--   · the ONLY source of a `Block₃` on a BF leg is a `produce` driver's
--     `sendBFBlock ! blk` (`SysNode.decProd … pp5`), and node A's decode
--     `SysNode.decNodeA` applies `decProd` to the LITERAL `blkA` on both legs
--     (`decProd linkAB hi blkA (prod-AB s)` / `decProd linkAC hi blkA …`), so
--     no state field can vary it;
--   · a relay's produce leg is `decCP l₁ l₂ (producing b pp) = decProd l₂ hi b pp`
--     with `b` the block its consume leg RECEIVED (`cons-cp3-rebind` below),
--     and that received value is pinned by the relay's BF CLIENT peer
--     (`cli-ablk-pins`), i.e. by what came off the wire;
--   · a copy cell is keyed `(link, dir, IDs)` and `IDs` DISCRIMINATES
--     `N2N_ChainSync` from `N2N_BlockFetch` (`Base.IDs`), so a ChainSync
--     `MsgCSRollForward` NEVER lands in a BlockFetch cell — and even if it did
--     it is not a `blockFetch (MsgBlock _)`, so `PipeInv.MsgIsBlk` ignores it;
--   · `MsgBlock` fills of a cell come ONLY from the BF-server wire-send
--     position `bsWblk b`, and that position's io payload is PINNED to
--     `MsgBlock b` (`srv-wblk-pins`); the three OTHER wire-send positions
--     (`bsWsb`/`bsWnb`/`bsWbd`) are pinned to `MsgStartBatch`/`MsgNoBlocks`/
--     `MsgBatchDone` and every remaining position offers NO wire-send at all
--     (`srv-no-wire-*`) — so no stale/foreign payload can masquerade as a block;
--   · STALE blocks are impossible in a stronger sense than "one round": every
--     `MsgBlock` value on any leg is `blkA`, so even a `draining` leftover or a
--     second in-flight block would still carry `blkA`;
--   · the decoder-state PLACEHOLDERS `consD blkA cp0` / `consuming blkA cp0`
--     (`SysNode.initNodeD`/`initNodeB`/`initNodeC`) are already `blkA`, and
--     `decCons l d b cp0 ≡ consume l d` / `decCons l d b cp1` DISCARD the field
--     (`cons-cp01-blind` below), so the placeholder is unobservable and cannot
--     leak a bogus value;
--   · node D has TWO legs (BD, CD) and both are instances of the same chain —
--     every fact below is stated at a general `(l , d)` or is mirrored on the
--     CD link.
--
-- CONSEQUENCE FOR THE CAMPAIGN.  The invariant is true, so `arrivedD` CAN be
-- strengthened with the `a ≡ b` conjunct.  What remains is not a truth question
-- but a PRESERVATION build: the eight per-leg value clauses have to ride the
-- existing `PipeInvS` fold (`PipeInvProd`/`PipeStepEmit`) through the io-sync
-- arm (`PipeTauIo`) and the visible-api arm (`PipeEvStep`).
--
-- Imported by nothing (a gate leaf, exactly like `PipeCellFalse`).
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Product using ( _×_; _,_; proj₁ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
import Data.Unit as U
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )
open import Relation.Nullary using ( Dec; yes; no )
open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI; AnyTypes; ContinueType; NodeKind; react )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Evidence.PipeValGate (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; linkAB; linkAC; linkBD; linkCD; produce; consume )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block; time₀; length₀ )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; lo; N2N_BlockFetch; FromResponder; FromInitiator )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Messages; blockFetch; MsgBlock; MsgStartBatch; MsgNoBlocks
        ; MsgBatchDone; DecEq-Payload )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; input; output; apiBF; apiCS
        ; sendBFBlock; recvBFBlock )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN

-- the whole-system process type
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (U.⊤)

------------------------------------------------------------------------
-- (0) The wire payload that carries block `b` on the responder direction —
-- the ONLY payload a BF server at `bsWblk b` can put on the wire.
------------------------------------------------------------------------

-- the BlockFetch `MsgBlock b` wire payload of a responder-side sender
blkPayload : Block → Payload
blkPayload b = time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)

------------------------------------------------------------------------
-- (1) THE SOURCE PIN.  Node A's `produce` driver at `pp5` IS an `Output`
-- node (`sendBFBlock ! blkA`), whose tail is the `pp6` decode.  An `Output`
-- offers its event at ONE value only, so the `sendBFBlock` api event of node A
-- can only ever fire carrying `blkA`.
------------------------------------------------------------------------

-- the `pp5` producer decode, exhibited as the `!`-pinned output of `blkA`
prod-pp5-output : (l : Link) (d : Dir)
  → SN.decProd l d blkA SN.pp5
      ≡ Op.Output (apiBF l d sendBFBlock) blkA (SN.decProd l d blkA SN.pp6)
prod-pp5-output l d = refl

-- an `Output` node's visible offer map is `nothing` at every value but its own
output-pins : {A : Set} ⦃ _ : DecEq A ⦄ (e : Net_Api Payload A) (v x : A) (P : NetProc)
            → (Op.Output-cont e v P (A , e) x ≡ nothing) ⊎ (x ≡ v)
output-pins {A} e v x P with Net_Api-≟ {Payload} (A , e) (A , e)
... | no  _    = inj₁ refl
... | yes refl with x ≟ v
...   | yes q  = inj₂ q
...   | no  _  = inj₁ refl

------------------------------------------------------------------------
-- (2) DRIVER ⇒ SERVER.  The api `sendBFBlock` carrying `b` moves the abstract
-- BF server from `bsStream` to the wire-send position `bsWblk b` — the value
-- travels INTO the peer position.
------------------------------------------------------------------------

-- the api `sendBFBlock` edge of the abstract BF server: `bsStream → bsWblk b`
srv-api-block : (b : Block)
  → NS.bfSnxt linkAB hi NS.bsStream (_ , apiBF linkAB hi sendBFBlock) b
      ≡ just (NS.bsWblk b)
srv-api-block b = refl

-- the same edge on the AC leg (node A's other produce driver)
srv-api-block-AC : (b : Block)
  → NS.bfSnxt linkAC hi NS.bsStream (_ , apiBF linkAC hi sendBFBlock) b
      ≡ just (NS.bsWblk b)
srv-api-block-AC b = refl

-- the same edge on the two DOWNSTREAM links (the relays' produce legs)
srv-api-block-BD : (b : Block)
  → NS.bfSnxt linkBD hi NS.bsStream (_ , apiBF linkBD hi sendBFBlock) b
      ≡ just (NS.bsWblk b)
srv-api-block-BD b = refl

srv-api-block-CD : (b : Block)
  → NS.bfSnxt linkCD hi NS.bsStream (_ , apiBF linkCD hi sendBFBlock) b
      ≡ just (NS.bsWblk b)
srv-api-block-CD b = refl

------------------------------------------------------------------------
-- (3) SERVER ⇒ CELL.  At `bsWblk b` the wire-send io is PINNED to the payload
-- `MsgBlock b`: any other payload is simply not offered.  So a cell fill from
-- this position carries exactly the block the server holds.
------------------------------------------------------------------------

-- the `bsWblk b` wire-send offers ONLY the `MsgBlock b` payload
srv-wblk-pins : (b : Block) (pl : Payload)
  → (NS.bfSnxt linkAB hi (NS.bsWblk b) (_ , input linkAB hi N2N_BlockFetch) pl
       ≡ nothing)
  ⊎ (pl ≡ blkPayload b)
srv-wblk-pins b pl with pl ≟ blkPayload b
... | yes q = inj₂ q
... | no  _ = inj₁ refl

------------------------------------------------------------------------
-- (4) NO OTHER SOURCE OF A CELL FILL.  The three other wire-send positions are
-- pinned to NON-block payloads, and every remaining server position offers no
-- wire-send at all.  Hence a `MsgBlock` in a leg cell can only have come from
-- `bsWblk`.
------------------------------------------------------------------------

-- `bsWsb` is pinned to `MsgStartBatch`
srv-wsb-pins : (pl : Payload)
  → (NS.bfSnxt linkAB hi NS.bsWsb (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing)
  ⊎ (pl ≡ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch))
srv-wsb-pins pl with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
... | yes q = inj₂ q
... | no  _ = inj₁ refl

-- `bsWnb` is pinned to `MsgNoBlocks`
srv-wnb-pins : (pl : Payload)
  → (NS.bfSnxt linkAB hi NS.bsWnb (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing)
  ⊎ (pl ≡ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks))
srv-wnb-pins pl with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
... | yes q = inj₂ q
... | no  _ = inj₁ refl

-- `bsWbd` is pinned to `MsgBatchDone`
srv-wbd-pins : (pl : Payload)
  → (NS.bfSnxt linkAB hi NS.bsWbd (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing)
  ⊎ (pl ≡ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone))
srv-wbd-pins pl with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
... | yes q = inj₂ q
... | no  _ = inj₁ refl

-- the four NON-wire-send server positions offer NO cell fill at all
srv-no-wire-idle : (pl : Payload)
  → NS.bfSnxt linkAB hi NS.bsIdle (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing
srv-no-wire-idle pl = refl

srv-no-wire-busy : (pl : Payload)
  → NS.bfSnxt linkAB hi NS.bsBusy (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing
srv-no-wire-busy pl = refl

srv-no-wire-stream : (pl : Payload)
  → NS.bfSnxt linkAB hi NS.bsStream (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing
srv-no-wire-stream pl = refl

srv-no-wire-ddone : (pl : Payload)
  → NS.bfSnxt linkAB hi NS.bsDdone (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing
srv-no-wire-ddone pl = refl

srv-no-wire-term : (pl : Payload)
  → NS.bfSnxt linkAB hi NS.bsTerm (_ , input linkAB hi N2N_BlockFetch) pl ≡ nothing
srv-no-wire-term pl = refl

------------------------------------------------------------------------
-- (5) CELL ⇒ CLIENT.  A BF client at `bcStream` that reads a `MsgBlock b` off
-- the wire lands at `bcAblk b` — the value travels out of the cell into the
-- receiving peer.  (The other two `bcStream` wire branches carry no block.)
------------------------------------------------------------------------

-- reading `MsgBlock b` at `bcStream` records the block: `bcStream → bcAblk b`
cli-stream-reads : ∀ {t m len} (b : Block)
  → NS.bfCnxt linkAB hi NS.bcStream (_ , output linkAB hi N2N_BlockFetch)
      (t , m , len , blockFetch (MsgBlock b))
      ≡ just (NS.bcAblk b)
cli-stream-reads b = refl

-- the same edge on the three other links
cli-stream-reads-AC : ∀ {t m len} (b : Block)
  → NS.bfCnxt linkAC hi NS.bcStream (_ , output linkAC hi N2N_BlockFetch)
      (t , m , len , blockFetch (MsgBlock b)) ≡ just (NS.bcAblk b)
cli-stream-reads-AC b = refl

cli-stream-reads-BD : ∀ {t m len} (b : Block)
  → NS.bfCnxt linkBD hi NS.bcStream (_ , output linkBD hi N2N_BlockFetch)
      (t , m , len , blockFetch (MsgBlock b)) ≡ just (NS.bcAblk b)
cli-stream-reads-BD b = refl

cli-stream-reads-CD : ∀ {t m len} (b : Block)
  → NS.bfCnxt linkCD hi NS.bcStream (_ , output linkCD hi N2N_BlockFetch)
      (t , m , len , blockFetch (MsgBlock b)) ≡ just (NS.bcAblk b)
cli-stream-reads-CD b = refl

------------------------------------------------------------------------
-- (6) CLIENT ⇒ API.  At `bcAblk b` the api `recvBFBlock` is PINNED to the held
-- block `b`: the peer offers no other value, so the value node D (or a relay)
-- observes on `recvBFBlock` IS the value that came off the wire.
------------------------------------------------------------------------

-- the `bcAblk b` api emit offers ONLY the held block
cli-ablk-pins : (b x : Block)
  → (NS.bfCnxt linkBD hi (NS.bcAblk b) (_ , apiBF linkBD hi recvBFBlock) x ≡ nothing)
  ⊎ (x ≡ b)
cli-ablk-pins b x with x ≟ b
... | yes q = inj₂ q
... | no  _ = inj₁ refl

-- the same pin on node D's other leg
cli-ablk-pins-CD : (b x : Block)
  → (NS.bfCnxt linkCD hi (NS.bcAblk b) (_ , apiBF linkCD hi recvBFBlock) x ≡ nothing)
  ⊎ (x ≡ b)
cli-ablk-pins-CD b x with x ≟ b
... | yes q = inj₂ q
... | no  _ = inj₁ refl

-- and on the two UPSTREAM links (the relays' consume legs)
cli-ablk-pins-AB : (b x : Block)
  → (NS.bfCnxt linkAB hi (NS.bcAblk b) (_ , apiBF linkAB hi recvBFBlock) x ≡ nothing)
  ⊎ (x ≡ b)
cli-ablk-pins-AB b x with x ≟ b
... | yes q = inj₂ q
... | no  _ = inj₁ refl

cli-ablk-pins-AC : (b x : Block)
  → (NS.bfCnxt linkAC hi (NS.bcAblk b) (_ , apiBF linkAC hi recvBFBlock) x ≡ nothing)
  ⊎ (x ≡ b)
cli-ablk-pins-AC b x with x ≟ b
... | yes q = inj₂ q
... | no  _ = inj₁ refl

------------------------------------------------------------------------
-- (7) API ⇒ CONSUMER STATE.  The consume driver at `cp3` is a PREFIX whose
-- continuation family is literally `λ b′ → decCons l d b′ cp4`: whatever value
-- the `recvBFBlock` api fires with is EXACTLY what the abstract consumer state
-- records.  (So the `b″` a `WalkPr.DeliverSig` carries is the D-client's held
-- block, and a value invariant on `dnClient`/`cons-lD` transfers to it.)
------------------------------------------------------------------------

-- the `cp3` consume decode REBINDS the fired block into the `cp4` decode
cons-cp3-rebind : (l : Link) (d : Dir) (b : Block₃)
  → SN.decCons l d b SN.cp3
      ≡ Op.Prefix (apiBF l d recvBFBlock) (λ b′ → SN.decCons l d b′ SN.cp4)
cons-cp3-rebind l d b = refl

-- past `cp3` the recorded block is CARRIED unchanged to the driver's result
cons-cp4-carries : (l : Link) (d : Dir) (b : Block₃)
  → SN.decCons l d b SN.cp6 ≡ Op.Ret b
cons-cp4-carries l d b = refl

------------------------------------------------------------------------
-- (8) THE PLACEHOLDERS ARE BLIND.  Before `cp2` the `Block₃` field of a
-- `ConsPh`/`ConsDPh`/`CPPh` is DISCARDED by the decode, so the `blkA`
-- placeholders `consD blkA cp0` / `consuming blkA cp0` of `initNodeD`/
-- `initNodeB`/`initNodeC` are unobservable and cannot leak a bogus value.
------------------------------------------------------------------------

-- at `cp0` the block field is discarded: the decode is the whole `consume` body
cons-cp0-blind : (l : Link) (d : Dir) (b b′ : Block₃)
  → SN.decCons l d b SN.cp0 ≡ SN.decCons l d b′ SN.cp0
cons-cp0-blind l d b b′ = refl

-- at `cp1` the block field is likewise discarded
cons-cp1-blind : (l : Link) (d : Dir) (b b′ : Block₃)
  → SN.decCons l d b SN.cp1 ≡ SN.decCons l d b′ SN.cp1
cons-cp1-blind l d b b′ = refl

------------------------------------------------------------------------
-- (9) RELAY HAND-OFF.  The relay driver's produce leg is `decProd` at the
-- CONSUMED block, and at `pp0` that is literally `produce l₂ hi b` — so the
-- block a relay re-emits is the block it received, with no state in between.
------------------------------------------------------------------------

-- a relay at `producing b pp0` IS `produce l₂ hi b`
relay-handoff : (l₁ l₂ : Link) (b : Block₃)
  → SN.decCP l₁ l₂ (SN.producing b SN.pp0) ≡ produce l₂ hi b
relay-handoff l₁ l₂ b = refl

-- and the relay's produce leg at `pp5` is the `!`-pin of the RELAYED block
relay-pp5-output : (l₁ l₂ : Link) (b : Block₃)
  → SN.decCP l₁ l₂ (SN.producing b SN.pp5)
      ≡ Op.Output (apiBF l₂ hi sendBFBlock) b (SN.decProd l₂ hi b SN.pp6)
relay-pp5-output l₁ l₂ b = refl
