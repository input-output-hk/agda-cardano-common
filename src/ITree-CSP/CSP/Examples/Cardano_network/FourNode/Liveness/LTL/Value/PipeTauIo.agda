{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the `PipeInvProd.TauIoS` ASSEMBLY (`Praos.PipeTauIo`),
-- item 1(e) of the session-31 frontier.
--
-- All four inputs of the io-SYNC arm are green leaves:
--   (a) `PipeMedKey`      — key-exposing medium io inversion + `setRead`
--   (b) `PipeBundleIoEvo` — BF-client io successor threading (`BlkReadAt`)
--   (c) `PipeSrvIoDec`    — BF-server io successor decode
--   (d) `PipeNodeIoEvo`   — whole-nodes io cone with BOTH slot families
-- THIS module is the glue that turns them into `tauIo : (l : TwoLegs) → TauIoS l`.
--
-- Shape: split the fired label (only `input`/`output` survive `ioES`), invert
-- the medium at the fired key, run the node cone, rebuild the successor state
-- `s′ = mkSys m′ (nA s″) … (nD s″)` and reflect the concrete τ (the plumbing is
-- `PipeClassCell.τreflect-io-classcell`, reused verbatim as `io-sync-wrun`).
-- Then discharge, per `PipeInv.Coupled` clause:
--   · CELL, untouched key    — `setRead`'s `inj₁`: the phase is literally the
--                              source one, so the OLD clause transports;
--   · CELL, INPUT at the leg's own key — the new phase is `full x`; a block
--                              payload is `PipeSrvFire.fill-{up,dn}-nodes`;
--   · CELL, OUTPUT at the leg's own key — `full x → draining x`, which
--                              `CellHasBlk` does not distinguish, so the OLD
--                              clause discharges it;
--   · CLIENT — straight off `PipeNodeIoEvo.AllCliIoCls`: fixed / not-holding /
--                              a BF wire READ AT THE LEG'S OWN KEY carrying a
--                              block, and THAT (by `medium-ev-out-key`) says the
--                              leg's own cell held a block, so again the OLD
--                              cell clause fires;
--   · SERVER — `PipeSrvInv.srvCoupled-pres` fed from `AllSrvIoCls`.
--
-- ECONOMY vs the session-31 recipe: the recipe routed the cell/client clauses
-- through `PipeInv.pipeInv⁺-io`'s three-arm `ClauseEvo`, which would force a
-- DECISION of `PlIsBlk x` (a `Messages`-wide enumeration) at every touched key.
-- Restating the transport in IMPLICATION form (`pipeInv⁺-io-imp`, four lines on
-- top of the frozen `pipeInv-frame`) removes the decision entirely: every clause
-- is discharged UNDER its own antecedent, which is exactly the block fact the
-- server cone / the old cell clause wants.  No `ClauseEvo`, no decidability.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( τ*-refl; _═[_]═►_; wev )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-io-sync-whole-wτ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos; cph )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( PipeInv; PipeInv⁺; pipeInv-frame; prodOf; relayOf; ProdSent; RelayFwd
        ; cellUp; cellDn; upClient; dnClient; CellHasBlk; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( SrvCoupled; upSrv; dnSrv; UpSrvEvo; DnSrvEvo; srvCoupled-pres )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire blkA
  using ( fill-up-nodes; fill-dn-nodes )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( medium-ev-in-key; medium-ev-out-key; setRead )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA
  using ( BlkReadAt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( CliIoCls; SrvIoCls; AllCliIoCls; AllSrvIoCls; top-nodes-io-evo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInvProd blkA
  using ( PipeInvS; TauIoS )

------------------------------------------------------------------------
-- (1) PER-LEG SELECTORS.  The node cone reports its fixities and classifiers
-- at the four CONCRETE slots; a leg picks its own out of them (`upLink legBD`
-- IS `linkAB`, so the key indices line up definitionally).
------------------------------------------------------------------------

-- the leg's producer-phase fixity out of the cone's two node-A fixities
legProd : (l : TwoLegs) {s s′ : SysState}
        → SN.NodeStateA.prod-AB (nA s) ≡ SN.NodeStateA.prod-AB (nA s′)
        → SN.NodeStateA.prod-AC (nA s) ≡ SN.NodeStateA.prod-AC (nA s′)
        → prodOf l s ≡ prodOf l s′
legProd legBD pab pac = pab
legProd legCD pab pac = pac

-- the leg's relay-phase fixity out of the cone's node-B / node-C fixities
legRelay : (l : TwoLegs) {s s′ : SysState}
         → SN.NodeStateB.cp-B (nB s) ≡ SN.NodeStateB.cp-B (nB s′)
         → SN.NodeStateC.cp-C (nC s) ≡ SN.NodeStateC.cp-C (nC s′)
         → relayOf l s ≡ relayOf l s′
legRelay legBD cb cc = cb
legRelay legCD cb cc = cc

-- the leg's D-consumer phase fixity out of the cone's two node-D fixities
legCons : (l : TwoLegs) {s s′ : SysState}
        → SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′)
        → SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′)
        → phOf l s ≡ phOf l s′
legCons legBD dbd dcd = cong cph dbd
legCons legCD dbd dcd = cong cph dcd

-- the leg's UPSTREAM client classifier (every index EXPLICIT: `AllCliIoCls`
-- is a defined ×-chain, so nothing here is inferable by unification)
pickCliUp : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → AllCliIoCls s s′ e a
          → CliIoCls (upLink l) hi (upClient l s) (upClient l s′) e a
pickCliUp legBD s s′ e a (q , _ , _ , _) = q
pickCliUp legCD s s′ e a (_ , q , _ , _) = q

-- the leg's DOWNSTREAM client classifier
pickCliDn : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
          → AllCliIoCls s s′ e a
          → CliIoCls (dnLink l) hi (dnClient l s) (dnClient l s′) e a
pickCliDn legBD s s′ e a (_ , _ , q , _) = q
pickCliDn legCD s s′ e a (_ , _ , _ , q) = q

-- the leg's UPSTREAM server classifier
pickSrvUp : (l : TwoLegs) (s s′ : SysState)
          → AllSrvIoCls s s′ → SrvIoCls (upSrv l s) (upSrv l s′)
pickSrvUp legBD s s′ (q , _ , _ , _) = q
pickSrvUp legCD s s′ (_ , q , _ , _) = q

-- the leg's DOWNSTREAM server classifier
pickSrvDn : (l : TwoLegs) (s s′ : SysState)
          → AllSrvIoCls s s′ → SrvIoCls (dnSrv l s) (dnSrv l s′)
pickSrvDn legBD s s′ (_ , _ , q , _) = q
pickSrvDn legCD s s′ (_ , _ , _ , q) = q

-- widen a two-arm `SrvIoCls` into `PipeSrvInv`'s three-arm evolution (the
-- consequent arm is never needed on an io: a server enters `bsBlk1` on an api)
srvIo⇒evo : {Q : Set} {bfs bfs′ : BFsPos}
          → SrvIoCls bfs bfs′ → (bfs ≡ bfs′) ⊎ ((BFsHasBlk bfs′ → ⊥) ⊎ Q)
srvIo⇒evo (inj₁ e)  = inj₁ e
srvIo⇒evo (inj₂ nb) = inj₂ (inj₁ nb)

------------------------------------------------------------------------
-- (2) CELL-KEY BOOKKEEPING.  `cellUp`/`cellDn` ARE the medium reads at
-- `(upLink l , hi , BF)` / `(dnLink l , hi , BF)`; a variable leg keeps both
-- sides stuck, so the identification needs a two-clause lemma.
------------------------------------------------------------------------

-- the leg's upstream cell is the medium cell at `(upLink l , hi , BF)`
cellUp-key : (l : TwoLegs) (s : SysState)
           → cellUp l s ≡ phase (med s) (upLink l) hi N2N_BlockFetch
cellUp-key legBD s = refl
cellUp-key legCD s = refl

-- the leg's downstream cell is the medium cell at `(dnLink l , hi , BF)`
cellDn-key : (l : TwoLegs) (s : SysState)
           → cellDn l s ≡ phase (med s) (dnLink l) hi N2N_BlockFetch
cellDn-key legBD s = refl
cellDn-key legCD s = refl

-- transport a cell read along the fired key's three equalities
atKey : (g : Link → Dir → IDs → CopyPhase) {k l₀ : Link} {kd d₀ : Dir} {ki id₀ : IDs}
        {v : CopyPhase}
      → k ≡ l₀ → kd ≡ d₀ → ki ≡ id₀ → g l₀ d₀ id₀ ≡ v → g k kd ki ≡ v
atKey g refl refl refl q = q

-- retarget a whole-nodes INPUT io step along the fired key's three equalities
stepAtKey : (s : SysState) {k l₀ : Link} {kd d₀ : Dir} {ki id₀ : IDs}
            {x : Payload} {N₁ : NetProc}
          → k ≡ l₀ → kd ≡ d₀ → ki ≡ id₀
          → absNodesOf s ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
          → absNodesOf s ─[ ev (evl (evLabel Payload (input k kd ki) x)) ]─► N₁
stepAtKey s refl refl refl st = st

-- `CellHasBlk` reads only the cell's message, so it cannot tell `draining` from
-- `full` (the OUTPUT case's whole content)
drain⇒full : (x : Payload) → CellHasBlk (draining x) → CellHasBlk (full x)
drain⇒full (_ , _ , _ , m) h = h

------------------------------------------------------------------------
-- (3) THE IMPLICATION-SHAPED `PipeInv⁺` TRANSPORT.  `PipeInv.pipeInv⁺-io`
-- wants a three-arm `ClauseEvo` per clause, which would force a decision of
-- `PlIsBlk`; here each clause is supplied directly, already under its own
-- antecedent.  The `PipeInv` half is the frozen `pipeInv-frame`.
------------------------------------------------------------------------

-- driver-fixed `PipeInv⁺` transport from the four clause discharges at `s′`
pipeInv⁺-io-imp : (l : TwoLegs) (s s′ : SysState)
  → prodOf  l s ≡ prodOf  l s′
  → relayOf l s ≡ relayOf l s′
  → phOf    l s ≡ phOf    l s′
  → PipeInv l s
  → (CellHasBlk (cellUp   l s′) → ProdSent (prodOf  l s′))
  → (BFcHasBlk  (upClient l s′) → ProdSent (prodOf  l s′))
  → (CellHasBlk (cellDn   l s′) → RelayFwd (relayOf l s′))
  → (BFcHasBlk  (dnClient l s′) → RelayFwd (relayOf l s′))
  → PipeInv⁺ l s′
pipeInv⁺-io-imp l s s′ pe re ce pinv f1 f2 f3 f4 =
  pipeInv-frame l s s′ pe re ce pinv , f1 , f2 , f3 , f4

------------------------------------------------------------------------
-- (4) THE FOUR CLAUSE DISCHARGES, stated generically in the consequent so one
-- copy serves both the upstream (`ProdSent`) and downstream (`RelayFwd`) leg.
------------------------------------------------------------------------

-- CELL clause across an INPUT io: untouched key ⇒ the old clause transports;
-- the leg's own key becomes `full x` and the caller's server-cone bridge
-- converts the block payload into the consequent
cellClause-in : {Q Q′ : Set} (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → (Q → Q′)
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)) k kd ki
  → ((k ≡ l₀) → (kd ≡ d₀) → (ki ≡ id₀) → PlIsBlk x → Q′)
  → (CellHasBlk cu → Q) → CellHasBlk cu′ → Q′
cellClause-in g k kd ki l₀ d₀ id₀ x mono ceq c′eq blkcase old h
  with setRead g l₀ d₀ id₀ (full x) k kd ki
... | inj₁ eq =
      mono (old (subst CellHasBlk (sym (trans ceq (trans eq (sym c′eq)))) h))
... | inj₂ (e1 , e2 , e3 , eq) =
      blkcase e1 e2 e3 (subst CellHasBlk (trans c′eq eq) h)

-- CELL clause across an OUTPUT io: untouched key ⇒ the old clause transports;
-- the leg's own key goes `full x → draining x`, and the source phase equality
-- feeds the OLD clause back
cellClause-out : {Q Q′ : Set} (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → (Q → Q′)
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)) k kd ki
  → g l₀ d₀ id₀ ≡ full x
  → (CellHasBlk cu → Q) → CellHasBlk cu′ → Q′
cellClause-out g k kd ki l₀ d₀ id₀ x mono ceq c′eq srcEq old h
  with setRead g l₀ d₀ id₀ (draining x) k kd ki
... | inj₁ eq =
      mono (old (subst CellHasBlk (sym (trans ceq (trans eq (sym c′eq)))) h))
... | inj₂ (e1 , e2 , e3 , eq) =
      mono (old (subst CellHasBlk (sym (trans ceq (atKey g e1 e2 e3 srcEq)))
                   (drain⇒full x (subst CellHasBlk (trans c′eq eq) h))))

-- CLIENT clause across an INPUT io: a wire WRITE never hands a BF client a
-- block (`BlkReadAt` on an `input` is `⊥`), so the client is fixed or empty
-- (stated on the UNFOLDED classifier: `BlkReadAt _ _ (input …) _` reduces to
-- `⊥` for ANY key, so mentioning the key here would leave it uninferable)
cliClause-in : {Q Q′ : Set} {bfc bfc′ : BFcPos}
  → (Q → Q′)
  → (bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ ⊥)
  → (BFcHasBlk bfc → Q) → BFcHasBlk bfc′ → Q′
cliClause-in mono (inj₁ eq)          old h = mono (old (subst BFcHasBlk (sym eq) h))
cliClause-in mono (inj₂ (inj₁ ¬blk)) old h = ⊥-elim (¬blk h)
cliClause-in mono (inj₂ (inj₂ ()))   old h

-- normalise a CLIENT classifier on an OUTPUT io: the block arm names the fired
-- key AND pins the protocol id to BlockFetch
cliOut-decode : (k : Link) (kd : Dir) {bfc bfc′ : BFcPos}
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → CliIoCls k kd bfc bfc′ (output l₀ d₀ id₀) x
  → (bfc ≡ bfc′)
  ⊎ ((BFcHasBlk bfc′ → ⊥)
     ⊎ ((l₀ ≡ k) × (d₀ ≡ kd) × (id₀ ≡ N2N_BlockFetch) × PlIsBlk x))
cliOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
cliOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ()))
cliOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
-- SESSION-36: the block arm now also carries `CliBlkVal bfc′ x`; this consumer
-- only wants `PlIsBlk x`, so it projects (the value half is consumed by the
-- `PipeVal` io arm, not here)
cliOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ (a , b , c))) =
  inj₂ (inj₂ (a , b , refl , proj₁ c))
cliOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
cliOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₂ (inj₂ ()))
cliOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
cliOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₂ (inj₂ ()))
cliOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
cliOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₂ (inj₂ ()))
cliOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₁ e)              = inj₁ e
cliOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₂ (inj₁ nb))      = inj₂ (inj₁ nb)
cliOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₂ (inj₂ ()))

-- CLIENT clause across an OUTPUT io: fixed / empty / a block read AT THE LEG'S
-- OWN KEY, which the caller turns into the consequent via the OLD cell clause
cliClause-out : {Q Q′ : Set} (k : Link) (kd : Dir) {bfc bfc′ : BFcPos}
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → (Q → Q′)
  → CliIoCls k kd bfc bfc′ (output l₀ d₀ id₀) x
  → ((l₀ ≡ k) → (d₀ ≡ kd) → (id₀ ≡ N2N_BlockFetch) → PlIsBlk x → Q′)
  → (BFcHasBlk bfc → Q) → BFcHasBlk bfc′ → Q′
cliClause-out k kd l₀ d₀ id₀ x mono cls blkcase old h
  with cliOut-decode k kd l₀ d₀ id₀ x cls
... | inj₁ eq                        = mono (old (subst BFcHasBlk (sym eq) h))
... | inj₂ (inj₁ ¬blk)               = ⊥-elim (¬blk h)
... | inj₂ (inj₂ (e1 , e2 , e3 , b)) = blkcase e1 e2 e3 b

------------------------------------------------------------------------
-- (5) THE REFLECTOR PLUMBING — `PipeClassCell.τreflect-io-classcell`'s concrete
-- weak τ-run, factored out so both io arms share it.
------------------------------------------------------------------------

-- the concrete hidden-τ run witnessing a medium/nodes io SYNC
io-sync-wrun : (r : RState) (m′ : MedState) (s″ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ : NetProc}
  → ioES .mem (X , e) a
  → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
  → M₁ ≡ decMed m′
  → nodesOf (toSys r) ═[ ev (evl (evLabel X e a)) ]═► nodesOf s″
  → rdec r ═[ τ ]═► ⟦ mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″) ⟧
io-sync-wrun r m′ s″ {X} {e} {a} iomem sM M₁≡ cWeakRun =
  lift-io-sync-whole-wτ (decMed (med (toSys r))) (nodesOf (toSys r)) iomem
    (wev τ*-refl
      (subst (λ z → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► z) M₁≡ sM)
      τ*-refl)
    cWeakRun

------------------------------------------------------------------------
-- (6) THE TWO io ARMS.
------------------------------------------------------------------------

-- the INPUT arm: the medium cell at the fired key goes `empty → full x`
tauIo-in : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , input l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))
tauIo-in l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
  let (_ , M₁≡) = medium-ev-in-key (med (toSys r)) l₀ d₀ id₀ x sM
      m′ : MedState
      m′ = mkMed (phase-upd (phase (med (toSys r))) l₀
                    (setCell (phase (med (toSys r)) l₀) d₀ id₀ (full x)))
                 (broken (med (toSys r)))
      (s″ , medEq , N₁≡ , cWeakRun , allCli , allSrv
          , epAB , epAC , ecB , ecC , edBD , edCD)
        = top-nodes-io-evo (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
      s′ : SysState
      s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
      r′ : RState
      r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
      pe : prodOf l (toSys r) ≡ prodOf l s′
      pe = legProd l epAB epAC
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      ce : phOf l (toSys r) ≡ phOf l s′
      ce = legCons l edBD edCD
      pres : PipeInvS l (toSys r) → PipeInvS l s′
      pres = λ ps →
        let ((pinv , cuOld , ucOld , cdOld , dcOld) , sc) = ps
        in  pipeInv⁺-io-imp l (toSys r) s′ pe re ce pinv
              (cellClause-in (phase (med (toSys r))) (upLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst ProdSent pe)
                 (cellUp-key l (toSys r)) (cellUp-key l s′)
                 (λ e1 e2 e3 blk → subst ProdSent pe
                    (fill-up-nodes l (toSys r) (stepAtKey (toSys r) e1 e2 e3 sN) blk sc))
                 cuOld)
              (cliClause-in (subst ProdSent pe)
                 (pickCliUp l (toSys r) s′ (input l₀ d₀ id₀) x allCli) ucOld)
              (cellClause-in (phase (med (toSys r))) (dnLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst RelayFwd re)
                 (cellDn-key l (toSys r)) (cellDn-key l s′)
                 (λ e1 e2 e3 blk → subst RelayFwd re
                    (fill-dn-nodes l (toSys r) (stepAtKey (toSys r) e1 e2 e3 sN) blk sc))
                 cdOld)
              (cliClause-in (subst RelayFwd re)
                 (pickCliDn l (toSys r) s′ (input l₀ d₀ id₀) x allCli) dcOld)
          , srvCoupled-pres l (toSys r) s′ (subst ProdSent pe) (subst RelayFwd re)
              (srvIo⇒evo (pickSrvUp l (toSys r) s′ allSrv))
              (srvIo⇒evo (pickSrvDn l (toSys r) s′ allSrv)) sc
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

-- the OUTPUT arm: the medium cell at the fired key goes `full x → draining x`
tauIo-out : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , output l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeInvS l (toSys r) → PipeInvS l (toSys r′))
tauIo-out l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
  let (srcFull , M₁≡) = medium-ev-out-key (med (toSys r)) l₀ d₀ id₀ x sM
      m′ : MedState
      m′ = mkMed (phase-upd (phase (med (toSys r))) l₀
                    (setCell (phase (med (toSys r)) l₀) d₀ id₀ (draining x)))
                 (broken (med (toSys r)))
      (s″ , medEq , N₁≡ , cWeakRun , allCli , allSrv
          , epAB , epAC , ecB , ecC , edBD , edCD)
        = top-nodes-io-evo (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
      s′ : SysState
      s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
      r′ : RState
      r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
      pe : prodOf l (toSys r) ≡ prodOf l s′
      pe = legProd l epAB epAC
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      ce : phOf l (toSys r) ≡ phOf l s′
      ce = legCons l edBD edCD
      pres : PipeInvS l (toSys r) → PipeInvS l s′
      pres = λ ps →
        let ((pinv , cuOld , ucOld , cdOld , dcOld) , sc) = ps
        in  pipeInv⁺-io-imp l (toSys r) s′ pe re ce pinv
              (cellClause-out (phase (med (toSys r))) (upLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst ProdSent pe)
                 (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull cuOld)
              (cliClause-out (upLink l) hi l₀ d₀ id₀ x (subst ProdSent pe)
                 (pickCliUp l (toSys r) s′ (output l₀ d₀ id₀) x allCli)
                 (λ e1 e2 e3 blk → subst ProdSent pe
                    (cuOld (subst CellHasBlk
                              (sym (trans (cellUp-key l (toSys r))
                                     (atKey (phase (med (toSys r)))
                                        (sym e1) (sym e2) (sym e3) srcFull)))
                              blk)))
                 ucOld)
              (cellClause-out (phase (med (toSys r))) (dnLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst RelayFwd re)
                 (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull cdOld)
              (cliClause-out (dnLink l) hi l₀ d₀ id₀ x (subst RelayFwd re)
                 (pickCliDn l (toSys r) s′ (output l₀ d₀ id₀) x allCli)
                 (λ e1 e2 e3 blk → subst RelayFwd re
                    (cdOld (subst CellHasBlk
                              (sym (trans (cellDn-key l (toSys r))
                                     (atKey (phase (med (toSys r)))
                                        (sym e1) (sym e2) (sym e3) srcFull)))
                              blk)))
                 dcOld)
          , srvCoupled-pres l (toSys r) s′ (subst ProdSent pe) (subst RelayFwd re)
              (srvIo⇒evo (pickSrvUp l (toSys r) s′ allSrv))
              (srvIo⇒evo (pickSrvDn l (toSys r) s′ allSrv)) sc
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

------------------------------------------------------------------------
-- (7) THE COMBINATOR.  Only `input`/`output` are in `ioES`; the other fourteen
-- `Net_Api` constructors are refuted by the membership witness.
------------------------------------------------------------------------

-- THE io-SYNC arm of `PipeInvProd.TauStepS`, total and unconditional
tauIo : (l : TwoLegs) → TauIoS l
tauIo l r {e = input  l₀ d₀ id₀} {a = x} iomem sM sN Meq = tauIo-in  l r l₀ d₀ id₀ x iomem sM sN Meq
tauIo l r {e = output l₀ d₀ id₀} {a = x} iomem sM sN Meq = tauIo-out l r l₀ d₀ id₀ x iomem sM sN Meq
tauIo l r {e = sndmsg _ _ _} ()
tauIo l r {e = rcvmsg _ _ _} ()
tauIo l r {e = tx     _ _ _} ()
tauIo l r {e = sndack _ _ _} ()
tauIo l r {e = rcvack _ _ _} ()
tauIo l r {e = ack    _ _ _} ()
tauIo l r {e = done   _ _ _} ()
tauIo l r {e = apiCS  _ _ _} ()
tauIo l r {e = apiBF  _ _ _} ()
tauIo l r {e = apiTS  _ _ _} ()
tauIo l r {e = apiKA  _ _ _} ()
tauIo l r {e = apiLN  _ _ _} ()
tauIo l r {e = apiLF  _ _ _} ()
tauIo l r {e = break  _}     ()
