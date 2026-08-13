{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `PipeValStep.TauIoV` ASSEMBLED (`Praos.PipeValTauIo`),
-- SESSION-39 step (ii)2.
--
-- The mirror of `PipeTauIo.tauIo-{in,out}` at `PipeValInv.PipeVal`.  Everything
-- structural is LIFTED from `PipeTauIo`, not re-derived: `io-sync-wrun`, the
-- ~20-constructor label split shape, `legRelay`, `pickCli{Up,Dn}`,
-- `pickSrv{Up,Dn}`, `cellUp-key`/`cellDn-key`/`atKey`/`stepAtKey`, and
-- `PipeMedKey.setRead`/`medium-ev-{in,out}-key`.
--
-- THE EIGHT CLAUSE DISCHARGES (all cores were built in sessions 37–39):
--   (1)(5) SERVER  — `srvIoV`: `SrvIoCls` fixed ⇒ `subst`; ¬-holding ⇒
--          `PipeValFill.notHasBlk⇒SrvValOK`.  An io never ENTERS `bsBlk1`
--          (that is an api), so there is no third arm.
--   (2)(6) CELL    — INPUT: untouched key ⇒ transport; the leg's own key ⇒
--          `PipeValFill.blkfill-cellValOK` fed by `PipeValFire`'s routing
--          (`nodes-blockfill-val` + `srvHitVal-{up,dn}`) and the server clause,
--          with `plBlk?` deciding the vacuous case first.  OUTPUT: `full x →
--          draining x`, `PipeValFill.cellValOK-full⇒draining`.
--   (3)(7) CLIENT  — INPUT: a wire WRITE never hands a client a block
--          (`BlkReadAt … (input …) _ = ⊥`).  OUTPUT: `cliValOut`, whose block
--          arm is `PipeValFill.cliRead⇒CliValOK` applied to `CliBlkVal` (the
--          session-36 strengthening) and the leg's own cell clause.
--   (4)    RELAY   — the relay driver is io-fixed (`legRelay`).
--   (8)    D-SLOT  — FREE: `top-nodes-io-evo`'s `edBD`/`edCD` are FULL
--          `ConsDPh` equalities (`PipeTauIo.legCons` only ever took `cong cph`
--          of them), so the whole slot transports.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValTauIo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break )
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; rdec; reach; Reachable )
open Reachable using ( rStepʷ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos; ConsDPh )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn; upClient; dnClient; relayOf; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( medium-ev-in-key; medium-ev-out-key; setRead )
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeCliIoDec blkA as CLI
open CLI using ( CliBlkVal )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( CliIoCls; SrvIoCls; AllCliIoCls; AllSrvIoCls; top-nodes-io-evo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire blkA
  using ( nodes-blockfill-hi; srvHit-up; srvHit-dn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo blkA
  using ( legRelay; pickCliUp; pickCliDn; pickSrvUp; pickSrvDn
        ; cellUp-key; cellDn-key; atKey; stepAtKey; io-sync-wrun )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; CellValOK; SrvValOK; CliValOK; RelayValOK; ConsDValOK; consOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload; hasBlk⇒isBlk1; notHasBlk⇒SrvValOK; notHasBlk⇒CliValOK
        ; cellValOK-full⇒draining; cliRead⇒CliValOK; blkfill-cellValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFire blkA
  using ( nodes-blockfill-val; srvHitVal-up; srvHitVal-dn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep blkA
  using ( TauIoV )

------------------------------------------------------------------------
-- (1) THE PAYLOAD DECISION.  `CellValOK` is UNCONDITIONAL (unlike
-- `CellHasBlk`, which is its own antecedent in `PipeInv`), so the fill case
-- must first dispose of the payloads on which the clause is vacuous.
------------------------------------------------------------------------

-- either the payload carries a block, or its cell-value clause is vacuous
plBlk? : (x : Payload) → PlIsBlk x ⊎ CellValOK (full x)
plBlk? (_ , _ , _ , blockFetch (MsgBlock _))        = inj₁ tt
plBlk? (_ , _ , _ , blockFetch (MsgRequestRange _)) = inj₂ tt
plBlk? (_ , _ , _ , blockFetch MsgStartBatch)       = inj₂ tt
plBlk? (_ , _ , _ , blockFetch MsgNoBlocks)         = inj₂ tt
plBlk? (_ , _ , _ , blockFetch MsgBatchDone)        = inj₂ tt
plBlk? (_ , _ , _ , blockFetch MsgClientDone)       = inj₂ tt
plBlk? (_ , _ , _ , chainSync _)                    = inj₂ tt
plBlk? (_ , _ , _ , txSubmission _)                 = inj₂ tt
plBlk? (_ , _ , _ , keepAlive _)                    = inj₂ tt
plBlk? (_ , _ , _ , leiosNotify _)                  = inj₂ tt
plBlk? (_ , _ , _ , leiosFetch _)                   = inj₂ tt

------------------------------------------------------------------------
-- (2) THE PER-CLAUSE TRANSPORTS.
------------------------------------------------------------------------

-- SERVER clause: an io never enters `bsBlk1` (that is an api), so the
-- two-arm `SrvIoCls` is the whole answer
srvIoV : {bfs bfs′ : BFsPos} → SrvIoCls bfs bfs′ → SrvValOK bfs → SrvValOK bfs′
srvIoV             (inj₁ eq) h = subst SrvValOK eq h
srvIoV {bfs′ = q}  (inj₂ nb) h = notHasBlk⇒SrvValOK q nb

-- CLIENT clause across an INPUT io: a wire WRITE never hands a client a block
-- (stated on the UNFOLDED classifier, exactly as `PipeTauIo.cliClause-in`)
cliValIn : {bfc bfc′ : BFcPos}
  → (bfc ≡ bfc′) ⊎ ((BFcHasBlk bfc′ → ⊥) ⊎ ⊥)
  → CliValOK bfc → CliValOK bfc′
cliValIn                (inj₁ eq)         h = subst CliValOK eq h
cliValIn {bfc′ = q}     (inj₂ (inj₁ nb))  h = notHasBlk⇒CliValOK q nb
cliValIn                (inj₂ (inj₂ ()))  h

-- the leg's node-D consume SLOT fixity — clause (8) rides FREE, because
-- `top-nodes-io-evo` already reports FULL `ConsDPh` equalities
legConsD : (l : TwoLegs) {s s′ : SysState}
         → SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′)
         → SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′)
         → consOf l s ≡ consOf l s′
legConsD legBD dbd dcd = dbd
legConsD legCD dbd dcd = dcd

-- CELL clause across an INPUT io
cellValIn : (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)) k kd ki
  → ((k ≡ l₀) → (kd ≡ d₀) → (ki ≡ id₀) → CellValOK (full x))
  → CellValOK cu → CellValOK cu′
cellValIn g k kd ki l₀ d₀ id₀ x ceq c′eq blkcase old
  with setRead g l₀ d₀ id₀ (full x) k kd ki
... | inj₁ eq =
      subst CellValOK (trans ceq (trans eq (sym c′eq))) old
... | inj₂ (e1 , e2 , e3 , eq) =
      subst CellValOK (sym (trans c′eq eq)) (blkcase e1 e2 e3)

-- CELL clause across an OUTPUT io (`full x → draining x`)
cellValOut : (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)) k kd ki
  → g l₀ d₀ id₀ ≡ full x
  → CellValOK cu → CellValOK cu′
cellValOut g k kd ki l₀ d₀ id₀ x ceq c′eq srcEq old
  with setRead g l₀ d₀ id₀ (draining x) k kd ki
... | inj₁ eq =
      subst CellValOK (trans ceq (trans eq (sym c′eq))) old
... | inj₂ (e1 , e2 , e3 , eq) =
      subst CellValOK (sym (trans c′eq eq))
        (cellValOK-full⇒draining x
          (subst CellValOK (trans ceq (atKey g e1 e2 e3 srcEq)) old))

-- normalise a CLIENT classifier on an OUTPUT io, KEEPING the value half
-- (`PipeTauIo.cliOut-decode` projects it away; this is the only reason the
-- decode is repeated rather than lifted)
cliValOut-decode : (k : Link) (kd : Dir) {bfc bfc′ : BFcPos}
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → CliIoCls k kd bfc bfc′ (output l₀ d₀ id₀) x
  → (bfc ≡ bfc′)
  ⊎ ((BFcHasBlk bfc′ → ⊥)
     ⊎ ((l₀ ≡ k) × (d₀ ≡ kd) × (id₀ ≡ N2N_BlockFetch)
        × (PlIsBlk x × CliBlkVal bfc′ x)))
cliValOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ()))
cliValOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_BlockFetch   x (inj₂ (inj₂ (a , b , c))) =
  inj₂ (inj₂ (a , b , refl , c))
cliValOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_TxSubmission x (inj₂ (inj₂ ()))
cliValOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_KeepAlive    x (inj₂ (inj₂ ()))
cliValOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_LeiosNotify  x (inj₂ (inj₂ ()))
cliValOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₁ e)         = inj₁ e
cliValOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₂ (inj₁ nb)) = inj₂ (inj₁ nb)
cliValOut-decode k kd l₀ d₀ N2N_LeiosFetch   x (inj₂ (inj₂ ()))

-- CLIENT clause across an OUTPUT io: fixed / ¬-holding / a block read AT THE
-- LEG'S OWN KEY, which the caller turns into the reader's value via the cell
cliValOutC : (k : Link) (kd : Dir) {bfc bfc′ : BFcPos}
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → CliIoCls k kd bfc bfc′ (output l₀ d₀ id₀) x
  → ((l₀ ≡ k) → (d₀ ≡ kd) → (id₀ ≡ N2N_BlockFetch) → CellValOK (full x))
  → CliValOK bfc → CliValOK bfc′
cliValOutC k kd l₀ d₀ id₀ x cls cellcase old
  with cliValOut-decode k kd l₀ d₀ id₀ x cls
... | inj₁ eq = subst CliValOK eq old
... | inj₂ (inj₁ nb) = notHasBlk⇒CliValOK _ nb
... | inj₂ (inj₂ (e1 , e2 , e3 , (pb , cv))) =
      cliRead⇒CliValOK _ x pb cv (cellcase e1 e2 e3)

------------------------------------------------------------------------
-- (3) THE TWO io ARMS.  Mirror of `PipeTauIo.tauIo-{in,out}`, same `let`
-- skeleton (never a `with` at a `PipeVal`-typed goal — the `blkA`-parameter
-- hazard), same successor construction, same `io-sync-wrun`.
------------------------------------------------------------------------

-- ⊎-eliminator used to consume `plBlk?` without a `with` at a `PipeVal` goal
orElse : {A B : Set} → A ⊎ B → (A → B) → B
orElse (inj₁ a) f = f a
orElse (inj₂ b) f = b

-- the INPUT arm: the medium cell at the fired key goes `empty → full x`
tauIoV-in : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , input l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
tauIoV-in l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
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
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      cd : consOf l (toSys r) ≡ consOf l s′
      cd = legConsD l edBD edCD
      pres : PipeVal l (toSys r) → PipeVal l s′
      pres = λ pv →
        let (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) = pv
            -- the leg's UPSTREAM fill: route to node A's own server, read its
            -- block off `PipeVal` clause (1), and pin the payload to it
            fillUp : (upLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
                   → CellValOK (full x)
            fillUp e1 e2 e3 = orElse (plBlk? x) (λ pb →
              let stp = stepAtKey (toSys r) e1 e2 e3 sN
                  (b , eqpos) = hasBlk⇒isBlk1 (upSrv l (toSys r))
                                  (srvHit-up l (toSys r) (nodes-blockfill-hi (toSys r) stp pb))
                  pineq = srvHitVal-up l (toSys r) b x
                            (nodes-blockfill-val (toSys r) b stp pb) eqpos
              in  subst (λ z → CellValOK (full z)) (sym pineq) (subst SrvValOK eqpos h1))
            -- the leg's DOWNSTREAM fill: the relay's own server, clause (5)
            fillDn : (dnLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
                   → CellValOK (full x)
            fillDn e1 e2 e3 = orElse (plBlk? x) (λ pb →
              let stp = stepAtKey (toSys r) e1 e2 e3 sN
                  (b , eqpos) = hasBlk⇒isBlk1 (dnSrv l (toSys r))
                                  (srvHit-dn l (toSys r) (nodes-blockfill-hi (toSys r) stp pb))
                  pineq = srvHitVal-dn l (toSys r) b x
                            (nodes-blockfill-val (toSys r) b stp pb) eqpos
              in  subst (λ z → CellValOK (full z)) (sym pineq) (subst SrvValOK eqpos h5))
        in  srvIoV (pickSrvUp l (toSys r) s′ allSrv) h1
          , cellValIn (phase (med (toSys r))) (upLink l) hi N2N_BlockFetch
              l₀ d₀ id₀ x (cellUp-key l (toSys r)) (cellUp-key l s′) fillUp h2
          , cliValIn (pickCliUp l (toSys r) s′ (input l₀ d₀ id₀) x allCli) h3
          , subst RelayValOK re h4
          , srvIoV (pickSrvDn l (toSys r) s′ allSrv) h5
          , cellValIn (phase (med (toSys r))) (dnLink l) hi N2N_BlockFetch
              l₀ d₀ id₀ x (cellDn-key l (toSys r)) (cellDn-key l s′) fillDn h6
          , cliValIn (pickCliDn l (toSys r) s′ (input l₀ d₀ id₀) x allCli) h7
          , subst ConsDValOK cd h8
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

-- the OUTPUT arm: the medium cell at the fired key goes `full x → draining x`
tauIoV-out : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , output l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
tauIoV-out l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
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
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      cd : consOf l (toSys r) ≡ consOf l s′
      cd = legConsD l edBD edCD
      pres : PipeVal l (toSys r) → PipeVal l s′
      pres = λ pv →
        let (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) = pv
            -- the reader's key IS the leg's own cell, so the leg's cell clause
            -- hands the reader the block's value (`cliRead⇒CliValOK`)
            readUp : (l₀ ≡ upLink l) → (d₀ ≡ hi) → (id₀ ≡ N2N_BlockFetch)
                   → CellValOK (full x)
            readUp e1 e2 e3 =
              subst CellValOK
                (trans (cellUp-key l (toSys r))
                       (atKey (phase (med (toSys r))) (sym e1) (sym e2) (sym e3) srcFull))
                h2
            readDn : (l₀ ≡ dnLink l) → (d₀ ≡ hi) → (id₀ ≡ N2N_BlockFetch)
                   → CellValOK (full x)
            readDn e1 e2 e3 =
              subst CellValOK
                (trans (cellDn-key l (toSys r))
                       (atKey (phase (med (toSys r))) (sym e1) (sym e2) (sym e3) srcFull))
                h6
        in  srvIoV (pickSrvUp l (toSys r) s′ allSrv) h1
          , cellValOut (phase (med (toSys r))) (upLink l) hi N2N_BlockFetch
              l₀ d₀ id₀ x (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull h2
          , cliValOutC (upLink l) hi l₀ d₀ id₀ x
              (pickCliUp l (toSys r) s′ (output l₀ d₀ id₀) x allCli) readUp h3
          , subst RelayValOK re h4
          , srvIoV (pickSrvDn l (toSys r) s′ allSrv) h5
          , cellValOut (phase (med (toSys r))) (dnLink l) hi N2N_BlockFetch
              l₀ d₀ id₀ x (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull h6
          , cliValOutC (dnLink l) hi l₀ d₀ id₀ x
              (pickCliDn l (toSys r) s′ (output l₀ d₀ id₀) x allCli) readDn h7
          , subst ConsDValOK cd h8
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

------------------------------------------------------------------------
-- (4) THE COMBINATOR.  Only `input`/`output` are in `ioES`; the other fourteen
-- `Net_Api` constructors are refuted by the membership witness.
------------------------------------------------------------------------

-- `PipeValStep.TauIoV`, total and unconditional
tauIoV : (l : TwoLegs) → TauIoV l
tauIoV l r {e = input  l₀ d₀ id₀} {a = x} iomem sM sN Meq = tauIoV-in  l r l₀ d₀ id₀ x iomem sM sN Meq
tauIoV l r {e = output l₀ d₀ id₀} {a = x} iomem sM sN Meq = tauIoV-out l r l₀ d₀ id₀ x iomem sM sN Meq
tauIoV l r {e = sndmsg _ _ _} ()
tauIoV l r {e = rcvmsg _ _ _} ()
tauIoV l r {e = tx     _ _ _} ()
tauIoV l r {e = sndack _ _ _} ()
tauIoV l r {e = rcvack _ _ _} ()
tauIoV l r {e = ack    _ _ _} ()
tauIoV l r {e = done   _ _ _} ()
tauIoV l r {e = apiCS  _ _ _} ()
tauIoV l r {e = apiBF  _ _ _} ()
tauIoV l r {e = apiTS  _ _ _} ()
tauIoV l r {e = apiKA  _ _ _} ()
tauIoV l r {e = apiLN  _ _ _} ()
tauIoV l r {e = apiLF  _ _ _} ()
tauIoV l r {e = break  _}     ()
