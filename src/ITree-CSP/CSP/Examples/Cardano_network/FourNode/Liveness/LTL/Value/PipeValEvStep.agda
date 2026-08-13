{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the VISIBLE-middle combinator at `PipeVal`
-- (`Praos.PipeValEvStep`), SESSION-51 step (iii): `evStepV : (l : TwoLegs) →
-- EvStepV l`, the last open argument of `PipeValStep.stepEmitV` beside the
-- already-closed `tauIoV` (`PipeValTauIo`, session 39).
--
-- The label dispatch is VERBATIM `PipeEvStep.evStep`'s (api-CSBF → the driver
-- bridge; `break` → the medium frame; io hidden; inert api + wire messages
-- refuted), so only the api and break arms carry content.
--
-- THE api ARM, clause by clause.  `PipeEvDriverCone.driverExpose` reports the
-- leg's step twice: `LegDriverStep` (phases + component fixities, session 26/33/
-- 40/41/45) and the session-51 `LegValStep` (the four VALUE facts the phase data
-- necessarily drops).  Here they are combined:
--
--   (1)/(5) the two BF SERVERS — `LegValStep`'s RAW `BfsSucc` witness names the
--           fired block and pins the successor to `bsBlk1 b″`; the whole-system
--           step then feeds `PipeValProd.prodFire-blkA-{AB,AC}` (upstream, node
--           A's `!`-pin) and `prodFire-relayVal-{BD,CD}` (downstream, conditional
--           on clause (4) at the SOURCE — available, since `PipeVal` is the
--           hypothesis).  A `¬ BFsHasBlk` successor makes `SrvValOK` `⊤`.
--   (2)/(6) the two CELLS — an api never touches a medium cell, so both are FIXED
--           in every `LegDriverStep` constructor: a `subst`.
--   (3)/(7) the two BF CLIENTS — fixed, or fired visibly to a `¬ BFcHasBlk`
--           successor (a client never ENTERS `bcBlk1` on an api), which makes
--           `CliValOK` `⊤`.
--   (4)     the RELAY driver — off the receive region `LegValStep.lvRelay` carries
--           the value across; ON it (`RelayPre`/`RelayHas`) `ldRelay`'s `wUp`
--           names the block the co-firing BF client held, and clause (3) says it
--           is `blkA`.
--   (8)     node D's DRIVER — past the receive `LegValStep.lvCons` fixes the
--           recorded block; ON the `cp3 → cp4` hop `ldCons`'s anchor ties the
--           recorded block to the client's, and clause (7) says it is `blkA`.
--
-- THE break ARM.  A `broken`-flip moves no node and preserves `phase`, so all
-- eight components are fixed and the preservation is `pipeVal-frame`.
--
-- STYLE (the blkA-parameterisation hazard, `PipeEvStep`'s assembly note).  Every
-- function whose type mentions the imported `PipeVal`/`SrvValOK`/… is `with`-FREE:
-- all case analysis lives in helpers that are abstract in the state (plain `CPPh`
-- / `ConsDPh` / `BFcPos` / `BFsPos` arguments), or in `break-invert`, whose
-- statement mentions no value predicate at all.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValEvStep (blkA : Block₃) where

open import Data.Unit using () renaming ( ⊤ to ⊤₀ )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; Block₃; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; sendBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( hi; N2N_BlockFetch )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA using
  ( MedState; phase; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( NetProc; absNodesOf; nodesOf; lift-med-whole-ev )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA using
  ( SysState; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA using
  ( RState; toSys; radec; rdec; rcloseʷ; rcloseʷ-abs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA using
  ( IsApiCSBF; aicCS; aicBF; aicDone )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA using
  ( oevB-no-io; oevB-refute )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
              ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1
              ; bsBatchDone1; bsSil
              ; CPPh; consuming; producing
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ConsDPh; consD; cblk; cph )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA using
  ( TwoLegs; legBD; legCD; phOf; linkOf; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA using
  ( ConsAdv; c01; c12; c23; c34; c45; c56 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA using
  ( ConsHeld )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( relayOf; cellUp; cellDn; upClient; dnClient
  ; RelayPre; RelayHas; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA using
  ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA using
  ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA using
  ( RelayStepKind; rMove; rFwd; rRecv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA using
  ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix
  ; LegValStep; lvUpSrv; lvDnSrv; lvRelay; lvCons; SrvValEvo; upLinkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA using
  ( reach-ev-driver; break-invert )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA using
  ( PipeVal; SrvValOK; CellValOK; CliValOK; RelayValOK; ConsDValOK; ConsValAt
  ; consOf; pipeVal-frame )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValProd blkA using
  ( prodFire-blkA-AB; prodFire-blkA-AC
  ; prodFire-relayVal-BD; prodFire-relayVal-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep blkA using
  ( EvStepV; StepEmitV; stepEmitV )
-- the io-sync arm, CLOSED in session 39
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValTauIo blkA using
  ( tauIoV )

------------------------------------------------------------------------
-- (1) The state-ABSTRACT value lemmas.  Every one of these takes plain peer /
-- phase positions, so nothing here can trip the blkA `with` hazard.
------------------------------------------------------------------------

-- a BF server that is NOT holding a block satisfies the value clause vacuously
¬blk⇒srvVal : (bfs : BFsPos) → (BFsHasBlk bfs → ⊥) → SrvValOK bfs
¬blk⇒srvVal (bsHead _)   nb = tt
¬blk⇒srvVal (bsReq1 _)   nb = tt
¬blk⇒srvVal bsDone1      nb = tt
¬blk⇒srvVal bsStart1     nb = tt
¬blk⇒srvVal bsNoBlk1     nb = tt
¬blk⇒srvVal (bsBlk1 b)   nb = ⊥-elim (nb tt)
¬blk⇒srvVal bsBatchDone1 nb = tt
¬blk⇒srvVal (bsSil _)    nb = tt

-- a BF client that is NOT holding a received block satisfies its clause vacuously
¬blk⇒cliVal : (bfc : BFcPos) → (BFcHasBlk bfc → ⊥) → CliValOK bfc
¬blk⇒cliVal (bcHead _) nb = tt
¬blk⇒cliVal (bcReq1 _) nb = tt
¬blk⇒cliVal bcDone1    nb = tt
¬blk⇒cliVal (bcBlk1 b) nb = ⊥-elim (nb tt)
¬blk⇒cliVal (bcSil _)  nb = tt

-- a BF client EVOLUTION (fixed, or fired to a non-holding successor) carries the
-- value clause across — this is the shape `ldRelay`/`ldCons` deliver
cliValEvo : (c c′ : BFcPos) → (c ≡ c′) ⊎ (BFcHasBlk c′ → ⊥)
          → CliValOK c → CliValOK c′
cliValEvo c c′ (inj₁ eq)  h = subst CliValOK eq h
cliValEvo c c′ (inj₂ nb)  h = ¬blk⇒cliVal c′ nb

-- inside the receive region (`RelayPre`) the relay's value clause is vacuous
relayPre⇒val : (x : CPPh) → RelayPre x → RelayValOK x
relayPre⇒val (consuming b cp0) _  = tt
relayPre⇒val (consuming b cp1) _  = tt
relayPre⇒val (consuming b cp2) _  = tt
relayPre⇒val (consuming b cp3) _  = tt
relayPre⇒val (consuming b cp4) ()
relayPre⇒val (consuming b cp5) ()
relayPre⇒val (consuming b cp6) ()
relayPre⇒val (producing b pp)  ()

-- `RelayPre` and `RelayHas` are disjoint
relayPre-has-⊥ : (x : CPPh) → RelayPre x → RelayHas x → ⊥
relayPre-has-⊥ (consuming b cp0) _  ()
relayPre-has-⊥ (consuming b cp1) _  ()
relayPre-has-⊥ (consuming b cp2) _  ()
relayPre-has-⊥ (consuming b cp3) _  ()
relayPre-has-⊥ (consuming b cp4) () _
relayPre-has-⊥ (consuming b cp5) () _
relayPre-has-⊥ (consuming b cp6) () _
relayPre-has-⊥ (producing b pp)  () _

-- an internal relay move: inside the receive region the successor is still in it
-- (so the clause is `⊤`); outside it, the cone's block-fixity map applies.  Cased
-- on the SOURCE phase so `RelayPre` reduces — no `with`, hence no goal
-- normalisation
relayVal-move : (x x′ : CPPh) → (RelayPre x → RelayPre x′)
              → ((RelayPre x → ⊥) → RelayValOK x → RelayValOK x′)
              → RelayValOK x → RelayValOK x′
relayVal-move (consuming b cp0) x′ fP vfix h = relayPre⇒val x′ (fP tt)
relayVal-move (consuming b cp1) x′ fP vfix h = relayPre⇒val x′ (fP tt)
relayVal-move (consuming b cp2) x′ fP vfix h = relayPre⇒val x′ (fP tt)
relayVal-move (consuming b cp3) x′ fP vfix h = relayPre⇒val x′ (fP tt)
relayVal-move (consuming b cp4) x′ fP vfix h = vfix (λ ()) h
relayVal-move (consuming b cp5) x′ fP vfix h = vfix (λ ()) h
relayVal-move (consuming b cp6) x′ fP vfix h = vfix (λ ()) h
relayVal-move (producing b pp)  x′ fP vfix h = vfix (λ ()) h

-- THE RELAY CLAUSE.  Off the receive the cone's map carries the value; on it the
-- co-firing BF client's block IS the relayed one, and clause (3) says it is `blkA`
relayValStep : (x x′ : CPPh) (c : BFcPos)
  → RelayStepKind x x′
  → ((RelayPre x → ⊥) → RelayValOK x → RelayValOK x′)
  → (RelayPre x → RelayHas x′
     → BFcHasBlk c × (Σ[ bc ∈ Block₃ ] (c ≡ bcBlk1 bc) × (x′ ≡ consuming bc cp4)))
  → CliValOK c → RelayValOK x → RelayValOK x′
relayValStep x x′ c (rMove fP fH fF nPH) vfix wUp hc h = relayVal-move x x′ fP vfix h
relayValStep x x′ c (rFwd hHas hFwd nPH) vfix wUp hc h =
  vfix (λ hPre → relayPre-has-⊥ x hPre hHas) h
relayValStep x x′ c (rRecv hPre hHas)    vfix wUp hc h =
  subst RelayValOK (sym (proj₂ (proj₂ (proj₂ (wUp hPre hHas)))))
    (subst CliValOK (proj₁ (proj₂ (proj₂ (wUp hPre hHas)))) hc)

-- the consume-driver value clause across a FIXED phase (the recorded block may
-- still move, but only outside the region the clause reads)
consValFixᵖ : (b b′ : Block₃) (ph : ConsPh)
            → (ConsHeld ph → b′ ≡ b) → ConsValAt b ph → ConsValAt b′ ph
consValFixᵖ b b′ cp0 f h = tt
consValFixᵖ b b′ cp1 f h = tt
consValFixᵖ b b′ cp2 f h = tt
consValFixᵖ b b′ cp3 f h = tt
consValFixᵖ b b′ cp4 f h = trans (f tt) h
consValFixᵖ b b′ cp5 f h = trans (f tt) h
consValFixᵖ b b′ cp6 f h = trans (f tt) h

-- the consume-driver value clause across a genuine `ConsAdv`: the three pre-receive
-- targets are vacuous, the `c34` delivery uses the anchor's cash-out, and the two
-- tail hops use the block fixity
consValAdvᵖ : (b b′ : Block₃) (ph ph′ : ConsPh) → ConsAdv ph ph′
            → (ConsHeld ph → b′ ≡ b) → (ph ≡ cp3 → b′ ≡ blkA)
            → ConsValAt b ph → ConsValAt b′ ph′
consValAdvᵖ b b′ cp0 cp1 c01 f anc h = tt
consValAdvᵖ b b′ cp1 cp2 c12 f anc h = tt
consValAdvᵖ b b′ cp2 cp3 c23 f anc h = tt
consValAdvᵖ b b′ cp3 cp4 c34 f anc h = anc refl
consValAdvᵖ b b′ cp4 cp5 c45 f anc h = trans (f tt) h
consValAdvᵖ b b′ cp5 cp6 c56 f anc h = trans (f tt) h

-- the two `ConsDPh`-level wrappers (`ConsDPh` is an eta record, so matching its
-- constructor exposes the block and phase without any transport)
consDValFix : (cd cd′ : ConsDPh) → cph cd ≡ cph cd′
            → (ConsHeld (cph cd) → cblk cd′ ≡ cblk cd)
            → ConsDValOK cd → ConsDValOK cd′
consDValFix (consD b ph) (consD b′ ph′) refl f h = consValFixᵖ b b′ ph f h

consDValAdv : (cd cd′ : ConsDPh) → ConsAdv (cph cd) (cph cd′)
            → (ConsHeld (cph cd) → cblk cd′ ≡ cblk cd)
            → (cph cd ≡ cp3 → cblk cd′ ≡ blkA)
            → ConsDValOK cd → ConsDValOK cd′
consDValAdv (consD b ph) (consD b′ ph′) ca f anc h = consValAdvᵖ b b′ ph ph′ ca f anc h

------------------------------------------------------------------------
-- (2) The two LEG-level wrappers for clause (8).  Cased on the leg so that
-- `phOf l s` and `cph (consOf l s)` (resp. `cblkOf l s` and `cblk (consOf l s)`)
-- become the SAME term — with `l` a variable both stay stuck.
------------------------------------------------------------------------

-- clause (8) across a step that leaves node D's phase fixed
consValStepFix : (l : TwoLegs) (s s′ : SysState)
               → phOf l s ≡ phOf l s′
               → (ConsHeld (phOf l s) → cblkOf l s′ ≡ cblkOf l s)
               → ConsDValOK (consOf l s) → ConsDValOK (consOf l s′)
consValStepFix legBD s s′ = consDValFix (consOf legBD s) (consOf legBD s′)
consValStepFix legCD s s′ = consDValFix (consOf legCD s) (consOf legCD s′)

-- clause (8) across node D's own genuine advance
consValStepAdv : (l : TwoLegs) (s s′ : SysState)
               → ConsAdv (phOf l s) (phOf l s′)
               → (ConsHeld (phOf l s) → cblkOf l s′ ≡ cblkOf l s)
               → (phOf l s ≡ cp3 → cblkOf l s′ ≡ blkA)
               → ConsDValOK (consOf l s) → ConsDValOK (consOf l s′)
consValStepAdv legBD s s′ = consDValAdv (consOf legBD s) (consOf legBD s′)
consValStepAdv legCD s s′ = consDValAdv (consOf legCD s) (consOf legCD s′)

------------------------------------------------------------------------
-- (3) The two SERVER clauses.  These are the only ones needing the WHOLE-SYSTEM
-- step: the raw `BfsSucc` witness pins the successor to `bsBlk1 b″` and the label
-- to `apiBF … sendBFBlock b″`, and `PipeValProd`'s produce-frame cones read
-- `b″ ≡ blkA` off the driver's `!`.  Cased on the leg, since each leg has its own
-- link and hence its own cone.
------------------------------------------------------------------------

-- clause (1): node A's upstream BF server
upSrvValStep : (l : TwoLegs) (r : RState) (s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → SrvValEvo (upLinkOf l) (upSrv l (toSys r)) (upSrv l s′) e a
  → SrvValOK (upSrv l (toSys r)) → SrvValOK (upSrv l s′)
upSrvValStep legBD r s′ step (inj₁ eq)                    h = subst SrvValOK eq h
upSrvValStep legBD r s′ step (inj₂ (inj₁ nb))             h = ¬blk⇒srvVal (upSrv legBD s′) nb
upSrvValStep legBD r s′ step (inj₂ (inj₂ (b″ , lbl , eq))) h =
  subst SrvValOK (sym eq)
    (prodFire-blkA-AB r (subst (λ z → radec r ─[ ev (evl z) ]─► _) lbl step))
upSrvValStep legCD r s′ step (inj₁ eq)                    h = subst SrvValOK eq h
upSrvValStep legCD r s′ step (inj₂ (inj₁ nb))             h = ¬blk⇒srvVal (upSrv legCD s′) nb
upSrvValStep legCD r s′ step (inj₂ (inj₂ (b″ , lbl , eq))) h =
  subst SrvValOK (sym eq)
    (prodFire-blkA-AC r (subst (λ z → radec r ─[ ev (evl z) ]─► _) lbl step))

-- clause (5): the relay's downstream BF server.  The relay produces with the block
-- it recorded, so the cone is CONDITIONAL on clause (4) at the source state
dnSrvValStep : (l : TwoLegs) (r : RState) (s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → SrvValEvo (linkOf l) (dnSrv l (toSys r)) (dnSrv l s′) e a
  → RelayValOK (relayOf l (toSys r))
  → SrvValOK (dnSrv l (toSys r)) → SrvValOK (dnSrv l s′)
dnSrvValStep legBD r s′ step (inj₁ eq)                    hr h = subst SrvValOK eq h
dnSrvValStep legBD r s′ step (inj₂ (inj₁ nb))             hr h = ¬blk⇒srvVal (dnSrv legBD s′) nb
dnSrvValStep legBD r s′ step (inj₂ (inj₂ (b″ , lbl , eq))) hr h =
  subst SrvValOK (sym eq)
    (prodFire-relayVal-BD r (subst (λ z → radec r ─[ ev (evl z) ]─► _) lbl step) hr)
dnSrvValStep legCD r s′ step (inj₁ eq)                    hr h = subst SrvValOK eq h
dnSrvValStep legCD r s′ step (inj₂ (inj₁ nb))             hr h = ¬blk⇒srvVal (dnSrv legCD s′) nb
dnSrvValStep legCD r s′ step (inj₂ (inj₂ (b″ , lbl , eq))) hr h =
  subst SrvValOK (sym eq)
    (prodFire-relayVal-CD r (subst (λ z → radec r ─[ ev (evl z) ]─► _) lbl step) hr)

------------------------------------------------------------------------
-- (4) `legStepV`: dispatch a `LegDriverStep` + its `LegValStep` to the eight
-- `PipeVal` clauses.  `with`-free: every arm is a direct clause match.
------------------------------------------------------------------------

legStepV : (l : TwoLegs) (r : RState) (s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → LegDriverStep l (toSys r) s′ e a → LegValStep l (toSys r) s′ e a
  → PipeVal l (toSys r) → PipeVal l s′
legStepV l r s′ step (ldProd padv re ce cue cde ue de) lv
                     (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
    upSrvValStep l r s′ step (lvUpSrv lv) h1
  , subst CellValOK  cue h2
  , subst CliValOK   ue  h3
  , subst RelayValOK re  h4
  , dnSrvValStep l r s′ step (lvDnSrv lv) h4 h5
  , subst CellValOK  cde h6
  , subst CliValOK   de  h7
  , consValStepFix l (toSys r) s′ ce (lvCons lv) h8
legStepV l r s′ step (ldRelay rk pe ce cue cde de upEvo wUp) lv
                     (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
    upSrvValStep l r s′ step (lvUpSrv lv) h1
  , subst CellValOK cue h2
  , cliValEvo (upClient l (toSys r)) (upClient l s′) upEvo h3
  , relayValStep (relayOf l (toSys r)) (relayOf l s′) (upClient l (toSys r))
                 rk (lvRelay lv) wUp h3 h4
  , dnSrvValStep l r s′ step (lvDnSrv lv) h4 h5
  , subst CellValOK cde h6
  , subst CliValOK  de  h7
  , consValStepFix l (toSys r) s′ ce (lvCons lv) h8
legStepV l r s′ step (ldCons cadv lbl pe re cue cde ue dnEvo wDn) lv
                     (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
    upSrvValStep l r s′ step (lvUpSrv lv) h1
  , subst CellValOK  cue h2
  , subst CliValOK   ue  h3
  , subst RelayValOK re  h4
  , dnSrvValStep l r s′ step (lvDnSrv lv) h4 h5
  , subst CellValOK  cde h6
  , cliValEvo (dnClient l (toSys r)) (dnClient l s′) dnEvo h7
  , consValStepAdv l (toSys r) s′ cadv (lvCons lv)
      (λ hcp → trans (proj₁ (proj₂ (proj₂ (lbl hcp))))
                     (subst CliValOK (proj₂ (proj₂ (proj₂ (lbl hcp)))) h7))
      h8
legStepV l r s′ step (ldFix pe re ce cue cde ue de) lv
                     (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
    upSrvValStep l r s′ step (lvUpSrv lv) h1
  , subst CellValOK  cue h2
  , subst CliValOK   ue  h3
  , subst RelayValOK re  h4
  , dnSrvValStep l r s′ step (lvDnSrv lv) h4 h5
  , subst CellValOK  cde h6
  , subst CliValOK   de  h7
  , consValStepFix l (toSys r) s′ ce (lvCons lv) h8

------------------------------------------------------------------------
-- (5) The two content-carrying arms of the dispatch.
------------------------------------------------------------------------

-- the api-CSBF arm: one `let` over the reflect bridge (`with`-FREE by design)
evStepV-api : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
evStepV-api l r aic apimem step =
  let (r′ , Mr , ld , _ , lv) = reach-ev-driver l r aic apimem step
  in  r′ , Mr , legStepV l r (toSys r′) step ld lv

-- the `break` frame at `PipeVal`: no node moves and `phase` is preserved, so all
-- eight components are fixed (mirror `PipeEvStep.frame-break`)
frame-breakV : (l : TwoLegs) (s : SysState) (m′ : MedState)
             → phase m′ ≡ phase (med s)
             → PipeVal l s → PipeVal l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
frame-breakV legBD s m′ pheq =
  pipeVal-frame legBD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl
    (cong (λ ph → ph linkAB hi N2N_BlockFetch) (sym pheq)) refl refl refl
    (cong (λ ph → ph linkBD hi N2N_BlockFetch) (sym pheq)) refl refl
frame-breakV legCD s m′ pheq =
  pipeVal-frame legCD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl
    (cong (λ ph → ph linkAC hi N2N_BlockFetch) (sym pheq)) refl refl refl
    (cong (λ ph → ph linkCD hi N2N_BlockFetch) (sym pheq)) refl refl

-- the `break` arm (mirror `PipeEvStep.evStep-break`; a single `let`)
evStepV-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
evStepV-break l r l₀ {a} step =
  let (m′ , medStep , pheq , Meq) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]═► ⟦ s′ ⟧
      wrun = wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l₀} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl
      r′ : RState
      r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
  in  r′
    , trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun))
    , frame-breakV l (toSys r) m′ pheq

------------------------------------------------------------------------
-- (6) `evStepV` — the TOTAL visible-middle combinator at `PipeVal`.  Label
-- dispatch VERBATIM `PipeEvStep.evStep`'s.
------------------------------------------------------------------------

evStepV : (l : TwoLegs) → EvStepV l
evStepV l r {evLabel _ (apiCS l₀ d₀ m) a} step = evStepV-api l r aicCS tt step
evStepV l r {evLabel _ (apiBF l₀ d₀ m) a} step = evStepV-api l r aicBF tt step
evStepV l r {evLabel _ (done  l₀ d₀ id) a} step = evStepV-api l r aicDone tt step
evStepV l r {evLabel _ (break l₀) a} step = evStepV-break l r l₀ step
evStepV l r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepV l r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepV l r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepV l r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepV l r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepV l r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepV l r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
evStepV l r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
evStepV l r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
evStepV l r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
evStepV l r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
evStepV l r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)

------------------------------------------------------------------------
-- (7) THE ASSEMBLED WEAK-MOVE VALUE TRANSPORTER.  `PipeValStep.stepEmitV` took
-- both per-step arms as explicit arguments; both are now built, so the weak-move
-- preservation `StepEmitV` is inhabited UNCONDITIONALLY — no premise, no
-- postulate.  This is the object `WalkDeliverB`'s delivery walk consumes.
------------------------------------------------------------------------

-- one weak visible move preserves the per-leg block-VALUE invariant
stepEmitVᶠ : (l : TwoLegs) → StepEmitV l
stepEmitVᶠ l = stepEmitV l (tauIoV l) (evStepV l)
