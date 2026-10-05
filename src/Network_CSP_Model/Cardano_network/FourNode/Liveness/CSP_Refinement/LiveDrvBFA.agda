{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- (T10) NODE A's UP-HOP BLOCKFETCH COUPLING — `LiveDrvBFA`, the `cp4` arm's
-- cross-node fact, and the campaign's FIRST invariant about the PRODUCER node.
--
-- *** WHAT IT SAYS, IN ONE LINE: once node A has fired its `sendBFBatchDone`, its
-- up BF server has left the batch region for good. ***
--
--     UpBd l s = ProdDone (prodOf l s) → SrvBatch (coarsenBFs (upSrv l s)) → ⊥
--
-- *** WHY THE `cp4` ARM NEEDS IT, AND WHY NOTHING LANDED SUPPLIES IT. ***  The arm's
-- leaf (`LiveUpOpen.upStream-⊥`) closes every configuration of the up hop except one
-- — server `bsStream`, cell empty, client `bcStream` — whose only enabled move is
-- NODE A's own api sync, and that sync is offered at `pp6` and nowhere else
-- (`LiveUpOpen` §7's F87 is the machine check).  The token gives `ProdSent` for free
-- at `cp4` (`LiveRelayCS` §5c), i.e. `{pp6 … pp9}`; this coupling removes the three
-- that are past the batch, because `SrvBatch bsStream` holds.  `ProdSent` ∧ ¬`ProdDone`
-- IS `≡ pp6` — §3's `upBd⇒pp6`.
--
-- *** THE ONE HARD STEP, AND WHERE IT IS PAID. ***  Every driver↔peer coupling in
-- this development eventually needs "the peer's api row fired ⇒ its OWN driver
-- moved" — the case `SrvApiRowP`'s fixity arm admits and the model cannot produce.
-- It is NOT payable here: the driver's step is what refutes it and `ldProd` projects
-- that step away.  It is paid at the bundle, in `LiveLegApiCone`'s per-label LANDING
-- family — §2b′⁺'s `SrvBdLand` (the `pp6 → pp7` crossing, reported as the PAIR
-- source-and-target) and `srvBatchKeep-up` (every step already past it), exported as
-- `VisLeaves⁺.vProdBd`/`vUpDone`.  With those two the api class below is FOUR lines.
--
-- CONTENTS: §1 the carried form, its base and its frame; §2 the five step classes;
-- §3 the consumer's sharpening; §4 the guard.
--
-- No postulate, no hole, no `mutual`, no `with` in anything whose type mentions an
-- imported `blkA`-parameterised predicate.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFA
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; input; output )
open import CSP.Examples.Cardano_network.Data p using ( Payload; ChainRange )
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_ )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; IDs )
-- (T10) §5b's two coarse/fine bridges dispatch on the peer's BF STATE at the loop
-- head and the loop re-entry, where `coarsenBFs` is stuck until the state is a
-- constructor (measured: `[UnsolvedConstraints] Is empty: coarsenBFs (bsHead st) …`)
import CSP.Examples.Cardano_network.BlockFetch p as BF

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  -- (T12 close) `med` was a SECOND `open import` of this module at the header's §6 group;
  -- unioned here for the one-import-per-parameterised-module rule
  using ( SysState; initial; nA; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  -- (T12 close) `broken` was a SECOND `open import` of this module, same reason as above
  using ( CopyPhase; empty; full; draining; broken )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
              -- (T10) §5's guard is a dispatch on the RELAY's phase, so its
              -- seventeen shapes are written out and the constructors are needed
              ; CPPh; consuming; producing; cp0; cp1; cp2; cp3; cp4; cp5; cp6 )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( coarsenBFs; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; ProdSent; ProdNotSent; prodSent-notSent-⊥
        ; relayOf; upClient; cellUp; BFcHasBlk
        -- (T10) … and the token itself, which the guard's `ProdSent` consequence reads
        ; PipeInv; PLvl; L0; L1; L2; L3; L4; RelayPre; RelayFwd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA
  using ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA as LIC
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA as LCI
-- (T12 close) ONE import of this module: the alias below was a second `import … as LCI`, so
-- the unqualified names now come off the alias by `open LCI`
open LCI
  -- the two io adjacency transcriptions, MATCHED below (so every constructor is in
  -- scope by name — `LiveDrvBF`'s measured `[PatternShadowsConstructor]` note)
  using ( SrvSendAdj; SrvReadAdj; ssSB; ssNB; ssBlk; ssBD; srReq; srCD
        -- (T10) §5's own: the client's two io adjacency families and the payloads
        -- its cell field refutes
        ; CliSendAdj; CliReadAdj; csReq; csCD; crSB; crNB; crBlk; crBD
        ; nbPayload; bdPayload; cdPayload; rrPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanRead blkA
  using ( sbPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( CellFullBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA
  using ( NoTwoTokens; nUpSrvCli; nUpCellCli )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
-- (T10) §6's arm is `isStable`-scoped, so it needs the reachable-config level and the
-- hop's channel invariant beside the leaf it calls
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
-- (T10) §5's region predicate (and §8's acceptance probe, which pins it to the cone)
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveUpOpen blkA as LUO
-- the api axis: the two (T10) landing facts, and the io axis: `LiveDrvBF`'s two
-- row reducers, reused verbatim at the UP hop (both are stated at an abstract key)
-- (T10) … and §5c's api arm reads the relay's own landing pair, qualified — and (T12 close)
-- this is now the module's ONE import of the cone: the two unqualified names below were a
-- second `open import … using (ProdDone; SrvBatch)`
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiCone blkA as LAC
open LAC using ( ProdDone; SrvBatch )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  using ( VisLeaves⁺; vProdBd; vUpDone
        -- (T10) §7's api arm reads the two SERVER keeps beside them
        ; vUpSrvKeep; vUpSrvGain )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBF blkA
  using ( srvFill-adj; srvRead-adj )

------------------------------------------------------------------------
-- §1  THE COUPLING, ITS BASE AND ITS FRAME.
------------------------------------------------------------------------

-- *** THE COUPLING. ***  A produce driver past its batch-done has its up BF server
-- outside the batch region.  Stated as a REFUTATION rather than as a region
-- membership because that is the shape both the preservation and the consumer want:
-- the arms all end in `⊥` and the consumer contraposes it against `SrvBatch bsStream`
UpBd : TwoLegs → SysState → Set
UpBd l s = ProdDone (prodOf l s) → SrvBatch (coarsenBFs (upSrv l s)) → ⊥

-- BASE — at `initial` node A's two produce drivers are at `pp0`, so `ProdDone` is
-- uninhabited and the clause is vacuous at either leg
upBd-init : (l : TwoLegs) → UpBd l initial
upBd-init legBD () _
upBd-init legCD () _

-- FRAME — the coupling reads exactly two components, so a step fixing both carries
-- it (the `drvBF-frame` shape at node A's slots)
upBd-frame : (l : TwoLegs) (s s′ : SysState)
           → prodOf l s ≡ prodOf l s′
           → coarsenBFs (upSrv l s) ≡ coarsenBFs (upSrv l s′)
           → UpBd l s → UpBd l s′
upBd-frame l s s′ peq seq h hd hb =
  h (subst ProdDone (sym peq) hd) (subst SrvBatch (sym seq) hb)

-- the two node-A slots are fixed whenever node A's RECORD is (the `break`/drain
-- shape, where every node record is a literal)
upBd-fix : (l : TwoLegs) (s s′ : SysState) → nA s ≡ nA s′
         → (prodOf l s ≡ prodOf l s′)
           × (coarsenBFs (upSrv l s) ≡ coarsenBFs (upSrv l s′))
upBd-fix legBD s s′ eq = cong (λ z → SN.NodeStateA.prod-AB z) eq
                       , cong (λ z → coarsenBFs (SN.NodeStateA.bfS-AB z)) eq
upBd-fix legCD s s′ eq = cong (λ z → SN.NodeStateA.prod-AC z) eq
                       , cong (λ z → coarsenBFs (SN.NodeStateA.bfS-AC z)) eq

------------------------------------------------------------------------
-- §2  THE FIVE STEP CLASSES.
--
-- The two io ones and the api one are below; the medium-τ and `break` classes are
-- `upBd-fix` + `upBd-frame` at the consumer, because both keep every node record
-- LITERAL (`LiveChanJoin` §6's drain and break arms pass `refl`).
------------------------------------------------------------------------

-- *** THE PRODUCER's OWN ADVANCE, CLASSIFIED AGAINST THE BATCH. ***  A step that
-- lands node A past its batch-done either started there — and then the source
-- clause applies — or IS the single crossing `a67`, which is the only edge into
-- `ProdDone` and the one the bundle's landing pins
padv-done : {y y′ : ProdPh} → ProdAdv y y′ → ProdDone y′
          → ProdDone y ⊎ ((y ≡ pp6) × (y′ ≡ pp6 → ⊥))
padv-done a01 ()
padv-done a12 ()
padv-done a23 ()
padv-done a34 ()
padv-done a45 ()
padv-done a56 ()
padv-done a67 _ = inj₂ (refl , λ ())
padv-done a78 _ = inj₁ tt
padv-done a89 _ = inj₁ tt

-- *** THE VISIBLE api CLASS. ***  Four lines, and every one of them is a landing
-- the bundle proved: at a step that does NOT move node A's producer the keep pulls
-- the target's batch membership back to the source; at one that does, either the
-- source was already past the batch (the keep again) or the step IS `a67`, and then
-- the pair says the successor's server is at `bsWbd`, which is outside the region.
upBd-api : (l : TwoLegs) (s s′ : SysState)
           {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
         → LegDriverStep l s s′ e a → VisLeaves⁺ l s s′
         → UpBd l s → UpBd l s′
upBd-api l s s′ (ldProd padv _ _ _ _ _ _) vl h hd′ hb′ = arms (padv-done padv hd′)
  where
  arms : ProdDone (prodOf l s) ⊎ ((prodOf l s ≡ pp6) × (prodOf l s′ ≡ pp6 → ⊥)) → ⊥
  arms (inj₁ hd)         = h hd (vUpDone vl hd hb′)
  arms (inj₂ (h6 , ¬h6)) = subst SrvBatch (proj₂ (vProdBd vl h6 ¬h6)) hb′
upBd-api l s s′ (ldRelay _ peq _ _ _ _ _ _ _) vl h hd′ hb′ =
  h hd (vUpDone vl hd hb′)
  where hd = subst ProdDone (sym peq) hd′
upBd-api l s s′ (ldCons _ _ peq _ _ _ _ _ _) vl h hd′ hb′ =
  h hd (vUpDone vl hd hb′)
  where hd = subst ProdDone (sym peq) hd′
upBd-api l s s′ (ldFix peq _ _ _ _ _ _) vl h hd′ hb′ =
  h hd (vUpDone vl hd hb′)
  where hd = subst ProdDone (sym peq) hd′

-- the two io adjacencies against the batch region, at ABSTRACT positions — the
-- `drvBF-fill-at` idiom, and it is forced: the indices of `SrvSendAdj` are stuck
-- applications at the call site, so the constructors cannot be matched there
-- (measured: `[SplitError.UnificationStuck]` at `ssSB`)
srvSend-batch : (q q′ : NS.BFsPos) (x : Payload)
              → SrvSendAdj q x q′ → SrvBatch q′ → SrvBatch q
srvSend-batch .NS.bsWsb      .NS.bsStream _ ssSB      _  = tt
srvSend-batch .NS.bsWnb      .NS.bsIdle   _ ssNB      ()
srvSend-batch .(NS.bsWblk b) .NS.bsStream _ (ssBlk b) _  = tt
srvSend-batch .NS.bsWbd      .NS.bsIdle   _ ssBD      ()

-- … and the READ direction, whose two rows both land OUTSIDE the region
srvRead-batch : (q q′ : NS.BFsPos) (x : Payload)
              → SrvReadAdj q x q′ → SrvBatch q′ → ⊥
srvRead-batch .NS.bsIdle .(NS.bsAreq r) _ (srReq r) ()
srvRead-batch .NS.bsIdle .NS.bsDdone    _ srCD      ()

-- *** THE io FILL CLASS. ***  Node A's driver is fixed across an io step, so the
-- whole question is the server's own wire-send: the two that LAND in the batch
-- region (`bsWsb`/`bsWblk`'s `MsgStartBatch`/`MsgBlock`) start inside it, and the
-- two that leave it (`bsWnb`/`bsWbd`) land at `bsIdle`, which is outside — so the
-- target's membership is contradictory there.  The region is io-closed on the way
-- in, and this arm is where that pays
upBd-fill : (l : TwoLegs) (s s′ : SysState)
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
          → prodOf l s ≡ prodOf l s′
          → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) (input l₀ d₀ id₀) x
          → UpBd l s → UpBd l s′
upBd-fill l s s′ l₀ d₀ id₀ x peq srvP h hd′ hb′ =
  arms (srvFill-adj (upLink l) hi (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x srvP)
  where
  hd : ProdDone (prodOf l s)
  hd = subst ProdDone (sym peq) hd′
  arms : (upSrv l s ≡ upSrv l s′)
         ⊎ SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′)) → ⊥
  arms (inj₁ seq) = h hd (subst SrvBatch (sym (cong coarsenBFs seq)) hb′)
  arms (inj₂ adj) = h hd (srvSend-batch _ _ x adj hb′)

-- *** THE io READ CLASS. ***  Node A's server reads only at `bsIdle`, and both its
-- rows land OUTSIDE the batch region (`bsAreq r`, `bsDdone`), so the target's
-- membership is contradictory on both — which is exactly why `bsAreq` is not in the
-- region (see `LiveLegApiCone`'s `SrvBatch`)
upBd-read : (l : TwoLegs) (s s′ : SysState)
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
          → prodOf l s ≡ prodOf l s′
          → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) (output l₀ d₀ id₀) x
          → UpBd l s → UpBd l s′
upBd-read l s s′ l₀ d₀ id₀ x peq srvP h hd′ hb′ =
  arms (srvRead-adj (upLink l) hi (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x srvP)
  where
  hd : ProdDone (prodOf l s)
  hd = subst ProdDone (sym peq) hd′
  arms : (upSrv l s ≡ upSrv l s′)
         ⊎ SrvReadAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′)) → ⊥
  arms (inj₁ seq) = h hd (subst SrvBatch (sym (cong coarsenBFs seq)) hb′)
  arms (inj₂ adj) = srvRead-batch _ _ x adj hb′

------------------------------------------------------------------------
-- §3  THE CONSUMER's SHARPENING — the arm's own `pin6`.
--
-- `ProdSent` (the token's `L2` producer conjunct, free at `cp4`) is `{pp6 … pp9}`
-- and the coupling removes `{pp7, pp8, pp9}` whenever the server is streaming.  The
-- intersection is the singleton the node-A api sync needs.
------------------------------------------------------------------------

-- a SENT producer that is not past its batch is at `pp6`, and nowhere else
sentNotDone⇒pp6 : (y : ProdPh) → ProdSent y → (ProdDone y → ⊥) → y ≡ pp6
sentNotDone⇒pp6 pp0 () _
sentNotDone⇒pp6 pp1 () _
sentNotDone⇒pp6 pp2 () _
sentNotDone⇒pp6 pp3 () _
sentNotDone⇒pp6 pp4 () _
sentNotDone⇒pp6 pp5 () _
sentNotDone⇒pp6 pp6 _  _  = refl
sentNotDone⇒pp6 pp7 _  nd = ⊥-elim (nd tt)
sentNotDone⇒pp6 pp8 _  nd = ⊥-elim (nd tt)
sentNotDone⇒pp6 pp9 _  nd = ⊥-elim (nd tt)

-- *** THE PIN, AT THE SHAPE `LiveUpOpen.upStream-⊥` TAKES IT. ***  This is the
-- hypothesis that module left open, discharged from the coupling and the token
upBd⇒pp6 : (l : TwoLegs) (s : SysState)
         → UpBd l s → ProdSent (prodOf l s)
         → coarsenBFs (upSrv l s) ≡ NS.bsStream → prodOf l s ≡ pp6
upBd⇒pp6 l s h hs pin =
  sentNotDone⇒pp6 (prodOf l s) hs (λ hd → h hd (subst SrvBatch (sym pin) tt))

------------------------------------------------------------------------
-- §4  THE GUARD — one, at the module's own novelty (the batch region's closure).
--
-- (F88  THE REGION EXCLUDES `bsAreq` ON PURPOSE, AND THE io READ CLASS IS WHY)
--      `LiveLegApiCone.SrvBatch`'s `bsAreq` clause set to `⊤` — the region widened
--      by the one position that makes it api-closed BACKWARDS, which is the shape a
--      reader who has only looked at the api class would choose.
--      *** RED ***: `LiveDrvBFA.agda:188.1-55: [ShouldBeEmpty] SrvBatch
--      (NS.bsAreq r) should be empty, but that's not obvious to me … when checking
--      the clause left hand side srvRead-batch .NS.bsIdle .(NS.bsAreq r) _ (srReq r)
--      ()`, EXIT=42 — the server's own wire-READ of the client's request LANDS at
--      `bsAreq`, so a region containing it is entered by an io step the class cannot
--      refute, and the absurd pattern that carried that arm stops typechecking.  The two directions pull opposite ways and the io one wins:
--      the api entries into `{bsBusy, bsWsb, bsStream, bsWblk}` are all refuted by
--      the bundle's landings instead.  Re-aiming note: F88 dies if `bfSnxt`'s
--      `bsIdle` read row is ever re-targeted away from `bsAreq`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §5  (T10) *** THE `cp4` CLIENT REGION — the arm's LAST invariant. ***
--
-- `LiveUpOpen` §6's leaf closes the client at `bcStream` and §3's sharpening closes
-- it at `bcIdle`; this clause says there is nothing else.  Its five excluded
-- positions are neither refutable by stability nor derivable from a landed invariant
-- — `LiveRelayCS.chanInv-idle-busy` is the machine-checked witness that
-- `(bsIdle , empty , bcBusy)` is channel-consistent AND move-free, and `bcAblk b`'s
-- one surviving configuration (an unread `MsgBatchDone` in the cell) is REACHABLE at
-- `cp3`, so no channel-level clause can exclude it.  It is excluded at `cp4`, and
-- only there, which is why the clause is GUARDED on the relay's own sub-phase.
--
-- *** THREE FIELDS, AND THE TWO COMPANIONS ARE NOT DECORATION: *** the region is left
-- by exactly one step — the client's own wire-READ of a block (`bcStream → bcAblk`) —
-- and refuting that needs "no unread block in the up cell", whose own preservation
-- needs "node A's server holds none".  Both are FREE at the entering step: the client
-- HOLDS there (the landing's second half), so `NoTwoTokens`' `nUpSrvCli`/`nUpCellCli`
-- deliver them.  The merged-field pass in the true direction — one record, three
-- facts that are only jointly realisable.
------------------------------------------------------------------------

-- THE GUARD: the arm's own sub-phase and nothing else.  A single-sub-phase guard is
-- sound here (unlike `DnFresh`'s wide one) because the ESTABLISHMENT is free at the
-- entering step; the guard's job is to keep the clause out of the states where it is
-- false — every relay phase before `cp4`
UpCp4 : CPPh → Set
UpCp4 (consuming _ cp0) = ⊥
UpCp4 (consuming _ cp1) = ⊥
UpCp4 (consuming _ cp2) = ⊥
UpCp4 (consuming _ cp3) = ⊥
UpCp4 (consuming _ cp4) = ⊤
UpCp4 (consuming _ cp5) = ⊥
UpCp4 (consuming _ cp6) = ⊥
UpCp4 (producing _ _)   = ⊥

-- … and its inversion: the guard IS the phase equation the landing's antecedent
-- wants (a total dispatch, so a new sub-phase is a coverage error here too)
upCp4⇒eq : (x : CPPh) → UpCp4 x → Σ[ b ∈ Block₃ ] (x ≡ consuming b cp4)
upCp4⇒eq (consuming b cp0) ()
upCp4⇒eq (consuming b cp1) ()
upCp4⇒eq (consuming b cp2) ()
upCp4⇒eq (consuming b cp3) ()
upCp4⇒eq (consuming b cp4) _ = b , refl
upCp4⇒eq (consuming b cp5) ()
upCp4⇒eq (consuming b cp6) ()
upCp4⇒eq (producing b q)   ()

-- … and the guard's own consequence off the carried token: at `cp4` the level
-- computation kills `L0`/`L1` by `RelayPre` and `L3`/`L4` by `RelayFwd`, so the one
-- surviving level's PRODUCER constraint is `ProdSent` (`LiveRelayCS` §5c's
-- `pipeInv⇒sent-cp4`, restated here because the api arm needs it BELOW that module)
upCp4⇒sent : (l : TwoLegs) (s : SysState)
           → UpCp4 (relayOf l s) → PipeInv l s → ProdSent (prodOf l s)
upCp4⇒sent l s g pinv = arms (upCp4⇒eq (relayOf l s) g) pinv
  where
  arms : Σ[ b ∈ Block₃ ] (relayOf l s ≡ consuming b cp4)
       → PipeInv l s → ProdSent (prodOf l s)
  arms (b , eq) (L0 , _  , hr , _) = ⊥-elim (subst RelayPre eq hr)
  arms (b , eq) (L1 , _  , hr , _) = ⊥-elim (subst RelayPre eq hr)
  arms (b , eq) (L2 , hp , _  , _) = hp
  arms (b , eq) (L3 , _  , hr , _) = ⊥-elim (subst RelayFwd eq hr)
  arms (b , eq) (L4 , _  , hr , _) = ⊥-elim (subst RelayFwd eq hr)

-- the CORE, on three ABSTRACT components and no accessor (`DnFreshC`'s discipline:
-- the preservation calculus is then pure position logic)
record UpCliC (q : NS.BFcPos) (sq : SN.BFsPos) (ph : CopyPhase) : Set where
  constructor mkUpCliC
  field
    ucReg  : LUO.UpCliReg q
    ucSrv  : BFsHasBlk sq → ⊥
    ucCell : CellFullBlk ph → ⊥
open UpCliC public

-- … and the carried form, GUARDED
UpCli : TwoLegs → SysState → Set
UpCli l s = UpCp4 (relayOf l s)
          → UpCliC (coarsenBFc (upClient l s)) (upSrv l s) (cellUp l s)

-- BASE — `initial` puts both relays at `consuming blkA cp0`, so the guard is
-- uninhabited at either leg
upCli-init : (l : TwoLegs) → UpCli l initial
upCli-init legBD ()
upCli-init legCD ()

-- FRAME — the four components the clause reads, fixed
upCli-frame : (l : TwoLegs) (s s′ : SysState)
            → relayOf l s ≡ relayOf l s′
            → coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′)
            → upSrv l s ≡ upSrv l s′ → cellUp l s ≡ cellUp l s′
            → UpCli l s → UpCli l s′
upCli-frame l s s′ req ceq seq pheq h g =
  mkUpCliC (subst LUO.UpCliReg ceq (ucReg src))
           (λ hb → ucSrv src (subst BFsHasBlk (sym seq) hb))
           (λ hc → ucCell src (subst CellFullBlk (sym pheq) hc))
  where src = h (subst UpCp4 (sym req) g)

-- … and the DRAIN shape: the cell may move, but only to a phase that is not `full`,
-- so the third field holds outright and the other two frame
upCli-drainish : (l : TwoLegs) (s s′ : SysState)
               → relayOf l s ≡ relayOf l s′
               → coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′)
               → upSrv l s ≡ upSrv l s′
               → (cellUp l s ≡ cellUp l s′) ⊎ (CellFullBlk (cellUp l s′) → ⊥)
               → UpCli l s → UpCli l s′
upCli-drainish l s s′ req ceq seq (inj₁ pheq) h g =
  upCli-frame l s s′ req ceq seq pheq h g
upCli-drainish l s s′ req ceq seq (inj₂ nb)   h g =
  mkUpCliC (subst LUO.UpCliReg ceq (ucReg src))
           (λ hb → ucSrv src (subst BFsHasBlk (sym seq) hb))
           nb
  where src = h (subst UpCp4 (sym req) g)

------------------------------------------------------------------------
-- §5b  THE POSITION LEMMAS THE CLASSES RUN ON.  Every ADJACENCY dispatch is a NAMED
-- lemma at abstract positions, because the adjacency's indices are stuck
-- applications at the call site (the banked `[SplitError.UnificationStuck]`, and
-- `LiveDrvBF.drvBF-fill-at`'s own reason).
------------------------------------------------------------------------

-- a HOLDING server's coarse position is a `bsWblk` (the fine-to-coarse bridge the io
-- arms need: the adjacencies are coarse and `BFsHasBlk` is fine)
hasBlk⇒wblk : (q : SN.BFsPos) → BFsHasBlk q → Σ[ b ∈ Block₃ ] (coarsenBFs q ≡ NS.bsWblk b)
hasBlk⇒wblk (SN.bsHead st)   ()
hasBlk⇒wblk (SN.bsReq1 r)    ()
hasBlk⇒wblk SN.bsDone1       ()
hasBlk⇒wblk SN.bsStart1      ()
hasBlk⇒wblk SN.bsNoBlk1      ()
hasBlk⇒wblk (SN.bsBlk1 b)    _ = b , refl
hasBlk⇒wblk SN.bsBatchDone1  ()
hasBlk⇒wblk (SN.bsSil st)    ()

-- … and its reverse (the `ssBlk` case reads its source off the ADJACENCY, coarse)
wblk⇒hasBlk : (q : SN.BFsPos) (b : Block₃) → coarsenBFs q ≡ NS.bsWblk b → BFsHasBlk q
wblk⇒hasBlk (SN.bsHead BF.stIdle)      b ()
wblk⇒hasBlk (SN.bsHead BF.stBusy)      b ()
wblk⇒hasBlk (SN.bsHead BF.stStreaming) b ()
wblk⇒hasBlk (SN.bsHead BF.stDone)      b ()
wblk⇒hasBlk (SN.bsReq1 r)    b ()
wblk⇒hasBlk SN.bsDone1       b ()
wblk⇒hasBlk SN.bsStart1      b ()
wblk⇒hasBlk SN.bsNoBlk1      b ()
wblk⇒hasBlk (SN.bsBlk1 b′)   b _ = tt
wblk⇒hasBlk SN.bsBatchDone1  b ()
wblk⇒hasBlk (SN.bsSil BF.stIdle)       b ()
wblk⇒hasBlk (SN.bsSil BF.stBusy)       b ()
wblk⇒hasBlk (SN.bsSil BF.stStreaming)  b ()
wblk⇒hasBlk (SN.bsSil BF.stDone)       b ()

-- NONE of the server's four wire-send TARGETS holds a block, so the second field
-- survives its own hop
sendAdj-tgt : (q q′ : NS.BFsPos) (x : Payload) → SrvSendAdj q x q′
            → (r : SN.BFsPos) → coarsenBFs r ≡ q′ → BFsHasBlk r → ⊥
sendAdj-tgt .NS.bsWsb .NS.bsStream _ ssSB r eq hb = wb (hasBlk⇒wblk r hb)
  where wb : Σ[ b ∈ Block₃ ] (coarsenBFs r ≡ NS.bsWblk b) → ⊥
        wb (b , wq) with trans (sym wq) eq
        ...            | ()
sendAdj-tgt .NS.bsWnb .NS.bsIdle _ ssNB r eq hb = wb (hasBlk⇒wblk r hb)
  where wb : Σ[ b ∈ Block₃ ] (coarsenBFs r ≡ NS.bsWblk b) → ⊥
        wb (b , wq) with trans (sym wq) eq
        ...            | ()
sendAdj-tgt .(NS.bsWblk b) .NS.bsStream _ (ssBlk b) r eq hb = wb (hasBlk⇒wblk r hb)
  where wb : Σ[ b′ ∈ Block₃ ] (coarsenBFs r ≡ NS.bsWblk b′) → ⊥
        wb (b′ , wq) with trans (sym wq) eq
        ...             | ()
sendAdj-tgt .NS.bsWbd .NS.bsIdle _ ssBD r eq hb = wb (hasBlk⇒wblk r hb)
  where wb : Σ[ b ∈ Block₃ ] (coarsenBFs r ≡ NS.bsWblk b) → ⊥
        wb (b , wq) with trans (sym wq) eq
        ...            | ()

-- … and neither of the server's two wire-READ targets holds one either (its own
-- reads are the reader at `bsIdle`, and they land at `bsAreq r`/`bsDdone`)
readAdj-tgt : (q q′ : NS.BFsPos) (x : Payload) → SrvReadAdj q x q′
            → (r : SN.BFsPos) → coarsenBFs r ≡ q′ → BFsHasBlk r → ⊥
readAdj-tgt .NS.bsIdle .(NS.bsAreq r) _ (srReq r) rr eq hb = wb (hasBlk⇒wblk rr hb)
  where wb : Σ[ b ∈ Block₃ ] (coarsenBFs rr ≡ NS.bsWblk b) → ⊥
        wb (b , wq) with trans (sym wq) eq
        ...            | ()
readAdj-tgt .NS.bsIdle .NS.bsDdone _ srCD rr eq hb = wb (hasBlk⇒wblk rr hb)
  where wb : Σ[ b ∈ Block₃ ] (coarsenBFs rr ≡ NS.bsWblk b) → ⊥
        wb (b , wq) with trans (sym wq) eq
        ...            | ()

-- the three RESPONDER and two INITIATOR payloads that are not blocks — the cell
-- field's own refutations at the five harmless fills
sbNotBlk : CellFullBlk (full sbPayload) → ⊥
sbNotBlk ()
nbNotBlk : CellFullBlk (full nbPayload) → ⊥
nbNotBlk ()
bdNotBlk : CellFullBlk (full bdPayload) → ⊥
bdNotBlk ()
rrNotBlk : (r : ChainRange) → CellFullBlk (full (rrPayload r)) → ⊥
rrNotBlk r ()
cdNotBlk : CellFullBlk (full cdPayload) → ⊥
cdNotBlk ()

-- the client's four wire-READ rows against the region: only the BLOCK delivery leaves
-- it, and the cell field is what refutes that one
cliRead-reg : (q q′ : NS.BFcPos) (x : Payload) (ph : CopyPhase)
            → CliReadAdj q x q′ → LUO.UpCliReg q → (CellFullBlk ph → ⊥) → ph ≡ full x
            → LUO.UpCliReg q′
cliRead-reg .NS.bcBusy   .NS.bcStream   _ ph crSB      () _  _
cliRead-reg .NS.bcBusy   .NS.bcIdle     _ ph crNB      () _  _
cliRead-reg .NS.bcStream .(NS.bcAblk b) _ ph (crBlk b) _  nc eq =
  ⊥-elim (nc (subst CellFullBlk (sym eq) tt))
cliRead-reg .NS.bcStream .NS.bcIdle     _ ph crBD      _  _  _  = tt

-- … and its two wire-SEND rows: both start OUTSIDE the region
cliSend-out : (q q′ : NS.BFcPos) (x : Payload) → CliSendAdj q x q′ → LUO.UpCliReg q → ⊥
cliSend-out .(NS.bcWrr r) .NS.bcBusy _ (csReq r) ()
cliSend-out .NS.bcWcd     .NS.bcTerm _ csCD      ()

-- … and neither writes a BLOCK
cliSend-notBlk : (q q′ : NS.BFcPos) (x : Payload) → CliSendAdj q x q′
               → CellFullBlk (full x) → ⊥
cliSend-notBlk .(NS.bcWrr r) .NS.bcBusy .(rrPayload r) (csReq r) hb = rrNotBlk r hb
cliSend-notBlk .NS.bcWcd     .NS.bcTerm .cdPayload     csCD      hb = cdNotBlk hb

-- … and of the server's four, the ONE that writes a block has a source the SECOND
-- field refutes; the other three write a responder message that is not one
srvSend-notBlk : (q q′ : NS.BFsPos) (x : Payload) (sq : SN.BFsPos)
               → coarsenBFs sq ≡ q → SrvSendAdj q x q′ → (BFsHasBlk sq → ⊥)
               → CellFullBlk (full x) → ⊥
srvSend-notBlk .NS.bsWsb .NS.bsStream .sbPayload sq _ ssSB _ hb = sbNotBlk hb
srvSend-notBlk .NS.bsWnb .NS.bsIdle   .nbPayload sq _ ssNB _ hb = nbNotBlk hb
srvSend-notBlk .(NS.bsWblk b) .NS.bsStream .(blkPayload b) sq eq (ssBlk b) ns hb =
  ns (wblk⇒hasBlk sq b eq)
srvSend-notBlk .NS.bsWbd .NS.bsIdle   .bdPayload sq _ ssBD _ hb = bdNotBlk hb

------------------------------------------------------------------------
-- §5c  THE THREE MOVING CLASSES.  Every arm takes its facts ALREADY REDUCED
-- (`LiveDrvBF` §3's idiom), so each is position logic over §5b.
------------------------------------------------------------------------

-- *** THE io READ CLASS. ***  The client is the only reader of this cell;
-- `cliRead-reg` is the whole content and the other two fields ride the drain shape
upCli-read : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → (upSrv l s ≡ upSrv l s′)
             ⊎ SrvReadAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
           → (cellUp l s ≡ cellUp l s′) ⊎ (CellFullBlk (cellUp l s′) → ⊥)
           → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
             ⊎ (CliReadAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
                × (cellUp l s ≡ full x))
           → UpCli l s → UpCli l s′
upCli-read l s s′ x req srvA phq cliA h g =
  mkUpCliC (regArm cliA) (srvArm srvA) (cellArm phq)
  where
  src = h (subst UpCp4 (sym req) g)
  regArm : (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
           ⊎ (CliReadAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
              × (cellUp l s ≡ full x))
         → LUO.UpCliReg (coarsenBFc (upClient l s′))
  regArm (inj₁ ceq)           = subst LUO.UpCliReg ceq (ucReg src)
  regArm (inj₂ (adj , srcf))  =
    cliRead-reg (coarsenBFc (upClient l s)) (coarsenBFc (upClient l s′)) x
                (cellUp l s) adj (ucReg src) (ucCell src) srcf
  -- the server may be the reader too (`bsIdle`'s two rows), and neither of its
  -- targets holds a block
  srvArm : (upSrv l s ≡ upSrv l s′)
           ⊎ SrvReadAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
         → BFsHasBlk (upSrv l s′) → ⊥
  srvArm (inj₁ seq) hb = ucSrv src (subst BFsHasBlk (sym seq) hb)
  srvArm (inj₂ adj) hb =
    readAdj-tgt (coarsenBFs (upSrv l s)) (coarsenBFs (upSrv l s′)) x adj
                (upSrv l s′) refl hb
  cellArm : (cellUp l s ≡ cellUp l s′) ⊎ (CellFullBlk (cellUp l s′) → ⊥)
          → CellFullBlk (cellUp l s′) → ⊥
  cellArm (inj₁ pheq) hc = ucCell src (subst CellFullBlk (sym pheq) hc)
  cellArm (inj₂ nb)   hc = nb hc

-- *** THE io FILL CLASS. ***  The cell goes `empty → full x` and the third field is
-- what has to be RE-ESTABLISHED: of the six wire-sends into this cell only one writes
-- a block, and its own source is refuted by the second field.
--
-- *** THE FILLED CASE CARRIES ITS WRITER, and it has to: *** "the cell filled and
-- NEITHER peer moved" is not refutable from position logic — it is refuted at the
-- caller, by the ownership certificates `LiveLegIoCone.SrvRowP`/`CliRowP` carry in
-- their fixity arms (`LiveChanJoinCS`'s own note on the same case).  So the datum
-- pairs the fill with the row that caused it, and this arm stays position logic
upCli-fill : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → (cellUp l s ≡ cellUp l s′)
             ⊎ ((cellUp l s′ ≡ full x)
                × (SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
                   ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))))
           → (upSrv l s ≡ upSrv l s′)
             ⊎ SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
           → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
             ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
           → UpCli l s → UpCli l s′
upCli-fill l s s′ x req phq srvA cliA h g =
  mkUpCliC (regArm cliA) (srvArm srvA) (cellArm phq)
  where
  src = h (subst UpCp4 (sym req) g)
  regArm : (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
           ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
         → LUO.UpCliReg (coarsenBFc (upClient l s′))
  regArm (inj₁ ceq) = subst LUO.UpCliReg ceq (ucReg src)
  regArm (inj₂ adj) =
    ⊥-elim (cliSend-out (coarsenBFc (upClient l s)) (coarsenBFc (upClient l s′)) x
                        adj (ucReg src))
  srvArm : (upSrv l s ≡ upSrv l s′)
           ⊎ SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
         → BFsHasBlk (upSrv l s′) → ⊥
  srvArm (inj₁ seq) hb = ucSrv src (subst BFsHasBlk (sym seq) hb)
  srvArm (inj₂ adj) hb =
    sendAdj-tgt (coarsenBFs (upSrv l s)) (coarsenBFs (upSrv l s′)) x adj
                (upSrv l s′) refl hb
  cellArm : (cellUp l s ≡ cellUp l s′)
            ⊎ ((cellUp l s′ ≡ full x)
               × (SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
                  ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))))
          → CellFullBlk (cellUp l s′) → ⊥
  cellArm (inj₁ pheq)             hc = ucCell src (subst CellFullBlk (sym pheq) hc)
  cellArm (inj₂ (fq , inj₁ sadj)) hc =
    srvSend-notBlk (coarsenBFs (upSrv l s)) (coarsenBFs (upSrv l s′)) x
                   (upSrv l s) refl sadj (ucSrv src) (subst CellFullBlk fq hc)
  cellArm (inj₂ (fq , inj₂ cadj)) hc =
    cliSend-notBlk (coarsenBFc (upClient l s)) (coarsenBFc (upClient l s′)) x cadj
                   (subst CellFullBlk fq hc)

-- *** THE VISIBLE api CLASS. ***  Two cases and both are the cone's: the relay did
-- not move (its phase AND its up client are fixed, so the clause transports) or the
-- step LANDS it at `cp4` — and then the region comes from the landing's FIRST half
-- and the two companions from `NoTwoTokens` at the source, whose antecedent is the
-- landing's SECOND half.  *** That is why the landing reports the pair. ***
upCli-api : (l : TwoLegs) (s s′ : SysState)
          → cellUp l s ≡ cellUp l s′
          → LAC.UpBfDrv (upClient l s) (upClient l s′) (relayOf l s) (relayOf l s′)
          → ((upSrv l s ≡ upSrv l s′) ⊎ (BFsHasBlk (upSrv l s) → ⊥))
          → ((BFsHasBlk (upSrv l s) → ⊥) → BFsHasBlk (upSrv l s′)
             → ProdNotSent (prodOf l s))
          → ((UpCp4 (relayOf l s) ⊎ BFcHasBlk (upClient l s)) → ProdSent (prodOf l s))
          → NoTwoTokens l s
          → UpCli l s → UpCli l s′
-- (A, cellCp3) both clauses re-cut by one trailing `_`: `UpBfDrv` gained the
-- PRE-REQUEST component, which the `cp4` region does not read
upCli-api l s s′ pheq (inj₁ (req , ceq) , _) keep gain hsent ntt h g =
  mkUpCliC (subst LUO.UpCliReg (cong coarsenBFc ceq) (ucReg src))
           (srvArm keep)
           (λ hc → ucCell src (subst CellFullBlk (sym pheq) hc))
  where
  gsrc = subst UpCp4 (sym req) g
  src  = h gsrc
  -- the server's own fixity is NOT in `UpBfDrv`'s fixity arm (that arm is the
  -- relay's pair); it comes from the cone's server keep, and its second disjunct is
  -- closed by the token's `ProdSent` at the guard
  srvArm : (upSrv l s ≡ upSrv l s′) ⊎ (BFsHasBlk (upSrv l s) → ⊥)
         → BFsHasBlk (upSrv l s′) → ⊥
  srvArm (inj₁ seq) hb = ucSrv src (subst BFsHasBlk (sym seq) hb)
  srvArm (inj₂ nb)  hb =
    prodSent-notSent-⊥ (prodOf l s) (hsent (inj₁ gsrc)) (gain nb hb)
upCli-api l s s′ pheq (inj₂ land , _) keep gain hsent ntt h g =
  mkUpCliC (subst LUO.UpCliReg (sym (proj₁ (land bb heq))) tt)
           tgtSrv
           (λ hc → nUpCellCli ntt (subst CellFullBlk (sym pheq) hc) hold)
  where
  bb : Block₃
  bb = proj₁ (upCp4⇒eq (relayOf l s′) g)
  heq : relayOf l s′ ≡ consuming bb cp4
  heq = proj₂ (upCp4⇒eq (relayOf l s′) g)
  hold : BFcHasBlk (upClient l s)
  hold = proj₂ (land bb heq)
  srcSrv : BFsHasBlk (upSrv l s) → ⊥
  srcSrv hb = nUpSrvCli ntt hb hold
  tgtSrv : BFsHasBlk (upSrv l s′) → ⊥
  tgtSrv = keepArm keep
    where
    keepArm : (upSrv l s ≡ upSrv l s′) ⊎ (BFsHasBlk (upSrv l s) → ⊥)
            → BFsHasBlk (upSrv l s′) → ⊥
    keepArm (inj₁ seq) hb = srcSrv (subst BFsHasBlk (sym seq) hb)
    keepArm (inj₂ nb)  hb =
      prodSent-notSent-⊥ (prodOf l s) (hsent (inj₂ hold)) (gain nb hb)

------------------------------------------------------------------------
-- §5d  (A, cellCp3) *** THE UP FACTOR OF THE `cellCp3` WINDOW: THE RELAY's UP BF
-- CLIENT IS AT `bcIdle` THROUGHOUT ITS PRE-REQUEST REGION. ***
--
--     UpIdl l s = LAC.UpPre (relayOf l s) → coarsenBFc (upClient l s) ≡ NS.bcIdle
--
-- *** WHY IT IS THE MISSING HALF, IN ONE LINE. ***  `LiveChanInv`'s `cvBlk`/`cvStr`
-- already give "an unread block in the up cell ⇒ the READER is inside the streaming
-- region" (`CliStrA`, `LiveChanInv:252-259`), as a theorem off `ChanUp` alone.
-- `CliStrA NS.bcIdle = ⊥`, so this clause and that one contradict at exactly the three
-- sub-phases where the window's antecedent can hold — and the window's conclusion is
-- the fourth, `cp3`.  No landed peer→driver object concludes it: `Coupled` and
-- `SrvCoupled` conclude the hop's PRODUCER, `DrvCp`'s `cp0`/`cp1` are `⊤` and its
-- `cp2`/`cp3` pin the up CS client, and `BFFreshC.bfPh` is `⊤` over the whole window.
--
-- *** THE GUARD, EVALUATED AT THE TARGET POSITIONS BEFORE ANYTHING IS BUILT ON IT
-- (the standing law).  `LAC.UpPre` is `⊤` at `consuming _ {cp0, cp1, cp2}` and `⊥`
-- everywhere else.  The premise's two reachable positions are `AtPos l lpUpCell` /
-- `lpDnCell` (`LiveLegInv:430-431`, `:440-441`), where the consumer holds `RelayPre
-- (relayOf l s)` — machine-enumerated as `consuming b {cp0, cp1, cp2, cp3}`.  So the
-- guard is INHABITED at three of the four and the fourth IS the goal: the clause has
-- content at every position it is consumed at, and nothing is being preserved
-- vacuously. ***  This is the difference from the freshness families, whose regions
-- (`RelayFreshBF`, `RelayFresh`, `RelayRfw`) are `⊥` at their consumer's positions.
--
-- *** AND WHY IT PRESERVES.  *** Out of `bcIdle` the BF client has NO io row at all
-- (`LiveChanInv:507-512`: the two SENDs start at `bcWrr`/`bcWcd`, the four READs at
-- `bcBusy`/`bcStream`), so BOTH io classes are refutations.  Its two api rows —
-- `sendBFRequestRange` and `sendBFClientDone` — are fired by the hop's OWN driver at
-- `cp2 → cp3` and `cp4 → cp5`, i.e. OUTSIDE the region's own advances, and the cone's
-- sharpened `UpBfDrv` is where that is spent: its new component reports the client's
-- fixity across `cp0 → cp1` and `cp1 → cp2` off the `apiCS` head inversion, together
-- with the SOURCE's region membership, so this module needs no `RelayAdv` of its own.
--
-- CARRIED AS `UpJoint`'s THIRD MEMBER, not as a ninth `LegJointU` factor (T11h's fold
-- rule): every class that moves `UpCli` moves this, the five `upJoint-*` wrappers
-- already take every input it needs, and `LiveChanJoin`'s five arm sites are UNCHANGED.
--
-- *** ACCEPTANCE, MEASURED: the gate's `upHalf` — `ChanUp l s → UpIdl l s → CellFull⁺ b
-- (cellUp l s) → RelayPre (relayOf l s) → RelayCp3 (relayOf l s)` — typechecks off this
-- factor and the carried channel invariant AND NOTHING ELSE, in 34 non-comment lines
-- (half one 11, the abstract-position dispatch 10, the composition 5, imports 8).
-- Probed green, `EXIT=0`, warning-clean, then deleted; slice C lands it for real. ***
------------------------------------------------------------------------

-- `bcIdle` is the source of NO client wire-read row, so the io READ class closes on
-- the clause itself (the SEND class reuses `cliSend-out` at `UpCliReg bcIdle = ⊤`)
--
-- (F111  *** IT IS `bcIdle` AND NOT MERELY "SOME PRE-STREAM POSITION" THAT CLOSES THE
--      io READ CLASS. ***)  state the same one-clause absurdity at `bcBusy`, the
--      position one wire-send further on, which the clause could plausibly have named.
--      *** RED ***: `LiveDrvBFA.agda:742.1-23: [ShouldBeEmpty] CliReadAdj NS.bcBusy x
--      q′ should be empty, but the following constructor patterns are valid: …
--      CliReadAdj.crSB … CliReadAdj.crNB … when checking the clause left hand side
--      cliRead-idle-⊥ x q′ ()`, EXIT=42 — `bcBusy` is the source of TWO reads, so a
--      clause pinning the client anywhere but `bcIdle` costs both io classes their free
--      refutation.  Reverted by string inversion.
cliRead-idle-⊥ : (x : Payload) (q′ : NS.BFcPos) → CliReadAdj NS.bcIdle x q′ → ⊥
cliRead-idle-⊥ x q′ ()

-- the carried form, GUARDED on the relay's pre-request region
UpIdl : TwoLegs → SysState → Set
UpIdl l s = LAC.UpPre (relayOf l s) → coarsenBFc (upClient l s) ≡ NS.bcIdle

-- BASE — `initial` puts both relays at `consuming blkA cp0`, INSIDE the guard, so
-- unlike `upCli-init` this one owes the value: both relays' up BF clients are `bcIdle`
upIdl-init : (l : TwoLegs) → UpIdl l initial
upIdl-init legBD _ = refl
upIdl-init legCD _ = refl

-- FRAME — the two components the clause reads, fixed (also the drain and `break`
-- shapes: neither touches the relay's phase or its up client)
upIdl-frame : (l : TwoLegs) (s s′ : SysState)
            → relayOf l s ≡ relayOf l s′
            → coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′)
            → UpIdl l s → UpIdl l s′
upIdl-frame l s s′ req ceq h g =
  trans (sym ceq) (h (subst LAC.UpPre (sym req) g))

-- THE VISIBLE api CLASS — two lines, because the cone's new component states the
-- fixity and the source's region membership TOGETHER
upIdl-api : (l : TwoLegs) (s s′ : SysState)
          → LAC.UpBfDrv (upClient l s) (upClient l s′) (relayOf l s) (relayOf l s′)
          → UpIdl l s → UpIdl l s′
upIdl-api l s s′ (_ , pre) h g =
  trans (cong coarsenBFc (sym (proj₁ (pre g)))) (h (proj₂ (pre g)))

-- THE io FILL CLASS — the relay is fixed and the client either is too or fired a
-- wire-SEND, whose two sources are both outside `UpCliReg`, which `bcIdle` inhabits
upIdl-fill : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
             ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
           → UpIdl l s → UpIdl l s′
upIdl-fill l s s′ x req (inj₁ ceq) h g = upIdl-frame l s s′ req ceq h g
upIdl-fill l s s′ x req (inj₂ adj) h g =
  ⊥-elim (cliSend-out (coarsenBFc (upClient l s)) (coarsenBFc (upClient l s′)) x adj
           (subst LUO.UpCliReg (sym (h (subst LAC.UpPre (sym req) g))) tt))

-- THE io READ CLASS — its mirror, and here the clause refutes the row DIRECTLY:
-- `bcIdle` is not the source of any of the four
upIdl-read : (l : TwoLegs) (s s′ : SysState) (x : Payload)
           → relayOf l s ≡ relayOf l s′
           → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
             ⊎ (CliReadAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
                × (cellUp l s ≡ full x))
           → UpIdl l s → UpIdl l s′
upIdl-read l s s′ x req (inj₁ ceq)          h g = upIdl-frame l s s′ req ceq h g
upIdl-read l s s′ x req (inj₂ (adj , srcf)) h g =
  ⊥-elim (cliRead-idle-⊥ x (coarsenBFc (upClient l s′))
           (subst (λ z → CliReadAdj z x (coarsenBFc (upClient l s′)))
                  (h (subst LAC.UpPre (sym req) g)) adj))

------------------------------------------------------------------------
-- §6  (T10) THE ARM's TWO CONJUNCTS, SHARPENED TOGETHER — what the discharge takes.
------------------------------------------------------------------------

-- *** THE ARM. ***  At `cp4`, with the leg's up hop unbroken and the configuration
-- stable, the relay's up BF client IS at `bcIdle`: the region leaves two positions,
-- `LiveUpOpen`'s leaf refutes the other one, and `upBd⇒pp6` supplies the one
-- cross-node fact that leaf needs.  This is `BFAt`'s `cp4` clause
upCli⇒bcIdle : (l : TwoLegs) (r : RState) (b : Block₃)
             → relayOf l (toSys r) ≡ consuming b cp4
             → broken (med (toSys r)) (upLink l) ≡ false
             → LCI.ChanUp l (toSys r)
             → UpBd l (toSys r) → UpCli l (toSys r)
             → ProdSent (prodOf l (toSys r))
             → isStable (radec r ∖ hidden blkA)
             → coarsenBFc (upClient l (toSys r)) ≡ NS.bcIdle
upCli⇒bcIdle l r b heq hbrk ivU hbd hcli hs sta =
  arms (LUO.upCliReg-cases (coarsenBFc (upClient l (toSys r)))
         (ucReg (hcli (subst UpCp4 (sym heq) tt))))
  where
  arms : (coarsenBFc (upClient l (toSys r)) ≡ NS.bcIdle)
         ⊎ (coarsenBFc (upClient l (toSys r)) ≡ NS.bcStream)
       → coarsenBFc (upClient l (toSys r)) ≡ NS.bcIdle
  arms (inj₁ hidl) = hidl
  arms (inj₂ hst) =
    ⊥-elim (LUO.upStream-⊥ l r hbrk ivU (upBd⇒pp6 l (toSys r) hbd hs) hst sta)

------------------------------------------------------------------------
-- §7  (T10) *** THE CARRIED PAIR. ***  `LiveDrvCSD.DnJoint`'s precedent: the two
-- objects travel as ONE `LegJointU` factor because every step class that moves one
-- moves the other, which halves the arm plumbing (five arms × one argument, not two).
--
-- Each arm below takes its facts ALREADY REDUCED, so `LiveChanJoin`'s edit is one
-- call per class plus the key dispatch that class already performs for `ChanLeg`.
------------------------------------------------------------------------

-- the pair — (A, cellCp3) now a TRIPLE: §5d's factor FOLDED IN rather than appended
-- as a ninth `LegJointU` factor (T11h's rule), which is what keeps `LiveChanJoin`'s
-- five arm sites byte-identical
UpJoint : TwoLegs → SysState → Set
UpJoint l s = UpBd l s × UpCli l s × UpIdl l s

-- BASE
upJoint-init : (l : TwoLegs) → UpJoint l initial
upJoint-init l = upBd-init l , upCli-init l , upIdl-init l

-- the three projections
upJoint⇒bd : (l : TwoLegs) (s : SysState) → UpJoint l s → UpBd l s
upJoint⇒bd l s = proj₁

upJoint⇒cli : (l : TwoLegs) (s : SysState) → UpJoint l s → UpCli l s
upJoint⇒cli l s j = proj₁ (proj₂ j)

-- (A, cellCp3) … and §5d's, the window's up factor
upJoint⇒idl : (l : TwoLegs) (s : SysState) → UpJoint l s → UpIdl l s
upJoint⇒idl l s j = proj₂ (proj₂ j)

-- FRAME — every component fixed (the `break` class, and the drain's miss arm)
upJoint-frame : (l : TwoLegs) (s s′ : SysState)
              → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
              → upClient l s ≡ upClient l s′ → upSrv l s ≡ upSrv l s′
              → cellUp l s ≡ cellUp l s′
              → UpJoint l s → UpJoint l s′
upJoint-frame l s s′ pe re ce se pheq (ub , uc , ui) =
    upBd-frame l s s′ pe (cong coarsenBFs se) ub
  , upCli-frame l s s′ re (cong coarsenBFc ce) se pheq uc
  , upIdl-frame l s s′ re (cong coarsenBFc ce) ui

-- … and the DRAIN shape (the cell may go to a non-`full` phase)
upJoint-drainish : (l : TwoLegs) (s s′ : SysState)
                 → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
                 → upClient l s ≡ upClient l s′ → upSrv l s ≡ upSrv l s′
                 → (cellUp l s ≡ cellUp l s′) ⊎ (CellFullBlk (cellUp l s′) → ⊥)
                 → UpJoint l s → UpJoint l s′
upJoint-drainish l s s′ pe re ce se phq (ub , uc , ui) =
    upBd-frame l s s′ pe (cong coarsenBFs se) ub
  , upCli-drainish l s s′ re (cong coarsenBFc ce) se phq uc
  -- (A, cellCp3) the drain shape differs only in the CELL, which §5d does not read
  , upIdl-frame l s s′ re (cong coarsenBFc ce) ui

-- THE VISIBLE api CLASS
upJoint-api : (l : TwoLegs) (s s′ : SysState)
              {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
            → cellUp l s ≡ cellUp l s′
            → LegDriverStep l s s′ e a → VisLeaves⁺ l s s′
            → LAC.UpBfDrv (upClient l s) (upClient l s′) (relayOf l s) (relayOf l s′)
            → ((UpCp4 (relayOf l s) ⊎ BFcHasBlk (upClient l s)) → ProdSent (prodOf l s))
            → NoTwoTokens l s
            → UpJoint l s → UpJoint l s′
upJoint-api l s s′ pheq ld vl ubf hsent ntt (ub , uc , ui) =
    upBd-api l s s′ ld vl ub
  , upCli-api l s s′ pheq ubf (vUpSrvKeep vl) (vUpSrvGain vl) hsent ntt uc
  -- (A, cellCp3) the SAME cone slot, at its new trailing component
  , upIdl-api l s s′ ubf ui

-- THE io FILL CLASS
upJoint-fill : (l : TwoLegs) (s s′ : SysState)
               (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
             → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
             → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) (input l₀ d₀ id₀) x
             → (cellUp l s ≡ cellUp l s′)
               ⊎ ((cellUp l s′ ≡ full x)
                  × (SrvSendAdj (coarsenBFs (upSrv l s)) x (coarsenBFs (upSrv l s′))
                     ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))))
             → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
               ⊎ CliSendAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
             → UpJoint l s → UpJoint l s′
upJoint-fill l s s′ l₀ d₀ id₀ x pe re srvP phq cliA (ub , uc , ui) =
    upBd-fill l s s′ l₀ d₀ id₀ x pe srvP ub
  , upCli-fill l s s′ x re phq
      (srvFill-adj (upLink l) hi (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x srvP) cliA uc
  , upIdl-fill l s s′ x re cliA ui

-- THE io READ CLASS
upJoint-read : (l : TwoLegs) (s s′ : SysState)
               (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
             → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
             → LIC.SrvRowP (upLink l) hi (upSrv l s) (upSrv l s′) (output l₀ d₀ id₀) x
             → (cellUp l s ≡ cellUp l s′) ⊎ (CellFullBlk (cellUp l s′) → ⊥)
             → (coarsenBFc (upClient l s) ≡ coarsenBFc (upClient l s′))
               ⊎ (CliReadAdj (coarsenBFc (upClient l s)) x (coarsenBFc (upClient l s′))
                  × (cellUp l s ≡ full x))
             → UpJoint l s → UpJoint l s′
upJoint-read l s s′ l₀ d₀ id₀ x pe re srvP phq cliA (ub , uc , ui) =
    upBd-read l s s′ l₀ d₀ id₀ x pe srvP ub
  , upCli-read l s s′ x re
      (srvRead-adj (upLink l) hi (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x srvP)
      phq cliA uc
  , upIdl-read l s s′ x re cliA ui
