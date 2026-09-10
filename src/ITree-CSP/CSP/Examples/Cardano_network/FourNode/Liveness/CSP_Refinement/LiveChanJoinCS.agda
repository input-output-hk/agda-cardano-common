{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LiveChanJoinCS` — *** THE CHAINSYNC CHANNEL INVARIANT'S JOIN ARMS: the whole
-- of item 2b THAT DOES NOT DEPEND ON A CONE. ***
--
-- `LiveChanCS` proves the per-hop ChainSync channel invariant's base, frame and
-- per-class preservation (`chanCS-pres` over the eight `HopEvo` arms); what it does
-- NOT do is thread it along a run.  That is the JOIN — a sixth trailing factor of
-- `LiveChanJoin.LegJointU` plus one arm per FSim step class — and this module is
-- everything in it that can be proved WITHOUT the api/io cones:
--
--   §1  the three REGION BRICKS and the `both peers moved` composition
--       (`chan-bothCsApi`), the CS analogue of `LiveChanInv.chan-bothApi`, plus the
--       two cross-peer wire refutations (`csSend-⊥`/`csRead-⊥`)
--   §2  the two medium key bricks, transcribed from `LiveChanJoin` §2 (see the
--       KEEP-IN-SYNC block: they are channel-GENERIC there, and this module sits
--       BELOW `LiveChanJoin`, which is where the join's factor must be appended)
--   §3  the four CS peers' per-leg FIXITY under a medium-only step and under a
--       drain — the two step classes whose arms need no cone at all
--   §4  *** THE HOP-PARAMETRIC ARMS ***, one per step class, in `LiveChanJoin`
--       §4's shape: `frame`, `drain`, `api` (the twenty-one-clause label dispatch,
--       ONCE for both hops) and `fill`/`read`, the io pair
--   §5  the two hop instances, the leg-level `break`/`drain` arms — FULLY WIRED,
--       nothing outstanding — and the leg-level api/io arms at their per-hop row
--       premises
--
-- *** THE io HALF WAS BLOCKED AND IS NOW GRANTED (owner grant #12). ***  An arm of
-- the join must produce a `HopEvo` for the hop's two peers out of the step, and every
-- `HopEvo` arm names BOTH peers: the mover's adjacency AND the other's fixity.  The
-- api side was already available (`LiveLegApiCone.BundleApiEvo:1275-1276` carries
-- `CScApiRowP`/`CSsApiRowP` for EVERY bundle at EVERY label).  The io side was not:
-- grant #11's `PipeNodeIoEvo.CssFact` is `CSsPos`-typed and reached nodes B and C
-- only, so six of the eight per-leg CS io slots were unreportable — node D's
-- down-hop CS CLIENT among them, and that is exactly the peer `ccPre` is about.
-- Grant #12 closes it: the fifth family `CscFact`, the A/D peel slots, and — the item
-- this module's own `csNoBoth` premise named and the ask first priced at zero — an
-- `IDs`-PARAMETRIC ownership layer, so the CS peers' role certificates come out of
-- grant #7's existing eight per-node witnesses at the same four `(link , hi)` keys.
-- The two families now arrive label-directed and CARRYING the certificate
-- (`LiveLegIoCone.CssIoRowP`/`CscIoRowP`), so §4's io arms discharge the
-- *(neither peer moved)* case internally and take no premise at all.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- the NON-polymorphic `⊤`, qualified: the carrier of the `done` event
import Data.Unit as U0
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong )

-- the `_≟_` the two medium key bricks of §2 dispatch on (`Link = Fin numLinks`,
-- `Dir`, `IDs`), and the instances the CS tables' own comparisons need
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanJoinCS
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Link; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF
  ; done; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break
  ; ApiCSTag; ApiCSCar ; store; env )
open import CSP.Examples.Cardano_network.Data p using ( Payload; Messages )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs; DecEq-Dir; DecEq-IDs
  -- (T6c) the payload's ROLE — the two `Mode` constructors are what make the
  -- *(neither peer moved)* case of an io FILL refutable at the CS channel too
  ; Mode; FromInitiator; FromResponder
  ; N2N_BlockFetch; N2N_ChainSync; N2N_KeepAlive; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS )
import CSP.Examples.Cardano_network.ChainSync p as CS

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; phase; MedState; mkMed; broken )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( coarsenCSs; coarsenCSc )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  using ( drainSucc )
-- (T6c) the payload's ROLE, channel-generic (`SysIoLink:2471-2481` — no `IDs`
-- occurs in either predicate), and the two ownership pairs the granted cone's
-- fixity arms carry
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink blkA
  using ( ClientIo; ServerIo; msgOrigin )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( NoCliIoAt; NoSrvIoAt )
-- (T6c, grant #12) *** THE TWO CS io FACT FAMILIES ARE THE CONE'S OWN. ***  They were
-- defined locally here while the io half was blocked; now that `factsP` carries them
-- the definitions live at the producer and this module consumes them, so the arms
-- take the cone's slots with no conversion at all.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( CssIoRowP; CscIoRowP )
-- the T4 row layer: the coarse ROW of a CS peer, its key pin, and the api-axis
-- label-directed facts the api cone threads
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CSsRow; CScRow; cssRow-key; cscRow-key
        ; CScApiRowP; CSsApiRowP )
-- the layer itself: the invariant, its regions, its adjacencies, its producers and
-- its per-hop instances
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA
  using ( ChanCS; mkChanCS; ccQui; ccPre; ccReq
        ; SrvPre; CliAwt; CellPreQ
        ; SrvApiAdj; saReq; saFI; saDone; saRF; saRB; saAR; saMRF; saMRB; saIF; saINF
        ; CliApiAdj; caReq; caFI; caDone; caRecvF; caRecvB; caRecvIF; caRecvIN
        ; SrvSendAdj; ssRF; ssRB; ssAR; ssIF; ssINF
        ; CliSendAdj; csReq; csFI; csDone
        ; SrvReadAdj; srReq; srFI; srDone
        ; CliReadAdj; crRF; crRB; crAR; crMRF; crMRB; crIF; crINF
        ; srvApiRow; srvDoneRow; cliApiRow; cliDoneRow-⊥
        ; srvSendRow; cliSendRow; srvReadRow; cliReadRow
        ; chan-srvApi; chan-cliApi; chan-srvSend; chan-cliSend
        ; chan-srvRead; chan-cliRead
        ; HopEvo; heFrame; heSrvApi; heCliApi; heSrvSend; heCliSend
        ; heSrvRead; heCliRead; heDrain
        ; chanCS-frame; chanCS-pres-eq; chanCS-pres-eq²
        ; upCSsOf; upCScOf; dnCSsOf; dnCScOf; cellCSUp; cellCSDn
        ; ChanCSUp; ChanCSDn; ChanCSLeg )

------------------------------------------------------------------------
-- §1  THE REGION BRICKS, THE `BOTH MOVED` COMPOSITION AND THE TWO CROSS-PEER WIRE
-- REFUTATIONS.  Everything here is about the ADJACENCIES alone — no leg, no link,
-- no medium — so it is shared by both hops with no instantiation.
------------------------------------------------------------------------

-- a server api edge that LANDS in the pre region also STARTS there.  Read off §4:
-- only `saReq` (`csAreq → csCanAwait`), `saFI` (`csAfi → csInt`) and `saAR`
-- (`csCanAwait → csWar`) have a target in `SrvPre`, and all three have a source in
-- it; the other seven land outside, where the antecedent is `⊥`.
srvApiAdj-pre : {sa sa′ : NS.CSsPos} → SrvApiAdj sa sa′ → SrvPre sa′ → SrvPre sa
srvApiAdj-pre saReq        h = tt
srvApiAdj-pre (saFI ps)    h = tt
srvApiAdj-pre saAR         h = tt
srvApiAdj-pre saDone       ()
srvApiAdj-pre (saRF ht)    ()
srvApiAdj-pre (saRB pt)    ()
srvApiAdj-pre (saMRF ht)   ()
srvApiAdj-pre (saMRB pt)   ()
srvApiAdj-pre (saIF pt)    ()
srvApiAdj-pre (saINF tp)   ()

-- *** NO CLIENT api EDGE STARTS IN THE AWAITING REGION. ***  All seven `CliApiAdj`
-- sources are `ccIdle` or one of the four `ccA*` emits, and `CliAwt` is `⊥` at
-- every one of them — which is the whole reason `chan-cliApi`'s seven clauses can
-- share one body, and the brick the `both moved` case below turns on.
cliApiAdj-notAwt : {ca ca′ : NS.CScPos} → CliApiAdj ca ca′ → CliAwt ca → ⊥
cliApiAdj-notAwt caReq         ()
cliApiAdj-notAwt (caFI ps)     ()
cliApiAdj-notAwt caDone        ()
cliApiAdj-notAwt (caRecvF ht)  ()
cliApiAdj-notAwt (caRecvB pt)  ()
cliApiAdj-notAwt (caRecvIF pt) ()
cliApiAdj-notAwt (caRecvIN tp) ()

-- *** BOTH PEERS MOVED ON ONE api LABEL — the CS analogue of
-- `LiveChanInv.chan-bothApi`, and it needs no case analysis at all. ***  The cell is
-- fixed, so all three successor clauses have the same shape: whatever puts the
-- SERVER in the pre region at the successor puts it there at the source
-- (`srvApiAdj-pre`), the source's `ccPre` then says the client was AWAITING, and
-- `cliApiAdj-notAwt` says a client that moved on an api was not.  `ccReq` is the
-- same argument off `ccReq` instead of `ccPre`.
--
-- (The case is REACHABLE only vacuously — the two peers of a hop live on different
-- nodes and one api step is one node's — but the row facts do not know that, so the
-- arm has to answer it.)
chan-bothCsApi : (sa sa′ : NS.CSsPos) (ph : CopyPhase) (ca ca′ : NS.CScPos)
               → SrvApiAdj sa sa′ → CliApiAdj ca ca′
               → ChanCS sa ph ca → ChanCS sa′ ph ca′
chan-bothCsApi sa sa′ ph ca ca′ sadj cadj iv =
  mkChanCS (λ h → ⊥-elim (cliApiAdj-notAwt cadj (ccPre iv (srvApiAdj-pre sadj h))))
           (λ h → ⊥-elim (cliApiAdj-notAwt cadj (ccPre iv (srvApiAdj-pre sadj h))))
           (λ h → ⊥-elim (cliApiAdj-notAwt cadj (ccReq iv h)))

-- BOTH peers would have written the SAME payload: impossible.  The server's five
-- wire-send rows are `≟`-gated on RESPONDER tuples and the client's three on
-- INITIATOR ones, so the two indices clash on `Mode` — one absurd pattern per
-- server row (`LiveChanInv.srvSend-cliSend-⊥`'s CS twin).
csSend-⊥ : {sa sa′ : NS.CSsPos} {ca ca′ : NS.CScPos} {x : Payload}
         → SrvSendAdj sa x sa′ → CliSendAdj ca x ca′ → ⊥
csSend-⊥ (ssRF h tp)  ()
csSend-⊥ (ssRB pt tp) ()
csSend-⊥ ssAR         ()
csSend-⊥ (ssIF pt tp) ()
csSend-⊥ (ssINF tp)   ()

-- … and BOTH would have READ it: the server reads the three INITIATOR messages and
-- the client the five RESPONDER ones, so the clash is on `MessageChainSync` (the
-- read rows are lenient in the tuple's first three components, which is why the
-- dispatch is on the SERVER's row and the message does the work)
csRead-⊥ : {sa sa′ : NS.CSsPos} {ca ca′ : NS.CScPos} {x : Payload}
         → SrvReadAdj sa x sa′ → CliReadAdj ca x ca′ → ⊥
csRead-⊥ srReq     ()
csRead-⊥ (srFI ps) ()
csRead-⊥ srDone    ()

------------------------------------------------------------------------
-- §2  THE TWO MEDIUM KEY BRICKS.
--
-- *** KEEP IN SYNC WITH `LiveChanJoin` §2 (`drain-cell-at` `:278-288`, `setRead⁺`
-- `:316-327`), CLAUSE BY CLAUSE. ***  Both are transcribed VERBATIM — they are
-- stated at an ABSTRACT key `(kl , kd , kid)` there and are therefore already
-- channel-generic, so no deviation was needed and none was made.
--
-- *** WHY A COPY AND NOT AN IMPORT. ***  `LiveChanJoin` is where the join's sixth
-- factor must be APPENDED (`LegJointU:199-201`), so `LiveChanJoin` will import THIS
-- module and this module cannot import it.  The two bricks are the only pieces of
-- `LiveChanJoin` §2 that are channel-generic — its four row-refutation tables and
-- its two ownership refutations are BF-keyed in their statements — so the honest
-- follow-up is to move exactly these two DOWN (to `PipeMedKey`, whose `setRead` and
-- `cell-drain-eq` they are the key-keeping variants of) and have both joins import
-- them; that is a landed-file edit inside the endpoint closure and is recorded as a
-- T6c follow-up rather than taken here.
------------------------------------------------------------------------

-- the drain's effect at ONE key: untouched, or this IS the drained key
drain-cell-at : (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                (kl : Link) (kd : Dir) (kid : IDs)
  → (phase (med (drainSucc s i d₀ id₀)) kl kd kid ≡ phase (med s) kl kd kid)
    ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
       × (phase (med (drainSucc s i d₀ id₀)) kl kd kid ≡ empty))
drain-cell-at s i d₀ id₀ kl kd kid with kl ≟ i
... | no  _ = inj₁ refl
... | yes refl with kd ≟ d₀ | kid ≟ id₀
...   | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
...   | no  _    | _        = inj₁ refl
...   | yes refl | no  _    = inj₁ refl

-- the io write's effect at ONE key, WITH the miss's reason kept
setRead⁺ : (g : Link → Dir → IDs → CopyPhase) (i : Link) (d₀ : Dir) (id₀ : IDs)
           (np : CopyPhase) (kl : Link) (kd : Dir) (kid : IDs)
  → (((kl ≡ i → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (kid ≡ id₀ → ⊥))
      × (g kl kd kid ≡ phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid))
    ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
       × (phase-upd g i (setCell (g i) d₀ id₀ np) kl kd kid ≡ np))
setRead⁺ g i d₀ id₀ np kl kd kid with kl ≟ i
... | no ¬p = inj₁ (inj₁ ¬p , refl)
setRead⁺ g i d₀ id₀ np kl kd kid | yes refl with kd ≟ d₀ | kid ≟ id₀
... | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
... | no ¬q    | _        = inj₁ (inj₂ (inj₁ ¬q) , refl)
... | yes refl | no ¬n    = inj₁ (inj₂ (inj₂ ¬n) , refl)

------------------------------------------------------------------------
-- §2b  THE CS io FACT, AND ITS OFF-KEY REFUTATION.
--
-- `CssIoRowP`/`CscIoRowP` are the io-axis twins of `LiveCSRow`'s `CSsApiRowP`/
-- `CScApiRowP`: "the peer is FIXED, or its coarse table fired at this label", and —
-- *** LIKE THEM, AND UNLIKE THE T5 CONE'S `CssRowP`, LABEL-DIRECTED. ***  Written
-- here because the arms of §4 must be STATED at BOTH peers and the cone has a type
-- for the server only (and only for the two relay ones; see the header).
--
-- *** WHY LABEL-DIRECTED, MEASURED. ***  `LiveLegIoCone.CssRowP` is the BARE
-- disjunction at every label, so a consumer holding it at `input l₀ d₀ id₀` for a
-- FOREIGN channel must refute a `csSnxt` row at a VARIABLE position — and that does
-- NOT reduce: Agda stops at the first blocked pattern, so the table's catch-all
-- (`NodeSpecs:490`) is unreachable while the position is a variable, even though
-- every informative clause mismatches on the event (measured: `[UnequalTerms]
-- NS.csSnxt k kd (coarsenCSs sa) (Payload , input l₀ d₀ N2N_BlockFetch) x !=
-- nothing`).  Refuting it position by position costs the full ROW→ADJACENCY
-- dispatch — 38 + 18 + 27 + 27 ≈ 110 clauses for the four tables, the T6b pricing
-- law's shape exactly.  Making the FACT label-directed instead costs nothing at all:
-- the BF axis already does it (`LiveLegIoCone.SrvRowP`/`CliRowP`, which is why
-- `LiveChanJoin.srvRow-off` is nine lines), and the io cone's own producer `bdP`
-- answers the CS slot with `inj₁ refl` at all twenty-five non-CS clauses anyway, so
-- the label-directed answer there is `refl` — a two-token change per clause.
--
-- HOW THE io WIRING LANDED (grant #12, `d5a64ab`), so a successor reads the tree and
-- not a recommendation: the io cone instantiates `PipeNodeIoEvo.Csf` at the **PAIR**
-- `LiveLegIoCone.CssPairP = CssRowP × CssIoRowP` — grant #11's frozen fact FIRST, the
-- label-directed one SECOND — and `Cscf` at `CscIoRowP` bare.  The pair is why
-- `AllCssFacts` never had to widen and `LiveDrvBF`'s four io arms are byte-identical:
-- they still read `CssRowP`, through one `proj₁` in `LiveChanJoin.dnCssRow`.  Every
-- arm of §4 takes the SECOND component, so the CS io slots of `AllCssP`/`AllCssUpP`
-- are reached by `proj₂` and the client slots of `AllCscP` directly
-- (`LiveChanJoin` §5d's four leg dispatches).  On the ChainSync channel the two
-- components are interconvertible for free (`inj₁`/`inj₂` pass straight through);
-- off it the conversion is only free AT THE PRODUCER, which is why the pair — and not
-- a conversion — is what the cone carries.
--
-- The off-key refutation is then nine lines per table: on the ChainSync channel the
-- label IS `ιCS (sendCS l₀ d₀)` definitionally (`NetworkPar:184-185`), so
-- `LiveCSRow.cssRow-key` recovers the fired key and contradicts the miss; off it the
-- fact IS the fixity equation.
------------------------------------------------------------------------

-- *** KEEP IN SYNC WITH `LiveChanJoin` §2 (`role-in` `:330-334`, `role-out`
-- `:337-341`, `fill-noPeer-⊥` `:345-350`, `read-noPeer-⊥` `:353-358`), LEMMA BY
-- LEMMA. ***  All four below are those four VERBATIM modulo the channel: `role-in`/
-- `role-out` are already channel-generic there (they read `msgOrigin` and mention no
-- `IDs`) and are transcribed unchanged; the two `-noPeer-⊥` twins are the same two
-- clauses with `N2N_BlockFetch` replaced by `N2N_ChainSync` throughout, and the same
-- `proj₁`/`proj₂` halves (`NoCliIoAt` is READ × WRITE, `NoSrvIoAt` is WRITE × READ —
-- get that backwards and the fill/read arms swap silently).
--
-- *** WHY A MARKER AND NOT JUST THE PROSE BELOW. ***  F40's banked lesson: a
-- falsification that collapses one of these onto its twin cannot be reverted by
-- string match (it happened — `srvSendMoveCS-at-⊥` became a byte-identical copy of
-- its BF twin and the revert found two occurrences).  Provenance in prose does not
-- flag that hazard; the marker convention does.  See also M-2: `role-in`/`role-out`
-- are now live in TWO files and the dedup is free — `LiveChanJoin` imports this
-- module, so its two copies can be deleted and re-pointed here (~10 lines, no
-- cycle).  Parked as a follow-up beside `drain-cell-at`/`setRead⁺` → `PipeMedKey`;
-- NOT done here, because this round is comment-only.
--
-- *** THE PAYLOAD's ROLE, and the two CS ownership refutations. ***  Every wire
-- payload is client- or server-originated (`Mode` has exactly two constructors), and
-- that is what refutes "the CS cell moved while BOTH of the hop's peers stayed
-- fixed": whichever role the payload carries, THAT peer's certificate — which the
-- granted cone's fixity arm now hands over — contradicts the fired label at its own
-- key.  This is `LiveChanJoin`'s `role-in`/`fill-noPeer-⊥` pair at the ChainSync
-- channel, and the pair is channel-generic there, so only the instantiation is new.
role-in : (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
        → ClientIo (input l₀ d₀ id₀) x ⊎ ServerIo (input l₀ d₀ id₀) x
role-in l₀ d₀ id₀ (t , md , ln , msg) with msgOrigin msg
... | FromInitiator = inj₁ refl
... | FromResponder = inj₂ refl

-- … and at a READ label (the roles swap: a client READS responder messages)
role-out : (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
         → ClientIo (output l₀ d₀ id₀) x ⊎ ServerIo (output l₀ d₀ id₀) x
role-out l₀ d₀ id₀ (t , md , ln , msg) with msgOrigin msg
... | FromResponder = inj₁ refl
... | FromInitiator = inj₂ refl

-- NEITHER CS peer moved while the cell FILLED: the two certificates decide it
csFill-noPeer-⊥ : (k : Link) (kd : Dir) (x : Payload)
  → ClientIo (input k kd N2N_ChainSync) x ⊎ ServerIo (input k kd N2N_ChainSync) x
  → NoSrvIoAt k kd N2N_ChainSync (input k kd N2N_ChainSync) x
  → NoCliIoAt k kd N2N_ChainSync (input k kd N2N_ChainSync) x → ⊥
csFill-noPeer-⊥ k kd x (inj₁ ci) nsrv ncli = proj₂ ncli refl refl refl ci
csFill-noPeer-⊥ k kd x (inj₂ si) nsrv ncli = proj₁ nsrv refl refl refl si

-- … and the READ mirror (the certificates' other halves)
csRead-noPeer-⊥ : (k : Link) (kd : Dir) (x : Payload)
  → ClientIo (output k kd N2N_ChainSync) x ⊎ ServerIo (output k kd N2N_ChainSync) x
  → NoSrvIoAt k kd N2N_ChainSync (output k kd N2N_ChainSync) x
  → NoCliIoAt k kd N2N_ChainSync (output k kd N2N_ChainSync) x → ⊥
csRead-noPeer-⊥ k kd x (inj₁ ci) nsrv ncli = proj₁ ncli refl refl refl ci
csRead-noPeer-⊥ k kd x (inj₂ si) nsrv ncli = proj₂ nsrv refl refl refl si

-- a fired SERVER row is impossible away from the hop's own key, at a WRITE label
cssRow-off : (k : Link) (kd : Dir) (sa sa′ : SN.CSsPos)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_ChainSync ≡ id₀ → ⊥))
  → CssIoRowP k kd sa sa′ (input l₀ d₀ id₀) x
  → sa ≡ sa′
cssRow-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x miss (inj₁ fx) = proj₁ fx
cssRow-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₁ ¬p) (inj₂ row) =
  ⊥-elim (¬p (sym (proj₁ (cssRow-key k kd (coarsenCSs sa) (CS.sendCS l₀ d₀) row))))
cssRow-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ ¬q)) (inj₂ row) =
  ⊥-elim (¬q (sym (proj₂ (cssRow-key k kd (coarsenCSs sa) (CS.sendCS l₀ d₀) row))))
cssRow-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ¬n)) (inj₂ row) =
  ⊥-elim (¬n refl)
cssRow-off k kd sa sa′ l₀ d₀ N2N_BlockFetch   x miss fx = fx
cssRow-off k kd sa sa′ l₀ d₀ N2N_KeepAlive    x miss fx = fx
cssRow-off k kd sa sa′ l₀ d₀ N2N_TxSubmission x miss fx = fx
cssRow-off k kd sa sa′ l₀ d₀ N2N_LeiosNotify  x miss fx = fx
cssRow-off k kd sa sa′ l₀ d₀ N2N_LeiosFetch   x miss fx = fx

-- … and at a READ label (the `receiveCS` image, same argument)
cssRowR-off : (k : Link) (kd : Dir) (sa sa′ : SN.CSsPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_ChainSync ≡ id₀ → ⊥))
  → CssIoRowP k kd sa sa′ (output l₀ d₀ id₀) x
  → sa ≡ sa′
cssRowR-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x miss (inj₁ fx) = proj₁ fx
cssRowR-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₁ ¬p) (inj₂ row) =
  ⊥-elim (¬p (sym (proj₁ (cssRow-key k kd (coarsenCSs sa) (CS.receiveCS l₀ d₀) row))))
cssRowR-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ ¬q)) (inj₂ row) =
  ⊥-elim (¬q (sym (proj₂ (cssRow-key k kd (coarsenCSs sa) (CS.receiveCS l₀ d₀) row))))
cssRowR-off k kd sa sa′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ¬n)) (inj₂ row) =
  ⊥-elim (¬n refl)
cssRowR-off k kd sa sa′ l₀ d₀ N2N_BlockFetch   x miss fx = fx
cssRowR-off k kd sa sa′ l₀ d₀ N2N_KeepAlive    x miss fx = fx
cssRowR-off k kd sa sa′ l₀ d₀ N2N_TxSubmission x miss fx = fx
cssRowR-off k kd sa sa′ l₀ d₀ N2N_LeiosNotify  x miss fx = fx
cssRowR-off k kd sa sa′ l₀ d₀ N2N_LeiosFetch   x miss fx = fx

-- the CLIENT twins
cscRow-off : (k : Link) (kd : Dir) (ca ca′ : SN.CScPos)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_ChainSync ≡ id₀ → ⊥))
  → CscIoRowP k kd ca ca′ (input l₀ d₀ id₀) x
  → ca ≡ ca′
cscRow-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x miss (inj₁ fx) = proj₁ fx
cscRow-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₁ ¬p) (inj₂ row) =
  ⊥-elim (¬p (sym (proj₁ (cscRow-key k kd (coarsenCSc ca) (CS.sendCS l₀ d₀) row))))
cscRow-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ ¬q)) (inj₂ row) =
  ⊥-elim (¬q (sym (proj₂ (cscRow-key k kd (coarsenCSc ca) (CS.sendCS l₀ d₀) row))))
cscRow-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ¬n)) (inj₂ row) =
  ⊥-elim (¬n refl)
cscRow-off k kd ca ca′ l₀ d₀ N2N_BlockFetch   x miss fx = fx
cscRow-off k kd ca ca′ l₀ d₀ N2N_KeepAlive    x miss fx = fx
cscRow-off k kd ca ca′ l₀ d₀ N2N_TxSubmission x miss fx = fx
cscRow-off k kd ca ca′ l₀ d₀ N2N_LeiosNotify  x miss fx = fx
cscRow-off k kd ca ca′ l₀ d₀ N2N_LeiosFetch   x miss fx = fx

cscRowR-off : (k : Link) (kd : Dir) (ca ca′ : SN.CScPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → ((k ≡ l₀ → ⊥) ⊎ (kd ≡ d₀ → ⊥) ⊎ (N2N_ChainSync ≡ id₀ → ⊥))
  → CscIoRowP k kd ca ca′ (output l₀ d₀ id₀) x
  → ca ≡ ca′
cscRowR-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x miss (inj₁ fx) = proj₁ fx
cscRowR-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₁ ¬p) (inj₂ row) =
  ⊥-elim (¬p (sym (proj₁ (cscRow-key k kd (coarsenCSc ca) (CS.receiveCS l₀ d₀) row))))
cscRowR-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₁ ¬q)) (inj₂ row) =
  ⊥-elim (¬q (sym (proj₂ (cscRow-key k kd (coarsenCSc ca) (CS.receiveCS l₀ d₀) row))))
cscRowR-off k kd ca ca′ l₀ d₀ N2N_ChainSync    x (inj₂ (inj₂ ¬n)) (inj₂ row) =
  ⊥-elim (¬n refl)
cscRowR-off k kd ca ca′ l₀ d₀ N2N_BlockFetch   x miss fx = fx
cscRowR-off k kd ca ca′ l₀ d₀ N2N_KeepAlive    x miss fx = fx
cscRowR-off k kd ca ca′ l₀ d₀ N2N_TxSubmission x miss fx = fx
cscRowR-off k kd ca ca′ l₀ d₀ N2N_LeiosNotify  x miss fx = fx
cscRowR-off k kd ca ca′ l₀ d₀ N2N_LeiosFetch   x miss fx = fx

------------------------------------------------------------------------
-- §3  THE FOUR CS PEERS' PER-LEG FIXITY under the two node-preserving step
-- classes.  A `break` replaces the MEDIUM only and a drain keeps all four node
-- records LITERAL (`PipeTauMed.drainSucc:87-91`), so every slot is `refl` once the
-- leg is a CONSTRUCTOR — which is exactly why these two arms need no cone.
------------------------------------------------------------------------

-- all four tracked CS peers are fixed when only the MEDIUM is replaced
break-cs-peers : (l : TwoLegs) (s : SysState) (m′ : MedState)
  → (upCSsOf l s ≡ upCSsOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
  × (upCScOf l s ≡ upCScOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
  × (dnCSsOf l s ≡ dnCSsOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
  × (dnCScOf l s ≡ dnCScOf l (mkSys m′ (nA s) (nB s) (nC s) (nD s)))
break-cs-peers legBD s m′ = refl , refl , refl , refl
break-cs-peers legCD s m′ = refl , refl , refl , refl

-- … and under a medium drain
drain-cs-peers : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → (upCSsOf l s ≡ upCSsOf l (drainSucc s i d₀ id₀))
  × (upCScOf l s ≡ upCScOf l (drainSucc s i d₀ id₀))
  × (dnCSsOf l s ≡ dnCSsOf l (drainSucc s i d₀ id₀))
  × (dnCScOf l s ≡ dnCScOf l (drainSucc s i d₀ id₀))
drain-cs-peers legBD s i d₀ id₀ = refl , refl , refl , refl
drain-cs-peers legCD s i d₀ id₀ = refl , refl , refl , refl

------------------------------------------------------------------------
-- §4  *** THE HOP-PARAMETRIC ARMS. ***  ONE copy of each step class, abstracted
-- over the hop: its link, its two CS peers, its CS cell and the propositional
-- bridge from the cell accessor to the medium key.  §5 instantiates this twice.
--
-- `LiveChanCS` is hop-generic underneath (`ChanCSUp`/`ChanCSDn` are both `ChanCS`
-- instances and both `-pres` lemmas are one-liners off `chanCS-pres-eq`), so the
-- arms here call `chanCS-pres-eq`/`-eq²` directly at the parametric components and
-- each instantiation's `ChanH` is the corresponding banked `ChanCSUp`/`ChanCSDn` by
-- unfolding — nothing is transported.  What this buys, exactly as on the BF axis:
-- the api arm's twenty-one-clause label dispatch and §2b's four row-refutation
-- tables exist ONCE for the two hops instead of twice.
------------------------------------------------------------------------

module HopArmCS
  (hLink : TwoLegs → Link)
  (hSrv  : TwoLegs → SysState → SN.CSsPos)
  (hCli  : TwoLegs → SysState → SN.CScPos)
  (hCell : TwoLegs → SysState → CopyPhase)
  -- the hop's CS cell accessor IS the medium key it names, propositionally (both
  -- instances discharge this with `refl` — `cellCSUp`/`cellCSDn` are DEFINED as
  -- that phase, unlike the BF `cellUp`/`cellDn`, which need `PipeTauIo`'s bridges)
  (hCell-key : (l : TwoLegs) (s : SysState)
             → hCell l s ≡ phase (med s) (hLink l) hi N2N_ChainSync)
  where

  -- this hop's CS channel invariant: the banked `ChanCSUp`/`ChanCSDn` by unfolding
  ChanH : TwoLegs → SysState → Set
  ChanH l s = ChanCS (coarsenCSs (hSrv l s)) (hCell l s) (coarsenCSc (hCli l s))

  -- *** THE HOP IS FRAMED: *** both CS peers and the CS cell fixed.  This is the arm
  -- the `break`, the off-key drain and the nineteen non-CS api labels reduce to.
  chanCSH-frame : (l : TwoLegs) (s s′ : SysState)
                → hSrv l s ≡ hSrv l s′
                → phase (med s′) (hLink l) hi N2N_ChainSync
                  ≡ phase (med s) (hLink l) hi N2N_ChainSync
                → hCli l s ≡ hCli l s′
                → ChanH l s → ChanH l s′
  chanCSH-frame l s s′ ue ce cle iv =
    chanCS-pres-eq (cong coarsenCSs (sym ue))
      (trans (hCell-key l s′) (trans ce (sym (hCell-key l s))))
      (cong coarsenCSc (sym cle)) heFrame iv

  -- ONE medium drain preserves this hop's invariant.  The drained key is either this
  -- hop's own — and then the cell goes `draining x → empty` with both peers fixed,
  -- which is `heDrain` — or it is another key and the hop is framed.
  chanCSH-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                  (x : Payload)
                → phase (med s) i d₀ id₀ ≡ draining x
                → hSrv l s ≡ hSrv l (drainSucc s i d₀ id₀)
                → hCli l s ≡ hCli l (drainSucc s i d₀ id₀)
                → ChanH l s → ChanH l (drainSucc s i d₀ id₀)
  chanCSH-drain l s i d₀ id₀ x drainEq use uce iv
    with drain-cell-at s i d₀ id₀ (hLink l) hi N2N_ChainSync
  ... | inj₁ same = chanCSH-frame l s (drainSucc s i d₀ id₀) use same uce iv
  ... | inj₂ (refl , refl , refl , tgtEq) =
        chanCS-pres-eq² refl (trans (hCell-key l s) drainEq) refl
          (cong coarsenCSs (sym use))
          (trans (hCell-key l (drainSucc s i d₀ id₀)) tgtEq)
          (cong coarsenCSc (sym uce)) heDrain iv

  -- an api leaves the MEDIUM untouched, so this hop's cell is fixed
  api-frame : (l : TwoLegs) (s s′ : SysState)
            → med s ≡ med s′
            → hSrv l s ≡ hSrv l s′ → hCli l s ≡ hCli l s′
            → ChanH l s → ChanH l s′
  api-frame l s s′ medEq ue cle iv =
    chanCSH-frame l s s′ ue
      (cong (λ m → phase m (hLink l) hi N2N_ChainSync) (sym medEq)) cle iv

  -- ONE visible api step preserves this hop's invariant.
  --
  -- The medium is untouched, so the cell is fixed and the two peers' adjacency facts
  -- decide.  All four shapes are answered on the `apiCS` channel; on
  -- `done … N2N_ChainSync` only the SERVER has a row (a CS CLIENT has NO `done` row
  -- at all — `LiveChanCS.cliDoneRow-⊥`), so the client's row arm is REFUTED there
  -- rather than composed; every other label leaves both peers fixed by the facts'
  -- own catch-all.
  --
  -- The dispatch is on the LABEL, and it has to be: `CScApiRowP`/`CSsApiRowP` are
  -- label-directed, so at a variable label they do not reduce.
  chanCSH-api : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
                (e : Net_Api Payload X) (a : X)
              → med s ≡ med s′
              → CSsApiRowP (hLink l) hi (hSrv l s) (hSrv l s′) e a
              → CScApiRowP (hLink l) hi (hCli l s) (hCli l s′) e a
              → ChanH l s → ChanH l s′
  -- the CS api channel: four shapes
  chanCSH-api l s s′ (apiCS l₀ d₀ m) v medEq (inj₁ seq) (inj₁ ceq) iv =
    api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiCS l₀ d₀ m) v medEq (inj₂ (refl , refl , srow)) (inj₁ ceq) iv =
    chanCS-pres-eq refl
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_ChainSync) (sym medEq))
                    (sym (hCell-key l s))))
      (cong coarsenCSc (sym ceq))
      (heSrvApi (srvApiRow (hLink l) hi (coarsenCSs (hSrv l s)) m v
                  (coarsenCSs (hSrv l s′)) srow)) iv
  chanCSH-api l s s′ (apiCS l₀ d₀ m) v medEq (inj₁ seq) (inj₂ (refl , refl , crow)) iv =
    chanCS-pres-eq (cong coarsenCSs (sym seq))
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_ChainSync) (sym medEq))
                    (sym (hCell-key l s))))
      refl
      (heCliApi (cliApiRow (hLink l) hi (coarsenCSc (hCli l s)) m v
                  (coarsenCSc (hCli l s′)) crow)) iv
  chanCSH-api l s s′ (apiCS l₀ d₀ m) v medEq (inj₂ (refl , refl , srow))
              (inj₂ (refl , refl , crow)) iv =
    -- `chan-bothCsApi` is a PRESERVATION lemma and not an adjacency, so it cannot
    -- ride `chanCS-pres-eq`'s dispatch: it is applied at the SOURCE cell and the
    -- cell is then framed across the (untouched) medium, exactly as
    -- `LiveChanJoin`'s own both-api clause routes `chan-bothApi` through
    -- `LiveChanInv.chan-frame`
    chanCS-frame _ _ _ _ _ _ refl
      (trans (hCell-key l s)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_ChainSync) medEq)
                    (sym (hCell-key l s′))))
      refl
      (chan-bothCsApi (coarsenCSs (hSrv l s)) (coarsenCSs (hSrv l s′))
        (hCell l s) (coarsenCSc (hCli l s)) (coarsenCSc (hCli l s′))
        (srvApiRow (hLink l) hi (coarsenCSs (hSrv l s)) m v
          (coarsenCSs (hSrv l s′)) srow)
        (cliApiRow (hLink l) hi (coarsenCSc (hCli l s)) m v
          (coarsenCSc (hCli l s′)) crow)
        iv)
  -- the `done … N2N_ChainSync` channel: the server's `csDdone → csTerm` handshake
  chanCSH-api l s s′ (done l₀ d₀ N2N_ChainSync) v medEq (inj₁ seq) (inj₁ ceq) iv =
    api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_ChainSync) v medEq
              (inj₂ (refl , refl , srow)) (inj₁ ceq) iv =
    chanCS-pres-eq refl
      (trans (hCell-key l s′)
             (trans (cong (λ m₁ → phase m₁ (hLink l) hi N2N_ChainSync) (sym medEq))
                    (sym (hCell-key l s))))
      (cong coarsenCSc (sym ceq))
      (heSrvApi (srvDoneRow (hLink l) hi (coarsenCSs (hSrv l s)) v
                  (coarsenCSs (hSrv l s′)) srow)) iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_ChainSync) v medEq _ (inj₂ (refl , refl , crow)) iv =
    ⊥-elim (cliDoneRow-⊥ (hLink l) hi (coarsenCSc (hCli l s)) v
              (coarsenCSc (hCli l s′)) crow)
  -- every other label: a CS peer has no row at all, so both facts are fixity
  chanCSH-api l s s′ (done l₀ d₀ N2N_BlockFetch)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_KeepAlive)    v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_TxSubmission) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_LeiosNotify)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (done l₀ d₀ N2N_LeiosFetch)   v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiBF l₀ d₀ m)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiKA l₀ d₀ m)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiTS l₀ d₀ m)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiLN l₀ d₀ m)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (apiLF l₀ d₀ m)  v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (input  l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (output l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (sndmsg l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (rcvmsg l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (tx     l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (sndack l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (rcvack l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (ack    l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (store l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (env l₀ d₀ id₀) v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv
  chanCSH-api l s s′ (break  l₀)        v medEq seq ceq iv = api-frame l s s′ medEq seq ceq iv

  -- *** THE FILL ARM at this hop. ***
  --
  -- At the fired key the hop's CS cell moves, so the invariant needs a peer to have
  -- moved WITH it, and the pair (server , client) has four shapes:
  --
  --   (row , fixed) / (fixed , row) — the adjacency, one `HopEvo` arm;
  --   (row , row)     — refuted by the PAYLOAD's ROLE (`csSend-⊥`: the server's five
  --                     wire-send rows are `≟`-gated on RESPONDER tuples and the
  --                     client's three on INITIATOR ones);
  --   (fixed , fixed) — the cell filled with NEITHER CS peer moving.  On the BF axis
  --                     this is refuted by grant #7's two ownership certificates, and
  --                     since grant #12 the CS axis HAS them: the ownership layer is
  --                     `IDs`-parametric, so `NoSrvIoAt`/`NoCliIoAt` at
  --                     `N2N_ChainSync` ride grant #7's own eight per-node witnesses
  --                     (the eight CS slots sit at the same four `(link , hi)` keys,
  --                     with the same roles), and the cone's fixity arms CARRY them.
  --                     So the case is DISCHARGED here — `csFill-noPeer-⊥` off
  --                     `role-in` — and the arm takes NO premise.  It was stated with
  --                     a `csNoBoth` premise while the io half was blocked; that
  --                     premise is gone.
  --
  -- Away from the fired key the hop is framed and a row is impossible (§2b).  THE
  -- KEY COMPARISON IS THE ARM'S OWN `with`, so the medium's `phase-upd`/`setCell`
  -- term and the rows' key equations reduce against the SAME scrutinees.
  chanCSH-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
    → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                        (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                     (broken (med s))
    → phase (med s) l₀ d₀ id₀ ≡ empty
    → CssIoRowP (hLink l) hi (hSrv l s) (hSrv l s′) (input l₀ d₀ id₀) x
    → CscIoRowP (hLink l) hi (hCli l s) (hCli l s′) (input l₀ d₀ id₀) x
    → ChanH l s → ChanH l s′
  chanCSH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty srow crow iv
    with setRead⁺ (phase (med s)) l₀ d₀ id₀ (full x) (hLink l) hi N2N_ChainSync
  -- AWAY from the hop's key: the hop is framed and neither row can be inhabited
  ... | inj₁ (miss , same) =
        chanCSH-frame l s s′
          (cssRow-off (hLink l) hi (hSrv l s) (hSrv l s′) l₀ d₀ id₀ x miss srow)
          (trans (cong (λ m → phase m (hLink l) hi N2N_ChainSync) sEq) (sym same))
          (cscRow-off (hLink l) hi (hCli l s) (hCli l s′) l₀ d₀ id₀ x miss crow) iv
  -- AT the hop's key: the cell filled, so exactly one of its peers moved
  ... | inj₂ (refl , refl , refl , tgt) = hit srow crow
    where
    cellSrc : hCell l s ≡ empty
    cellSrc = trans (hCell-key l s) srcEmpty
    cellTgt : hCell l s′ ≡ full x
    cellTgt = trans (hCell-key l s′)
                    (trans (cong (λ m → phase m (hLink l) hi N2N_ChainSync) sEq) tgt)
    hit : CssIoRowP (hLink l) hi (hSrv l s) (hSrv l s′)
            (input (hLink l) hi N2N_ChainSync) x
        → CscIoRowP (hLink l) hi (hCli l s) (hCli l s′)
            (input (hLink l) hi N2N_ChainSync) x
        → ChanH l s′
    -- the SERVER wrote: its row is the adjacency, the client is fixed
    hit (inj₂ srowEq) (inj₁ (ceq , _)) =
      chanCS-pres-eq² refl cellSrc refl refl cellTgt (cong coarsenCSc (sym ceq))
        (heSrvSend (srvSendRow (hLink l) hi (coarsenCSs (hSrv l s)) x
                     (coarsenCSs (hSrv l s′)) srowEq)) iv
    -- … or the CLIENT did (its request, its find-intersect, or its done)
    hit (inj₁ (seq , _)) (inj₂ crowEq) =
      chanCS-pres-eq² refl cellSrc refl (cong coarsenCSs (sym seq)) cellTgt refl
        (heCliSend (cliSendRow (hLink l) hi (coarsenCSc (hCli l s)) x
                     (coarsenCSc (hCli l s′)) crowEq)) iv
    -- BOTH would have written the SAME payload: impossible by its role
    hit (inj₂ srowEq) (inj₂ crowEq) =
      ⊥-elim (csSend-⊥
                (srvSendRow (hLink l) hi (coarsenCSs (hSrv l s)) x
                  (coarsenCSs (hSrv l s′)) srowEq)
                (cliSendRow (hLink l) hi (coarsenCSc (hCli l s)) x
                  (coarsenCSc (hCli l s′)) crowEq))
    -- NEITHER moved while the cell filled: (T6c, grant #12) DISCHARGED here, from
    -- the two certificates the granted cone's fixity arms carry
    hit (inj₁ (_ , nsrv)) (inj₁ (_ , ncli)) =
      ⊥-elim (csFill-noPeer-⊥ (hLink l) hi x
                (role-in (hLink l) hi N2N_ChainSync x) nsrv ncli)

  -- *** THE READ ARM at this hop *** — the fill's mirror: the cell goes
  -- `full x → draining x`, the reader is the peer whose ROLE the payload is not, and
  -- the same four shapes are answered the same four ways.
  chanCSH-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
    → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                        (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                     (broken (med s))
    → phase (med s) l₀ d₀ id₀ ≡ full x
    → CssIoRowP (hLink l) hi (hSrv l s) (hSrv l s′) (output l₀ d₀ id₀) x
    → CscIoRowP (hLink l) hi (hCli l s) (hCli l s′) (output l₀ d₀ id₀) x
    → ChanH l s → ChanH l s′
  chanCSH-read l s s′ l₀ d₀ id₀ x sEq srcFull srow crow iv
    with setRead⁺ (phase (med s)) l₀ d₀ id₀ (draining x) (hLink l) hi N2N_ChainSync
  ... | inj₁ (miss , same) =
        chanCSH-frame l s s′
          (cssRowR-off (hLink l) hi (hSrv l s) (hSrv l s′) l₀ d₀ id₀ x miss srow)
          (trans (cong (λ m → phase m (hLink l) hi N2N_ChainSync) sEq) (sym same))
          (cscRowR-off (hLink l) hi (hCli l s) (hCli l s′) l₀ d₀ id₀ x miss crow) iv
  ... | inj₂ (refl , refl , refl , tgt) = hit srow crow
    where
    cellSrc : hCell l s ≡ full x
    cellSrc = trans (hCell-key l s) srcFull
    cellTgt : hCell l s′ ≡ draining x
    cellTgt = trans (hCell-key l s′)
                    (trans (cong (λ m → phase m (hLink l) hi N2N_ChainSync) sEq) tgt)
    hit : CssIoRowP (hLink l) hi (hSrv l s) (hSrv l s′)
            (output (hLink l) hi N2N_ChainSync) x
        → CscIoRowP (hLink l) hi (hCli l s) (hCli l s′)
            (output (hLink l) hi N2N_ChainSync) x
        → ChanH l s′
    -- the SERVER read — the step that ENTERS the pre region
    hit (inj₂ srowEq) (inj₁ (ceq , _)) =
      chanCS-pres-eq² refl cellSrc refl refl cellTgt (cong coarsenCSc (sym ceq))
        (heSrvRead (srvReadRow (hLink l) hi (coarsenCSs (hSrv l s)) x
                     (coarsenCSs (hSrv l s′)) srowEq)) iv
    -- … or the CLIENT did — the DELIVERY
    hit (inj₁ (seq , _)) (inj₂ crowEq) =
      chanCS-pres-eq² refl cellSrc refl (cong coarsenCSs (sym seq)) cellTgt refl
        (heCliRead (cliReadRow (hLink l) hi (coarsenCSc (hCli l s)) x
                     (coarsenCSc (hCli l s′)) crowEq)) iv
    -- BOTH would have read the same payload: impossible by its message class
    hit (inj₂ srowEq) (inj₂ crowEq) =
      ⊥-elim (csRead-⊥
                (srvReadRow (hLink l) hi (coarsenCSs (hSrv l s)) x
                  (coarsenCSs (hSrv l s′)) srowEq)
                (cliReadRow (hLink l) hi (coarsenCSc (hCli l s)) x
                  (coarsenCSc (hCli l s′)) crowEq))
    -- NEITHER moved while the cell drained into a reader: DISCHARGED, the mirror
    hit (inj₁ (_ , nsrv)) (inj₁ (_ , ncli)) =
      ⊥-elim (csRead-noPeer-⊥ (hLink l) hi x
                (role-out (hLink l) hi N2N_ChainSync x) nsrv ncli)

------------------------------------------------------------------------
-- §5  THE TWO INSTANCES, AND THE LEG'S TWO HOPS PER STEP CLASS.
--
-- All five classes are stated at their per-hop premises; since grant #12 every one of
-- those premises IS a slot of `LiveLegIoCone`'s cone or of `LiveLegApiExpose`'s api
-- record, so `LiveChanJoin`'s arms supply them by SELECTION and nothing else.  The
-- two node-preserving classes (`break`, medium drain) need no cone at all.
------------------------------------------------------------------------

-- the leg's UP CS hop: node A's CS server, the up CS cell, the relay's CS client
module HUpCS = HopArmCS upLink upCSsOf upCScOf cellCSUp (λ l s → refl)

-- … and its DOWN CS hop: the relay's CS server, the down CS cell, node D's CS client
module HDnCS = HopArmCS dnLink dnCSsOf dnCScOf cellCSDn (λ l s → refl)

-- ONE `break` preserves BOTH CS hops: a break moves the medium's BROKEN bits only,
-- so the phase function is preserved and all four node records are LITERAL
chanCSLeg-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
                → phase m′ ≡ phase (med s)
                → ChanCSLeg l s
                → ChanCSLeg l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
chanCSLeg-break l s m′ pheq (ivU , ivD) =
  let (useU , uceU , useD , uceD) = break-cs-peers l s m′
  in  HUpCS.chanCSH-frame l s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) useU
        (cong (λ g → g (upLink l) hi N2N_ChainSync) pheq) uceU ivU
    , HDnCS.chanCSH-frame l s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) useD
        (cong (λ g → g (dnLink l) hi N2N_ChainSync) pheq) uceD ivD

-- ONE medium drain preserves BOTH CS hops (the drained key hits at most one of the
-- two CS cells, and all four CS peers are fixed by §3)
chanCSLeg-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                  (x : Payload)
                → phase (med s) i d₀ id₀ ≡ draining x
                → ChanCSLeg l s → ChanCSLeg l (drainSucc s i d₀ id₀)
chanCSLeg-drain l s i d₀ id₀ x drainEq (ivU , ivD) =
  let (use , uce , dse , dce) = drain-cs-peers l s i d₀ id₀
  in  HUpCS.chanCSH-drain l s i d₀ id₀ x drainEq use uce ivU
    , HDnCS.chanCSH-drain l s i d₀ id₀ x drainEq dse dce ivD

-- ONE visible api step preserves BOTH CS hops, off the four per-hop api rows.  TWO
-- of the four exist in `LiveLegApiExpose.DriverExposed⁺` already
-- (`deCSRowsBD`/`deCSRowsCD` — the relay's up-hop CS CLIENT and its down-hop CS
-- SERVER); the other two (node A's up-hop CS SERVER, node D's down-hop CS CLIENT)
-- exist at the BUNDLE layer (`LiveLegApiCone.BundleApiEvo:1275-1276`) and need two
-- record slots and their six arm bindings — NO grant, NO base edit.
chanCSLeg-api : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
                (e : Net_Api Payload X) (a : X)
              → med s ≡ med s′
              → CSsApiRowP (upLink l) hi (upCSsOf l s) (upCSsOf l s′) e a
                × CScApiRowP (upLink l) hi (upCScOf l s) (upCScOf l s′) e a
              → CSsApiRowP (dnLink l) hi (dnCSsOf l s) (dnCSsOf l s′) e a
                × CScApiRowP (dnLink l) hi (dnCScOf l s) (dnCScOf l s′) e a
              → ChanCSLeg l s → ChanCSLeg l s′
chanCSLeg-api l s s′ e a medEq (srowU , crowU) (srowD , crowD) (ivU , ivD) =
    HUpCS.chanCSH-api l s s′ e a medEq srowU crowU ivU
  , HDnCS.chanCSH-api l s s′ e a medEq srowD crowD ivD

-- ONE io FILL preserves BOTH CS hops, off the four per-hop io rows and nothing else.
-- All four ARE cone slots since grant #12 — node A's two up-hop servers
-- (`AllCssUpP`), the four clients (`AllCscP`) and grant #11's two down-hop servers
-- (`AllCssP`) — and the ownership premises the blocked-era signature carried are
-- gone: §4 discharges the *(neither peer moved)* case from the certificates the
-- fixity arms carry.  This arm is the one the T6c blocker WAS about; it is closed.
chanCSLeg-fill : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (full x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ empty
  → CssIoRowP (upLink l) hi (upCSsOf l s) (upCSsOf l s′) (input l₀ d₀ id₀) x
    × CscIoRowP (upLink l) hi (upCScOf l s) (upCScOf l s′) (input l₀ d₀ id₀) x
  → CssIoRowP (dnLink l) hi (dnCSsOf l s) (dnCSsOf l s′) (input l₀ d₀ id₀) x
    × CscIoRowP (dnLink l) hi (dnCScOf l s) (dnCScOf l s′) (input l₀ d₀ id₀) x
  → ChanCSLeg l s → ChanCSLeg l s′
chanCSLeg-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty (srowU , crowU) (srowD , crowD)
               (ivU , ivD) =
    HUpCS.chanCSH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty srowU crowU ivU
  , HDnCS.chanCSH-fill l s s′ l₀ d₀ id₀ x sEq srcEmpty srowD crowD ivD

-- … and ONE io READ
chanCSLeg-read : (l : TwoLegs) (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs)
                 (x : Payload)
  → med s′ ≡ mkMed (phase-upd (phase (med s)) l₀
                      (setCell (phase (med s) l₀) d₀ id₀ (draining x)))
                   (broken (med s))
  → phase (med s) l₀ d₀ id₀ ≡ full x
  → CssIoRowP (upLink l) hi (upCSsOf l s) (upCSsOf l s′) (output l₀ d₀ id₀) x
    × CscIoRowP (upLink l) hi (upCScOf l s) (upCScOf l s′) (output l₀ d₀ id₀) x
  → CssIoRowP (dnLink l) hi (dnCSsOf l s) (dnCSsOf l s′) (output l₀ d₀ id₀) x
    × CscIoRowP (dnLink l) hi (dnCScOf l s) (dnCScOf l s′) (output l₀ d₀ id₀) x
  → ChanCSLeg l s → ChanCSLeg l s′
chanCSLeg-read l s s′ l₀ d₀ id₀ x sEq srcFull (srowU , crowU) (srowD , crowD)
               (ivU , ivD) =
    HUpCS.chanCSH-read l s s′ l₀ d₀ id₀ x sEq srcFull srowU crowU ivU
  , HDnCS.chanCSH-read l s s′ l₀ d₀ id₀ x sEq srcFull srowD crowD ivD
