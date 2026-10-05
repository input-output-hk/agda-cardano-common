{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cross-node api campaign, Task 6b — *** THE PER-HOP ChainSync CHANNEL
-- INVARIANT ***, payload-generic, with its preservation calculus.
--
-- WHY THIS MODULE EXISTS.  T6's framing gate ruled that `pp2` (and `cp6`/`pp0`)
-- split into a TABLE half and a CHANNEL half: the region shape of `pp2` is a fact
-- about `NodeSpecs.csSnxt` (machine-checked at `LiveCSRow` §4c), while the
-- SHARPENING of that region — refuting the stability of `csWar` — needs the PHASE
-- OF A CHAINSYNC MEDIUM CELL, a fact the development did not possess anywhere
-- (`LiveChanInv` has zero ChainSync content; `PipeInv.cellUp`/`cellDn` and
-- `PipeValInv.PipeVal`'s two cell components are all keyed at `N2N_BlockFetch`;
-- `LiveChanJoin.LegJointU` names no CS cell; a tree-wide `phase … N2N_ChainSync`
-- found no site).  This module is that object, at the shape `LiveRelayCS` §6(iii)
-- names: a two-sided invariant relating one hop's
--
--     (CS server position , cell phase , CS client position)
--
-- and NOTHING else — no `blkA`, no leg, no link, no driver in the statement.
--
-- *** THE STRUCTURE IS THREE CLAUSES, NOT FIVE — AND THE REASON IS THE CONSUMER,
-- NOT THE PROTOCOL SHAPE. ***  `LiveChanInv`'s five clauses are `cvStr`/`cvBlk`
-- (the STREAMING region: an unread block's reader is aligned) plus
-- `cvPre`/`cvQui`/`cvReq` (the PRE region: the cell holds nothing unread and the
-- client is awaiting).  Only the second triple transposes, and here is the honest
-- argument for why — *** CORRECTED at the T6b review (its finding I-1); the first
-- version of this block claimed ChainSync's peers "alternate strictly, so no state
-- in which one peer writes twice exists", and THAT IS FALSE: ***
-- `csCanAwait --sendCSAwaitReply--> csWar --wire-send--> csMust
--  --sendCSRollForward--> csWrf ht --wire-send--> csIdle` is a two-message SERVER
-- BURST with no intervening client message and no requirement that the client has
-- read, which is exactly why §2's `SrvPre` has to exclude `csMust` and the five
-- `csW*` (see that header, and F31).  ChainSync DOES have a write-burst region; it
-- is simply out of this invariant's SCOPE.
--
-- The real argument is about what the missing clauses FEED.  `cvStr`/`cvBlk` exist
-- only to prove `LiveChanInv.H19`, `chanInv⇒h19` is GATED on `SrvStr`, and its only
-- consumers are `LiveSrvOpen.srvOpen-up`/`srvOpen-dn` (`:214-297`) — the
-- TOKEN-HOLDING BF server arms (`SrvHas⁺ blkA`, whose fourth escape arm
-- `NoTwoTokens` cuts).  The CS axis has no such arm family at all: its four
-- residual clauses (`LiveRelayCS:192-198`) are bare position equations
-- (`cp5 ≡ ccIdle`, `cp6`/`pp0 ≡ csAreq`, `pp2 ≡ csMust`) with no token and no
-- `NoTwoTokens`.  And the BF arm this module's consumer is modelled on — the
-- WIRE-SEND position `bsWsb` — does not use `H19` either: `LiveSrvOpen:312-320`
-- says so outright ("`H19` is gated on `SrvStr`, and `SrvStr bsWsb = ⊥` … T2
-- strengthened `cvQui` to the POSITIVE `CellPreQ` … no third arm exists, because a
-- `full` cell is what `CellPreQ` excludes").  So the `csWar-⊥` obligation rides
-- **exactly the `cvQui` analogue and nothing else**, and `ccQui`+`ccPre`+`ccReq` is
-- the complete transposition of the clauses that obligation consumes: no content is
-- silently lost.  The item was priced "scoped to the pre-region" and that scope is
-- what is built; §6's closing note records what a CS `H19` would additionally need.
--
-- *** THE T4 DISCOUNT IS REAL AND IS TAKEN. ***  §4b's seven row producers are the
-- only bulk in the module, and §4c does NOT re-derive the peer-step inversion:
-- `LiveCSRow.cssRow-of`/`cscRow-of` already turn a real abstract CS peer step into
-- its FIRED COARSE ROW (through `tableSpec-ev-inv` and the 313-pair coarse
-- injectivity `tssInj`/`tscInj`), so each of §4c's seven bridges is a two-line
-- composition instead of a `rowAdj`-shaped re-derivation.
--
-- CONTENTS
--   §1  the eight wire payloads (five responder, three initiator) and the
--       message-class reader on a cell phase
--   §2  the two position REGIONS, as total dispatches on the ABSTRACT position
--       types (`NodeSpecs.CSsPos`/`CScPos` — thirteen and twelve constructors, no
--       catch-all), and the cell-phase predicates
--   §3  *** THE INVARIANT ***: three clauses, what each is for, base and frame
--   §4  the six step ADJACENCIES — transcriptions of `csSnxt`'s eighteen rows and
--       `csCnxt`'s seventeen (see the KEEP-IN-SYNC block)
--   §4b *** THE ADJACENCY PRODUCERS ***: every fired table row yields its §4
--       constructor, by a dispatch TOTAL on the position/tag/message datatypes —
--       which closes the vacuity hole an omitted row would leave
--   §4c the same at the STEP level, riding `LiveCSRow`'s row wrappers: a real
--       visible step of a real abstract CS peer produces its adjacency
--   §5  *** THE PRESERVATION CALCULUS ***: one lemma per step class (seven)
--   §6  the consumers: the pre-region cell fact, at `csWar` and at an equation
--   §7  the two hop instances (up and down, both legs), base, frame, the per-hop
--       EVOLUTION datatype and the ONE preservation theorem over its eight arms
--
-- WHAT IS NOT HERE, AND WHY (honest scope).  The JOIN — carrying `ChanCSLeg` as a
-- trailing factor of `LiveChanJoin.LegJointU` so the FSim's `Rel` holds it at
-- every reachable config — is NOT in this module, exactly as `ChanUp`/`ChanDn`
-- were not in `LiveChanInv` when it landed (the join arrived a task later, in
-- `LiveChanJoin`).  §7 gives the object a base case, a frame and a complete
-- per-step preservation calculus; that is the same status `LiveLegStep.NoTwoTokens`
-- had after `LiveTokenExcl` (`LiveTokenExcl.agda:1100-1113`).  Also NOT here: the
-- `csWar-⊥` stability refutation itself (it needs §6's fact PLUS the CS io ladder
-- and the CS medium kits, which are `LiveIoIntroCS`'s, and the reachability
-- threading, which is the join's).
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.List using ( List )
open import Data.Maybe using ( just )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- the NON-polymorphic `⊤`, qualified: it is the carrier of the `done` event and
-- of the payload-free api tags, and must not shadow the polymorphic one above
import Data.Unit as U0
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; subst; cong )

-- the `_≟_` the two decode tables gate their key and payload comparisons on: the
-- SAME instances must be in scope here, or §4b's `with`-abstractions cannot see
-- the tables' own comparisons (`DecEq-Fin` for `Link = Fin numLinks`, `DecEq-Dir`
-- for `Dir`, `DecEq-Payload` for the wire tuples, and the four api-value ones —
-- `List Point` spelled explicitly, as `LiveCSRow.csAfi-nq` spells it)
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link; input; output; done; apiCS; ApiCSTag; ApiCSCar
        ; sendCSRequestNext; sendCSFindIntersect; sendCSDone; sendCSAwaitReply
        ; sendCSRollForward; sendCSRollBackward; sendCSIntersectFound
        ; sendCSIntersectNotFound; recvCSRollforward; recvCSRollback
        ; recvCSIntersectFound; recvCSIntersectNotFound
        ; reqCSRequestNext; reqCSFindIntersect )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Messages; blockFetch; keepAlive; chainSync; txSubmission
        ; leiosNotify; leiosFetch; MessageChainSync; Point; Header; Tip
        ; MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward; MsgCSRollBackward
        ; MsgCSFindIntersect; MsgCSIntersectFound; MsgCSIntersectNotFound
        ; MsgCSDone; DecEq-Point; DecEq-Tip; DecEq-Payload )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; N2N_ChainSync; Mode; FromInitiator; FromResponder; DecEq-Dir )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length; time₀; length₀ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( phase; CopyPhase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open NS using ( DecEq-H×T; DecEq-P×T )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absCSc; absCSs; coarsenCSs; coarsenCSc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
-- (the T4 row layer: the coarse ROW of a real abstract CS peer step, off
-- `tableSpec-ev-inv` + the 313-pair coarse injectivity — §4c rides these two and
-- re-derives nothing)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow blkA
  using ( CSsRow; CScRow; cssRow-of; cscRow-of )

------------------------------------------------------------------------
-- §1  THE WIRE PAYLOADS, AND THE MESSAGE CLASS OF AN UNREAD CELL.
--
-- The five RESPONDER-side payloads and the three INITIATOR-side ones are exactly
-- the tuples `csSnxt`/`csCnxt`'s wire-SEND rows are `≟`-gated on
-- (`NodeSpecs.agda:460-489`, `:315-332`), so a cell filled by either peer holds
-- one of these eight terms verbatim.  The wire-READ rows, by contrast, are LENIENT
-- in `(time , mode , length)` (they pattern-match the message only), so every
-- predicate below reads the cell through `FullMsg`, which is lenient too — that is
-- what makes the read classes of §4 faithful rather than convenient.
------------------------------------------------------------------------

-- the `MsgCSRollForward h tp` wire payload of a responder-side CS sender
rfPayload : Header → Tip → Payload
rfPayload h tp = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp)

-- … the `MsgCSRollBackward pt tp` one
rbPayload : Point → Tip → Payload
rbPayload pt tp = time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)

-- … the `MsgCSAwaitReply` one (the payload the `pp2` region's wire-send carries)
arPayload : Payload
arPayload = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply

-- … the `MsgCSIntersectFound pt tp` one
ifPayload : Point → Tip → Payload
ifPayload pt tp = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)

-- … and the `MsgCSIntersectNotFound tp` one
inPayload : Tip → Payload
inPayload tp = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)

-- the initiator-side `MsgCSRequestNext`
rnPayload : Payload
rnPayload = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext

-- … the initiator-side `MsgCSFindIntersect ps`
fiPayload : List Point → Payload
fiPayload ps = time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)

-- … and the initiator-side `MsgCSDone`
cdPayload : Payload
cdPayload = time₀ , FromInitiator , length₀ , chainSync MsgCSDone

-- the cell holds an UNREAD payload carrying the ChainSync message `mc` (lenient in
-- the tuple's other three components, exactly as the readers' table rows are)
FullMsg : CopyPhase → MessageChainSync → Set
FullMsg ph mc = Σ[ t ∈ Time ] Σ[ md ∈ Mode ] Σ[ ln ∈ Length ]
                  (ph ≡ full (t , md , ln , chainSync mc))

------------------------------------------------------------------------
-- §2  THE TWO REGIONS, and the cell-phase predicates.
--
-- Each region is a total dispatch on the ABSTRACT position datatype, so it is
-- exhaustive with no catch-all and every membership question reduces to `⊤`/`⊥`.
------------------------------------------------------------------------

-- *** THE SERVER'S PRE REGION. ***  The server has taken the client's request off
-- the wire and its own reply has not reached the wire yet.  Read off `csSnxt`:
-- the region is ENTERED only by the server's wire-READ at `csIdle`
-- (`:416-427` — which leaves the cell `draining`, so the cell fact is
-- ESTABLISHED there and nowhere else) and LEFT only by the server's own five
-- wire-SENDS (`:460-489`).
--
-- *** WHY `csMust` AND THE FIVE `csW*` POSITIONS ARE OUT, and it is not an
-- omission. ***  `csMust` is reached BY a wire-send (of `MsgCSAwaitReply`), so at
-- `csMust` the cell may hold that very payload unread; and from `csMust` the
-- server may emit its api reply immediately, so at `csWrf`/`csWrb` the cell may
-- STILL hold it.  The state `(csWrf ht , full arPayload , ccAwait)` is genuinely
-- reachable — putting those positions in the region would make the invariant
-- FALSE, not merely expensive.  (Falsification F31 is exactly that: `csMust` added
-- to `SrvPre` goes red at `chan-srvSend`'s `ssAR` arm.)
SrvPre : NS.CSsPos → Set
SrvPre NS.csIdle       = ⊥
SrvPre NS.csAreq       = ⊤
SrvPre NS.csCanAwait   = ⊤
SrvPre (NS.csAfi ps)   = ⊤
SrvPre NS.csInt        = ⊤
SrvPre NS.csDdone      = ⊥
SrvPre NS.csMust       = ⊥
SrvPre (NS.csWrf ht)   = ⊥
SrvPre (NS.csWrb pt)   = ⊥
SrvPre NS.csWar        = ⊤
SrvPre (NS.csWif pt)   = ⊥
SrvPre (NS.csWin tp)   = ⊥
SrvPre NS.csTerm       = ⊥

-- *** THE CLIENT'S AWAITING REGION. ***  The client has a request outstanding and
-- CANNOT write the cell: its only rows at these two positions are `output` READS
-- (`:333-360`).  Every other client position either writes (`ccWreq`/`ccWfi`/
-- `ccWdone`), or is one api step away from a position that writes (`ccIdle`, and
-- the four `cc[ARF|ARB|AIF|AIN]` emits that return to `ccIdle`), or is terminal.
-- `ccMust` is OUT for the same reason `csMust` is: it is reached by the client's
-- READ of `MsgCSAwaitReply`, at which point the server has already left the
-- region.
CliAwt : NS.CScPos → Set
CliAwt NS.ccIdle       = ⊥
CliAwt NS.ccWreq       = ⊥
CliAwt NS.ccAwait      = ⊤
CliAwt (NS.ccWfi ps)   = ⊥
CliAwt NS.ccInt        = ⊤
CliAwt NS.ccWdone      = ⊥
CliAwt NS.ccMust       = ⊥
CliAwt (NS.ccArf ht)   = ⊥
CliAwt (NS.ccArb pt)   = ⊥
CliAwt (NS.ccAif pt)   = ⊥
CliAwt (NS.ccAin tp)   = ⊥
CliAwt NS.ccTerm       = ⊥

-- the cell holds an unread client REQUEST — either of the two the client sends
-- (`MsgCSDone` is deliberately NOT here: it moves the server to `csDdone`, which
-- is outside the pre region, so no clause needs it)
ReqFull : CopyPhase → Set
ReqFull ph = FullMsg ph MsgCSRequestNext
           ⊎ (Σ[ ps ∈ List Point ] FullMsg ph (MsgCSFindIntersect ps))

-- *** THE PRE-REGION CELL PREDICATE. ***  the cell of a channel whose server is in
-- its pre region holds nothing UNREAD: it is empty, or already DRAINING what was
-- read out of it.  The POSITIVE polarity is the point (T2's lesson on the BF
-- axis): a stability ladder needs the positive phase to fire the server's own
-- wire-send (`medOfferInCS` wants `phase … ≡ empty`) or the medium's drain τ
-- (`medDrainτCS` wants `draining`), and a negative "no responder payload is in
-- flight" admits `full` and pins nothing.
CellPreQ : CopyPhase → Set
CellPreQ ph = (ph ≡ empty) ⊎ (Σ[ x ∈ Payload ] (ph ≡ draining x))

-- a `full` cell is NOT a pre-region cell (the refutation §5's client-read arms
-- consume: a read needs the cell `full`, and the pre region forbids it)
preQ-full-⊥ : (x : Payload) → CellPreQ (full x) → ⊥
preQ-full-⊥ x (inj₁ ())
preQ-full-⊥ x (inj₂ (_ , ()))

------------------------------------------------------------------------
-- §3  *** THE INVARIANT. ***  Three clauses on one hop's three components.
--
-- WHAT EACH CLAUSE IS FOR, and why none can be dropped:
--
--   `ccQui` — THE PAYLOAD.  In the server's pre region the cell holds nothing
--             unread.  This is the clause the `pp2` stability ladder fires from —
--             `csWar ∈ SrvPre`, so `ccQui` hands `csWar-⊥` the two-armed
--             `empty ⊎ draining` it needs — and it is what §6 delivers.
--   `ccPre` — in the server's pre region the client is awaiting.  Without it
--             `ccQui` is NOT preserved: the client's own three wire-sends would
--             fill the cell under the server's pre region, and the only thing that
--             refutes them is that their SOURCE positions are outside `CliAwt`.
--   `ccReq` — an unread REQUEST in the cell has its client awaiting.  This is what
--             carries `ccPre` across the server's wire-READ of the request — the
--             step that ENTERS the pre region, at which the successor's `ccPre`
--             must be established from the SOURCE state and nothing else can do it.
--
-- The three are mutually load-bearing and the cycle is not circular: `ccQui`
-- refutes the client's READS (which would leave `CliAwt`), `ccPre` refutes the
-- client's WRITES (which would break `ccQui`), and `ccReq` is what the one
-- region-entering step establishes `ccPre` from.  Every arm of §5 is one of those
-- three moves.
--
-- NOTE WHAT IS ABSENT: no `blkA`, no leg, no link, no driver.  The invariant is a
-- statement about ONE ChainSync channel and nothing else.
------------------------------------------------------------------------

-- *** THE PER-HOP CHAINSYNC CHANNEL INVARIANT. ***
record ChanCS (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos) : Set where
  constructor mkChanCS
  field
    ccQui : SrvPre sa → CellPreQ ph
    ccPre : SrvPre sa → CliAwt ca
    ccReq : ReqFull ph → CliAwt ca
open ChanCS public

-- BASE — an idle server, an empty cell and an idle client: every antecedent is
-- uninhabited (this is the channel's state at `SysDecode.initial`)
chanCS-init : ChanCS NS.csIdle empty NS.ccIdle
chanCS-init =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

-- FRAME — the invariant reads exactly three components, so a step fixing all
-- three carries it
chanCS-frame : (sa sa′ : NS.CSsPos) (ph ph′ : CopyPhase) (ca ca′ : NS.CScPos)
             → sa ≡ sa′ → ph ≡ ph′ → ca ≡ ca′
             → ChanCS sa ph ca → ChanCS sa′ ph′ ca′
chanCS-frame sa .sa ph .ph ca .ca refl refl refl iv = iv

------------------------------------------------------------------------
-- §4  THE SIX STEP ADJACENCIES — FAITHFUL transcriptions of the two tables.
--
-- *** KEEP IN SYNC — `NodeSpecs.csSnxt` (`:414-490`) and `csCnxt` (`:304-381`).
-- An OMITTED row here makes §5's preservation VACUOUSLY true for a step that
-- really exists, so the two lists below are exhaustive by construction and each
-- row is annotated with its source line.  If either table gains a row, the
-- matching adjacency MUST gain a constructor. ***
--
--   `csSnxt`, eighteen rows:
--     csIdle      + output + MsgCSRequestNext          → csAreq      :416-419  srReq
--     csIdle      + output + MsgCSFindIntersect ps     → csAfi ps    :420-423  srFI
--     csIdle      + output + MsgCSDone                 → csDdone     :424-427  srDone
--     csAreq      + apiCS reqCSRequestNext             → csCanAwait  :428-430  saReq
--     csAfi ps    + apiCS reqCSFindIntersect           → csInt       :431-435  saFI
--     csDdone     + done                               → csTerm      :436-438  saDone
--     csCanAwait  + apiCS sendCSRollForward ht         → csWrf ht    :439-441  saRF
--     csCanAwait  + apiCS sendCSRollBackward pt        → csWrb pt    :442-444  saRB
--     csCanAwait  + apiCS sendCSAwaitReply             → csWar       :445-447  saAR
--     csMust      + apiCS sendCSRollForward ht         → csWrf ht    :448-450  saMRF
--     csMust      + apiCS sendCSRollBackward pt        → csWrb pt    :451-453  saMRB
--     csInt       + apiCS sendCSIntersectFound pt      → csWif pt    :454-456  saIF
--     csInt       + apiCS sendCSIntersectNotFound tp   → csWin tp    :457-459  saINF
--     csWrf(h,tp) + input  + MsgCSRollForward h tp     → csIdle      :460-465  ssRF
--     csWrb(p,tp) + input  + MsgCSRollBackward p tp    → csIdle      :466-471  ssRB
--     csWar       + input  + MsgCSAwaitReply           → csMust      :472-477  ssAR
--     csWif(p,tp) + input  + MsgCSIntersectFound p tp  → csIdle      :478-483  ssIF
--     csWin tp    + input  + MsgCSIntersectNotFound tp → csIdle      :484-489  ssINF
--
--   `csCnxt`, seventeen rows:
--     ccIdle      + apiCS sendCSRequestNext            → ccWreq      :306-308  caReq
--     ccIdle      + apiCS sendCSFindIntersect ps       → ccWfi ps    :309-311  caFI
--     ccIdle      + apiCS sendCSDone                   → ccWdone     :312-314  caDone
--     ccWreq      + input  + MsgCSRequestNext          → ccAwait     :315-320  csReq
--     ccWfi ps    + input  + MsgCSFindIntersect ps     → ccInt       :321-326  csFI
--     ccWdone     + input  + MsgCSDone                 → ccTerm      :327-332  csDone
--     ccAwait     + output + MsgCSRollForward h tp     → ccArf(h,tp) :333-336  crRF
--     ccAwait     + output + MsgCSRollBackward p tp    → ccArb(p,tp) :337-340  crRB
--     ccAwait     + output + MsgCSAwaitReply           → ccMust      :341-344  crAR
--     ccMust      + output + MsgCSRollForward h tp     → ccArf(h,tp) :345-348  crMRF
--     ccMust      + output + MsgCSRollBackward p tp    → ccArb(p,tp) :349-352  crMRB
--     ccInt       + output + MsgCSIntersectFound p tp  → ccAif(p,tp) :353-356  crIF
--     ccInt       + output + MsgCSIntersectNotFound tp → ccAin tp    :357-360  crINF
--     ccArf ht    + apiCS recvCSRollforward            → ccIdle      :361-365  caRecvF
--     ccArb pt    + apiCS recvCSRollback               → ccIdle      :366-370  caRecvB
--     ccAif pt    + apiCS recvCSIntersectFound         → ccIdle      :371-375  caRecvIF
--     ccAin tp    + apiCS recvCSIntersectNotFound      → ccIdle      :376-380  caRecvIN
--
-- The wire-SEND rows are `≟`-gated on an exact payload tuple, so the `ss*`/`cs*`
-- constructors carry the exact payload; the wire-READ rows match the message only,
-- so the `sr*`/`cr*` constructors are lenient in `(time , mode , length)`.
--
-- *** AND THE SAME DEVIATION `LiveChanInv` §4 preserves. ***  Five of the api rows
-- are `≟`-gated on the SOURCE's own value in the table — `csSnxt` row 5 gates
-- `reqCSFindIntersect` against the `csAfi ps` list, and `csCnxt` rows 14-17 gate
-- each `recvCS*` against the value the source position holds — and the
-- adjacencies below DROP that pin: `saFI ps` / `caRecvF ht` / … bind the SOURCE's
-- value (so the source position is pinned) but say nothing about the api event's
-- own argument.  The direction is safe, being a HYPOTHESIS-position weakening: the
-- adjacency holds of MORE steps, so §5 proves more, and §4b's total producers still
-- catch any OMITTED row.  A re-sync must preserve the omission, not "restore" the
-- pins — restoring them would break every producer.
------------------------------------------------------------------------

-- the server's non-io adjacencies (its nine api rows and its `done` row): the
-- steps at which the server moves and the CELL DOES NOT
data SrvApiAdj : NS.CSsPos → NS.CSsPos → Set where
  saReq  : SrvApiAdj NS.csAreq NS.csCanAwait
  saFI   : (ps : List Point) → SrvApiAdj (NS.csAfi ps) NS.csInt
  saDone : SrvApiAdj NS.csDdone NS.csTerm
  saRF   : (ht : Header × Tip) → SrvApiAdj NS.csCanAwait (NS.csWrf ht)
  saRB   : (pt : Point × Tip) → SrvApiAdj NS.csCanAwait (NS.csWrb pt)
  saAR   : SrvApiAdj NS.csCanAwait NS.csWar
  saMRF  : (ht : Header × Tip) → SrvApiAdj NS.csMust (NS.csWrf ht)
  saMRB  : (pt : Point × Tip) → SrvApiAdj NS.csMust (NS.csWrb pt)
  saIF   : (pt : Point × Tip) → SrvApiAdj NS.csInt (NS.csWif pt)
  saINF  : (tp : Tip) → SrvApiAdj NS.csInt (NS.csWin tp)

-- the client's non-io adjacencies (its seven api rows; a CS CLIENT has no `done`
-- row at all — `§4b`'s `cliDoneRow-⊥` is the machine check of that)
data CliApiAdj : NS.CScPos → NS.CScPos → Set where
  caReq    : CliApiAdj NS.ccIdle NS.ccWreq
  caFI     : (ps : List Point) → CliApiAdj NS.ccIdle (NS.ccWfi ps)
  caDone   : CliApiAdj NS.ccIdle NS.ccWdone
  caRecvF  : (ht : Header × Tip) → CliApiAdj (NS.ccArf ht) NS.ccIdle
  caRecvB  : (pt : Point × Tip) → CliApiAdj (NS.ccArb pt) NS.ccIdle
  caRecvIF : (pt : Point × Tip) → CliApiAdj (NS.ccAif pt) NS.ccIdle
  caRecvIN : (tp : Tip) → CliApiAdj (NS.ccAin tp) NS.ccIdle

-- the server's WIRE-SEND adjacencies: the cell goes `empty → full x` and the
-- payload is pinned by the row's own `≟` gate
data SrvSendAdj : NS.CSsPos → Payload → NS.CSsPos → Set where
  ssRF  : (h : Header) (tp : Tip)
        → SrvSendAdj (NS.csWrf (h , tp)) (rfPayload h tp) NS.csIdle
  ssRB  : (pt : Point) (tp : Tip)
        → SrvSendAdj (NS.csWrb (pt , tp)) (rbPayload pt tp) NS.csIdle
  ssAR  : SrvSendAdj NS.csWar arPayload NS.csMust
  ssIF  : (pt : Point) (tp : Tip)
        → SrvSendAdj (NS.csWif (pt , tp)) (ifPayload pt tp) NS.csIdle
  ssINF : (tp : Tip) → SrvSendAdj (NS.csWin tp) (inPayload tp) NS.csIdle

-- the client's WIRE-SEND adjacencies
data CliSendAdj : NS.CScPos → Payload → NS.CScPos → Set where
  csReq  : CliSendAdj NS.ccWreq rnPayload NS.ccAwait
  csFI   : (ps : List Point) → CliSendAdj (NS.ccWfi ps) (fiPayload ps) NS.ccInt
  csDone : CliSendAdj NS.ccWdone cdPayload NS.ccTerm

-- the server's WIRE-READ adjacencies: the cell goes `full x → draining x` and the
-- row is lenient in the tuple's first three components
data SrvReadAdj : NS.CSsPos → Payload → NS.CSsPos → Set where
  srReq  : {t : Time} {md : Mode} {ln : Length}
         → SrvReadAdj NS.csIdle (t , md , ln , chainSync MsgCSRequestNext) NS.csAreq
  srFI   : {t : Time} {md : Mode} {ln : Length} (ps : List Point)
         → SrvReadAdj NS.csIdle (t , md , ln , chainSync (MsgCSFindIntersect ps))
                      (NS.csAfi ps)
  srDone : {t : Time} {md : Mode} {ln : Length}
         → SrvReadAdj NS.csIdle (t , md , ln , chainSync MsgCSDone) NS.csDdone

-- the client's WIRE-READ adjacencies (the reader's `output` — the ONLY way a cell
-- leaves `full`, and it always advances the reader)
data CliReadAdj : NS.CScPos → Payload → NS.CScPos → Set where
  crRF  : {t : Time} {md : Mode} {ln : Length} (h : Header) (tp : Tip)
        → CliReadAdj NS.ccAwait (t , md , ln , chainSync (MsgCSRollForward h tp))
                     (NS.ccArf (h , tp))
  crRB  : {t : Time} {md : Mode} {ln : Length} (pt : Point) (tp : Tip)
        → CliReadAdj NS.ccAwait (t , md , ln , chainSync (MsgCSRollBackward pt tp))
                     (NS.ccArb (pt , tp))
  crAR  : {t : Time} {md : Mode} {ln : Length}
        → CliReadAdj NS.ccAwait (t , md , ln , chainSync MsgCSAwaitReply) NS.ccMust
  crMRF : {t : Time} {md : Mode} {ln : Length} (h : Header) (tp : Tip)
        → CliReadAdj NS.ccMust (t , md , ln , chainSync (MsgCSRollForward h tp))
                     (NS.ccArf (h , tp))
  crMRB : {t : Time} {md : Mode} {ln : Length} (pt : Point) (tp : Tip)
        → CliReadAdj NS.ccMust (t , md , ln , chainSync (MsgCSRollBackward pt tp))
                     (NS.ccArb (pt , tp))
  crIF  : {t : Time} {md : Mode} {ln : Length} (pt : Point) (tp : Tip)
        → CliReadAdj NS.ccInt (t , md , ln , chainSync (MsgCSIntersectFound pt tp))
                     (NS.ccAif (pt , tp))
  crINF : {t : Time} {md : Mode} {ln : Length} (tp : Tip)
        → CliReadAdj NS.ccInt (t , md , ln , chainSync (MsgCSIntersectNotFound tp))
                     (NS.ccAin tp)

------------------------------------------------------------------------
-- §4b  *** THE ADJACENCY PRODUCERS — WHERE §4 STOPS BEING A TRANSCRIPTION. ***
--
-- §4's six datatypes are HAND transcriptions of the two tables, and Agda cannot
-- check a transcription: an OMITTED row makes §5's preservation VACUOUSLY true for
-- a step that really exists.  The eight producers below are what closes that hole.
-- Each takes a FIRED TABLE ROW — `csSnxt`/`csCnxt` applied at the peer's OWN key,
-- yielding `just` — and returns the matching §4 constructor by a dispatch that is
-- TOTAL on the position datatype and, wherever the table splits further, on
-- `ApiCSTag` or on `Messages`/`MessageChainSync`.  *** TOTALITY IS THE CHECK: *** a
-- row present in the table but ABSENT from the adjacency leaves a `just` with no
-- constructor to return, and the clause simply cannot be written.
--
-- WHAT THIS STILL DOES NOT CATCH, stated so it is not over-read: a SPURIOUS
-- constructor (one with no table row) is invisible here, because these functions
-- only ever CONSTRUCT adjacencies.  The KEEP-IN-SYNC block above is the standing
-- defence, and the falsification of record for this section is a wrong row
-- CONSTRUCTOR: retargeting `ssAR` at `csIdle` must go red, and does, naming the
-- table's real target (**F35** — corrected at the T6b review, finding M-7: this
-- line used to say F32, which is the `ccPre` clause probe).  F34 is the OTHER
-- failure mode, an absent-row body at the same arm.
--
-- AND THE CROSS-FAMILY BLIND SPOT, closed as far as it can be: the producers'
-- signatures FIX the event families they cover — `{input, output, apiCS, done}` on
-- the server side, `{input, output, apiCS, done}` on the client's.  The client's
-- `done` producer is a REFUTATION (`cliDoneRow-⊥`), which is the machine check
-- that the CS client really has no `done` row; a ChainSync row added on a family
-- outside those four (an `apiKA` row, say) would be invisible to all eight, so if
-- either table gains one, a producer for THAT family must be added here.
--
-- THE KEYS ARE PINNED to the peer's own `(l , d)`.  A peer's table returns
-- `nothing` at any other key (the `l′ ≟ l | d′ ≟ d` gate of every row), so no step
-- at a foreign key exists to produce — a foreign-key step is a FRAME step for this
-- hop, never an adjacency.
------------------------------------------------------------------------

-- (1) THE SERVER'S FIVE WIRE-SEND ROWS (`input` at its own key).  The five
-- informative positions are exactly the five `≟`-gated rows; the eight others have
-- no `input` clause at all, so the table falls to its catch-all (`:490`).
srvSendRow : (l : Link) (d : Dir) (sa : NS.CSsPos) (x : Payload) (sa′ : NS.CSsPos)
           → NS.csSnxt l d sa (Payload , input l d N2N_ChainSync) x ≡ just sa′
           → SrvSendAdj sa x sa′
srvSendRow l d NS.csIdle     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csAreq     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csCanAwait x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d (NS.csAfi ps) x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csInt      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csDdone    x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csMust     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d NS.csTerm     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow l d (NS.csWrf (h , tp)) x sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj (NS.csWrf (h , tp)) (rfPayload h tp) z)
                (just-injective eq) (ssRF h tp)
srvSendRow l d (NS.csWrb (pt , tp)) x sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj (NS.csWrb (pt , tp)) (rbPayload pt tp) z)
                (just-injective eq) (ssRB pt tp)
srvSendRow l d NS.csWar x sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj NS.csWar arPayload z) (just-injective eq) ssAR
srvSendRow l d (NS.csWif (pt , tp)) x sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj (NS.csWif (pt , tp)) (ifPayload pt tp) z)
                (just-injective eq) (ssIF pt tp)
srvSendRow l d (NS.csWin tp) x sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj (NS.csWin tp) (inPayload tp) z)
                (just-injective eq) (ssINF tp)

-- (2) THE SERVER'S THREE WIRE-READ ROWS (`output` at its own key).  These rows
-- pattern-match the MESSAGE and leave `(time , mode , length)` free, so the
-- dispatch is on `Messages`/`MessageChainSync` as well as on the position — and the
-- resulting constructors are lenient in the same three components.
srvReadRow : (l : Link) (d : Dir) (sa : NS.CSsPos) (x : Payload) (sa′ : NS.CSsPos)
           → NS.csSnxt l d sa (Payload , output l d N2N_ChainSync) x ≡ just sa′
           → SrvReadAdj sa x sa′
srvReadRow l d NS.csAreq          x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csCanAwait      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d (NS.csAfi ps)      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csInt           x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csDdone         x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csMust          x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d (NS.csWrf ht)      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d (NS.csWrb pt)      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csWar           x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d (NS.csWif pt)      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d (NS.csWin tp)      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csTerm          x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , keepAlive m)    sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , blockFetch m)   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , txSubmission m) sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , leiosNotify m)  sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , leiosFetch m)   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync MsgCSAwaitReply)             sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync (MsgCSRollForward h tp))     sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync (MsgCSRollBackward pt tp))   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync (MsgCSIntersectFound pt tp)) sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync (MsgCSIntersectNotFound tp)) sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow l d NS.csIdle (t , md , ln , chainSync MsgCSRequestNext) sa′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvReadAdj NS.csIdle (t , md , ln , chainSync MsgCSRequestNext) z)
            (just-injective eq) srReq
srvReadRow l d NS.csIdle (t , md , ln , chainSync (MsgCSFindIntersect ps)) sa′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvReadAdj NS.csIdle
                     (t , md , ln , chainSync (MsgCSFindIntersect ps)) z)
            (just-injective eq) (srFI ps)
srvReadRow l d NS.csIdle (t , md , ln , chainSync MsgCSDone) sa′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvReadAdj NS.csIdle (t , md , ln , chainSync MsgCSDone) z)
            (just-injective eq) srDone

-- (3) THE SERVER'S NINE api ROWS.  The five positions that offer an api need the
-- `ApiCSTag` dispatch as well (the table matches the tag as a CONSTRUCTOR, so a tag
-- variable leaves it stuck); the eight other positions have no `apiCS` clause at
-- any tag and fall to the catch-all with the tag still a variable.
srvApiRow : (l : Link) (d : Dir) (sa : NS.CSsPos) (m : ApiCSTag) (v : ApiCSCar m)
            (sa′ : NS.CSsPos)
          → NS.csSnxt l d sa (ApiCSCar m , apiCS l d m) v ≡ just sa′
          → SrvApiAdj sa sa′
srvApiRow l d NS.csIdle      m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csDdone     m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csWrf ht)  m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csWrb pt)  m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csWar       m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csWif pt)  m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csWin tp)  m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csTerm      m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSRequestNext        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSFindIntersect      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSDone               v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSAwaitReply         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSRollForward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSRollBackward       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq sendCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq recvCSRollforward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq recvCSRollback           v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq recvCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq recvCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq reqCSFindIntersect       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csAreq reqCSRequestNext         v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csAreq z) (just-injective eq) saReq
srvApiRow l d (NS.csAfi ps) sendCSRequestNext        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSFindIntersect      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSDone               v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSAwaitReply         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSRollForward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSRollBackward       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) sendCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) recvCSRollforward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) recvCSRollback           v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) recvCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) recvCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) reqCSRequestNext         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d (NS.csAfi ps) reqCSFindIntersect       v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with _≟_ ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ v ps
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvApiAdj (NS.csAfi ps) z) (just-injective eq) (saFI ps)
srvApiRow l d NS.csCanAwait sendCSRequestNext        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait sendCSFindIntersect      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait sendCSDone               v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait sendCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait sendCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait recvCSRollforward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait recvCSRollback           v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait recvCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait recvCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait reqCSRequestNext         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait reqCSFindIntersect       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csCanAwait sendCSRollForward        v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csCanAwait z) (just-injective eq) (saRF v)
srvApiRow l d NS.csCanAwait sendCSRollBackward       v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csCanAwait z) (just-injective eq) (saRB v)
srvApiRow l d NS.csCanAwait sendCSAwaitReply         v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csCanAwait z) (just-injective eq) saAR
srvApiRow l d NS.csMust sendCSRequestNext        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSFindIntersect      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSDone               v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSAwaitReply         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust recvCSRollforward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust recvCSRollback           v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust recvCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust recvCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust reqCSRequestNext         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust reqCSFindIntersect       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csMust sendCSRollForward        v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csMust z) (just-injective eq) (saMRF v)
srvApiRow l d NS.csMust sendCSRollBackward       v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csMust z) (just-injective eq) (saMRB v)
srvApiRow l d NS.csInt sendCSRequestNext        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSFindIntersect      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSDone               v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSAwaitReply         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSRollForward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSRollBackward       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt recvCSRollforward        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt recvCSRollback           v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt recvCSIntersectFound     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt recvCSIntersectNotFound  v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt reqCSRequestNext         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt reqCSFindIntersect       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow l d NS.csInt sendCSIntersectFound     v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csInt z) (just-injective eq) (saIF v)
srvApiRow l d NS.csInt sendCSIntersectNotFound  v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csInt z) (just-injective eq) (saINF v)

-- (4) THE SERVER'S `done` ROW — the eighteenth row of `csSnxt`, on the only event
-- family neither io nor api (`done`, whose carrier is the non-polymorphic `⊤`)
srvDoneRow : (l : Link) (d : Dir) (sa : NS.CSsPos) (v : U0.⊤) (sa′ : NS.CSsPos)
           → NS.csSnxt l d sa (U0.⊤ , done l d N2N_ChainSync) v ≡ just sa′
           → SrvApiAdj sa sa′
srvDoneRow l d NS.csIdle       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csAreq       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csCanAwait   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d (NS.csAfi ps)   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csInt        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csMust       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d (NS.csWrf ht)   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d (NS.csWrb pt)   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csWar        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d (NS.csWif pt)   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d (NS.csWin tp)   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csTerm       v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow l d NS.csDdone      v sa′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.csDdone z) (just-injective eq) saDone

-- (5) THE CLIENT'S THREE WIRE-SEND ROWS (`input` at its own key)
cliSendRow : (l : Link) (d : Dir) (ca : NS.CScPos) (x : Payload) (ca′ : NS.CScPos)
           → NS.csCnxt l d ca (Payload , input l d N2N_ChainSync) x ≡ just ca′
           → CliSendAdj ca x ca′
cliSendRow l d NS.ccIdle      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d NS.ccAwait     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d NS.ccInt       x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d NS.ccMust      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d (NS.ccArf ht)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d (NS.ccArb pt)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d (NS.ccAif pt)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d (NS.ccAin tp)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d NS.ccTerm      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow l d NS.ccWreq x ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliSendAdj NS.ccWreq rnPayload z) (just-injective eq) csReq
cliSendRow l d (NS.ccWfi ps) x ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliSendAdj (NS.ccWfi ps) (fiPayload ps) z)
                (just-injective eq) (csFI ps)
cliSendRow l d NS.ccWdone x ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliSendAdj NS.ccWdone cdPayload z) (just-injective eq) csDone

-- (6) THE CLIENT'S SEVEN WIRE-READ ROWS (`output` at its own key) — the ONLY step
-- class that empties a `full` cell.  Three positions read, and each reads two or
-- three message classes, so this is the `Messages` dispatch three times over.
cliReadRow : (l : Link) (d : Dir) (ca : NS.CScPos) (x : Payload) (ca′ : NS.CScPos)
           → NS.csCnxt l d ca (Payload , output l d N2N_ChainSync) x ≡ just ca′
           → CliReadAdj ca x ca′
cliReadRow l d NS.ccIdle      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccWreq      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d (NS.ccWfi ps)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccWdone     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d (NS.ccArf ht)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d (NS.ccArb pt)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d (NS.ccAif pt)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d (NS.ccAin tp)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccTerm      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , keepAlive m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , blockFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , txSubmission m) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , leiosNotify m)  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , leiosFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync MsgCSRequestNext)             ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync (MsgCSFindIntersect ps))      ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync (MsgCSIntersectFound pt tp))  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync (MsgCSIntersectNotFound tp))  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync MsgCSDone)                    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync (MsgCSRollForward h tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccAwait
                     (t , md , ln , chainSync (MsgCSRollForward h tp)) z)
            (just-injective eq) (crRF h tp)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync (MsgCSRollBackward pt tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccAwait
                     (t , md , ln , chainSync (MsgCSRollBackward pt tp)) z)
            (just-injective eq) (crRB pt tp)
cliReadRow l d NS.ccAwait (t , md , ln , chainSync MsgCSAwaitReply) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccAwait (t , md , ln , chainSync MsgCSAwaitReply) z)
            (just-injective eq) crAR
cliReadRow l d NS.ccMust (t , md , ln , keepAlive m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , blockFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , txSubmission m) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , leiosNotify m)  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , leiosFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync MsgCSRequestNext)            ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync MsgCSAwaitReply)             ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync (MsgCSFindIntersect ps))     ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync (MsgCSIntersectFound pt tp)) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync (MsgCSIntersectNotFound tp)) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync MsgCSDone)                   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccMust (t , md , ln , chainSync (MsgCSRollForward h tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccMust
                     (t , md , ln , chainSync (MsgCSRollForward h tp)) z)
            (just-injective eq) (crMRF h tp)
cliReadRow l d NS.ccMust (t , md , ln , chainSync (MsgCSRollBackward pt tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccMust
                     (t , md , ln , chainSync (MsgCSRollBackward pt tp)) z)
            (just-injective eq) (crMRB pt tp)
cliReadRow l d NS.ccInt (t , md , ln , keepAlive m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , blockFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , txSubmission m) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , leiosNotify m)  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , leiosFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync MsgCSRequestNext)           ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync MsgCSAwaitReply)            ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync (MsgCSFindIntersect ps))    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync (MsgCSRollForward h tp))    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync (MsgCSRollBackward pt tp))  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync MsgCSDone)                  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow l d NS.ccInt (t , md , ln , chainSync (MsgCSIntersectFound pt tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccInt
                     (t , md , ln , chainSync (MsgCSIntersectFound pt tp)) z)
            (just-injective eq) (crIF pt tp)
cliReadRow l d NS.ccInt (t , md , ln , chainSync (MsgCSIntersectNotFound tp)) ca′ eq
  with l ≟ l | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.ccInt
                     (t , md , ln , chainSync (MsgCSIntersectNotFound tp)) z)
            (just-injective eq) (crINF tp)

-- (7) THE CLIENT'S SEVEN api ROWS
cliApiRow : (l : Link) (d : Dir) (ca : NS.CScPos) (m : ApiCSTag) (v : ApiCSCar m)
            (ca′ : NS.CScPos)
          → NS.csCnxt l d ca (ApiCSCar m , apiCS l d m) v ≡ just ca′
          → CliApiAdj ca ca′
cliApiRow l d NS.ccWreq     m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccAwait    m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccWfi ps) m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccInt      m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccWdone    m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccMust     m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccTerm     m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSAwaitReply         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSRollForward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSRollBackward       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle recvCSRollforward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle recvCSRollback           v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle recvCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle recvCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle reqCSRequestNext         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle reqCSFindIntersect       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d NS.ccIdle sendCSRequestNext        v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliApiAdj NS.ccIdle z) (just-injective eq) caReq
cliApiRow l d NS.ccIdle sendCSFindIntersect      v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliApiAdj NS.ccIdle z) (just-injective eq) (caFI v)
cliApiRow l d NS.ccIdle sendCSDone               v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliApiAdj NS.ccIdle z) (just-injective eq) caDone
cliApiRow l d (NS.ccArf ht) sendCSRequestNext        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSFindIntersect      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSDone               v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSAwaitReply         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSRollForward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSRollBackward       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) sendCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) recvCSRollback           v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) recvCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) recvCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) reqCSRequestNext         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) reqCSFindIntersect       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArf ht) recvCSRollforward        v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with _≟_ ⦃ DecEq-H×T ⦄ v ht
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliApiAdj (NS.ccArf ht) z) (just-injective eq) (caRecvF ht)
cliApiRow l d (NS.ccArb pt) sendCSRequestNext        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSFindIntersect      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSDone               v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSAwaitReply         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSRollForward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSRollBackward       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) sendCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) recvCSRollforward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) recvCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) recvCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) reqCSRequestNext         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) reqCSFindIntersect       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccArb pt) recvCSRollback           v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with _≟_ ⦃ DecEq-P×T ⦄ v pt
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliApiAdj (NS.ccArb pt) z) (just-injective eq) (caRecvB pt)
cliApiRow l d (NS.ccAif pt) sendCSRequestNext        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSFindIntersect      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSDone               v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSAwaitReply         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSRollForward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSRollBackward       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) sendCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) recvCSRollforward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) recvCSRollback           v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) recvCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) reqCSRequestNext         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) reqCSFindIntersect       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAif pt) recvCSIntersectFound     v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with _≟_ ⦃ DecEq-P×T ⦄ v pt
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliApiAdj (NS.ccAif pt) z) (just-injective eq) (caRecvIF pt)
cliApiRow l d (NS.ccAin tp) sendCSRequestNext        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSFindIntersect      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSDone               v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSAwaitReply         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSRollForward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSRollBackward       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) sendCSIntersectNotFound  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) recvCSRollforward        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) recvCSRollback           v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) recvCSIntersectFound     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) reqCSRequestNext         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) reqCSFindIntersect       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow l d (NS.ccAin tp) recvCSIntersectNotFound  v ca′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with _≟_ ⦃ DecEq-Tip ⦄ v tp
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliApiAdj (NS.ccAin tp) z) (just-injective eq) (caRecvIN tp)

-- (8) THE CLIENT'S `done` NON-ROW — machine-checked, TOTAL on `CScPos`.  The CS
-- client has no `done` handshake (`NodeSpecs:290`: `ccWdone → ccTerm` is the
-- WIRE-send, and the table's twelve positions have no `done` clause), so this
-- family is a refutation rather than a producer — which is exactly what closes
-- §4b's cross-family blind spot on the client side.
cliDoneRow-⊥ : (l : Link) (d : Dir) (ca : NS.CScPos) (v : U0.⊤) (ca′ : NS.CScPos)
             → NS.csCnxt l d ca (U0.⊤ , done l d N2N_ChainSync) v ≡ just ca′ → ⊥
cliDoneRow-⊥ l d NS.ccIdle      v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccWreq      v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccAwait     v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d (NS.ccWfi ps)  v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccInt       v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccWdone     v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccMust      v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d (NS.ccArf ht)  v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d (NS.ccArb pt)  v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d (NS.ccAif pt)  v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d (NS.ccAin tp)  v ca′ eq = nothing-absurd eq
cliDoneRow-⊥ l d NS.ccTerm      v ca′ eq = nothing-absurd eq

------------------------------------------------------------------------
-- §4c  THE STEP-LEVEL FORM: an adjacency off a REAL abstract peer STEP.
--
-- *** THIS IS WHERE THE T4 ROW LAYER PAYS. ***  `LiveCSRow.cssRow-of`/`cscRow-of`
-- already do the whole recovery — `tableSpec-ev-inv` at `Tcss`/`Tcsc` plus the
-- 313-pair coarse injectivity `tssInj`/`tscInj` — and hand back the FIRED COARSE
-- ROW between the two fine positions' coarsenings.  So each bridge below is §4b's
-- producer applied to that row, and this module re-derives no inversion at all
-- (`LiveChanInv` had to build its own `rowAdj` because the BF axis had no row
-- layer).  This is the sense in which "every real step produces its row" is a
-- THEOREM here rather than a reading.
------------------------------------------------------------------------

-- the server's fired WIRE-SEND row, at a real abstract step
srvSend-of : (l : Link) (d : Dir) (pos pos′ : SN.CSsPos) (x : Payload) {M : NetProc}
           → absCSs l d pos
             ─[ ev (evl (evLabel Payload (input l d N2N_ChainSync) x)) ]─► M
           → M ≡ absCSs l d pos′
           → SrvSendAdj (coarsenCSs pos) x (coarsenCSs pos′)
srvSend-of l d pos pos′ x step Meq =
  srvSendRow l d (coarsenCSs pos) x (coarsenCSs pos′)
             (cssRow-of l d pos pos′ step Meq)

-- … its fired WIRE-READ row
srvRead-of : (l : Link) (d : Dir) (pos pos′ : SN.CSsPos) (x : Payload) {M : NetProc}
           → absCSs l d pos
             ─[ ev (evl (evLabel Payload (output l d N2N_ChainSync) x)) ]─► M
           → M ≡ absCSs l d pos′
           → SrvReadAdj (coarsenCSs pos) x (coarsenCSs pos′)
srvRead-of l d pos pos′ x step Meq =
  srvReadRow l d (coarsenCSs pos) x (coarsenCSs pos′)
             (cssRow-of l d pos pos′ step Meq)

-- … its fired api row
srvApi-of : (l : Link) (d : Dir) (pos pos′ : SN.CSsPos) (m : ApiCSTag)
            (v : ApiCSCar m) {M : NetProc}
          → absCSs l d pos ─[ ev (evl (evLabel (ApiCSCar m) (apiCS l d m) v)) ]─► M
          → M ≡ absCSs l d pos′
          → SrvApiAdj (coarsenCSs pos) (coarsenCSs pos′)
srvApi-of l d pos pos′ m v step Meq =
  srvApiRow l d (coarsenCSs pos) m v (coarsenCSs pos′)
            (cssRow-of l d pos pos′ step Meq)

-- … and its fired `done` row
srvDone-of : (l : Link) (d : Dir) (pos pos′ : SN.CSsPos) (v : U0.⊤) {M : NetProc}
           → absCSs l d pos
             ─[ ev (evl (evLabel U0.⊤ (done l d N2N_ChainSync) v)) ]─► M
           → M ≡ absCSs l d pos′
           → SrvApiAdj (coarsenCSs pos) (coarsenCSs pos′)
srvDone-of l d pos pos′ v step Meq =
  srvDoneRow l d (coarsenCSs pos) v (coarsenCSs pos′)
             (cssRow-of l d pos pos′ step Meq)

-- the client's fired WIRE-SEND row
cliSend-of : (l : Link) (d : Dir) (pos pos′ : SN.CScPos) (x : Payload) {M : NetProc}
           → absCSc l d pos
             ─[ ev (evl (evLabel Payload (input l d N2N_ChainSync) x)) ]─► M
           → M ≡ absCSc l d pos′
           → CliSendAdj (coarsenCSc pos) x (coarsenCSc pos′)
cliSend-of l d pos pos′ x step Meq =
  cliSendRow l d (coarsenCSc pos) x (coarsenCSc pos′)
             (cscRow-of l d pos pos′ step Meq)

-- … its fired WIRE-READ row (the cell's delivery)
cliRead-of : (l : Link) (d : Dir) (pos pos′ : SN.CScPos) (x : Payload) {M : NetProc}
           → absCSc l d pos
             ─[ ev (evl (evLabel Payload (output l d N2N_ChainSync) x)) ]─► M
           → M ≡ absCSc l d pos′
           → CliReadAdj (coarsenCSc pos) x (coarsenCSc pos′)
cliRead-of l d pos pos′ x step Meq =
  cliReadRow l d (coarsenCSc pos) x (coarsenCSc pos′)
             (cscRow-of l d pos pos′ step Meq)

-- … and its fired api row
cliApi-of : (l : Link) (d : Dir) (pos pos′ : SN.CScPos) (m : ApiCSTag)
            (v : ApiCSCar m) {M : NetProc}
          → absCSc l d pos ─[ ev (evl (evLabel (ApiCSCar m) (apiCS l d m) v)) ]─► M
          → M ≡ absCSc l d pos′
          → CliApiAdj (coarsenCSc pos) (coarsenCSc pos′)
cliApi-of l d pos pos′ m v step Meq =
  cliApiRow l d (coarsenCSc pos) m v (coarsenCSc pos′)
            (cscRow-of l d pos pos′ step Meq)

------------------------------------------------------------------------
-- §5  *** THE PRESERVATION CALCULUS. ***  One lemma per step class.
--
-- The successor phase is written LITERALLY in each conclusion (`full x`,
-- `draining x`, `empty`) rather than through an equation, because the medium's
-- banked key lemmas produce exactly that: `PipeMedKey.cell-in-key` returns
-- `(ph ≡ empty) × (Mk ≡ decCopy … (full x))` and `cell-out-key` returns
-- `(ph ≡ full x) × (Mk ≡ decCopy … (draining x))`.
--
-- *** WHERE THE THREE CLAUSES DO THEIR WORK — one line each. ***  `ccReq` is
-- ESTABLISHED by the client's own request wire-send (`chan-cliSend`) and SPENT by
-- the server's wire-read (`chan-srvRead`, the only step that ENTERS the pre
-- region).  `ccPre` is spent to refute the client's three writes and the seven api
-- moves that leave `CliAwt` (`chan-cliApi`, `chan-cliSend`).  `ccQui` is
-- ESTABLISHED by the server's wire-read (which leaves the cell `draining`) and by
-- the medium's drain, and SPENT to refute all seven of the client's reads
-- (`chan-cliRead`, through `preQ-full-⊥`).
------------------------------------------------------------------------

-- (1) THE SERVER'S api/`done` STEPS — the cell and the client are fixed.  Four
-- edges stay INSIDE the pre region (`saReq`, `saFI`, `saAR` and nothing else) and
-- carry both clauses across; the other six LEAVE it, so their successors' two
-- region clauses are vacuous.
chan-srvApi : (sa sa′ : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
            → SrvApiAdj sa sa′ → ChanCS sa ph ca → ChanCS sa′ ph ca
chan-srvApi .NS.csAreq .NS.csCanAwait ph ca saReq iv =
  mkChanCS (λ _ → ccQui iv tt) (λ _ → ccPre iv tt) (ccReq iv)
chan-srvApi .(NS.csAfi ps) .NS.csInt ph ca (saFI ps) iv =
  mkChanCS (λ _ → ccQui iv tt) (λ _ → ccPre iv tt) (ccReq iv)
chan-srvApi .NS.csCanAwait .NS.csWar ph ca saAR iv =
  mkChanCS (λ _ → ccQui iv tt) (λ _ → ccPre iv tt) (ccReq iv)
chan-srvApi .NS.csDdone .NS.csTerm ph ca saDone iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csCanAwait .(NS.csWrf ht) ph ca (saRF ht) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csCanAwait .(NS.csWrb pt) ph ca (saRB pt) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csMust .(NS.csWrf ht) ph ca (saMRF ht) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csMust .(NS.csWrb pt) ph ca (saMRB pt) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csInt .(NS.csWif pt) ph ca (saIF pt) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)
chan-srvApi .NS.csInt .(NS.csWin tp) ph ca (saINF tp) iv =
  mkChanCS (λ ()) (λ ()) (ccReq iv)

-- (2) THE CLIENT'S api STEPS — the server and the cell are fixed.  ALL SEVEN
-- edges leave `CliAwt` (three from `ccIdle`, four from the api emits back to
-- `ccIdle`), so all seven are REFUTED from the source's own two client clauses —
-- one body, seven times.
chan-cliApi : (sa : NS.CSsPos) (ph : CopyPhase) (ca ca′ : NS.CScPos)
            → CliApiAdj ca ca′ → ChanCS sa ph ca → ChanCS sa ph ca′
chan-cliApi sa ph .NS.ccIdle .NS.ccWreq caReq iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .NS.ccIdle .(NS.ccWfi ps) (caFI ps) iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .NS.ccIdle .NS.ccWdone caDone iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .(NS.ccArf ht) .NS.ccIdle (caRecvF ht) iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .(NS.ccArb pt) .NS.ccIdle (caRecvB pt) iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .(NS.ccAif pt) .NS.ccIdle (caRecvIF pt) iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))
chan-cliApi sa ph .(NS.ccAin tp) .NS.ccIdle (caRecvIN tp) iv =
  mkChanCS (ccQui iv) (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccReq iv h))

-- (3) THE io FILL BY THE SERVER — the cell goes `empty → full x` and the client
-- does not move.  Every one of the five wire-sends LEAVES the pre region (four
-- land at `csIdle`, the `MsgCSAwaitReply` one at `csMust`), so the two region
-- clauses are vacuous at the successor; `ccReq` holds because a RESPONDER payload
-- is not a request, which is a constructor clash on `MessageChainSync`.
chan-srvSend : (sa sa′ : NS.CSsPos) (x : Payload) (ca : NS.CScPos)
             → SrvSendAdj sa x sa′ → ChanCS sa empty ca → ChanCS sa′ (full x) ca
chan-srvSend .(NS.csWrf (h , tp)) .NS.csIdle .(rfPayload h tp) ca (ssRF h tp) iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvSend .(NS.csWrb (pt , tp)) .NS.csIdle .(rbPayload pt tp) ca (ssRB pt tp) iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvSend .NS.csWar .NS.csMust .arPayload ca ssAR iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvSend .(NS.csWif (pt , tp)) .NS.csIdle .(ifPayload pt tp) ca (ssIF pt tp) iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvSend .(NS.csWin tp) .NS.csIdle .(inPayload tp) ca (ssINF tp) iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

-- (4) THE io FILL BY THE CLIENT — its two requests or its done message.  All
-- three rows start from a client position OUTSIDE `CliAwt`, so the source's
-- `ccPre` refutes the server's pre region outright and `ccQui` needs nothing else;
-- the two REQUEST rows then ESTABLISH `ccPre`/`ccReq` at the awaiting position the
-- wire-send itself advances to (this is the clause `chan-srvRead` will spend).
chan-cliSend : (sa : NS.CSsPos) (x : Payload) (ca ca′ : NS.CScPos)
             → CliSendAdj ca x ca′ → ChanCS sa empty ca → ChanCS sa (full x) ca′
chan-cliSend sa .rnPayload .NS.ccWreq .NS.ccAwait csReq iv =
  mkChanCS (λ h → ⊥-elim (ccPre iv h)) (λ _ → tt) (λ _ → tt)
chan-cliSend sa .(fiPayload ps) .(NS.ccWfi ps) .NS.ccInt (csFI ps) iv =
  mkChanCS (λ h → ⊥-elim (ccPre iv h)) (λ _ → tt) (λ _ → tt)
chan-cliSend sa .cdPayload .NS.ccWdone .NS.ccTerm csDone iv =
  mkChanCS (λ h → ⊥-elim (ccPre iv h)) (λ h → ⊥-elim (ccPre iv h))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

-- (5) *** THE SERVER'S WIRE-READ — the pre region is ENTERED here. ***  The cell
-- goes `full x → draining x`, so `ccQui` is ESTABLISHED outright (the crux fact:
-- a `draining` cell holds nothing unread), and `ccPre` is established from the
-- source's `ccReq` — the clause that exists for exactly this step.  The `MsgCSDone`
-- row lands at `csDdone`, outside the region, and is vacuous.
chan-srvRead : (sa sa′ : NS.CSsPos) (x : Payload) (ca : NS.CScPos)
             → SrvReadAdj sa x sa′ → ChanCS sa (full x) ca
             → ChanCS sa′ (draining x) ca
chan-srvRead .NS.csIdle .NS.csAreq _ ca (srReq {t} {md} {ln}) iv =
  mkChanCS (λ _ → inj₂ (_ , refl))
           (λ _ → ccReq iv (inj₁ (t , md , ln , refl)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvRead .NS.csIdle .(NS.csAfi ps) _ ca (srFI {t} {md} {ln} ps) iv =
  mkChanCS (λ _ → inj₂ (_ , refl))
           (λ _ → ccReq iv (inj₂ (ps , t , md , ln , refl)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-srvRead .NS.csIdle .NS.csDdone _ ca srDone iv =
  mkChanCS (λ ()) (λ ())
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

-- (6) *** THE CLIENT'S WIRE-READ — the clause `ccQui` exists to refute. ***  All
-- seven rows need the cell `full`, and every one of them lands the client OUTSIDE
-- `CliAwt`, so `ccPre` at the successor is refuted from the source's `ccQui`
-- through `preQ-full-⊥`.  One body, seven times — and note WHY, since the header's
-- corrected argument applies here too: `LiveChanInv.chan-cliRead` needs four
-- distinct bodies because two of its rows must keep a `cvStr` arm alive across the
-- read.  There is no `ccStr` to keep alive HERE, not because ChainSync's peers
-- alternate (they do not — see the header), but because this invariant is SCOPED to
-- the pre region, and inside the pre region a `full` cell is already excluded.
chan-cliRead : (sa : NS.CSsPos) (x : Payload) (ca ca′ : NS.CScPos)
             → CliReadAdj ca x ca′ → ChanCS sa (full x) ca
             → ChanCS sa (draining x) ca′
chan-cliRead sa _ .NS.ccAwait .(NS.ccArf (h , tp)) (crRF h tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccAwait .(NS.ccArb (pt , tp)) (crRB pt tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccAwait .NS.ccMust crAR iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccMust .(NS.ccArf (h , tp)) (crMRF h tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccMust .(NS.ccArb (pt , tp)) (crMRB pt tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccInt .(NS.ccAif (pt , tp)) (crIF pt tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })
chan-cliRead sa _ .NS.ccInt .(NS.ccAin tp) (crINF tp) iv =
  mkChanCS (λ _ → inj₂ (_ , refl)) (λ h₁ → ⊥-elim (preQ-full-⊥ _ (ccQui iv h₁)))
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

-- (7) THE MEDIUM's OWN DRAIN τ — `draining x → empty`, both peers fixed.  The
-- cell was already holding nothing unread, and it still is.
chan-drain : (sa : NS.CSsPos) (x : Payload) (ca : NS.CScPos)
           → ChanCS sa (draining x) ca → ChanCS sa empty ca
chan-drain sa x ca iv =
  mkChanCS (λ _ → inj₁ refl) (ccPre iv)
           (λ { (inj₁ (_ , _ , _ , ())) ; (inj₂ (_ , _ , _ , _ , ())) })

------------------------------------------------------------------------
-- §6  THE CONSUMERS — the pre-region cell fact, in the three shapes the `pp2`
-- ladder and its successors ask for.
--
-- *** WHAT A CS `H19` WOULD ADDITIONALLY NEED, recorded so the scope boundary is
-- not re-litigated. ***  `LiveChanInv.H19` is a THREE-armed disjunction ("empty, or
-- a payload its reader accepts, or draining") and it needs `cvStr`/`cvBlk` — the
-- READER-ALIGNMENT clauses — because the BF server may be sitting on an unread
-- block while its client is elsewhere.  The CS analogue would be a fourth clause
-- `SrvW sa → CliAwtR ca` over a SECOND server region (the five `csW*` wire-send
-- positions plus `csMust`) and a SECOND client region (`{ccAwait, ccMust, ccInt}`),
-- and each new clause adds an obligation to all seven §5 lemmas: ≈150 code.  It is
-- NOT built because NOTHING CONSUMES `H19` on this axis — `chanInv⇒h19` is gated on
-- `SrvStr` and its only consumers are the token-holding BF server arms
-- `LiveSrvOpen.srvOpen-up`/`srvOpen-dn` (`:214-297`), a family the CS axis does not
-- have (see the module header's corrected argument).  `pp2` needs `ccQui` at
-- `csWar`, which sits INSIDE the pre region where `full` is already excluded, so the
-- two-armed `CellPreQ` is complete there exactly as it is at `bsWsb`
-- (`LiveSrvOpen:312-320`); and `cp6`/`pp0` need the ARRIVAL relation (a driver-side
-- coupling), not a reader-alignment one.  Item 2a was priced "scoped to the
-- pre-region" and this is that scope, exactly.
------------------------------------------------------------------------

-- the pre-region cell fact, generic in the position
chanCS⇒preQ : (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
            → ChanCS sa ph ca → SrvPre sa → CellPreQ ph
chanCS⇒preQ sa ph ca iv h = ccQui iv h

-- *** THE `pp2` FORM. ***  at `csWar` the cell is empty or draining — i.e. either
-- the server's own `MsgCSAwaitReply` wire-send is enabled (`LiveIoIntroCS`'s
-- `medOfferInCS` + the CS io ladder) or the medium's drain τ is (`medDrainτCS`).
-- This is the fact `csWar-⊥`, the `LiveSrvOpen.srvWsb-⊥` twin, is missing.
chanCS-war⇒preQ : (ph : CopyPhase) (ca : NS.CScPos)
                → ChanCS NS.csWar ph ca → CellPreQ ph
chanCS-war⇒preQ ph ca iv = ccQui iv tt

-- … the same at an EQUATION on the server's coarse position, which is the shape a
-- carried coupling hands out (`LiveDrvBF.DrvCp`'s clauses are all
-- `coarsenCSs (dnCSs l s) ≡ …`)
chanCS-at-war : (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
              → ChanCS sa ph ca → sa ≡ NS.csWar → CellPreQ ph
chanCS-at-war sa ph ca iv eqs =
  ccQui iv (subst SrvPre (sym eqs) tt)

-- … and at `csCanAwait` and `csAreq`, the two other pre-region positions the
-- residual CS arms name (`pp1`'s and `cp6`/`pp0`'s slots): the SAME clause, so a
-- successor task pays nothing extra for them
chanCS-at-canAwait : (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
                   → ChanCS sa ph ca → sa ≡ NS.csCanAwait → CellPreQ ph
chanCS-at-canAwait sa ph ca iv eqs =
  ccQui iv (subst SrvPre (sym eqs) tt)

chanCS-at-areq : (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
               → ChanCS sa ph ca → sa ≡ NS.csAreq → CellPreQ ph
chanCS-at-areq sa ph ca iv eqs =
  ccQui iv (subst SrvPre (sym eqs) tt)

-- the CLIENT-side reading of the same invariant: in the server's pre region the
-- client is awaiting, so it offers no wire-send — the fact a cross-node arm needs
-- to know that the cell stays quiet (and the `cp6`/`pp0` direction's other half)
chanCS⇒cliAwt : (sa : NS.CSsPos) (ph : CopyPhase) (ca : NS.CScPos)
              → ChanCS sa ph ca → SrvPre sa → CliAwt ca
chanCS⇒cliAwt sa ph ca iv h = ccPre iv h

------------------------------------------------------------------------
-- §7  THE HOP INSTANCES, the per-hop EVOLUTION, and the ONE preservation theorem.
--
-- The invariant is applied FOUR times — the leg's up hop (node A's CS server, the
-- up CS cell, the relay's CS client) and its down hop (the relay's CS server, the
-- down CS cell, node D's CS client), at each of the two legs — through accessors
-- defined here, with NO restatement.
--
-- *** WHY THE ACCESSORS ARE LOCAL and not `LiveRelayOpen`'s. ***  `dnCSs`/`upCSc`
-- live in `LiveRelayOpen`, which sits far above this module in the DAG; importing
-- it would make the channel layer unusable by anything below it (and `LiveDrvBF`,
-- which is where the `pp2` coupling lives, is one of those consumers).  The two
-- definitions are LITERALLY the same expressions as `LiveRelayOpen:197-205`
-- (`SN.NodeStateB.csS-BD (nB s)` and so on), so a consumer holding either form can
-- pass it to the other by `refl`; the down-hop CLIENT and the two cells have no
-- accessor anywhere yet and are introduced here (this is the "no `phase …
-- N2N_ChainSync` site exists" gap the T6 verification confirmed four ways).
--
-- The dirs are read off `SysNode`'s bundle applications, not assumed.  *** THE
-- ATTRIBUTIONS BELOW WERE SWAPPED AND ARE CORRECTED (T6b review, finding M-5); the
-- CONCLUSION was and is right. ***  `bundleG : (l : Link) (cl sv : Dir) → …`
-- (`:909-917`) takes the CLIENT's direction first and the SERVER's second — its
-- body is `decCSc l cl csc ⦀ decCSs l sv css` (`:913`).  So:
--   · down hop, the relay's CS SERVER at `hi`: node B's BD bundle is
--     `bundleG linkBD lo hi` (`:1071`, inside `decNodeB`);
--   · down hop, node D's CS CLIENT at `hi`: node D's BD bundle is
--     `bundleG linkBD hi lo` (`:1005`, inside `decNodeD`);
--   · up hop, node A's CS SERVER at `hi`: `bundleA` HARDWIRES `lo hi` (`:862-869`,
--     the CS line `:865`), so node A's dirs are not visible at its `decNodeA` call
--     sites at all;
--   · up hop, the relay's CS CLIENT at `hi`: node B's AB bundle is
--     `bundleG linkAB hi lo` (`:1070`).
-- One cell, one writer, one reader, both at `hi`, at both hops — exactly as the BF
-- cell accessors are keyed.  (Leg CD is the same four facts with `decNodeC:1116-1117`
-- for node C and `decNodeD:1006` for node D.)
------------------------------------------------------------------------

-- the leg's UP-hop CS SERVER (node A's, on link AB for `legBD` / AC for `legCD`)
upCSsOf : TwoLegs → SysState → SN.CSsPos
upCSsOf legBD s = SN.NodeStateA.csS-AB (nA s)
upCSsOf legCD s = SN.NodeStateA.csS-AC (nA s)

-- … and its UP-hop CS CLIENT (the relay's own — `LiveRelayOpen.upCSc`'s expression)
upCScOf : TwoLegs → SysState → SN.CScPos
upCScOf legBD s = SN.NodeStateB.csC-AB (nB s)
upCScOf legCD s = SN.NodeStateC.csC-AC (nC s)

-- the leg's DOWN-hop CS SERVER (the relay's — `LiveRelayOpen.dnCSs`'s expression)
dnCSsOf : TwoLegs → SysState → SN.CSsPos
dnCSsOf legBD s = SN.NodeStateB.csS-BD (nB s)
dnCSsOf legCD s = SN.NodeStateC.csS-CD (nC s)

-- … and its DOWN-hop CS CLIENT (node D's — no accessor existed anywhere)
dnCScOf : TwoLegs → SysState → SN.CScPos
dnCScOf legBD s = SN.NodeStateD.csC-BD (nD s)
dnCScOf legCD s = SN.NodeStateD.csC-CD (nD s)

-- *** THE FIRST `phase … N2N_ChainSync` ACCESSORS IN THE DEVELOPMENT. ***  the
-- leg's UP CS cell (`(upLink l , hi , N2N_ChainSync)`) …
cellCSUp : TwoLegs → SysState → CopyPhase
cellCSUp l s = phase (med s) (upLink l) hi N2N_ChainSync

-- … and its DOWN CS cell, the one the `pp2` ladder fires from
cellCSDn : TwoLegs → SysState → CopyPhase
cellCSDn l s = phase (med s) (dnLink l) hi N2N_ChainSync

-- the leg's UP hop
ChanCSUp : TwoLegs → SysState → Set
ChanCSUp l s =
  ChanCS (coarsenCSs (upCSsOf l s)) (cellCSUp l s) (coarsenCSc (upCScOf l s))

-- … and its DOWN hop
ChanCSDn : TwoLegs → SysState → Set
ChanCSDn l s =
  ChanCS (coarsenCSs (dnCSsOf l s)) (cellCSDn l s) (coarsenCSc (dnCScOf l s))

-- one leg's two CS hops
ChanCSLeg : TwoLegs → SysState → Set
ChanCSLeg l s = ChanCSUp l s × ChanCSDn l s

-- BASE — at `initial` every CS peer sits at its idle head and every cell is empty,
-- so both hops of both legs are §3's base case
chanCSLeg-init : (l : TwoLegs) → ChanCSLeg l initial
chanCSLeg-init legBD = chanCS-init , chanCS-init
chanCSLeg-init legCD = chanCS-init , chanCS-init

-- the per-hop EVOLUTION across ONE step: which of the eight classes moved it.
-- `heFrame` is the "nothing in this hop moved" arm — a step at another link,
-- another protocol or another peer's api, or a link BREAK (which passes the phase
-- function through unchanged, `PipeEvStep:305`).
--
-- WHY A DATATYPE, not a nested `⊎`: the eight arms carry DIFFERENT index patterns
-- — the io classes pin the source AND the successor phase, the api classes fix the
-- phase, the drain fixes both peers — so as a datatype each arm's phase discipline
-- is checked at CONSTRUCTION and the preservation dispatch is forced total by the
-- datatype rather than by a reading.
data HopEvo : NS.CSsPos → CopyPhase → NS.CScPos
            → NS.CSsPos → CopyPhase → NS.CScPos → Set where
  heFrame   : ∀ {sa ph ca} → HopEvo sa ph ca sa ph ca
  heSrvApi  : ∀ {sa sa′ ph ca} → SrvApiAdj sa sa′ → HopEvo sa ph ca sa′ ph ca
  heCliApi  : ∀ {sa ph ca ca′} → CliApiAdj ca ca′ → HopEvo sa ph ca sa ph ca′
  heSrvSend : ∀ {sa sa′ ca} {x : Payload} → SrvSendAdj sa x sa′
            → HopEvo sa empty ca sa′ (full x) ca
  heCliSend : ∀ {sa ca ca′} {x : Payload} → CliSendAdj ca x ca′
            → HopEvo sa empty ca sa (full x) ca′
  heSrvRead : ∀ {sa sa′ ca} {x : Payload} → SrvReadAdj sa x sa′
            → HopEvo sa (full x) ca sa′ (draining x) ca
  heCliRead : ∀ {sa ca ca′} {x : Payload} → CliReadAdj ca x ca′
            → HopEvo sa (full x) ca sa (draining x) ca′
  heDrain   : ∀ {sa ca} {x : Payload} → HopEvo sa (draining x) ca sa empty ca

-- *** THE ONE PRESERVATION THEOREM. ***  a TOTAL dispatch on the evolution
-- datatype; every arm is §5's lemma for that class, applied and nothing else
chanCS-pres : {sa sa′ : NS.CSsPos} {ph ph′ : CopyPhase} {ca ca′ : NS.CScPos}
            → HopEvo sa ph ca sa′ ph′ ca′ → ChanCS sa ph ca → ChanCS sa′ ph′ ca′
chanCS-pres heFrame         iv = iv
chanCS-pres (heSrvApi adj)  iv = chan-srvApi  _ _ _ _ adj iv
chanCS-pres (heCliApi adj)  iv = chan-cliApi  _ _ _ _ adj iv
chanCS-pres (heSrvSend adj) iv = chan-srvSend _ _ _ _ adj iv
chanCS-pres (heCliSend adj) iv = chan-cliSend _ _ _ _ adj iv
chanCS-pres (heSrvRead adj) iv = chan-srvRead _ _ _ _ adj iv
chanCS-pres (heCliRead adj) iv = chan-cliRead _ _ _ _ adj iv
chanCS-pres heDrain         iv = chan-drain   _ _ _ iv

-- … the same with the successor's three components given by EQUATIONS instead of
-- literally: the frame lemma composed with the dispatch, once
chanCS-pres-eq : {sa sa′ sa″ : NS.CSsPos} {ph ph′ ph″ : CopyPhase}
                 {ca ca′ ca″ : NS.CScPos}
               → sa″ ≡ sa′ → ph″ ≡ ph′ → ca″ ≡ ca′
               → HopEvo sa ph ca sa′ ph′ ca′ → ChanCS sa ph ca → ChanCS sa″ ph″ ca″
chanCS-pres-eq ue ce cle evo iv =
  chanCS-frame _ _ _ _ _ _ (sym ue) (sym ce) (sym cle) (chanCS-pres evo iv)

-- … and with the SOURCE's three components given by equations TOO.  A real caller
-- holds the source phase PROPOSITIONALLY — `PipeMedKey.cell-in-key` returns
-- `ph ≡ empty`, and that `ph` is the leg's `cellCSDn l s` only after
-- `PipeTauIo.atKey` — so without this form it must hand-roll a source frame before
-- it can name the `HopEvo` arm.  Two frames and the dispatch.
chanCS-pres-eq² : {sa₀ sa sa′ sa″ : NS.CSsPos} {ph₀ ph ph′ ph″ : CopyPhase}
                  {ca₀ ca ca′ ca″ : NS.CScPos}
                → sa₀ ≡ sa → ph₀ ≡ ph → ca₀ ≡ ca
                → sa″ ≡ sa′ → ph″ ≡ ph′ → ca″ ≡ ca′
                → HopEvo sa ph ca sa′ ph′ ca′
                → ChanCS sa₀ ph₀ ca₀ → ChanCS sa″ ph″ ca″
chanCS-pres-eq² ue₀ ce₀ cle₀ ue ce cle evo iv =
  chanCS-pres-eq ue ce cle evo (chanCS-frame _ _ _ _ _ _ ue₀ ce₀ cle₀ iv)

-- the UP hop's evolution across one step, at the accessors
ChanCSUpEvo : TwoLegs → SysState → SysState → Set
ChanCSUpEvo l s s′ =
  HopEvo (coarsenCSs (upCSsOf l s))  (cellCSUp l s)  (coarsenCSc (upCScOf l s))
         (coarsenCSs (upCSsOf l s′)) (cellCSUp l s′) (coarsenCSc (upCScOf l s′))

-- … and the DOWN hop's
ChanCSDnEvo : TwoLegs → SysState → SysState → Set
ChanCSDnEvo l s s′ =
  HopEvo (coarsenCSs (dnCSsOf l s))  (cellCSDn l s)  (coarsenCSc (dnCScOf l s))
         (coarsenCSs (dnCSsOf l s′)) (cellCSDn l s′) (coarsenCSc (dnCScOf l s′))

-- THE LIFT AT THE UP HOP, with the successor's components read off the peel's OWN
-- equations (the form a real step can feed; `ChanCSUpEvo` is its `refl` case)
chanCSUp-pres : (l : TwoLegs) (s s′ : SysState)
                {sa′ : NS.CSsPos} {ph′ : CopyPhase} {ca′ : NS.CScPos}
              → coarsenCSs (upCSsOf l s′) ≡ sa′ → cellCSUp l s′ ≡ ph′
              → coarsenCSc (upCScOf l s′) ≡ ca′
              → HopEvo (coarsenCSs (upCSsOf l s)) (cellCSUp l s)
                       (coarsenCSc (upCScOf l s)) sa′ ph′ ca′
              → ChanCSUp l s → ChanCSUp l s′
chanCSUp-pres l s s′ ue ce cle evo iv = chanCS-pres-eq ue ce cle evo iv

-- … and at the DOWN hop
chanCSDn-pres : (l : TwoLegs) (s s′ : SysState)
                {sa′ : NS.CSsPos} {ph′ : CopyPhase} {ca′ : NS.CScPos}
              → coarsenCSs (dnCSsOf l s′) ≡ sa′ → cellCSDn l s′ ≡ ph′
              → coarsenCSc (dnCScOf l s′) ≡ ca′
              → HopEvo (coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                       (coarsenCSc (dnCScOf l s)) sa′ ph′ ca′
              → ChanCSDn l s → ChanCSDn l s′
chanCSDn-pres l s s′ de fe dle evo iv = chanCS-pres-eq de fe dle evo iv

-- *** ONE LEG'S TWO CS HOPS ACROSS ONE STEP. ***  the object a join would thread
chanCSLeg-pres : (l : TwoLegs) (s s′ : SysState)
               → ChanCSUpEvo l s s′ → ChanCSDnEvo l s s′
               → ChanCSLeg l s → ChanCSLeg l s′
chanCSLeg-pres l s s′ eu ed (ivU , ivD) =
    chanCSUp-pres l s s′ refl refl refl eu ivU
  , chanCSDn-pres l s s′ refl refl refl ed ivD

-- FRAME at the leg: the SIX slots the two hops read, all fixed — a step at another
-- link, another protocol, another peer's api, or a link break
chanCSLeg-frame : (l : TwoLegs) (s s′ : SysState)
                → upCSsOf l s ≡ upCSsOf l s′ → cellCSUp l s ≡ cellCSUp l s′
                → upCScOf l s ≡ upCScOf l s′
                → dnCSsOf l s ≡ dnCSsOf l s′ → cellCSDn l s ≡ cellCSDn l s′
                → dnCScOf l s ≡ dnCScOf l s′
                → ChanCSLeg l s → ChanCSLeg l s′
chanCSLeg-frame l s s′ ue ce cle de fe dle (ivU , ivD) =
    chanCSUp-pres l s s′ (cong coarsenCSs (sym ue)) (sym ce)
      (cong coarsenCSc (sym cle)) heFrame ivU
  , chanCSDn-pres l s s′ (cong coarsenCSs (sym de)) (sym fe)
      (cong coarsenCSc (sym dle)) heFrame ivD

-- *** THE DOWN-HOP CONSUMER AT A STATE. ***  the `pp2` ladder's own shape: the
-- leg's down CS server at `csWar` has a cell that is empty or draining
chanCSDn-war : (l : TwoLegs) (s : SysState)
             → ChanCSDn l s → coarsenCSs (dnCSsOf l s) ≡ NS.csWar
             → CellPreQ (cellCSDn l s)
chanCSDn-war l s iv eqs =
  chanCS-at-war (coarsenCSs (dnCSsOf l s)) (cellCSDn l s)
                (coarsenCSc (dnCScOf l s)) iv eqs
