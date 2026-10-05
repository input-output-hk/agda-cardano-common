{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 2 — *** THE PER-HOP BlockFetch CHANNEL
-- INVARIANT ***, payload-generic, with its preservation calculus.
--
-- WHAT THIS IS, AND WHY IT IS THE ONE OBJECT THE io FAMILY NEEDED.  Task 1
-- landed the four cell facts conditional on `LiveCellOpen.CellRdy` — "a cell
-- holding the token has its reader aligned" — and PARKED it, because its
-- preservation has exactly one arm that is not a transport: the io FILL, where
-- the reader's position must be established from the SOURCE state.  The Task-1
-- review's verdict (its §3) is that no cheap widening exists (both naive shapes
-- are FALSE; the machine-checked counter-state of record is
-- `LTL/Evidence/PipeCellFalse.agda`, which shows the StartBatch-unread
-- configuration lies on EVERY delivering run), and that the honest object is a
-- per-hop channel invariant.  This module is that object.
--
-- THE CRUX STRUCTURAL FACT the route rests on (review finding I-4): *a copy cell
-- can only be emptied by a reader's `output`, and that `output` ADVANCES the
-- reader* (`SysMedium.decCopy`: `full x` has the single visible offer `output …
-- ! x`, `draining x` is its post-`output` derivative whose force is the loop-back
-- `sil`, and there is no `full → empty` edge and no `full`-accepting `input`).
-- So "the cell is empty NOW" is a state-based encoding of "the previous payload
-- was consumed", which is precisely the capacity argument `LiveLegInv.agda:564-573`
-- names and declines.  Every `cvStr`/`cvQui` arm below is that fact in action.
--
-- PAYLOAD-GENERIC BY CONSTRUCTION (review finding I-2).  The invariant never
-- mentions `blkA`, never mentions a leg, and never mentions a link: it is five
-- clauses over ONE hop's three abstract components
--
--     (server position , cell phase , client position)
--
-- and the two instances the campaign needs — `bcStream` at a block payload
-- (Task 1's `CellRdy`) and `bcBusy` at `MsgStartBatch` (the H19 middle arm) — are
-- both CONSEQUENCES (§6), through `LiveChanRead`'s payload-generic
-- `CliAcceptsA`.  The four hop instances (2 legs × up/down) are four
-- APPLICATIONS of the same statement (§7), not four copies.
--
-- CONTENTS
--   §1  the wire payloads and the message-class reader on a cell phase
--   §2  the four position REGIONS, as total dispatches on the ABSTRACT position
--       types (`NodeSpecs.BFsPos`/`BFcPos` — ten and seven constructors, no
--       catch-all), and the cell-phase predicates
--   §3  *** THE INVARIANT ***: five clauses, and what each one is for
--   §4  the six step ADJACENCIES — transcriptions of `bfSnxt`'s twelve rows and
--       `bfCnxt`'s nine (see the KEEP-IN-SYNC block)
--   §4b *** THE ADJACENCY PRODUCERS ***: every fired table row yields its §4
--       constructor, by a dispatch TOTAL on the position/tag/message datatypes —
--       which is what makes §4 machine-checked in the direction that matters and
--       closes the vacuity hole an omitted row would leave
--   §4c the same at the STEP level, off `tableSpec-ev-inv`: a real visible step
--       of a real peer produces its adjacency
--   §5  *** THE PRESERVATION CALCULUS ***: one lemma per step class, including
--       `chan-srvSend` — the io FILL, i.e. CellRdy's hard arm, which closes as a
--       pure application of the SOURCE state's clauses
--   §6  the consumers: the payload-generic reader fact, the THREE-ARMED H19
--       disjunction, and the block instance
--   §7  the four hop instances, `CellRdy` DISCHARGED, and the four cell facts at
--       `InFlightOpen`'s field types
--   §7b *** THE LEG-LEVEL LIFT ***: the per-hop evolution datatype, the ONE
--       preservation theorem over its eight arms, and the lift along the four
--       accessors — `PipeSrvInv`'s `UpSrvEvo`/`srvCoupled-pres` shape at this hop
--   §7c the DISCHARGE: `LiveCellOpen`'s own four cell theorems, applied to the
--       DERIVED `CellRdy` instead of its parked one
--
-- WHAT IS NOT HERE, AND WHY (honest scope).  The REACHABILITY closure — carrying
-- §7b's per-step preservation along a run, i.e. the `RState` wrappers — is the
-- ASSEMBLY's job, exactly as it is for `LiveLegStep.NoTwoTokens` (proved in
-- `LiveTokenExcl` "statement, base, frame and preservation over every step
-- class", with the wrappers deferred, `LiveTokenExcl.agda:1100-1113`).  So
-- `ChanLeg` has the same status as `NoTwoTokens`: an object with a base case, a
-- frame and a complete preservation calculus, not a parked statement.  What §7b
-- ALSO does not do is peel the FSim's own step arms down to the peer steps §4c
-- consumes; the banked peels that do it (`PipeMedKey.cell-in-key`/`cell-out-key`
-- for the cell, `LiveLegIoCone`'s cones for the peers) meet §7b's interface
-- exactly — its equations are written in the LITERAL successor shape those
-- lemmas produce.  Task-2's claim that this wiring "is a transcription, not new
-- content" was WRONG (review I-2) and is withdrawn: §4b/§4c/§7b are ~430 lines.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`.
------------------------------------------------------------------------

open import Data.Bool using ( false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( just )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- the NON-polymorphic `⊤`, qualified: it is the carrier of the `done` event and
-- of the payload-free api tags, and must not shadow the polymorphic one above
import Data.Unit as U0
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; subst; cong )

-- the `_≟_` the two decode tables gate their key and payload comparisons on:
-- the SAME instances must be in scope here, or §4b's `with`-abstractions cannot
-- see the tables' own comparisons (`DecEq-Fin` for `Link = Fin numLinks`,
-- `DecEq-Dir` for `Dir`, `DecEq-ChainRange`/`decBlock`/`DecEq-Payload` for the
-- three gated values)
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )

open import Process_Trees using ( ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Link; input; output; done; apiBF; ApiBFTag; ApiBFCar
        ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
        ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Messages; blockFetch; keepAlive; chainSync; txSubmission
        ; leiosNotify; leiosFetch; MessageBlockFetch; ChainRange
        ; MsgRequestRange; MsgStartBatch; MsgNoBlocks; MsgBlock
        ; MsgBatchDone; MsgClientDone; DecEq-ChainRange; DecEq-Payload )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; N2N_BlockFetch; Mode; FromInitiator; FromResponder; DecEq-Dir )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length; time₀; length₀; decBlock )
import CSP.Examples.Cardano_network.BlockFetch p as BF

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken; CopyPhase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; coarsenBFs; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( ceqBFc03; ceqBFc05 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn; upClient; dnClient; BFcHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( lpUpCell; lpDnCell; CellFull⁺; cellFull⁺⇒fullBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA
  using ( NoTwoTokens; nUpCellCli; nDnCellCli )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( RefutedAt; Window; wLink1; wLink2 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCellOpen blkA
  -- (T4, review I-2: the two window-form theorems `cellOpen-up-w`/`cellOpen-dn-w`
  -- are NO LONGER imported — §7c now layers over §7's raw pair instead of taking
  -- the independent route through them)
  using ( CliStream; CellRdy )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanRead blkA
  using ( CliAcceptsA; sbPayload; acceptsBlk⇒stream
        ; cellFull-up-⊥; cellFull-dn-⊥ )
-- (T2 review M-1) both abstract BF offer tables, from the copy the frozen io
-- decodes already use — `SysIoLink5:2324-2325` (`Tbfc`) and `:2780-2781` (`Tbfs`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( Tbfc; Tbfs )

------------------------------------------------------------------------
-- §1  THE WIRE PAYLOADS, AND THE MESSAGE CLASS OF AN UNREAD CELL.
--
-- The four RESPONDER-side payloads and the two INITIATOR-side ones are exactly
-- the tuples `bfSnxt`/`bfCnxt`'s wire-SEND rows are `≟`-gated on
-- (`NodeSpecs.agda:610-639`, `:524-535`), so a cell filled by either peer holds
-- one of these six terms verbatim.  The wire-READ rows, by contrast, are
-- LENIENT in `(time , mode , length)` (they pattern-match the message only), so
-- every predicate below reads the cell through `FullMsg`, which is lenient too —
-- that is what makes the read classes of §4 faithful rather than convenient.
------------------------------------------------------------------------

-- the `MsgNoBlocks` wire payload of a responder-side BF sender
nbPayload : Payload
nbPayload = time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks

-- … the `MsgBatchDone` one
bdPayload : Payload
bdPayload = time₀ , FromResponder , length₀ , blockFetch MsgBatchDone

-- … the initiator-side `MsgRequestRange r`
rrPayload : ChainRange → Payload
rrPayload r = time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)

-- … and the initiator-side `MsgClientDone`
cdPayload : Payload
cdPayload = time₀ , FromInitiator , length₀ , blockFetch MsgClientDone

-- the cell holds an UNREAD payload carrying the BlockFetch message `mb`
-- (lenient in the tuple's other three components, exactly as the readers' table
-- rows are)
FullMsg : CopyPhase → MessageBlockFetch → Set
FullMsg ph mb = Σ[ t ∈ Time ] Σ[ md ∈ Mode ] Σ[ ln ∈ Length ]
                  (ph ≡ full (t , md , ln , blockFetch mb))

-- `full` is injective (used to identify the cell's payload with the one the
-- consumer asks about)
full-inj : {x y : Payload} → full x ≡ full y → x ≡ y
full-inj refl = refl

------------------------------------------------------------------------
-- §2  THE FOUR REGIONS, and the cell-phase predicates.
--
-- Each region is a total dispatch on the ABSTRACT position datatype, so it is
-- exhaustive with no catch-all and every membership question reduces to `⊤`/`⊥`.
------------------------------------------------------------------------

-- the BF SERVER is in its STREAMING region: it has wire-sent its
-- `MsgStartBatch` and has not yet wire-sent its `MsgBatchDone`.  (The region is
-- ENTERED only by that wire-send — `bfSnxt bsWsb (input …) ≡ just bsStream` — and
-- LEFT only by the `MsgBatchDone`/`MsgBlock` wire-sends, which is what makes §5's
-- arms decidable.)
SrvStr : NS.BFsPos → Set
SrvStr NS.bsIdle      = ⊥
SrvStr (NS.bsAreq r)  = ⊥
SrvStr NS.bsBusy      = ⊥
SrvStr NS.bsDdone     = ⊥
SrvStr NS.bsWsb       = ⊥
SrvStr NS.bsStream    = ⊤
SrvStr NS.bsWnb       = ⊥
SrvStr (NS.bsWblk b)  = ⊤
SrvStr NS.bsWbd       = ⊤
SrvStr NS.bsTerm      = ⊥

-- … and its PRE region: it has taken the client's request and its own
-- `MsgStartBatch` / `MsgNoBlocks` has not reached the wire yet
SrvPre : NS.BFsPos → Set
SrvPre NS.bsIdle      = ⊥
SrvPre (NS.bsAreq r)  = ⊤
SrvPre NS.bsBusy      = ⊤
SrvPre NS.bsDdone     = ⊥
SrvPre NS.bsWsb       = ⊤
SrvPre NS.bsStream    = ⊥
SrvPre NS.bsWnb       = ⊤
SrvPre (NS.bsWblk b)  = ⊥
SrvPre NS.bsWbd       = ⊥
SrvPre NS.bsTerm      = ⊥

-- the BF CLIENT has read its `MsgStartBatch` and has not yet read its
-- `MsgBatchDone`: streaming, or holding a delivered block
CliStrA : NS.BFcPos → Set
CliStrA NS.bcIdle      = ⊥
CliStrA (NS.bcWrr r)   = ⊥
CliStrA NS.bcBusy      = ⊥
CliStrA NS.bcWcd       = ⊥
CliStrA NS.bcStream    = ⊤
CliStrA (NS.bcAblk b)  = ⊤
CliStrA NS.bcTerm      = ⊥

-- … and is still awaiting it
CliBusyA : NS.BFcPos → Set
CliBusyA NS.bcIdle      = ⊥
CliBusyA (NS.bcWrr r)   = ⊥
CliBusyA NS.bcBusy      = ⊤
CliBusyA NS.bcWcd       = ⊥
CliBusyA NS.bcStream    = ⊥
CliBusyA (NS.bcAblk b)  = ⊥
CliBusyA NS.bcTerm      = ⊥

-- NOTE (Task 2b cleanup): the region-DISJOINTNESS lemma `srvStr-pre-⊥` used to
-- sit here, with a comment claiming §5's client-read arms consume it.  They do
-- not — `chan-cliRead` refutes its two arms with the LOCAL `nbBusy-⊥`/
-- `bdStream-⊥` instead — and nothing else consumed it either, so it is deleted.
-- The two regions are still disjoint by construction (`SrvStr` and `SrvPre` are
-- total dispatches on `BFsPos` whose `⊤` sets do not meet), and any future
-- consumer should re-derive the one line it needs rather than keep a lemma
-- alive for documentation.

-- the client's coarse position is the awaiting one (read off the region)
cliBusy⇒eq : (ca : NS.BFcPos) → CliBusyA ca → ca ≡ NS.bcBusy
cliBusy⇒eq NS.bcIdle     ()
cliBusy⇒eq (NS.bcWrr r)  ()
cliBusy⇒eq NS.bcBusy     _ = refl
cliBusy⇒eq NS.bcWcd      ()
cliBusy⇒eq NS.bcStream   ()
cliBusy⇒eq (NS.bcAblk b) ()
cliBusy⇒eq NS.bcTerm     ()

-- the client HOLDS a delivered block (the escape arm of §6's reader fact, cut at
-- every use site by the carried `NoTwoTokens`)
CliHoldA : NS.BFcPos → Set
CliHoldA ca = Σ[ b ∈ Block₃ ] (ca ≡ NS.bcAblk b)

-- the streaming region splits into "at the delivery position" and "holding"
cliStr⇒eq : (ca : NS.BFcPos) → CliStrA ca → (ca ≡ NS.bcStream) ⊎ CliHoldA ca
cliStr⇒eq NS.bcIdle     ()
cliStr⇒eq (NS.bcWrr r)  ()
cliStr⇒eq NS.bcBusy     ()
cliStr⇒eq NS.bcWcd      ()
cliStr⇒eq NS.bcStream   _ = inj₁ refl
cliStr⇒eq (NS.bcAblk b) _ = inj₂ (b , refl)
cliStr⇒eq NS.bcTerm     ()

-- the cell holds an unread block (any block)
BlkFull : CopyPhase → Set
BlkFull ph = Σ[ b ∈ Block₃ ] FullMsg ph (MsgBlock b)

-- the cell holds an unread client request
ReqFull : CopyPhase → Set
ReqFull ph = Σ[ r ∈ ChainRange ] FullMsg ph (MsgRequestRange r)

-- the cell is compatible with a client that has already read its
-- `MsgStartBatch`: it is empty, or draining, or holds an unread block
CellQuiet : CopyPhase → Set
CellQuiet ph = (ph ≡ empty) ⊎ (Σ[ x ∈ Payload ] (ph ≡ draining x)) ⊎ BlkFull ph

-- *** THE PRE-REGION CELL PREDICATE (cross-node api campaign, T2). ***  The cell
-- of a channel whose server is in its PRE region holds nothing UNREAD: it is
-- empty, or already DRAINING what was read out of it.
--
-- *** THIS REPLACED A WEAKER PREDICATE, AND THE STRENGTHENING IS THE POINT. ***
-- `cvQui` used to say "no RESPONDER-side payload is in flight" (`RespFull ph → ⊥`,
-- a NEGATIVE fact over the server's own four wire messages).  That polarity is
-- unusable for a stability ladder, which needs the POSITIVE cell phase to fire the
-- server's wire-send (`medOfferIn` wants `phase … ≡ empty`) — and `¬ RespFull`
-- admits `full (rrPayload r)`, `full cdPayload` and `draining`, so it pins nothing.
-- `CellPreQ` is the positive form.  It is STRICTLY STRONGER (`preQ-full-⊥`
-- below is what the old field's consumers take, and more), and it is preserved at every step class for one
-- reason: the only two rows that FILL the cell are the client's own wire-sends, and
-- both start from a client position OUTSIDE the awaiting one, which `cvPre` already
-- refutes against the server's pre region.  So the strengthening costs nothing at
-- twenty-one of the twenty-three producer sites (§5).
CellPreQ : CopyPhase → Set
CellPreQ ph = (ph ≡ empty) ⊎ (Σ[ x ∈ Payload ] (ph ≡ draining x))

-- a `full` cell is NOT a pre-region cell — the form the old `cvQui` consumers take
-- (and strictly more than they used to get: ANY unread payload refutes the pre
-- region now, not only a responder-side one)
preQ-full-⊥ : (x : Payload) → CellPreQ (full x) → ⊥
preQ-full-⊥ x (inj₁ ())
preQ-full-⊥ x (inj₂ (_ , ()))

------------------------------------------------------------------------
-- §3  *** THE INVARIANT. ***  Five clauses on one hop's three components.
--
-- WHAT EACH CLAUSE IS FOR, and why none can be dropped:
--
--   `cvStr` — THE WORKHOUSE.  In the server's streaming region the channel is in
--             one of exactly two configurations: the `MsgStartBatch` is still
--             unread and the client is still awaiting it, or the cell is quiet
--             (empty / draining / an unread block) and the client has advanced.
--             §6 reads BOTH consumers off this clause.
--   `cvBlk` — an unread BLOCK in the cell puts its server in the streaming
--             region.  This is what lets §7's cell facts drop `cvStr`'s server
--             gate (`AtPos lpUpCell` says nothing about the server).
--   `cvPre` — in the server's pre region the client is awaiting.  This is the
--             clause the io FILL of the `MsgStartBatch` consumes (§5's
--             `chan-srvSend`, arm `ssSB`) — i.e. CellRdy's hard arm pays here.
--   `cvQui` — in the server's pre region the cell holds nothing UNREAD: it is
--             empty or draining (`CellPreQ`).  This is the clause that refutes the
--             four client-read arms that would otherwise break `cvPre` (§5's
--             `chan-cliRead`, through `preQ-full-⊥`), and — since T2 strengthened
--             its polarity — the clause the `pp5` stability ladder fires the
--             server's own wire-send from (`LiveSrvOpen.srvWsb-⊥`).
--   `cvReq` — an unread REQUEST in the cell has its client awaiting.  This is
--             what carries `cvPre` across the server's wire-READ of the request,
--             the step that ENTERS the pre region (§5's `chan-srvRead`).
--
-- NOTE WHAT IS ABSENT: no `blkA`, no leg, no link, no driver.  The invariant is a
-- statement about ONE BlockFetch channel and nothing else.
------------------------------------------------------------------------

-- the two configurations of a channel whose server is streaming
ChanStr : CopyPhase → NS.BFcPos → Set
ChanStr ph ca = (FullMsg ph MsgStartBatch × CliBusyA ca)
              ⊎ (CellQuiet ph × CliStrA ca)

-- *** THE PER-HOP CHANNEL INVARIANT. ***
record ChanInv (sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos) : Set where
  constructor mkChan
  field
    cvStr : SrvStr sa → ChanStr ph ca
    cvBlk : BlkFull ph → SrvStr sa
    cvPre : SrvPre sa → CliBusyA ca
    cvQui : SrvPre sa → CellPreQ ph
    cvReq : ReqFull ph → CliBusyA ca
    -- *** (T10) THE SIXTH CLAUSE — `cvBlk`'s TWIN AT THE OTHER RESPONDER MESSAGE.
    -- ***  An unread `MsgStartBatch` puts its server in the streaming region: the
    -- server ENTERS that region by writing exactly this message (`bfSnxt bsWsb
    -- (input …) ≡ just bsStream`, `NodeSpecs:610-613`) and can only leave it by a
    -- wire-send, which needs the cell EMPTY — and the cell is holding this very
    -- message.  It exists for `cvBd`: without it the source of the client's
    -- `MsgStartBatch` READ (`chan-cliRead`'s `crSB` arm) has no server fact at all,
    -- and the phantom state `(bsIdle , full MsgStartBatch , bcBusy)` — which the
    -- five original clauses ADMIT — would make the seventh clause FALSE at the
    -- target.  That is the machine-checked reason this pair lands together
    cvSb  : FullMsg ph MsgStartBatch → SrvStr sa
    -- *** (T10) THE SEVENTH — THE CLIENT-ANTECEDENT CLAUSE, and the one the `cp4`
    -- arm turns on. ***  A client that has read its `MsgStartBatch` and not yet its
    -- `MsgBatchDone` faces a server that is still streaming, or a `MsgBatchDone`
    -- that is in the cell unread.  It is what the `cp4` leaf needs and what NO
    -- landed clause supplies: `cvStr`/`cvBlk`/`cvPre`/`cvQui`/`cvReq` are all
    -- SERVER- or CELL-antecedent, so at a client in the streaming region with an
    -- `sa` outside `SrvStr` they say nothing at all.
    --
    -- *** THIS IS NOT S-a, AND THE DIFFERENCE IS THE ONE T9 MEASURED. ***  S-a was
    -- refuted in its specified place because the state it had to exclude —
    -- `(bsIdle , empty , bcIdle)` — IS `chanInv-init`.  This clause is VACUOUS at
    -- `chanInv-init` (`CliStrA bcIdle = ⊥`), which is exactly why it can be a
    -- hop-generic field where S-a could not.  Its establishing step is the SERVER's
    -- own `MsgBatchDone` wire-send (`chan-srvSend`'s `ssBD` arm), which fills the
    -- cell with the message the second disjunct names
    cvBd  : CliStrA ca → SrvStr sa ⊎ FullMsg ph MsgBatchDone
open ChanInv public

-- *** THE (T10) PAIR's FALSIFICATION, arity-preserving, RED, reverted. ***
--
-- (F86  THE SIXTH CLAUSE IS NOT A RESTATEMENT OF `cvBlk`)  `chan-cliRead`'s `crSB`
--      arm supplies the target's `cvBd` from `cvBlk` — the LANDED cell-antecedent
--      clause — instead of from the new `cvSb`.  Both have the same consequent
--      (`SrvStr sa`) and the same arity, so the mutation is invisible to a reader
--      who has not checked WHICH message the cell is holding.
--      *** RED ***: `LiveChanInv.agda:1182.54-58: [UnequalTerms] MsgStartBatch !=
--      MsgBlock blkA of type MessageBlockFetch … when checking that the expression
--      refl has type full (t , md , ln , blockFetch MsgStartBatch) ≡ full (t , md ,
--      ln , blockFetch (MsgBlock blkA))`, EXIT=42.  **The error EXHIBITS the cell's
--      own payload**: at the step that puts the client INTO the streaming region the
--      cell holds a `MsgStartBatch`, so no landed clause reaches the server, and
--      that is exactly the gap `cvSb` fills.  Re-aiming note: F86 dies if `cvBlk`'s
--      antecedent is ever widened past `BlkFull`.
--
-- (T10) a source clause whose SERVER is outside the streaming region can only be
-- offering `cvBd`'s second disjunct — the shape the six server-api arms consume
-- (the first disjunct's type REDUCES to `⊥` at those positions, which is what makes
-- one absurd pattern serve all six)
bdOnly : {ph : CopyPhase} → ⊥ ⊎ FullMsg ph MsgBatchDone → FullMsg ph MsgBatchDone
bdOnly (inj₁ ())
bdOnly (inj₂ h) = h

-- (T10) … and a DRAINING cell holds no unread `MsgBatchDone`, so a source clause
-- there yields its SERVER-side disjunct outright (the drain arm's own shape)
bdDrainOnly : {x : Payload} {q : NS.BFsPos}
            → SrvStr q ⊎ FullMsg (draining x) MsgBatchDone → SrvStr q
bdDrainOnly (inj₁ h) = h
bdDrainOnly (inj₂ (_ , _ , _ , ()))

-- (T10) … and an EMPTY one holds none either (the two io-FILL arms whose target
-- server is outside the region: the source is empty and the source server is too)
bdEmpty-⊥ : FullMsg empty MsgBatchDone → ⊥
bdEmpty-⊥ (_ , _ , _ , ())

-- (T10) … and a cell holding some OTHER BlockFetch message holds no `MsgBatchDone`.
-- Stated at the MESSAGE (with its distinctness as the caller's `λ ()`) rather than
-- as one absurd pattern per site, because an inline pattern lambda at these two use
-- sites leaves the payload's three components as unsolved metas — measured, and the
-- reason this helper is named at all
bdMsg-⊥ : {t : Time} {md : Mode} {ln : Length} {mb : MessageBlockFetch}
        → (MsgBatchDone ≡ mb → ⊥)
        → FullMsg (full (t , md , ln , blockFetch mb)) MsgBatchDone → ⊥
bdMsg-⊥ ne (_ , _ , _ , refl) = ne refl

-- BASE — an idle server, an empty cell and an idle client: every antecedent is
-- uninhabited (this is the channel's state at `SysDecode.initial`).
-- (T10) … and so are the two new ones: `empty` is no unread `MsgStartBatch`, and an
-- idle client is not in the streaming region — the check that says this pair could
-- be a `ChanInv` field where S-a could not
chanInv-init : ChanInv NS.bsIdle empty NS.bcIdle
chanInv-init =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ ())
         (λ ()) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())

-- FRAME — the invariant reads exactly three components, so a step fixing all
-- three carries it (the `pipeInv⁺-frame` shape at the hop)
chan-frame : (sa sa′ : NS.BFsPos) (ph ph′ : CopyPhase) (ca ca′ : NS.BFcPos)
           → sa ≡ sa′ → ph ≡ ph′ → ca ≡ ca′
           → ChanInv sa ph ca → ChanInv sa′ ph′ ca′
chan-frame sa .sa ph .ph ca .ca refl refl refl iv = iv

------------------------------------------------------------------------
-- §4  THE SIX STEP ADJACENCIES — FAITHFUL transcriptions of the two tables.
--
-- *** KEEP IN SYNC — `NodeSpecs.bfSnxt` (`:586-640`) and `bfCnxt` (`:516-557`).
-- An OMITTED row here makes §5's preservation VACUOUSLY true for a step that
-- really exists, so the two lists below are exhaustive by construction and each
-- row is annotated with its source line.  If either table gains a row, the
-- matching adjacency MUST gain a constructor. ***
--
--   `bfSnxt`, twelve rows:
--     bsIdle    + output + MsgRequestRange r  → bsAreq r   :588-591  srReq
--     bsIdle    + output + MsgClientDone      → bsDdone    :592-595  srCD
--     bsAreq r  + apiBF reqBFRange            → bsBusy     :596-600  saReq
--     bsDdone   + done                        → bsTerm     :601-603  saDone
--     bsBusy    + apiBF sendBFStartBatch      → bsWsb      :604-606  saSB
--     bsBusy    + apiBF sendBFNoBlocks        → bsWnb      :607-609  saNB
--     bsWsb     + input  + MsgStartBatch      → bsStream   :610-615  ssSB
--     bsWnb     + input  + MsgNoBlocks        → bsIdle     :616-621  ssNB
--     bsStream  + apiBF sendBFBlock b         → bsWblk b   :622-624  saBlk
--     bsStream  + apiBF sendBFBatchDone       → bsWbd      :625-627  saBD
--     bsWblk b  + input  + MsgBlock b         → bsStream   :628-633  ssBlk
--     bsWbd     + input  + MsgBatchDone       → bsIdle     :634-639  ssBD
--
--   `bfCnxt`, nine rows:
--     bcIdle    + apiBF sendBFRequestRange r  → bcWrr r    :518-520  caReq
--     bcIdle    + apiBF sendBFClientDone      → bcWcd      :521-523  caDone
--     bcWrr r   + input  + MsgRequestRange r  → bcBusy     :524-529  csReq
--     bcWcd     + input  + MsgClientDone      → bcTerm     :530-535  csCD
--     bcBusy    + output + MsgStartBatch      → bcStream   :536-539  crSB
--     bcBusy    + output + MsgNoBlocks        → bcIdle     :540-543  crNB
--     bcStream  + output + MsgBlock b         → bcAblk b   :544-547  crBlk
--     bcStream  + output + MsgBatchDone       → bcIdle     :548-551  crBD
--     bcAblk b  + apiBF recvBFBlock b         → bcStream   :552-556  caRecv
--
-- The wire-SEND rows are `≟`-gated on an exact payload tuple, so the `ss*`/`cs*`
-- constructors carry the exact payload; the wire-READ rows match the message
-- only, so the `sr*`/`cr*` constructors are lenient in `(time , mode , length)`.
--
-- *** AND ONE MORE DEVIATION, TO PRESERVE (named at the whole-branch final review,
-- I-4). ***  Two of the api rows are `≟`-gated on the SOURCE's own payload in the
-- table — `bfSnxt` row 3 gates the `reqBFRange` argument against the range the
-- source `bsAreq r` holds, and `bfCnxt` row 9 gates the `recvBFBlock` argument
-- against the block the source `bcAblk b` holds — and the adjacencies below DROP
-- that pin: `saReq r` and `caRecv b` bind the SOURCE's value (so the source
-- position is pinned) but say nothing about the api event's own argument.  The
-- direction is safe, being a HYPOTHESIS-position weakening: the adjacency holds of
-- MORE steps, so §5's preservation lemmas prove more, and §4b's seven total row
-- producers still catch any OMITTED row (the vacuity channel this block guards).
-- A re-sync must preserve the omission, not "restore" the pins — restoring them
-- would strengthen the adjacency and break every producer.
------------------------------------------------------------------------

-- the server's non-io adjacencies (its four api rows and its `done` row): the
-- steps at which the server moves and the CELL DOES NOT
data SrvApiAdj : NS.BFsPos → NS.BFsPos → Set where
  saReq  : (r : ChainRange) → SrvApiAdj (NS.bsAreq r) NS.bsBusy
  saSB   : SrvApiAdj NS.bsBusy NS.bsWsb
  saNB   : SrvApiAdj NS.bsBusy NS.bsWnb
  saBlk  : (b : Block₃) → SrvApiAdj NS.bsStream (NS.bsWblk b)
  saBD   : SrvApiAdj NS.bsStream NS.bsWbd
  saDone : SrvApiAdj NS.bsDdone NS.bsTerm

-- the client's non-io adjacencies (its three api rows)
data CliApiAdj : NS.BFcPos → NS.BFcPos → Set where
  caReq  : (r : ChainRange) → CliApiAdj NS.bcIdle (NS.bcWrr r)
  caDone : CliApiAdj NS.bcIdle NS.bcWcd
  caRecv : (b : Block₃) → CliApiAdj (NS.bcAblk b) NS.bcStream

-- the server's WIRE-SEND adjacencies: the cell goes `empty → full x` and the
-- payload is pinned by the row's own `≟` gate
data SrvSendAdj : NS.BFsPos → Payload → NS.BFsPos → Set where
  ssSB  : SrvSendAdj NS.bsWsb sbPayload NS.bsStream
  ssNB  : SrvSendAdj NS.bsWnb nbPayload NS.bsIdle
  ssBlk : (b : Block₃) → SrvSendAdj (NS.bsWblk b) (blkPayload b) NS.bsStream
  ssBD  : SrvSendAdj NS.bsWbd bdPayload NS.bsIdle

-- the client's WIRE-SEND adjacencies
data CliSendAdj : NS.BFcPos → Payload → NS.BFcPos → Set where
  csReq : (r : ChainRange) → CliSendAdj (NS.bcWrr r) (rrPayload r) NS.bcBusy
  csCD  : CliSendAdj NS.bcWcd cdPayload NS.bcTerm

-- the server's WIRE-READ adjacencies: the cell goes `full x → draining x` and
-- the row is lenient in the tuple's first three components
data SrvReadAdj : NS.BFsPos → Payload → NS.BFsPos → Set where
  srReq : {t : Time} {md : Mode} {ln : Length} (r : ChainRange)
        → SrvReadAdj NS.bsIdle (t , md , ln , blockFetch (MsgRequestRange r)) (NS.bsAreq r)
  srCD  : {t : Time} {md : Mode} {ln : Length}
        → SrvReadAdj NS.bsIdle (t , md , ln , blockFetch MsgClientDone) NS.bsDdone

-- the client's WIRE-READ adjacencies (the reader's `output` — the ONLY way a
-- cell leaves `full`, and it always advances the reader)
data CliReadAdj : NS.BFcPos → Payload → NS.BFcPos → Set where
  crSB  : {t : Time} {md : Mode} {ln : Length}
        → CliReadAdj NS.bcBusy (t , md , ln , blockFetch MsgStartBatch) NS.bcStream
  crNB  : {t : Time} {md : Mode} {ln : Length}
        → CliReadAdj NS.bcBusy (t , md , ln , blockFetch MsgNoBlocks) NS.bcIdle
  crBlk : {t : Time} {md : Mode} {ln : Length} (b : Block₃)
        → CliReadAdj NS.bcStream (t , md , ln , blockFetch (MsgBlock b)) (NS.bcAblk b)
  crBD  : {t : Time} {md : Mode} {ln : Length}
        → CliReadAdj NS.bcStream (t , md , ln , blockFetch MsgBatchDone) NS.bcIdle

------------------------------------------------------------------------
-- §4b  *** THE ADJACENCY PRODUCERS — WHERE §4 STOPS BEING A TRANSCRIPTION. ***
--
-- §4's six datatypes are HAND transcriptions of the two tables, and Agda cannot
-- check a transcription: an OMITTED row makes §5's preservation VACUOUSLY true
-- for a step that really exists (Task-2 report Concern 1; Task-2 review §1).
-- The seven producers below are what closes that hole.  Each takes a FIRED TABLE
-- ROW — `bfSnxt`/`bfCnxt` applied at the peer's OWN key, yielding `just` — and
-- returns the matching §4 constructor by a dispatch that is TOTAL on the
-- position datatype and, wherever the table splits further, on `ApiBFTag` or on
-- `Messages`/`MessageBlockFetch`.  *** TOTALITY IS THE CHECK: *** a row present
-- in the table but ABSENT from the adjacency leaves a `just` with no constructor
-- to return, and the clause simply cannot be written.  Every real step therefore
-- produces its row, and §5 is no longer conditional on a reading of the source.
--
-- WHAT THIS STILL DOES NOT CATCH, stated so it is not over-read: a SPURIOUS
-- constructor (one with no table row) is invisible here, because these functions
-- only ever CONSTRUCT adjacencies.  The review's independent re-derivation
-- (21 / 21, zero spurious) is the record, and the KEEP-IN-SYNC block above is
-- the standing defence.  The falsification of record for this section is a wrong
-- row CONSTRUCTOR: swapping `ssNB` for `ssBD` in `srvSendRow` must go red.
--
-- AND THE SECOND BLIND SPOT (T2b review M-3), which is CROSS-FAMILY: the seven
-- producers' signatures FIX the event families they cover — `{input, output,
-- apiBF, done}` on the server side, `{input, output, apiBF}` on the client's — so
-- totality is per-family.  A BlockFetch row added to `bfSnxt`/`bfCnxt` on a NEW
-- family (an `apiKA` row, say, or a client `done` row) would be invisible to all
-- seven and would SILENTLY RESTORE the vacuity hole for that step: the lift's
-- frame arm would absorb it as "nothing moved" while the peer really moved.  If
-- either table gains a row on a family not listed above, a producer for THAT
-- family must be added here, not just a constructor to §4.
--
-- THE KEYS ARE PINNED to the peer's own `(i , d)`.  A peer's table returns
-- `nothing` at any other key (the `l′ ≟ l | d′ ≟ d` gate of every row), so no
-- step at a foreign key exists to produce — and §6b's leg-level lift reads a
-- foreign-key step through the FRAME arm, never through an adjacency.
------------------------------------------------------------------------

-- `just` is injective: the fired row NAMES the successor position
just-inj : {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- (the two abstract offer tables `Tbfs`/`Tbfc` are IMPORTED from `SysIoLink6`
-- (T2 review M-1) — `SysIoLink5:2780-2781`/`:2324-2325` are the copies the frozen
-- io decodes use, and `absBFs i d q` / `absBFc i d q` ARE `tableSpec` at them by
-- definition, so no local re-spelling and no third KEEP-IN-SYNC surface)

-- (1) THE SERVER'S FOUR WIRE-SEND ROWS (`input` at its own key).  The four
-- informative positions are exactly the four `≟`-gated rows; the six others have
-- no `input` clause at all, so the table falls to its catch-all `nothing`.
srvSendRow : (i : Link) (d : Dir) (sa : NS.BFsPos) (x : Payload) (sa′ : NS.BFsPos)
           → NS.bfSnxt i d sa (Payload , input i d N2N_BlockFetch) x ≡ just sa′
           → SrvSendAdj sa x sa′
srvSendRow i d NS.bsIdle     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d (NS.bsAreq r) x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d NS.bsBusy     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d NS.bsDdone    x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d NS.bsStream   x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d NS.bsTerm     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvSendRow i d NS.bsWsb      x sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj NS.bsWsb sbPayload z) (just-inj eq) ssSB
srvSendRow i d NS.bsWnb      x sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj NS.bsWnb nbPayload z) (just-inj eq) ssNB
srvSendRow i d (NS.bsWblk b) x sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj (NS.bsWblk b) (blkPayload b) z) (just-inj eq)
                (ssBlk b)
srvSendRow i d NS.bsWbd      x sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvSendAdj NS.bsWbd bdPayload z) (just-inj eq) ssBD

-- (2) THE SERVER'S TWO WIRE-READ ROWS (`output` at its own key).  These rows
-- pattern-match the MESSAGE and leave `(time , mode , length)` free, so the
-- dispatch is on `Messages`/`MessageBlockFetch` as well as on the position — and
-- the resulting constructors are lenient in the same three components.
srvReadRow : (i : Link) (d : Dir) (sa : NS.BFsPos) (x : Payload) (sa′ : NS.BFsPos)
           → NS.bfSnxt i d sa (Payload , output i d N2N_BlockFetch) x ≡ just sa′
           → SrvReadAdj sa x sa′
srvReadRow i d (NS.bsAreq r) x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsBusy     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsDdone    x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsWsb      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsStream   x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsWnb      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d (NS.bsWblk b) x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsWbd      x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsTerm     x sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , keepAlive m)    sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , chainSync m)    sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , txSubmission m) sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , leiosNotify m)  sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , leiosFetch m)   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch MsgStartBatch)  sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch MsgNoBlocks)    sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch (MsgBlock b))   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch MsgBatchDone)   sa′ eq = ⊥-elim (nothing-absurd eq)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch (MsgRequestRange r)) sa′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvReadAdj NS.bsIdle (t , md , ln , blockFetch (MsgRequestRange r)) z)
            (just-inj eq) (srReq r)
srvReadRow i d NS.bsIdle (t , md , ln , blockFetch MsgClientDone) sa′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvReadAdj NS.bsIdle (t , md , ln , blockFetch MsgClientDone) z)
            (just-inj eq) srCD

-- (3) THE SERVER'S FIVE api ROWS.  The three positions that offer an api need
-- the `ApiBFTag` dispatch as well (the table matches the tag as a CONSTRUCTOR,
-- so a tag variable leaves it stuck); the seven other positions have no `apiBF`
-- clause at any tag.
srvApiRow : (i : Link) (d : Dir) (sa : NS.BFsPos) (m : ApiBFTag) (v : ApiBFCar m)
            (sa′ : NS.BFsPos)
          → NS.bfSnxt i d sa (ApiBFCar m , apiBF i d m) v ≡ just sa′
          → SrvApiAdj sa sa′
srvApiRow i d NS.bsIdle     m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsDdone    m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsWsb      m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsWnb      m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsWblk b) m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsWbd      m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsTerm     m v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFRequestRange v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFClientDone   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFStartBatch   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFNoBlocks     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFBlock        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) sendBFBatchDone    v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) recvBFBlock        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d (NS.bsAreq r) reqBFRange         v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with v ≟ r
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → SrvApiAdj (NS.bsAreq r) z) (just-inj eq) (saReq r)
srvApiRow i d NS.bsBusy sendBFRequestRange v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy sendBFClientDone   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy sendBFBlock        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy sendBFBatchDone    v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy recvBFBlock        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy reqBFRange         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsBusy sendBFStartBatch   v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.bsBusy z) (just-inj eq) saSB
srvApiRow i d NS.bsBusy sendBFNoBlocks     v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.bsBusy z) (just-inj eq) saNB
srvApiRow i d NS.bsStream sendBFRequestRange v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream sendBFClientDone   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream sendBFStartBatch   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream sendBFNoBlocks     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream recvBFBlock        v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream reqBFRange         v sa′ eq = ⊥-elim (nothing-absurd eq)
srvApiRow i d NS.bsStream sendBFBlock        v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.bsStream z) (just-inj eq) (saBlk v)
srvApiRow i d NS.bsStream sendBFBatchDone    v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.bsStream z) (just-inj eq) saBD

-- (4) THE SERVER'S `done` ROW — the twelfth row of `bfSnxt`, on the only event
-- family neither io nor api (`done`, whose carrier is the non-polymorphic `⊤`)
srvDoneRow : (i : Link) (d : Dir) (sa : NS.BFsPos) (v : U0.⊤) (sa′ : NS.BFsPos)
           → NS.bfSnxt i d sa (U0.⊤ , done i d N2N_BlockFetch) v ≡ just sa′
           → SrvApiAdj sa sa′
srvDoneRow i d NS.bsIdle     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d (NS.bsAreq r) v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsBusy     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsWsb      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsStream   v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsWnb      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d (NS.bsWblk b) v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsWbd      v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsTerm     v sa′ eq = ⊥-elim (nothing-absurd eq)
srvDoneRow i d NS.bsDdone    v sa′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → SrvApiAdj NS.bsDdone z) (just-inj eq) saDone

-- (5) THE CLIENT'S TWO WIRE-SEND ROWS (`input` at its own key)
cliSendRow : (i : Link) (d : Dir) (ca : NS.BFcPos) (x : Payload) (ca′ : NS.BFcPos)
           → NS.bfCnxt i d ca (Payload , input i d N2N_BlockFetch) x ≡ just ca′
           → CliSendAdj ca x ca′
cliSendRow i d NS.bcIdle     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow i d NS.bcBusy     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow i d NS.bcStream   x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow i d (NS.bcAblk b) x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow i d NS.bcTerm     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliSendRow i d (NS.bcWrr r)  x ca′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliSendAdj (NS.bcWrr r) (rrPayload r) z) (just-inj eq)
                (csReq r)
cliSendRow i d NS.bcWcd      x ca′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl
      with x ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliSendAdj NS.bcWcd cdPayload z) (just-inj eq) csCD

-- (6) THE CLIENT'S FOUR WIRE-READ ROWS (`output` at its own key) — the ONLY step
-- class that empties a `full` cell.  Two positions read, and each reads two
-- message classes, so this is the `Messages` dispatch twice over.
cliReadRow : (i : Link) (d : Dir) (ca : NS.BFcPos) (x : Payload) (ca′ : NS.BFcPos)
           → NS.bfCnxt i d ca (Payload , output i d N2N_BlockFetch) x ≡ just ca′
           → CliReadAdj ca x ca′
cliReadRow i d NS.bcIdle     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d (NS.bcWrr r)  x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcWcd      x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d (NS.bcAblk b) x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcTerm     x ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , keepAlive m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , chainSync m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , txSubmission m) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , leiosNotify m)  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , leiosFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch (MsgRequestRange r)) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch (MsgBlock b))        ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch MsgBatchDone)        ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch MsgClientDone)       ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch MsgStartBatch) ca′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.bcBusy (t , md , ln , blockFetch MsgStartBatch) z)
            (just-inj eq) crSB
cliReadRow i d NS.bcBusy (t , md , ln , blockFetch MsgNoBlocks) ca′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.bcBusy (t , md , ln , blockFetch MsgNoBlocks) z)
            (just-inj eq) crNB
cliReadRow i d NS.bcStream (t , md , ln , keepAlive m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , chainSync m)    ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , txSubmission m) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , leiosNotify m)  ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , leiosFetch m)   ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch (MsgRequestRange r)) ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch MsgStartBatch)       ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch MsgNoBlocks)         ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch MsgClientDone)       ca′ eq = ⊥-elim (nothing-absurd eq)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch (MsgBlock b)) ca′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.bcStream (t , md , ln , blockFetch (MsgBlock b)) z)
            (just-inj eq) (crBlk b)
cliReadRow i d NS.bcStream (t , md , ln , blockFetch MsgBatchDone) ca′ eq
  with i ≟ i | d ≟ d
... | no ¬p    | _     = ⊥-elim (¬p refl)
... | yes refl | no ¬q = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliReadAdj NS.bcStream (t , md , ln , blockFetch MsgBatchDone) z)
            (just-inj eq) crBD

-- (7) THE CLIENT'S THREE api ROWS
cliApiRow : (i : Link) (d : Dir) (ca : NS.BFcPos) (m : ApiBFTag) (v : ApiBFCar m)
            (ca′ : NS.BFcPos)
          → NS.bfCnxt i d ca (ApiBFCar m , apiBF i d m) v ≡ just ca′
          → CliApiAdj ca ca′
cliApiRow i d (NS.bcWrr r) m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcBusy    m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcWcd     m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcStream  m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcTerm    m v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle sendBFStartBatch v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle sendBFNoBlocks   v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle sendBFBlock      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle sendBFBatchDone  v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle recvBFBlock      v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle reqBFRange       v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d NS.bcIdle sendBFRequestRange v ca′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliApiAdj NS.bcIdle z) (just-inj eq) (caReq v)
cliApiRow i d NS.bcIdle sendBFClientDone   v ca′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl =
      subst (λ z → CliApiAdj NS.bcIdle z) (just-inj eq) caDone
cliApiRow i d (NS.bcAblk b) sendBFRequestRange v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) sendBFClientDone   v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) sendBFStartBatch   v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) sendBFNoBlocks     v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) sendBFBlock        v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) sendBFBatchDone    v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) reqBFRange         v ca′ eq = ⊥-elim (nothing-absurd eq)
cliApiRow i d (NS.bcAblk b) recvBFBlock        v ca′ eq with i ≟ i | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with v ≟ b
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes refl =
          subst (λ z → CliApiAdj (NS.bcAblk b) z) (just-inj eq) (caRecv b)

------------------------------------------------------------------------
-- §4c  THE STEP-LEVEL FORM: an adjacency off a REAL abstract peer STEP.
--
-- `SysStep.absBFc i d q` is `tableSpec (Tbfc i d) (coarsenBFc q)` and
-- `absBFs i d q` is `tableSpec (Tbfs i d) (coarsenBFs q)`, both by DEFINITION,
-- so the seven bridges below apply at the system's own peers with no glue: a
-- visible step of the peer fires exactly one table edge (`tableSpec-ev-inv`) and
-- §4b turns that edge into its adjacency.  This is the sense in which "every
-- real step produces its row" is a THEOREM rather than a reading.
------------------------------------------------------------------------

-- one fired table edge, mapped to whatever the row producer returns
rowAdj : {Pos : Set} (T : NS.Table Pos) (q : Pos) {X : Set} (e : Net_Api Payload X)
         (a : X) {M : NetProc} (R : Pos → Set)
       → ((q′ : Pos) → NS.Table.nxt T q (X , e) a ≡ just q′ → R q′)
       → NS.tableSpec T q ─[ ev (evl (evLabel X e a)) ]─► M
       → Σ[ q′ ∈ Pos ] (R q′ × (M ≡ NS.tableSpec T q′))
rowAdj T q e a R prod st with tableSpec-ev-inv T q st
... | q′ , ceq , meq = q′ , prod q′ ceq , meq

-- the server's fired WIRE-SEND row
srvSend-of : (i : Link) (d : Dir) (sa : NS.BFsPos) (x : Payload) {M : NetProc}
           → NS.tableSpec (Tbfs i d) sa
             ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch) x)) ]─► M
           → Σ[ sa′ ∈ NS.BFsPos ]
               (SrvSendAdj sa x sa′ × (M ≡ NS.tableSpec (Tbfs i d) sa′))
srvSend-of i d sa x =
  rowAdj (Tbfs i d) sa (input i d N2N_BlockFetch) x (SrvSendAdj sa x)
         (srvSendRow i d sa x)

-- … its fired WIRE-READ row
srvRead-of : (i : Link) (d : Dir) (sa : NS.BFsPos) (x : Payload) {M : NetProc}
           → NS.tableSpec (Tbfs i d) sa
             ─[ ev (evl (evLabel Payload (output i d N2N_BlockFetch) x)) ]─► M
           → Σ[ sa′ ∈ NS.BFsPos ]
               (SrvReadAdj sa x sa′ × (M ≡ NS.tableSpec (Tbfs i d) sa′))
srvRead-of i d sa x =
  rowAdj (Tbfs i d) sa (output i d N2N_BlockFetch) x (SrvReadAdj sa x)
         (srvReadRow i d sa x)

-- … its fired api row
srvApi-of : (i : Link) (d : Dir) (sa : NS.BFsPos) (m : ApiBFTag) (v : ApiBFCar m)
            {M : NetProc}
          → NS.tableSpec (Tbfs i d) sa
            ─[ ev (evl (evLabel (ApiBFCar m) (apiBF i d m) v)) ]─► M
          → Σ[ sa′ ∈ NS.BFsPos ]
              (SrvApiAdj sa sa′ × (M ≡ NS.tableSpec (Tbfs i d) sa′))
srvApi-of i d sa m v =
  rowAdj (Tbfs i d) sa (apiBF i d m) v (SrvApiAdj sa) (srvApiRow i d sa m v)

-- … and its fired `done` row
srvDone-of : (i : Link) (d : Dir) (sa : NS.BFsPos) (v : U0.⊤) {M : NetProc}
           → NS.tableSpec (Tbfs i d) sa
             ─[ ev (evl (evLabel U0.⊤ (done i d N2N_BlockFetch) v)) ]─► M
           → Σ[ sa′ ∈ NS.BFsPos ]
               (SrvApiAdj sa sa′ × (M ≡ NS.tableSpec (Tbfs i d) sa′))
srvDone-of i d sa v =
  rowAdj (Tbfs i d) sa (done i d N2N_BlockFetch) v (SrvApiAdj sa)
         (srvDoneRow i d sa v)

-- the client's fired WIRE-SEND row
cliSend-of : (i : Link) (d : Dir) (ca : NS.BFcPos) (x : Payload) {M : NetProc}
           → NS.tableSpec (Tbfc i d) ca
             ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch) x)) ]─► M
           → Σ[ ca′ ∈ NS.BFcPos ]
               (CliSendAdj ca x ca′ × (M ≡ NS.tableSpec (Tbfc i d) ca′))
cliSend-of i d ca x =
  rowAdj (Tbfc i d) ca (input i d N2N_BlockFetch) x (CliSendAdj ca x)
         (cliSendRow i d ca x)

-- … its fired WIRE-READ row (the cell's delivery)
cliRead-of : (i : Link) (d : Dir) (ca : NS.BFcPos) (x : Payload) {M : NetProc}
           → NS.tableSpec (Tbfc i d) ca
             ─[ ev (evl (evLabel Payload (output i d N2N_BlockFetch) x)) ]─► M
           → Σ[ ca′ ∈ NS.BFcPos ]
               (CliReadAdj ca x ca′ × (M ≡ NS.tableSpec (Tbfc i d) ca′))
cliRead-of i d ca x =
  rowAdj (Tbfc i d) ca (output i d N2N_BlockFetch) x (CliReadAdj ca x)
         (cliReadRow i d ca x)

-- … and its fired api row
cliApi-of : (i : Link) (d : Dir) (ca : NS.BFcPos) (m : ApiBFTag) (v : ApiBFCar m)
            {M : NetProc}
          → NS.tableSpec (Tbfc i d) ca
            ─[ ev (evl (evLabel (ApiBFCar m) (apiBF i d m) v)) ]─► M
          → Σ[ ca′ ∈ NS.BFcPos ]
              (CliApiAdj ca ca′ × (M ≡ NS.tableSpec (Tbfc i d) ca′))
cliApi-of i d ca m v =
  rowAdj (Tbfc i d) ca (apiBF i d m) v (CliApiAdj ca) (cliApiRow i d ca m v)

------------------------------------------------------------------------
-- §5  *** THE PRESERVATION CALCULUS. ***  One lemma per step class.
--
-- The successor phase is written LITERALLY in each conclusion (`full x`,
-- `draining x`, `empty`) rather than through an equation, because the medium's
-- banked key lemmas produce exactly that: `PipeMedKey.cell-in-key` returns
-- `(ph ≡ empty) × (Mk ≡ decCopy … (full x))` and `cell-out-key` returns
-- `(ph ≡ full x) × (Mk ≡ decCopy … (draining x))`.
------------------------------------------------------------------------

-- a channel whose client is at a NON-region position has no `ChanStr` (the
-- refutation the two client-send arms and the `bcIdle` api arms consume)
chanStr-⊥ : (ph : CopyPhase) (ca : NS.BFcPos)
          → (CliBusyA ca → ⊥) → (CliStrA ca → ⊥) → ChanStr ph ca → ⊥
chanStr-⊥ ph ca ¬b ¬s (inj₁ (_ , hb)) = ¬b hb
chanStr-⊥ ph ca ¬b ¬s (inj₂ (_ , hs)) = ¬s hs

-- an EMPTY cell's `ChanStr` is the quiet arm, so its client has advanced
chanStr-empty⇒str : (ca : NS.BFcPos) → ChanStr empty ca → CliStrA ca
chanStr-empty⇒str ca (inj₁ ((_ , _ , _ , ()) , _))
chanStr-empty⇒str ca (inj₂ (_ , hs)) = hs

-- … and so is a DRAINING cell's
chanStr-drain⇒str : (x : Payload) (ca : NS.BFcPos) → ChanStr (draining x) ca → CliStrA ca
chanStr-drain⇒str x ca (inj₁ ((_ , _ , _ , ()) , _))
chanStr-drain⇒str x ca (inj₂ (_ , hs)) = hs

-- the holding client's `ChanStr` moves to the delivery position (the api
-- `recvBFBlock` arm)
chanStr-hold⇒stream : (ph : CopyPhase) (b : Block₃)
                    → ChanStr ph (NS.bcAblk b) → ChanStr ph NS.bcStream
chanStr-hold⇒stream ph b (inj₁ (_ , ()))
chanStr-hold⇒stream ph b (inj₂ (hq , _)) = inj₂ (hq , tt)

-- (1) THE SERVER'S api/`done` STEPS — the cell and the client are fixed
chan-srvApi : (sa sa′ : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
            → SrvApiAdj sa sa′ → ChanInv sa ph ca → ChanInv sa′ ph ca
-- (T10) the two new clauses across this class: the THREE arms whose target is
-- outside `SrvStr` transport the source's own — `cvSb`'s consequent is `⊥` at both
-- ends and `cvBd`'s first disjunct with it, so `bdOnly` carries the cell fact — and
-- the two `bsStream` arms ESTABLISH both outright, their target being in the region
chan-srvApi .(NS.bsAreq r) .NS.bsBusy ph ca (saReq r) iv =
  mkChan (λ ()) (λ hb → cvBlk iv hb) (λ _ → cvPre iv tt) (λ _ → cvQui iv tt) (cvReq iv)
         (λ h → cvSb iv h) (λ h → inj₂ (bdOnly (cvBd iv h)))
chan-srvApi .NS.bsBusy .NS.bsWsb ph ca saSB iv =
  mkChan (λ ()) (λ hb → cvBlk iv hb) (λ _ → cvPre iv tt) (λ _ → cvQui iv tt) (cvReq iv)
         (λ h → cvSb iv h) (λ h → inj₂ (bdOnly (cvBd iv h)))
chan-srvApi .NS.bsBusy .NS.bsWnb ph ca saNB iv =
  mkChan (λ ()) (λ hb → cvBlk iv hb) (λ _ → cvPre iv tt) (λ _ → cvQui iv tt) (cvReq iv)
         (λ h → cvSb iv h) (λ h → inj₂ (bdOnly (cvBd iv h)))
chan-srvApi .NS.bsStream .(NS.bsWblk b) ph ca (saBlk b) iv =
  mkChan (λ _ → cvStr iv tt) (λ _ → tt) (λ ()) (λ ()) (cvReq iv)
         (λ _ → tt) (λ _ → inj₁ tt)
chan-srvApi .NS.bsStream .NS.bsWbd ph ca saBD iv =
  mkChan (λ _ → cvStr iv tt) (λ _ → tt) (λ ()) (λ ()) (cvReq iv)
         (λ _ → tt) (λ _ → inj₁ tt)
chan-srvApi .NS.bsDdone .NS.bsTerm ph ca saDone iv =
  mkChan (λ ()) (λ hb → cvBlk iv hb) (λ ()) (λ ()) (cvReq iv)
         (λ h → cvSb iv h) (λ h → inj₂ (bdOnly (cvBd iv h)))

-- (2) THE CLIENT'S api STEPS — the cell and the server are fixed.  The two
-- `bcIdle` rows are REFUTED from the source clauses (an idle client is in
-- neither region), and the delivery row keeps the quiet arm.
chan-cliApi : (sa : NS.BFsPos) (ph : CopyPhase) (ca ca′ : NS.BFcPos)
            → CliApiAdj ca ca′ → ChanInv sa ph ca → ChanInv sa ph ca′
-- (T10) the server and the cell are fixed, so `cvSb` transports UNCHANGED at all
-- three; `cvBd`'s two `bcIdle` targets are outside the streaming region and its
-- delivery row moves the client INSIDE it from the other member of the same region,
-- so the source answers at `tt`
chan-cliApi sa ph .NS.bcIdle .(NS.bcWrr r) (caReq r) iv =
  mkChan (λ h → ⊥-elim (chanStr-⊥ ph NS.bcIdle (λ ()) (λ ()) (cvStr iv h)))
         (cvBlk iv) (λ h → cvPre iv h) (cvQui iv) (λ h → cvReq iv h)
         (cvSb iv) (λ ())
chan-cliApi sa ph .NS.bcIdle .NS.bcWcd caDone iv =
  mkChan (λ h → ⊥-elim (chanStr-⊥ ph NS.bcIdle (λ ()) (λ ()) (cvStr iv h)))
         (cvBlk iv) (λ h → cvPre iv h) (cvQui iv) (λ h → cvReq iv h)
         (cvSb iv) (λ ())
chan-cliApi sa ph .(NS.bcAblk b) .NS.bcStream (caRecv b) iv =
  mkChan (λ h → chanStr-hold⇒stream ph b (cvStr iv h))
         (cvBlk iv) (λ h → cvPre iv h) (cvQui iv) (λ h → cvReq iv h)
         (cvSb iv) (λ _ → cvBd iv tt)

-- (3) *** THE io FILL BY THE SERVER — CellRdy's HARD ARM. ***  The cell goes
-- `empty → full x` and the client does not move, so the successor's `cvStr` must
-- ESTABLISH the reader's position from the SOURCE state.  Both arms close as
-- pure applications: the `MsgStartBatch` fill reads it off `cvPre` (the server
-- was in its pre region), and the block fill reads it off `cvStr` at the EMPTY
-- cell (the crux fact: an empty cell means the previous payload was consumed, so
-- the client has advanced).  This is the arm the Task-1 report priced as
-- "NOT free" and the review's I-1 identified as the fill site's own material.
chan-srvSend : (sa sa′ : NS.BFsPos) (x : Payload) (ca : NS.BFcPos)
             → SrvSendAdj sa x sa′ → ChanInv sa empty ca → ChanInv sa′ (full x) ca
-- *** (T10) AND THIS CLASS CARRIES THE SEVENTH CLAUSE's ESTABLISHING STEP — the
-- `ssBD` arm. ***  The server's own `MsgBatchDone` wire-send is what makes `cvBd`
-- true after the server leaves `SrvStr`: the message it leaves in the cell IS the
-- second disjunct.  The `ssNB` arm is the mirror NEGATIVE — its target is outside
-- the region and its payload is not a `MsgBatchDone`, so the arm has to REFUTE the
-- source's antecedent, which it can: at an EMPTY cell with `bsWnb` both of the
-- source's disjuncts are uninhabited
chan-srvSend .NS.bsWsb .NS.bsStream .sbPayload ca ssSB iv =
  mkChan (λ _ → inj₁ ((time₀ , FromResponder , length₀ , refl) , cvPre iv tt))
         (λ { (_ , _ , _ , _ , ()) }) (λ ()) (λ ())
         (λ { (_ , _ , _ , _ , ()) })
         (λ _ → tt) (λ _ → inj₁ tt)
chan-srvSend .NS.bsWnb .NS.bsIdle .nbPayload ca ssNB iv =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ ()) (λ ())
         (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ h → ⊥-elim (bdEmpty-⊥ (bdOnly (cvBd iv h))))
chan-srvSend .(NS.bsWblk b) .NS.bsStream .(blkPayload b) ca (ssBlk b) iv =
  mkChan (λ _ → inj₂ ( inj₂ (inj₂ (b , time₀ , FromResponder , length₀ , refl))
                     , chanStr-empty⇒str ca (cvStr iv tt) ))
         (λ _ → tt) (λ ()) (λ ())
         (λ { (_ , _ , _ , _ , ()) })
         (λ _ → tt) (λ _ → inj₁ tt)
chan-srvSend .NS.bsWbd .NS.bsIdle .bdPayload ca ssBD iv =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ ()) (λ ())
         (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ _ → inj₂ (time₀ , FromResponder , length₀ , refl))

-- (4) THE io FILL BY THE CLIENT — its request or its done message.  Both rows
-- start from a client position that is in NEITHER region, so `cvStr` is refuted
-- from the source and the request row ESTABLISHES `cvPre`/`cvReq` outright (the
-- client's own wire-send is what advances it to the awaiting position).
chan-cliSend : (sa : NS.BFsPos) (x : Payload) (ca ca′ : NS.BFcPos)
             → CliSendAdj ca x ca′ → ChanInv sa empty ca → ChanInv sa (full x) ca′
-- (T10) both rows fill the cell with an INITIATOR-side message, so the sixth
-- clause's antecedent is absurd at the target; and both LAND the client outside the
-- streaming region, so the seventh's is
chan-cliSend sa .(rrPayload r) .(NS.bcWrr r) .NS.bcBusy (csReq r) iv =
  mkChan (λ h → ⊥-elim (chanStr-⊥ empty (NS.bcWrr r) (λ ()) (λ ()) (cvStr iv h)))
         (λ { (_ , _ , _ , _ , ()) }) (λ _ → tt)
         (λ h → ⊥-elim (cvPre iv h)) (λ _ → tt)
         (λ { (_ , _ , _ , ()) }) (λ ())
chan-cliSend sa .cdPayload .NS.bcWcd .NS.bcTerm csCD iv =
  mkChan (λ h → ⊥-elim (chanStr-⊥ empty NS.bcWcd (λ ()) (λ ()) (cvStr iv h)))
         (λ { (_ , _ , _ , _ , ()) }) (λ h → cvPre iv h)
         (λ h → ⊥-elim (cvPre iv h)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())

-- (5) THE SERVER'S WIRE-READ — it takes the client's request (or its done) out
-- of the cell.  The pre region is ENTERED here, and `cvReq` is exactly the
-- clause that carries the client's position across it.
chan-srvRead : (sa sa′ : NS.BFsPos) (x : Payload) (ca : NS.BFcPos)
             → SrvReadAdj sa x sa′ → ChanInv sa (full x) ca
             → ChanInv sa′ (draining x) ca
-- (T10) both rows take an INITIATOR-side message out of the cell, so the source's
-- seventh clause has BOTH disjuncts uninhabited (`bsIdle` is outside `SrvStr`, and
-- the cell holds a request or a done) — the client is therefore outside the
-- streaming region at the source and the target's antecedent is refuted from it
chan-srvRead .NS.bsIdle .(NS.bsAreq r) _ ca (srReq {t} {md} {ln} r) iv =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) })
         (λ _ → cvReq iv (r , t , md , ln , refl))
         (λ _ → inj₂ (_ , refl)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ h → ⊥-elim (bdMsg-⊥ (λ ()) (bdOnly (cvBd iv h))))
chan-srvRead .NS.bsIdle .NS.bsDdone _ ca srCD iv =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ ())
         (λ ()) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ h → ⊥-elim (bdMsg-⊥ (λ ()) (bdOnly (cvBd iv h))))

-- (6) *** THE CLIENT'S WIRE-READ — the crux fact in action. ***  This is the
-- ONLY step that empties a `full` cell, and it ALWAYS advances the client.  The
-- `MsgStartBatch` row is what moves the channel from `cvStr`'s awaiting arm to
-- its quiet arm; the two rows that land the client OUTSIDE both regions
-- (`MsgNoBlocks`, `MsgBatchDone`) are refuted from the source `cvStr`, because
-- the cell's payload class contradicts the arm the source client's position
-- forces.
chan-cliRead : (sa : NS.BFsPos) (x : Payload) (ca ca′ : NS.BFcPos)
             → CliReadAdj ca x ca′ → ChanInv sa (full x) ca
             → ChanInv sa (draining x) ca′
-- *** (T10) AND THIS CLASS IS WHERE THE SIXTH CLAUSE EARNS ITS KEEP — the `crSB`
-- arm. ***  The step lands the client INSIDE the streaming region while the cell
-- goes `draining`, so the target's seventh clause must produce a SERVER fact out of
-- nothing but the source; `cvSb` is that fact, read off the very `MsgStartBatch`
-- the client is reading.  Without it the five original clauses admit
-- `(bsIdle , full MsgStartBatch , bcBusy)` and the target is FALSE there
chan-cliRead sa _ .NS.bcBusy .NS.bcStream (crSB {t} {md} {ln}) iv =
  mkChan (λ _ → inj₂ (inj₂ (inj₁ (_ , refl)) , tt))
         (λ { (_ , _ , _ , _ , ()) })
         (λ h → ⊥-elim (preQ-full-⊥ _ (cvQui iv h)))
         (λ _ → inj₂ (_ , refl)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ _ → inj₁ (cvSb iv (t , md , ln , refl)))
chan-cliRead sa _ .NS.bcBusy .NS.bcIdle (crNB {t} {md} {ln}) iv =
  mkChan (λ h → ⊥-elim (nbBusy-⊥ (cvStr iv h)))
         (λ { (_ , _ , _ , _ , ()) })
         (λ h → ⊥-elim (preQ-full-⊥ _ (cvQui iv h)))
         (λ _ → inj₂ (_ , refl)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())
  where
  -- an unread `MsgNoBlocks` cannot sit in the awaiting arm (it is not a
  -- `MsgStartBatch`) and its client is not in the streaming region
  nbBusy-⊥ : ChanStr (full (t , md , ln , blockFetch MsgNoBlocks)) NS.bcBusy → ⊥
  nbBusy-⊥ (inj₁ ((_ , _ , _ , ()) , _))
  nbBusy-⊥ (inj₂ (_ , ()))
-- (T10) the BLOCK row keeps the client inside the region, and its own unread block
-- gives the server fact through `cvBlk` — `cvSb`'s role at `crSB`, one message over
chan-cliRead sa _ .NS.bcStream .(NS.bcAblk b) (crBlk {t} {md} {ln} b) iv =
  mkChan (λ _ → inj₂ (inj₂ (inj₁ (_ , refl)) , tt))
         (λ { (_ , _ , _ , _ , ()) })
         (λ h → ⊥-elim (preQ-full-⊥ _ (cvQui iv h)))
         (λ _ → inj₂ (_ , refl)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) })
         (λ _ → inj₁ (cvBlk iv (b , t , md , ln , refl)))
chan-cliRead sa _ .NS.bcStream .NS.bcIdle (crBD {t} {md} {ln}) iv =
  mkChan (λ h → ⊥-elim (bdStream-⊥ (cvStr iv h)))
         (λ { (_ , _ , _ , _ , ()) })
         (λ h → ⊥-elim (preQ-full-⊥ _ (cvQui iv h)))
         (λ _ → inj₂ (_ , refl)) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())
  where
  -- an unread `MsgBatchDone` is not a block, so the quiet arm cannot hold it,
  -- and a streaming client is not awaiting
  bdStream-⊥ : ChanStr (full (t , md , ln , blockFetch MsgBatchDone)) NS.bcStream → ⊥
  bdStream-⊥ (inj₁ (_ , ()))
  bdStream-⊥ (inj₂ (inj₁ () , _))
  bdStream-⊥ (inj₂ (inj₂ (inj₁ (_ , ())) , _))
  bdStream-⊥ (inj₂ (inj₂ (inj₂ (_ , _ , _ , _ , ())) , _))

-- (7) THE MEDIUM's OWN DRAIN τ — `draining x → empty`, both peers fixed.  The
-- draining phase already carries the client's advance, so the quiet arm simply
-- changes disjunct.
chan-drain : (sa : NS.BFsPos) (x : Payload) (ca : NS.BFcPos)
           → ChanInv sa (draining x) ca → ChanInv sa empty ca
chan-drain sa x ca iv =
  mkChan (λ h → inj₂ (inj₁ refl , chanStr-drain⇒str x ca (cvStr iv h)))
         (λ { (_ , _ , _ , _ , ()) }) (cvPre iv)
         (λ _ → inj₁ refl) (λ { (_ , _ , _ , _ , ()) })
         -- (T10) the drain empties the cell, so the seventh clause's SECOND
         -- disjunct is gone at the target and the source must have been offering
         -- the first — which it was, a `draining` cell holding no unread message
         (λ { (_ , _ , _ , ()) })
         (λ h → inj₁ (bdDrainOnly (cvBd iv h)))

------------------------------------------------------------------------
-- §6  THE CONSUMERS — payload-generic, and the THREE-ARMED H19 disjunction.
--
-- H19 is the gate verdict's row at `lpUpSrv`/`lpDnSrv`
-- (`docs/superpowers/specs/2026-08-11-stable-offer-falsification.md:193`), and
-- the LegPos-24 verify report's Claim 3 is that the TWO-armed form is FALSE
-- because `draining` is reachable.  The three arms below are a TOTAL dispatch on
-- `CopyPhase`, so the shape is forced rather than chosen.
------------------------------------------------------------------------

-- the lenient `bcBusy` row: an awaiting client accepts a `MsgStartBatch` at any
-- `(time , mode , length)` (`ceqBFc03` is already stated that way — the pin in
-- `LiveChanRead.busyAcceptsSb` is its `sbPayload` instance)
busyAcceptsSbM : (i : Link) (t : Time) (md : Mode) (ln : Length)
               → CliAcceptsA i hi NS.bcBusy (t , md , ln , blockFetch MsgStartBatch)
busyAcceptsSbM i t md ln = NS.bcStream , ceqBFc03 {t} {md} {ln} i hi

-- … and the lenient `bcStream` row for a block delivery
streamAcceptsBlkM : (i : Link) (t : Time) (md : Mode) (ln : Length) (b : Block₃)
                  → CliAcceptsA i hi NS.bcStream (t , md , ln , blockFetch (MsgBlock b))
streamAcceptsBlkM i t md ln b = NS.bcAblk b , ceqBFc05 {t} {md} {ln} {b} i hi

-- *** THE PAYLOAD-GENERIC READER FACT. ***  while the server is streaming, an
-- unread cell payload is accepted by its own reader — unless the reader is
-- holding a delivered block, the escape the carried `NoTwoTokens` cuts.
chanInv⇒accepts : (i : Link) (sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                  (x : Payload)
                → ChanInv sa ph ca → SrvStr sa → ph ≡ full x
                → CliAcceptsA i hi ca x ⊎ CliHoldA ca
chanInv⇒accepts i sa ph ca x iv hstr eqf = arms (cvStr iv hstr)
  where
  -- the awaiting arm: the payload IS the StartBatch and the client is there
  armBusy : (t : Time) (md : Mode) (ln : Length)
          → ph ≡ full (t , md , ln , blockFetch MsgStartBatch) → CliBusyA ca
          → CliAcceptsA i hi ca x ⊎ CliHoldA ca
  armBusy t md ln eqs hb =
    inj₁ (subst (λ z → CliAcceptsA i hi z x) (sym (cliBusy⇒eq ca hb))
           (subst (λ z → CliAcceptsA i hi NS.bcBusy z)
                  (sym (full-inj (trans (sym eqf) eqs)))
                  (busyAcceptsSbM i t md ln)))
  -- the quiet arm at an unread BLOCK: the client is streaming (accepts) or
  -- holding (the escape)
  armBlk : (b : Block₃) (t : Time) (md : Mode) (ln : Length)
         → ph ≡ full (t , md , ln , blockFetch (MsgBlock b)) → CliStrA ca
         → CliAcceptsA i hi ca x ⊎ CliHoldA ca
  armBlk b t md ln eqs hs with cliStr⇒eq ca hs
  ... | inj₂ hold = inj₂ hold
  ... | inj₁ eqc  =
        inj₁ (subst (λ z → CliAcceptsA i hi z x) (sym eqc)
               (subst (λ z → CliAcceptsA i hi NS.bcStream z)
                      (sym (full-inj (trans (sym eqf) eqs)))
                      (streamAcceptsBlkM i t md ln b)))
  -- the quiet arm's other two disjuncts contradict `ph ≡ full x`
  armQuiet : CellQuiet ph → CliStrA ca → CliAcceptsA i hi ca x ⊎ CliHoldA ca
  armQuiet (inj₁ eqe)                     hs with trans (sym eqf) eqe
  ...                                           | ()
  armQuiet (inj₂ (inj₁ (y , eqd)))        hs with trans (sym eqf) eqd
  ...                                           | ()
  armQuiet (inj₂ (inj₂ (b , t , md , ln , eqs))) hs = armBlk b t md ln eqs hs
  arms : ChanStr ph ca → CliAcceptsA i hi ca x ⊎ CliHoldA ca
  arms (inj₁ ((t , md , ln , eqs) , hb)) = armBusy t md ln eqs hb
  arms (inj₂ (hq , hs))                  = armQuiet hq hs

-- *** THE THREE-ARMED H19 DISJUNCTION. ***  at a streaming server, the cell is
-- empty (the server's own wire-send is enabled), or holds a payload its reader
-- accepts (the reader's delivery is enabled), or is draining (the medium's own
-- τ is enabled).  The two-armed form the LegPos-24 spike stated is FALSE.
H19 : Link → CopyPhase → NS.BFcPos → Set
H19 i ph ca =
    (ph ≡ empty)
  ⊎ (Σ[ x ∈ Payload ] (ph ≡ full x) × (CliAcceptsA i hi ca x ⊎ CliHoldA ca))
  ⊎ (Σ[ x ∈ Payload ] (ph ≡ draining x))

-- H19 is a THEOREM of the channel invariant (a total dispatch on the phase)
chanInv⇒h19 : (i : Link) (sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
            → ChanInv sa ph ca → SrvStr sa → H19 i ph ca
chanInv⇒h19 i sa empty        ca iv hstr = inj₁ refl
chanInv⇒h19 i sa (full x)     ca iv hstr =
  inj₂ (inj₁ (x , refl , chanInv⇒accepts i sa (full x) ca x iv hstr refl))
chanInv⇒h19 i sa (draining x) ca iv hstr = inj₂ (inj₂ (x , refl))

-- the BLOCK instance, with the server gate DROPPED: an unread block in the cell
-- puts its own server in the streaming region (`cvBlk`), so the reader fact
-- holds with no server hypothesis at all — which is what the cell positions
-- need, since `AtPos l lpUpCell` says nothing about the server
chanInv⇒blkAccepts : (i : Link) (sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                     (b : Block₃)
                   → ChanInv sa ph ca → ph ≡ full (blkPayload b)
                   → CliAcceptsA i hi ca (blkPayload b) ⊎ CliHoldA ca
chanInv⇒blkAccepts i sa ph ca b iv eqf =
  chanInv⇒accepts i sa ph ca (blkPayload b) iv
    (cvBlk iv (b , time₀ , FromResponder , length₀ , eqf)) eqf

------------------------------------------------------------------------
-- §7  THE FOUR HOP INSTANCES, `CellRdy` DISCHARGED, AND THE FOUR CELL FACTS.
--
-- The invariant is applied FOUR times — the leg's up hop (node A's BF server,
-- the up cell, the relay's BF client) and its down hop (the relay's BF server,
-- the down cell, node D's BF client), at each of the two legs — through the
-- banked accessors, with NO restatement.
--
-- THE ESCAPE ARM IS CUT BY A CARRIED THEOREM, not by a new premise:
-- `LiveLegStep.NoTwoTokens` (PROVED in `LiveTokenExcl` — statement, base, frame
-- and preservation over every step class) has exactly the fields
-- `nUpCellCli : CellFullBlk (cellUp l s) → BFcHasBlk (upClient l s) → ⊥` and
-- `nDnCellCli`, and `AtPos l lpUpCell` supplies their first argument through
-- `LiveLegInv.cellFull⁺⇒fullBlk`.
------------------------------------------------------------------------

-- the leg's UP hop: node A's BF server, the up cell, the relay's BF client
ChanUp : TwoLegs → SysState → Set
ChanUp l s = ChanInv (coarsenBFs (upSrv l s)) (cellUp l s) (coarsenBFc (upClient l s))

-- … and its DOWN hop: the relay's BF server, the down cell, node D's BF client
ChanDn : TwoLegs → SysState → Set
ChanDn l s = ChanInv (coarsenBFs (dnSrv l s)) (cellDn l s) (coarsenBFc (dnClient l s))

-- one leg's two hops
ChanLeg : TwoLegs → SysState → Set
ChanLeg l s = ChanUp l s × ChanDn l s

-- a client whose COARSE position is the delivery-pending one HOLDS a block, in
-- `NoTwoTokens`' own vocabulary (`PipeInv.BFcHasBlk`, on the fine position)
holdA⇒hasBlk : (q : SN.BFcPos) → CliHoldA (coarsenBFc q) → BFcHasBlk q
holdA⇒hasBlk (SN.bcHead BF.stIdle)      (_ , ())
holdA⇒hasBlk (SN.bcHead BF.stBusy)      (_ , ())
holdA⇒hasBlk (SN.bcHead BF.stStreaming) (_ , ())
holdA⇒hasBlk (SN.bcHead BF.stDone)      (_ , ())
holdA⇒hasBlk (SN.bcReq1 r)                 (_ , ())
holdA⇒hasBlk SN.bcDone1                    (_ , ())
holdA⇒hasBlk (SN.bcBlk1 b)                 _ = tt
holdA⇒hasBlk (SN.bcSil BF.stIdle)       (_ , ())
holdA⇒hasBlk (SN.bcSil BF.stBusy)       (_ , ())
holdA⇒hasBlk (SN.bcSil BF.stStreaming)  (_ , ())
holdA⇒hasBlk (SN.bcSil BF.stDone)       (_ , ())

-- *** `CellRdy` DISCHARGED. ***  Task 1's parked conjunct is a COROLLARY of the
-- channel invariant plus the carried `NoTwoTokens`: the invariant's block
-- instance gives "the reader accepts the token", the exclusion kills the
-- holding escape, and `LiveChanRead`'s derived pin turns acceptance into
-- `LiveCellOpen.CliStream`.
chanLeg⇒cellRdy : (l : TwoLegs) (s : SysState)
                → ChanLeg l s → NoTwoTokens l s → CellRdy l s
chanLeg⇒cellRdy l s (ivU , ivD) ntt = up , dn
  where
  -- the escape cut at the UP cell, on an EXPLICIT argument (never a `with`: the
  -- campaign's rule for anything whose type mentions the imported `CellFull⁺`)
  upArms : CellFull⁺ blkA (cellUp l s)
         → CliAcceptsA (upLink l) hi (coarsenBFc (upClient l s)) (blkPayload blkA)
           ⊎ CliHoldA (coarsenBFc (upClient l s))
         → CliStream (upClient l s)
  upArms hu (inj₁ acc)  =
    acceptsBlk⇒stream (upLink l) hi (coarsenBFc (upClient l s)) blkA acc
  upArms hu (inj₂ hold) =
    ⊥-elim (nUpCellCli ntt (cellFull⁺⇒fullBlk blkA (cellUp l s) hu)
             (holdA⇒hasBlk (upClient l s) hold))
  up : CellFull⁺ blkA (cellUp l s) → CliStream (upClient l s)
  up hu = upArms hu (chanInv⇒blkAccepts (upLink l) (coarsenBFs (upSrv l s))
                      (cellUp l s) (coarsenBFc (upClient l s)) blkA ivU hu)
  -- … and at the DOWN cell
  dnArms : CellFull⁺ blkA (cellDn l s)
         → CliAcceptsA (dnLink l) hi (coarsenBFc (dnClient l s)) (blkPayload blkA)
           ⊎ CliHoldA (coarsenBFc (dnClient l s))
         → CliStream (dnClient l s)
  dnArms hd (inj₁ acc)  =
    acceptsBlk⇒stream (dnLink l) hi (coarsenBFc (dnClient l s)) blkA acc
  dnArms hd (inj₂ hold) =
    ⊥-elim (nDnCellCli ntt (cellFull⁺⇒fullBlk blkA (cellDn l s) hd)
             (holdA⇒hasBlk (dnClient l s) hold))
  dn : CellFull⁺ blkA (cellDn l s) → CliStream (dnClient l s)
  dn hd = dnArms hd (chanInv⇒blkAccepts (dnLink l) (coarsenBFs (dnSrv l s))
                      (cellDn l s) (coarsenBFc (dnClient l s)) blkA ivD hd)

-- *** `oUpCell` AT BOTH LEGS, off the invariant. ***  the same conclusion Task 1
-- reached, with the reader-alignment premise replaced by an object that has a
-- preservation calculus (§5) and a carried theorem
cellOpen-up-chan : (l : TwoLegs) (r : RState)
                 → broken (med (toSys r)) (upLink l) ≡ false
                 → ChanUp l (toSys r) → NoTwoTokens l (toSys r)
                 → RefutedAt l lpUpCell blkA r
cellOpen-up-chan l r hbrk ivU ntt at sta =
  arms (chanInv⇒blkAccepts (upLink l) (coarsenBFs (upSrv l (toSys r)))
         (cellUp l (toSys r)) (coarsenBFc (upClient l (toSys r))) blkA ivU (proj₁ at))
  where
  arms : CliAcceptsA (upLink l) hi (coarsenBFc (upClient l (toSys r))) (blkPayload blkA)
         ⊎ CliHoldA (coarsenBFc (upClient l (toSys r)))
       → ⊥
  arms (inj₁ acc)  =
    cellFull-up-⊥ l r (blkPayload blkA) hbrk (proj₁ at) acc sta
  arms (inj₂ hold) =
    nUpCellCli ntt (cellFull⁺⇒fullBlk blkA (cellUp l (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (upClient l (toSys r)) hold)

-- *** `oDnCell` AT BOTH LEGS ***
cellOpen-dn-chan : (l : TwoLegs) (r : RState)
                 → broken (med (toSys r)) (dnLink l) ≡ false
                 → ChanDn l (toSys r) → NoTwoTokens l (toSys r)
                 → RefutedAt l lpDnCell blkA r
cellOpen-dn-chan l r hbrk ivD ntt at sta =
  arms (chanInv⇒blkAccepts (dnLink l) (coarsenBFs (dnSrv l (toSys r)))
         (cellDn l (toSys r)) (coarsenBFc (dnClient l (toSys r))) blkA ivD (proj₁ at))
  where
  arms : CliAcceptsA (dnLink l) hi (coarsenBFc (dnClient l (toSys r))) (blkPayload blkA)
         ⊎ CliHoldA (coarsenBFc (dnClient l (toSys r)))
       → ⊥
  arms (inj₁ acc)  =
    cellFull-dn-⊥ l r (blkPayload blkA) hbrk (proj₁ at) acc sta
  arms (inj₂ hold) =
    nDnCellCli ntt (cellFull⁺⇒fullBlk blkA (cellDn l (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (dnClient l (toSys r)) hold)

------------------------------------------------------------------------
-- §7b  *** THE LEG-LEVEL LIFT. ***
--
-- §5 proves preservation at ONE hop, per step class, on the ABSTRACT triple.
-- What a consumer holds instead is a LEG and a STEP, with the three components
-- reached through the accessors `upSrv`/`cellUp`/`upClient` (and their down
-- twins).  This section closes that gap in the shape `LTL/Value/PipeSrvInv.agda`
-- established for the server coupling: an EVOLUTION WITNESS naming which class
-- moved the hop (`UpSrvEvo` there, `HopEvo` here), ONE preservation theorem
-- dispatching on it (`srvCoupled-pres` there, `chanInv-pres` here), and a lift
-- along the accessors that is a `subst` per component (`srvCoupled-frame`'s
-- shape, at four hops here).
--
-- WHY A DATATYPE, not a nested `⊎`: the eight arms carry DIFFERENT index
-- patterns — the io classes pin the source AND the successor phase, the api
-- classes fix the phase, the drain fixes both peers — so as a datatype each
-- arm's phase discipline is checked at CONSTRUCTION and the preservation
-- dispatch is forced total by the datatype rather than by a reading.  (It is
-- also the campaign's standing rule that every dispatch be on a datatype.)
--
-- WHAT THE ARMS COST A CALLER — each is what the banked peels already return:
-- `PipeMedKey.cell-in-key` returns `(ph ≡ empty) × (successor ≡ … (full x))`,
-- which is `heSrvSend`/`heCliSend`'s pair of phase indices; `cell-out-key`
-- returns `(ph ≡ full x) × (successor ≡ … (draining x))`, which is
-- `heSrvRead`/`heCliRead`'s; the drain τ writes `empty` over `draining x`
-- (`SysOracle_TauCore:1084-1089`), which is `heDrain`'s; and the peer adjacency
-- is §4c's producer at the fired peer step.  The `-eq` forms take those
-- equations in the direction the peels produce them (`accessor s′ ≡ literal`),
-- so no caller has to `sym` anything.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §6b  *** THE TWO CROSS-PEER REFUTATIONS, and the api COMPOSITION. ***  What a
-- consumer of §4c's producers holds at a real step is a fact PER PEER, so the
-- pair (server, client) has four shapes and only two of them are a `HopEvo` arm.
-- These three lemmas close the other two:
--
--   · BOTH peers fired the same io — impossible, and the reason is the PAYLOAD's
--     ROLE: a hop's cell is one slot that both peers write, but the server's four
--     wire-send rows are gated on RESPONDER tuples and the client's two on
--     INITIATOR ones (and symmetrically for the reads), so no payload fires both.
--     One absurd pattern per server row does it.
--   · BOTH peers fired the same api — this one needs NO refutation: an api leaves
--     the cell alone, so the two adjacencies COMPOSE (the intermediate channel
--     state is a value, not a state of the system).
------------------------------------------------------------------------

-- no payload is both a server wire-send and a client wire-send
srvSend-cliSend-⊥ : {sa sa′ : NS.BFsPos} {ca ca′ : NS.BFcPos} {x : Payload}
                  → SrvSendAdj sa x sa′ → CliSendAdj ca x ca′ → ⊥
srvSend-cliSend-⊥ ssSB      ()
srvSend-cliSend-⊥ ssNB      ()
srvSend-cliSend-⊥ (ssBlk b) ()
srvSend-cliSend-⊥ ssBD      ()

-- … and none is both a server wire-read and a client wire-read
srvRead-cliRead-⊥ : {sa sa′ : NS.BFsPos} {ca ca′ : NS.BFcPos} {x : Payload}
                  → SrvReadAdj sa x sa′ → CliReadAdj ca x ca′ → ⊥
srvRead-cliRead-⊥ (srReq r) ()
srvRead-cliRead-⊥ srCD      ()

-- BOTH peers moved on an api: the two preservations compose at the fixed cell
chan-bothApi : (sa sa′ : NS.BFsPos) (ph : CopyPhase) (ca ca′ : NS.BFcPos)
             → SrvApiAdj sa sa′ → CliApiAdj ca ca′
             → ChanInv sa ph ca → ChanInv sa′ ph ca′
chan-bothApi sa sa′ ph ca ca′ adjS adjC iv =
  chan-cliApi sa′ ph ca ca′ adjC (chan-srvApi sa sa′ ph ca adjS iv)

-- the per-hop EVOLUTION across ONE step: which of the eight classes moved it.
-- `heFrame` is the "nothing in this hop moved" arm — a step at another link or
-- another protocol, an api of another peer, or a link BREAK (which passes the
-- phase function through unchanged, `PipeEvStep:305`).
data HopEvo : NS.BFsPos → CopyPhase → NS.BFcPos
            → NS.BFsPos → CopyPhase → NS.BFcPos → Set where
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
chanInv-pres : {sa sa′ : NS.BFsPos} {ph ph′ : CopyPhase} {ca ca′ : NS.BFcPos}
             → HopEvo sa ph ca sa′ ph′ ca′ → ChanInv sa ph ca → ChanInv sa′ ph′ ca′
chanInv-pres heFrame         iv = iv
chanInv-pres (heSrvApi adj)  iv = chan-srvApi  _ _ _ _ adj iv
chanInv-pres (heCliApi adj)  iv = chan-cliApi  _ _ _ _ adj iv
chanInv-pres (heSrvSend adj) iv = chan-srvSend _ _ _ _ adj iv
chanInv-pres (heCliSend adj) iv = chan-cliSend _ _ _ _ adj iv
chanInv-pres (heSrvRead adj) iv = chan-srvRead _ _ _ _ adj iv
chanInv-pres (heCliRead adj) iv = chan-cliRead _ _ _ _ adj iv
chanInv-pres heDrain         iv = chan-drain   _ _ _ iv

-- … the same with the successor's three components given by EQUATIONS instead
-- of literally: the frame lemma composed with the dispatch, once
chanInv-pres-eq : {sa sa′ sa″ : NS.BFsPos} {ph ph′ ph″ : CopyPhase}
                  {ca ca′ ca″ : NS.BFcPos}
                → sa″ ≡ sa′ → ph″ ≡ ph′ → ca″ ≡ ca′
                → HopEvo sa ph ca sa′ ph′ ca′ → ChanInv sa ph ca → ChanInv sa″ ph″ ca″
chanInv-pres-eq ue ce cle evo iv =
  chan-frame _ _ _ _ _ _ (sym ue) (sym ce) (sym cle) (chanInv-pres evo iv)

-- … and with the SOURCE's three components given by equations TOO (T2b review
-- M-2).  A real caller holds the source phase PROPOSITIONALLY — `PipeMedKey`'s
-- `cell-in-key` returns `ph ≡ empty`, and that `ph` is the leg's `cellUp l s`
-- only after `PipeTauIo.atKey` — so without this form it must hand-roll a source
-- `chan-frame` before it can name the `HopEvo` arm.  Two frames and the dispatch.
chanInv-pres-eq² : {sa₀ sa sa′ sa″ : NS.BFsPos} {ph₀ ph ph′ ph″ : CopyPhase}
                   {ca₀ ca ca′ ca″ : NS.BFcPos}
                 → sa₀ ≡ sa → ph₀ ≡ ph → ca₀ ≡ ca
                 → sa″ ≡ sa′ → ph″ ≡ ph′ → ca″ ≡ ca′
                 → HopEvo sa ph ca sa′ ph′ ca′
                 → ChanInv sa₀ ph₀ ca₀ → ChanInv sa″ ph″ ca″
chanInv-pres-eq² ue₀ ce₀ cle₀ ue ce cle evo iv =
  chanInv-pres-eq ue ce cle evo (chan-frame _ _ _ _ _ _ ue₀ ce₀ cle₀ iv)

-- the UP hop's evolution across one step, at the banked accessors
ChanUpEvo : TwoLegs → SysState → SysState → Set
ChanUpEvo l s s′ =
  HopEvo (coarsenBFs (upSrv l s))  (cellUp l s)  (coarsenBFc (upClient l s))
         (coarsenBFs (upSrv l s′)) (cellUp l s′) (coarsenBFc (upClient l s′))

-- … and the DOWN hop's
ChanDnEvo : TwoLegs → SysState → SysState → Set
ChanDnEvo l s s′ =
  HopEvo (coarsenBFs (dnSrv l s))  (cellDn l s)  (coarsenBFc (dnClient l s))
         (coarsenBFs (dnSrv l s′)) (cellDn l s′) (coarsenBFc (dnClient l s′))

-- THE LIFT AT THE UP HOP, with the successor's components read off the peel's
-- OWN equations (the form a real step can feed; `ChanUpEvo` is its `refl` case)
chanUp-pres : (l : TwoLegs) (s s′ : SysState)
              {sa′ : NS.BFsPos} {ph′ : CopyPhase} {ca′ : NS.BFcPos}
            → coarsenBFs (upSrv l s′) ≡ sa′ → cellUp l s′ ≡ ph′
            → coarsenBFc (upClient l s′) ≡ ca′
            → HopEvo (coarsenBFs (upSrv l s)) (cellUp l s) (coarsenBFc (upClient l s))
                     sa′ ph′ ca′
            → ChanUp l s → ChanUp l s′
chanUp-pres l s s′ ue ce cle evo iv = chanInv-pres-eq ue ce cle evo iv

-- … and at the DOWN hop
chanDn-pres : (l : TwoLegs) (s s′ : SysState)
              {sa′ : NS.BFsPos} {ph′ : CopyPhase} {ca′ : NS.BFcPos}
            → coarsenBFs (dnSrv l s′) ≡ sa′ → cellDn l s′ ≡ ph′
            → coarsenBFc (dnClient l s′) ≡ ca′
            → HopEvo (coarsenBFs (dnSrv l s)) (cellDn l s) (coarsenBFc (dnClient l s))
                     sa′ ph′ ca′
            → ChanDn l s → ChanDn l s′
chanDn-pres l s s′ de fe dle evo iv = chanInv-pres-eq de fe dle evo iv

-- *** ONE LEG'S TWO HOPS ACROSS ONE STEP. ***  the object the assembly threads
chanLeg-pres : (l : TwoLegs) (s s′ : SysState)
             → ChanUpEvo l s s′ → ChanDnEvo l s s′ → ChanLeg l s → ChanLeg l s′
chanLeg-pres l s s′ eu ed (ivU , ivD) =
    chanUp-pres l s s′ refl refl refl eu ivU
  , chanDn-pres l s s′ refl refl refl ed ivD

-- FRAME at the leg: the SIX slots the two hops read, all fixed — the
-- `PipeSrvInv.srvCoupled-frame` shape at this invariant's components (a step at
-- another link, another protocol, another peer's api, or a link break)
chanLeg-frame : (l : TwoLegs) (s s′ : SysState)
              → upSrv l s ≡ upSrv l s′ → cellUp l s ≡ cellUp l s′
              → upClient l s ≡ upClient l s′
              → dnSrv l s ≡ dnSrv l s′ → cellDn l s ≡ cellDn l s′
              → dnClient l s ≡ dnClient l s′
              → ChanLeg l s → ChanLeg l s′
chanLeg-frame l s s′ ue ce cle de fe dle (ivU , ivD) =
    chanUp-pres l s s′ (cong coarsenBFs (sym ue)) (sym ce)
      (cong coarsenBFc (sym cle)) heFrame ivU
  , chanDn-pres l s s′ (cong coarsenBFs (sym de)) (sym fe)
      (cong coarsenBFc (sym dle)) heFrame ivD

-- BASE — at `initial` every BF peer sits at its idle head and every cell is
-- empty, so both hops of both legs are §3's base case
chanLeg-init : (l : TwoLegs) → ChanLeg l initial
chanLeg-init legBD = chanInv-init , chanInv-init
chanLeg-init legCD = chanInv-init , chanInv-init

------------------------------------------------------------------------
-- §7c  *** THE DISCHARGE — `LiveCellOpen`'s PARKED PREMISE, SUPPLIED. ***
--
-- Task 1 proved the four cell facts FROM `CellRdy` and PARKED it (its (H2));
-- §7's `chanLeg⇒cellRdy` DERIVES `CellRdy` from `ChanLeg` + `NoTwoTokens`; and
-- §7b gives `ChanLeg` a base case, a frame and a complete per-step preservation
-- calculus.  The composition below is the discharge, taken at the WINDOW form of
-- Task 1's own theorems — the four cell facts of record with NO parked conjunct
-- left in their premises.  What remains is the leg's own window (Task 1's (H1),
-- discharged there off `wLink1`/`wLink2`) and the two INVARIANTS
-- `ChanLeg`/`NoTwoTokens`, whose reachability closure is the assembly's job for
-- both, exactly as for `LegInv` (`LiveTokenExcl.agda:1100-1113`).
--
-- *** WHAT THIS IS NOT: *** it is not itself a claim that `ChanLeg l (toSys r)`
-- holds at every reachable state — this module states the calculus, not the
-- threading.  It IS the claim that no consumer of `LiveCellOpen` needs the parked
-- `CellRdy` any more: the premise it takes is now an object with a proof calculus
-- behind it.  *** AND THE THREADING NOW EXISTS: *** `LiveChanJoin` carries
-- `ChanLeg` — both hops — through all five step classes as a trailing factor of the
-- assembly's joint invariant, exactly as `NoTwoTokens` is carried, so the FSim's
-- `Rel` holds it at every reachable config and `LivenessProof.Premises` names no
-- channel field at all.
--
-- AND IT IS NOT A PARALLEL ROUTE to §7's `cellOpen-up-chan`/`cellOpen-dn-chan`
-- (the Task-2b cleanup's whole point was to leave ONE route per conclusion).
-- *** TASK-4 FIX (T2b review I-2): the two are now LAYERED IN THE LITERAL SENSE,
-- the way `LiveCellOpen.cellOpen-up-w = cellOpen-up (wLink1 w)` is. ***  Before
-- this fix `cellOpen-w-chan` reached the SAME two conclusions by a genuinely
-- INDEPENDENT route (`chanLeg⇒cellRdy` + `LiveCellOpen`'s per-leg ladder), so the
-- io-refutation half was proved twice by different means and the ONE-ROUTE rule
-- was met in premise strength only.  It is now a CALL of §7's raw pair with the
-- window's two link fields projected out, which is what the interface actually
-- wanted: §7's pair is the weaker-premised form (each arm needs only its OWN
-- hop's invariant plus that link's `broken … ≡ false`, which is exactly the shape
-- Task 4's field edit landed).  `chanLeg⇒cellRdy` STAYS as the type-level
-- discharge of Task 1's parked parameter — that is its whole job — but it is no
-- longer on the path to these two conclusions.
------------------------------------------------------------------------

-- *** THE FOUR CELL FACTS, OFF PROVED CONTENT. ***  §7's raw pair at both legs
-- with the leg's window supplying each hop's link fact (T2b review I-2's layering)
cellOpen-w-chan : (l : TwoLegs) (r : RState)
                → Window l (toSys r) (upLink l) (dnLink l)
                → ChanLeg l (toSys r) → NoTwoTokens l (toSys r)
                → RefutedAt l lpUpCell blkA r × RefutedAt l lpDnCell blkA r
cellOpen-w-chan l r w chl ntt =
    cellOpen-up-chan l r (wLink1 w) (proj₁ chl) ntt
  , cellOpen-dn-chan l r (wLink2 w) (proj₂ chl) ntt
