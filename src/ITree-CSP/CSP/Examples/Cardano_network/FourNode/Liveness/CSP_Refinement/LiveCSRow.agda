{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — THE CHAINSYNC ROW LAYER (`Praos.LiveCSRow`), T4 of the
-- cross-node api campaign.
--
-- *** WHAT THIS MODULE IS, AND WHICH ROUTE IT TAKES. ***  A consumer that needs a
-- peer ADJACENCY out of a fired api step has TWO routes (the corrected doctrine
-- sentence, `STABR_STATUS.md` §5's coarse-ROW bullet): widen the decode with a
-- trailing row field (KEEP-IN-SYNC at the decode, no table obligation), or recover
-- the row POST HOC from COARSE-position injectivity of the peer's table (no
-- KEEP-IN-SYNC, but a standing support-distinctness review obligation on
-- `NodeSpecs`).  This module is ROUTE TWO for the ChainSync axis: NO decode
-- widening, NO LTL edit, no `Premises`/`livenessSpec` edit, and nothing frozen is
-- transcribed except the one bundle peel §5 declares.
--
-- What the recovery rests on is `tsSupport` (§1): a `tableSpec` EQUATION TRANSFERS
-- OFFER SUPPORT — fire `q₁`'s row with the banked `tableSpec-ev-fwd`, transport the
-- step along the equation, read `q₂`'s row off it with the banked
-- `tableSpec-ev-inv`.  It is generic in `Pos` and in the table, so coarse
-- injectivity of a `tableSpec` table is single-peel provable EXACTLY WHEN its coarse
-- positions have pairwise-distinct offer SUPPORTS.  What is FALSE — and all that
-- `absCS{c,s}-sil-collapse` (`SysStep:1148-1150`) actually proves — is FINE-position
-- injectivity: `coarsenCSc` identifies `csSil st` with `csHead st`, so the
-- collapse's coarse witness pair is DIAGONAL and constrains nothing off the
-- diagonal.  Never cite the sil-collapse against this route.
--
-- *** THE STANDING REVIEW OBLIGATION (R2), AS A PREDICATE AND NOT AS PROSE. ***
-- `Separates`/`SupportDistinct` (§1) name the condition; §2 and §3 CHECK it against
-- the two live tables by exhibiting, for every ordered pair of distinct coarse
-- positions, a separating probe (or the symmetric one, for the two nested pairs).
-- A future `NodeSpecs` row that gives two coarse positions the SAME support kills
-- the single-peel route — different targets are NOT enough to save it — and it will
-- surface as a red clause in §2/§3 rather than as a silent weakening.
--
-- Sources (mined, not imported — the spike files are `.txt` archives):
--   • `tsSupport`, the `ccIdle`/`ccWreq` rows and the six-line wrapper are
--     transcribed from `task-3-spike-SpikeCSRowCSP.agda.txt` (§1 `:97-107`,
--     §2 `:124-138`, §3 `:155-180`, §5 `:250-259`), whose spike module was green.
--   • the tables checked here: `NodeSpecs.csCnxt` `:306-381` (17 informative rows,
--     12 coarse positions) and `NodeSpecs.csSnxt` `:416-490` (18 informative rows,
--     13 coarse positions) — spans re-derived in this round, not relayed.
--   • the two banked generic table lemmas: `SysOracle_NodeTauEv.tableSpec-ev-fwd`
--     `:979-984` and `tableSpec-ev-inv` `:963-966`, with `nothing-absurd` `:997-998`
--     and the `tsForce-ret`/`tsForce-react` pair `:827-836`.
--
-- Two negatives banked by the spike verification and honoured here: a pattern
-- variable named `no` collides with `Relation.Nullary.no` (nothing here is called
-- `no`), and every `ceqCS*` with payload-shape implicits needs them SPELLED at a
-- generic call site (`ceqCSc06`/`07`/`10`, `ceqCSs01`/`14`… below).
--
-- *** WHAT (T5) ADDED, AND WHAT IT FOUND. ***  §4b is the PER-KEY SOURCE/TARGET
-- PIN the T4 review identified as the layer's missing link: a recovered ROW names
-- a coarse EDGE at a VARIABLE source, while `LiveRelayCS.CSAt`'s `cp5`/`pp1`
-- clauses name a TARGET, and only the enumeration AT THE KEY closes the gap.  Two
-- keys are built — `recvCSRollforward` (client, `cp5`) and `reqCSRequestNext`
-- (server, `pp1`) — plus the four io refutations that machine-check "no
-- `input`/`output` row touches `ccIdle` or `csCanAwait`".
--
-- *** THE io-CONE BLOCKER THIS HEADER ONCE RECORDED — RESOLVED INSIDE THE SAME TASK.
-- ***  Kept as HISTORY, in four dated steps, because the retraction in (2) is the part
-- worth carrying; read NONE of it as a standing obstruction (review I-2).
--
--   (1) FOUND (T5, round 1 — the round ended BLOCKED with the pins below landed and no
--       arm discharged).  A driver-tail coupling on either CS slot must survive all
--       five step classes, and its two io classes need the shape the BF coupling gets
--       from `LiveLegIoCone` — "the peer is FIXED, or its row fired".  For the CS peers
--       that shape existed NOWHERE: `PipeNodeIoEvo.BundleEvo` bound `csc′`/`css′`
--       EXISTENTIALLY and carried facts only for the BF client (`Cf`), the BF server
--       (`Sf`) and the bundle's `InertPos` (`If`); neither the four node peel records
--       nor `top-nodes-io-evoP`'s output carried the CS slots any further.
--   (2) RETRACTED — AND THIS HALF STANDS, AS A REASONING PATTERN.  The gate
--       verification's "for `cp5`/`pp1` the io classes are frame-only" is TRUE about the
--       TABLES — §4b's four refutations ARE that fact, proved — and does NOT follow for
--       the CONE: a refutation still needs the fired row to refute.  *** "No row at the
--       position" is a fact about the TABLE; "the peer did not move" is a fact about the
--       CONE, and the second never follows from the first. ***
--   (3) VERIFIED, THEN DEMOTED TO PLUMBING.  The adversarial verification confirmed the
--       gap at the fact CHANNEL and priced the rest as wiring: §5's
--       `absBundleCS-ev-prod⁺` is generic in the CS event and
--       `ιCS (sendCS l d) = input l d N2N_ChainSync` DEFINITIONALLY
--       (`NetworkPar:184-185`), so the io labels needed no new peel at all.  Its
--       doctrine guard applies to this block too: the "second peel" route closes as
--       FINE recovery REFUTED (the `absCS*-sil-collapse` makes `absNodeB`/`absNodesOf`
--       provably non-injective by `cong`) plus COARSE recovery blocked by the missing
--       `_⦀_`/`_∥⇘⇙_` injectivity — NEVER by the absolute "no injectivity anywhere",
--       which the T3/T4 reversal refuted once already (task-5 report §11).
--   (4) CLOSED by OWNER GRANT #11, SERVER HALF.  `PipeNodeIoEvo` gained a FOURTH fact
--       family: `CssFact` (`:207-212`), the trailing `BundleEvo` conjunct (`:215-230`),
--       the `IoFacts` field plus the premise-free `csRefl` (`:584-`), ONE peel field on
--       each RELAY node record only (`:640-700` — nodes A and D untouched, since both
--       tracked CS servers are the relays'), and a trailing `top-nodes-io-evoP`
--       component (`:1103-`); the CSP-side instance is `LiveLegIoCone.CssRowP`.
--       `LiveRelayCS`'s `pp1` arm is DISCHARGED off it, through §4b's server pin.
--       `cp5` still wants the grant's CLIENT half, which is deliberately unbuilt (no
--       consumer yet).  *** ALL FOUR ANCHORS ABOVE RE-DERIVED AT THIS ROUND: *** the
--       three the round-1 text cited (`:185-197`, `:597-653`, `:1035-…`) were
--       invalidated by grant #11's own insertions into that very file.
--
-- No postulate, no hole, no `mutual`; base modules touched: NONE.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit using ( ⊤; tt )
-- the `Par` merge argument lives at the POLYMORPHIC unit (`Level.Lift 0ℓ ⊤`), while
-- the `done` channel's carrier is the plain one — both are needed, so the
-- polymorphic constructor travels under a distinct name
open import Data.Unit.Polymorphic using () renaming ( tt to ttP )
open import Data.Bool using ( true; false )
open import Data.List using ( List )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_; yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; _≢_; refl; sym; trans; cong; subst )
open import Class.DecEq using ( DecEq; _≟_ )
open import Class.DecEq.Instances using ( DecEq-Fin )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI; ret; react )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCSRow
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; ApiCSTag; ApiCSCar
  ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break; done
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; store; env
  -- (T5 / review M-4) `sendCSDone`, `sendCSFindIntersect`, `sendCSIntersectFound`
  -- and `sendCSRollBackward` were DEAD here (each occurred once, in this list) and
  -- are pruned; the tables reduce at those tags without the constructor being in
  -- scope, since `using` controls names and not reduction.  `just-injective` was
  -- the fifth dead entry the review found and is LIVE as of §4b, so it stays.
  -- (T8c-ii) `sendCSDone` is LIVE again — §4c's third client EDGE pin reads its row
  ; sendCSRequestNext; sendCSAwaitReply; sendCSDone
  ; sendCSRollForward
  ; sendCSIntersectNotFound; recvCSRollforward; recvCSRollback
  ; recvCSIntersectFound; recvCSIntersectNotFound
  ; reqCSRequestNext; reqCSFindIntersect )
open import CSP.Examples.Cardano_network.Data p using
  ( Payload; Point; Header; Tip; point; header; tip
  ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-Payload
  ; chainSync; MsgCSRequestNext; MsgCSFindIntersect; MsgCSDone
  ; MsgCSRollForward; MsgCSRollBackward; MsgCSAwaitReply
  ; MsgCSIntersectFound; MsgCSIntersectNotFound )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( time₀; length₀ )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; DecEq-Dir; FromInitiator; FromResponder; IDs
  ; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission
  ; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS )
import CSP.Examples.Cardano_network.ChainSync p as CS

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_ )
open Op using () renaming ( ∅ES to ∅ESa )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open NS using ( DecEq-H×T; DecEq-P×T )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( CScPos; CSsPos; BFcPos; BFsPos; InertPos
              ; kac; kas; tsc; tss; lnc; lns; lfc; lfs
              ; bundleG; decKAc; decKAs; decCSc; decCSs )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absCSc; absCSs; coarsenCSc; coarsenCSs; absBundleG
                 ; absKAc; absKAs; absBFc; absBFs; absTSc; absTSs
                 ; absLNc; absLNs; absLFc; absLFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( csEvLink; csCnxt-link-no; csSnxt-link-no )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( csEvDir; noOffer→viewV; ιKA⁻¹∘ιCS
        ; decKAc-noOffer; decKAs-noOffer
        ; absKAc-noCS; absKAs-noCS; absBFc-noCS; absBFs-noCS
        ; absTSc-noCS; absTSs-noCS )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteKaTs blkA
  using ( csCnxt-dir-no; csSnxt-dir-no; absCSs-dir-noBoth; decCSc-dir-noOffer
        ; absLNc-noCS; absLNs-noCS; absLFc-noCS; absLFs-noCS )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA
  using ( csTail-css-noOffer; csTail-bfc-noOffer )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( ⦀-wev-L; ⦀-wev-R; absCSc-ev-dir; absCSs-ev-dir )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; tableSpec-ev-fwd; nothing-absurd
        ; tsForce-ret; tsForce-react )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA
  using ( Tcsc; Tcss; decCSc-ev-prod-abs; decCSs-ev-prod-abs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  using ( ceqCSc01; ceqCSc06; ceqCSc07; ceqCSc10; ceqCSc11; ceqCSc12; ceqCSc13
        ; ceqCSc15; ceqCSc16; ceqCSc17; ceqCSc18
        ; ceqCSs01; ceqCSs06; ceqCSs07; ceqCSs10; ceqCSs11; ceqCSs12; ceqCSs13
        ; ceqCSs14; ceqCSs15; ceqCSs16; ceqCSs17; ceqCSs18 )

------------------------------------------------------------------------
-- §1  *** THE DEEPER OBJECT: A `tableSpec` EQUATION TRANSFERS OFFER SUPPORT. ***
--
-- Generic in `Pos` and in the table — it mentions only `NodeSpecs.Table` and the
-- two banked table lemmas — so it is neither CS-specific nor layer-specific.
-- Everything below is bookkeeping on top of it.
------------------------------------------------------------------------

-- if `q₁` offers the event and `tableSpec` cannot tell `q₁` from `q₂`, then `q₂`
-- offers it too (fire at `q₁`, transport along the equation, invert at `q₂`)
tsSupport : {Pos : Set} (T : NS.Table Pos) (q₁ q₂ : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {p₁ : Pos}
  → NS.Table.isFin T q₁ ≡ false
  → NS.Table.nxt T q₁ (X , e) a ≡ just p₁
  → NS.tableSpec T q₁ ≡ NS.tableSpec T q₂
  → Σ[ q′ ∈ Pos ] (NS.Table.nxt T q₂ (X , e) a ≡ just q′)
tsSupport T q₁ q₂ {X} {e} {a} {p₁} fin row eq
  with tableSpec-ev-inv T q₂
         (subst (λ z → z ─[ ev (evl (evLabel X e a)) ]─► NS.tableSpec T p₁) eq
                (tableSpec-ev-fwd T q₁ fin row))
... | q′ , ceq , _ = q′ , ceq

-- a SEPARATING PROBE for an ordered pair: `q₁` fires an offer that `q₂` refuses.
-- (review M-1) NO TERM of this type — or of `SupportDistinct` below — is built
-- anywhere, DELIBERATELY: the obligation is checked in the INJECTIVITY form of
-- §2/§3, which is the form every consumer wants, and a support collapse surfaces
-- there as a red clause.  The two predicates are here to NAME the condition.
Separates : {Pos : Set} (T : NS.Table Pos) (q₁ q₂ : Pos) → Set₁
Separates {Pos} T q₁ q₂ =
  Σ[ X ∈ Set 0ℓ ] Σ[ e ∈ Net_Api Payload X ] Σ[ a ∈ X ] Σ[ p₁ ∈ Pos ]
      (NS.Table.isFin T q₁ ≡ false)
    × (NS.Table.nxt T q₁ (X , e) a ≡ just p₁)
    × (NS.Table.nxt T q₂ (X , e) a ≡ nothing)

-- THE R2 REVIEW OBLIGATION, NAMED: every ordered pair of DISTINCT coarse positions
-- is separated in one of the two directions.  This — not row-distinctness — is what
-- makes coarse injectivity single-peel provable; two positions with the SAME
-- support kill the route even when their targets differ.  §2/§3 check it for the
-- two CS tables, pair by pair, in the injectivity form the consumers want.
SupportDistinct : {Pos : Set} (T : NS.Table Pos) → Set₁
SupportDistinct {Pos} T = (q₁ q₂ : Pos) → ¬ (q₁ ≡ q₂)
  → Separates T q₁ q₂ ⊎ Separates T q₂ q₁

-- a separating probe REFUTES a `tableSpec` equation (the support transfer turns the
-- refusal into `nothing ≡ just _`) — the one step every §2/§3 clause takes
sep : {Pos : Set} (T : NS.Table Pos) (q₁ q₂ : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {p₁ : Pos}
  → NS.Table.isFin T q₁ ≡ false
  → NS.Table.nxt T q₁ (X , e) a ≡ just p₁
  → NS.Table.nxt T q₂ (X , e) a ≡ nothing
  → NS.tableSpec T q₁ ≡ NS.tableSpec T q₂ → ⊥
sep T q₁ q₂ fin row nq eq =
  nothing-absurd (trans (sym nq) (proj₂ (tsSupport T q₁ q₂ fin row eq)))

-- a TERMINAL position is never `tableSpec`-equal to a non-terminal one (`ret` vs a
-- react node), so the probe-less terminals need NO probe at all: one generic line
-- replaces the eleven symmetric probes their row would otherwise take
tsFinSep : {Pos : Set} (T : NS.Table Pos) (q₁ q₂ : Pos)
  → NS.Table.isFin T q₁ ≡ true
  → NS.Table.isFin T q₂ ≡ false
  → NS.tableSpec T q₁ ≡ NS.tableSpec T q₂ → ⊥
tsFinSep T q₁ q₂ f₁ f₂ eq
  with trans (sym (tsForce-ret T q₁ f₁))
             (trans (cong (λ z → PTree.force z) eq) (tsForce-react T q₂ f₂))
... | ()

-- `_≟_` at UNEQUAL arguments answers `no`, in rewritable form (the `≟-yes-refl`
-- twin; the witness is returned because `¬` has no proof irrelevance here)
≟-noΣ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x y : A}
      → ¬ (x ≡ y) → Σ[ ne ∈ ¬ (x ≡ y) ] ((x ≟ y) ≡ no ne)
≟-noΣ {x = x} {y} ne with x ≟ y
... | yes e   = ⊥-elim (ne e)
... | no  ne′ = ne′ , refl

-- COARSE-position injectivity of the CS-CLIENT table (the layer's hypothesis, and
-- §2's theorem)
TscInj : (l : Link) (d : Dir) → Set₁
TscInj l d = (q₁ q₂ : NS.CScPos)
           → NS.tableSpec (Tcsc l d) q₁ ≡ NS.tableSpec (Tcsc l d) q₂ → q₁ ≡ q₂

-- … and of the CS-SERVER table (§3's theorem)
TssInj : (l : Link) (d : Dir) → Set₁
TssInj l d = (q₁ q₂ : NS.CSsPos)
           → NS.tableSpec (Tcss l d) q₁ ≡ NS.tableSpec (Tcss l d) q₂ → q₁ ≡ q₂

------------------------------------------------------------------------
-- §2  COARSE INJECTIVITY OF THE CS-CLIENT TABLE — all twelve rows.
--
-- One row per SOURCE position, one clause per rival.  Three shapes occur:
--
--   (a) the rival has NO clause at the probe's key, so `csCnxt`'s catch-all
--       (`NodeSpecs:381`) answers `nothing` by `refl` — one line;
--   (b) the rival HAS a clause at that key (the wire-send trio at `input`, the
--       four api families at their own tag), so its table application is STUCK on
--       `l ≟ l`/`d ≟ d` and the payload `≟` has to decide — a two-line refusal
--       helper, and for a SAME-FAMILY rival a `≟` on the index first;
--   (c) the pair is NESTED (`ccMust`'s support ⊊ `ccAwait`'s), so the probe runs
--       from the LARGER side and the equation is used symmetrically.
--
-- `ccTerm` is the probe-less terminal: `tsFinSep`, no probe.
------------------------------------------------------------------------

-- the `ccWreq` wire-send refuses every `input` payload but its own
ccWreq-nq : (l : Link) (d : Dir) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext))
  → NS.csCnxt l d NS.ccWreq (Payload , input l d N2N_ChainSync) pl ≡ nothing
ccWreq-nq l d pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `ccWfi ps` wire-send likewise (its own payload carries the point list)
ccWfi-nq : (l : Link) (d : Dir) (ps : List Point) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)))
  → NS.csCnxt l d (NS.ccWfi ps) (Payload , input l d N2N_ChainSync) pl ≡ nothing
ccWfi-nq l d ps pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … and the `ccWdone` wire-send
ccWdone-nq : (l : Link) (d : Dir) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone))
  → NS.csCnxt l d NS.ccWdone (Payload , input l d N2N_ChainSync) pl ≡ nothing
ccWdone-nq l d pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- the `ccArf` api emit refuses every `recvCSRollforward` value but its own
ccArf-nq : (l : Link) (d : Dir) (ht v : Header × Tip) → ¬ (v ≡ ht)
  → NS.csCnxt l d (NS.ccArf ht) (ApiCSCar recvCSRollforward , apiCS l d recvCSRollforward) v
    ≡ nothing
ccArf-nq l d ht v ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `ccArb` api emit
ccArb-nq : (l : Link) (d : Dir) (pt v : Point × Tip) → ¬ (v ≡ pt)
  → NS.csCnxt l d (NS.ccArb pt) (ApiCSCar recvCSRollback , apiCS l d recvCSRollback) v
    ≡ nothing
ccArb-nq l d pt v ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `ccAif` api emit
ccAif-nq : (l : Link) (d : Dir) (pt v : Point × Tip) → ¬ (v ≡ pt)
  → NS.csCnxt l d (NS.ccAif pt) (ApiCSCar recvCSIntersectFound , apiCS l d recvCSIntersectFound) v
    ≡ nothing
ccAif-nq l d pt v ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … and the `ccAin` api emit
ccAin-nq : (l : Link) (d : Dir) (tp v : Tip) → ¬ (v ≡ tp)
  → NS.csCnxt l d (NS.ccAin tp) (ApiCSCar recvCSIntersectNotFound , apiCS l d recvCSIntersectNotFound) v
    ≡ nothing
ccAin-nq l d tp v ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- ROW 1 — `ccIdle` is separated from every rival by its `sendCSRequestNext` offer
tscInj-ccIdle : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccIdle ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccIdle ≡ q₂
tscInj-ccIdle l d NS.ccIdle       eq = refl
tscInj-ccIdle l d NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccWreq       {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccAwait      {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle (NS.ccWfi ps)   {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccInt        {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccWdone      {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccMust       {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle (NS.ccArf ht)   {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle (NS.ccArb pt)   {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle (NS.ccAif pt)   {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle (NS.ccAin tp)   {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)
tscInj-ccIdle l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccIdle NS.ccTerm       {e = apiCS l d sendCSRequestNext} {a = tt} refl (ceqCSc01 l d) refl eq)

-- ROW 2 — `ccWreq`'s own wire-read of `MsgCSRequestNext`.  The two rival wire-sends
-- have a clause at this very key, so they need the refusal helpers.
tscInj-ccWreq : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccWreq ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccWreq ≡ q₂
tscInj-ccWreq l d NS.ccWreq       eq = refl
tscInj-ccWreq l d NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccIdle       {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccAwait      {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq (NS.ccWfi ps)   {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) (ccWfi-nq l d ps _ (λ ())) eq)
tscInj-ccWreq l d NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccInt        {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccWdone      {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) (ccWdone-nq l d _ (λ ())) eq)
tscInj-ccWreq l d NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccMust       {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq (NS.ccArf ht)   {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq (NS.ccArb pt)   {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq (NS.ccAif pt)   {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq (NS.ccAin tp)   {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)
tscInj-ccWreq l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccWreq NS.ccTerm       {e = input l d N2N_ChainSync} refl (ceqCSc11 l d) refl eq)

-- ROW 3 — `ccAwait`'s `MsgCSAwaitReply` read is the offer `ccMust` does NOT have,
-- which is what separates the nested pair (and the payload implicits are spelled)
tscInj-ccAwait : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccAwait ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccAwait ≡ q₂
tscInj-ccAwait l d NS.ccAwait      eq = refl
tscInj-ccAwait l d NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccIdle       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccWreq       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait (NS.ccWfi ps)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccInt        {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccWdone      {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccMust       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait (NS.ccArf ht)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait (NS.ccArb pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait (NS.ccAif pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait (NS.ccAin tp)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)
tscInj-ccAwait l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccTerm       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl eq)

-- ROW 4 — `ccWfi ps`: a VALUE-INDEXED wire-send, so the same-family rival needs the
-- index `≟` (which the table's own payload guard then decides)
tscInj-ccWfi : (l : Link) (d : Dir) (pts : List Point) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) (NS.ccWfi pts) ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccWfi pts ≡ q₂
tscInj-ccWfi l d pts NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccIdle       {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccWreq       {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) (ccWreq-nq l d _ (λ ())) eq)
tscInj-ccWfi l d pts NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccAwait      {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccInt        {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccWdone      {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) (ccWdone-nq l d _ (λ ())) eq)
tscInj-ccWfi l d pts NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccMust       {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) (NS.ccArf ht)   {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) (NS.ccArb pt)   {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) (NS.ccAif pt)   {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) (NS.ccAin tp)   {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
tscInj-ccWfi l d pts NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) NS.ccTerm       {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d) refl eq)
-- (the `List Point` instance is SPELLED: `ChainSync`'s own `DecEq-ListPoint` is a
-- second candidate here, and only the ambient generic one is the instance the
-- tables' own guards were elaborated with)
tscInj-ccWfi l d pts (NS.ccWfi ps)   eq
  with _≟_ ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ pts ps
... | yes e  = cong NS.ccWfi e
... | no  ne = ⊥-elim (sep (Tcsc l d) (NS.ccWfi pts) (NS.ccWfi ps)
                        {e = input l d N2N_ChainSync} refl (ceqCSc12 {pts} l d)
                        (ccWfi-nq l d ps _ (λ e → ne (fi-inj e))) eq)
  where
    -- the payload determines the point list (the `chainSync` message is injective)
    fi-inj : (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect pts))
             ≡ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
           → pts ≡ ps
    fi-inj refl = refl

-- ROW 5 — `ccInt`'s `MsgCSIntersectNotFound` read (the probe needs a Tip, and the
-- module parameter supplies one)
tscInj-ccInt : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccInt ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccInt ≡ q₂
tscInj-ccInt l d NS.ccInt        eq = refl
tscInj-ccInt l d NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccIdle       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccWreq       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccAwait      {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccInt (NS.ccWfi ps)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccWdone      {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccMust       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccInt (NS.ccArf ht)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccInt (NS.ccArb pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccInt (NS.ccAif pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccInt (NS.ccAin tp)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)
tscInj-ccInt l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccInt NS.ccTerm       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound (tip blkA))} refl (ceqCSc10 {time₀} {FromResponder} {length₀} {tip blkA} l d) refl eq)

-- ROW 6 — `ccWdone`'s own wire-read of `MsgCSDone`
tscInj-ccWdone : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccWdone ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccWdone ≡ q₂
tscInj-ccWdone l d NS.ccWdone      eq = refl
tscInj-ccWdone l d NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccIdle       {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccWreq       {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) (ccWreq-nq l d _ (λ ())) eq)
tscInj-ccWdone l d NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccAwait      {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone (NS.ccWfi ps)   {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) (ccWfi-nq l d ps _ (λ ())) eq)
tscInj-ccWdone l d NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccInt        {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccMust       {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone (NS.ccArf ht)   {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone (NS.ccArb pt)   {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone (NS.ccAif pt)   {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone (NS.ccAin tp)   {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)
tscInj-ccWdone l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccWdone NS.ccTerm       {e = input l d N2N_ChainSync} refl (ceqCSc13 l d) refl eq)

-- ROW 7 — `ccMust`, the SMALLER half of the nested pair: its own
-- `MsgCSRollForward` probe separates it from everything except `ccAwait`, which
-- answers that probe too — so the `ccAwait` clause runs the LARGER side's
-- `MsgCSAwaitReply` probe and uses the equation symmetrically
tscInj-ccMust : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccMust ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccMust ≡ q₂
tscInj-ccMust l d NS.ccMust       eq = refl
tscInj-ccMust l d NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) NS.ccAwait NS.ccMust {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply} refl (ceqCSc06 {time₀} {FromResponder} {length₀} l d) refl (sym eq))
tscInj-ccMust l d NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) NS.ccMust NS.ccIdle       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) NS.ccMust NS.ccWreq       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) NS.ccMust (NS.ccWfi ps)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) NS.ccMust NS.ccInt        {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) NS.ccMust NS.ccWdone      {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) NS.ccMust (NS.ccArf ht)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccMust (NS.ccArb pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) NS.ccMust (NS.ccAif pt)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) NS.ccMust (NS.ccAin tp)   {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)
tscInj-ccMust l d NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) NS.ccMust NS.ccTerm       {e = output l d N2N_ChainSync} {a = time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward (header blkA) (tip blkA))} refl (ceqCSc07 {time₀} {FromResponder} {length₀} {header blkA} {tip blkA} l d) refl eq)

-- ROW 8 — `ccArf ht`: a VALUE-INDEXED api emit; the family rival's own payload `≟`
-- decides, so the row is generic in the carried header/tip
tscInj-ccArf : (l : Link) (d : Dir) (ht : Header × Tip) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) (NS.ccArf ht) ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccArf ht ≡ q₂
tscInj-ccArf l d (h , t) NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccIdle       {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccWreq       {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccAwait      {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) (NS.ccWfi ps)   {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccInt        {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccWdone      {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccMust       {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) (NS.ccArb pt)   {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) (NS.ccAif pt)   {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) (NS.ccAin tp)   {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) NS.ccTerm       {e = apiCS l d recvCSRollforward} {a = h , t} refl (ceqCSc15 {h} {t} l d) refl eq)
tscInj-ccArf l d (h , t) (NS.ccArf ht′)  eq
  with (h , t) ≟ ht′
... | yes e  = cong NS.ccArf e
... | no  ne = ⊥-elim (sep (Tcsc l d) (NS.ccArf (h , t)) (NS.ccArf ht′)
                        {e = apiCS l d recvCSRollforward} {a = h , t} refl
                        (ceqCSc15 {h} {t} l d) (ccArf-nq l d ht′ (h , t) ne) eq)

-- ROW 9 — `ccArb pt`, the same shape at `recvCSRollback`
tscInj-ccArb : (l : Link) (d : Dir) (pt : Point × Tip) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) (NS.ccArb pt) ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccArb pt ≡ q₂
tscInj-ccArb l d (x , t) NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccIdle       {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccWreq       {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccAwait      {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) (NS.ccWfi ps)   {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccInt        {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccWdone      {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccMust       {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) (NS.ccArf ht)   {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) (NS.ccAif pt)   {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) (NS.ccAin tp)   {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) NS.ccTerm       {e = apiCS l d recvCSRollback} {a = x , t} refl (ceqCSc16 {x} {t} l d) refl eq)
tscInj-ccArb l d (x , t) (NS.ccArb pt′)  eq
  with (x , t) ≟ pt′
... | yes e  = cong NS.ccArb e
... | no  ne = ⊥-elim (sep (Tcsc l d) (NS.ccArb (x , t)) (NS.ccArb pt′)
                        {e = apiCS l d recvCSRollback} {a = x , t} refl
                        (ceqCSc16 {x} {t} l d) (ccArb-nq l d pt′ (x , t) ne) eq)

-- ROW 10 — `ccAif pt`, at `recvCSIntersectFound`
tscInj-ccAif : (l : Link) (d : Dir) (pt : Point × Tip) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) (NS.ccAif pt) ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccAif pt ≡ q₂
tscInj-ccAif l d (x , t) NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccIdle       {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccWreq       {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccAwait      {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) (NS.ccWfi ps)   {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccInt        {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccWdone      {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccMust       {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) (NS.ccArf ht)   {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) (NS.ccArb pt)   {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) (NS.ccAin tp)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) (NS.ccAin tp)   {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) NS.ccTerm       {e = apiCS l d recvCSIntersectFound} {a = x , t} refl (ceqCSc17 {x} {t} l d) refl eq)
tscInj-ccAif l d (x , t) (NS.ccAif pt′)  eq
  with (x , t) ≟ pt′
... | yes e  = cong NS.ccAif e
... | no  ne = ⊥-elim (sep (Tcsc l d) (NS.ccAif (x , t)) (NS.ccAif pt′)
                        {e = apiCS l d recvCSIntersectFound} {a = x , t} refl
                        (ceqCSc17 {x} {t} l d) (ccAif-nq l d pt′ (x , t) ne) eq)

-- ROW 11 — `ccAin tp`, at `recvCSIntersectNotFound` (a bare `Tip` index)
tscInj-ccAin : (l : Link) (d : Dir) (tp : Tip) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) (NS.ccAin tp) ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccAin tp ≡ q₂
tscInj-ccAin l d tp NS.ccIdle       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccIdle       {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccWreq       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccWreq       {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccAwait      eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccAwait      {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp (NS.ccWfi ps)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) (NS.ccWfi ps)   {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccInt        eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccInt        {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccWdone      eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccWdone      {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccMust       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccMust       {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp (NS.ccArf ht)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) (NS.ccArf ht)   {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp (NS.ccArb pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) (NS.ccArb pt)   {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp (NS.ccAif pt)   eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) (NS.ccAif pt)   {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp NS.ccTerm       eq = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) NS.ccTerm       {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl (ceqCSc18 {tp} l d) refl eq)
tscInj-ccAin l d tp (NS.ccAin tp′)  eq
  with tp ≟ tp′
... | yes e  = cong NS.ccAin e
... | no  ne = ⊥-elim (sep (Tcsc l d) (NS.ccAin tp) (NS.ccAin tp′)
                        {e = apiCS l d recvCSIntersectNotFound} {a = tp} refl
                        (ceqCSc18 {tp} l d) (ccAin-nq l d tp′ tp ne) eq)

-- ROW 12 — `ccTerm`, the PROBE-LESS terminal: it has no row of its own, so the
-- separation is the `ret`/`react` mismatch and no rival probe is needed
tscInj-ccTerm : (l : Link) (d : Dir) (q₂ : NS.CScPos)
  → NS.tableSpec (Tcsc l d) NS.ccTerm ≡ NS.tableSpec (Tcsc l d) q₂
  → NS.ccTerm ≡ q₂
tscInj-ccTerm l d NS.ccTerm      eq = refl
tscInj-ccTerm l d NS.ccIdle      eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccIdle      refl refl eq)
tscInj-ccTerm l d NS.ccWreq      eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccWreq      refl refl eq)
tscInj-ccTerm l d NS.ccAwait     eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccAwait     refl refl eq)
tscInj-ccTerm l d (NS.ccWfi ps)  eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm (NS.ccWfi ps)  refl refl eq)
tscInj-ccTerm l d NS.ccInt       eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccInt       refl refl eq)
tscInj-ccTerm l d NS.ccWdone     eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccWdone     refl refl eq)
tscInj-ccTerm l d NS.ccMust      eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm NS.ccMust      refl refl eq)
tscInj-ccTerm l d (NS.ccArf ht)  eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm (NS.ccArf ht)  refl refl eq)
tscInj-ccTerm l d (NS.ccArb pt)  eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm (NS.ccArb pt)  refl refl eq)
tscInj-ccTerm l d (NS.ccAif pt)  eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm (NS.ccAif pt)  refl refl eq)
tscInj-ccTerm l d (NS.ccAin tp)  eq = ⊥-elim (tsFinSep (Tcsc l d) NS.ccTerm (NS.ccAin tp)  refl refl eq)

-- *** THE CS-CLIENT TABLE IS COARSE-POSITION INJECTIVE. ***  Twelve rows, and with
-- them the support-distinctness CHECK of `csCnxt`: every ordered pair of distinct
-- coarse positions is separated (asymmetrically for the one nested pair
-- `ccMust ⊊ ccAwait`, structurally for the terminal `ccTerm`).
tscInj : (l : Link) (d : Dir) → TscInj l d
tscInj l d NS.ccIdle      q₂ eq = tscInj-ccIdle  l d q₂ eq
tscInj l d NS.ccWreq      q₂ eq = tscInj-ccWreq  l d q₂ eq
tscInj l d NS.ccAwait     q₂ eq = tscInj-ccAwait l d q₂ eq
tscInj l d (NS.ccWfi ps)  q₂ eq = tscInj-ccWfi   l d ps q₂ eq
tscInj l d NS.ccInt       q₂ eq = tscInj-ccInt   l d q₂ eq
tscInj l d NS.ccWdone     q₂ eq = tscInj-ccWdone l d q₂ eq
tscInj l d NS.ccMust      q₂ eq = tscInj-ccMust  l d q₂ eq
tscInj l d (NS.ccArf ht)  q₂ eq = tscInj-ccArf   l d ht q₂ eq
tscInj l d (NS.ccArb pt)  q₂ eq = tscInj-ccArb   l d pt q₂ eq
tscInj l d (NS.ccAif pt)  q₂ eq = tscInj-ccAif   l d pt q₂ eq
tscInj l d (NS.ccAin tp)  q₂ eq = tscInj-ccAin   l d tp q₂ eq
tscInj l d NS.ccTerm      q₂ eq = tscInj-ccTerm  l d q₂ eq

------------------------------------------------------------------------
-- §3  COARSE INJECTIVITY OF THE CS-SERVER TABLE — all thirteen rows.
--
-- The same three shapes as §2, with the counts the other way round: the SERVER's
-- five wire-send positions all sit at the `input` key, so each of them needs the
-- other four's refusal helpers, and four of the five are value-indexed.  The nested
-- pair here is `csMust ⊊ csCanAwait` (the server's `sendCSAwaitReply` is the offer
-- `csMust` lacks), and `csTerm` is the probe-less terminal.
------------------------------------------------------------------------

-- the `csWrf` wire-send refuses every `input` payload but its own
csWrf-nq : (l : Link) (d : Dir) (h : Header) (t : Tip) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)))
  → NS.csSnxt l d (NS.csWrf (h , t)) (Payload , input l d N2N_ChainSync) pl ≡ nothing
csWrf-nq l d h t pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `csWrb` wire-send
csWrb-nq : (l : Link) (d : Dir) (x : Point) (t : Tip) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward x t)))
  → NS.csSnxt l d (NS.csWrb (x , t)) (Payload , input l d N2N_ChainSync) pl ≡ nothing
csWrb-nq l d x t pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `csWar` wire-send (no index: its payload is closed)
csWar-nq : (l : Link) (d : Dir) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply))
  → NS.csSnxt l d NS.csWar (Payload , input l d N2N_ChainSync) pl ≡ nothing
csWar-nq l d pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … the `csWif` wire-send
csWif-nq : (l : Link) (d : Dir) (x : Point) (t : Tip) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound x t)))
  → NS.csSnxt l d (NS.csWif (x , t)) (Payload , input l d N2N_ChainSync) pl ≡ nothing
csWif-nq l d x t pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- … and the `csWin` wire-send
csWin-nq : (l : Link) (d : Dir) (t : Tip) (pl : Payload)
  → ¬ (pl ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound t)))
  → NS.csSnxt l d (NS.csWin t) (Payload , input l d N2N_ChainSync) pl ≡ nothing
csWin-nq l d t pl ne
  rewrite ≟-yes-refl l | ≟-yes-refl d | proj₂ (≟-noΣ ne) = refl

-- the `csAfi` api emit refuses every `reqCSFindIntersect` value but its own (the
-- `List Point` instance spelled, as in §2's family clause)
csAfi-nq : (l : Link) (d : Dir) (ps v : List Point) → ¬ (v ≡ ps)
  → NS.csSnxt l d (NS.csAfi ps) (ApiCSCar reqCSFindIntersect , apiCS l d reqCSFindIntersect) v
    ≡ nothing
csAfi-nq l d ps v ne
  rewrite ≟-yes-refl l | ≟-yes-refl d
  | proj₂ (≟-noΣ ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ ne) = refl

-- ROW 1 — `csIdle` is the server's ONLY `output`-keyed position, so its
-- `MsgCSRequestNext` read separates it from all twelve rivals
tssInj-csIdle : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csIdle ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csIdle ≡ q₂
tssInj-csIdle l d NS.csIdle          eq = refl
tssInj-csIdle l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csAreq          {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csCanAwait      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csIdle (NS.csAfi ps)      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csInt           {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csDdone         {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csMust          {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csIdle (NS.csWrf ht)      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csIdle (NS.csWrb pt)      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csWar           {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csIdle (NS.csWif pt)      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csIdle (NS.csWin tp)      {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)
tssInj-csIdle l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csIdle NS.csTerm          {e = output l d N2N_ChainSync} {a = time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext} refl (ceqCSs01 {time₀} {FromInitiator} {length₀} l d) refl eq)

-- ROW 2 — `csAreq`'s own `reqCSRequestNext` emit
tssInj-csAreq : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csAreq ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csAreq ≡ q₂
tssInj-csAreq l d NS.csAreq          eq = refl
tssInj-csAreq l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csIdle          {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csCanAwait      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csAreq (NS.csAfi ps)      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csInt           {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csDdone         {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csMust          {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csAreq (NS.csWrf ht)      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csAreq (NS.csWrb pt)      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csWar           {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csAreq (NS.csWif pt)      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csAreq (NS.csWin tp)      {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)
tssInj-csAreq l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csAreq NS.csTerm          {e = apiCS l d reqCSRequestNext} {a = tt} refl (ceqCSs11 {tt} l d) refl eq)

-- ROW 3 — `csCanAwait`, the LARGER half of the nested pair: its
-- `sendCSAwaitReply` offer is the one `csMust` does not have
tssInj-csCanAwait : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csCanAwait ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csCanAwait ≡ q₂
tssInj-csCanAwait l d NS.csCanAwait      eq = refl
tssInj-csCanAwait l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csIdle          {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csAreq          {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait (NS.csAfi ps)      {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csInt           {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csDdone         {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csMust          {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait (NS.csWrf ht)      {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait (NS.csWrb pt)      {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csWar           {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait (NS.csWif pt)      {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait (NS.csWin tp)      {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)
tssInj-csCanAwait l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csTerm          {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl eq)

-- ROW 4 — `csAfi ps`: the server's one VALUE-INDEXED api emit
tssInj-csAfi : (l : Link) (d : Dir) (ps : List Point) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) (NS.csAfi ps) ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csAfi ps ≡ q₂
tssInj-csAfi l d ps NS.csIdle          eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csIdle          {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csAreq          eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csAreq          {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csCanAwait      {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csInt           eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csInt           {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csDdone         eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csDdone         {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csMust          eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csMust          {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) (NS.csWrf ht)      {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) (NS.csWrb pt)      {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csWar           eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csWar           {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) (NS.csWif pt)      {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) (NS.csWin tp)      {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps NS.csTerm          eq = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) NS.csTerm          {e = apiCS l d reqCSFindIntersect} {a = ps} refl (ceqCSs12 {ps} l d) refl eq)
tssInj-csAfi l d ps (NS.csAfi ps′)     eq
  with _≟_ ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ ps ps′
... | yes e  = cong NS.csAfi e
... | no  ne = ⊥-elim (sep (Tcss l d) (NS.csAfi ps) (NS.csAfi ps′)
                        {e = apiCS l d reqCSFindIntersect} {a = ps} refl
                        (ceqCSs12 {ps} l d) (csAfi-nq l d ps′ ps ne) eq)

-- ROW 5 — `csInt`'s `sendCSIntersectNotFound` emit (the probe needs a Tip)
tssInj-csInt : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csInt ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csInt ≡ q₂
tssInj-csInt l d NS.csInt           eq = refl
tssInj-csInt l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csIdle          {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csAreq          {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csCanAwait      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csInt (NS.csAfi ps)      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csDdone         {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csMust          {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csInt (NS.csWrf ht)      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csInt (NS.csWrb pt)      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csWar           {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csInt (NS.csWif pt)      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csInt (NS.csWin tp)      {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)
tssInj-csInt l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csInt NS.csTerm          {e = apiCS l d sendCSIntersectNotFound} {a = tip blkA} refl (ceqCSs10 {tip blkA} l d) refl eq)

-- ROW 6 — `csDdone`, the server's node-local `done` handshake (its own key)
tssInj-csDdone : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csDdone ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csDdone ≡ q₂
tssInj-csDdone l d NS.csDdone         eq = refl
tssInj-csDdone l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csIdle          {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csAreq          {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csCanAwait      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csDdone (NS.csAfi ps)      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csInt           {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csMust          {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csDdone (NS.csWrf ht)      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csDdone (NS.csWrb pt)      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csWar           {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csDdone (NS.csWif pt)      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csDdone (NS.csWin tp)      {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)
tssInj-csDdone l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csDdone NS.csTerm          {e = done l d N2N_ChainSync} {a = tt} refl (ceqCSs13 {tt} l d) refl eq)

-- ROW 7 — `csMust`, the SMALLER half of the nested pair: the `csCanAwait` clause
-- runs the LARGER side's probe and uses the equation symmetrically
tssInj-csMust : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csMust ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csMust ≡ q₂
tssInj-csMust l d NS.csMust          eq = refl
tssInj-csMust l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csCanAwait NS.csMust {e = apiCS l d sendCSAwaitReply} {a = tt} refl (ceqCSs06 {tt} l d) refl (sym eq))
tssInj-csMust l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csIdle          {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csAreq          {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csMust (NS.csAfi ps)      {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csInt           {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csDdone         {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d (NS.csWrf ht)      eq = ⊥-elim (sep (Tcss l d) NS.csMust (NS.csWrf ht)      {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d (NS.csWrb pt)      eq = ⊥-elim (sep (Tcss l d) NS.csMust (NS.csWrb pt)      {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d NS.csWar           eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csWar           {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d (NS.csWif pt)      eq = ⊥-elim (sep (Tcss l d) NS.csMust (NS.csWif pt)      {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d (NS.csWin tp)      eq = ⊥-elim (sep (Tcss l d) NS.csMust (NS.csWin tp)      {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)
tssInj-csMust l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csMust NS.csTerm          {e = apiCS l d sendCSRollForward} {a = header blkA , tip blkA} refl (ceqCSs07 {header blkA , tip blkA} l d) refl eq)

-- ROW 8 — `csWrf (h , t)`: a wire-send, so the four sibling wire-sends need their
-- refusal helpers and the family rival needs the index `≟` first
tssInj-csWrf : (l : Link) (d : Dir) (ht : Header × Tip) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) (NS.csWrf ht) ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csWrf ht ≡ q₂
tssInj-csWrf l d (h , t) NS.csIdle          eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csIdle          {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) NS.csAreq          eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csAreq          {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csCanAwait      {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) (NS.csAfi ps)      {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) NS.csInt           eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csInt           {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) NS.csDdone         eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csDdone         {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) NS.csMust          eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csMust          {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) (NS.csWrb (x , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) (NS.csWrb (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) (csWrb-nq l d x u _ (λ ())) eq)
tssInj-csWrf l d (h , t) NS.csWar           eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csWar           {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) (csWar-nq l d _ (λ ())) eq)
tssInj-csWrf l d (h , t) (NS.csWif (x , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) (NS.csWif (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) (csWif-nq l d x u _ (λ ())) eq)
tssInj-csWrf l d (h , t) (NS.csWin u)       eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) (NS.csWin u)       {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) (csWin-nq l d u _ (λ ())) eq)
tssInj-csWrf l d (h , t) NS.csTerm          eq = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) NS.csTerm          {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d) refl eq)
tssInj-csWrf l d (h , t) (NS.csWrf (h′ , t′)) eq
  with (h , t) ≟ (h′ , t′)
... | yes e  = cong NS.csWrf e
... | no  ne = ⊥-elim (sep (Tcss l d) (NS.csWrf (h , t)) (NS.csWrf (h′ , t′))
                        {e = input l d N2N_ChainSync} refl (ceqCSs14 {h} {t} l d)
                        (csWrf-nq l d h′ t′ _ (λ e → ne (rf-inj e))) eq)
  where
    -- the payload determines the carried header/tip pair
    rf-inj : (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
             ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h′ t′))
           → (h , t) ≡ (h′ , t′)
    rf-inj refl = refl

-- ROW 9 — `csWrb (x , t)`, the same shape at `MsgCSRollBackward`
tssInj-csWrb : (l : Link) (d : Dir) (pt : Point × Tip) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) (NS.csWrb pt) ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csWrb pt ≡ q₂
tssInj-csWrb l d (x , t) NS.csIdle          eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csIdle          {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) NS.csAreq          eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csAreq          {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csCanAwait      {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) (NS.csAfi ps)      {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) NS.csInt           eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csInt           {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) NS.csDdone         eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csDdone         {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) NS.csMust          eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csMust          {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) (NS.csWrf (h , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) (NS.csWrf (h , u)) {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) (csWrf-nq l d h u _ (λ ())) eq)
tssInj-csWrb l d (x , t) NS.csWar           eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csWar           {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) (csWar-nq l d _ (λ ())) eq)
tssInj-csWrb l d (x , t) (NS.csWif (y , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) (NS.csWif (y , u)) {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) (csWif-nq l d y u _ (λ ())) eq)
tssInj-csWrb l d (x , t) (NS.csWin u)       eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) (NS.csWin u)       {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) (csWin-nq l d u _ (λ ())) eq)
tssInj-csWrb l d (x , t) NS.csTerm          eq = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) NS.csTerm          {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d) refl eq)
tssInj-csWrb l d (x , t) (NS.csWrb (x′ , t′)) eq
  with (x , t) ≟ (x′ , t′)
... | yes e  = cong NS.csWrb e
... | no  ne = ⊥-elim (sep (Tcss l d) (NS.csWrb (x , t)) (NS.csWrb (x′ , t′))
                        {e = input l d N2N_ChainSync} refl (ceqCSs15 {x} {t} l d)
                        (csWrb-nq l d x′ t′ _ (λ e → ne (rb-inj e))) eq)
  where
    -- the payload determines the carried point/tip pair
    rb-inj : (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward x t))
             ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward x′ t′))
           → (x , t) ≡ (x′ , t′)
    rb-inj refl = refl

-- ROW 10 — `csWar`, the one wire-send with no index (its payload is closed)
tssInj-csWar : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csWar ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csWar ≡ q₂
tssInj-csWar l d NS.csWar           eq = refl
tssInj-csWar l d NS.csIdle          eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csIdle          {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d NS.csAreq          eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csAreq          {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csCanAwait      {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) NS.csWar (NS.csAfi ps)      {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d NS.csInt           eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csInt           {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d NS.csDdone         eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csDdone         {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d NS.csMust          eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csMust          {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)
tssInj-csWar l d (NS.csWrf (h , u)) eq = ⊥-elim (sep (Tcss l d) NS.csWar (NS.csWrf (h , u)) {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) (csWrf-nq l d h u _ (λ ())) eq)
tssInj-csWar l d (NS.csWrb (x , u)) eq = ⊥-elim (sep (Tcss l d) NS.csWar (NS.csWrb (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) (csWrb-nq l d x u _ (λ ())) eq)
tssInj-csWar l d (NS.csWif (x , u)) eq = ⊥-elim (sep (Tcss l d) NS.csWar (NS.csWif (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) (csWif-nq l d x u _ (λ ())) eq)
tssInj-csWar l d (NS.csWin u)       eq = ⊥-elim (sep (Tcss l d) NS.csWar (NS.csWin u)       {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) (csWin-nq l d u _ (λ ())) eq)
tssInj-csWar l d NS.csTerm          eq = ⊥-elim (sep (Tcss l d) NS.csWar NS.csTerm          {e = input l d N2N_ChainSync} refl (ceqCSs16 l d) refl eq)

-- ROW 11 — `csWif (x , t)`, at `MsgCSIntersectFound`
tssInj-csWif : (l : Link) (d : Dir) (pt : Point × Tip) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) (NS.csWif pt) ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csWif pt ≡ q₂
tssInj-csWif l d (x , t) NS.csIdle          eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csIdle          {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) NS.csAreq          eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csAreq          {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csCanAwait      {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) (NS.csAfi ps)      {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) NS.csInt           eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csInt           {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) NS.csDdone         eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csDdone         {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) NS.csMust          eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csMust          {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) (NS.csWrf (h , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) (NS.csWrf (h , u)) {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) (csWrf-nq l d h u _ (λ ())) eq)
tssInj-csWif l d (x , t) (NS.csWrb (y , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) (NS.csWrb (y , u)) {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) (csWrb-nq l d y u _ (λ ())) eq)
tssInj-csWif l d (x , t) NS.csWar           eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csWar           {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) (csWar-nq l d _ (λ ())) eq)
tssInj-csWif l d (x , t) (NS.csWin u)       eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) (NS.csWin u)       {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) (csWin-nq l d u _ (λ ())) eq)
tssInj-csWif l d (x , t) NS.csTerm          eq = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) NS.csTerm          {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d) refl eq)
tssInj-csWif l d (x , t) (NS.csWif (x′ , t′)) eq
  with (x , t) ≟ (x′ , t′)
... | yes e  = cong NS.csWif e
... | no  ne = ⊥-elim (sep (Tcss l d) (NS.csWif (x , t)) (NS.csWif (x′ , t′))
                        {e = input l d N2N_ChainSync} refl (ceqCSs17 {x} {t} l d)
                        (csWif-nq l d x′ t′ _ (λ e → ne (if-inj e))) eq)
  where
    -- the payload determines the carried point/tip pair
    if-inj : (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound x t))
             ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound x′ t′))
           → (x , t) ≡ (x′ , t′)
    if-inj refl = refl

-- ROW 12 — `csWin t`, at `MsgCSIntersectNotFound` (a bare `Tip` index)
tssInj-csWin : (l : Link) (d : Dir) (t : Tip) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) (NS.csWin t) ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csWin t ≡ q₂
tssInj-csWin l d t NS.csIdle          eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csIdle          {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t NS.csAreq          eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csAreq          {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t NS.csCanAwait      eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csCanAwait      {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t (NS.csAfi ps)      eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) (NS.csAfi ps)      {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t NS.csInt           eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csInt           {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t NS.csDdone         eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csDdone         {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t NS.csMust          eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csMust          {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t (NS.csWrf (h , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) (NS.csWrf (h , u)) {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) (csWrf-nq l d h u _ (λ ())) eq)
tssInj-csWin l d t (NS.csWrb (x , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) (NS.csWrb (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) (csWrb-nq l d x u _ (λ ())) eq)
tssInj-csWin l d t NS.csWar           eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csWar           {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) (csWar-nq l d _ (λ ())) eq)
tssInj-csWin l d t (NS.csWif (x , u)) eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) (NS.csWif (x , u)) {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) (csWif-nq l d x u _ (λ ())) eq)
tssInj-csWin l d t NS.csTerm          eq = ⊥-elim (sep (Tcss l d) (NS.csWin t) NS.csTerm          {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d) refl eq)
tssInj-csWin l d t (NS.csWin t′) eq
  with t ≟ t′
... | yes e  = cong NS.csWin e
... | no  ne = ⊥-elim (sep (Tcss l d) (NS.csWin t) (NS.csWin t′)
                        {e = input l d N2N_ChainSync} refl (ceqCSs18 {t} l d)
                        (csWin-nq l d t′ _ (λ e → ne (in-inj e))) eq)
  where
    -- the payload determines the carried tip
    in-inj : (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound t))
             ≡ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound t′))
           → t ≡ t′
    in-inj refl = refl

-- ROW 13 — `csTerm`, the server's PROBE-LESS terminal
tssInj-csTerm : (l : Link) (d : Dir) (q₂ : NS.CSsPos)
  → NS.tableSpec (Tcss l d) NS.csTerm ≡ NS.tableSpec (Tcss l d) q₂
  → NS.csTerm ≡ q₂
tssInj-csTerm l d NS.csTerm          eq = refl
tssInj-csTerm l d NS.csIdle          eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csIdle          refl refl eq)
tssInj-csTerm l d NS.csAreq          eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csAreq          refl refl eq)
tssInj-csTerm l d NS.csCanAwait      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csCanAwait      refl refl eq)
tssInj-csTerm l d (NS.csAfi ps)      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm (NS.csAfi ps)      refl refl eq)
tssInj-csTerm l d NS.csInt           eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csInt           refl refl eq)
tssInj-csTerm l d NS.csDdone         eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csDdone         refl refl eq)
tssInj-csTerm l d NS.csMust          eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csMust          refl refl eq)
tssInj-csTerm l d (NS.csWrf ht)      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm (NS.csWrf ht)      refl refl eq)
tssInj-csTerm l d (NS.csWrb pt)      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm (NS.csWrb pt)      refl refl eq)
tssInj-csTerm l d NS.csWar           eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm NS.csWar           refl refl eq)
tssInj-csTerm l d (NS.csWif pt)      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm (NS.csWif pt)      refl refl eq)
tssInj-csTerm l d (NS.csWin tp)      eq = ⊥-elim (tsFinSep (Tcss l d) NS.csTerm (NS.csWin tp)      refl refl eq)

-- *** THE CS-SERVER TABLE IS COARSE-POSITION INJECTIVE. ***  Thirteen rows, and
-- with them the support-distinctness CHECK of `csSnxt`.
tssInj : (l : Link) (d : Dir) → TssInj l d
tssInj l d NS.csIdle      q₂ eq = tssInj-csIdle     l d q₂ eq
tssInj l d NS.csAreq      q₂ eq = tssInj-csAreq     l d q₂ eq
tssInj l d NS.csCanAwait  q₂ eq = tssInj-csCanAwait l d q₂ eq
tssInj l d (NS.csAfi ps)  q₂ eq = tssInj-csAfi      l d ps q₂ eq
tssInj l d NS.csInt       q₂ eq = tssInj-csInt      l d q₂ eq
tssInj l d NS.csDdone     q₂ eq = tssInj-csDdone    l d q₂ eq
tssInj l d NS.csMust      q₂ eq = tssInj-csMust     l d q₂ eq
tssInj l d (NS.csWrf ht)  q₂ eq = tssInj-csWrf      l d ht q₂ eq
tssInj l d (NS.csWrb pt)  q₂ eq = tssInj-csWrb      l d pt q₂ eq
tssInj l d NS.csWar       q₂ eq = tssInj-csWar      l d q₂ eq
tssInj l d (NS.csWif pt)  q₂ eq = tssInj-csWif      l d pt q₂ eq
tssInj l d (NS.csWin tp)  q₂ eq = tssInj-csWin      l d tp q₂ eq
tssInj l d NS.csTerm      q₂ eq = tssInj-csTerm     l d q₂ eq

------------------------------------------------------------------------
-- §4  *** THE ROW, AND THE SIX-LINE EVENT-GENERIC WRAPPER. ***
--
-- `CScRow`/`CSsRow` are the CS twins of `PipeBundleEvo.CliApiRow`/`SrvApiRow`
-- (`:169-181`): the FIRED COARSE ROW of a peer at its own key, stated over the FINE
-- positions the bundle's slots carry.  `cscRow-of`/`cssRow-of` are the whole of the
-- recovery: they CALL `tableSpec-ev-inv` and the §2/§3 injectivity, mirror no frozen
-- code, and never touch the bundle or `csc-hstep`.  The event is ARBITRARY, so one
-- lemma per peer serves the five `apiCS` driver events, both io labels and `doneCS`.
------------------------------------------------------------------------

-- the fired coarse row of a CS CLIENT peer at key `(l , d)`, event-generic
CScRow : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         (pos pos′ : SN.CScPos) → Set
CScRow l d {X} e a pos pos′ =
  NS.csCnxt l d (coarsenCSc pos) (X , e) a ≡ just (coarsenCSc pos′)

-- … and of a CS SERVER peer
CSsRow : (l : Link) (d : Dir) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
         (pos pos′ : SN.CSsPos) → Set
CSsRow l d {X} e a pos pos′ =
  NS.csSnxt l d (coarsenCSs pos) (X , e) a ≡ just (coarsenCSs pos′)

-- *** THE WRAPPER (client). ***  Any abstract CS-client step whose target is KNOWN
-- to be a fine successor position — which is exactly what the frozen
-- `decCSc-ev-prod-abs` hands out — reports its fired row.
cscRow-of : (l : Link) (d : Dir) (pos pos′ : SN.CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → M ≡ absCSc l d pos′
  → CScRow l d e a pos pos′
cscRow-of l d pos pos′ {X} {e} {a} step Meq
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc pos) step
... | q′ , ceq , Meq′ =
      subst (λ z → NS.csCnxt l d (coarsenCSc pos) (X , e) a ≡ just z)
            (tscInj l d q′ (coarsenCSc pos′) (trans (sym Meq′) Meq)) ceq

-- *** THE WRAPPER (server). ***  The same six lines at the other peer.
cssRow-of : (l : Link) (d : Dir) (pos pos′ : SN.CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → M ≡ absCSs l d pos′
  → CSsRow l d e a pos pos′
cssRow-of l d pos pos′ {X} {e} {a} step Meq
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs pos) step
... | q′ , ceq , Meq′ =
      subst (λ z → NS.csSnxt l d (coarsenCSs pos) (X , e) a ≡ just z)
            (tssInj l d q′ (coarsenCSs pos′) (trans (sym Meq′) Meq)) ceq

-- the CS client's fired row off the FROZEN peer inversion — the peer layer, CALLING
-- and never transcribing (`SysIoLink5.decCSc-ev-prod-abs` supplies the fine
-- successor, the concrete weak run and `M ≡ absCSc l d pos′`)
cscRowInv : (l : Link) (d : Dir) (pos : SN.CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSc l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ SN.CScPos ]
      (SN.decCSc l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► SN.decCSc l d pos′)
      × (M ≡ absCSc l d pos′)
      × CScRow l d (ιCS e₁) a pos pos′
cscRowInv l d pos step with decCSc-ev-prod-abs l d pos step
... | pos′ , run , Meq = pos′ , run , Meq , cscRow-of l d pos pos′ step Meq

-- … and the CS server's
cssRowInv : (l : Link) (d : Dir) (pos : SN.CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSs l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ SN.CSsPos ]
      (SN.decCSs l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► SN.decCSs l d pos′)
      × (M ≡ absCSs l d pos′)
      × CSsRow l d (ιCS e₁) a pos pos′
cssRowInv l d pos step with decCSs-ev-prod-abs l d pos step
... | pos′ , run , Meq = pos′ , run , Meq , cssRow-of l d pos pos′ step Meq

-- a fired row PINS the event's key to the peer's own `(l , d)`: a foreign link or
-- direction makes the table answer `nothing` (the two banked `-no` pins)
cscRow-key : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} {q′ : NS.CScPos}
  → NS.csCnxt l d q (X , ιCS e₁) a ≡ just q′
  → (csEvLink e₁ ≡ l) × (csEvDir e₁ ≡ d)
cscRow-key l d q e₁ row with csEvLink e₁ ≟ l | csEvDir e₁ ≟ d
... | yes el | yes ed = el , ed
... | yes _  | no  nd = ⊥-elim (nothing-absurd (trans (sym (csCnxt-dir-no  l d q e₁ nd)) row))
... | no  nl | _      = ⊥-elim (nothing-absurd (trans (sym (csCnxt-link-no l d q e₁ nl)) row))

-- … the server's twin
cssRow-key : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} {q′ : NS.CSsPos}
  → NS.csSnxt l d q (X , ιCS e₁) a ≡ just q′
  → (csEvLink e₁ ≡ l) × (csEvDir e₁ ≡ d)
cssRow-key l d q e₁ row with csEvLink e₁ ≟ l | csEvDir e₁ ≟ d
... | yes el | yes ed = el , ed
... | yes _  | no  nd = ⊥-elim (nothing-absurd (trans (sym (csSnxt-dir-no  l d q e₁ nd)) row))
... | no  nl | _      = ⊥-elim (nothing-absurd (trans (sym (csSnxt-link-no l d q e₁ nl)) row))

------------------------------------------------------------------------
-- §4a  THE LABEL-DIRECTED api FACTS, in the shape the api cone threads.
--
-- Exactly `PipeBundleEvo.CliApiRow`/`SrvApiRow` and the cone's
-- `CliApiRowP`/`SrvApiRowP` with the CS tables substituted: the ROW carries the
-- fired key's two equations, and the `P` fact is "the peer is FIXED, or its coarse
-- table fired at this label".  Two channels have CS rows — `apiCS` for both peers
-- and `done … N2N_ChainSync` (the server's `csDdone` handshake; a CS CLIENT has no
-- `done` row at all, so its `done` disjunct is simply never taken).
------------------------------------------------------------------------

-- the CS CLIENT's api-channel row, at the fired key
CScApiRow : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (pos pos′ : SN.CScPos)
            (m : ApiCSTag) (a : ApiCSCar m) → Set
CScApiRow k kd l₀ d₀ pos pos′ m a =
  (l₀ ≡ k) × (d₀ ≡ kd) × CScRow k kd (apiCS l₀ d₀ m) a pos pos′

-- … and on the `done` channel (the table's `csDdone`-shaped row)
CScDoneRow : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (pos pos′ : SN.CScPos)
             (a : ⊤) → Set
CScDoneRow k kd l₀ d₀ pos pos′ a =
  (l₀ ≡ k) × (d₀ ≡ kd) × CScRow k kd (done l₀ d₀ N2N_ChainSync) a pos pos′

-- the CS SERVER's api-channel row
CSsApiRow : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (pos pos′ : SN.CSsPos)
            (m : ApiCSTag) (a : ApiCSCar m) → Set
CSsApiRow k kd l₀ d₀ pos pos′ m a =
  (l₀ ≡ k) × (d₀ ≡ kd) × CSsRow k kd (apiCS l₀ d₀ m) a pos pos′

-- … and its `done`-channel row (`csDdone → csTerm`)
CSsDoneRow : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (pos pos′ : SN.CSsPos)
             (a : ⊤) → Set
CSsDoneRow k kd l₀ d₀ pos pos′ a =
  (l₀ ≡ k) × (d₀ ≡ kd) × CSsRow k kd (done l₀ d₀ N2N_ChainSync) a pos pos′

-- the CLIENT's api-axis adjacency FACT, label-directed
CScApiRowP : (k : Link) (kd : Dir) (pos pos′ : SN.CScPos)
             {X : Set 0ℓ} → Net_Api Payload X → X → Set
CScApiRowP k kd pos pos′ (apiCS l₀ d₀ m) v =
  (pos ≡ pos′) ⊎ CScApiRow k kd l₀ d₀ pos pos′ m v
CScApiRowP k kd pos pos′ (done l₀ d₀ N2N_ChainSync) v =
  (pos ≡ pos′) ⊎ CScDoneRow k kd l₀ d₀ pos pos′ v
CScApiRowP k kd pos pos′ _ _ = pos ≡ pos′

-- … and the SERVER's
CSsApiRowP : (k : Link) (kd : Dir) (pos pos′ : SN.CSsPos)
             {X : Set 0ℓ} → Net_Api Payload X → X → Set
CSsApiRowP k kd pos pos′ (apiCS l₀ d₀ m) v =
  (pos ≡ pos′) ⊎ CSsApiRow k kd l₀ d₀ pos pos′ m v
CSsApiRowP k kd pos pos′ (done l₀ d₀ N2N_ChainSync) v =
  (pos ≡ pos′) ⊎ CSsDoneRow k kd l₀ d₀ pos pos′ v
CSsApiRowP k kd pos pos′ _ _ = pos ≡ pos′

-- a CS client that did NOT move satisfies its adjacency fact at EVERY label (the
-- label dispatch is unavoidable — the fact itself is label-directed)
cscApiRow-fix : (k : Link) (kd : Dir) (pos : SN.CScPos)
                {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → CScApiRowP k kd pos pos e a
cscApiRow-fix k kd pos (apiCS _ _ _) a = inj₁ refl
cscApiRow-fix k kd pos (done _ _ N2N_ChainSync)    a = inj₁ refl
cscApiRow-fix k kd pos (done _ _ N2N_BlockFetch)   a = refl
cscApiRow-fix k kd pos (done _ _ N2N_KeepAlive)    a = refl
cscApiRow-fix k kd pos (done _ _ N2N_TxSubmission) a = refl
cscApiRow-fix k kd pos (done _ _ N2N_LeiosNotify)  a = refl
cscApiRow-fix k kd pos (done _ _ N2N_LeiosFetch)   a = refl
cscApiRow-fix k kd pos (apiBF _ _ _)  a = refl
cscApiRow-fix k kd pos (apiKA _ _ _)  a = refl
cscApiRow-fix k kd pos (apiTS _ _ _)  a = refl
cscApiRow-fix k kd pos (apiLN _ _ _)  a = refl
cscApiRow-fix k kd pos (apiLF _ _ _)  a = refl
cscApiRow-fix k kd pos (input  _ _ _) a = refl
cscApiRow-fix k kd pos (output _ _ _) a = refl
cscApiRow-fix k kd pos (sndmsg _ _ _) a = refl
cscApiRow-fix k kd pos (rcvmsg _ _ _) a = refl
cscApiRow-fix k kd pos (tx     _ _ _) a = refl
cscApiRow-fix k kd pos (sndack _ _ _) a = refl
cscApiRow-fix k kd pos (rcvack _ _ _) a = refl
cscApiRow-fix k kd pos (ack    _ _ _) a = refl
cscApiRow-fix k kd pos (store _ _ _) a = refl
cscApiRow-fix k kd pos (env _ _ _) a = refl
cscApiRow-fix k kd pos (break  _)     a = refl

-- … and a CS server that did not move
cssApiRow-fix : (k : Link) (kd : Dir) (pos : SN.CSsPos)
                {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → CSsApiRowP k kd pos pos e a
cssApiRow-fix k kd pos (apiCS _ _ _) a = inj₁ refl
cssApiRow-fix k kd pos (done _ _ N2N_ChainSync)    a = inj₁ refl
cssApiRow-fix k kd pos (done _ _ N2N_BlockFetch)   a = refl
cssApiRow-fix k kd pos (done _ _ N2N_KeepAlive)    a = refl
cssApiRow-fix k kd pos (done _ _ N2N_TxSubmission) a = refl
cssApiRow-fix k kd pos (done _ _ N2N_LeiosNotify)  a = refl
cssApiRow-fix k kd pos (done _ _ N2N_LeiosFetch)   a = refl
cssApiRow-fix k kd pos (apiBF _ _ _)  a = refl
cssApiRow-fix k kd pos (apiKA _ _ _)  a = refl
cssApiRow-fix k kd pos (apiTS _ _ _)  a = refl
cssApiRow-fix k kd pos (apiLN _ _ _)  a = refl
cssApiRow-fix k kd pos (apiLF _ _ _)  a = refl
cssApiRow-fix k kd pos (input  _ _ _) a = refl
cssApiRow-fix k kd pos (output _ _ _) a = refl
cssApiRow-fix k kd pos (sndmsg _ _ _) a = refl
cssApiRow-fix k kd pos (rcvmsg _ _ _) a = refl
cssApiRow-fix k kd pos (tx     _ _ _) a = refl
cssApiRow-fix k kd pos (sndack _ _ _) a = refl
cssApiRow-fix k kd pos (rcvack _ _ _) a = refl
cssApiRow-fix k kd pos (ack    _ _ _) a = refl
cssApiRow-fix k kd pos (store _ _ _) a = refl
cssApiRow-fix k kd pos (env _ _ _) a = refl
cssApiRow-fix k kd pos (break  _)     a = refl

-- an `apiCS`-label fired row IS the client's label-directed api fact (the key
-- equations come from the row itself, via the two `-no` pins)
cscApiRowP-api : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                 (a : ApiCSCar m) (pos pos′ : SN.CScPos)
               → CScRow k kd (apiCS l₀ d₀ m) a pos pos′
               → CScApiRowP k kd pos pos′ (apiCS l₀ d₀ m) a
cscApiRowP-api k kd l₀ d₀ m a pos pos′ row =
  inj₂ (proj₁ pin , proj₂ pin , row)
  where pin = cscRow-key k kd (coarsenCSc pos) (CS.apiCSev l₀ d₀ m) row

-- … at the `done … N2N_ChainSync` label
cscApiRowP-done : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (a : ⊤)
                  (pos pos′ : SN.CScPos)
                → CScRow k kd (done l₀ d₀ N2N_ChainSync) a pos pos′
                → CScApiRowP k kd pos pos′ (done l₀ d₀ N2N_ChainSync) a
cscApiRowP-done k kd l₀ d₀ a pos pos′ row =
  inj₂ (proj₁ pin , proj₂ pin , row)
  where pin = cscRow-key k kd (coarsenCSc pos) (CS.doneCS l₀ d₀) row

-- … and the server's two
cssApiRowP-api : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (m : ApiCSTag)
                 (a : ApiCSCar m) (pos pos′ : SN.CSsPos)
               → CSsRow k kd (apiCS l₀ d₀ m) a pos pos′
               → CSsApiRowP k kd pos pos′ (apiCS l₀ d₀ m) a
cssApiRowP-api k kd l₀ d₀ m a pos pos′ row =
  inj₂ (proj₁ pin , proj₂ pin , row)
  where pin = cssRow-key k kd (coarsenCSs pos) (CS.apiCSev l₀ d₀ m) row

cssApiRowP-done : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (a : ⊤)
                  (pos pos′ : SN.CSsPos)
                → CSsRow k kd (done l₀ d₀ N2N_ChainSync) a pos pos′
                → CSsApiRowP k kd pos pos′ (done l₀ d₀ N2N_ChainSync) a
cssApiRowP-done k kd l₀ d₀ a pos pos′ row =
  inj₂ (proj₁ pin , proj₂ pin , row)
  where pin = cssRow-key k kd (coarsenCSs pos) (CS.doneCS l₀ d₀) row

------------------------------------------------------------------------
-- §4b  *** THE PER-KEY SOURCE/TARGET PIN (T5). ***  A recovered ROW names an
-- EDGE of the coarse table; a consumer of `LiveRelayCS.CSAt` needs the edge's
-- TARGET.  Those are not the same thing, and §4's wrapper cannot close the gap:
-- the row it hands back is
-- `csCnxt l d (coarsenCSc pos) (X , apiCS l d m) a ≡ just (coarsenCSc pos′)` with
-- `pos` a VARIABLE, while the banked `ceqCSc15-18` are stated at the KNOWN source
-- `ccArf ht`.  Coarse injectivity (§2/§3) does not help — it is about `tableSpec`
-- equality, not about which positions answer a key.  What closes it is the
-- ENUMERATION at the key: "at `apiCS l d recvCSRollforward` the only answering
-- position is `ccArf ht`, and its target is `ccIdle`".
--
-- This is the CS twin of `LiveDrvBF.srvReqLands` (`:298-315`, the BF axis's own
-- per-key pin, whose conclusion is likewise the LANDING and not an adjacency) and
-- it is what `LiveChanInv.rowAdj`-shaped plumbing consumes.  Both pins are TOTAL
-- on the position datatype — twelve clauses for the client, thirteen for the
-- server — so a new `NodeSpecs` position is a coverage error here rather than a
-- silently-weakened landing.
--
-- *** (T8c-ii) THE SECTION NOW HAS FIVE MEMBERS, AND THREE OF THEM ARE EDGES rather
-- than landings. ***  `LiveDrvCSD`'s joint node-D adjacency `CliDrvAdj` names the
-- SOURCE of each of its three ChainSync rows as well as the target (`cdReq` is
-- `ccIdle → ccWreq`, `cdRecvF ht` is `ccArf ht → ccIdle`, `cdDone` is `ccIdle →
-- ccWdone`), so its producer needs the whole edge and not just the landing.  Hence
-- `cscRfwEdge`/`cscReqEdge`/`cscDoneEdge` below, at exactly the THREE client keys node
-- D's consume driver ever offers (`SysNode.decCons`: `sendCSRequestNext` at `cp0`,
-- `recvCSRollforward` at `cp1`, `sendCSDone` at `cp5`).  *** `cscRfwLands` is now the
-- second projection of `cscRfwEdge` and NOT a second copy of the same twelve clauses
-- — its type is unchanged, so no consumer moved. ***  The three keys are still the
-- only ones reachable, for the reason the next paragraph gives.
--
-- *** ONLY TWO KEYS ARE BUILT, AND THE REASON IS NOT ECONOMY. ***  The T4 review
-- priced this item at "`cp5`'s four `recvCS*` keys plus the two or three server
-- keys".  Four client keys would be four copies of the same twelve clauses, but
-- only ONE of them can ever fire on the relay's own up hop: `apiCS` events are in
-- `apiES`, so a CS client step needs its node's DRIVER to offer the same event,
-- and the relay's consume driver offers exactly one `recvCS*` — `recvCSRollforward`,
-- at `cp1` (`SysNode.decCons:936-937`).  The other three (`recvCSRollback`,
-- `recvCSIntersectFound`, `recvCSIntersectNotFound`) land at `ccIdle` too and are
-- provable by the identical shape; they are deliberately NOT built because no
-- consumer can reach them.  The server side is the same story: `pp1`'s key is
-- `reqCSRequestNext` and the produce driver's `pp0` row is the only offer of it.
--
-- The four io REFUTATIONS below are the other half of the same enumeration, and
-- they machine-check the gate verification's own claim ("no `input`/`output` row
-- touches `ccIdle` or `csCanAwait`") rather than relaying it.  They are stated at
-- a fully GENERIC key AND channel — `csCnxt`/`csSnxt` have no io clause at those
-- two positions at all, so the table's catch-all (`NodeSpecs:381`/`:490`) answers
-- `nothing` whatever the label's link, direction and `IDs` are.
------------------------------------------------------------------------

-- *** THE CLIENT PIN, AS AN EDGE (T8c-ii: SOURCE as well as target). ***  a fired
-- `recvCSRollforward` row at the CS client's own key can only leave `ccArf ht`, and
-- it lands at `ccIdle`.  The SOURCE half is what `LiveDrvCSD`'s joint-adjacency
-- producer needs (`CliDrvAdj`'s `cdRecvF` names it); the target half is what T7's
-- `cp5` chain needed, and `cscRfwLands` below is now this pin's second projection
-- rather than a second copy of the same twelve clauses
cscRfwEdge : (l : Link) (d : Dir) (q : NS.CScPos) (v : Header × Tip)
             (q′ : NS.CScPos)
           → NS.csCnxt l d q (ApiCSCar recvCSRollforward , apiCS l d recvCSRollforward) v
             ≡ just q′
           → Σ[ ht ∈ Header × Tip ] ((q ≡ NS.ccArf ht) × (q′ ≡ NS.ccIdle))
cscRfwEdge l d NS.ccIdle       v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccWreq       v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccAwait      v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d (NS.ccWfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccWdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccMust       v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d (NS.ccArb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d (NS.ccAif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d (NS.ccAin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d NS.ccTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cscRfwEdge l d (NS.ccArf ht)   v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl with v ≟ ht
...     | no  _   = ⊥-elim (nothing-absurd eq)
...     | yes _   = ht , refl , sym (just-injective eq)

-- … and the LANDING half, T5's original conclusion, now a projection
cscRfwLands : (l : Link) (d : Dir) (q : NS.CScPos) (v : Header × Tip)
              (q′ : NS.CScPos)
            → NS.csCnxt l d q (ApiCSCar recvCSRollforward , apiCS l d recvCSRollforward) v
              ≡ just q′
            → q′ ≡ NS.ccIdle
cscRfwLands l d q v q′ eq = proj₂ (proj₂ (cscRfwEdge l d q v q′ eq))

-- *** (T8c-ii) THE CLIENT'S `sendCSRequestNext` EDGE — `ccIdle → ccWreq`. ***  The
-- ONE row of that key in the whole client table, and the edge `CliDrvAdj`'s `cdReq`
-- names.  *** This is the pin the whole cp6/pp0 discharge turns on: *** without it
-- node D's api carry cannot name the successor position at the `cp0 → cp1` hop, and
-- `CliAt cp1 ccIdle = CliPost ccIdle = ⊥` makes the fixity alternative unusable
cscReqEdge : (l : Link) (d : Dir) (q : NS.CScPos) (v : ApiCSCar sendCSRequestNext)
             (q′ : NS.CScPos)
           → NS.csCnxt l d q (ApiCSCar sendCSRequestNext , apiCS l d sendCSRequestNext) v
             ≡ just q′
           → (q ≡ NS.ccIdle) × (q′ ≡ NS.ccWreq)
cscReqEdge l d NS.ccWreq       v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccAwait      v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d (NS.ccWfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccWdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccMust       v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d (NS.ccArf ht)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d (NS.ccArb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d (NS.ccAif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d (NS.ccAin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cscReqEdge l d NS.ccIdle       v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl = refl , sym (just-injective eq)

-- *** (T8c-ii) … and the `sendCSDone` EDGE — `ccIdle → ccWdone`, `CliDrvAdj`'s
-- `cdDone`. ***  The same twelve clauses at the third and last client key node D's
-- consume driver ever offers (`SysNode.decCons:955-957`, the `cp5` row)
cscDoneEdge : (l : Link) (d : Dir) (q : NS.CScPos) (v : ApiCSCar sendCSDone)
              (q′ : NS.CScPos)
            → NS.csCnxt l d q (ApiCSCar sendCSDone , apiCS l d sendCSDone) v ≡ just q′
            → (q ≡ NS.ccIdle) × (q′ ≡ NS.ccWdone)
cscDoneEdge l d NS.ccWreq       v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccAwait      v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d (NS.ccWfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccWdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccMust       v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d (NS.ccArf ht)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d (NS.ccArb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d (NS.ccAif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d (NS.ccAin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cscDoneEdge l d NS.ccIdle       v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl = refl , sym (just-injective eq)

-- *** THE SERVER PIN. ***  a fired `reqCSRequestNext` row at the CS server's own
-- key LANDS at `csCanAwait` (`pp1`'s equation, and `pp0`'s own sync is the step
-- that fires it)
cssReqLands : (l : Link) (d : Dir) (q : NS.CSsPos) (v : ApiCSCar reqCSRequestNext)
              (q′ : NS.CSsPos)
            → NS.csSnxt l d q (ApiCSCar reqCSRequestNext , apiCS l d reqCSRequestNext) v
              ≡ just q′
            → q′ ≡ NS.csCanAwait
cssReqLands l d NS.csIdle       v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csCanAwait   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d (NS.csAfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csDdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csMust       v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d (NS.csWrf ht)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d (NS.csWrb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csWar        v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d (NS.csWif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d (NS.csWin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cssReqLands l d NS.csAreq       v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _      = ⊥-elim (¬p refl)
... | yes refl | no ¬q  = ⊥-elim (¬q refl)
... | yes refl | yes refl = sym (just-injective eq)

-- `ccIdle` has NO wire-SEND row — at any key, on any channel
cscIdle-in-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               (q′ : NS.CScPos)
             → NS.csCnxt l d NS.ccIdle (Payload , input l₀ d₀ id₀) x ≡ just q′ → ⊥
cscIdle-in-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

-- … and no wire-READ row either, so the CS client's io classes at `cp5` are
-- refutations rather than regions (the `bsBusy` situation, not the `bsWsb` one)
cscIdle-out-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                (q′ : NS.CScPos)
              → NS.csCnxt l d NS.ccIdle (Payload , output l₀ d₀ id₀) x ≡ just q′ → ⊥
cscIdle-out-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

-- `csCanAwait` is io-closed in the same way: its three rows are all `apiCS`
cssCanAwait-in-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                   (q′ : NS.CSsPos)
                 → NS.csSnxt l d NS.csCanAwait (Payload , input l₀ d₀ id₀) x ≡ just q′ → ⊥
cssCanAwait-in-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

cssCanAwait-out-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                    (q′ : NS.CSsPos)
                  → NS.csSnxt l d NS.csCanAwait (Payload , output l₀ d₀ id₀) x ≡ just q′ → ⊥
cssCanAwait-out-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

------------------------------------------------------------------------
-- §4c  *** THE `pp2` REGION'S TABLE FACTS (T6) — THE THIRD PIN AND THE CLOSURE. ***
--
-- The ChainSync twins of `LiveDrvBF` §2's BlockFetch five: the per-key pin
-- (`srvReqLands`) and the four io facts that make a two-position region CLOSED
-- (`srvSend-wsb-stream`, `srvSend-stream-⊥`, `srvRead-wsb-⊥`, `srvRead-stream-⊥`).
--
-- *** WHY `pp2` IS A REGION AND NOT A POSITION, read off `NodeSpecs.csSnxt`. ***
-- `csWar` is entered by exactly ONE row — the relay driver's own `pp1 → pp2` step,
-- `csCanAwait + apiCS sendCSAwaitReply` (`:445-447`) — and it is left by exactly
-- ONE, the server's own `MsgCSAwaitReply` WIRE-SEND (`:472-477`), which lands at
-- `csMust`.  So at the instant the driver ENTERS `pp2` the leg's down CS server is
-- at `csWar` and NOT at `csMust`, and `LiveRelayCS.CSAt`'s `pp2` equation
-- (`≡ csMust`) is one io hop away from anything a carried coupling can state.  What
-- IS carryable is the PAIR, and these five lemmas are what close it: the one io row
-- inside the region stays inside it (`cssWar-in-must`), `csMust` has no io row at
-- all (`cssMust-in-⊥`/`cssMust-out-⊥`), and neither end has a wire-READ row
-- (`cssWar-out-⊥` too).  That is the `{bsWsb, bsStream}` situation verbatim — the
-- region framing of `pp2`, machine-checked here rather than relayed.
--
-- *** AND WHAT THEY DO NOT BUY — READ THIS BEFORE PRICING `pp2` AGAIN. ***  The
-- region is NOT the discharge.  Sharpening `(≡ csWar) ⊎ (≡ csMust)` down to the
-- residual's singleton needs the STABILITY refutation of `csWar` — the
-- `LiveSrvOpen.srvWsb-⊥` twin — and that twin needs a fact NOTHING in this
-- development has: the phase of a ChainSync MEDIUM CELL.  Re-derived by grep at
-- T6, not relayed: `LiveChanInv` has zero `CSs`/`ChainSync` occurrences;
-- `PipeInv.cellUp`/`cellDn` are keyed at `N2N_BlockFetch` (`:424-432`) and
-- `PipeValInv.PipeVal`'s two cell components are those same two cells; a tree-wide
-- grep for a `phase … N2N_ChainSync` finds no site at all.  So the `csWar` half is
-- refutable only behind a CS down-hop CHANNEL invariant — which is `LiveRelayCS`
-- §6(iii)'s framing, not the region one — plus a CS io ladder.  Of that ladder
-- rungs 1 and 2 EXIST (`SysOracle_PeerEvCSBF.aCSs` `:639-644` with the `csWar`
-- wire-send row `ceqCSs16` `:700-704`, and `SysOracle_RouteKaTs.absBundle-CSs-ev`
-- `:1668`); rungs 3-4 (the
-- node and nodes lifts, `LiveIoIntro.srvInNodeB-BD`'s twins) do not, and the two
-- medium kits `LiveIoIntro.medOfferIn`/`medDrainτ` are hard-wired to
-- `N2N_BlockFetch` in their statements.  T6's framing gate priced that inventory
-- past its stop and stopped; the five lemmas below are the framing-INDEPENDENT
-- half, needed under EITHER framing.
--
-- The pin is TOTAL on `CSsPos` (thirteen clauses, no catch-all) for §4b's reason.
-- The four io facts are stated at a generic key AND a generic channel — but
-- `cssWar-in-must` has to DISPATCH on the `IDs`, which is the one place these
-- differ from §4b's four: the table's `csWar` clause names `N2N_ChainSync`
-- LITERALLY, so at a variable channel the application is STUCK rather than
-- `nothing`, while `ccIdle`/`csCanAwait` have no io clause at all and fall straight
-- to the catch-all (`NodeSpecs:490`).
------------------------------------------------------------------------

-- *** THE THIRD PIN. ***  a fired `sendCSAwaitReply` row at the CS server's own key
-- LANDS at `csWar` — the `pp2` region's ENTRY, and the relay driver's `pp1 → pp2`
-- step (`SysNode.decProd:800`) is the step that fires it
cssAwaitLands : (l : Link) (d : Dir) (q : NS.CSsPos) (v : ApiCSCar sendCSAwaitReply)
                (q′ : NS.CSsPos)
              → NS.csSnxt l d q (ApiCSCar sendCSAwaitReply , apiCS l d sendCSAwaitReply) v
                ≡ just q′
              → q′ ≡ NS.csWar
cssAwaitLands l d NS.csIdle       v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csAreq       v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d (NS.csAfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csDdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csMust       v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d (NS.csWrf ht)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d (NS.csWrb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csWar        v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d (NS.csWif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d (NS.csWin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cssAwaitLands l d NS.csCanAwait   v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes refl | no ¬q    = ⊥-elim (¬q refl)
... | yes refl | yes refl = sym (just-injective eq)

-- *** (T11b) THE FOURTH PIN — `sendCSRollForward`. ***  the `pp3` landing's own, and
-- the one thing §6h's field 1 cannot be preserved across `pp2 → pp3` without.
--
-- *** WHY IT NEEDS NO SOURCE-POSITION ANTECEDENT even though the tag has TWO rows. ***
-- `csSnxt`'s `sendCSRollForward` clauses are `csCanAwait` (`NodeSpecs:439-441`) and
-- `csMust` (`:448-450`), and BOTH land at `csWrf ht` with `ht` the FIRED VALUE — so
-- the target is determined by the value alone and the conclusion can name it, which
-- is sharper than the three siblings' fixed positions.  (The `pp2` region's right end
-- `csMust` is the one the relay's own hop actually fires from; `csCanAwait` is here
-- because the table has the row, not because the arm reaches it.)
cssRfwLands : (l : Link) (d : Dir) (q : NS.CSsPos) (v : ApiCSCar sendCSRollForward)
              (q′ : NS.CSsPos)
            → NS.csSnxt l d q (ApiCSCar sendCSRollForward , apiCS l d sendCSRollForward) v
              ≡ just q′
            → q′ ≡ NS.csWrf v
cssRfwLands l d NS.csIdle       v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csAreq       v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d (NS.csAfi ps)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csInt        v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csDdone      v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d (NS.csWrf ht)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d (NS.csWrb pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csWar        v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d (NS.csWif pt)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d (NS.csWin tp)   v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csTerm       v q′ eq = ⊥-elim (nothing-absurd eq)
cssRfwLands l d NS.csCanAwait   v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes refl | no ¬q    = ⊥-elim (¬q refl)
... | yes refl | yes refl = sym (just-injective eq)
cssRfwLands l d NS.csMust       v q′ eq with l ≟ l | d ≟ d
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes refl | no ¬q    = ⊥-elim (¬q refl)
... | yes refl | yes refl = sym (just-injective eq)

-- *** THE ROW THAT CLOSES THE REGION. ***  `csWar`'s ONE io row is the server's own
-- `MsgCSAwaitReply` wire-send, and it lands INSIDE the region, at `csMust`.  This is
-- the whole reason `pp2`'s clause has to be a region: unlike `csCanAwait`, `csWar`
-- is not io-closed on its own.  (`LiveDrvBF.srvSend-wsb-stream`'s twin, one level
-- lower: the CS axis carries the coarse ROW itself rather than an adjacency
-- datatype, so the fact is stated at the table and not at a `SrvSendAdj`.)
cssWar-in-must : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                 (q′ : NS.CSsPos)
               → NS.csSnxt l d NS.csWar (Payload , input l₀ d₀ id₀) x ≡ just q′
               → q′ ≡ NS.csMust
cssWar-in-must l d l₀ d₀ N2N_BlockFetch   x q′ eq = ⊥-elim (nothing-absurd eq)
cssWar-in-must l d l₀ d₀ N2N_KeepAlive    x q′ eq = ⊥-elim (nothing-absurd eq)
cssWar-in-must l d l₀ d₀ N2N_TxSubmission x q′ eq = ⊥-elim (nothing-absurd eq)
cssWar-in-must l d l₀ d₀ N2N_LeiosNotify  x q′ eq = ⊥-elim (nothing-absurd eq)
cssWar-in-must l d l₀ d₀ N2N_LeiosFetch   x q′ eq = ⊥-elim (nothing-absurd eq)
cssWar-in-must l d l₀ d₀ N2N_ChainSync    x q′ eq with l₀ ≟ l | d₀ ≟ d
... | no ¬p    | _        = ⊥-elim (nothing-absurd eq)
... | yes refl | no ¬q    = ⊥-elim (nothing-absurd eq)
... | yes refl | yes refl
      with x ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _ = ⊥-elim (nothing-absurd eq)
...     | yes _ = sym (just-injective eq)

-- … and `csWar` has no wire-READ row at all, so the READ direction REFUTES the
-- fired-row arm at this end of the region
cssWar-out-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               (q′ : NS.CSsPos)
             → NS.csSnxt l d NS.csWar (Payload , output l₀ d₀ id₀) x ≡ just q′ → ⊥
cssWar-out-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

-- … and the region's OTHER end is io-CLOSED outright: `csMust`'s two rows are both
-- `apiCS` (`NodeSpecs:448-453`), so BOTH io directions refute there
cssMust-in-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               (q′ : NS.CSsPos)
             → NS.csSnxt l d NS.csMust (Payload , input l₀ d₀ id₀) x ≡ just q′ → ⊥
cssMust-in-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

cssMust-out-⊥ : (l : Link) (d : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
                (q′ : NS.CSsPos)
              → NS.csSnxt l d NS.csMust (Payload , output l₀ d₀ id₀) x ≡ just q′ → ⊥
cssMust-out-⊥ l d l₀ d₀ id₀ x q′ eq = nothing-absurd eq

------------------------------------------------------------------------
-- §5  *** THE ROW-CARRYING 12-PEER BUNDLE PEEL — THE LAYER'S ONE MIRROR. ***
--
-- KEEP-IN-SYNC WITH `SysIoLink6:330-462` (`BundleCSEvR-abs` `:330-343`,
-- `finishCSc-ev-abs` `:345-370`, `finishCSs-ev-abs` `:372-398`,
-- `absBundleCS-ev-prod` `:400-462`).  *** (T5 / review M-3) THE LAST TWO ANCHORS
-- WERE EACH OFF BY ONE and are corrected above, re-derived at this round: `:399`
-- is blank, and `absBundleCS-ev-prod`'s block opens with its two comment lines at
-- `:400-401` (signature `:402`), so the four spans are comment-inclusive and
-- contiguous, as the other two already were. ***  *** THIS IS THE ONLY TRANSCRIPTION IN THE
-- LAYER, AND IT IS UNAVOIDABLE: *** `_⦀_` has NO injectivity, so the peer-level
-- step `sM` and the successor slot must come out of ONE peel — the frozen
-- `absBundleCS-ev-prod` returns the bundle-level equality and the concrete run but
-- NOT `sM`, and a second peel yields a decomposition that cannot be tied to the
-- first (`finishCSc-ev-abs` has both in scope and returns neither).  Gate route 3
-- stays blocked; this mirror is the price.
--
-- DEVIATIONS FROM THE SOURCE, DECLARED:
--   (D1) each `bcscEB⁺`/`bcssEB⁺` carries a FOURTH field, the fired coarse row.
--   (D2) the two `finish` folds obtain the successor through §4's `cscRowInv`/
--        `cssRowInv` instead of calling `decCSc/CSs-ev-prod-abs` directly — the
--        SAME frozen call with the row read off it, so the successor, the run and
--        the `Meq` are the frozen ones and only the row is new.
--   (D3) nothing else: the ten sibling refutations, the `⦀-wev` tower and the
--        `cong` retargeting blobs are transcribed unchanged.  When the source
--        changes, this section changes with it, part by part.
--   (D4) (T5 / review M-2, an UNDECLARED deviation now declared) the `Par-ev-elim`
--        merge argument here is `(λ _ _ → ttP)` where the source's is
--        `(λ _ _ → tt)`: this module names both `⊤`s — the `done` channel's plain
--        carrier and the polymorphic unit the merge wants — so the polymorphic
--        constructor travels renamed (import comment at `:58-61`).  Semantically
--        identical; declared because THIS is where the next sync diff meets it.
------------------------------------------------------------------------

-- which driven CS peer fired, its updated position, the concrete WEAK run, AND THE
-- FIRED COARSE ROW (D1 — the ⁺ of `SysIoLink6.BundleCSEvR-abs`)
data BundleCSEvR-abs⁺ (l : Link) (cl sv : Dir)
     (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
     (ip : SN.InertPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcscEB⁺ : (csc′ : SN.CScPos)
        → Bd′ ≡ absBundleG l cl sv csc′ css bfc bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► bundleG l cl sv csc′ css bfc bfs ip
        → CScRow l cl (ιCS e₁) a csc csc′
        → BundleCSEvR-abs⁺ l cl sv csc css bfc bfs ip e₁ a Bd′
  bcssEB⁺ : (css′ : SN.CSsPos)
        → Bd′ ≡ absBundleG l cl sv csc css′ bfc bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► bundleG l cl sv csc css′ bfc bfs ip
        → CSsRow l sv (ιCS e₁) a css css′
        → BundleCSEvR-abs⁺ l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a CS-CLIENT abstract fire into the ⁺ bundle result (mirror of
-- `SysIoLink6.finishCSc-ev-abs:345-370`; D2 at the leaf call)
finishCSc-ev-abs⁺ : (l : Link) (cl sv : Dir) (csc : SN.CScPos) (css : SN.CSsPos)
    (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR-abs⁺ l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (P′
        ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSc-ev-abs⁺ l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with cscRowInv l cl csc sM
... | csc′ , run , Meq , row =
      bcscEB⁺ csc′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (z
               ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁)))
            (⦀-wev-L (decCSc l cl csc) _
              (noOffer→viewV _
                (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                  (λ q → cl≢sv (trans (sym (absCSc-ev-dir l cl csc sM)) q))))
              run)))
        row

-- fold a CS-SERVER abstract fire into the ⁺ bundle result (mirror of
-- `SysIoLink6.finishCSs-ev-abs:372-399`; D2 at the leaf call)
finishCSs-ev-abs⁺ : (l : Link) (cl sv : Dir) (csc : SN.CScPos) (css : SN.CSsPos)
    (bfc : SN.BFcPos) (bfs : SN.BFsPos) (ip : SN.InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → absCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR-abs⁺ l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (P′
        ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishCSs-ev-abs⁺ l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM with cssRowInv l sv css sM
... | css′ , run , Meq , row =
      bcssEB⁺ css′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (z
               ⦀ (absBFc l cl bfc ⦀ (absBFs l sv bfs
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc)
                (decCSc-dir-noOffer l cl csc e₁ (λ q → cl≢sv (trans (sym q) (absCSs-ev-dir l sv css sM)))))
              (⦀-wev-L (decCSs l sv css) _
                (noOffer→viewV _ (csTail-bfc-noOffer l cl sv bfc bfs ip e₁))
                run))))
        row

-- the ⁺ 12-peer abstract bundle ev-inversion (CS): peel each `⦀`, refute the ten
-- siblings, fold the driven CS peer WITH ITS ROW (mirror of
-- `SysIoLink6.absBundleCS-ev-prod:401-462`; D3 — the refutations are unchanged)
absBundleCS-ev-prod⁺ : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : SN.CScPos) (css : SN.CSsPos) (bfc : SN.BFcPos) (bfs : SN.BFsPos)
       (ip : SN.InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → BundleCSEvR-abs⁺ l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleCS-ev-prod⁺ l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM      = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noCS l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM      = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noCS l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = finishCSc-ev-abs⁺ l cl sv csc css bfc bfs ip cl≢sv sM
...     | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absCSs l sv css) _ (absCSs-dir-noBoth l sv css e₁ (λ q → cl≢sv (trans (sym (absCSc-ev-dir l cl csc sM)) q))) (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))) (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = finishCSs-ev-abs⁺ l cl sv csc css bfc bfs ip cl≢sv sM
...       | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFc l cl bfc) _ (absBFc-noCS l cl bfc e₁) (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-noCS l sv bfs e₁) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁))))))) (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (absBFc-noCS l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (absBFs-noCS l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noCS l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noCS l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noCS l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noCS l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → ttP) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noCS l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs      = ⊥-elim (absLFs-noCS l sv (lfs ip) e₁ (_ , qs))
