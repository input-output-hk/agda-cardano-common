{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness campaign — M1: the parametric consume-pipeline core
-- (`Liveness.PipePair`), part 3 (option-1 slicing).
--
-- ONE consume-side node pipeline, parametric in the link `l` and the
-- client direction `d`, instantiable for the BD and CD pipelines of
-- `nodeD` (M4 attaches the shared breakable medium by congruence; M5
-- walks the assembled abstract system).
--
-- M2 SEAM (not a bare `⦀`): `nodeD = (mini_BD ⦀ mini_CD) ∥⇘apiES⇙
-- (drv_BD ⦀ drv_CD)` is NOT syntactically `pipe_BD ⦀ pipe_CD` — M2 needs
-- (i) a `Par⊤`/`⦀` interchange over link-disjoint api alphabets before
-- `cong-⦀` of the two `pipe≈DR` instances applies, (ii) a link-REFINED
-- `Alpha` (`peerAlpha` is link-blind — same-(protocol,dir) peers on
-- different links aren't separated) with sharper `OffersOnly`, and
-- (iii) an `OffersOnly` builder through `∥⇘_⇙` for a whole pipe.
--
-- DESIGN HISTORY (kept as the audit trail):
--   · Part 1 folded the per-link breakable medium cell INTO `pipe` and
--     hid io — and flagged that its provisional fetch-chain spec was too
--     small (KA free-api finding).
--   · Part 2 (post-fairness resume) found the part-1 slicing UNSOUND: the
--     copy medium is direction-preserving, so in a SINGLE-node pipe every
--     peer's wire send is echoed back to ITSELF as the wrong message type
--     — the isolated medium-folded pipe deadlocks after one visible event
--     per protocol, and the KA loop does NOT free-run there (it is an
--     emergent property of the two-node assembly).  Part-1's "KA
--     free-runs in loopback isolation" claim was WRONG for that slicing.
--   · Part 3 (this revision) — controller-adjudicated OPTION 1: revert to
--     the spike §Q2 slicing.  `pipe l d` is the NODE-SIDE pipeline only —
--     NO medium, NO hide; the io (wire) events are FREE solo-visible
--     offers.  Under free io the KA client's api/wire loop DOES free-run,
--     so `pipeSpec` exhibits it, together with the full io-visible
--     surface of all eight peers.  `break` is a medium event and leaves
--     M1 entirely (M4/M5's concern).
--
-- FINAL SPEC SHAPE (record prominently — M2/M4/M5 consume this):
--
--   pipe     l d = miniProtocols l d (flipDir d) ∥⇘ apiES ⇙ (consume l d >> Skip)
--   pipeSpec l d = ( kaClientSpec l d  ⦀ (kaServerSpec l sv
--                  ⦀ (csClientSpec l d ⦀ (csServerSpec l sv
--                  ⦀ (bfClientSpec l d ⦀ (bfServerSpec l sv
--                  ⦀ (tsClientSpec l d ⦀ tsServerSpec l sv)))))))
--                    ∥⇘ apiES ⇙ (consume l d >> Skip)          [sv = flipDir d]
--
-- where each `x{Client,Server}Spec` is a τ-FREE position-indexed react
-- FSM over `Net_Api Payload` (a pure next-state TABLE interpreted by the
-- one guarded builder `tableSpec`), mirroring that peer's FSM with the
-- rename (`ιKA`/`ιCS`/`ιBF`/`ιTS`) applied and the `iter` loop-τs erased.
-- The KA loop is exhibited by `kcClient → kcWmsg c → kcAwait c → kcClient`
-- (visible apiKA request, wire send, wire response — perpetual, with the
-- `sendKADone` exit to √).  The driver is kept VERBATIM (`consume l d >>
-- Skip` — `>>=` is τ-free at the ret junction, so the driver leg of the
-- bisim is reflexivity; part-1's "one bind-τ" remark was wrong).
--
-- RECORDED DEVIATION (proof architecture): `pipeSpec` is COMPOSITIONAL
-- (the same `⦀`/`∥⇘apiES⇙` shape as `pipe`, with each renamed iter-peer
-- replaced by its τ-free table FSM), NOT a monolithic flat FSM.  A flat
-- product FSM over eight io-free peers is neither small nor useful, while
-- this shape (a) erases exactly the τ/rename/iter noise, (b) lets
-- `pipe≈DR` be assembled from EIGHT small per-peer rename-erasure bisims
-- via the PROVEN congruences `cong-⦀` and `cong-Par⊤-L`
-- (`CSP.Laws.Bisim.DRCongruence`; `Sep` discharged from `OffersOnly` —
-- pairwise-disjoint peer alphabets; the driver offers only apiES events),
-- with NO composite stepping at all, and (c) keeps M2's `⦀`-assembly and
-- M4's medium-attach untouched.  The perLink recipe still governs the
-- INTERNALS of each per-peer bisim.  The spec side is fully τ-free
-- (helps M5's Realisableᴿ); the impl side's only τs are the eight
-- peers' `iter` loop re-entry sils.
--
-- M2-facing contract (names stable): `pipe`, `pipeSpec`,
-- `PipeBisim l d = pipe l d ≈DR pipeSpec l d`.
--
-- STATUS: PROVED.  The proof term `pipe≈DR : (l) → pipe l hi ≈DR pipeSpec l hi`
-- and the two goal terms `goalBD-proof : goalBD` / `goalCD-proof : goalCD`
-- live in `PipePairAssembly` (the 8 per-peer bisims live in
-- `PipePairPeersKB`/`KB2`/`Peers3`/`Peers4`/`Peers5`/`Peers6`, the CS/TS
-- impl-side OffersOnly in `PipePairPeers2`; assembled by 7×cong-⦀ +
-- cong-Par⊤ apiES over `sep-from-OffersOnly`/`peerAlpha-Disj` + `sep-R`).
--
-- Postulate-free in these modules; transitively rests on the repo's
-- certified König-step baseline (Par-Diverges→ via cong-Par⊤/cong-⦀,
-- certified from one dne in ClassicalFromLEM), as elsewhere in the
-- DR-congruence layer.  No holes or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
import Data.Fin as F
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
open PTree

-- the concrete FourNode instantiation: the shared Params `p`, the `consume`
-- driver, the `apiES` sync set, and the two consume-side link ids
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; consume; apiES; linkBD; linkCD )

open import CSP.Examples.Cardano_network.Params using (Params)
open Params p   -- Cookie/Block/Txid/Time/Length/time₀/length₀ + DecEq instances

-- control enums (Dir/IDs/Mode/BlockingStyle) + their DecEq instances
open import CSP.Examples.Cardano_network.Base

-- the shared payload (message datatypes + DecEq instances)
open import CSP.Examples.Cardano_network.Data p

-- the shared alphabet (Net_Api events, api tag enums) — opened fully so
-- the tag/channel constructors and DecEq instances are all in scope
open import CSP.Examples.Cardano_network.Net p

-- the mini-protocol peer bundle (all eight renamed peers on the link) plus the
-- impl peers + their event injections (needed for the impl-side OffersOnly 2(b))
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( miniProtocols
        ; KAclientA; KAserverA; ιKA; ιKA⁻¹; ιKA-linv
        ; BFclientA; BFserverA; ιBF; ιBF⁻¹; ιBF-linv )
-- the KeepAlive source peer FSMs (client/server step functions + states)
open import CSP.Examples.Cardano_network.KeepAlive p
  using ( KAEv; KAEv-≟; sendKA; receiveKA; apiKAev; doneKA
        ; KAState; stClient; stServer; stDone; Rr
        ; clientStep; serverStep; KAclientStClient; KAserverStClient )
-- source-side operators for KAEv (name the impl bisim states: iter/iter-bind/Ret)
import CSP.Operators {E = KAEv} KAEv-≟ as SrcOp
-- the KA rename instance (the same module application NetworkPar's peers use)
import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
-- the BlockFetch source peer FSM (qualified — its BFState/step/Rr names clash
-- with KeepAlive's stDone/serverStep/Rr, so it must NOT be opened)
import CSP.Examples.Cardano_network.BlockFetch p as BF
-- source-side operators for BFEv (name the BF server bisim's iter/iter-bind/Output states)
import CSP.Operators {E = BF.BFEv} BF.BFEv-≟ as SrcOpB
-- the BF rename instance (the same module application NetworkPar's peers use)
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; Skip )

open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; deadlock-no-τ )
-- weak steps + the relation→DRbisim coinduction principle (per-peer bisims)
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev )
open import Semantics.BisimFromRel {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( module DRFromRel )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.PipePair where

------------------------------------------------------------------------
-- Missing product/list DecEq instances for the `!`-output value gates
-- (mirroring the local instances of the peer modules).
------------------------------------------------------------------------

instance
  -- ℕ equality (component of the TS request triple)
  DecEq-ℕ' : DecEq ℕ
  DecEq-ℕ' = DecEqI.DecEq-ℕ
  -- Header × Tip (CS rollforward api payload)
  DecEq-H×T : DecEq (Header × Tip)
  DecEq-H×T = DecEqI.DecEq-×
  -- Point × Tip (CS rollback / intersect-found api payload)
  DecEq-P×T : DecEq (Point × Tip)
  DecEq-P×T = DecEqI.DecEq-×
  -- Cookie × Cookie (KA errCookie api payload)
  DecEq-Cookie² : DecEq (Cookie × Cookie)
  DecEq-Cookie² = DecEqI.DecEq-×
  -- ℕ × ℕ (component of the TS request triple)
  DecEq-ℕ×ℕ : DecEq (ℕ × ℕ)
  DecEq-ℕ×ℕ = DecEqI.DecEq-×
  -- BlockingStyle × ℕ × ℕ (TS request-txids api payload)
  DecEq-BS×ℕ×ℕ : DecEq (BlockingStyle × ℕ × ℕ)
  DecEq-BS×ℕ×ℕ = DecEqI.DecEq-×

------------------------------------------------------------------------
-- Direction flip: the server runs on the direction opposite the client.
------------------------------------------------------------------------

-- the server-side direction opposite a client direction
flipDir : Dir → Dir
flipDir lo = hi
flipDir hi = lo

------------------------------------------------------------------------
-- The real composite `pipe l d` (option-1 / spike-§Q2 slicing).
------------------------------------------------------------------------

-- the node-side pipeline: the eight-peer bundle synchronised (on apiES)
-- with the `consume` driver — NO medium, NO hide (io events free-visible).
-- For (l , d) = (linkBD , hi) this is exactly `nodeD`'s BD half.
pipe : (l : Link) (d : Dir)
     → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
pipe l d = miniProtocols l d (flipDir d) ∥⇘ apiES ⇙ (consume l d >> Skip)

------------------------------------------------------------------------
-- The τ-free table-FSM interpreter.
--
-- Each spec peer is a PURE next-state table over `Net_Api Payload`
-- events plus a terminal predicate, interpreted by ONE guarded
-- corecursive builder (`tableSpec`): terminal positions are √ (`ret`),
-- non-terminal positions are stable react nodes offering exactly the
-- table's edges.  The corecursive call sits under `just` inside the
-- named helper `tGo` — the `CSP.Rename` `rnMc` productivity pattern.
------------------------------------------------------------------------

-- the shared component tree type of the pipeline
NetTree : Set₁
NetTree = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- a τ-free FSM table: terminal (√) positions + the next-position table
record Table (Pos : Set) : Set₁ where
  field
    isFin : Pos → Bool
    nxt   : Pos → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe Pos)

-- interpret a table from a position (guarded corecursive builder)
tableSpec : {Pos : Set} → Table Pos → Pos → NetTree
-- successor wrapper: the corecursive call, guarded under `just`
tGo : {Pos : Set} → Table Pos → Maybe Pos → Maybe NetTree
-- the react offer map of a non-terminal position (table edge → successor)
tMenu : {Pos : Set} → Table Pos → Pos
      → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe NetTree)

tGo T nothing  = nothing
tGo T (just q) = just (tableSpec T q)

tMenu T q at a = tGo T (Table.nxt T q at a)

-- the node shape of a table position, keyed on its (Bool) terminal flag: √ (ret)
-- when terminal, else a stable react offering exactly the table's edges.  Named
-- (rather than an inline `with` on `isFin`) so that `force (tableSpec T q)` is
-- DEFINITIONALLY `tsNode T q (isFin T q)` — this exposes the `isFin` scrutinee to
-- the OffersOnly proof (`tsNode-fin`/`tsNode-nonfin`), sidestepping the classic
-- with-stuck-force problem.
tsNode : {Pos : Set} → Table Pos → Pos → Bool
       → NodeKind (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
tsNode T q true  = ret tt
tsNode T q false = react (tMenu T q) (λ _ _ → nothing)

force (tableSpec T q) = tsNode T q (Table.isFin T q)

------------------------------------------------------------------------
-- KeepAlive client spec (dir d, sends stamped FromInitiator).
--
-- The autonomous KA loop `kcClient → kcWmsg c → kcAwait c → kcClient`
-- (apiKA ∉ apiES ⇒ free) plus the `sendKADone` exit to √ — THE loop the
-- fairness campaign's `BlockLiveness⁺ᶠ` excludes by `Fair`.
------------------------------------------------------------------------

-- KA client positions (state heads + mid-prefix positions)
data KAcPos : Set where
  kcClient : KAcPos                     -- loop head: offer the two api requests
  kcWmsg   : Cookie → KAcPos            -- wire-send of MsgKeepAlive c
  kcAwait  : Cookie → KAcPos            -- awaiting the response to c
  kcWdone  : KAcPos                     -- wire-send of MsgKADone
  kcDdone  : KAcPos                     -- the client-local done event
  kcErr    : Cookie → Cookie → KAcPos   -- errCookie api emit (req , rsp)
  kcTerm   : KAcPos                     -- √ after the done handshake
  kcTermE  : KAcPos                     -- √ after errCookie

-- KA client terminal positions
kaCfin : KAcPos → Bool
kaCfin kcTerm  = true
kaCfin kcTermE = true
kaCfin _       = false

-- KA client next-state table (mirrors `KeepAlive.clientStep` renamed)
kaCnxt : Link → Dir → KAcPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe KAcPos)
kaCnxt l d kcClient (_ , apiKA l′ d′ sendKAMsg) c with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (kcWmsg c)
... | _        | _        = nothing
kaCnxt l d kcClient (_ , apiKA l′ d′ sendKADone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just kcWdone
... | _        | _        = nothing
kaCnxt l d (kcWmsg c) (_ , input l′ d′ N2N_KeepAlive) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | yes _ = just (kcAwait c)
...     | no  _ = nothing
kaCnxt l d (kcWmsg c) (_ , input l′ d′ N2N_KeepAlive) pl | _ | _ = nothing
kaCnxt l d kcWdone (_ , input l′ d′ N2N_KeepAlive) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | yes _ = just kcDdone
...     | no  _ = nothing
kaCnxt l d kcWdone (_ , input l′ d′ N2N_KeepAlive) pl | _ | _ = nothing
kaCnxt l d kcDdone (_ , done l′ d′ N2N_KeepAlive) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just kcTerm
... | _        | _        = nothing
kaCnxt l d (kcAwait c) (_ , output l′ d′ N2N_KeepAlive)
      (t , m , len , keepAlive (MsgKeepAliveResponse c′)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with c ≟ c′
...   | yes _ = just kcClient
...   | no  _ = just (kcErr c c′)
kaCnxt l d (kcAwait c) (_ , output l′ d′ N2N_KeepAlive)
      (t , m , len , keepAlive (MsgKeepAliveResponse c′)) | _ | _ = nothing
kaCnxt l d (kcErr cq cr) (_ , apiKA l′ d′ errCookie) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ (cq , cr)
...   | yes _ = just kcTermE
...   | no  _ = nothing
kaCnxt l d (kcErr cq cr) (_ , apiKA l′ d′ errCookie) x | _ | _ = nothing
kaCnxt l d _ _ = λ _ → nothing

-- the KA client spec peer
kaClientSpec : Link → Dir → NetTree
kaClientSpec l d = tableSpec (record { isFin = kaCfin ; nxt = kaCnxt l d }) kcClient

------------------------------------------------------------------------
-- KeepAlive server spec (dir sv, sends stamped FromResponder): the pure
-- echo — receive a keepalive, return its cookie; a done-msg ends it.
------------------------------------------------------------------------

-- KA server positions
data KAsPos : Set where
  ksClient : KAsPos            -- awaiting a request from the wire
  ksResp   : Cookie → KAsPos   -- wire-send of the response to c
  ksDdone  : KAsPos            -- the server-local done event
  ksTerm   : KAsPos            -- √ after the done handshake

-- KA server terminal positions
kaSfin : KAsPos → Bool
kaSfin ksTerm = true
kaSfin _      = false

-- KA server next-state table (mirrors `KeepAlive.serverStep` renamed)
kaSnxt : Link → Dir → KAsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe KAsPos)
kaSnxt l d ksClient (_ , output l′ d′ N2N_KeepAlive)
      (t , m , len , keepAlive (MsgKeepAlive c)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ksResp c)
... | _        | _        = nothing
kaSnxt l d ksClient (_ , output l′ d′ N2N_KeepAlive)
      (t , m , len , keepAlive MsgKADone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ksDdone
... | _        | _        = nothing
kaSnxt l d ksDdone (_ , done l′ d′ N2N_KeepAlive) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ksTerm
... | _        | _        = nothing
kaSnxt l d (ksResp c) (_ , input l′ d′ N2N_KeepAlive) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | yes _ = just ksClient
...     | no  _ = nothing
kaSnxt l d (ksResp c) (_ , input l′ d′ N2N_KeepAlive) pl | _ | _ = nothing
kaSnxt l d _ _ = λ _ → nothing

-- the KA server spec peer
kaServerSpec : Link → Dir → NetTree
kaServerSpec l d = tableSpec (record { isFin = kaSfin ; nxt = kaSnxt l d }) ksClient

------------------------------------------------------------------------
-- ChainSync client spec (dir d; api events ∈ apiES ⇒ driver-gated).
------------------------------------------------------------------------

-- CS client positions
data CScPos : Set where
  ccIdle  : CScPos                  -- state head: offer the three api requests
  ccWreq  : CScPos                  -- wire-send of MsgCSRequestNext
  ccAwait : CScPos                  -- stCanAwait: awaiting the server reply
  ccWfi   : List Point → CScPos     -- wire-send of MsgCSFindIntersect pts
  ccInt   : CScPos                  -- stIntersect: awaiting the intersect reply
  ccWdone : CScPos                  -- wire-send of MsgCSDone
  ccDdone : CScPos                  -- the client-local done event
  ccMust  : CScPos                  -- stMustReply (after AwaitReply)
  ccArf   : Header × Tip → CScPos   -- api emit of recvCSRollforward
  ccArb   : Point × Tip → CScPos    -- api emit of recvCSRollback
  ccAif   : Point × Tip → CScPos    -- api emit of recvCSIntersectFound
  ccAin   : Tip → CScPos            -- api emit of recvCSIntersectNotFound
  ccTerm  : CScPos                  -- √ after the done handshake

-- CS client terminal positions
csCfin : CScPos → Bool
csCfin ccTerm = true
csCfin _      = false

-- CS client next-state table (mirrors `ChainSync.clientStep` renamed)
csCnxt : Link → Dir → CScPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe CScPos)
csCnxt l d ccIdle (_ , apiCS l′ d′ sendCSRequestNext) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ccWreq
... | _        | _        = nothing
csCnxt l d ccIdle (_ , apiCS l′ d′ sendCSFindIntersect) pts with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccWfi pts)
... | _        | _        = nothing
csCnxt l d ccIdle (_ , apiCS l′ d′ sendCSDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ccWdone
... | _        | _        = nothing
csCnxt l d ccWreq (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | yes _ = just ccAwait
...     | no  _ = nothing
csCnxt l d ccWreq (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csCnxt l d (ccWfi pts) (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect pts))
...     | yes _ = just ccInt
...     | no  _ = nothing
csCnxt l d (ccWfi pts) (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csCnxt l d ccWdone (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | yes _ = just ccDdone
...     | no  _ = nothing
csCnxt l d ccWdone (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csCnxt l d ccDdone (_ , done l′ d′ N2N_ChainSync) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ccTerm
... | _        | _        = nothing
csCnxt l d ccAwait (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSRollForward h tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccArf (h , tp))
... | _        | _        = nothing
csCnxt l d ccAwait (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSRollBackward pt tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccArb (pt , tp))
... | _        | _        = nothing
csCnxt l d ccAwait (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync MsgCSAwaitReply) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just ccMust
... | _        | _        = nothing
csCnxt l d ccMust (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSRollForward h tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccArf (h , tp))
... | _        | _        = nothing
csCnxt l d ccMust (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSRollBackward pt tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccArb (pt , tp))
... | _        | _        = nothing
csCnxt l d ccInt (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSIntersectFound pt tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccAif (pt , tp))
... | _        | _        = nothing
csCnxt l d ccInt (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSIntersectNotFound tp)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (ccAin tp)
... | _        | _        = nothing
csCnxt l d (ccArf ht) (_ , apiCS l′ d′ recvCSRollforward) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ ht
...   | yes _ = just ccIdle
...   | no  _ = nothing
csCnxt l d (ccArf ht) (_ , apiCS l′ d′ recvCSRollforward) x | _ | _ = nothing
csCnxt l d (ccArb pt) (_ , apiCS l′ d′ recvCSRollback) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ pt
...   | yes _ = just ccIdle
...   | no  _ = nothing
csCnxt l d (ccArb pt) (_ , apiCS l′ d′ recvCSRollback) x | _ | _ = nothing
csCnxt l d (ccAif pt) (_ , apiCS l′ d′ recvCSIntersectFound) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ pt
...   | yes _ = just ccIdle
...   | no  _ = nothing
csCnxt l d (ccAif pt) (_ , apiCS l′ d′ recvCSIntersectFound) x | _ | _ = nothing
csCnxt l d (ccAin tp) (_ , apiCS l′ d′ recvCSIntersectNotFound) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ tp
...   | yes _ = just ccIdle
...   | no  _ = nothing
csCnxt l d (ccAin tp) (_ , apiCS l′ d′ recvCSIntersectNotFound) x | _ | _ = nothing
csCnxt l d _ _ = λ _ → nothing

-- the CS client spec peer
csClientSpec : Link → Dir → NetTree
csClientSpec l d = tableSpec (record { isFin = csCfin ; nxt = csCnxt l d }) ccIdle

------------------------------------------------------------------------
-- ChainSync server spec (dir sv; its api events are ∈ apiES but never
-- offered by the driver at sv — composed-blocked, exhibited regardless).
------------------------------------------------------------------------

-- CS server positions
data CSsPos : Set where
  csIdle      : CSsPos                  -- awaiting a request from the wire
  csAreq      : CSsPos                  -- api emit of reqCSRequestNext
  csCanAwait  : CSsPos                  -- stCanAwait: offer the three api replies
  csAfi       : List Point → CSsPos     -- api emit of reqCSFindIntersect
  csInt       : CSsPos                  -- stIntersect: offer the two api replies
  csDdone     : CSsPos                  -- the server-local done event
  csMust      : CSsPos                  -- stMustReply: offer the two api replies
  csWrf       : Header × Tip → CSsPos   -- wire-send of MsgCSRollForward
  csWrb       : Point × Tip → CSsPos    -- wire-send of MsgCSRollBackward
  csWar       : CSsPos                  -- wire-send of MsgCSAwaitReply
  csWif       : Point × Tip → CSsPos    -- wire-send of MsgCSIntersectFound
  csWin       : Tip → CSsPos            -- wire-send of MsgCSIntersectNotFound
  csTerm      : CSsPos                  -- √ after the done handshake

-- CS server terminal positions
csSfin : CSsPos → Bool
csSfin csTerm = true
csSfin _      = false

-- CS server next-state table (mirrors `ChainSync.serverStep` renamed)
csSnxt : Link → Dir → CSsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe CSsPos)
csSnxt l d csIdle (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync MsgCSRequestNext) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just csAreq
... | _        | _        = nothing
csSnxt l d csIdle (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync (MsgCSFindIntersect pts)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csAfi pts)
... | _        | _        = nothing
csSnxt l d csIdle (_ , output l′ d′ N2N_ChainSync)
      (t , m , len , chainSync MsgCSDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just csDdone
... | _        | _        = nothing
csSnxt l d csAreq (_ , apiCS l′ d′ reqCSRequestNext) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just csCanAwait
... | _        | _        = nothing
csSnxt l d (csAfi pts) (_ , apiCS l′ d′ reqCSFindIntersect) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ pts
...   | yes _ = just csInt
...   | no  _ = nothing
csSnxt l d (csAfi pts) (_ , apiCS l′ d′ reqCSFindIntersect) x | _ | _ = nothing
csSnxt l d csDdone (_ , done l′ d′ N2N_ChainSync) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just csTerm
... | _        | _        = nothing
csSnxt l d csCanAwait (_ , apiCS l′ d′ sendCSRollForward) ht with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWrf ht)
... | _        | _        = nothing
csSnxt l d csCanAwait (_ , apiCS l′ d′ sendCSRollBackward) pt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWrb pt)
... | _        | _        = nothing
csSnxt l d csCanAwait (_ , apiCS l′ d′ sendCSAwaitReply) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just csWar
... | _        | _        = nothing
csSnxt l d csMust (_ , apiCS l′ d′ sendCSRollForward) ht with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWrf ht)
... | _        | _        = nothing
csSnxt l d csMust (_ , apiCS l′ d′ sendCSRollBackward) pt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWrb pt)
... | _        | _        = nothing
csSnxt l d csInt (_ , apiCS l′ d′ sendCSIntersectFound) pt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWif pt)
... | _        | _        = nothing
csSnxt l d csInt (_ , apiCS l′ d′ sendCSIntersectNotFound) tp with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (csWin tp)
... | _        | _        = nothing
csSnxt l d (csWrf (h , tp)) (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp))
...     | yes _ = just csIdle
...     | no  _ = nothing
csSnxt l d (csWrf (h , tp)) (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csSnxt l d (csWrb (pt , tp)) (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | yes _ = just csIdle
...     | no  _ = nothing
csSnxt l d (csWrb (pt , tp)) (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csSnxt l d csWar (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | yes _ = just csMust
...     | no  _ = nothing
csSnxt l d csWar (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csSnxt l d (csWif (pt , tp)) (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | yes _ = just csIdle
...     | no  _ = nothing
csSnxt l d (csWif (pt , tp)) (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csSnxt l d (csWin tp) (_ , input l′ d′ N2N_ChainSync) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | yes _ = just csIdle
...     | no  _ = nothing
csSnxt l d (csWin tp) (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
csSnxt l d _ _ = λ _ → nothing

-- the CS server spec peer
csServerSpec : Link → Dir → NetTree
csServerSpec l d = tableSpec (record { isFin = csSfin ; nxt = csSnxt l d }) csIdle

------------------------------------------------------------------------
-- BlockFetch client spec (dir d; api events driver-gated).
------------------------------------------------------------------------

-- BF client positions
data BFcPos : Set where
  bcIdle   : BFcPos               -- state head: offer the two api requests
  bcWrr    : ChainRange → BFcPos  -- wire-send of MsgRequestRange r
  bcBusy   : BFcPos               -- awaiting StartBatch / NoBlocks
  bcWcd    : BFcPos               -- wire-send of MsgClientDone
  bcDdone  : BFcPos               -- the client-local done event
  bcStream : BFcPos               -- streaming: awaiting blocks / BatchDone
  bcAblk   : Block → BFcPos       -- api emit of recvBFBlock b
  bcTerm   : BFcPos               -- √ after the done handshake

-- BF client terminal positions
bfCfin : BFcPos → Bool
bfCfin bcTerm = true
bfCfin _      = false

-- BF client next-state table (mirrors `BlockFetch.clientStep` renamed)
bfCnxt : Link → Dir → BFcPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe BFcPos)
bfCnxt l d bcIdle (_ , apiBF l′ d′ sendBFRequestRange) r with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (bcWrr r)
... | _        | _        = nothing
bfCnxt l d bcIdle (_ , apiBF l′ d′ sendBFClientDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bcWcd
... | _        | _        = nothing
bfCnxt l d (bcWrr r) (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | yes _ = just bcBusy
...     | no  _ = nothing
bfCnxt l d (bcWrr r) (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfCnxt l d bcWcd (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | yes _ = just bcDdone
...     | no  _ = nothing
bfCnxt l d bcWcd (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfCnxt l d bcDdone (_ , done l′ d′ N2N_BlockFetch) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bcTerm
... | _        | _        = nothing
bfCnxt l d bcBusy (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch MsgStartBatch) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bcStream
... | _        | _        = nothing
bfCnxt l d bcBusy (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch MsgNoBlocks) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bcIdle
... | _        | _        = nothing
bfCnxt l d bcStream (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch (MsgBlock b)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (bcAblk b)
... | _        | _        = nothing
bfCnxt l d bcStream (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch MsgBatchDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bcIdle
... | _        | _        = nothing
bfCnxt l d (bcAblk b) (_ , apiBF l′ d′ recvBFBlock) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ b
...   | yes _ = just bcStream
...   | no  _ = nothing
bfCnxt l d (bcAblk b) (_ , apiBF l′ d′ recvBFBlock) x | _ | _ = nothing
bfCnxt l d _ _ = λ _ → nothing

-- the BF client spec peer
bfClientSpec : Link → Dir → NetTree
bfClientSpec l d = tableSpec (record { isFin = bfCfin ; nxt = bfCnxt l d }) bcIdle

------------------------------------------------------------------------
-- BlockFetch server spec (dir sv; api events composed-blocked).
------------------------------------------------------------------------

-- BF server positions
data BFsPos : Set where
  bsIdle   : BFsPos               -- awaiting a request from the wire
  bsAreq   : ChainRange → BFsPos  -- api emit of reqBFRange r
  bsBusy   : BFsPos               -- offer StartBatch / NoBlocks api
  bsDdone  : BFsPos               -- the server-local done event
  bsWsb    : BFsPos               -- wire-send of MsgStartBatch
  bsStream : BFsPos               -- offer Block / BatchDone api
  bsWnb    : BFsPos               -- wire-send of MsgNoBlocks
  bsWblk   : Block → BFsPos       -- wire-send of MsgBlock b
  bsWbd    : BFsPos               -- wire-send of MsgBatchDone
  bsTerm   : BFsPos               -- √ after the done handshake

-- BF server terminal positions
bfSfin : BFsPos → Bool
bfSfin bsTerm = true
bfSfin _      = false

-- BF server next-state table (mirrors `BlockFetch.serverStep` renamed)
bfSnxt : Link → Dir → BFsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe BFsPos)
bfSnxt l d bsIdle (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch (MsgRequestRange r)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (bsAreq r)
... | _        | _        = nothing
bfSnxt l d bsIdle (_ , output l′ d′ N2N_BlockFetch)
      (t , m , len , blockFetch MsgClientDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bsDdone
... | _        | _        = nothing
bfSnxt l d (bsAreq r) (_ , apiBF l′ d′ reqBFRange) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ r
...   | yes _ = just bsBusy
...   | no  _ = nothing
bfSnxt l d (bsAreq r) (_ , apiBF l′ d′ reqBFRange) x | _ | _ = nothing
bfSnxt l d bsDdone (_ , done l′ d′ N2N_BlockFetch) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bsTerm
... | _        | _        = nothing
bfSnxt l d bsBusy (_ , apiBF l′ d′ sendBFStartBatch) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bsWsb
... | _        | _        = nothing
bfSnxt l d bsBusy (_ , apiBF l′ d′ sendBFNoBlocks) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bsWnb
... | _        | _        = nothing
bfSnxt l d bsWsb (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | yes _ = just bsStream
...     | no  _ = nothing
bfSnxt l d bsWsb (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfSnxt l d bsWnb (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | yes _ = just bsIdle
...     | no  _ = nothing
bfSnxt l d bsWnb (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfSnxt l d bsStream (_ , apiBF l′ d′ sendBFBlock) b with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (bsWblk b)
... | _        | _        = nothing
bfSnxt l d bsStream (_ , apiBF l′ d′ sendBFBatchDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just bsWbd
... | _        | _        = nothing
bfSnxt l d (bsWblk b) (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | yes _ = just bsStream
...     | no  _ = nothing
bfSnxt l d (bsWblk b) (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfSnxt l d bsWbd (_ , input l′ d′ N2N_BlockFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | yes _ = just bsIdle
...     | no  _ = nothing
bfSnxt l d bsWbd (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
bfSnxt l d _ _ = λ _ → nothing

-- the BF server spec peer
bfServerSpec : Link → Dir → NetTree
bfServerSpec l d = tableSpec (record { isFin = bfSfin ; nxt = bfSnxt l d }) bsIdle

------------------------------------------------------------------------
-- TxSubmission client (submitter) spec (dir d; apiTS ∉ apiES ⇒ free).
------------------------------------------------------------------------

-- TS client positions
data TScPos : Set where
  tcInit  : TScPos                             -- wire-send of MsgTSInit
  tcIdle  : TScPos                             -- awaiting a request from the wire
  tcAri   : BlockingStyle × ℕ × ℕ → TScPos     -- api emit of recvTSRequestTxIds
  tcBlk   : TScPos                             -- blocking request outstanding
  tcNbl   : TScPos                             -- non-blocking request outstanding
  tcArt   : List Txid → TScPos                 -- api emit of recvTSRequestTxs
  tcTxs   : TScPos                             -- txs request outstanding
  tcWri   : List Txid → TScPos                 -- wire-send of MsgTSReplyTxIds
  tcWdone : TScPos                             -- wire-send of MsgTSDone
  tcDdone : TScPos                             -- the client-local done event
  tcWrt   : List Tx → TScPos                   -- wire-send of MsgTSReplyTxs
  tcTerm  : TScPos                             -- √ after the done handshake

-- TS client terminal positions
tsCfin : TScPos → Bool
tsCfin tcTerm = true
tsCfin _      = false

-- TS client next-state table (mirrors `TxSubmission.clientStep` renamed)
tsCnxt : Link → Dir → TScPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe TScPos)
tsCnxt l d tcInit (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | yes _ = just tcIdle
...     | no  _ = nothing
tsCnxt l d tcInit (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsCnxt l d tcIdle (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission (MsgTSRequestTxIds bs a r)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tcAri (bs , a , r))
... | _        | _        = nothing
tsCnxt l d tcIdle (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission (MsgTSRequestTxs ids)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tcArt ids)
... | _        | _        = nothing
tsCnxt l d (tcAri (Blocking , a , r)) (_ , apiTS l′ d′ recvTSRequestTxIds) x
      with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ (Blocking , a , r)
...   | yes _ = just tcBlk
...   | no  _ = nothing
tsCnxt l d (tcAri (Blocking , a , r)) (_ , apiTS l′ d′ recvTSRequestTxIds) x
      | _ | _ = nothing
tsCnxt l d (tcAri (NonBlocking , a , r)) (_ , apiTS l′ d′ recvTSRequestTxIds) x
      with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ (NonBlocking , a , r)
...   | yes _ = just tcNbl
...   | no  _ = nothing
tsCnxt l d (tcAri (NonBlocking , a , r)) (_ , apiTS l′ d′ recvTSRequestTxIds) x
      | _ | _ = nothing
tsCnxt l d (tcArt ids) (_ , apiTS l′ d′ recvTSRequestTxs) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ ids
...   | yes _ = just tcTxs
...   | no  _ = nothing
tsCnxt l d (tcArt ids) (_ , apiTS l′ d′ recvTSRequestTxs) x | _ | _ = nothing
tsCnxt l d tcBlk (_ , apiTS l′ d′ sendTSReplyTxIds) ids with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tcWri ids)
... | _        | _        = nothing
tsCnxt l d tcBlk (_ , apiTS l′ d′ sendTSDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tcWdone
... | _        | _        = nothing
tsCnxt l d tcNbl (_ , apiTS l′ d′ sendTSReplyTxIds) ids with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tcWri ids)
... | _        | _        = nothing
tsCnxt l d tcTxs (_ , apiTS l′ d′ sendTSReplyTxs) txs with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tcWrt txs)
... | _        | _        = nothing
tsCnxt l d (tcWri ids) (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | yes _ = just tcIdle
...     | no  _ = nothing
tsCnxt l d (tcWri ids) (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsCnxt l d tcWdone (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | yes _ = just tcDdone
...     | no  _ = nothing
tsCnxt l d tcWdone (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsCnxt l d tcDdone (_ , done l′ d′ N2N_TxSubmission) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tcTerm
... | _        | _        = nothing
tsCnxt l d (tcWrt txs) (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | yes _ = just tcIdle
...     | no  _ = nothing
tsCnxt l d (tcWrt txs) (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsCnxt l d _ _ = λ _ → nothing

-- the TS client spec peer
tsClientSpec : Link → Dir → NetTree
tsClientSpec l d = tableSpec (record { isFin = tsCfin ; nxt = tsCnxt l d }) tcInit

------------------------------------------------------------------------
-- TxSubmission server (requester) spec (dir sv; apiTS free).
------------------------------------------------------------------------

-- TS server positions
data TSsPos : Set where
  tsInit  : TSsPos               -- awaiting the submitter's MsgTSInit
  tsIdle  : TSsPos               -- offer the three api pull requests
  tsWib   : ℕ × ℕ → TSsPos       -- wire-send of MsgTSRequestTxIds Blocking
  tsWin   : ℕ × ℕ → TSsPos       -- wire-send of MsgTSRequestTxIds NonBlocking
  tsWrt   : List Txid → TSsPos   -- wire-send of MsgTSRequestTxs
  tsBlk   : TSsPos               -- blocking reply awaited
  tsNbl   : TSsPos               -- non-blocking reply awaited
  tsTxs   : TSsPos               -- txs reply awaited
  tsDdone : TSsPos               -- the server-local done event
  tsTerm  : TSsPos               -- √ after the done handshake

-- TS server terminal positions
tsSfin : TSsPos → Bool
tsSfin tsTerm = true
tsSfin _      = false

-- TS server next-state table (mirrors `TxSubmission.serverStep` renamed)
tsSnxt : Link → Dir → TSsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe TSsPos)
tsSnxt l d tsInit (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission MsgTSInit) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsIdle
... | _        | _        = nothing
tsSnxt l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) ar with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tsWib ar)
... | _        | _        = nothing
tsSnxt l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) ar with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tsWin ar)
... | _        | _        = nothing
tsSnxt l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxsPipelined) ids with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (tsWrt ids)
... | _        | _        = nothing
tsSnxt l d (tsWib (a , r)) (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
...     | yes _ = just tsBlk
...     | no  _ = nothing
tsSnxt l d (tsWib (a , r)) (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsSnxt l d (tsWin (a , r)) (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
...     | yes _ = just tsNbl
...     | no  _ = nothing
tsSnxt l d (tsWin (a , r)) (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsSnxt l d (tsWrt ids) (_ , input l′ d′ N2N_TxSubmission) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | yes _ = just tsTxs
...     | no  _ = nothing
tsSnxt l d (tsWrt ids) (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
tsSnxt l d tsBlk (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission (MsgTSReplyTxIds ids)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsIdle
... | _        | _        = nothing
tsSnxt l d tsBlk (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission MsgTSDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsDdone
... | _        | _        = nothing
tsSnxt l d tsDdone (_ , done l′ d′ N2N_TxSubmission) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsTerm
... | _        | _        = nothing
tsSnxt l d tsNbl (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission (MsgTSReplyTxIds ids)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsIdle
... | _        | _        = nothing
tsSnxt l d tsTxs (_ , output l′ d′ N2N_TxSubmission)
      (t , m , len , txSubmission (MsgTSReplyTxs txs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just tsIdle
... | _        | _        = nothing
tsSnxt l d _ _ = λ _ → nothing

-- the TS server spec peer
tsServerSpec : Link → Dir → NetTree
tsServerSpec l d = tableSpec (record { isFin = tsSfin ; nxt = tsSnxt l d }) tsInit

------------------------------------------------------------------------
-- The spec `pipeSpec l d` — the FINAL SHAPE (see the header): the eight
-- τ-free spec peers in `miniProtocols`' exact `⦀` nesting, synchronised
-- on apiES with the VERBATIM driver.
------------------------------------------------------------------------

-- the abstract node-side pipeline: τ-free peer FSMs + the verbatim driver
pipeSpec : (l : Link) (d : Dir)
         → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
pipeSpec l d =
  ( kaClientSpec l d ⦀ (kaServerSpec l (flipDir d)
      ⦀ (csClientSpec l d ⦀ (csServerSpec l (flipDir d)
      ⦀ (bfClientSpec l d ⦀ (bfServerSpec l (flipDir d)
      ⦀ (tsClientSpec l d ⦀ tsServerSpec l (flipDir d))))))) )
  ∥⇘ apiES ⇙ (consume l d >> Skip)

------------------------------------------------------------------------
-- OFFERSONLY LAYER (assembly prerequisite).
--
-- The `pipe≈DR` assembly (7×`cong-⦀` + 1×`cong-Par⊤-L`) discharges each
-- `Sep` side-condition from `OffersOnly` (via `sep-from-OffersOnly`): each
-- of the eight peers confines its visible offers to a per-(protocol,dir)
-- alphabet, and those eight alphabets are pairwise disjoint, so no two
-- peers ever both-offer a non-sync event.  This section builds the
-- SPEC-side confinement: a GENERIC `tableSpec-OffersOnly` lemma (uniform
-- over any table whose fired edges lie in α) + the per-(protocol,dir)
-- alphabet machinery + the pairwise-disjointness lemma + the eight
-- spec-peer instances + the driver's confinement.
------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Function.Base using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst; ≡-≟-identity)
open import Data.Product using (Σ-syntax)

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; sRet; sSil; sVis; sTau; ev; evl; evLabel; Event√; √; Label; τ
        ; Diverges )

import CSP.Laws.Bisim.DRCongruenceRep
open import CSP.Laws.Bisim.DRCongruenceRep (Net_Api-≟ {Payload})
  using ( Alpha; Disj; OffersOnly; MenuConf
        ; OffersOnly-deadlock; OffersOnly-Ret; OffersOnly-Skip; OffersOnly-mono
        ; OffersOnly-pchoice; OffersOnly-Prefix; OffersOnly-Prefix₀; OffersOnly-Output
        ; OffersOnly->>=; sep-from-OffersOnly )
open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload})
  using ( Sep; cong-⦀; cong-Par⊤-L )

open Op using ( ∅ES )
open import Process_Trees using (NodeKind)

------------------------------------------------------------------------
-- Generic table confinement.
--
-- `force (tableSpec T q)` is DEFINITIONALLY `tsNode T q (isFin T q)`, so
-- the two force shapes are recovered by `rewrite` on the `isFin` flag
-- (`tsNode-fin`/`tsNode-nonfin`); `tMenu`'s edge is recovered likewise
-- from the `nxt` value (`tMenu-just`/`tMenu-nothing`).
------------------------------------------------------------------------

-- terminal position: force is `ret tt` (recovered from the `isFin` flag)
tsNode-fin : {Pos : Set} (T : Table Pos) (q : Pos) → Table.isFin T q ≡ true
           → tsNode T q (Table.isFin T q) ≡ ret tt
tsNode-fin T q eq rewrite eq = refl

-- non-terminal position: force is the stable react offering the table's edges
tsNode-nonfin : {Pos : Set} (T : Table Pos) (q : Pos) → Table.isFin T q ≡ false
              → tsNode T q (Table.isFin T q) ≡ react (tMenu T q) (λ _ _ → nothing)
tsNode-nonfin T q eq rewrite eq = refl

-- a non-edge: the menu offers nothing (recovered from the `nxt` value)
tMenu-nothing : {Pos : Set} (T : Table Pos) (q : Pos)
                (at : AnyTypes (Net_Api Payload)) (a : proj₁ at)
              → Table.nxt T q at a ≡ nothing → tMenu T q at a ≡ nothing
tMenu-nothing T q at a eq rewrite eq = refl

-- a fired edge: the menu leads to the successor position's tree
tMenu-just : {Pos : Set} (T : Table Pos) (q : Pos)
             (at : AnyTypes (Net_Api Payload)) (a : proj₁ at) {q′ : Pos}
           → Table.nxt T q at a ≡ just q′ → tMenu T q at a ≡ just (tableSpec T q′)
tMenu-just T q at a eq rewrite eq = refl

-- GENERIC: a table whose every FIRED edge is an `α`-event is `α`-confined at
-- every position.  Proved by copattern corecursion: `now` reads off the fired
-- edge's `α`-membership from the hypothesis; `step` either lands in `deadlock`
-- (terminal √) or corecurses on the successor position (visible edge); τ / ret
-- / sil shapes are refuted from the (with-reduced) force equation.  The
-- `with Table.isFin T q in eqFin` reduces the step's force hypothesis `eqf` to
-- `ret tt ≡ …` (terminal) or `react (tMenu T q) ∅t ≡ …` (offering) directly.
tableSpec-OffersOnly :
    {Pos : Set} (α : Alpha) (T : Table Pos)
  → (∀ q at a {q′} → Table.nxt T q at a ≡ just q′ → α at a)
  → ∀ q → OffersOnly α (tableSpec T q)
tableSpec-OffersOnly α T inα q .OffersOnly.now (sVis {at = at} {a = a} eqf br)
  with Table.isFin T q in eqFin
... | true  = case eqf of λ ()
... | false with react-injective eqf
...   | menu≡ , _ with Table.nxt T q at a in eqN
...     | just q′ = inα q at a eqN
...     | nothing =
          case trans (sym (tMenu-nothing T q at a eqN))
                     (subst (λ g → g at a ≡ just _) (sym menu≡) br) of λ ()
tableSpec-OffersOnly α T inα q .OffersOnly.step st with Table.isFin T q in eqFin
... | true with st
...   | sRet _     = OffersOnly-deadlock
...   | sSil eqf   = case trans (sym (tsNode-fin T q eqFin)) eqf of λ ()
...   | sVis eqf _ = case trans (sym (tsNode-fin T q eqFin)) eqf of λ ()
...   | sTau eqf _ = case trans (sym (tsNode-fin T q eqFin)) eqf of λ ()
tableSpec-OffersOnly α T inα q .OffersOnly.step st | false with st
...   | sRet eqf = case trans (sym (tsNode-nonfin T q eqFin)) eqf of λ ()
...   | sSil eqf = case trans (sym (tsNode-nonfin T q eqFin)) eqf of λ ()
...   | sVis {at = at} {a = a} eqf br
        with react-injective (trans (sym (tsNode-nonfin T q eqFin)) eqf)
...     | menu≡ , _ with Table.nxt T q at a in eqN
...       | just q′
            rewrite sym (just-injective
                          (trans (sym (tMenu-just T q at a eqN))
                                 (subst (λ g → g at a ≡ just _) (sym menu≡) br)))
            = tableSpec-OffersOnly α T inα q′
...       | nothing =
            case trans (sym (tMenu-nothing T q at a eqN))
                       (subst (λ g → g at a ≡ just _) (sym menu≡) br) of λ ()
tableSpec-OffersOnly α T inα q .OffersOnly.step st | false | sTau {i = i} {a = a} eqf br
  with react-injective (trans (sym (tsNode-nonfin T q eqFin)) eqf)
...   | _ , τc≡ = case subst (λ g → g i a ≡ just _) (sym τc≡) br of λ ()

------------------------------------------------------------------------
-- Per-(protocol,dir) alphabets and their pairwise disjointness.
--
-- Each of the eight peers confines its offers to the events of ONE
-- (protocol, dir) slot.  A client (dir d) and its same-protocol server
-- (dir `flipDir d`) get DISTINCT slots (different dir), and distinct
-- protocols get distinct slots — so all eight slots are pairwise
-- distinct and the alphabets pairwise disjoint, which is exactly what
-- `sep-from-OffersOnly` needs to discharge every `Sep ∅ES` in the
-- assembly.
------------------------------------------------------------------------

-- the (protocol, dir) slot of a peer-relevant event (wire input/output/done
-- carry their protocol as the `IDs` field; the api events fix the protocol).
slot : AnyTypes (Net_Api Payload) → Maybe (IDs × Dir)
slot (_ , input  _ d i) = just (i , d)
slot (_ , output _ d i) = just (i , d)
slot (_ , done   _ d i) = just (i , d)
slot (_ , apiKA  _ d _) = just (N2N_KeepAlive , d)
slot (_ , apiCS  _ d _) = just (N2N_ChainSync , d)
slot (_ , apiBF  _ d _) = just (N2N_BlockFetch , d)
slot (_ , apiTS  _ d _) = just (N2N_TxSubmission , d)
slot _                  = nothing

-- the alphabet of one peer: exactly the events of its (protocol, dir) slot
peerAlpha : IDs → Dir → Alpha
peerAlpha i d at a = slot at ≡ just (i , d)

-- distinct slots ⇒ disjoint alphabets (a single event has one slot)
peerAlpha-Disj : ∀ {i₁ d₁ i₂ d₂} → ¬ (i₁ , d₁) ≡ (i₂ , d₂)
               → Disj (peerAlpha i₁ d₁) (peerAlpha i₂ d₂)
peerAlpha-Disj neq at a s₁ s₂ = neq (just-injective (trans (sym s₁) s₂))

------------------------------------------------------------------------
-- The driver's confinement.
--
-- `consume l d >> Skip` offers ONLY apiCS/apiBF events on (l,d) — all in
-- apiES — so its offered alphabet is `drvAlpha`.  Built purely from the
-- leaf builders (`>>=`/Prefix/Prefix₀/Output/Ret), no table analysis.
-- In the assembly this discharges the top-level `Sep apiES bundle driver`
-- (the driver never offers a non-apiES event; see `sep-R` note in report).
------------------------------------------------------------------------

-- the driver alphabet: apiCS ∪ apiBF on (l,d)
drvAlpha : Link → Dir → Alpha
drvAlpha l d at a = peerAlpha N2N_ChainSync d at a ⊎ peerAlpha N2N_BlockFetch d at a

-- the `consume` driver confines to `drvAlpha` (the CS/BF client api on (l,d))
consume-OffersOnly : (l : Link) (d : Dir)
                   → OffersOnly (drvAlpha l d) (consume l d >> Skip {0ℓ})
consume-OffersOnly l d =
  OffersOnly->>=
    (OffersOnly-Prefix₀ (λ _ → inj₁ refl)
      (OffersOnly-Prefix (λ _ → inj₁ refl)
        (λ { (header b , _) →
          OffersOnly-Output (inj₂ refl)
            (OffersOnly-Prefix (λ _ → inj₂ refl)
              (λ b′ →
                OffersOnly-Output (inj₂ refl)
                  (OffersOnly-Prefix₀ (λ _ → inj₁ refl) OffersOnly-Ret)))})))
    (λ _ → OffersOnly-Skip)

------------------------------------------------------------------------
-- Per-spec-peer edge→slot lemmas + per-spec-peer OffersOnly (recipe item 1).
--
-- For each spec peer, its next-state table fires an edge ONLY on events of
-- that peer's (protocol,dir) slot, so `peerAlpha` confines it and
-- `tableSpec-OffersOnly` yields the peer's `OffersOnly`.  Each edge lemma is a
-- mechanical position×event×(tag|ID|message) case analysis mirroring the
-- table's `with l′ ≟ l | d′ ≟ d` gates: a FIRING (position,event) reproduces
-- the gate and returns `refl` in the `yes refl | yes refl` branch (there
-- `slot` computes to the peer's slot, independent of the payload `with`),
-- while every non-firing case reduces the table to `nothing` and the edge
-- hypothesis is absurd.  The table's case tree splits `q` first, so EVERY
-- position must be enumerated for EVERY event (a wildcard `q` stays stuck on
-- appearing events); wire-`output` clauses additionally decompose the
-- structured payload (Messages wrapper + constructor) that the table matches.
--
-- These lemmas are SCRIPT-GENERATED (mirroring the repo's mkDR precedent):
-- the generator `.superpowers/sdd/gen-edge-lemmas.py` emits exactly this
-- block from a per-peer firing table; only the generated Agda is committed.
------------------------------------------------------------------------
-- KA client: every fired edge is an apiKA/wire event on (N2N_KeepAlive , d)
ka-c-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → kaCnxt l d q at a ≡ just q′
          → peerAlpha N2N_KeepAlive d at a
ka-c-edge l d kcClient (_ , input _ _ _) a ()
ka-c-edge l d kcClient (_ , output _ _ _) a ()
ka-c-edge l d kcClient (_ , sndmsg _ _ _) a ()
ka-c-edge l d kcClient (_ , rcvmsg _ _ _) a ()
ka-c-edge l d kcClient (_ , tx _ _ _) a ()
ka-c-edge l d kcClient (_ , sndack _ _ _) a ()
ka-c-edge l d kcClient (_ , rcvack _ _ _) a ()
ka-c-edge l d kcClient (_ , ack _ _ _) a ()
ka-c-edge l d kcClient (_ , done _ _ _) a ()
ka-c-edge l d kcClient (_ , apiCS _ _ _) a ()
ka-c-edge l d kcClient (_ , apiBF _ _ _) a ()
ka-c-edge l d kcClient (_ , apiTS _ _ _) a ()
ka-c-edge l d kcClient (_ , apiKA l′ d′ sendKAMsg) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d kcClient (_ , apiKA l′ d′ sendKADone) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d kcClient (_ , apiKA l′ d′ errCookie) a ()
ka-c-edge l d kcClient (_ , apiLN _ _ _) a ()
ka-c-edge l d kcClient (_ , apiLF _ _ _) a ()
ka-c-edge l d kcClient (_ , break _) a ()
ka-c-edge l d (kcWmsg c) (_ , input _ _ N2N_ChainSync) a ()
ka-c-edge l d (kcWmsg c) (_ , input _ _ N2N_BlockFetch) a ()
ka-c-edge l d (kcWmsg c) (_ , input _ _ N2N_TxSubmission) a ()
ka-c-edge l d (kcWmsg c) (_ , input l′ d′ N2N_KeepAlive) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d (kcWmsg c) (_ , input _ _ N2N_LeiosNotify) a ()
ka-c-edge l d (kcWmsg c) (_ , input _ _ N2N_LeiosFetch) a ()
ka-c-edge l d (kcWmsg c) (_ , output _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , sndmsg _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , rcvmsg _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , tx _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , sndack _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , rcvack _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , ack _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , done _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiCS _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiBF _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiTS _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiKA _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiLN _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , apiLF _ _ _) a ()
ka-c-edge l d (kcWmsg c) (_ , break _) a ()
ka-c-edge l d (kcAwait c) (_ , input _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_ChainSync) a ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_BlockFetch) a ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_TxSubmission) a ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , keepAlive (MsgKeepAlive _)) ()
ka-c-edge l d (kcAwait c) (_ , output l′ d′ N2N_KeepAlive) (_ , _ , _ , keepAlive (MsgKeepAliveResponse _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , keepAlive MsgKADone) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , blockFetch _) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , chainSync _) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , txSubmission _) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , leiosNotify _) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , leiosFetch _) ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_LeiosNotify) a ()
ka-c-edge l d (kcAwait c) (_ , output _ _ N2N_LeiosFetch) a ()
ka-c-edge l d (kcAwait c) (_ , sndmsg _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , rcvmsg _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , tx _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , sndack _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , rcvack _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , ack _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , done _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiCS _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiBF _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiTS _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiKA _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiLN _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , apiLF _ _ _) a ()
ka-c-edge l d (kcAwait c) (_ , break _) a ()
ka-c-edge l d kcWdone (_ , input _ _ N2N_ChainSync) a ()
ka-c-edge l d kcWdone (_ , input _ _ N2N_BlockFetch) a ()
ka-c-edge l d kcWdone (_ , input _ _ N2N_TxSubmission) a ()
ka-c-edge l d kcWdone (_ , input l′ d′ N2N_KeepAlive) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d kcWdone (_ , input _ _ N2N_LeiosNotify) a ()
ka-c-edge l d kcWdone (_ , input _ _ N2N_LeiosFetch) a ()
ka-c-edge l d kcWdone (_ , output _ _ _) a ()
ka-c-edge l d kcWdone (_ , sndmsg _ _ _) a ()
ka-c-edge l d kcWdone (_ , rcvmsg _ _ _) a ()
ka-c-edge l d kcWdone (_ , tx _ _ _) a ()
ka-c-edge l d kcWdone (_ , sndack _ _ _) a ()
ka-c-edge l d kcWdone (_ , rcvack _ _ _) a ()
ka-c-edge l d kcWdone (_ , ack _ _ _) a ()
ka-c-edge l d kcWdone (_ , done _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiCS _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiBF _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiTS _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiKA _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiLN _ _ _) a ()
ka-c-edge l d kcWdone (_ , apiLF _ _ _) a ()
ka-c-edge l d kcWdone (_ , break _) a ()
ka-c-edge l d kcDdone (_ , input _ _ _) a ()
ka-c-edge l d kcDdone (_ , output _ _ _) a ()
ka-c-edge l d kcDdone (_ , sndmsg _ _ _) a ()
ka-c-edge l d kcDdone (_ , rcvmsg _ _ _) a ()
ka-c-edge l d kcDdone (_ , tx _ _ _) a ()
ka-c-edge l d kcDdone (_ , sndack _ _ _) a ()
ka-c-edge l d kcDdone (_ , rcvack _ _ _) a ()
ka-c-edge l d kcDdone (_ , ack _ _ _) a ()
ka-c-edge l d kcDdone (_ , done _ _ N2N_ChainSync) a ()
ka-c-edge l d kcDdone (_ , done _ _ N2N_BlockFetch) a ()
ka-c-edge l d kcDdone (_ , done _ _ N2N_TxSubmission) a ()
ka-c-edge l d kcDdone (_ , done l′ d′ N2N_KeepAlive) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d kcDdone (_ , done _ _ N2N_LeiosNotify) a ()
ka-c-edge l d kcDdone (_ , done _ _ N2N_LeiosFetch) a ()
ka-c-edge l d kcDdone (_ , apiCS _ _ _) a ()
ka-c-edge l d kcDdone (_ , apiBF _ _ _) a ()
ka-c-edge l d kcDdone (_ , apiTS _ _ _) a ()
ka-c-edge l d kcDdone (_ , apiKA _ _ _) a ()
ka-c-edge l d kcDdone (_ , apiLN _ _ _) a ()
ka-c-edge l d kcDdone (_ , apiLF _ _ _) a ()
ka-c-edge l d kcDdone (_ , break _) a ()
ka-c-edge l d (kcErr cq cr) (_ , input _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , output _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , sndmsg _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , rcvmsg _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , tx _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , sndack _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , rcvack _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , ack _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , done _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiCS _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiBF _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiTS _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiKA l′ d′ sendKAMsg) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiKA l′ d′ sendKADone) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiKA l′ d′ errCookie) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-c-edge l d (kcErr cq cr) (_ , apiLN _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , apiLF _ _ _) a ()
ka-c-edge l d (kcErr cq cr) (_ , break _) a ()
ka-c-edge l d kcTerm (_ , input _ _ _) a ()
ka-c-edge l d kcTerm (_ , output _ _ _) a ()
ka-c-edge l d kcTerm (_ , sndmsg _ _ _) a ()
ka-c-edge l d kcTerm (_ , rcvmsg _ _ _) a ()
ka-c-edge l d kcTerm (_ , tx _ _ _) a ()
ka-c-edge l d kcTerm (_ , sndack _ _ _) a ()
ka-c-edge l d kcTerm (_ , rcvack _ _ _) a ()
ka-c-edge l d kcTerm (_ , ack _ _ _) a ()
ka-c-edge l d kcTerm (_ , done _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiCS _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiBF _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiTS _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiKA _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiLN _ _ _) a ()
ka-c-edge l d kcTerm (_ , apiLF _ _ _) a ()
ka-c-edge l d kcTerm (_ , break _) a ()
ka-c-edge l d kcTermE (_ , input _ _ _) a ()
ka-c-edge l d kcTermE (_ , output _ _ _) a ()
ka-c-edge l d kcTermE (_ , sndmsg _ _ _) a ()
ka-c-edge l d kcTermE (_ , rcvmsg _ _ _) a ()
ka-c-edge l d kcTermE (_ , tx _ _ _) a ()
ka-c-edge l d kcTermE (_ , sndack _ _ _) a ()
ka-c-edge l d kcTermE (_ , rcvack _ _ _) a ()
ka-c-edge l d kcTermE (_ , ack _ _ _) a ()
ka-c-edge l d kcTermE (_ , done _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiCS _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiBF _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiTS _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiKA _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiLN _ _ _) a ()
ka-c-edge l d kcTermE (_ , apiLF _ _ _) a ()
ka-c-edge l d kcTermE (_ , break _) a ()

-- the ka-c spec confines to the (N2N_KeepAlive , d) slot
kaClientSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_KeepAlive d) (kaClientSpec l d)
kaClientSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_KeepAlive d) _ (ka-c-edge l d) kcClient

-- KA server: every fired edge is a keepAlive wire event on (N2N_KeepAlive , d)
ka-s-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → kaSnxt l d q at a ≡ just q′
          → peerAlpha N2N_KeepAlive d at a
ka-s-edge l d ksClient (_ , input _ _ _) a ()
ka-s-edge l d ksClient (_ , output _ _ N2N_ChainSync) a ()
ka-s-edge l d ksClient (_ , output _ _ N2N_BlockFetch) a ()
ka-s-edge l d ksClient (_ , output _ _ N2N_TxSubmission) a ()
ka-s-edge l d ksClient (_ , output l′ d′ N2N_KeepAlive) (_ , _ , _ , keepAlive (MsgKeepAlive _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , keepAlive (MsgKeepAliveResponse _)) ()
ka-s-edge l d ksClient (_ , output l′ d′ N2N_KeepAlive) (_ , _ , _ , keepAlive MsgKADone) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , blockFetch _) ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , chainSync _) ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , txSubmission _) ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , leiosNotify _) ()
ka-s-edge l d ksClient (_ , output _ _ N2N_KeepAlive) (_ , _ , _ , leiosFetch _) ()
ka-s-edge l d ksClient (_ , output _ _ N2N_LeiosNotify) a ()
ka-s-edge l d ksClient (_ , output _ _ N2N_LeiosFetch) a ()
ka-s-edge l d ksClient (_ , sndmsg _ _ _) a ()
ka-s-edge l d ksClient (_ , rcvmsg _ _ _) a ()
ka-s-edge l d ksClient (_ , tx _ _ _) a ()
ka-s-edge l d ksClient (_ , sndack _ _ _) a ()
ka-s-edge l d ksClient (_ , rcvack _ _ _) a ()
ka-s-edge l d ksClient (_ , ack _ _ _) a ()
ka-s-edge l d ksClient (_ , done _ _ _) a ()
ka-s-edge l d ksClient (_ , apiCS _ _ _) a ()
ka-s-edge l d ksClient (_ , apiBF _ _ _) a ()
ka-s-edge l d ksClient (_ , apiTS _ _ _) a ()
ka-s-edge l d ksClient (_ , apiKA _ _ _) a ()
ka-s-edge l d ksClient (_ , apiLN _ _ _) a ()
ka-s-edge l d ksClient (_ , apiLF _ _ _) a ()
ka-s-edge l d ksClient (_ , break _) a ()
ka-s-edge l d (ksResp c) (_ , input _ _ N2N_ChainSync) a ()
ka-s-edge l d (ksResp c) (_ , input _ _ N2N_BlockFetch) a ()
ka-s-edge l d (ksResp c) (_ , input _ _ N2N_TxSubmission) a ()
ka-s-edge l d (ksResp c) (_ , input l′ d′ N2N_KeepAlive) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-s-edge l d (ksResp c) (_ , input _ _ N2N_LeiosNotify) a ()
ka-s-edge l d (ksResp c) (_ , input _ _ N2N_LeiosFetch) a ()
ka-s-edge l d (ksResp c) (_ , output _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , sndmsg _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , rcvmsg _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , tx _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , sndack _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , rcvack _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , ack _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , done _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiCS _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiBF _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiTS _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiKA _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiLN _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , apiLF _ _ _) a ()
ka-s-edge l d (ksResp c) (_ , break _) a ()
ka-s-edge l d ksDdone (_ , input _ _ _) a ()
ka-s-edge l d ksDdone (_ , output _ _ _) a ()
ka-s-edge l d ksDdone (_ , sndmsg _ _ _) a ()
ka-s-edge l d ksDdone (_ , rcvmsg _ _ _) a ()
ka-s-edge l d ksDdone (_ , tx _ _ _) a ()
ka-s-edge l d ksDdone (_ , sndack _ _ _) a ()
ka-s-edge l d ksDdone (_ , rcvack _ _ _) a ()
ka-s-edge l d ksDdone (_ , ack _ _ _) a ()
ka-s-edge l d ksDdone (_ , done _ _ N2N_ChainSync) a ()
ka-s-edge l d ksDdone (_ , done _ _ N2N_BlockFetch) a ()
ka-s-edge l d ksDdone (_ , done _ _ N2N_TxSubmission) a ()
ka-s-edge l d ksDdone (_ , done l′ d′ N2N_KeepAlive) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ka-s-edge l d ksDdone (_ , done _ _ N2N_LeiosNotify) a ()
ka-s-edge l d ksDdone (_ , done _ _ N2N_LeiosFetch) a ()
ka-s-edge l d ksDdone (_ , apiCS _ _ _) a ()
ka-s-edge l d ksDdone (_ , apiBF _ _ _) a ()
ka-s-edge l d ksDdone (_ , apiTS _ _ _) a ()
ka-s-edge l d ksDdone (_ , apiKA _ _ _) a ()
ka-s-edge l d ksDdone (_ , apiLN _ _ _) a ()
ka-s-edge l d ksDdone (_ , apiLF _ _ _) a ()
ka-s-edge l d ksDdone (_ , break _) a ()
ka-s-edge l d ksTerm (_ , input _ _ _) a ()
ka-s-edge l d ksTerm (_ , output _ _ _) a ()
ka-s-edge l d ksTerm (_ , sndmsg _ _ _) a ()
ka-s-edge l d ksTerm (_ , rcvmsg _ _ _) a ()
ka-s-edge l d ksTerm (_ , tx _ _ _) a ()
ka-s-edge l d ksTerm (_ , sndack _ _ _) a ()
ka-s-edge l d ksTerm (_ , rcvack _ _ _) a ()
ka-s-edge l d ksTerm (_ , ack _ _ _) a ()
ka-s-edge l d ksTerm (_ , done _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiCS _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiBF _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiTS _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiKA _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiLN _ _ _) a ()
ka-s-edge l d ksTerm (_ , apiLF _ _ _) a ()
ka-s-edge l d ksTerm (_ , break _) a ()

-- the ka-s spec confines to the (N2N_KeepAlive , d) slot
kaServerSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_KeepAlive d) (kaServerSpec l d)
kaServerSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_KeepAlive d) _ (ka-s-edge l d) ksClient

-- CS client: every fired edge is an apiCS/wire event on (N2N_ChainSync , d)
cs-c-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → csCnxt l d q at a ≡ just q′
          → peerAlpha N2N_ChainSync d at a
cs-c-edge l d ccIdle (_ , input _ _ _) a ()
cs-c-edge l d ccIdle (_ , output _ _ _) a ()
cs-c-edge l d ccIdle (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccIdle (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccIdle (_ , tx _ _ _) a ()
cs-c-edge l d ccIdle (_ , sndack _ _ _) a ()
cs-c-edge l d ccIdle (_ , rcvack _ _ _) a ()
cs-c-edge l d ccIdle (_ , ack _ _ _) a ()
cs-c-edge l d ccIdle (_ , done _ _ _) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSRequestNext) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSFindIntersect) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSDone) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ recvCSRollback) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-c-edge l d ccIdle (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-c-edge l d ccIdle (_ , apiBF _ _ _) a ()
cs-c-edge l d ccIdle (_ , apiTS _ _ _) a ()
cs-c-edge l d ccIdle (_ , apiKA _ _ _) a ()
cs-c-edge l d ccIdle (_ , apiLN _ _ _) a ()
cs-c-edge l d ccIdle (_ , apiLF _ _ _) a ()
cs-c-edge l d ccIdle (_ , break _) a ()
cs-c-edge l d ccWreq (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccWreq (_ , input _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccWreq (_ , input _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccWreq (_ , input _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccWreq (_ , input _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccWreq (_ , input _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccWreq (_ , output _ _ _) a ()
cs-c-edge l d ccWreq (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccWreq (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccWreq (_ , tx _ _ _) a ()
cs-c-edge l d ccWreq (_ , sndack _ _ _) a ()
cs-c-edge l d ccWreq (_ , rcvack _ _ _) a ()
cs-c-edge l d ccWreq (_ , ack _ _ _) a ()
cs-c-edge l d ccWreq (_ , done _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiCS _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiBF _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiTS _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiKA _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiLN _ _ _) a ()
cs-c-edge l d ccWreq (_ , apiLF _ _ _) a ()
cs-c-edge l d ccWreq (_ , break _) a ()
cs-c-edge l d ccAwait (_ , input _ _ _) a ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , keepAlive _) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , blockFetch _) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSRequestNext) ()
cs-c-edge l d ccAwait (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSAwaitReply) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccAwait (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccAwait (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSDone) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , txSubmission _) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosNotify _) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosFetch _) ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccAwait (_ , output _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccAwait (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccAwait (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccAwait (_ , tx _ _ _) a ()
cs-c-edge l d ccAwait (_ , sndack _ _ _) a ()
cs-c-edge l d ccAwait (_ , rcvack _ _ _) a ()
cs-c-edge l d ccAwait (_ , ack _ _ _) a ()
cs-c-edge l d ccAwait (_ , done _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiCS _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiBF _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiTS _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiKA _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiLN _ _ _) a ()
cs-c-edge l d ccAwait (_ , apiLF _ _ _) a ()
cs-c-edge l d ccAwait (_ , break _) a ()
cs-c-edge l d (ccWfi pts) (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d (ccWfi pts) (_ , input _ _ N2N_BlockFetch) a ()
cs-c-edge l d (ccWfi pts) (_ , input _ _ N2N_TxSubmission) a ()
cs-c-edge l d (ccWfi pts) (_ , input _ _ N2N_KeepAlive) a ()
cs-c-edge l d (ccWfi pts) (_ , input _ _ N2N_LeiosNotify) a ()
cs-c-edge l d (ccWfi pts) (_ , input _ _ N2N_LeiosFetch) a ()
cs-c-edge l d (ccWfi pts) (_ , output _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , sndmsg _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , rcvmsg _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , tx _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , sndack _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , rcvack _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , ack _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , done _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiCS _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiBF _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiTS _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiKA _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiLN _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , apiLF _ _ _) a ()
cs-c-edge l d (ccWfi pts) (_ , break _) a ()
cs-c-edge l d ccInt (_ , input _ _ _) a ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , keepAlive _) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , blockFetch _) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSRequestNext) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSAwaitReply) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
cs-c-edge l d ccInt (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccInt (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSDone) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , txSubmission _) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosNotify _) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosFetch _) ()
cs-c-edge l d ccInt (_ , output _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccInt (_ , output _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccInt (_ , output _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccInt (_ , output _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccInt (_ , output _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccInt (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccInt (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccInt (_ , tx _ _ _) a ()
cs-c-edge l d ccInt (_ , sndack _ _ _) a ()
cs-c-edge l d ccInt (_ , rcvack _ _ _) a ()
cs-c-edge l d ccInt (_ , ack _ _ _) a ()
cs-c-edge l d ccInt (_ , done _ _ _) a ()
cs-c-edge l d ccInt (_ , apiCS _ _ _) a ()
cs-c-edge l d ccInt (_ , apiBF _ _ _) a ()
cs-c-edge l d ccInt (_ , apiTS _ _ _) a ()
cs-c-edge l d ccInt (_ , apiKA _ _ _) a ()
cs-c-edge l d ccInt (_ , apiLN _ _ _) a ()
cs-c-edge l d ccInt (_ , apiLF _ _ _) a ()
cs-c-edge l d ccInt (_ , break _) a ()
cs-c-edge l d ccWdone (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccWdone (_ , input _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccWdone (_ , input _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccWdone (_ , input _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccWdone (_ , input _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccWdone (_ , input _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccWdone (_ , output _ _ _) a ()
cs-c-edge l d ccWdone (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccWdone (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccWdone (_ , tx _ _ _) a ()
cs-c-edge l d ccWdone (_ , sndack _ _ _) a ()
cs-c-edge l d ccWdone (_ , rcvack _ _ _) a ()
cs-c-edge l d ccWdone (_ , ack _ _ _) a ()
cs-c-edge l d ccWdone (_ , done _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiCS _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiBF _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiTS _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiKA _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiLN _ _ _) a ()
cs-c-edge l d ccWdone (_ , apiLF _ _ _) a ()
cs-c-edge l d ccWdone (_ , break _) a ()
cs-c-edge l d ccDdone (_ , input _ _ _) a ()
cs-c-edge l d ccDdone (_ , output _ _ _) a ()
cs-c-edge l d ccDdone (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccDdone (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccDdone (_ , tx _ _ _) a ()
cs-c-edge l d ccDdone (_ , sndack _ _ _) a ()
cs-c-edge l d ccDdone (_ , rcvack _ _ _) a ()
cs-c-edge l d ccDdone (_ , ack _ _ _) a ()
cs-c-edge l d ccDdone (_ , done l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccDdone (_ , done _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccDdone (_ , done _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccDdone (_ , done _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccDdone (_ , done _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccDdone (_ , done _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccDdone (_ , apiCS _ _ _) a ()
cs-c-edge l d ccDdone (_ , apiBF _ _ _) a ()
cs-c-edge l d ccDdone (_ , apiTS _ _ _) a ()
cs-c-edge l d ccDdone (_ , apiKA _ _ _) a ()
cs-c-edge l d ccDdone (_ , apiLN _ _ _) a ()
cs-c-edge l d ccDdone (_ , apiLF _ _ _) a ()
cs-c-edge l d ccDdone (_ , break _) a ()
cs-c-edge l d ccMust (_ , input _ _ _) a ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , keepAlive _) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , blockFetch _) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSRequestNext) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSAwaitReply) ()
cs-c-edge l d ccMust (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccMust (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSDone) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , txSubmission _) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosNotify _) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosFetch _) ()
cs-c-edge l d ccMust (_ , output _ _ N2N_BlockFetch) a ()
cs-c-edge l d ccMust (_ , output _ _ N2N_TxSubmission) a ()
cs-c-edge l d ccMust (_ , output _ _ N2N_KeepAlive) a ()
cs-c-edge l d ccMust (_ , output _ _ N2N_LeiosNotify) a ()
cs-c-edge l d ccMust (_ , output _ _ N2N_LeiosFetch) a ()
cs-c-edge l d ccMust (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccMust (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccMust (_ , tx _ _ _) a ()
cs-c-edge l d ccMust (_ , sndack _ _ _) a ()
cs-c-edge l d ccMust (_ , rcvack _ _ _) a ()
cs-c-edge l d ccMust (_ , ack _ _ _) a ()
cs-c-edge l d ccMust (_ , done _ _ _) a ()
cs-c-edge l d ccMust (_ , apiCS _ _ _) a ()
cs-c-edge l d ccMust (_ , apiBF _ _ _) a ()
cs-c-edge l d ccMust (_ , apiTS _ _ _) a ()
cs-c-edge l d ccMust (_ , apiKA _ _ _) a ()
cs-c-edge l d ccMust (_ , apiLN _ _ _) a ()
cs-c-edge l d ccMust (_ , apiLF _ _ _) a ()
cs-c-edge l d ccMust (_ , break _) a ()
cs-c-edge l d (ccArf ht) (_ , input _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , output _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , sndmsg _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , rcvmsg _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , tx _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , sndack _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , rcvack _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , ack _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , done _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSDone) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ recvCSRollforward) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ recvCSRollback) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-c-edge l d (ccArf ht) (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-c-edge l d (ccArf ht) (_ , apiBF _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , apiTS _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , apiKA _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , apiLN _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , apiLF _ _ _) a ()
cs-c-edge l d (ccArf ht) (_ , break _) a ()
cs-c-edge l d (ccArb pt) (_ , input _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , output _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , sndmsg _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , rcvmsg _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , tx _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , sndack _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , rcvack _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , ack _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , done _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSDone) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ recvCSRollback) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-c-edge l d (ccArb pt) (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-c-edge l d (ccArb pt) (_ , apiBF _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , apiTS _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , apiKA _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , apiLN _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , apiLF _ _ _) a ()
cs-c-edge l d (ccArb pt) (_ , break _) a ()
cs-c-edge l d (ccAif pt) (_ , input _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , output _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , sndmsg _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , rcvmsg _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , tx _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , sndack _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , rcvack _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , ack _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , done _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSDone) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ recvCSRollback) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ recvCSIntersectFound) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-c-edge l d (ccAif pt) (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-c-edge l d (ccAif pt) (_ , apiBF _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , apiTS _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , apiKA _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , apiLN _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , apiLF _ _ _) a ()
cs-c-edge l d (ccAif pt) (_ , break _) a ()
cs-c-edge l d (ccAin tp) (_ , input _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , output _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , sndmsg _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , rcvmsg _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , tx _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , sndack _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , rcvack _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , ack _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , done _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSDone) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ recvCSRollback) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ recvCSIntersectNotFound) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-c-edge l d (ccAin tp) (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-c-edge l d (ccAin tp) (_ , apiBF _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , apiTS _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , apiKA _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , apiLN _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , apiLF _ _ _) a ()
cs-c-edge l d (ccAin tp) (_ , break _) a ()
cs-c-edge l d ccTerm (_ , input _ _ _) a ()
cs-c-edge l d ccTerm (_ , output _ _ _) a ()
cs-c-edge l d ccTerm (_ , sndmsg _ _ _) a ()
cs-c-edge l d ccTerm (_ , rcvmsg _ _ _) a ()
cs-c-edge l d ccTerm (_ , tx _ _ _) a ()
cs-c-edge l d ccTerm (_ , sndack _ _ _) a ()
cs-c-edge l d ccTerm (_ , rcvack _ _ _) a ()
cs-c-edge l d ccTerm (_ , ack _ _ _) a ()
cs-c-edge l d ccTerm (_ , done _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiCS _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiBF _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiTS _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiKA _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiLN _ _ _) a ()
cs-c-edge l d ccTerm (_ , apiLF _ _ _) a ()
cs-c-edge l d ccTerm (_ , break _) a ()

-- the cs-c spec confines to the (N2N_ChainSync , d) slot
csClientSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_ChainSync d) (csClientSpec l d)
csClientSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_ChainSync d) _ (cs-c-edge l d) ccIdle

-- CS server: every fired edge is an apiCS/wire event on (N2N_ChainSync , d)
cs-s-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → csSnxt l d q at a ≡ just q′
          → peerAlpha N2N_ChainSync d at a
cs-s-edge l d csIdle (_ , input _ _ _) a ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , keepAlive _) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , blockFetch _) ()
cs-s-edge l d csIdle (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSRequestNext) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSAwaitReply) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollForward _ _)) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSRollBackward _ _)) ()
cs-s-edge l d csIdle (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSFindIntersect _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectFound _ _)) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , chainSync (MsgCSIntersectNotFound _)) ()
cs-s-edge l d csIdle (_ , output l′ d′ N2N_ChainSync) (_ , _ , _ , chainSync MsgCSDone) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , txSubmission _) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosNotify _) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_ChainSync) (_ , _ , _ , leiosFetch _) ()
cs-s-edge l d csIdle (_ , output _ _ N2N_BlockFetch) a ()
cs-s-edge l d csIdle (_ , output _ _ N2N_TxSubmission) a ()
cs-s-edge l d csIdle (_ , output _ _ N2N_KeepAlive) a ()
cs-s-edge l d csIdle (_ , output _ _ N2N_LeiosNotify) a ()
cs-s-edge l d csIdle (_ , output _ _ N2N_LeiosFetch) a ()
cs-s-edge l d csIdle (_ , sndmsg _ _ _) a ()
cs-s-edge l d csIdle (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csIdle (_ , tx _ _ _) a ()
cs-s-edge l d csIdle (_ , sndack _ _ _) a ()
cs-s-edge l d csIdle (_ , rcvack _ _ _) a ()
cs-s-edge l d csIdle (_ , ack _ _ _) a ()
cs-s-edge l d csIdle (_ , done _ _ _) a ()
cs-s-edge l d csIdle (_ , apiCS _ _ _) a ()
cs-s-edge l d csIdle (_ , apiBF _ _ _) a ()
cs-s-edge l d csIdle (_ , apiTS _ _ _) a ()
cs-s-edge l d csIdle (_ , apiKA _ _ _) a ()
cs-s-edge l d csIdle (_ , apiLN _ _ _) a ()
cs-s-edge l d csIdle (_ , apiLF _ _ _) a ()
cs-s-edge l d csIdle (_ , break _) a ()
cs-s-edge l d csAreq (_ , input _ _ _) a ()
cs-s-edge l d csAreq (_ , output _ _ _) a ()
cs-s-edge l d csAreq (_ , sndmsg _ _ _) a ()
cs-s-edge l d csAreq (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csAreq (_ , tx _ _ _) a ()
cs-s-edge l d csAreq (_ , sndack _ _ _) a ()
cs-s-edge l d csAreq (_ , rcvack _ _ _) a ()
cs-s-edge l d csAreq (_ , ack _ _ _) a ()
cs-s-edge l d csAreq (_ , done _ _ _) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSDone) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ recvCSRollback) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ reqCSRequestNext) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csAreq (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-s-edge l d csAreq (_ , apiBF _ _ _) a ()
cs-s-edge l d csAreq (_ , apiTS _ _ _) a ()
cs-s-edge l d csAreq (_ , apiKA _ _ _) a ()
cs-s-edge l d csAreq (_ , apiLN _ _ _) a ()
cs-s-edge l d csAreq (_ , apiLF _ _ _) a ()
cs-s-edge l d csAreq (_ , break _) a ()
cs-s-edge l d csCanAwait (_ , input _ _ _) a ()
cs-s-edge l d csCanAwait (_ , output _ _ _) a ()
cs-s-edge l d csCanAwait (_ , sndmsg _ _ _) a ()
cs-s-edge l d csCanAwait (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csCanAwait (_ , tx _ _ _) a ()
cs-s-edge l d csCanAwait (_ , sndack _ _ _) a ()
cs-s-edge l d csCanAwait (_ , rcvack _ _ _) a ()
cs-s-edge l d csCanAwait (_ , ack _ _ _) a ()
cs-s-edge l d csCanAwait (_ , done _ _ _) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSDone) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSAwaitReply) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSRollForward) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSRollBackward) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ recvCSRollback) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-s-edge l d csCanAwait (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-s-edge l d csCanAwait (_ , apiBF _ _ _) a ()
cs-s-edge l d csCanAwait (_ , apiTS _ _ _) a ()
cs-s-edge l d csCanAwait (_ , apiKA _ _ _) a ()
cs-s-edge l d csCanAwait (_ , apiLN _ _ _) a ()
cs-s-edge l d csCanAwait (_ , apiLF _ _ _) a ()
cs-s-edge l d csCanAwait (_ , break _) a ()
cs-s-edge l d (csAfi pts) (_ , input _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , output _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , sndmsg _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , rcvmsg _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , tx _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , sndack _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , rcvack _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , ack _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , done _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSDone) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ recvCSRollback) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-s-edge l d (csAfi pts) (_ , apiCS l′ d′ reqCSFindIntersect) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d (csAfi pts) (_ , apiBF _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , apiTS _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , apiKA _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , apiLN _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , apiLF _ _ _) a ()
cs-s-edge l d (csAfi pts) (_ , break _) a ()
cs-s-edge l d csInt (_ , input _ _ _) a ()
cs-s-edge l d csInt (_ , output _ _ _) a ()
cs-s-edge l d csInt (_ , sndmsg _ _ _) a ()
cs-s-edge l d csInt (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csInt (_ , tx _ _ _) a ()
cs-s-edge l d csInt (_ , sndack _ _ _) a ()
cs-s-edge l d csInt (_ , rcvack _ _ _) a ()
cs-s-edge l d csInt (_ , ack _ _ _) a ()
cs-s-edge l d csInt (_ , done _ _ _) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSDone) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSRollForward) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSRollBackward) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSIntersectFound) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csInt (_ , apiCS l′ d′ sendCSIntersectNotFound) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csInt (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ recvCSRollback) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-s-edge l d csInt (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-s-edge l d csInt (_ , apiBF _ _ _) a ()
cs-s-edge l d csInt (_ , apiTS _ _ _) a ()
cs-s-edge l d csInt (_ , apiKA _ _ _) a ()
cs-s-edge l d csInt (_ , apiLN _ _ _) a ()
cs-s-edge l d csInt (_ , apiLF _ _ _) a ()
cs-s-edge l d csInt (_ , break _) a ()
cs-s-edge l d csDdone (_ , input _ _ _) a ()
cs-s-edge l d csDdone (_ , output _ _ _) a ()
cs-s-edge l d csDdone (_ , sndmsg _ _ _) a ()
cs-s-edge l d csDdone (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csDdone (_ , tx _ _ _) a ()
cs-s-edge l d csDdone (_ , sndack _ _ _) a ()
cs-s-edge l d csDdone (_ , rcvack _ _ _) a ()
cs-s-edge l d csDdone (_ , ack _ _ _) a ()
cs-s-edge l d csDdone (_ , done l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csDdone (_ , done _ _ N2N_BlockFetch) a ()
cs-s-edge l d csDdone (_ , done _ _ N2N_TxSubmission) a ()
cs-s-edge l d csDdone (_ , done _ _ N2N_KeepAlive) a ()
cs-s-edge l d csDdone (_ , done _ _ N2N_LeiosNotify) a ()
cs-s-edge l d csDdone (_ , done _ _ N2N_LeiosFetch) a ()
cs-s-edge l d csDdone (_ , apiCS _ _ _) a ()
cs-s-edge l d csDdone (_ , apiBF _ _ _) a ()
cs-s-edge l d csDdone (_ , apiTS _ _ _) a ()
cs-s-edge l d csDdone (_ , apiKA _ _ _) a ()
cs-s-edge l d csDdone (_ , apiLN _ _ _) a ()
cs-s-edge l d csDdone (_ , apiLF _ _ _) a ()
cs-s-edge l d csDdone (_ , break _) a ()
cs-s-edge l d csMust (_ , input _ _ _) a ()
cs-s-edge l d csMust (_ , output _ _ _) a ()
cs-s-edge l d csMust (_ , sndmsg _ _ _) a ()
cs-s-edge l d csMust (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csMust (_ , tx _ _ _) a ()
cs-s-edge l d csMust (_ , sndack _ _ _) a ()
cs-s-edge l d csMust (_ , rcvack _ _ _) a ()
cs-s-edge l d csMust (_ , ack _ _ _) a ()
cs-s-edge l d csMust (_ , done _ _ _) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSRequestNext) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSFindIntersect) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSDone) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSAwaitReply) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSRollForward) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSRollBackward) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSIntersectFound) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ sendCSIntersectNotFound) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ recvCSRollforward) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ recvCSRollback) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ recvCSIntersectFound) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ recvCSIntersectNotFound) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ reqCSRequestNext) a ()
cs-s-edge l d csMust (_ , apiCS l′ d′ reqCSFindIntersect) a ()
cs-s-edge l d csMust (_ , apiBF _ _ _) a ()
cs-s-edge l d csMust (_ , apiTS _ _ _) a ()
cs-s-edge l d csMust (_ , apiKA _ _ _) a ()
cs-s-edge l d csMust (_ , apiLN _ _ _) a ()
cs-s-edge l d csMust (_ , apiLF _ _ _) a ()
cs-s-edge l d csMust (_ , break _) a ()
cs-s-edge l d (csWrf ht) (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d (csWrf ht) (_ , input _ _ N2N_BlockFetch) a ()
cs-s-edge l d (csWrf ht) (_ , input _ _ N2N_TxSubmission) a ()
cs-s-edge l d (csWrf ht) (_ , input _ _ N2N_KeepAlive) a ()
cs-s-edge l d (csWrf ht) (_ , input _ _ N2N_LeiosNotify) a ()
cs-s-edge l d (csWrf ht) (_ , input _ _ N2N_LeiosFetch) a ()
cs-s-edge l d (csWrf ht) (_ , output _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , sndmsg _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , rcvmsg _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , tx _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , sndack _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , rcvack _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , ack _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , done _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiCS _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiBF _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiTS _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiKA _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiLN _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , apiLF _ _ _) a ()
cs-s-edge l d (csWrf ht) (_ , break _) a ()
cs-s-edge l d (csWrb pt) (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d (csWrb pt) (_ , input _ _ N2N_BlockFetch) a ()
cs-s-edge l d (csWrb pt) (_ , input _ _ N2N_TxSubmission) a ()
cs-s-edge l d (csWrb pt) (_ , input _ _ N2N_KeepAlive) a ()
cs-s-edge l d (csWrb pt) (_ , input _ _ N2N_LeiosNotify) a ()
cs-s-edge l d (csWrb pt) (_ , input _ _ N2N_LeiosFetch) a ()
cs-s-edge l d (csWrb pt) (_ , output _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , sndmsg _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , rcvmsg _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , tx _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , sndack _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , rcvack _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , ack _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , done _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiCS _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiBF _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiTS _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiKA _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiLN _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , apiLF _ _ _) a ()
cs-s-edge l d (csWrb pt) (_ , break _) a ()
cs-s-edge l d csWar (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d csWar (_ , input _ _ N2N_BlockFetch) a ()
cs-s-edge l d csWar (_ , input _ _ N2N_TxSubmission) a ()
cs-s-edge l d csWar (_ , input _ _ N2N_KeepAlive) a ()
cs-s-edge l d csWar (_ , input _ _ N2N_LeiosNotify) a ()
cs-s-edge l d csWar (_ , input _ _ N2N_LeiosFetch) a ()
cs-s-edge l d csWar (_ , output _ _ _) a ()
cs-s-edge l d csWar (_ , sndmsg _ _ _) a ()
cs-s-edge l d csWar (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csWar (_ , tx _ _ _) a ()
cs-s-edge l d csWar (_ , sndack _ _ _) a ()
cs-s-edge l d csWar (_ , rcvack _ _ _) a ()
cs-s-edge l d csWar (_ , ack _ _ _) a ()
cs-s-edge l d csWar (_ , done _ _ _) a ()
cs-s-edge l d csWar (_ , apiCS _ _ _) a ()
cs-s-edge l d csWar (_ , apiBF _ _ _) a ()
cs-s-edge l d csWar (_ , apiTS _ _ _) a ()
cs-s-edge l d csWar (_ , apiKA _ _ _) a ()
cs-s-edge l d csWar (_ , apiLN _ _ _) a ()
cs-s-edge l d csWar (_ , apiLF _ _ _) a ()
cs-s-edge l d csWar (_ , break _) a ()
cs-s-edge l d (csWif pt) (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d (csWif pt) (_ , input _ _ N2N_BlockFetch) a ()
cs-s-edge l d (csWif pt) (_ , input _ _ N2N_TxSubmission) a ()
cs-s-edge l d (csWif pt) (_ , input _ _ N2N_KeepAlive) a ()
cs-s-edge l d (csWif pt) (_ , input _ _ N2N_LeiosNotify) a ()
cs-s-edge l d (csWif pt) (_ , input _ _ N2N_LeiosFetch) a ()
cs-s-edge l d (csWif pt) (_ , output _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , sndmsg _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , rcvmsg _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , tx _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , sndack _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , rcvack _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , ack _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , done _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiCS _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiBF _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiTS _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiKA _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiLN _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , apiLF _ _ _) a ()
cs-s-edge l d (csWif pt) (_ , break _) a ()
cs-s-edge l d (csWin tp) (_ , input l′ d′ N2N_ChainSync) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
cs-s-edge l d (csWin tp) (_ , input _ _ N2N_BlockFetch) a ()
cs-s-edge l d (csWin tp) (_ , input _ _ N2N_TxSubmission) a ()
cs-s-edge l d (csWin tp) (_ , input _ _ N2N_KeepAlive) a ()
cs-s-edge l d (csWin tp) (_ , input _ _ N2N_LeiosNotify) a ()
cs-s-edge l d (csWin tp) (_ , input _ _ N2N_LeiosFetch) a ()
cs-s-edge l d (csWin tp) (_ , output _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , sndmsg _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , rcvmsg _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , tx _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , sndack _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , rcvack _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , ack _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , done _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiCS _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiBF _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiTS _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiKA _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiLN _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , apiLF _ _ _) a ()
cs-s-edge l d (csWin tp) (_ , break _) a ()
cs-s-edge l d csTerm (_ , input _ _ _) a ()
cs-s-edge l d csTerm (_ , output _ _ _) a ()
cs-s-edge l d csTerm (_ , sndmsg _ _ _) a ()
cs-s-edge l d csTerm (_ , rcvmsg _ _ _) a ()
cs-s-edge l d csTerm (_ , tx _ _ _) a ()
cs-s-edge l d csTerm (_ , sndack _ _ _) a ()
cs-s-edge l d csTerm (_ , rcvack _ _ _) a ()
cs-s-edge l d csTerm (_ , ack _ _ _) a ()
cs-s-edge l d csTerm (_ , done _ _ _) a ()
cs-s-edge l d csTerm (_ , apiCS _ _ _) a ()
cs-s-edge l d csTerm (_ , apiBF _ _ _) a ()
cs-s-edge l d csTerm (_ , apiTS _ _ _) a ()
cs-s-edge l d csTerm (_ , apiKA _ _ _) a ()
cs-s-edge l d csTerm (_ , apiLN _ _ _) a ()
cs-s-edge l d csTerm (_ , apiLF _ _ _) a ()
cs-s-edge l d csTerm (_ , break _) a ()

-- the cs-s spec confines to the (N2N_ChainSync , d) slot
csServerSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_ChainSync d) (csServerSpec l d)
csServerSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_ChainSync d) _ (cs-s-edge l d) csIdle

-- BF client: every fired edge is an apiBF/wire event on (N2N_BlockFetch , d)
bf-c-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → bfCnxt l d q at a ≡ just q′
          → peerAlpha N2N_BlockFetch d at a
bf-c-edge l d bcIdle (_ , input _ _ _) a ()
bf-c-edge l d bcIdle (_ , output _ _ _) a ()
bf-c-edge l d bcIdle (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcIdle (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcIdle (_ , tx _ _ _) a ()
bf-c-edge l d bcIdle (_ , sndack _ _ _) a ()
bf-c-edge l d bcIdle (_ , rcvack _ _ _) a ()
bf-c-edge l d bcIdle (_ , ack _ _ _) a ()
bf-c-edge l d bcIdle (_ , done _ _ _) a ()
bf-c-edge l d bcIdle (_ , apiCS _ _ _) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFRequestRange) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFClientDone) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFStartBatch) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFNoBlocks) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFBlock) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ sendBFBatchDone) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ recvBFBlock) a ()
bf-c-edge l d bcIdle (_ , apiBF l′ d′ reqBFRange) a ()
bf-c-edge l d bcIdle (_ , apiTS _ _ _) a ()
bf-c-edge l d bcIdle (_ , apiKA _ _ _) a ()
bf-c-edge l d bcIdle (_ , apiLN _ _ _) a ()
bf-c-edge l d bcIdle (_ , apiLF _ _ _) a ()
bf-c-edge l d bcIdle (_ , break _) a ()
bf-c-edge l d (bcWrr r) (_ , input _ _ N2N_ChainSync) a ()
bf-c-edge l d (bcWrr r) (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d (bcWrr r) (_ , input _ _ N2N_TxSubmission) a ()
bf-c-edge l d (bcWrr r) (_ , input _ _ N2N_KeepAlive) a ()
bf-c-edge l d (bcWrr r) (_ , input _ _ N2N_LeiosNotify) a ()
bf-c-edge l d (bcWrr r) (_ , input _ _ N2N_LeiosFetch) a ()
bf-c-edge l d (bcWrr r) (_ , output _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , sndmsg _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , rcvmsg _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , tx _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , sndack _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , rcvack _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , ack _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , done _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiCS _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiBF _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiTS _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiKA _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiLN _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , apiLF _ _ _) a ()
bf-c-edge l d (bcWrr r) (_ , break _) a ()
bf-c-edge l d bcBusy (_ , input _ _ _) a ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_ChainSync) a ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , keepAlive _) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgRequestRange _)) ()
bf-c-edge l d bcBusy (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgStartBatch) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcBusy (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgNoBlocks) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgBlock _)) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgBatchDone) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgClientDone) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , chainSync _) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , txSubmission _) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosNotify _) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosFetch _) ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_TxSubmission) a ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_KeepAlive) a ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_LeiosNotify) a ()
bf-c-edge l d bcBusy (_ , output _ _ N2N_LeiosFetch) a ()
bf-c-edge l d bcBusy (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcBusy (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcBusy (_ , tx _ _ _) a ()
bf-c-edge l d bcBusy (_ , sndack _ _ _) a ()
bf-c-edge l d bcBusy (_ , rcvack _ _ _) a ()
bf-c-edge l d bcBusy (_ , ack _ _ _) a ()
bf-c-edge l d bcBusy (_ , done _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiCS _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiBF _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiTS _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiKA _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiLN _ _ _) a ()
bf-c-edge l d bcBusy (_ , apiLF _ _ _) a ()
bf-c-edge l d bcBusy (_ , break _) a ()
bf-c-edge l d bcWcd (_ , input _ _ N2N_ChainSync) a ()
bf-c-edge l d bcWcd (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcWcd (_ , input _ _ N2N_TxSubmission) a ()
bf-c-edge l d bcWcd (_ , input _ _ N2N_KeepAlive) a ()
bf-c-edge l d bcWcd (_ , input _ _ N2N_LeiosNotify) a ()
bf-c-edge l d bcWcd (_ , input _ _ N2N_LeiosFetch) a ()
bf-c-edge l d bcWcd (_ , output _ _ _) a ()
bf-c-edge l d bcWcd (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcWcd (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcWcd (_ , tx _ _ _) a ()
bf-c-edge l d bcWcd (_ , sndack _ _ _) a ()
bf-c-edge l d bcWcd (_ , rcvack _ _ _) a ()
bf-c-edge l d bcWcd (_ , ack _ _ _) a ()
bf-c-edge l d bcWcd (_ , done _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiCS _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiBF _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiTS _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiKA _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiLN _ _ _) a ()
bf-c-edge l d bcWcd (_ , apiLF _ _ _) a ()
bf-c-edge l d bcWcd (_ , break _) a ()
bf-c-edge l d bcDdone (_ , input _ _ _) a ()
bf-c-edge l d bcDdone (_ , output _ _ _) a ()
bf-c-edge l d bcDdone (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcDdone (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcDdone (_ , tx _ _ _) a ()
bf-c-edge l d bcDdone (_ , sndack _ _ _) a ()
bf-c-edge l d bcDdone (_ , rcvack _ _ _) a ()
bf-c-edge l d bcDdone (_ , ack _ _ _) a ()
bf-c-edge l d bcDdone (_ , done _ _ N2N_ChainSync) a ()
bf-c-edge l d bcDdone (_ , done l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcDdone (_ , done _ _ N2N_TxSubmission) a ()
bf-c-edge l d bcDdone (_ , done _ _ N2N_KeepAlive) a ()
bf-c-edge l d bcDdone (_ , done _ _ N2N_LeiosNotify) a ()
bf-c-edge l d bcDdone (_ , done _ _ N2N_LeiosFetch) a ()
bf-c-edge l d bcDdone (_ , apiCS _ _ _) a ()
bf-c-edge l d bcDdone (_ , apiBF _ _ _) a ()
bf-c-edge l d bcDdone (_ , apiTS _ _ _) a ()
bf-c-edge l d bcDdone (_ , apiKA _ _ _) a ()
bf-c-edge l d bcDdone (_ , apiLN _ _ _) a ()
bf-c-edge l d bcDdone (_ , apiLF _ _ _) a ()
bf-c-edge l d bcDdone (_ , break _) a ()
bf-c-edge l d bcStream (_ , input _ _ _) a ()
bf-c-edge l d bcStream (_ , output _ _ N2N_ChainSync) a ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , keepAlive _) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgRequestRange _)) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgStartBatch) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgNoBlocks) ()
bf-c-edge l d bcStream (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgBlock _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcStream (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgBatchDone) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgClientDone) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , chainSync _) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , txSubmission _) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosNotify _) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosFetch _) ()
bf-c-edge l d bcStream (_ , output _ _ N2N_TxSubmission) a ()
bf-c-edge l d bcStream (_ , output _ _ N2N_KeepAlive) a ()
bf-c-edge l d bcStream (_ , output _ _ N2N_LeiosNotify) a ()
bf-c-edge l d bcStream (_ , output _ _ N2N_LeiosFetch) a ()
bf-c-edge l d bcStream (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcStream (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcStream (_ , tx _ _ _) a ()
bf-c-edge l d bcStream (_ , sndack _ _ _) a ()
bf-c-edge l d bcStream (_ , rcvack _ _ _) a ()
bf-c-edge l d bcStream (_ , ack _ _ _) a ()
bf-c-edge l d bcStream (_ , done _ _ _) a ()
bf-c-edge l d bcStream (_ , apiCS _ _ _) a ()
bf-c-edge l d bcStream (_ , apiBF _ _ _) a ()
bf-c-edge l d bcStream (_ , apiTS _ _ _) a ()
bf-c-edge l d bcStream (_ , apiKA _ _ _) a ()
bf-c-edge l d bcStream (_ , apiLN _ _ _) a ()
bf-c-edge l d bcStream (_ , apiLF _ _ _) a ()
bf-c-edge l d bcStream (_ , break _) a ()
bf-c-edge l d (bcAblk b) (_ , input _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , output _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , sndmsg _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , rcvmsg _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , tx _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , sndack _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , rcvack _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , ack _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , done _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , apiCS _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFRequestRange) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFClientDone) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFStartBatch) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFNoBlocks) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFBlock) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ sendBFBatchDone) a ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ recvBFBlock) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-c-edge l d (bcAblk b) (_ , apiBF l′ d′ reqBFRange) a ()
bf-c-edge l d (bcAblk b) (_ , apiTS _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , apiKA _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , apiLN _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , apiLF _ _ _) a ()
bf-c-edge l d (bcAblk b) (_ , break _) a ()
bf-c-edge l d bcTerm (_ , input _ _ _) a ()
bf-c-edge l d bcTerm (_ , output _ _ _) a ()
bf-c-edge l d bcTerm (_ , sndmsg _ _ _) a ()
bf-c-edge l d bcTerm (_ , rcvmsg _ _ _) a ()
bf-c-edge l d bcTerm (_ , tx _ _ _) a ()
bf-c-edge l d bcTerm (_ , sndack _ _ _) a ()
bf-c-edge l d bcTerm (_ , rcvack _ _ _) a ()
bf-c-edge l d bcTerm (_ , ack _ _ _) a ()
bf-c-edge l d bcTerm (_ , done _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiCS _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiBF _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiTS _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiKA _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiLN _ _ _) a ()
bf-c-edge l d bcTerm (_ , apiLF _ _ _) a ()
bf-c-edge l d bcTerm (_ , break _) a ()

-- the bf-c spec confines to the (N2N_BlockFetch , d) slot
bfClientSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_BlockFetch d) (bfClientSpec l d)
bfClientSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_BlockFetch d) _ (bf-c-edge l d) bcIdle

-- BF server: every fired edge is an apiBF/wire event on (N2N_BlockFetch , d)
bf-s-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → bfSnxt l d q at a ≡ just q′
          → peerAlpha N2N_BlockFetch d at a
bf-s-edge l d bsIdle (_ , input _ _ _) a ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_ChainSync) a ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , keepAlive _) ()
bf-s-edge l d bsIdle (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgRequestRange _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgStartBatch) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgNoBlocks) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch (MsgBlock _)) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgBatchDone) ()
bf-s-edge l d bsIdle (_ , output l′ d′ N2N_BlockFetch) (_ , _ , _ , blockFetch MsgClientDone) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , chainSync _) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , txSubmission _) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosNotify _) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_BlockFetch) (_ , _ , _ , leiosFetch _) ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_TxSubmission) a ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_KeepAlive) a ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_LeiosNotify) a ()
bf-s-edge l d bsIdle (_ , output _ _ N2N_LeiosFetch) a ()
bf-s-edge l d bsIdle (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsIdle (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsIdle (_ , tx _ _ _) a ()
bf-s-edge l d bsIdle (_ , sndack _ _ _) a ()
bf-s-edge l d bsIdle (_ , rcvack _ _ _) a ()
bf-s-edge l d bsIdle (_ , ack _ _ _) a ()
bf-s-edge l d bsIdle (_ , done _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiCS _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiBF _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiTS _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiKA _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiLN _ _ _) a ()
bf-s-edge l d bsIdle (_ , apiLF _ _ _) a ()
bf-s-edge l d bsIdle (_ , break _) a ()
bf-s-edge l d (bsAreq r) (_ , input _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , output _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , sndmsg _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , rcvmsg _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , tx _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , sndack _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , rcvack _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , ack _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , done _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , apiCS _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFRequestRange) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFClientDone) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFStartBatch) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFNoBlocks) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFBlock) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ sendBFBatchDone) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ recvBFBlock) a ()
bf-s-edge l d (bsAreq r) (_ , apiBF l′ d′ reqBFRange) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d (bsAreq r) (_ , apiTS _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , apiKA _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , apiLN _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , apiLF _ _ _) a ()
bf-s-edge l d (bsAreq r) (_ , break _) a ()
bf-s-edge l d bsBusy (_ , input _ _ _) a ()
bf-s-edge l d bsBusy (_ , output _ _ _) a ()
bf-s-edge l d bsBusy (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsBusy (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsBusy (_ , tx _ _ _) a ()
bf-s-edge l d bsBusy (_ , sndack _ _ _) a ()
bf-s-edge l d bsBusy (_ , rcvack _ _ _) a ()
bf-s-edge l d bsBusy (_ , ack _ _ _) a ()
bf-s-edge l d bsBusy (_ , done _ _ _) a ()
bf-s-edge l d bsBusy (_ , apiCS _ _ _) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFRequestRange) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFClientDone) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFStartBatch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFNoBlocks) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFBlock) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ sendBFBatchDone) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ recvBFBlock) a ()
bf-s-edge l d bsBusy (_ , apiBF l′ d′ reqBFRange) a ()
bf-s-edge l d bsBusy (_ , apiTS _ _ _) a ()
bf-s-edge l d bsBusy (_ , apiKA _ _ _) a ()
bf-s-edge l d bsBusy (_ , apiLN _ _ _) a ()
bf-s-edge l d bsBusy (_ , apiLF _ _ _) a ()
bf-s-edge l d bsBusy (_ , break _) a ()
bf-s-edge l d bsDdone (_ , input _ _ _) a ()
bf-s-edge l d bsDdone (_ , output _ _ _) a ()
bf-s-edge l d bsDdone (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsDdone (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsDdone (_ , tx _ _ _) a ()
bf-s-edge l d bsDdone (_ , sndack _ _ _) a ()
bf-s-edge l d bsDdone (_ , rcvack _ _ _) a ()
bf-s-edge l d bsDdone (_ , ack _ _ _) a ()
bf-s-edge l d bsDdone (_ , done _ _ N2N_ChainSync) a ()
bf-s-edge l d bsDdone (_ , done l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsDdone (_ , done _ _ N2N_TxSubmission) a ()
bf-s-edge l d bsDdone (_ , done _ _ N2N_KeepAlive) a ()
bf-s-edge l d bsDdone (_ , done _ _ N2N_LeiosNotify) a ()
bf-s-edge l d bsDdone (_ , done _ _ N2N_LeiosFetch) a ()
bf-s-edge l d bsDdone (_ , apiCS _ _ _) a ()
bf-s-edge l d bsDdone (_ , apiBF _ _ _) a ()
bf-s-edge l d bsDdone (_ , apiTS _ _ _) a ()
bf-s-edge l d bsDdone (_ , apiKA _ _ _) a ()
bf-s-edge l d bsDdone (_ , apiLN _ _ _) a ()
bf-s-edge l d bsDdone (_ , apiLF _ _ _) a ()
bf-s-edge l d bsDdone (_ , break _) a ()
bf-s-edge l d bsWsb (_ , input _ _ N2N_ChainSync) a ()
bf-s-edge l d bsWsb (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsWsb (_ , input _ _ N2N_TxSubmission) a ()
bf-s-edge l d bsWsb (_ , input _ _ N2N_KeepAlive) a ()
bf-s-edge l d bsWsb (_ , input _ _ N2N_LeiosNotify) a ()
bf-s-edge l d bsWsb (_ , input _ _ N2N_LeiosFetch) a ()
bf-s-edge l d bsWsb (_ , output _ _ _) a ()
bf-s-edge l d bsWsb (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsWsb (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsWsb (_ , tx _ _ _) a ()
bf-s-edge l d bsWsb (_ , sndack _ _ _) a ()
bf-s-edge l d bsWsb (_ , rcvack _ _ _) a ()
bf-s-edge l d bsWsb (_ , ack _ _ _) a ()
bf-s-edge l d bsWsb (_ , done _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiCS _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiBF _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiTS _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiKA _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiLN _ _ _) a ()
bf-s-edge l d bsWsb (_ , apiLF _ _ _) a ()
bf-s-edge l d bsWsb (_ , break _) a ()
bf-s-edge l d bsStream (_ , input _ _ _) a ()
bf-s-edge l d bsStream (_ , output _ _ _) a ()
bf-s-edge l d bsStream (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsStream (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsStream (_ , tx _ _ _) a ()
bf-s-edge l d bsStream (_ , sndack _ _ _) a ()
bf-s-edge l d bsStream (_ , rcvack _ _ _) a ()
bf-s-edge l d bsStream (_ , ack _ _ _) a ()
bf-s-edge l d bsStream (_ , done _ _ _) a ()
bf-s-edge l d bsStream (_ , apiCS _ _ _) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFRequestRange) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFClientDone) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFStartBatch) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFNoBlocks) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFBlock) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ sendBFBatchDone) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ recvBFBlock) a ()
bf-s-edge l d bsStream (_ , apiBF l′ d′ reqBFRange) a ()
bf-s-edge l d bsStream (_ , apiTS _ _ _) a ()
bf-s-edge l d bsStream (_ , apiKA _ _ _) a ()
bf-s-edge l d bsStream (_ , apiLN _ _ _) a ()
bf-s-edge l d bsStream (_ , apiLF _ _ _) a ()
bf-s-edge l d bsStream (_ , break _) a ()
bf-s-edge l d bsWnb (_ , input _ _ N2N_ChainSync) a ()
bf-s-edge l d bsWnb (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsWnb (_ , input _ _ N2N_TxSubmission) a ()
bf-s-edge l d bsWnb (_ , input _ _ N2N_KeepAlive) a ()
bf-s-edge l d bsWnb (_ , input _ _ N2N_LeiosNotify) a ()
bf-s-edge l d bsWnb (_ , input _ _ N2N_LeiosFetch) a ()
bf-s-edge l d bsWnb (_ , output _ _ _) a ()
bf-s-edge l d bsWnb (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsWnb (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsWnb (_ , tx _ _ _) a ()
bf-s-edge l d bsWnb (_ , sndack _ _ _) a ()
bf-s-edge l d bsWnb (_ , rcvack _ _ _) a ()
bf-s-edge l d bsWnb (_ , ack _ _ _) a ()
bf-s-edge l d bsWnb (_ , done _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiCS _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiBF _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiTS _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiKA _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiLN _ _ _) a ()
bf-s-edge l d bsWnb (_ , apiLF _ _ _) a ()
bf-s-edge l d bsWnb (_ , break _) a ()
bf-s-edge l d (bsWblk b) (_ , input _ _ N2N_ChainSync) a ()
bf-s-edge l d (bsWblk b) (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d (bsWblk b) (_ , input _ _ N2N_TxSubmission) a ()
bf-s-edge l d (bsWblk b) (_ , input _ _ N2N_KeepAlive) a ()
bf-s-edge l d (bsWblk b) (_ , input _ _ N2N_LeiosNotify) a ()
bf-s-edge l d (bsWblk b) (_ , input _ _ N2N_LeiosFetch) a ()
bf-s-edge l d (bsWblk b) (_ , output _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , sndmsg _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , rcvmsg _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , tx _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , sndack _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , rcvack _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , ack _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , done _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiCS _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiBF _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiTS _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiKA _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiLN _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , apiLF _ _ _) a ()
bf-s-edge l d (bsWblk b) (_ , break _) a ()
bf-s-edge l d bsWbd (_ , input _ _ N2N_ChainSync) a ()
bf-s-edge l d bsWbd (_ , input l′ d′ N2N_BlockFetch) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
bf-s-edge l d bsWbd (_ , input _ _ N2N_TxSubmission) a ()
bf-s-edge l d bsWbd (_ , input _ _ N2N_KeepAlive) a ()
bf-s-edge l d bsWbd (_ , input _ _ N2N_LeiosNotify) a ()
bf-s-edge l d bsWbd (_ , input _ _ N2N_LeiosFetch) a ()
bf-s-edge l d bsWbd (_ , output _ _ _) a ()
bf-s-edge l d bsWbd (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsWbd (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsWbd (_ , tx _ _ _) a ()
bf-s-edge l d bsWbd (_ , sndack _ _ _) a ()
bf-s-edge l d bsWbd (_ , rcvack _ _ _) a ()
bf-s-edge l d bsWbd (_ , ack _ _ _) a ()
bf-s-edge l d bsWbd (_ , done _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiCS _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiBF _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiTS _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiKA _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiLN _ _ _) a ()
bf-s-edge l d bsWbd (_ , apiLF _ _ _) a ()
bf-s-edge l d bsWbd (_ , break _) a ()
bf-s-edge l d bsTerm (_ , input _ _ _) a ()
bf-s-edge l d bsTerm (_ , output _ _ _) a ()
bf-s-edge l d bsTerm (_ , sndmsg _ _ _) a ()
bf-s-edge l d bsTerm (_ , rcvmsg _ _ _) a ()
bf-s-edge l d bsTerm (_ , tx _ _ _) a ()
bf-s-edge l d bsTerm (_ , sndack _ _ _) a ()
bf-s-edge l d bsTerm (_ , rcvack _ _ _) a ()
bf-s-edge l d bsTerm (_ , ack _ _ _) a ()
bf-s-edge l d bsTerm (_ , done _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiCS _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiBF _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiTS _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiKA _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiLN _ _ _) a ()
bf-s-edge l d bsTerm (_ , apiLF _ _ _) a ()
bf-s-edge l d bsTerm (_ , break _) a ()

-- the bf-s spec confines to the (N2N_BlockFetch , d) slot
bfServerSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_BlockFetch d) (bfServerSpec l d)
bfServerSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_BlockFetch d) _ (bf-s-edge l d) bsIdle

-- TS client: every fired edge is an apiTS/wire event on (N2N_TxSubmission , d)
ts-c-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → tsCnxt l d q at a ≡ just q′
          → peerAlpha N2N_TxSubmission d at a
ts-c-edge l d tcInit (_ , input _ _ N2N_ChainSync) a ()
ts-c-edge l d tcInit (_ , input _ _ N2N_BlockFetch) a ()
ts-c-edge l d tcInit (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcInit (_ , input _ _ N2N_KeepAlive) a ()
ts-c-edge l d tcInit (_ , input _ _ N2N_LeiosNotify) a ()
ts-c-edge l d tcInit (_ , input _ _ N2N_LeiosFetch) a ()
ts-c-edge l d tcInit (_ , output _ _ _) a ()
ts-c-edge l d tcInit (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcInit (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcInit (_ , tx _ _ _) a ()
ts-c-edge l d tcInit (_ , sndack _ _ _) a ()
ts-c-edge l d tcInit (_ , rcvack _ _ _) a ()
ts-c-edge l d tcInit (_ , ack _ _ _) a ()
ts-c-edge l d tcInit (_ , done _ _ _) a ()
ts-c-edge l d tcInit (_ , apiCS _ _ _) a ()
ts-c-edge l d tcInit (_ , apiBF _ _ _) a ()
ts-c-edge l d tcInit (_ , apiTS _ _ _) a ()
ts-c-edge l d tcInit (_ , apiKA _ _ _) a ()
ts-c-edge l d tcInit (_ , apiLN _ _ _) a ()
ts-c-edge l d tcInit (_ , apiLF _ _ _) a ()
ts-c-edge l d tcInit (_ , break _) a ()
ts-c-edge l d tcIdle (_ , input _ _ _) a ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_ChainSync) a ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_BlockFetch) a ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , keepAlive _) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , blockFetch _) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , chainSync _) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSInit) ()
ts-c-edge l d tcIdle (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
ts-c-edge l d tcIdle (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSDone) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosNotify _) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosFetch _) ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_KeepAlive) a ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_LeiosNotify) a ()
ts-c-edge l d tcIdle (_ , output _ _ N2N_LeiosFetch) a ()
ts-c-edge l d tcIdle (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcIdle (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcIdle (_ , tx _ _ _) a ()
ts-c-edge l d tcIdle (_ , sndack _ _ _) a ()
ts-c-edge l d tcIdle (_ , rcvack _ _ _) a ()
ts-c-edge l d tcIdle (_ , ack _ _ _) a ()
ts-c-edge l d tcIdle (_ , done _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiCS _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiBF _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiTS _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiKA _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiLN _ _ _) a ()
ts-c-edge l d tcIdle (_ , apiLF _ _ _) a ()
ts-c-edge l d tcIdle (_ , break _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , input _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , output _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , sndmsg _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , rcvmsg _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , tx _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , sndack _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , rcvack _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , ack _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , done _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiCS _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiBF _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSReplyTxIds) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSDone) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ recvTSRequestTxIds) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiKA _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiLN _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , apiLF _ _ _) a ()
ts-c-edge l d (tcAri (Blocking , a₁ , r₁)) (_ , break _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , input _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , output _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , sndmsg _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , rcvmsg _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , tx _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , sndack _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , rcvack _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , ack _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , done _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiCS _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiBF _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSReplyTxIds) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSDone) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ recvTSRequestTxIds) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiKA _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiLN _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , apiLF _ _ _) a ()
ts-c-edge l d (tcAri (NonBlocking , a₁ , r₁)) (_ , break _) a ()
ts-c-edge l d tcBlk (_ , input _ _ _) a ()
ts-c-edge l d tcBlk (_ , output _ _ _) a ()
ts-c-edge l d tcBlk (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcBlk (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcBlk (_ , tx _ _ _) a ()
ts-c-edge l d tcBlk (_ , sndack _ _ _) a ()
ts-c-edge l d tcBlk (_ , rcvack _ _ _) a ()
ts-c-edge l d tcBlk (_ , ack _ _ _) a ()
ts-c-edge l d tcBlk (_ , done _ _ _) a ()
ts-c-edge l d tcBlk (_ , apiCS _ _ _) a ()
ts-c-edge l d tcBlk (_ , apiBF _ _ _) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSReplyTxIds) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSDone) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ recvTSRequestTxIds) a ()
ts-c-edge l d tcBlk (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-c-edge l d tcBlk (_ , apiKA _ _ _) a ()
ts-c-edge l d tcBlk (_ , apiLN _ _ _) a ()
ts-c-edge l d tcBlk (_ , apiLF _ _ _) a ()
ts-c-edge l d tcBlk (_ , break _) a ()
ts-c-edge l d tcNbl (_ , input _ _ _) a ()
ts-c-edge l d tcNbl (_ , output _ _ _) a ()
ts-c-edge l d tcNbl (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcNbl (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcNbl (_ , tx _ _ _) a ()
ts-c-edge l d tcNbl (_ , sndack _ _ _) a ()
ts-c-edge l d tcNbl (_ , rcvack _ _ _) a ()
ts-c-edge l d tcNbl (_ , ack _ _ _) a ()
ts-c-edge l d tcNbl (_ , done _ _ _) a ()
ts-c-edge l d tcNbl (_ , apiCS _ _ _) a ()
ts-c-edge l d tcNbl (_ , apiBF _ _ _) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSReplyTxIds) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSDone) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ recvTSRequestTxIds) a ()
ts-c-edge l d tcNbl (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-c-edge l d tcNbl (_ , apiKA _ _ _) a ()
ts-c-edge l d tcNbl (_ , apiLN _ _ _) a ()
ts-c-edge l d tcNbl (_ , apiLF _ _ _) a ()
ts-c-edge l d tcNbl (_ , break _) a ()
ts-c-edge l d (tcArt ids) (_ , input _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , output _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , sndmsg _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , rcvmsg _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , tx _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , sndack _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , rcvack _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , ack _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , done _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , apiCS _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , apiBF _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSReplyTxIds) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSDone) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ recvTSRequestTxIds) a ()
ts-c-edge l d (tcArt ids) (_ , apiTS l′ d′ recvTSRequestTxs) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d (tcArt ids) (_ , apiKA _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , apiLN _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , apiLF _ _ _) a ()
ts-c-edge l d (tcArt ids) (_ , break _) a ()
ts-c-edge l d tcTxs (_ , input _ _ _) a ()
ts-c-edge l d tcTxs (_ , output _ _ _) a ()
ts-c-edge l d tcTxs (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcTxs (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcTxs (_ , tx _ _ _) a ()
ts-c-edge l d tcTxs (_ , sndack _ _ _) a ()
ts-c-edge l d tcTxs (_ , rcvack _ _ _) a ()
ts-c-edge l d tcTxs (_ , ack _ _ _) a ()
ts-c-edge l d tcTxs (_ , done _ _ _) a ()
ts-c-edge l d tcTxs (_ , apiCS _ _ _) a ()
ts-c-edge l d tcTxs (_ , apiBF _ _ _) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSReplyTxIds) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSReplyTxs) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSDone) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ recvTSRequestTxIds) a ()
ts-c-edge l d tcTxs (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-c-edge l d tcTxs (_ , apiKA _ _ _) a ()
ts-c-edge l d tcTxs (_ , apiLN _ _ _) a ()
ts-c-edge l d tcTxs (_ , apiLF _ _ _) a ()
ts-c-edge l d tcTxs (_ , break _) a ()
ts-c-edge l d (tcWri ids) (_ , input _ _ N2N_ChainSync) a ()
ts-c-edge l d (tcWri ids) (_ , input _ _ N2N_BlockFetch) a ()
ts-c-edge l d (tcWri ids) (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d (tcWri ids) (_ , input _ _ N2N_KeepAlive) a ()
ts-c-edge l d (tcWri ids) (_ , input _ _ N2N_LeiosNotify) a ()
ts-c-edge l d (tcWri ids) (_ , input _ _ N2N_LeiosFetch) a ()
ts-c-edge l d (tcWri ids) (_ , output _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , sndmsg _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , rcvmsg _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , tx _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , sndack _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , rcvack _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , ack _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , done _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiCS _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiBF _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiTS _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiKA _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiLN _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , apiLF _ _ _) a ()
ts-c-edge l d (tcWri ids) (_ , break _) a ()
ts-c-edge l d tcWdone (_ , input _ _ N2N_ChainSync) a ()
ts-c-edge l d tcWdone (_ , input _ _ N2N_BlockFetch) a ()
ts-c-edge l d tcWdone (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcWdone (_ , input _ _ N2N_KeepAlive) a ()
ts-c-edge l d tcWdone (_ , input _ _ N2N_LeiosNotify) a ()
ts-c-edge l d tcWdone (_ , input _ _ N2N_LeiosFetch) a ()
ts-c-edge l d tcWdone (_ , output _ _ _) a ()
ts-c-edge l d tcWdone (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcWdone (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcWdone (_ , tx _ _ _) a ()
ts-c-edge l d tcWdone (_ , sndack _ _ _) a ()
ts-c-edge l d tcWdone (_ , rcvack _ _ _) a ()
ts-c-edge l d tcWdone (_ , ack _ _ _) a ()
ts-c-edge l d tcWdone (_ , done _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiCS _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiBF _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiTS _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiKA _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiLN _ _ _) a ()
ts-c-edge l d tcWdone (_ , apiLF _ _ _) a ()
ts-c-edge l d tcWdone (_ , break _) a ()
ts-c-edge l d tcDdone (_ , input _ _ _) a ()
ts-c-edge l d tcDdone (_ , output _ _ _) a ()
ts-c-edge l d tcDdone (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcDdone (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcDdone (_ , tx _ _ _) a ()
ts-c-edge l d tcDdone (_ , sndack _ _ _) a ()
ts-c-edge l d tcDdone (_ , rcvack _ _ _) a ()
ts-c-edge l d tcDdone (_ , ack _ _ _) a ()
ts-c-edge l d tcDdone (_ , done _ _ N2N_ChainSync) a ()
ts-c-edge l d tcDdone (_ , done _ _ N2N_BlockFetch) a ()
ts-c-edge l d tcDdone (_ , done l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d tcDdone (_ , done _ _ N2N_KeepAlive) a ()
ts-c-edge l d tcDdone (_ , done _ _ N2N_LeiosNotify) a ()
ts-c-edge l d tcDdone (_ , done _ _ N2N_LeiosFetch) a ()
ts-c-edge l d tcDdone (_ , apiCS _ _ _) a ()
ts-c-edge l d tcDdone (_ , apiBF _ _ _) a ()
ts-c-edge l d tcDdone (_ , apiTS _ _ _) a ()
ts-c-edge l d tcDdone (_ , apiKA _ _ _) a ()
ts-c-edge l d tcDdone (_ , apiLN _ _ _) a ()
ts-c-edge l d tcDdone (_ , apiLF _ _ _) a ()
ts-c-edge l d tcDdone (_ , break _) a ()
ts-c-edge l d (tcWrt txs) (_ , input _ _ N2N_ChainSync) a ()
ts-c-edge l d (tcWrt txs) (_ , input _ _ N2N_BlockFetch) a ()
ts-c-edge l d (tcWrt txs) (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-c-edge l d (tcWrt txs) (_ , input _ _ N2N_KeepAlive) a ()
ts-c-edge l d (tcWrt txs) (_ , input _ _ N2N_LeiosNotify) a ()
ts-c-edge l d (tcWrt txs) (_ , input _ _ N2N_LeiosFetch) a ()
ts-c-edge l d (tcWrt txs) (_ , output _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , sndmsg _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , rcvmsg _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , tx _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , sndack _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , rcvack _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , ack _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , done _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiCS _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiBF _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiTS _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiKA _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiLN _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , apiLF _ _ _) a ()
ts-c-edge l d (tcWrt txs) (_ , break _) a ()
ts-c-edge l d tcTerm (_ , input _ _ _) a ()
ts-c-edge l d tcTerm (_ , output _ _ _) a ()
ts-c-edge l d tcTerm (_ , sndmsg _ _ _) a ()
ts-c-edge l d tcTerm (_ , rcvmsg _ _ _) a ()
ts-c-edge l d tcTerm (_ , tx _ _ _) a ()
ts-c-edge l d tcTerm (_ , sndack _ _ _) a ()
ts-c-edge l d tcTerm (_ , rcvack _ _ _) a ()
ts-c-edge l d tcTerm (_ , ack _ _ _) a ()
ts-c-edge l d tcTerm (_ , done _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiCS _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiBF _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiTS _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiKA _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiLN _ _ _) a ()
ts-c-edge l d tcTerm (_ , apiLF _ _ _) a ()
ts-c-edge l d tcTerm (_ , break _) a ()

-- the ts-c spec confines to the (N2N_TxSubmission , d) slot
tsClientSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_TxSubmission d) (tsClientSpec l d)
tsClientSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_TxSubmission d) _ (ts-c-edge l d) tcInit

-- TS server: every fired edge is an apiTS/wire event on (N2N_TxSubmission , d)
ts-s-edge : (l : Link) (d : Dir)
          → ∀ q at a {q′} → tsSnxt l d q at a ≡ just q′
          → peerAlpha N2N_TxSubmission d at a
ts-s-edge l d tsInit (_ , input _ _ _) a ()
ts-s-edge l d tsInit (_ , output _ _ N2N_ChainSync) a ()
ts-s-edge l d tsInit (_ , output _ _ N2N_BlockFetch) a ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , keepAlive _) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , blockFetch _) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , chainSync _) ()
ts-s-edge l d tsInit (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSInit) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSDone) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosNotify _) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosFetch _) ()
ts-s-edge l d tsInit (_ , output _ _ N2N_KeepAlive) a ()
ts-s-edge l d tsInit (_ , output _ _ N2N_LeiosNotify) a ()
ts-s-edge l d tsInit (_ , output _ _ N2N_LeiosFetch) a ()
ts-s-edge l d tsInit (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsInit (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsInit (_ , tx _ _ _) a ()
ts-s-edge l d tsInit (_ , sndack _ _ _) a ()
ts-s-edge l d tsInit (_ , rcvack _ _ _) a ()
ts-s-edge l d tsInit (_ , ack _ _ _) a ()
ts-s-edge l d tsInit (_ , done _ _ _) a ()
ts-s-edge l d tsInit (_ , apiCS _ _ _) a ()
ts-s-edge l d tsInit (_ , apiBF _ _ _) a ()
ts-s-edge l d tsInit (_ , apiTS _ _ _) a ()
ts-s-edge l d tsInit (_ , apiKA _ _ _) a ()
ts-s-edge l d tsInit (_ , apiLN _ _ _) a ()
ts-s-edge l d tsInit (_ , apiLF _ _ _) a ()
ts-s-edge l d tsInit (_ , break _) a ()
ts-s-edge l d tsIdle (_ , input _ _ _) a ()
ts-s-edge l d tsIdle (_ , output _ _ _) a ()
ts-s-edge l d tsIdle (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsIdle (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsIdle (_ , tx _ _ _) a ()
ts-s-edge l d tsIdle (_ , sndack _ _ _) a ()
ts-s-edge l d tsIdle (_ , rcvack _ _ _) a ()
ts-s-edge l d tsIdle (_ , ack _ _ _) a ()
ts-s-edge l d tsIdle (_ , done _ _ _) a ()
ts-s-edge l d tsIdle (_ , apiCS _ _ _) a ()
ts-s-edge l d tsIdle (_ , apiBF _ _ _) a ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSReplyTxIds) a ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSReplyTxs) a ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSDone) a ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxIdsBlocking) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxIdsPipelined) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ sendTSRequestTxsPipelined) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ recvTSRequestTxIds) a ()
ts-s-edge l d tsIdle (_ , apiTS l′ d′ recvTSRequestTxs) a ()
ts-s-edge l d tsIdle (_ , apiKA _ _ _) a ()
ts-s-edge l d tsIdle (_ , apiLN _ _ _) a ()
ts-s-edge l d tsIdle (_ , apiLF _ _ _) a ()
ts-s-edge l d tsIdle (_ , break _) a ()
ts-s-edge l d (tsWib ar) (_ , input _ _ N2N_ChainSync) a ()
ts-s-edge l d (tsWib ar) (_ , input _ _ N2N_BlockFetch) a ()
ts-s-edge l d (tsWib ar) (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d (tsWib ar) (_ , input _ _ N2N_KeepAlive) a ()
ts-s-edge l d (tsWib ar) (_ , input _ _ N2N_LeiosNotify) a ()
ts-s-edge l d (tsWib ar) (_ , input _ _ N2N_LeiosFetch) a ()
ts-s-edge l d (tsWib ar) (_ , output _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , sndmsg _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , rcvmsg _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , tx _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , sndack _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , rcvack _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , ack _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , done _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiCS _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiBF _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiTS _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiKA _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiLN _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , apiLF _ _ _) a ()
ts-s-edge l d (tsWib ar) (_ , break _) a ()
ts-s-edge l d (tsWin ar) (_ , input _ _ N2N_ChainSync) a ()
ts-s-edge l d (tsWin ar) (_ , input _ _ N2N_BlockFetch) a ()
ts-s-edge l d (tsWin ar) (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d (tsWin ar) (_ , input _ _ N2N_KeepAlive) a ()
ts-s-edge l d (tsWin ar) (_ , input _ _ N2N_LeiosNotify) a ()
ts-s-edge l d (tsWin ar) (_ , input _ _ N2N_LeiosFetch) a ()
ts-s-edge l d (tsWin ar) (_ , output _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , sndmsg _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , rcvmsg _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , tx _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , sndack _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , rcvack _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , ack _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , done _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiCS _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiBF _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiTS _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiKA _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiLN _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , apiLF _ _ _) a ()
ts-s-edge l d (tsWin ar) (_ , break _) a ()
ts-s-edge l d (tsWrt ids) (_ , input _ _ N2N_ChainSync) a ()
ts-s-edge l d (tsWrt ids) (_ , input _ _ N2N_BlockFetch) a ()
ts-s-edge l d (tsWrt ids) (_ , input l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d (tsWrt ids) (_ , input _ _ N2N_KeepAlive) a ()
ts-s-edge l d (tsWrt ids) (_ , input _ _ N2N_LeiosNotify) a ()
ts-s-edge l d (tsWrt ids) (_ , input _ _ N2N_LeiosFetch) a ()
ts-s-edge l d (tsWrt ids) (_ , output _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , sndmsg _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , rcvmsg _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , tx _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , sndack _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , rcvack _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , ack _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , done _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiCS _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiBF _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiTS _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiKA _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiLN _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , apiLF _ _ _) a ()
ts-s-edge l d (tsWrt ids) (_ , break _) a ()
ts-s-edge l d tsBlk (_ , input _ _ _) a ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_ChainSync) a ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_BlockFetch) a ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , keepAlive _) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , blockFetch _) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , chainSync _) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSInit) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)) ()
ts-s-edge l d tsBlk (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
ts-s-edge l d tsBlk (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSDone) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosNotify _) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosFetch _) ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_KeepAlive) a ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_LeiosNotify) a ()
ts-s-edge l d tsBlk (_ , output _ _ N2N_LeiosFetch) a ()
ts-s-edge l d tsBlk (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsBlk (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsBlk (_ , tx _ _ _) a ()
ts-s-edge l d tsBlk (_ , sndack _ _ _) a ()
ts-s-edge l d tsBlk (_ , rcvack _ _ _) a ()
ts-s-edge l d tsBlk (_ , ack _ _ _) a ()
ts-s-edge l d tsBlk (_ , done _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiCS _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiBF _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiTS _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiKA _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiLN _ _ _) a ()
ts-s-edge l d tsBlk (_ , apiLF _ _ _) a ()
ts-s-edge l d tsBlk (_ , break _) a ()
ts-s-edge l d tsNbl (_ , input _ _ _) a ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_ChainSync) a ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_BlockFetch) a ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , keepAlive _) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , blockFetch _) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , chainSync _) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSInit) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)) ()
ts-s-edge l d tsNbl (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSDone) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosNotify _) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosFetch _) ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_KeepAlive) a ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_LeiosNotify) a ()
ts-s-edge l d tsNbl (_ , output _ _ N2N_LeiosFetch) a ()
ts-s-edge l d tsNbl (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsNbl (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsNbl (_ , tx _ _ _) a ()
ts-s-edge l d tsNbl (_ , sndack _ _ _) a ()
ts-s-edge l d tsNbl (_ , rcvack _ _ _) a ()
ts-s-edge l d tsNbl (_ , ack _ _ _) a ()
ts-s-edge l d tsNbl (_ , done _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiCS _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiBF _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiTS _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiKA _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiLN _ _ _) a ()
ts-s-edge l d tsNbl (_ , apiLF _ _ _) a ()
ts-s-edge l d tsNbl (_ , break _) a ()
ts-s-edge l d tsTxs (_ , input _ _ _) a ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_ChainSync) a ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_BlockFetch) a ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , keepAlive _) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , blockFetch _) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , chainSync _) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSInit) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxIds _)) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSRequestTxs _)) ()
ts-s-edge l d tsTxs (_ , output l′ d′ N2N_TxSubmission) (_ , _ , _ , txSubmission (MsgTSReplyTxs _)) eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , txSubmission MsgTSDone) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosNotify _) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_TxSubmission) (_ , _ , _ , leiosFetch _) ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_KeepAlive) a ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_LeiosNotify) a ()
ts-s-edge l d tsTxs (_ , output _ _ N2N_LeiosFetch) a ()
ts-s-edge l d tsTxs (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsTxs (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsTxs (_ , tx _ _ _) a ()
ts-s-edge l d tsTxs (_ , sndack _ _ _) a ()
ts-s-edge l d tsTxs (_ , rcvack _ _ _) a ()
ts-s-edge l d tsTxs (_ , ack _ _ _) a ()
ts-s-edge l d tsTxs (_ , done _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiCS _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiBF _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiTS _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiKA _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiLN _ _ _) a ()
ts-s-edge l d tsTxs (_ , apiLF _ _ _) a ()
ts-s-edge l d tsTxs (_ , break _) a ()
ts-s-edge l d tsDdone (_ , input _ _ _) a ()
ts-s-edge l d tsDdone (_ , output _ _ _) a ()
ts-s-edge l d tsDdone (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsDdone (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsDdone (_ , tx _ _ _) a ()
ts-s-edge l d tsDdone (_ , sndack _ _ _) a ()
ts-s-edge l d tsDdone (_ , rcvack _ _ _) a ()
ts-s-edge l d tsDdone (_ , ack _ _ _) a ()
ts-s-edge l d tsDdone (_ , done _ _ N2N_ChainSync) a ()
ts-s-edge l d tsDdone (_ , done _ _ N2N_BlockFetch) a ()
ts-s-edge l d tsDdone (_ , done l′ d′ N2N_TxSubmission) a eq with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = refl
... | yes refl | no _ = case eq of λ ()
... | no _     | _     = case eq of λ ()
ts-s-edge l d tsDdone (_ , done _ _ N2N_KeepAlive) a ()
ts-s-edge l d tsDdone (_ , done _ _ N2N_LeiosNotify) a ()
ts-s-edge l d tsDdone (_ , done _ _ N2N_LeiosFetch) a ()
ts-s-edge l d tsDdone (_ , apiCS _ _ _) a ()
ts-s-edge l d tsDdone (_ , apiBF _ _ _) a ()
ts-s-edge l d tsDdone (_ , apiTS _ _ _) a ()
ts-s-edge l d tsDdone (_ , apiKA _ _ _) a ()
ts-s-edge l d tsDdone (_ , apiLN _ _ _) a ()
ts-s-edge l d tsDdone (_ , apiLF _ _ _) a ()
ts-s-edge l d tsDdone (_ , break _) a ()
ts-s-edge l d tsTerm (_ , input _ _ _) a ()
ts-s-edge l d tsTerm (_ , output _ _ _) a ()
ts-s-edge l d tsTerm (_ , sndmsg _ _ _) a ()
ts-s-edge l d tsTerm (_ , rcvmsg _ _ _) a ()
ts-s-edge l d tsTerm (_ , tx _ _ _) a ()
ts-s-edge l d tsTerm (_ , sndack _ _ _) a ()
ts-s-edge l d tsTerm (_ , rcvack _ _ _) a ()
ts-s-edge l d tsTerm (_ , ack _ _ _) a ()
ts-s-edge l d tsTerm (_ , done _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiCS _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiBF _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiTS _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiKA _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiLN _ _ _) a ()
ts-s-edge l d tsTerm (_ , apiLF _ _ _) a ()
ts-s-edge l d tsTerm (_ , break _) a ()

-- the ts-s spec confines to the (N2N_TxSubmission , d) slot
tsServerSpec-OffersOnly : (l : Link) (d : Dir)
                        → OffersOnly (peerAlpha N2N_TxSubmission d) (tsServerSpec l d)
tsServerSpec-OffersOnly l d =
  tableSpec-OffersOnly (peerAlpha N2N_TxSubmission d) _ (ts-s-edge l d) tsInit

------------------------------------------------------------------------
-- Item 2(a): OffersOnly transported through an injective alphabet rename.
--
-- A GENERIC (in the source alphabet E₁ and its event injection ι into
-- `Net_Api Payload`) lemma: if a SOURCE process P confines its offers to a
-- source alphabet α, then its injective rename `renameMap P` confines its
-- offers to the ι-image `ιImg α`.  Because ι is injective, `invPreimg` is a
-- singleton/empty enumerator, so the rename fan-in collapses (`rnCollect`/
-- `rnFan` are ≤1-ary) and every renamed edge is the ι-image of a single
-- source edge.  Proved by copattern corecursion, inverting each renamed step
-- through the `renameMap` force clauses (`frr-*-inv`) + `rnFan-inv`/
-- `rnCollect-inv` (the `elim-aligned` technique of `TraceLawsRenameGen`,
-- lifted from traces to the single-step `OffersOnly` closure and specialised
-- to the injective preimage).  Instantiated per source peer below.
------------------------------------------------------------------------

module RenOO
  {E₁ : Set → Set}
  (E₁-≟   : (x y : AnyTypes E₁) → Dec (x ≡ y))
  (ι      : ∀ {A} → E₁ A → Net_Api Payload A)
  (ι⁻¹    : ∀ {A} → Net_Api Payload A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where

  open import Data.Product using (Σ-syntax)
  open import Data.List using (List; []; _∷_)
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here; there)

  -- the injective rename operator + helpers for this instance
  open import CSP.Rename {E₁ = E₁} {E₂ = Net_Api Payload} ι ι⁻¹ ι-linv
  -- source-side OffersOnly / Alpha (target side is the ambient `Net_Api` one)
  module Src = CSP.Laws.Bisim.DRCongruenceRep E₁-≟
  -- source LTS constructors (target ones are the ambient `sVis`/… in scope)
  open import Semantics.LTS {E = E₁} {I = ExtI E₁} as SrcL
    using () renaming ( _─[_]─►_ to _─[_]─►ˢ_ ; sRet to sRetˢ ; sSil to sSilˢ
                      ; sVis to sVisˢ ; sTau to sTauˢ )

  -- renameMap force clause inversions (definitional `with force P`)
  frr-sil-inv : ∀ {ℓr} {Rr : Set ℓr}
                {P : PTree E₁ (ExtI E₁) Rr} {W : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
              → PTree.force (renameMap P) ≡ sil W
              → Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ] (PTree.force P ≡ sil P₁ × W ≡ renameMap P₁)
  frr-sil-inv {P = P} eq with PTree.force P
  ... | sil P₁ with refl ← eq = P₁ , refl , refl

  -- react clause: recover the source menu/τc + the renamed-menu equation
  frr-react-inv : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                  {v  : (bt : AnyTypes (Net_Api Payload)) → ContinueType bt (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
                  {τc : (i  : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr))}
                → PTree.force (renameMap P) ≡ react v τc
                → Σ[ vP ∈ ((at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))) ]
                  Σ[ τcP ∈ ((i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))) ]
                    (PTree.force P ≡ react vP τcP
                     × v ≡ (λ bt b → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                                          (rnCollect vP (invPreimg ι-vis-inv bt b)))
                     × τc ≡ extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP)
  frr-react-inv {P = P} eq with PTree.force P
  ... | react vP τcP = vP , τcP , refl
        , sym (proj₁ (react-injective eq)) , sym (proj₂ (react-injective eq))

  -- rnFan is a singleton (injective ⇒ never ≥2 sources) or a ≥2 list (refuted)
  rnFan-inv : ∀ {ℓr} {Rr : Set ℓr}
              {ts : List (PTree E₁ (ExtI E₁) Rr)} {W : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Rr}
            → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv) ts ≡ just W
            → (Σ[ t ∈ PTree E₁ (ExtI E₁) Rr ] (ts ≡ t ∷ [] × W ≡ renameMap t))
            ⊎ (Σ[ t ∈ _ ] Σ[ u ∈ _ ] Σ[ r ∈ _ ] (ts ≡ t ∷ u ∷ r))
  rnFan-inv {ts = t ∷ []}    refl = inj₁ (t , refl , refl)
  rnFan-inv {ts = t ∷ u ∷ r} refl = inj₂ (t , u , r , refl)

  -- a collected continuation comes from an enabled preimage entry (keeps the entry)
  rnCollect-inv : ∀ {ℓr} {Rr : Set ℓr} {ℓP} {Pr : (at : AnyTypes E₁) → proj₁ at → Set ℓP}
                    {vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
                    {entries : List (Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] Pr at a)}
                    {t : PTree E₁ (ExtI E₁) Rr}
                → t ∈ rnCollect vP entries
                → Σ[ at ∈ AnyTypes E₁ ] Σ[ a ∈ proj₁ at ] Σ[ pr ∈ Pr at a ]
                    ((at , a , pr) ∈ entries × vP at a ≡ just t)
  rnCollect-inv {entries = []} ()
  rnCollect-inv {vP = vP} {entries = (at , a , pr) ∷ rest} mem with vP at a in eqv
  ... | nothing with at′ , a′ , pr′ , memE , eqv′ ← rnCollect-inv {vP = vP} {entries = rest} mem =
        at′ , a′ , pr′ , there memE , eqv′
  ... | just t′ with mem
  ...   | here refl  = at , a , pr , here refl , eqv
  ...   | there mem′ with at′ , a′ , pr′ , memE , eqv′ ← rnCollect-inv {vP = vP} {entries = rest} mem′ =
          at′ , a′ , pr′ , there memE , eqv′

  -- the injective preimage's collected list has length ≤1: it can never be ≥2
  rnCollect-≤1 : ∀ {ℓr} {Rr : Set ℓr}
                 {vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
                 {X : Set} {bt : Net_Api Payload X} {b : X}
                 {t u : PTree E₁ (ExtI E₁) Rr} {r : List (PTree E₁ (ExtI E₁) Rr)}
               → rnCollect vP (invPreimg ι-vis-inv (X , bt) b) ≡ t ∷ u ∷ r → ⊥
  rnCollect-≤1 {vP = vP} {X = X} {bt = bt} {b = b} eq with ι-vis-inv (X , bt) b
  ... | nothing = case eq of λ ()
  ... | just (at , a) with vP at a
  ...   | nothing = case eq of λ ()
  ...   | just _  = case eq of λ ()

  -- invert the injective visible inverse: a hit fixes the source event / value
  ivi-inv : {X : Set} {e₂ : Net_Api Payload X} {a : X} {ce : ConcEvent₁}
          → ι-vis-inv (X , e₂) a ≡ just ce
          → Σ[ e₁ ∈ E₁ X ] (ι⁻¹ e₂ ≡ just e₁ × ce ≡ ((X , e₁) , a))
  ivi-inv {e₂ = e₂} {a = a} eq with ι⁻¹ e₂
  ... | just e₁ = e₁ , refl , sym (just-injective eq)

  -- the ι-image of a source alphabet
  ιImg : Src.Alpha → Alpha
  ιImg α (X , e₂) a = Σ[ e₁ ∈ E₁ X ] (ι⁻¹ e₂ ≡ just e₁ × α (X , e₁) a)

  -- THE LEMMA: OffersOnly transported through the injective rename
  ren-OffersOnly : ∀ {ℓr} {Rr : Set ℓr} {α : Src.Alpha} {P : PTree E₁ (ExtI E₁) Rr}
                 → Src.OffersOnly α P → OffersOnly (ιImg α) (renameMap P)
  ren-OffersOnly {α = α} {P = P} ooP .OffersOnly.now (sVis {at = X , e₂} {a = a} eqf br)
    with frr-react-inv {P = P} eqf
  ... | vP , τcP , eqP , v≡ , _
        with rnFan-inv (subst (λ g → g (X , e₂) a ≡ just _) v≡ br)
  ...     | inj₂ (t , u , r , eqts) = ⊥-elim (rnCollect-≤1 eqts)
  ...     | inj₁ (t , eqts , _)
            with rnCollect-inv {vP = vP} {entries = invPreimg ι-vis-inv (X , e₂) a}
                         (subst (t ∈_) (sym eqts) (here refl))
  ...         | at , a′ , pr , memE , eqv with ivi-inv pr
  ...            | e₁ , eqinv , ce≡ =
                   e₁ , eqinv
                 , subst (λ ce → α (proj₁ ce) (proj₂ ce)) ce≡
                         (Src.OffersOnly.now ooP (sVisˢ eqP eqv))
  ren-OffersOnly ooP .OffersOnly.step (sRet eqf) = OffersOnly-deadlock
  ren-OffersOnly {P = P} ooP .OffersOnly.step (sSil eqf) with frr-sil-inv {P = P} eqf
  ... | P₁ , eqP , refl = ren-OffersOnly (Src.OffersOnly.step ooP (sSilˢ eqP))
  ren-OffersOnly {P = P} ooP .OffersOnly.step (sVis {at = X , e₂} {a = a} eqf br)
    with frr-react-inv {P = P} eqf
  ... | vP , τcP , eqP , v≡ , _
        with rnFan-inv (subst (λ g → g (X , e₂) a ≡ just _) v≡ br)
  ...     | inj₂ (t , u , r , eqts) = ⊥-elim (rnCollect-≤1 eqts)
  ...     | inj₁ (t , eqts , refl)
            with rnCollect-inv {vP = vP} {entries = invPreimg ι-vis-inv (X , e₂) a}
                         (subst (t ∈_) (sym eqts) (here refl))
  ...         | at , a′ , pr , memE , eqv =
                ren-OffersOnly (Src.OffersOnly.step ooP (sVisˢ eqP eqv))
  ren-OffersOnly {P = P} ooP .OffersOnly.step (sTau {i = A , eι₂} {a = a} eqf br)
    with frr-react-inv {P = P} eqf
  ... | vP , τcP , eqP , _ , τc≡
        with extBwd eι₂ | subst (λ g → g (A , eι₂) a ≡ just _) τc≡ br
  ...   | nothing  | br′ = case br′ of λ ()
  ...   | just eι₁ | br′ with τcP (A , eι₁) a in eqt
  ...      | nothing = case br′ of λ ()
  ...      | just t′ rewrite sym (just-injective br′) =
                ren-OffersOnly (Src.OffersOnly.step ooP (sTauˢ eqP eqt))

------------------------------------------------------------------------
-- Item 2(b): per-peer source + impl OffersOnly (KeepAlive).
--
-- For each source peer we (i) confine its offers to a source alphabet keyed
-- on direction only (the protocol is fixed by the source event type), (ii)
-- transport that through the injective rename via `RenOO.ren-OffersOnly`, and
-- (iii) `OffersOnly-mono` the ι-image into the ambient `peerAlpha` slot.  The
-- mono is a per-Net_Api-constructor case analysis: the four KA-relevant
-- constructors carry direction `d` through `ι⁻¹`, everything else has empty
-- preimage so the ι-image membership is absurd.
------------------------------------------------------------------------

-- the generic ren-OffersOnly specialised to the KA alphabet injection
module RenKA-OO = RenOO KAEv-≟ ιKA ιKA⁻¹ ιKA-linv

-- source-side OffersOnly builders for the KA alphabet
module SrcKA = CSP.Laws.Bisim.DRCongruenceRep KAEv-≟

-- the (direction) slot of a KA source event (the protocol is implicit = KA)
slotKA : AnyTypes KAEv → Maybe Dir
slotKA (_ , sendKA    _ d) = just d
slotKA (_ , receiveKA _ d) = just d
slotKA (_ , apiKAev   _ d _) = just d
slotKA (_ , doneKA    _ d) = just d

-- the KA source alphabet on direction `d`: every event on that direction
srcAlphaKA : Dir → SrcKA.Alpha
srcAlphaKA d at a = slotKA at ≡ just d

-- the ι-image of `srcAlphaKA d` lands in the KA peer slot on `d`
ka-img⊆ : (d : Dir) → ∀ at a → RenKA-OO.ιImg (srcAlphaKA d) at a → peerAlpha N2N_KeepAlive d at a
ka-img⊆ d (_ , input  l′ d′ N2N_KeepAlive)    a (_ , refl , refl) = refl
ka-img⊆ d (_ , output l′ d′ N2N_KeepAlive)    a (_ , refl , refl) = refl
ka-img⊆ d (_ , done   l′ d′ N2N_KeepAlive)    a (_ , refl , refl) = refl
ka-img⊆ d (_ , apiKA  l′ d′ m)                a (_ , refl , refl) = refl
ka-img⊆ d (_ , input  l′ d′ N2N_ChainSync)    a (_ , () , _)
ka-img⊆ d (_ , input  l′ d′ N2N_BlockFetch)   a (_ , () , _)
ka-img⊆ d (_ , input  l′ d′ N2N_TxSubmission) a (_ , () , _)
ka-img⊆ d (_ , input  l′ d′ N2N_LeiosNotify)  a (_ , () , _)
ka-img⊆ d (_ , input  l′ d′ N2N_LeiosFetch)   a (_ , () , _)
ka-img⊆ d (_ , output l′ d′ N2N_ChainSync)    a (_ , () , _)
ka-img⊆ d (_ , output l′ d′ N2N_BlockFetch)   a (_ , () , _)
ka-img⊆ d (_ , output l′ d′ N2N_TxSubmission) a (_ , () , _)
ka-img⊆ d (_ , output l′ d′ N2N_LeiosNotify)  a (_ , () , _)
ka-img⊆ d (_ , output l′ d′ N2N_LeiosFetch)   a (_ , () , _)
ka-img⊆ d (_ , done   l′ d′ N2N_ChainSync)    a (_ , () , _)
ka-img⊆ d (_ , done   l′ d′ N2N_BlockFetch)   a (_ , () , _)
ka-img⊆ d (_ , done   l′ d′ N2N_TxSubmission) a (_ , () , _)
ka-img⊆ d (_ , done   l′ d′ N2N_LeiosNotify)  a (_ , () , _)
ka-img⊆ d (_ , done   l′ d′ N2N_LeiosFetch)   a (_ , () , _)
ka-img⊆ d (_ , sndmsg l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , rcvmsg l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , tx     l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , sndack l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , rcvack l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , ack    l′ d′ i)                a (_ , () , _)
ka-img⊆ d (_ , apiCS  l′ d′ m)                a (_ , () , _)
ka-img⊆ d (_ , apiBF  l′ d′ m)                a (_ , () , _)
ka-img⊆ d (_ , apiTS  l′ d′ m)                a (_ , () , _)
ka-img⊆ d (_ , apiLN  l′ d′ m)                a (_ , () , _)
ka-img⊆ d (_ , apiLF  l′ d′ m)                a (_ , () , _)
ka-img⊆ d (_ , break  l′)                     a (_ , () , _)

-- KA SERVER source peer confines its offers to `srcAlphaKA lo`.
-- The server is a pure echo: its menu splits are all payload-CONSTRUCTOR
-- patterns (matched directly in the clause LHS) + the `l′ ≟ l`/`d′ ≟ d` gate,
-- with NO internal value comparison (`≟`) — unlike the CLIENT, whose
-- `stServer` errCookie branch has an internal `with cookieReq ≟ cookieRsp`
-- that does not share with an outer `with`, blocking continuation extraction
-- (see Part-7 blocker note).  Proved at CONCRETE (link,dir) = (linkBD, lo)
-- (the server half of `pipeBD`); the fully-`∀ l d` version needs the "pin".
-- l-GENERALISED KA server source OffersOnly.  The link gate is cross-module
-- (KeepAlive.serverStep's `l′ ≟ l`), so `with l′ ≟ l` does NOT reduce the menu
-- while `l` is abstract (`l ≟ l` stuck; Part-7 finding).  We 4-way enumerate
-- `l` (Link = Fin 4); under each concrete link the Fin×Dir menu enumeration
-- fires only at (that link , lo) and refutes the other 7 pairs (`nothing`).
kaServerSrc-OO : (l : Link) → SrcKA.OffersOnly (srcAlphaKA lo) (KAserverStClient l lo)
kaServerSrc-OO F.zero = SrcKA.OffersOnly-iter {k = serverStep F.zero lo} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA lo) (serverStep F.zero lo q)
  step stClient      = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA lo) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAlive c)) refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKADone)) refl = refl , SrcKA.OffersOnly-Prefix₀ (λ _ → refl) SrcKA.OffersOnly-Ret
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAliveResponse _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _) eq   = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _) eq    = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _) eq  = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _) eq   = case eq of λ ()
    mc (_ , sendKA _ _)    _ eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) _ eq = case eq of λ ()
    mc (_ , doneKA _ _)    _ eq = case eq of λ ()
  step (stServer c)  = SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
  step stDone        = SrcKA.OffersOnly-Ret
kaServerSrc-OO (F.suc F.zero) = SrcKA.OffersOnly-iter {k = serverStep (F.suc F.zero) lo} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA lo) (serverStep (F.suc F.zero) lo q)
  step stClient      = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA lo) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAlive c)) refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKADone)) refl = refl , SrcKA.OffersOnly-Prefix₀ (λ _ → refl) SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAliveResponse _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _) eq   = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _) eq    = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _) eq  = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _) eq   = case eq of λ ()
    mc (_ , sendKA _ _)    _ eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) _ eq = case eq of λ ()
    mc (_ , doneKA _ _)    _ eq = case eq of λ ()
  step (stServer c)  = SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
  step stDone        = SrcKA.OffersOnly-Ret
kaServerSrc-OO (F.suc (F.suc F.zero)) = SrcKA.OffersOnly-iter {k = serverStep (F.suc (F.suc F.zero)) lo} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA lo) (serverStep (F.suc (F.suc F.zero)) lo q)
  step stClient      = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA lo) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAlive c)) refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKADone)) refl = refl , SrcKA.OffersOnly-Prefix₀ (λ _ → refl) SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAliveResponse _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _) eq   = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _) eq    = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _) eq  = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _) eq   = case eq of λ ()
    mc (_ , sendKA _ _)    _ eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) _ eq = case eq of λ ()
    mc (_ , doneKA _ _)    _ eq = case eq of λ ()
  step (stServer c)  = SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
  step stDone        = SrcKA.OffersOnly-Ret
kaServerSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcKA.OffersOnly-iter {k = serverStep (F.suc (F.suc (F.suc F.zero))) lo} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA lo) (serverStep (F.suc (F.suc (F.suc F.zero))) lo q)
  step stClient      = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA lo) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAlive c)) refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAlive c)) ()
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKADone)) refl = refl , SrcKA.OffersOnly-Prefix₀ (λ _ → refl) SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKADone)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAliveResponse _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _) eq   = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _) eq    = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _) eq  = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _) eq   = case eq of λ ()
    mc (_ , sendKA _ _)    _ eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) _ eq = case eq of λ ()
    mc (_ , doneKA _ _)    _ eq = case eq of λ ()
  step (stServer c)  = SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
  step stDone        = SrcKA.OffersOnly-Ret
-- KA server IMPL peer confines to its (KeepAlive, lo) slot (transport + mono)
kaServer-OO : (l : Link) → OffersOnly (peerAlpha N2N_KeepAlive lo) (KAserverA l lo)
kaServer-OO l = OffersOnly-mono (ka-img⊆ lo) (RenKA-OO.ren-OffersOnly (kaServerSrc-OO l))

-- l-GENERALISED KA client source OffersOnly (dir = hi).  Same 4-way link
-- enumeration as the server; the api-emit menu (stClient) fires apiKAev at
-- (link , hi) and the response menu (stServer) fires receiveKA at (link , hi)
-- with the internal cookie gate `cookieReq ≟ cr` (both branches confine).
kaClientSrc-OO : (l : Link) → SrcKA.OffersOnly (srcAlphaKA hi) (KAclientStClient l hi)
kaClientSrc-OO F.zero = SrcKA.OffersOnly-iter {k = clientStep F.zero hi} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA hi) (clientStep F.zero hi q)
  step stClient = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , apiKAev F.zero lo sendKAMsg) a ()
    mc (_ , apiKAev F.zero hi sendKAMsg) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc F.zero) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKAMsg) a ()
    mc (_ , apiKAev F.zero lo sendKADone) a ()
    mc (_ , apiKAev F.zero hi sendKADone) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc F.zero) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKADone) a ()
    mc (_ , apiKAev _ _ errCookie) a eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , receiveKA _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step (stServer cookieReq) = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) eq with cookieReq ≟ cr
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | yes _ = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | no _  = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAlive _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive MsgKADone)        eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _)   eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step stDone = SrcKA.OffersOnly-Ret
kaClientSrc-OO (F.suc F.zero) = SrcKA.OffersOnly-iter {k = clientStep (F.suc F.zero) hi} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA hi) (clientStep (F.suc F.zero) hi q)
  step stClient = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , apiKAev F.zero lo sendKAMsg) a ()
    mc (_ , apiKAev F.zero hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKAMsg) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKAMsg) a ()
    mc (_ , apiKAev F.zero lo sendKADone) a ()
    mc (_ , apiKAev F.zero hi sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKADone) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKADone) a ()
    mc (_ , apiKAev _ _ errCookie) a eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , receiveKA _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step (stServer cookieReq) = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) eq with cookieReq ≟ cr
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | yes _ = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | no _  = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAlive _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive MsgKADone)        eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _)   eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step stDone = SrcKA.OffersOnly-Ret
kaClientSrc-OO (F.suc (F.suc F.zero)) = SrcKA.OffersOnly-iter {k = clientStep (F.suc (F.suc F.zero)) hi} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA hi) (clientStep (F.suc (F.suc F.zero)) hi q)
  step stClient = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , apiKAev F.zero lo sendKAMsg) a ()
    mc (_ , apiKAev F.zero hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKAMsg) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKAMsg) a ()
    mc (_ , apiKAev F.zero lo sendKADone) a ()
    mc (_ , apiKAev F.zero hi sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKADone) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKADone) a ()
    mc (_ , apiKAev _ _ errCookie) a eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , receiveKA _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step (stServer cookieReq) = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) eq with cookieReq ≟ cr
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | yes _ = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | no _  = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAlive _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive MsgKADone)        eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _)   eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step stDone = SrcKA.OffersOnly-Ret
kaClientSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcKA.OffersOnly-iter {k = clientStep (F.suc (F.suc (F.suc F.zero))) hi} {a = stClient} step
  where
  step : ∀ q → SrcKA.OffersOnly (srcAlphaKA hi) (clientStep (F.suc (F.suc (F.suc F.zero))) hi q)
  step stClient = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , apiKAev F.zero lo sendKAMsg) a ()
    mc (_ , apiKAev F.zero hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKAMsg) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKAMsg) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev F.zero lo sendKADone) a ()
    mc (_ , apiKAev F.zero hi sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc F.zero) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc F.zero)) hi sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) lo sendKADone) a ()
    mc (_ , apiKAev (F.suc (F.suc (F.suc F.zero))) hi sendKADone) a refl = refl , SrcKA.OffersOnly-Output refl SrcKA.OffersOnly-Ret
    mc (_ , apiKAev _ _ errCookie) a eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , receiveKA _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step (stServer cookieReq) = SrcKA.OffersOnly-pchoice mc
    where
    mc : SrcKA.MenuConf (srcAlphaKA hi) _
    mc (_ , receiveKA F.zero lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA F.zero hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc F.zero) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc F.zero)) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) ()
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) eq with cookieReq ≟ cr
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | yes _ = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , keepAlive (MsgKeepAliveResponse cr)) refl | no _  = refl , SrcKA.OffersOnly-Ret
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive (MsgKeepAlive _)) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , keepAlive MsgKADone)        eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , blockFetch _)   eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , receiveKA l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , sendKA _ _)    a eq = case eq of λ ()
    mc (_ , apiKAev _ _ _) a eq = case eq of λ ()
    mc (_ , doneKA _ _)    a eq = case eq of λ ()
  step stDone = SrcKA.OffersOnly-Ret
-- KA CLIENT impl peer confines to its (KeepAlive, hi) slot (transport + mono)
kaClient-OO : (l : Link) → OffersOnly (peerAlpha N2N_KeepAlive hi) (KAclientA l hi)
kaClient-OO l = OffersOnly-mono (ka-img⊆ hi) (RenKA-OO.ren-OffersOnly (kaClientSrc-OO l))

------------------------------------------------------------------------
-- Item 2(b), BlockFetch server: a SECOND-protocol impl-side OffersOnly,
-- demonstrating the server-transport replication recipe generalises past
-- KeepAlive.  The BF server is a pure echo (three non-terminal states, NO
-- internal value gate — all splits are structural payloads + l/d gates), so
-- it follows the KA-server template directly.  Proved at CONCRETE
-- (linkBD , lo) — the BF-server half of `pipeBD`.
------------------------------------------------------------------------

-- the generic ren-OffersOnly specialised to the BlockFetch alphabet injection
module RenBF-OO = RenOO BF.BFEv-≟ ιBF ιBF⁻¹ ιBF-linv

-- source-side OffersOnly builders for the BF alphabet
module SrcBF = CSP.Laws.Bisim.DRCongruenceRep BF.BFEv-≟

-- the (direction) slot of a BF source event (the protocol is implicit = BF)
slotBF : AnyTypes BF.BFEv → Maybe Dir
slotBF (_ , BF.sendBF    _ d)   = just d
slotBF (_ , BF.receiveBF _ d)   = just d
slotBF (_ , BF.apiBFev   _ d _) = just d
slotBF (_ , BF.doneBF    _ d)   = just d

-- the BF source alphabet on direction `d`: every event on that direction
srcAlphaBF : Dir → SrcBF.Alpha
srcAlphaBF d at a = slotBF at ≡ just d

-- the ι-image of `srcAlphaBF d` lands in the BF peer slot on `d`
bf-img⊆ : (d : Dir) → ∀ at a → RenBF-OO.ιImg (srcAlphaBF d) at a → peerAlpha N2N_BlockFetch d at a
bf-img⊆ d (_ , input  l′ d′ N2N_BlockFetch)   a (_ , refl , refl) = refl
bf-img⊆ d (_ , output l′ d′ N2N_BlockFetch)   a (_ , refl , refl) = refl
bf-img⊆ d (_ , done   l′ d′ N2N_BlockFetch)   a (_ , refl , refl) = refl
bf-img⊆ d (_ , apiBF  l′ d′ m)                a (_ , refl , refl) = refl
bf-img⊆ d (_ , input  l′ d′ N2N_ChainSync)    a (_ , () , _)
bf-img⊆ d (_ , input  l′ d′ N2N_TxSubmission) a (_ , () , _)
bf-img⊆ d (_ , input  l′ d′ N2N_KeepAlive)    a (_ , () , _)
bf-img⊆ d (_ , input  l′ d′ N2N_LeiosNotify)  a (_ , () , _)
bf-img⊆ d (_ , input  l′ d′ N2N_LeiosFetch)   a (_ , () , _)
bf-img⊆ d (_ , output l′ d′ N2N_ChainSync)    a (_ , () , _)
bf-img⊆ d (_ , output l′ d′ N2N_TxSubmission) a (_ , () , _)
bf-img⊆ d (_ , output l′ d′ N2N_KeepAlive)    a (_ , () , _)
bf-img⊆ d (_ , output l′ d′ N2N_LeiosNotify)  a (_ , () , _)
bf-img⊆ d (_ , output l′ d′ N2N_LeiosFetch)   a (_ , () , _)
bf-img⊆ d (_ , done   l′ d′ N2N_ChainSync)    a (_ , () , _)
bf-img⊆ d (_ , done   l′ d′ N2N_TxSubmission) a (_ , () , _)
bf-img⊆ d (_ , done   l′ d′ N2N_KeepAlive)    a (_ , () , _)
bf-img⊆ d (_ , done   l′ d′ N2N_LeiosNotify)  a (_ , () , _)
bf-img⊆ d (_ , done   l′ d′ N2N_LeiosFetch)   a (_ , () , _)
bf-img⊆ d (_ , sndmsg l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , rcvmsg l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , tx     l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , sndack l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , rcvack l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , ack    l′ d′ i)                a (_ , () , _)
bf-img⊆ d (_ , apiCS  l′ d′ m)                a (_ , () , _)
bf-img⊆ d (_ , apiKA  l′ d′ m)                a (_ , () , _)
bf-img⊆ d (_ , apiTS  l′ d′ m)                a (_ , () , _)
bf-img⊆ d (_ , apiLN  l′ d′ m)                a (_ , () , _)
bf-img⊆ d (_ , apiLF  l′ d′ m)                a (_ , () , _)
bf-img⊆ d (_ , break  l′)                     a (_ , () , _)

-- l-GENERALISED BF server source OffersOnly (dir = lo).  4-way link enumeration;
-- per concrete link the stIdle recv menu and stBusy/stStreaming api-emit menus
-- fire only at (that link , lo); other Fin×Dir pairs and events refute.
bfServerSrc-OO : (l : Link) → SrcBF.OffersOnly (srcAlphaBF lo) (BF.BFserverStClient l lo)
bfServerSrc-OO F.zero = SrcBF.OffersOnly-iter {k = BF.serverStep F.zero lo} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF lo) (BF.serverStep F.zero lo q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgRequestRange range)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgClientDone) refl = refl , SrcBF.OffersOnly-Prefix₀ (λ _ → refl) SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFStartBatch) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev F.zero hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFNoBlocks) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev F.zero hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFBlock) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev F.zero hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFBatchDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev F.zero hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)     a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfServerSrc-OO (F.suc F.zero) = SrcBF.OffersOnly-iter {k = BF.serverStep (F.suc F.zero) lo} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF lo) (BF.serverStep (F.suc F.zero) lo q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgRequestRange range)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgClientDone) refl = refl , SrcBF.OffersOnly-Prefix₀ (λ _ → refl) SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFStartBatch) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFNoBlocks) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBlock) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBatchDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)     a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfServerSrc-OO (F.suc (F.suc F.zero)) = SrcBF.OffersOnly-iter {k = BF.serverStep (F.suc (F.suc F.zero)) lo} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF lo) (BF.serverStep (F.suc (F.suc F.zero)) lo q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgRequestRange range)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgClientDone) refl = refl , SrcBF.OffersOnly-Prefix₀ (λ _ → refl) SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFStartBatch) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFNoBlocks) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBlock) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBatchDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)     a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfServerSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcBF.OffersOnly-iter {k = BF.serverStep (F.suc (F.suc (F.suc F.zero))) lo} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF lo) (BF.serverStep (F.suc (F.suc (F.suc F.zero))) lo q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgRequestRange range)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgRequestRange range)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgClientDone) refl = refl , SrcBF.OffersOnly-Prefix₀ (λ _ → refl) SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgClientDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)   eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFStartBatch) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFStartBatch) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFNoBlocks) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFNoBlocks) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF lo) _
    mc (_ , BF.apiBFev F.zero lo sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBlock) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBlock) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFBatchDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFBatchDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFRequestRange) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFClientDone)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)     a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)        a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)         a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
-- BF SERVER impl peer confines to its (BlockFetch, lo) slot (transport + mono)
bfServer-OO : (l : Link) → OffersOnly (peerAlpha N2N_BlockFetch lo) (BFserverA l lo)
bfServer-OO l = OffersOnly-mono (bf-img⊆ lo) (RenBF-OO.ren-OffersOnly (bfServerSrc-OO l))

------------------------------------------------------------------------
-- Item 2(b), BlockFetch client OffersOnly at (linkBD , hi).  Reuses the
-- BF infra (RenBF-OO / slotBF / srcAlphaBF / bf-img⊆); only the source
-- FSM is `clientStep` (idle emits the two api requests via a wire send;
-- busy/streaming await wire inputs; done is √).  The two api-emit offers
-- at `stIdle` are Fin×Dir enumerated (finding 1) with only (linkBD , hi)
-- firing.
------------------------------------------------------------------------

-- l-GENERALISED BF client source OffersOnly (dir = hi).  4-way link enumeration.
bfClientSrc-OO : (l : Link) → SrcBF.OffersOnly (srcAlphaBF hi) (BF.BFclientStClient l hi)
bfClientSrc-OO F.zero = SrcBF.OffersOnly-iter {k = BF.clientStep F.zero hi} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF hi) (BF.clientStep F.zero hi q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.apiBFev F.zero lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFRequestRange) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFClientDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)  a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)       a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgStartBatch) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgNoBlocks) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgBlock b)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgBatchDone) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)         eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfClientSrc-OO (F.suc F.zero) = SrcBF.OffersOnly-iter {k = BF.clientStep (F.suc F.zero) hi} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF hi) (BF.clientStep (F.suc F.zero) hi q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.apiBFev F.zero lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFRequestRange) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFClientDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)  a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)       a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgStartBatch) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgNoBlocks) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgBlock b)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgBatchDone) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)         eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfClientSrc-OO (F.suc (F.suc F.zero)) = SrcBF.OffersOnly-iter {k = BF.clientStep (F.suc (F.suc F.zero)) hi} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF hi) (BF.clientStep (F.suc (F.suc F.zero)) hi q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.apiBFev F.zero lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFRequestRange) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFClientDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev _ _ sendBFStartBatch) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)  a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)       a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgStartBatch) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgNoBlocks) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgBlock b)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgBatchDone) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)         eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
bfClientSrc-OO (F.suc (F.suc (F.suc F.zero))) = SrcBF.OffersOnly-iter {k = BF.clientStep (F.suc (F.suc (F.suc F.zero))) hi} {a = BF.stIdle} step
  where
  step : ∀ q → SrcBF.OffersOnly (srcAlphaBF hi) (BF.clientStep (F.suc (F.suc (F.suc F.zero))) hi q)
  step BF.stIdle = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.apiBFev F.zero lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFRequestRange) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFRequestRange) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev F.zero lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev F.zero hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc F.zero) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc F.zero)) hi sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) lo sendBFClientDone) a ()
    mc (_ , BF.apiBFev (F.suc (F.suc (F.suc F.zero))) hi sendBFClientDone) a refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.apiBFev _ _ sendBFStartBatch) a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFNoBlocks)   a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ sendBFBatchDone)  a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ recvBFBlock)      a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ reqBFRange)       a eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.receiveBF _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stBusy = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgStartBatch) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgStartBatch) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgNoBlocks) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgNoBlocks) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgBlock b))        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgBatchDone)        eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stStreaming = SrcBF.OffersOnly-pchoice mc
    where
    mc : SrcBF.MenuConf (srcAlphaBF hi) _
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch (MsgBlock b)) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch (MsgBlock b)) refl = refl , SrcBF.OffersOnly-Output refl SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF F.zero lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF F.zero hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc F.zero) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc F.zero)) hi) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) lo) (t , m , len , blockFetch MsgBatchDone) ()
    mc (_ , BF.receiveBF (F.suc (F.suc (F.suc F.zero))) hi) (t , m , len , blockFetch MsgBatchDone) refl = refl , SrcBF.OffersOnly-Ret
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch (MsgRequestRange r)) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgStartBatch)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgNoBlocks)         eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , blockFetch MsgClientDone)       eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , keepAlive _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , chainSync _)    eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , txSubmission _) eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosNotify _)  eq = case eq of λ ()
    mc (_ , BF.receiveBF l′ d′) (t , m , len , leiosFetch _)   eq = case eq of λ ()
    mc (_ , BF.sendBF _ _)    a eq = case eq of λ ()
    mc (_ , BF.apiBFev _ _ _) a eq = case eq of λ ()
    mc (_ , BF.doneBF _ _)    a eq = case eq of λ ()
  step BF.stDone = SrcBF.OffersOnly-Ret
-- BF CLIENT impl peer confines to its (BlockFetch, hi) slot (transport + mono)
bfClient-OO : (l : Link) → OffersOnly (peerAlpha N2N_BlockFetch hi) (BFclientA l hi)
bfClient-OO l = OffersOnly-mono (bf-img⊆ hi) (RenBF-OO.ren-OffersOnly (bfClientSrc-OO l))

------------------------------------------------------------------------

------------------------------------------------------------------------
-- The M2-facing contract goal TYPE.
------------------------------------------------------------------------

-- the divergence-respecting weak bisimulation the milestone proves;
-- the proof term `pipe≈DR : (l) → PipeBisim l hi` is PROVED in
-- `PipePairAssembly` (via 8 per-peer rename/iter-erasure bisims + cong-⦀/cong-Par⊤)
PipeBisim : (l : Link) (d : Dir) → Set _
PipeBisim l d = pipe l d ≈DR pipeSpec l d

------------------------------------------------------------------------
-- Instantiation smoke test: the two `nodeD` pipelines and their goal
-- types elaborate (definitions only — no stepping).
------------------------------------------------------------------------

-- the BD consume pipeline (nodeD's BD half)
pipeBD : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
pipeBD = pipe linkBD hi

-- the CD consume pipeline (nodeD's CD half)
pipeCD : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
pipeCD = pipe linkCD hi

-- the two goal types (PROVED as `goalBD-proof`/`goalCD-proof` in PipePairAssembly)
goalBD : Set _
goalBD = PipeBisim linkBD hi

goalCD : Set _
goalCD = PipeBisim linkCD hi
