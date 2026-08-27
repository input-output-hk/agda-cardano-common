{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — τ-free node specs in the Praos namespace
-- (`Praos.NodeSpecs`).
--
-- The four `nodeXSpec` abstract nodes and their τ-free building blocks,
-- rebuilt IN THE PRAOS NAMESPACE so `abstractSystem` (`Praos.AbstractSystem`)
-- can be assembled WITHOUT importing the route-1 `Liveness.System` (or any
-- route-1 ≈DR proof module).  Importing the route-1 node modules
-- (`Liveness.NodeA/NodeBC/NodeD`) transitively rebuilds the heavy
-- `PipePairPeers*` proof modules (>480 s / timed out) — SLOW, not red — so
-- the self-contained τ-free table specs are COPIED here verbatim.
--
-- Sources (copied verbatim, only the module header/imports adjusted):
--   • DecEq instances + `flipDir`           ← Liveness.PipePair:159-191
--   • `NetTree`/`Table`/`tableSpec`/`tGo`/`tMenu`/`tsNode` interpreter
--     + the 8 τ-free peer table specs
--     (kaClientSpec/kaServerSpec/csClientSpec/csServerSpec/
--      bfClientSpec/bfServerSpec/tsClientSpec/tsServerSpec)
--                                            ← Liveness.PipePair:204-914
--   • `specBundle`                           ← Liveness.NodeDOffers:2332-2338
--   • `specBundleFlip`                       ← Liveness.NodeAOffers:112-118
--   • `nodeASpec`                            ← Liveness.NodeA:86-90
--   • `nodeBSpec`/`nodeCSpec`                ← Liveness.NodeBC:121-153
--   • `nodeDSpec`                            ← Liveness.NodeD:108-112
--
-- These are pure τ-free next-state table FSMs over `Net_Api Payload`; they
-- reference NEITHER `miniProtocols` NOR any ≈DR proof, hence the copy is
-- self-contained and typechecks in seconds.
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Process_Trees
open PTree

-- the concrete FourNode instantiation: shared Params `p`, the produce/consume
-- drivers, the `apiES` sync set, the seed block `blkA`, and the four link ids
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; produce; consume; apiES; linkAB; linkAC; linkBD; linkCD )

open import CSP.Examples.Cardano_network.Params using (Params)
open Params p   -- Cookie/Block/Txid/Time/Length/time₀/length₀ + DecEq instances

-- control enums (Dir/IDs/Mode/BlockingStyle/Link) + their DecEq instances
open import CSP.Examples.Cardano_network.Base

-- the shared payload (message datatypes + DecEq instances)
open import CSP.Examples.Cardano_network.Data p

-- the shared alphabet (Net_Api events, api tag enums) + DecEq instances
open import CSP.Examples.Cardano_network.Net p

-- Net_Api operators used by the node specs + their drivers
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _>>_; _>>=_; Skip )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs (blkA : Block₃) where

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
  -- NOTE: List Vote / List Tx / List VoteBlob equality is resolved by the
  -- AMBIENT generic `DecEqI.DecEq-List` — a NAMED local instance for them
  -- clashes with the generic (UnsolvedConstraints ambiguity), so is omitted.
  -- Point × LFBitmap (LF sendLFBlockTxsRequest api payload)
  DecEq-Point×LFBitmap : DecEq (Point × LFBitmap)
  DecEq-Point×LFBitmap = DecEqI.DecEq-×
  -- Block × List Tx (LF recvLFRangeBlock api payload)
  DecEq-Block×ListTx : DecEq (Block × List Tx)
  DecEq-Block×ListTx = DecEqI.DecEq-×

------------------------------------------------------------------------
-- Direction flip: the server runs on the direction opposite the client.
------------------------------------------------------------------------

-- the server-side direction opposite a client direction
flipDir : Dir → Dir
flipDir lo = hi
flipDir hi = lo

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
-- The KA loop `kcClient → kcWmsg c → kcAwait c → kcClient` plus the
-- `sendKADone` exit to √.  NOTE (Praos model): `apiKA ∈ apiES` on this branch
-- (FourNodeDiamond:154-162 gates ALL api channels), and the node drivers never
-- offer `apiKA`, so KA is INERT (frozen at `kcClient`), NOT a free-running
-- loop — the fairness `BlockLiveness⁺ᶠ` route is superseded here.
------------------------------------------------------------------------

-- KA client positions (state heads + mid-prefix positions)
data KAcPos : Set where
  kcClient : KAcPos                     -- loop head: offer the two api requests
  kcWmsg   : Cookie → KAcPos            -- wire-send of MsgKeepAlive c
  kcAwait  : Cookie → KAcPos            -- awaiting the response to c
  kcWdone  : KAcPos                     -- wire-send of MsgKADone (→ kcTerm directly; client has no node-local done)
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
...     | yes _ = just kcTerm
...     | no  _ = nothing
kaCnxt l d kcWdone (_ , input l′ d′ N2N_KeepAlive) pl | _ | _ = nothing
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
  ksRecv   : Cookie → KAsPos   -- api emit of recvKACookie (reports the received cookie c)
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
... | yes refl | yes refl = just (ksRecv c)
... | _        | _        = nothing
-- ksRecv: fire the api recvKACookie reporting the received cookie, then send the response
kaSnxt l d (ksRecv c) (_ , apiKA l′ d′ recvKACookie) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ c
...   | yes _ = just (ksResp c)
...   | no  _ = nothing
kaSnxt l d (ksRecv c) (_ , apiKA l′ d′ recvKACookie) x | _ | _ = nothing
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
  ccWdone : CScPos                  -- wire-send of MsgCSDone (→ ccTerm directly; client has no node-local done)
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
...     | yes _ = just ccTerm
...     | no  _ = nothing
csCnxt l d ccWdone (_ , input l′ d′ N2N_ChainSync) pl | _ | _ = nothing
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
  bcWcd    : BFcPos               -- wire-send of MsgClientDone (→ bcTerm directly; client has no node-local done)
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
...     | yes _ = just bcTerm
...     | no  _ = nothing
bfCnxt l d bcWcd (_ , input l′ d′ N2N_BlockFetch) pl | _ | _ = nothing
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
-- TxSubmission client (submitter) spec (dir d; apiTS ∈ apiES on this branch, so
-- TS is driver-gated: one MsgTSInit warm-up, then INERT at stIdle — not free).
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
  tcWdone : TScPos                             -- wire-send of MsgTSDone (→ tcTerm directly; client has no node-local done)
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
...     | yes _ = just tcTerm
...     | no  _ = nothing
tsCnxt l d tcWdone (_ , input l′ d′ N2N_TxSubmission) pl | _ | _ = nothing
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
-- LeiosNotify client spec (dir d, sends FromInitiator): the consumer loop
-- `lncIdle → lncWreq → lncBusy → recv-api → lncIdle` and the `sendLNDone`
-- exit to √.  Mirrors `LeiosNotify.clientStep` renamed through `ιLN`
-- (apiLNev↦apiLN, sendLN↦input N2N_LeiosNotify, receiveLN↦output …).
------------------------------------------------------------------------

-- LN client positions (state heads + mid-prefix positions)
data LNcPos : Set where
  lncIdle : LNcPos                 -- loop head: request-next / done api offers
  lncWreq : LNcPos                 -- wire-send MsgLNRequestNext (→ busy)
  lncWdone : LNcPos                -- wire-send MsgLNDone (→ √)
  lncBusy : LNcPos                 -- await one of the four notifications
  lncRann : Header → LNcPos        -- api emit recvLNBlockAnnouncement h (→ idle)
  lncRoff : Point → LNcPos         -- api emit recvLNBlockOffer q (→ idle)
  lncRtxs : Point → LNcPos         -- api emit recvLNBlockTxsOffer q (→ idle)
  lncRvot : List Vote → LNcPos     -- api emit recvLNVotesOffer vs (→ idle)
  lncTerm : LNcPos                 -- √ after the done handshake

-- LN client terminal positions
lnCfin : LNcPos → Bool
lnCfin lncTerm = true
lnCfin _       = false

-- LN client next-state table (mirrors `LeiosNotify.clientStep` renamed)
lnCnxt : Link → Dir → LNcPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe LNcPos)
lnCnxt l d lncIdle (_ , apiLN l′ d′ sendLNRequestNext) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lncWreq
... | _        | _        = nothing
lnCnxt l d lncIdle (_ , apiLN l′ d′ sendLNDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lncWdone
... | _        | _        = nothing
lnCnxt l d lncWreq (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | yes _ = just lncBusy
...     | no  _ = nothing
lnCnxt l d lncWreq (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnCnxt l d lncWdone (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | yes _ = just lncTerm
...     | no  _ = nothing
lnCnxt l d lncWdone (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnCnxt l d lncBusy (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify (MsgLNBlockAnnouncement h)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lncRann h)
... | _        | _        = nothing
lnCnxt l d lncBusy (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify (MsgLNBlockOffer q)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lncRoff q)
... | _        | _        = nothing
lnCnxt l d lncBusy (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify (MsgLNBlockTxsOffer q)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lncRtxs q)
... | _        | _        = nothing
lnCnxt l d lncBusy (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify (MsgLNVotesOffer vs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lncRvot vs)
... | _        | _        = nothing
lnCnxt l d (lncRann h) (_ , apiLN l′ d′ recvLNBlockAnnouncement) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ h
...   | yes _ = just lncIdle
...   | no  _ = nothing
lnCnxt l d (lncRann h) (_ , apiLN l′ d′ recvLNBlockAnnouncement) x | _ | _ = nothing
lnCnxt l d (lncRoff q) (_ , apiLN l′ d′ recvLNBlockOffer) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ q
...   | yes _ = just lncIdle
...   | no  _ = nothing
lnCnxt l d (lncRoff q) (_ , apiLN l′ d′ recvLNBlockOffer) x | _ | _ = nothing
lnCnxt l d (lncRtxs q) (_ , apiLN l′ d′ recvLNBlockTxsOffer) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ q
...   | yes _ = just lncIdle
...   | no  _ = nothing
lnCnxt l d (lncRtxs q) (_ , apiLN l′ d′ recvLNBlockTxsOffer) x | _ | _ = nothing
lnCnxt l d (lncRvot vs) (_ , apiLN l′ d′ recvLNVotesOffer) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ vs
...   | yes _ = just lncIdle
...   | no  _ = nothing
lnCnxt l d (lncRvot vs) (_ , apiLN l′ d′ recvLNVotesOffer) x | _ | _ = nothing
lnCnxt l d _ _ = λ _ → nothing

-- the LN client spec peer
lnClientSpec : Link → Dir → NetTree
lnClientSpec l d = tableSpec (record { isFin = lnCfin ; nxt = lnCnxt l d }) lncIdle

------------------------------------------------------------------------
-- LeiosNotify server spec (dir sv, sends FromResponder): the producer
-- awaits a request off the wire, then either terminates (Done) or delivers
-- exactly one of the four notifications, returning to idle.  Mirrors
-- `LeiosNotify.serverStep` renamed through `ιLN`.
------------------------------------------------------------------------

-- LN server positions
data LNsPos : Set where
  lnsIdle : LNsPos                 -- await a request off the wire
  lnsBusy : LNsPos                 -- choose which notification to send (api)
  lnsWann : Header → LNsPos        -- wire-send MsgLNBlockAnnouncement h (→ idle)
  lnsWoff : Point → LNsPos         -- wire-send MsgLNBlockOffer q (→ idle)
  lnsWtxs : Point → LNsPos         -- wire-send MsgLNBlockTxsOffer q (→ idle)
  lnsWvot : List Vote → LNsPos     -- wire-send MsgLNVotesOffer vs (→ idle)
  lnsDone : LNsPos                 -- the server-local done event (→ √)
  lnsTerm : LNsPos                 -- √ after the done handshake

-- LN server terminal positions
lnSfin : LNsPos → Bool
lnSfin lnsTerm = true
lnSfin _       = false

-- LN server next-state table (mirrors `LeiosNotify.serverStep` renamed)
lnSnxt : Link → Dir → LNsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe LNsPos)
lnSnxt l d lnsIdle (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify MsgLNRequestNext) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lnsBusy
... | _        | _        = nothing
lnSnxt l d lnsIdle (_ , output l′ d′ N2N_LeiosNotify)
      (t , m , len , leiosNotify MsgLNDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lnsDone
... | _        | _        = nothing
lnSnxt l d lnsBusy (_ , apiLN l′ d′ sendLNBlockAnnouncement) h with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lnsWann h)
... | _        | _        = nothing
lnSnxt l d lnsBusy (_ , apiLN l′ d′ sendLNBlockOffer) q with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lnsWoff q)
... | _        | _        = nothing
lnSnxt l d lnsBusy (_ , apiLN l′ d′ sendLNBlockTxsOffer) q with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lnsWtxs q)
... | _        | _        = nothing
lnSnxt l d lnsBusy (_ , apiLN l′ d′ sendLNVotesOffer) vs with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lnsWvot vs)
... | _        | _        = nothing
lnSnxt l d (lnsWann h) (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | yes _ = just lnsIdle
...     | no  _ = nothing
lnSnxt l d (lnsWann h) (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnSnxt l d (lnsWoff q) (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | yes _ = just lnsIdle
...     | no  _ = nothing
lnSnxt l d (lnsWoff q) (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnSnxt l d (lnsWtxs q) (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | yes _ = just lnsIdle
...     | no  _ = nothing
lnSnxt l d (lnsWtxs q) (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnSnxt l d (lnsWvot vs) (_ , input l′ d′ N2N_LeiosNotify) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | yes _ = just lnsIdle
...     | no  _ = nothing
lnSnxt l d (lnsWvot vs) (_ , input l′ d′ N2N_LeiosNotify) pl | _ | _ = nothing
lnSnxt l d lnsDone (_ , done l′ d′ N2N_LeiosNotify) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lnsTerm
... | _        | _        = nothing
lnSnxt l d _ _ = λ _ → nothing

-- the LN server spec peer
lnServerSpec : Link → Dir → NetTree
lnServerSpec l d = tableSpec (record { isFin = lnSfin ; nxt = lnSnxt l d }) lnsIdle

------------------------------------------------------------------------
-- LeiosFetch client spec (dir d, sends FromInitiator): the consumer loop
-- requests one of five things (EB / txs / votes / block-range / done);
-- the block-range case STREAMS (self-loop on `recvLFRangeBlock` until the
-- Last message returns to idle).  Mirrors `LeiosFetch.clientStep` renamed
-- through `ιLF` (apiLFev↦apiLF, sendLF↦input N2N_LeiosFetch, receiveLF↦output).
------------------------------------------------------------------------

-- LF client positions
data LFcPos : Set where
  lfcIdle : LFcPos                       -- loop head: five request api offers
  lfcWblk : EBHash → LFcPos              -- wire-send MsgLFBlockRequest h (→ blk)
  lfcWtxs : Point × LFBitmap → LFcPos     -- wire-send MsgLFBlockTxsRequest (→ btx)
  lfcWvot : List Vote → LFcPos           -- wire-send MsgLFVotesRequest vs (→ vot)
  lfcWrng : ChainRange → LFcPos          -- wire-send MsgLFBlockRangeRequest r (→ rng)
  lfcWdone : LFcPos                      -- wire-send MsgLFDone (→ √)
  lfcBlk : LFcPos                        -- await MsgLFBlock
  lfcBtx : LFcPos                        -- await MsgLFBlockTxs
  lfcVot : LFcPos                        -- await MsgLFVoteDelivery
  lfcRng : LFcPos                        -- await MsgLFNext/Last… (streaming head)
  lfcRblk : EB → LFcPos                  -- api emit recvLFBlock e (→ idle)
  lfcRbtx : List Tx → LFcPos             -- api emit recvLFBlockTxs ts (→ idle)
  lfcRvot : List VoteBlob → LFcPos       -- api emit recvLFVoteDelivery vs (→ idle)
  lfcRnextRng : Block × List Tx → LFcPos  -- api emit recvLFRangeBlock (→ rng, loop)
  lfcRlastRng : Block × List Tx → LFcPos  -- api emit recvLFRangeBlock (→ idle, final)
  lfcTerm : LFcPos                       -- √ after the done handshake

-- LF client terminal positions
lfCfin : LFcPos → Bool
lfCfin lfcTerm = true
lfCfin _       = false

-- LF client next-state table (mirrors `LeiosFetch.clientStep` renamed)
lfCnxt : Link → Dir → LFcPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe LFcPos)
lfCnxt l d lfcIdle (_ , apiLF l′ d′ sendLFBlockRequest) pt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcWblk pt)
... | _        | _        = nothing
lfCnxt l d lfcIdle (_ , apiLF l′ d′ sendLFBlockTxsRequest) pb with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcWtxs pb)
... | _        | _        = nothing
lfCnxt l d lfcIdle (_ , apiLF l′ d′ sendLFVotesRequest) vs with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcWvot vs)
... | _        | _        = nothing
lfCnxt l d lfcIdle (_ , apiLF l′ d′ sendLFBlockRangeRequest) r with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcWrng r)
... | _        | _        = nothing
lfCnxt l d lfcIdle (_ , apiLF l′ d′ sendLFDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfcWdone
... | _        | _        = nothing
lfCnxt l d (lfcWblk pt) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | yes _ = just lfcBlk
...     | no  _ = nothing
lfCnxt l d (lfcWblk pt) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfCnxt l d (lfcWtxs (pt , bm)) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | yes _ = just lfcBtx
...     | no  _ = nothing
lfCnxt l d (lfcWtxs (pt , bm)) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfCnxt l d (lfcWvot vs) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | yes _ = just lfcVot
...     | no  _ = nothing
lfCnxt l d (lfcWvot vs) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfCnxt l d (lfcWrng r) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | yes _ = just lfcRng
...     | no  _ = nothing
lfCnxt l d (lfcWrng r) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfCnxt l d lfcWdone (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | yes _ = just lfcTerm
...     | no  _ = nothing
lfCnxt l d lfcWdone (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfCnxt l d lfcBlk (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFBlock b)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcRblk b)
... | _        | _        = nothing
lfCnxt l d lfcBtx (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFBlockTxs ts)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcRbtx ts)
... | _        | _        = nothing
lfCnxt l d lfcVot (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFVoteDelivery vs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcRvot vs)
... | _        | _        = nothing
lfCnxt l d lfcRng (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcRnextRng (b , ts))
... | _        | _        = nothing
lfCnxt l d lfcRng (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfcRlastRng (b , ts))
... | _        | _        = nothing
lfCnxt l d (lfcRblk b) (_ , apiLF l′ d′ recvLFBlock) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ b
...   | yes _ = just lfcIdle
...   | no  _ = nothing
lfCnxt l d (lfcRblk b) (_ , apiLF l′ d′ recvLFBlock) x | _ | _ = nothing
lfCnxt l d (lfcRbtx ts) (_ , apiLF l′ d′ recvLFBlockTxs) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ ts
...   | yes _ = just lfcIdle
...   | no  _ = nothing
lfCnxt l d (lfcRbtx ts) (_ , apiLF l′ d′ recvLFBlockTxs) x | _ | _ = nothing
lfCnxt l d (lfcRvot vs) (_ , apiLF l′ d′ recvLFVoteDelivery) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ vs
...   | yes _ = just lfcIdle
...   | no  _ = nothing
lfCnxt l d (lfcRvot vs) (_ , apiLF l′ d′ recvLFVoteDelivery) x | _ | _ = nothing
lfCnxt l d (lfcRnextRng bt) (_ , apiLF l′ d′ recvLFRangeBlock) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ bt
...   | yes _ = just lfcRng
...   | no  _ = nothing
lfCnxt l d (lfcRnextRng bt) (_ , apiLF l′ d′ recvLFRangeBlock) x | _ | _ = nothing
lfCnxt l d (lfcRlastRng bt) (_ , apiLF l′ d′ recvLFRangeBlock) x with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl with x ≟ bt
...   | yes _ = just lfcIdle
...   | no  _ = nothing
lfCnxt l d (lfcRlastRng bt) (_ , apiLF l′ d′ recvLFRangeBlock) x | _ | _ = nothing
lfCnxt l d _ _ = λ _ → nothing

-- the LF client spec peer
lfClientSpec : Link → Dir → NetTree
lfClientSpec l d = tableSpec (record { isFin = lfCfin ; nxt = lfCnxt l d }) lfcIdle

------------------------------------------------------------------------
-- LeiosFetch server spec (dir sv, sends FromResponder): the producer
-- awaits a request off the wire and delivers in the matching busy state,
-- streaming the block-range case (self-loop on Next before the Last).
-- Mirrors `LeiosFetch.serverStep` renamed through `ιLF`.
------------------------------------------------------------------------

-- LF server positions
data LFsPos : Set where
  lfsIdle : LFsPos                       -- await one of five requests off the wire
  lfsBlk : LFsPos                        -- deliver a block (api)
  lfsBtx : LFsPos                        -- deliver selective txs (api)
  lfsVot : LFsPos                        -- deliver votes (api)
  lfsRng : LFsPos                        -- deliver a range item (api, streaming head)
  lfsDone : LFsPos                       -- the server-local done event (→ √)
  lfsWblk : EB → LFsPos                  -- wire-send MsgLFBlock e (→ idle)
  lfsWtxs : List Tx → LFsPos             -- wire-send MsgLFBlockTxs ts (→ idle)
  lfsWvot : List VoteBlob → LFsPos       -- wire-send MsgLFVoteDelivery vs (→ idle)
  lfsWnext : Block × List Tx → LFsPos     -- wire-send MsgLFNext… (→ rng, loop)
  lfsWlast : Block × List Tx → LFsPos     -- wire-send MsgLFLast… (→ idle, final)
  lfsTerm : LFsPos                       -- √ after the done handshake

-- LF server terminal positions
lfSfin : LFsPos → Bool
lfSfin lfsTerm = true
lfSfin _       = false

-- LF server next-state table (mirrors `LeiosFetch.serverStep` renamed)
lfSnxt : Link → Dir → LFsPos
       → (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe LFsPos)
lfSnxt l d lfsIdle (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFBlockRequest pt)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsBlk
... | _        | _        = nothing
lfSnxt l d lfsIdle (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFBlockTxsRequest pt bm)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsBtx
... | _        | _        = nothing
lfSnxt l d lfsIdle (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFVotesRequest vs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsVot
... | _        | _        = nothing
lfSnxt l d lfsIdle (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch (MsgLFBlockRangeRequest r)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsRng
... | _        | _        = nothing
lfSnxt l d lfsIdle (_ , output l′ d′ N2N_LeiosFetch)
      (t , m , len , leiosFetch MsgLFDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsDone
... | _        | _        = nothing
lfSnxt l d lfsBlk (_ , apiLF l′ d′ sendLFBlock) b with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfsWblk b)
... | _        | _        = nothing
lfSnxt l d lfsBtx (_ , apiLF l′ d′ sendLFBlockTxs) ts with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfsWtxs ts)
... | _        | _        = nothing
lfSnxt l d lfsVot (_ , apiLF l′ d′ sendLFVoteDelivery) vs with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfsWvot vs)
... | _        | _        = nothing
lfSnxt l d lfsRng (_ , apiLF l′ d′ sendLFNextBlockAndTxsInRange) bt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfsWnext bt)
... | _        | _        = nothing
lfSnxt l d lfsRng (_ , apiLF l′ d′ sendLFLastBlockAndTxsInRange) bt with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (lfsWlast bt)
... | _        | _        = nothing
lfSnxt l d (lfsWblk b) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | yes _ = just lfsIdle
...     | no  _ = nothing
lfSnxt l d (lfsWblk b) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfSnxt l d (lfsWtxs ts) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | yes _ = just lfsIdle
...     | no  _ = nothing
lfSnxt l d (lfsWtxs ts) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfSnxt l d (lfsWvot vs) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | yes _ = just lfsIdle
...     | no  _ = nothing
lfSnxt l d (lfsWvot vs) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfSnxt l d (lfsWnext (b , ts)) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | yes _ = just lfsRng
...     | no  _ = nothing
lfSnxt l d (lfsWnext (b , ts)) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfSnxt l d (lfsWlast (b , ts)) (_ , input l′ d′ N2N_LeiosFetch) pl with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl
      with pl ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | yes _ = just lfsIdle
...     | no  _ = nothing
lfSnxt l d (lfsWlast (b , ts)) (_ , input l′ d′ N2N_LeiosFetch) pl | _ | _ = nothing
lfSnxt l d lfsDone (_ , done l′ d′ N2N_LeiosFetch) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just lfsTerm
... | _        | _        = nothing
lfSnxt l d _ _ = λ _ → nothing

-- the LF server spec peer
lfServerSpec : Link → Dir → NetTree
lfServerSpec l d = tableSpec (record { isFin = lfSfin ; nxt = lfSnxt l d }) lfsIdle

------------------------------------------------------------------------
-- The τ-free spec bundles (mirror `miniProtocols l hi lo` / `l lo hi`).
------------------------------------------------------------------------

-- the τ-free spec bundle for the CONSUME orientation (client hi, server lo)
-- (copied from Liveness.NodeDOffers:2332-2338)
specBundle : (l : Link) → NetTree
specBundle l =
  kaClientSpec l hi ⦀ (kaServerSpec l lo
    ⦀ (csClientSpec l hi ⦀ (csServerSpec l lo
    ⦀ (bfClientSpec l hi ⦀ (bfServerSpec l lo
    ⦀ (tsClientSpec l hi ⦀ (tsServerSpec l lo
    ⦀ (lnClientSpec l hi ⦀ (lnServerSpec l lo
    ⦀ (lfClientSpec l hi ⦀ lfServerSpec l lo))))))))))

-- the τ-free spec bundle for the PRODUCE orientation (client lo, server hi)
-- (copied from Liveness.NodeAOffers:112-118)
specBundleFlip : (l : Link) → NetTree
specBundleFlip l =
  kaClientSpec l lo ⦀ (kaServerSpec l hi
    ⦀ (csClientSpec l lo ⦀ (csServerSpec l hi
    ⦀ (bfClientSpec l lo ⦀ (bfServerSpec l hi
    ⦀ (tsClientSpec l lo ⦀ (tsServerSpec l hi
    ⦀ (lnClientSpec l lo ⦀ (lnServerSpec l hi
    ⦀ (lfClientSpec l lo ⦀ lfServerSpec l hi))))))))))

------------------------------------------------------------------------
-- The four abstract nodes (12-peer specBundle diamond).  Each mirrors its
-- route-1 impl node's exact `⦀`/`∥⇘ apiES ⇙`/driver skeleton, with the
-- mini-protocol bundle replaced by its τ-free spec bundle and the driver
-- kept verbatim.  ALL 12 peers (KA/CS/BF/TS/LN/LF, client+server) are present
-- both sides (STEP-5 symmetrization) so the √ done-condition matches the
-- concrete `bundleG` peer-for-peer (the sound √ co-move of step 6).
------------------------------------------------------------------------

-- abstract node A: the two FLIPPED spec bundles + verbatim produce pair
-- (copied from Liveness.NodeA:86-90)
nodeASpec : NetTree
nodeASpec =
  (specBundleFlip linkAB ⦀ specBundleFlip linkAC)
    ∥⇘ apiES ⇙ (produce linkAB hi blkA ⦀ produce linkAC hi blkA)

-- abstract node B: straight AB spec bundle ⦀ flipped BD spec bundle + relay
-- (copied from Liveness.NodeBC:121-125)
nodeBSpec : NetTree
nodeBSpec =
  (specBundle linkAB ⦀ specBundleFlip linkBD)
    ∥⇘ apiES ⇙ (consume linkAB hi >>= λ b → produce linkBD hi b)

-- abstract node C: straight AC spec bundle ⦀ flipped CD spec bundle + relay
-- (copied from Liveness.NodeBC:149-153)
nodeCSpec : NetTree
nodeCSpec =
  (specBundle linkAC ⦀ specBundleFlip linkCD)
    ∥⇘ apiES ⇙ (consume linkAC hi >>= λ b → produce linkCD hi b)

-- abstract node D: the two straight spec bundles + verbatim consume pair
-- (copied from Liveness.NodeD:108-112)
nodeDSpec : NetTree
nodeDSpec =
  (specBundle linkBD ⦀ specBundle linkCD)
    ∥⇘ apiES ⇙ ((consume linkBD hi >> Skip {0ℓ}) ⦀ (consume linkCD hi >> Skip {0ℓ}))
