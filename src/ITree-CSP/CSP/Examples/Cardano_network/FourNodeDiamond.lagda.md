# Four-node diamond — block-production scenario

Four nodes over one shared medium in a diamond (edges A–B, A–C, B–D, C–D):

```text
        A
       / \
      B   C
       \ /
        D
```

`A` produces a block; it is announced (ChainSync) and served (BlockFetch) to
`B` and `C`, which relay it onward to `D`. Each node's mini-protocol peers are
*API-driven*: application logic engages their `apiCS`/`apiBF` events to advance
the protocol FSMs. See the design doc
`docs/superpowers/specs/2026-07-03-four-node-scenario-node-logic-design.md`.

```agda
{-# OPTIONS --guardedness #-}
```

```agda
import Data.Unit as U
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (#_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Level using (0ℓ)
open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.FourNodeDiamond where
```

The trivial `⊤` data domains keep their decidable equality:

```agda
-- trivial decidable equality for the ⊤ data domains
instance
  decEq⊤ : DecEq U.⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }
```

A concrete three-value block type so `Point`/`Header`/`Tip` carry a
distinguishable block (A produces `b1`; `b2`/`b3` populate the type):

```agda
-- concrete block domain
data Block₃ : Set where
  b1 b2 b3 : Block₃

-- decidable equality on Block₃ (3×3)
instance
  DecEq-Block₃ : DecEq Block₃
  DecEq-Block₃ ._≟_ = go
    where
    go : (x y : Block₃) → Dec (x ≡ y)
    go b1 b1 = yes refl
    go b2 b2 = yes refl
    go b3 b3 = yes refl
    go b1 b2 = no λ ()
    go b1 b3 = no λ ()
    go b2 b1 = no λ ()
    go b2 b3 = no λ ()
    go b3 b1 = no λ ()
    go b3 b2 = no λ ()
```

Concrete scenario: 8 connections per protocol; `Block = Block₃`, other domains ⊤:

```agda
-- concrete Params: Block = Block₃, all other data domains ⊤, 8 conns per protocol
p : Params
p = record
  { Cookie = U.⊤ ; Block = Block₃ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numConns = λ _ → 8
  ; decCookie = decEq⊤ ; decBlock = DecEq-Block₃ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = decEq⊤ ; decLength = decEq⊤ }
```

```agda
open import CSP.Examples.Cardano_network.Net p
  using ( Conn; Net_Api; Net_Api-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF
        ; reqCSRequestNext; sendCSRollForward; sendCSAwaitReply; sendCSRequestNext
        ; recvCSRollforward; sendCSDone
        ; reqBFRange; sendBFStartBatch; sendBFBlock; sendBFBatchDone
        ; sendBFRequestRange; recvBFBlock; sendBFClientDone )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Point; Header; Tip; ChainRange
        ; point; header; tip; chainRange
        ; DecEq-Point; DecEq-Header; DecEq-Tip; DecEq-ChainRange )
open import CSP.Examples.Cardano_network.NetCommon p using (NetworkA; CopySpecA; ioES)
open import CSP.Examples.Cardano_network.NetworkPar p using (miniProtocols)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( Par⊤; _∥⇘_⇙_; _⦀_; _∖_; Skip; Ret
              ; Prefix; Prefix₀; Output; _>>=_; _>>_
              ; chanSet; EventSet )
```

`DecEq (Header × Tip)` is needed for the `sendCSRollForward` output:

```agda
-- product DecEq for the RollForward carrier (Header × Tip)
instance
  DecEq-Header×Tip : DecEq (Header × Tip)
  DecEq-Header×Tip = DecEqI.DecEq-×
```

Directional link ids (`Conn N2N_KeepAlive = Fin 8`). A–B: ab/ba, A–C: ac/ca,
B–D: bd/db, C–D: cd/dc:

```agda
-- directional link ids; A's client uses the first, its peer's client the swapped id
ab ba ac ca bd db cd dc : Conn N2N_KeepAlive
ab = # 0
ba = # 1
ac = # 2
ca = # 3
bd = # 4
db = # 5
cd = # 6
dc = # 7
```

```agda
-- a uniform link bundle: every protocol's client on `cl`, server on `sv`
mp : Conn N2N_KeepAlive → Conn N2N_KeepAlive
   → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
mp cl sv = miniProtocols cl sv cl sv cl sv cl sv
```

The API synchronisation set `{| apiCS, apiBF |}` — the rendezvous between a
node's peer bundle and its logic:

```agda
-- membership of the {| apiCS, apiBF |} sync set (by channel, ignoring payload)
apiSet : AnyTypes (Net_Api Payload) → Set
apiSet (_ , apiCS _ _) = ⊤
apiSet (_ , apiBF _ _) = ⊤
apiSet _               = ⊥

-- decidability of apiSet membership
apiSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (apiSet at)
apiSet-dec (_ , apiCS  _ _) = yes tt
apiSet-dec (_ , apiBF  _ _) = yes tt
apiSet-dec (_ , input  _ _) = no λ ()
apiSet-dec (_ , output _ _) = no λ ()
apiSet-dec (_ , sndmsg _ _) = no λ ()
apiSet-dec (_ , rcvmsg _ _) = no λ ()
apiSet-dec (_ , tx     _ _) = no λ ()
apiSet-dec (_ , sndack _ _) = no λ ()
apiSet-dec (_ , rcvack _ _) = no λ ()
apiSet-dec (_ , ack    _ _) = no λ ()
apiSet-dec (_ , done   _ _) = no λ ()
apiSet-dec (_ , apiTS  _ _) = no λ ()
apiSet-dec (_ , apiKA  _ _) = no λ ()
apiSet-dec (_ , apiLN  _ _) = no λ ()
apiSet-dec (_ , apiLF  _ _) = no λ ()

-- the {| apiCS, apiBF |} event set
apiES : EventSet
apiES = chanSet apiSet apiSet-dec
```

## Node logic

`produce c blk` drives the ChainSync + BlockFetch **server** peers on Conn `c`:
await the consumer's `RequestNext`, detour through the ChainSync server's
`stMustReply` state with an `AwaitReply` (Praos-faithful), push a `RollForward`
header, then answer the block-range request with a one-block batch.

```agda
-- server-side logic on Conn c: announce `blk` via ChainSync (via AwaitReply), serve it via BlockFetch
produce : Conn N2N_KeepAlive → Block₃
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
produce c blk =
  apiCS c reqCSRequestNext ⟶₀
  (apiCS c sendCSAwaitReply ⟶₀
  (apiCS c sendCSRollForward ! (header blk , tip blk) ⟶
  (apiBF c reqBFRange ⟶
  (λ _ →
  (apiBF c sendBFStartBatch ! U.tt ⟶
  (apiBF c sendBFBlock ! blk ⟶
  (apiBF c sendBFBatchDone ! U.tt ⟶
  Skip)))))))
```

`consume c` drives the ChainSync + BlockFetch **client** peers on Conn `c`:
request the next header, request the announced block's range, receive the block,
close both protocols, and return the received block (so relays can forward it).

```agda
-- client-side logic on Conn c: fetch the announced block; returns the block received
consume : Conn N2N_KeepAlive
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃
consume c =
  apiCS c sendCSRequestNext ⟶₀
  (apiCS c recvCSRollforward ⟶
  (λ { (header b , _) →
  (apiBF c sendBFRequestRange ! (chainRange (point b) (point b)) ⟶
  (apiBF c recvBFBlock ⟶
  (λ b′ →
  (apiBF c sendBFClientDone ! U.tt ⟶
  (apiCS c sendCSDone ⟶₀
  Ret b′))))) }))
```

## Nodes

Each node composes its two link bundles (interleaved) with its logic,
synchronised on `apiES`. Role/Conn mapping: A produces on `ba`(→B)/`ca`(→C);
B consumes on `ba`(from A) and produces on `db`(→D); C consumes on `ca` and
produces on `dc`; D consumes on `db`(from B) and `dc`(from C).

```agda
-- node A (producer): CS+BF servers on ba (→B) and ca (→C), each announcing b1
nodeA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeA = (mp ab ba ⦀ mp ac ca) ∥⇘ apiES ⇙ (produce ba b1 ⦀ produce ca b1)

-- node B (relay): consume from A on ba, then relay the received block to D on db
nodeB : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeB = (mp ba ab ⦀ mp bd db) ∥⇘ apiES ⇙ (consume ba >>= λ b → produce db b)

-- node C (relay): consume from A on ca, then relay the received block to D on dc
nodeC : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeC = (mp ca ac ⦀ mp cd dc) ∥⇘ apiES ⇙ (consume ca >>= λ b → produce dc b)

-- node D (consumer): consume from B on db and from C on dc (blocks discarded)
nodeD : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeD = (mp db bd ⦀ mp dc cd) ∥⇘ apiES ⇙ ((consume db >> Skip) ⦀ (consume dc >> Skip))
```

## Systems

The four nodes interleaved, synchronised with the medium on `{| input, output |}`,
io then hidden. Two variants over the same nodes: the `NetworkA` multiplexer
(kept for future use) and the FD-equivalent `CopySpec` medium.

```agda
-- the whole network over the full NetworkA multiplexer, io hidden
system : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
system = (NetworkA ∥⇘ ioES ⇙ (nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES

-- the same nodes over the FD-equivalent CopySpec medium (NetworkA ≈FD CopySpec)
System_CopySpec : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
System_CopySpec = (CopySpecA ∥⇘ ioES ⇙ (nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES
```

## Reachability / has-trace — a documented limitation

An explicit LTS has-trace witness (`System_CopySpec ⟹⟨ s ⟩ P′`) showing that a
block produced by `A` reaches `D` is **intractable** in Agda here, at any scope.
A feasibility spike (2026-07-05) found that constructing even a *single*
`─[ l ]─►` step of the composed system — via `sVis refl refl` — costs ≈2.5 min
and ≈20 GB, because taking one step forces the whole `∖ ioES` / `∥⇘` / `⦀` /
`renameMap CopySpec` medium-plus-peers term to weak-head normal form. A full
`A→{B,C}→D` trace is ~150+ such steps over states that only grow, so it cannot
be typechecked in reasonable time or memory; the single-hop `B→D` witness runs
on the same medium and is equally intractable. This is a limitation of
definitional normalisation on the composed term, not a soundness gap — the model
itself typechecks. Establishing reachability, if ever needed, would require a
different technique (a reflected/decidable small-step evaluator, or an abstract
trace transported across a bisimulation to a tiny specification), each a
substantial effort beyond a sanity check.
