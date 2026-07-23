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
open import Data.List using (List; _∷_; [])
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)
import Class.DecEq.Instances as DecEqI

open import Level using (0ℓ)
open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.FourNode.FourNodeDiamond where
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

Four TCP links, each running every wire protocol in both directions
(KA/CS/BF/TS; Leios omitted — no peers for it in this scenario):

```agda
-- both directions × the four wire protocols (Leios omitted: no peers)
uniformCfg : List (Dir × IDs)
uniformCfg = (lo , N2N_KeepAlive)    ∷ (hi , N2N_KeepAlive)
           ∷ (lo , N2N_ChainSync)    ∷ (hi , N2N_ChainSync)
           ∷ (lo , N2N_BlockFetch)   ∷ (hi , N2N_BlockFetch)
           ∷ (lo , N2N_TxSubmission) ∷ (hi , N2N_TxSubmission) ∷ []
```

Concrete scenario: 4 links, uniform config on each; `Block = Block₃`, other domains ⊤:

```agda
-- concrete Params: Block = Block₃, all other data domains ⊤, 4 links, uniform config
p : Params
p = record
  { Cookie = U.⊤ ; Block = Block₃ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numLinks = 4 ; linkConfig = λ _ → uniformCfg
  ; decCookie = decEq⊤ ; decBlock = DecEq-Block₃ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = decEq⊤ ; decLength = decEq⊤ }
```

```agda
open import CSP.Examples.Cardano_network.Net p
  using ( Link; Net_Api; Net_Api-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break
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

The four TCP links (`Link = Fin 4`): A–B, A–C, B–D, C–D:

```agda
-- the four TCP links (Fin 4)
linkAB linkAC linkBD linkCD : Link
linkAB = # 0
linkAC = # 1
linkBD = # 2
linkCD = # 3
```

The API synchronisation set `{| apiCS, apiBF |}` — the rendezvous between a
node's peer bundle and its logic:

```agda
-- membership of the {| apiCS, apiBF |} sync set (by channel, ignoring payload)
apiSet : AnyTypes (Net_Api Payload) → Set
apiSet (_ , apiCS _ _ _) = ⊤
apiSet (_ , apiBF _ _ _) = ⊤
apiSet _                 = ⊥

-- decidability of apiSet membership
apiSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (apiSet at)
apiSet-dec (_ , apiCS  _ _ _) = yes tt
apiSet-dec (_ , apiBF  _ _ _) = yes tt
apiSet-dec (_ , input  _ _ _) = no λ ()
apiSet-dec (_ , output _ _ _) = no λ ()
apiSet-dec (_ , sndmsg _ _ _) = no λ ()
apiSet-dec (_ , rcvmsg _ _ _) = no λ ()
apiSet-dec (_ , tx     _ _ _) = no λ ()
apiSet-dec (_ , sndack _ _ _) = no λ ()
apiSet-dec (_ , rcvack _ _ _) = no λ ()
apiSet-dec (_ , ack    _ _ _) = no λ ()
apiSet-dec (_ , done   _ _ _) = no λ ()
apiSet-dec (_ , apiTS  _ _ _) = no λ ()
apiSet-dec (_ , apiKA  _ _ _) = no λ ()
apiSet-dec (_ , apiLN  _ _ _) = no λ ()
apiSet-dec (_ , apiLF  _ _ _) = no λ ()
apiSet-dec (_ , break  _)     = no λ ()

-- the {| apiCS, apiBF |} event set
apiES : EventSet
apiES = chanSet apiSet apiSet-dec
```

## Node logic

`produce l d blk` drives the ChainSync + BlockFetch **server** peers on link
`l`, direction `d`: await the consumer's `RequestNext`, detour through the
ChainSync server's `stMustReply` state with an `AwaitReply` (Praos-faithful),
push a `RollForward` header, then answer the block-range request with a
one-block batch.

```agda
-- server-side logic on (l, d): announce `blk` via ChainSync (via AwaitReply), serve it via BlockFetch
produce : (l : Link) (d : Dir) → Block₃
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
produce l d blk =
  apiCS l d reqCSRequestNext ⟶₀
  (apiCS l d sendCSAwaitReply ⟶₀
  (apiCS l d sendCSRollForward ! (header blk , tip blk) ⟶
  (apiBF l d reqBFRange ⟶
  (λ _ →
  (apiBF l d sendBFStartBatch ! U.tt ⟶
  (apiBF l d sendBFBlock ! blk ⟶
  (apiBF l d sendBFBatchDone ! U.tt ⟶
  Skip)))))))
```

`consume l d` drives the ChainSync + BlockFetch **client** peers on link `l`,
direction `d`: request the next header, request the announced block's range,
receive the block, close both protocols, and return the received block (so
relays can forward it).

```agda
-- client-side logic on (l, d): fetch the announced block; returns the block received
consume : (l : Link) (d : Dir)
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃
consume l d =
  apiCS l d sendCSRequestNext ⟶₀
  (apiCS l d recvCSRollforward ⟶
  (λ { (header b , _) →
  (apiBF l d sendBFRequestRange ! (chainRange (point b) (point b)) ⟶
  (apiBF l d recvBFBlock ⟶
  (λ b′ →
  (apiBF l d sendBFClientDone ! U.tt ⟶
  (apiCS l d sendCSDone ⟶₀
  Ret b′))))) }))
```

## Nodes

Each node composes its two link bundles (interleaved) with its logic,
synchronised on `apiES`. Endpoint assignment: A is `lo` on AB & AC; B is `hi`
on AB and `lo` on BD; C is `hi` on AC and `lo` on CD; D is `hi` on BD & CD.
A node **`produce`s on the direction where it is the server** and
**`consume`s on the direction where it is the client**; a matching
`produce`/`consume` pair lands on the same `(l, d)` instance.

```agda
-- A (lo-endpoint of AB, AC): client on lo, server on hi; A produces on its server dir = hi
nodeA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeA = (miniProtocols linkAB lo hi ⦀ miniProtocols linkAC lo hi)
          ∥⇘ apiES ⇙ (produce linkAB hi b1 ⦀ produce linkAC hi b1)

-- B (hi-endpoint of AB, lo-endpoint of BD): client on hi (AB), server on hi (BD)
nodeB : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeB = (miniProtocols linkAB hi lo ⦀ miniProtocols linkBD lo hi)
          ∥⇘ apiES ⇙ (consume linkAB hi >>= λ b → produce linkBD hi b)

-- C (hi-endpoint of AC, lo-endpoint of CD): client on hi (AC), server on hi (CD)
nodeC : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeC = (miniProtocols linkAC hi lo ⦀ miniProtocols linkCD lo hi)
          ∥⇘ apiES ⇙ (consume linkAC hi >>= λ b → produce linkCD hi b)

-- D (hi-endpoint of BD, CD): client on hi both; consumes on hi both
nodeD : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeD = (miniProtocols linkBD hi lo ⦀ miniProtocols linkCD hi lo)
          ∥⇘ apiES ⇙ ((consume linkBD hi >> Skip) ⦀ (consume linkCD hi >> Skip))
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
