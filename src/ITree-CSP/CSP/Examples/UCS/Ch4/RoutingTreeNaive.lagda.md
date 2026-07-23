# UCS chapter 4 §4.2.1: the naive store-and-forward routing *tree* deadlocks

A "UCS" example, porting the **naive tree-routing** network of A.W. Roscoe's
*Understanding Concurrent Systems* (UCS), chapter 4 (routing networks),
machine-readable companion file:

- `fdr-examples/ucs/chapter04/tree1.csp` (UCS ch. 4 §4.2.1, the naive tree)

`N = 5` nodes are arranged in a **tree** with edges
`{ {0,1}, {0,2}, {0,3}, {1,4} }` (node `0` is the hub; `1` is an inner node with
child `4`; `2`, `3`, `4` are leaves).  Each node is a **one-packet**
store-and-forward buffer: it may accept a fresh packet injected locally
(`send`) or a packet handed to it by a neighbour (`pass?j.i`), and it then
either delivers the packet (`receive`, if this node is the destination) or hands
it on toward the destination's subtree (`pass.i.(next i r)`).  In CSP:

```csp
NodeE1(i)        = send.i?dst -> NodeF1(i)(i , dst)
                   [] pass?j:nbrs(i).i?p -> NodeF1(i)(p)
NodeF1(i)(s , r) = if i == r then receive.i.s -> NodeE1(i)
                              else pass.i.(next(i)(r)).(s , r) -> NodeE1(i)
Tree             = || i : Node @ [A(i)] NodeE1(i)
assert Tree :[deadlock free]          -- FAILS in FDR (strong conflict)
```

**Why the tree deadlocks (strong conflict).**  A tree has no cycles, so —
unlike the ring — a global stuck state needs *every* node blocked
simultaneously; two adjacent nodes each holding a packet destined *through* the
other form a **strong conflict**.  A node holding a packet for a *remote*
destination has committed to a **single** output — the forwarding
`pass.i.(next i r)` — and offers nothing else (in particular it no longer offers
`pass?j.i` *input*, since it holds no free slot).  Fill every node with a packet
routed *across* the `0–1` edge and its incident subtrees:

- node `0` holds `(0,4)` → wants `pass.0.1`   ┐ the strong-conflict pair:
- node `1` holds `(1,2)` → wants `pass.1.0`   ┘ each wants to hand to the other
- node `2` holds `(2,1)` → wants `pass.2.0`
- node `3` holds `(3,1)` → wants `pass.3.0`
- node `4` holds `(4,0)` → wants `pass.4.1`

Every node's sole offer is a synchronisation `pass.i.(next i r)` whose intended
recipient `next i r` — itself full, forwarding elsewhere and offering *no*
`pass` input — declines.  So the whole tree is **stuck**.  FDR's
`Tree :[deadlock free]` assertion therefore *fails*; we prove the dual,
`HasDeadlock`, and derive `¬ DeadlockFree`.

**Modelling notes.**

- `Node = Fin 5`; a packet is `(src , dst) : Node × Node`.  The payload is
  trivial (`T = ⊤`), so only the routing header `(src , dst)` is carried.
- Three value-carrying event channels: `send.i.dst` (inject at `i`), `receive.i.s`
  (deliver at `i`, from source `s`), and `pass.i.j.(s , r)` (node `i` hands the
  packet to neighbour `j`).  `send.i` / `receive.i` live in node `i`'s alphabet
  only (they fire **solo**); `pass.i.j` lives in *both* `A i` and `A j` (it is a
  **sync** between the two adjacent nodes it connects — sender `i`, receiver `j`).
- The forwarding output `pass.i.(next i r) -> NodeE1 i` is modelled with the
  packet value *generalised* (the offer is present at `pass.i.(next i r)` for
  every packet value, all landing in the packet-agnostic continuation
  `NodeE1 i`), exactly as `RoutingRingNaive` did.  This is faithful to the
  deadlock: the continuation is identical, and the recipient neighbour declines
  the forward at *every* value (a full node offers *no* `pass` input), so the
  stuck configuration is genuinely stuck regardless.  Keeping the offer
  value-generalised lets the composite offer map reduce definitionally at every
  event, so `IsStuck` is read straight off it.

The scaffold defined here (`TEv`, `TEv-≟`, `Node`, `nbrs`, `next`, `A`) is
shared with a later swap-tree module.

## §1. Imports, node type, tree topology

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch4.RoutingTreeNaive where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

Node : Set
Node = Fin 5

n0 n1 n2 n3 n4 : Node
n0 = fzero
n1 = fsuc fzero
n2 = fsuc (fsuc fzero)
n3 = fsuc (fsuc (fsuc fzero))
n4 = fsuc (fsuc (fsuc (fsuc fzero)))

-- Tree edges { {0,1}, {0,2}, {0,3}, {1,4} }, as an adjacency table.
nbrs : Node → List Node
nbrs fzero                              = n1 ∷ n2 ∷ n3 ∷ []
nbrs (fsuc fzero)                       = n0 ∷ n4 ∷ []
nbrs (fsuc (fsuc fzero))                = n0 ∷ []
nbrs (fsuc (fsuc (fsuc fzero)))         = n0 ∷ []
nbrs (fsuc (fsuc (fsuc (fsuc fzero))))  = n1 ∷ []

-- `next i r` = the neighbour of `i` on the (unique, tree) path toward `r`.
-- Concrete routing table for THIS tree (defaults are harmless: a node only ever
-- forwards toward a genuine remote destination in its own subtree split).
next : Node → Node → Node
next fzero (fsuc (fsuc fzero))                     = n2   -- 0 → 2 (child 2)
next fzero (fsuc (fsuc (fsuc fzero)))              = n3   -- 0 → 3 (child 3)
next fzero _                                       = n1   -- 0 → 1 (toward {1,4})
next (fsuc fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) = n4   -- 1 → 4 (child 4)
next (fsuc fzero) _                                = n0   -- 1 → 0 (toward hub)
next (fsuc (fsuc fzero)) _                         = n0   -- 2 → 0 (leaf)
next (fsuc (fsuc (fsuc fzero))) _                  = n0   -- 3 → 0 (leaf)
next (fsuc (fsuc (fsuc (fsuc fzero)))) _           = n1   -- 4 → 1 (leaf)
```

## §2. The event type and its decidable equality

```agda
data TEv : Set → Set where
  send    : TEv (Node × Node)                    -- send.i.dst      : (i , dst)
  receive : TEv (Node × Node)                    -- receive.i.src   : (i , src)
  pass    : TEv (Node × (Node × (Node × Node)))  -- pass.i.j.(s,r)  : (i , (j , (s , r)))

TEv-≟ : (x y : AnyTypes TEv) → Dec (x ≡ y)
TEv-≟ (_ , send)    (_ , send)    = yes refl
TEv-≟ (_ , receive) (_ , receive) = yes refl
TEv-≟ (_ , pass)    (_ , pass)    = yes refl
TEv-≟ (_ , send)    (_ , receive) = no (λ ())
TEv-≟ (_ , send)    (_ , pass)    = no (λ ())
TEv-≟ (_ , receive) (_ , send)    = no (λ ())
TEv-≟ (_ , receive) (_ , pass)    = no (λ ())
TEv-≟ (_ , pass)    (_ , send)    = no (λ ())
TEv-≟ (_ , pass)    (_ , receive) = no (λ ())

open import CSP.Operators TEv-≟
open EventSet
```

## §3. Per-node alphabets

Node `i` owns `send.i`, `receive.i`, and every `pass` endpoint it touches: a
`pass.from.to` event belongs to `A i` when `i` is either the sender (`from ≡ i`)
or the receiver (`to ≡ i`).  Thus `send`/`receive` are node-`i`-solo, while each
`pass.i.j` synchronises exactly the two adjacent nodes `i` and `j`.

```agda
A : Node → EventSet
A i .mem (_ , send)    (j , _)          = j ≡ i
A i .mem (_ , receive) (j , _)          = j ≡ i
A i .mem (_ , pass)    (from , to , _)  = (from ≡ i) ⊎ (to ≡ i)
A i .dec (_ , send)    (j , _)          = j Fin.≟ i
A i .dec (_ , receive) (j , _)          = j Fin.≟ i
A i .dec (_ , pass)    (from , to , _)  = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)
```

## §4. The naive node and the tree

`NodeE1 i` is the empty node; `NodeF1 i (s , r)` is the node holding packet
`(s , r)`.  Following the `RoutingRingNaive` idiom, the corecursive
`NodeE1`/`NodeF1` loop is written as **inlined `react` copatterns** (the
corecursive calls sit directly under `just`), which the guardedness checker
accepts — the operator forms would route the recursion through function
arguments.

```agda
DProcT : Set₁
DProcT = PTree TEv (ExtI TEv) (⊤poly {lzero})

NodeE1 : Node → DProcT
NodeF1 : Node → (Node × Node) → DProcT

force (NodeE1 i) = react
  (λ where
     (_ , send)    (j , dst)         → case j Fin.≟ i of λ where
         (yes _) → just (NodeF1 i (i , dst))
         (no  _) → nothing
     (_ , receive) _                 → nothing
     (_ , pass)    (from , to , p)   → case to Fin.≟ i of λ where
         (yes _) → just (NodeF1 i p)          -- accept a packet passed to i
         (no  _) → nothing)
  ∅t

force (NodeF1 i (s , r)) = react
  (λ where
     (_ , send)    _                 → nothing
     (_ , receive) (j , src)         → case i Fin.≟ r of λ where
         (yes _) → case j Fin.≟ i of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → just (NodeE1 i)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , pass)    (from , to , _)   → case i Fin.≟ r of λ where
         (yes _) → nothing                    -- destination: no forwarding
         (no  _) → case from Fin.≟ i of λ where
             (yes _) → case to Fin.≟ next i r of λ where
                 (yes _) → just (NodeE1 i)     -- forward to next i r
                 (no  _) → nothing
             (no  _) → nothing)
  ∅t

node : Node → Comp TEv (⊤poly {lzero})
node i = comp (A i) (NodeE1 i)

naiveTree : PTree TEv (ExtI TEv)
              (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ node n4 ∷ []))
naiveTree = ∥ₐ⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ node n4 ∷ [])
```

## §5. The reachable deadlock

Each node `i` injects the packet `(i , dstᵢ)` chosen so that every node ends up
forwarding across the `0–1` edge or into its subtree: `dst₀ = 4`, `dst₁ = 2`,
`dst₂ = 1`, `dst₃ = 1`, `dst₄ = 0`.  After the five solo `send` steps, node `i`
sits in the forwarding state `NodeF1 i (i , dstᵢ)`, offering only its single
`pass.i.(next i dstᵢ)`.

The concrete held packets and their forwarding components:

```agda
scomp : Node → (Node × Node) → Comp TEv (⊤poly {lzero})
scomp i p = comp (A i) (NodeF1 i p)

-- the five intermediate configurations and the stuck endpoint
T1 T2 T3 T4 stuckTree : PTree TEv (ExtI TEv)
                          (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ node n4 ∷ []))
T1        = ∥ₐ⁺ (scomp n0 (n0 , n4)) (node n1 ∷ node n2 ∷ node n3 ∷ node n4 ∷ [])
T2        = ∥ₐ⁺ (scomp n0 (n0 , n4)) (scomp n1 (n1 , n2) ∷ node n2 ∷ node n3 ∷ node n4 ∷ [])
T3        = ∥ₐ⁺ (scomp n0 (n0 , n4)) (scomp n1 (n1 , n2) ∷ scomp n2 (n2 , n1) ∷ node n3 ∷ node n4 ∷ [])
T4        = ∥ₐ⁺ (scomp n0 (n0 , n4)) (scomp n1 (n1 , n2) ∷ scomp n2 (n2 , n1) ∷ scomp n3 (n3 , n1) ∷ node n4 ∷ [])
stuckTree = ∥ₐ⁺ (scomp n0 (n0 , n4)) (scomp n1 (n1 , n2) ∷ scomp n2 (n2 , n1) ∷ scomp n3 (n3 , n1) ∷ scomp n4 (n4 , n0) ∷ [])
```

### §5.1 Verification machinery

```agda
open import Semantics.LTS      {E = TEv} {I = ExtI TEv}
open import Semantics.Deadlock {E = TEv} {I = ExtI TEv}
  using ( IsStuck; HasDeadlock; DeadlockFree
        ; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; hasDeadlock⇒¬deadlockFree )
open import CSP.Laws.AlphaParallelList TEv-≟ using (VisHead; ∥ₐ⁺-headed)
```

### §5.2 The five solo `send` steps

`send.i` is in `A i` only, so each fires **solo**: the head node advances
(`αpar-soloL-step`) or a tail node does (`αpar-soloR-step`), leaving the other
operands untouched.

```agda
sendEv : Node → Node → Event
sendEv i d = evLabel (Node × Node) send (i , d)

step0 : naiveTree ─[ ev (evl (sendEv n0 n4)) ]─► T1
step0 = αpar-soloL-step {P′ = NodeF1 n0 (n0 , n4)}
          refl
          (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ (inj₁ ())))
             ; (inj₂ (inj₂ (inj₂ (inj₁ ())))) ; (inj₂ (inj₂ (inj₂ (inj₂ ())))) })
          refl refl refl

step1 : T1 ─[ ev (evl (sendEv n1 n2)) ]─► T2
step1 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1 (n1 , n2)) (node n2 ∷ node n3 ∷ node n4 ∷ [])}
          (λ ()) (inj₁ refl) refl refl refl

step2 : T2 ─[ ev (evl (sendEv n2 n1)) ]─► T3
step2 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1 (n1 , n2)) (scomp n2 (n2 , n1) ∷ node n3 ∷ node n4 ∷ [])}
          (λ ()) (inj₂ (inj₁ refl)) refl refl refl

step3 : T3 ─[ ev (evl (sendEv n3 n1)) ]─► T4
step3 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1 (n1 , n2)) (scomp n2 (n2 , n1) ∷ scomp n3 (n3 , n1) ∷ node n4 ∷ [])}
          (λ ()) (inj₂ (inj₂ (inj₁ refl))) refl refl refl

step4 : T4 ─[ ev (evl (sendEv n4 n0)) ]─► stuckTree
step4 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1 (n1 , n2)) (scomp n2 (n2 , n1) ∷ scomp n3 (n3 , n1) ∷ scomp n4 (n4 , n0) ∷ [])}
          (λ ()) (inj₂ (inj₂ (inj₂ (inj₁ refl)))) refl refl refl

reach : naiveTree ⟹∖√⟨ sendEv n0 n4 ∷ sendEv n1 n2 ∷ sendEv n2 n1 ∷ sendEv n3 n1 ∷ sendEv n4 n0 ∷ [] ⟩ stuckTree
reach = ∖√-ev step0 (∖√-ev step1 (∖√-ev step2 (∖√-ev step3 (∖√-ev step4 ∖√-refl))))
```

### §5.3 The stuck configuration

Every component is a react-headed-and-stable single-offer node, so the fold is
react-headed-and-stable (`∥ₐ⁺-headed`) — this refutes any τ-step.  For a visible
event, the merged offer of the five-fold `∥ₐ⁺` reduces to `nothing`:
`send`/`receive` are declined by every (forwarding) node, and each `pass.i.j` is
a synchronisation whose recipient node `j` (also forwarding, offering *no* `pass`
input) declines.  We read this off by direct reduction.  Because a `pass` sync is
identified by *both* endpoints (sender `from`, receiver `to`), the `pass` clauses
split on both node indices.

```agda
NodeF1-VisHead : ∀ {i p} → VisHead (NodeF1 i p)
NodeF1-VisHead = _ , _ , refl , (λ _ _ → refl)

allVH : All (λ d → VisHead (Comp.proc d))
             (scomp n0 (n0 , n4) ∷ scomp n1 (n1 , n2) ∷ scomp n2 (n2 , n1)
              ∷ scomp n3 (n3 , n1) ∷ scomp n4 (n4 , n0) ∷ [])
allVH = NodeF1-VisHead ∷ NodeF1-VisHead ∷ NodeF1-VisHead ∷ NodeF1-VisHead ∷ NodeF1-VisHead ∷ []

stuck-headed : VisHead stuckTree
stuck-headed = ∥ₐ⁺-headed (scomp n0 (n0 , n4))
                 (scomp n1 (n1 , n2) ∷ scomp n2 (n2 , n1) ∷ scomp n3 (n3 , n1) ∷ scomp n4 (n4 , n0) ∷ [])
                 allVH

stuck-IsStuck : IsStuck stuckTree
stuck-IsStuck (sRet eq) = case eq of λ ()
stuck-IsStuck (sSil eq) = case eq of λ ()
stuck-IsStuck (sTau {i = i} {a = a} refl br) with stuck-headed
... | (v , τc , refl , st) rewrite st i a = case br of λ ()
-- send: no forwarding node offers `send`
stuck-IsStuck (sVis {at = _ , send} {a = fzero , _}                    refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc fzero , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc (fsuc fzero) , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc (fsuc (fsuc (fsuc fzero))) , _} refl br) = case br of λ ()
-- receive: no node is at its destination, so none offers `receive`
stuck-IsStuck (sVis {at = _ , receive} {a = fzero , _}                    refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc fzero , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc (fsuc fzero) , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc (fsuc (fsuc (fsuc fzero))) , _} refl br) = case br of λ ()
-- pass.from.to: the receiver `to` (full, forwarding elsewhere) declines every incoming pass.
stuck-IsStuck (sVis {at = _ , pass} {a = fzero , fzero , _}                                  refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fzero , fsuc fzero , _}                             refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fzero , fsuc (fsuc fzero) , _}                      refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fzero , fsuc (fsuc (fsuc fzero)) , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fzero , fsuc (fsuc (fsuc (fsuc fzero))) , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc fzero , fzero , _}                             refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , _}                        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc fzero , fsuc (fsuc fzero) , _}                 refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc fzero , fsuc (fsuc (fsuc fzero)) , _}          refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc fzero , fsuc (fsuc (fsuc (fsuc fzero))) , _}   refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc fzero) , fzero , _}                      refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc fzero) , fsuc fzero , _}                 refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc fzero) , fsuc (fsuc fzero) , _}          refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc fzero) , fsuc (fsuc (fsuc fzero)) , _}   refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc fzero) , fsuc (fsuc (fsuc (fsuc fzero))) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc fzero)) , fzero , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc fzero)) , fsuc fzero , _}          refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc fzero)) , fsuc (fsuc fzero) , _}   refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc fzero)) , fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc fzero)) , fsuc (fsuc (fsuc (fsuc fzero))) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc (fsuc fzero))) , fzero , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc (fsuc fzero))) , fsuc fzero , _}   refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc (fsuc fzero))) , fsuc (fsuc fzero) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc (fsuc fzero))) , fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , pass} {a = fsuc (fsuc (fsuc (fsuc fzero))) , fsuc (fsuc (fsuc (fsuc fzero))) , _} refl br) = case br of λ ()
```

### §5.4 The deadlock theorem

```agda
naiveTree-deadlocks : HasDeadlock naiveTree
naiveTree-deadlocks =
  sendEv n0 n4 ∷ sendEv n1 n2 ∷ sendEv n2 n1 ∷ sendEv n3 n1 ∷ sendEv n4 n0 ∷ []
  , stuckTree , reach , stuck-IsStuck

¬naiveTree-deadlockFree : ¬ DeadlockFree naiveTree
¬naiveTree-deadlockFree = hasDeadlock⇒¬deadlockFree naiveTree-deadlocks
```

So `Tree :[deadlock free]` fails exactly as FDR reports: once every node holds a
packet routed across the `0–1` edge, the naive one-packet store-and-forward tree
is a **strong conflict** — a set of mutually blocked forwardings with no free
slot anywhere to break it.
</content>
</invoke>
