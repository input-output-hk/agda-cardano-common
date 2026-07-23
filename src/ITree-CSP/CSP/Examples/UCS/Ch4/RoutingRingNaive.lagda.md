# UCS chapter 4 §4.2: the naive store-and-forward routing ring deadlocks

A "UCS" example, porting the **naive routing ring** of A.W. Roscoe's
*Understanding Concurrent Systems* (UCS), chapter 4 (routing networks),
machine-readable companion file:

- `fdr-examples/ucs/chapter04/dring.csp` (UCS ch. 4 §4.2, the naive ring)

`N = 4` nodes are arranged in a ring.  Each node is a **one-packet**
store-and-forward buffer: it may accept a fresh packet injected locally
(`send`) or a packet handed over the ring by its predecessor (`ring.i`), and it
then either delivers the packet (`receive`, if this node is the destination) or
hands it on to its successor (`ring.(i+1)%4`).  In CSP:

```csp
D (i)          = send.i?dst -> D'(i)(i , dst)  []  ring.i?p -> D'(i)(p)
D'(i)(s , r)   = if i == r then receive.i.s -> D(i)
                            else ring.((i+1)%4).(s , r) -> D(i)
Ring           = || i : Node @ [A(i)] D(i)
assert Ring :[deadlock free]          -- FAILS in FDR
```

**Why the ring deadlocks.**  A node holding a packet destined for a *remote*
node has committed to a **single** output — the forwarding `ring.(i+1)%4` — and
offers nothing else (in particular it no longer offers `ring.i?` *input*, since
it holds no free slot).  Fill *every* node with a remote packet (node `i` sends
to its neighbour `(i+1)%4`): all four nodes sit in `D'` wanting to output
`ring.(i+1)%4` while its intended recipient — the neighbour, *also* full — will
not accept `ring.(i+1)%4?`.  Each node's sole offer is a synchronisation that
its partner declines, so the whole ring is **stuck**.  FDR's
`Ring :[deadlock free]` assertion therefore *fails*; we prove the dual,
`HasDeadlock`, and derive `¬ DeadlockFree`.

**Modelling notes.**

- `Node = Fin 4`; a packet is `(src , dst) : Node × Node`.  The message payload
  is trivial (the source notes `T = {0}` suffices for the deadlock), so only the
  routing header `(src , dst)` is carried.
- Three value-carrying event channels, each tagged by the *node index* in the
  value: `send.i.dst` (inject at `i`, destination `dst`), `receive.i.s`
  (deliver at `i`, from source `s`), `ring.j.(s , r)` (packet handed to node
  `j`).  `send.i` / `receive.i` live in node `i`'s alphabet only (they fire
  **solo**); `ring.j` lives in both `A j` and `A ((j-1)%4)` (it is a **sync**
  between the two adjacent nodes it connects).
- The forwarding output `ring.(i+1)%4 -> D i` is modelled with the packet value
  *generalised* (the offer is present at `ring.(i+1)%4` for every value, all
  landing in the packet-agnostic continuation `D i`).  This is faithful to the
  deadlock: the continuation is identical, and the recipient neighbour declines
  `ring.(i+1)%4` at *every* value (it offers nothing at that index while full),
  so the stuck configuration is genuinely stuck regardless.  Keeping the offer
  value-generalised lets the composite offer map reduce definitionally at every
  event, so `IsStuck` is read straight off it (the DiningPhilosophers
  `dead-IsStuck` / `dp-csp-deadlock-reachable` pattern).

The scaffold defined here (`REv`, `REv-≟`, `Node`, `nextN`, `A`) is shared with
the later non-blocking-ring module.

## §1. Imports, node type, ring arithmetic

```agda
{-# OPTIONS --guardedness #-}

module CSP.Examples.UCS.Ch4.RoutingRingNaive where

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
Node = Fin 4

n0 n1 n2 n3 : Node
n0 = fzero
n1 = fsuc fzero
n2 = fsuc (fsuc fzero)
n3 = fsuc (fsuc (fsuc fzero))

-- (i + 1) mod 4, as a concrete four-case function.
nextN : Node → Node
nextN fzero                         = n1
nextN (fsuc fzero)                  = n2
nextN (fsuc (fsuc fzero))           = n3
nextN (fsuc (fsuc (fsuc fzero)))    = n0
```

## §2. The event type and its decidable equality

```agda
data REv : Set → Set where
  send    : REv (Node × Node)            -- send.i.dst      : (i , dst)
  receive : REv (Node × Node)            -- receive.i.src   : (i , src)
  ring    : REv (Node × (Node × Node))   -- ring.j.(src,dst): (j , (s , r))

REv-≟ : (x y : AnyTypes REv) → Dec (x ≡ y)
REv-≟ (_ , send)    (_ , send)    = yes refl
REv-≟ (_ , receive) (_ , receive) = yes refl
REv-≟ (_ , ring)    (_ , ring)    = yes refl
REv-≟ (_ , send)    (_ , receive) = no (λ ())
REv-≟ (_ , send)    (_ , ring)    = no (λ ())
REv-≟ (_ , receive) (_ , send)    = no (λ ())
REv-≟ (_ , receive) (_ , ring)    = no (λ ())
REv-≟ (_ , ring)    (_ , send)    = no (λ ())
REv-≟ (_ , ring)    (_ , receive) = no (λ ())

open import CSP.Operators REv-≟
open EventSet
```

## §3. Per-node alphabets

Node `i` owns `send.i`, `receive.i`, and the two ring endpoints it touches:
`ring.i` (packets arriving from its predecessor) and `ring.(i+1)%4` (packets it
forwards to its successor).

```agda
A : Node → EventSet
A i .mem (_ , send)    (j , _) = j ≡ i
A i .mem (_ , receive) (j , _) = j ≡ i
A i .mem (_ , ring)    (j , _) = (j ≡ i) ⊎ (j ≡ nextN i)
A i .dec (_ , send)    (j , _) = j Fin.≟ i
A i .dec (_ , receive) (j , _) = j Fin.≟ i
A i .dec (_ , ring)    (j , _) = (j Fin.≟ i) ⊎-dec (j Fin.≟ nextN i)
```

## §4. The naive node and the ring

`D i` is the empty node; `D′ i (s , r)` is the node holding packet `(s , r)`.
Following the `Customer`/`Merchant` (UCS ch. 3) idiom, the corecursive
`D`/`D′` loop is written as **inlined `react` copatterns** (the corecursive
calls sit directly under `just`), which the guardedness checker accepts — the
operator forms would route the recursion through function arguments.

```agda
DProcR : Set₁
DProcR = PTree REv (ExtI REv) (⊤poly {lzero})

D  : Node → DProcR
D′ : Node → (Node × Node) → DProcR

force (D i) = react
  (λ where
     (_ , send)    (j , dst) → case j Fin.≟ i of λ where
         (yes _) → just (D′ i (i , dst))
         (no  _) → nothing
     (_ , receive) _         → nothing
     (_ , ring)    (j , p)   → case j Fin.≟ i of λ where
         (yes _) → just (D′ i p)
         (no  _) → nothing)
  ∅t

force (D′ i (s , r)) = react
  (λ where
     (_ , send)    _         → nothing
     (_ , receive) (j , src) → case i Fin.≟ r of λ where
         (yes _) → case j Fin.≟ i of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → just (D i)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , ring)    (j , _)   → case i Fin.≟ r of λ where
         (yes _) → nothing                        -- destination: no forwarding
         (no  _) → case j Fin.≟ nextN i of λ where
             (yes _) → just (D i)                 -- forward to (i+1)%4
             (no  _) → nothing)
  ∅t

node : Node → Comp REv (⊤poly {lzero})
node i = comp (A i) (D i)

naiveRing : PTree REv (ExtI REv) (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ []))
naiveRing = ∥ₐ⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ [])
```

## §5. The reachable deadlock

Choose the **remote** destination `dstᵢ = (i+1)%4` for each node.  After the
four solo `send` steps, node `i` holds `(i , (i+1)%4)` and is in the forwarding
state `D′ i (i , (i+1)%4)`, offering only `ring.(i+1)%4`.

```agda
scomp : Node → Comp REv (⊤poly {lzero})
scomp i = comp (A i) (D′ i (i , nextN i))

-- the four intermediate configurations and the stuck endpoint
R1 R2 R3 stuckRing : PTree REv (ExtI REv) (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ node n3 ∷ []))
R1       = ∥ₐ⁺ (scomp n0) (node  n1 ∷ node  n2 ∷ node  n3 ∷ [])
R2       = ∥ₐ⁺ (scomp n0) (scomp n1 ∷ node  n2 ∷ node  n3 ∷ [])
R3       = ∥ₐ⁺ (scomp n0) (scomp n1 ∷ scomp n2 ∷ node  n3 ∷ [])
stuckRing = ∥ₐ⁺ (scomp n0) (scomp n1 ∷ scomp n2 ∷ scomp n3 ∷ [])
```

### §5.1 Verification machinery

```agda
open import Semantics.LTS      {E = REv} {I = ExtI REv}
open import Semantics.Deadlock {E = REv} {I = ExtI REv}
  using ( IsStuck; HasDeadlock; DeadlockFree
        ; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; hasDeadlock⇒¬deadlockFree )
open import CSP.Laws.AlphaParallelList REv-≟ using (VisHead; ∥ₐ⁺-headed)
```

### §5.2 The four solo `send` steps

`send.i` is in `A i` only, so each fires **solo**: the head node advances
(`αpar-soloL-step`) or a tail node does (`αpar-soloR-step`), leaving the other
operands untouched.

```agda
sendEv : Node → Node → Event
sendEv i d = evLabel (Node × Node) send (i , d)

step0 : naiveRing ─[ ev (evl (sendEv n0 n1)) ]─► R1
step0 = αpar-soloL-step {P′ = D′ n0 (n0 , n1)}
          refl
          (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ (inj₁ ()))) ; (inj₂ (inj₂ (inj₂ ()))) })
          refl refl refl

step1 : R1 ─[ ev (evl (sendEv n1 n2)) ]─► R2
step1 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1) (node n2 ∷ node n3 ∷ [])}
          (λ ()) (inj₁ refl) refl refl refl

step2 : R2 ─[ ev (evl (sendEv n2 n3)) ]─► R3
step2 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1) (scomp n2 ∷ node n3 ∷ [])}
          (λ ()) (inj₂ (inj₁ refl)) refl refl refl

step3 : R3 ─[ ev (evl (sendEv n3 n0)) ]─► stuckRing
step3 = αpar-soloR-step {Q′ = ∥ₐ⁺ (scomp n1) (scomp n2 ∷ scomp n3 ∷ [])}
          (λ ()) (inj₂ (inj₂ (inj₁ refl))) refl refl refl

reach : naiveRing ⟹∖√⟨ sendEv n0 n1 ∷ sendEv n1 n2 ∷ sendEv n2 n3 ∷ sendEv n3 n0 ∷ [] ⟩ stuckRing
reach = ∖√-ev step0 (∖√-ev step1 (∖√-ev step2 (∖√-ev step3 ∖√-refl)))
```

### §5.3 The stuck configuration

Every component is a react-headed-and-stable single-offer node, so the fold is
react-headed-and-stable (`∥ₐ⁺-headed`) — this refutes any τ-step.  For a visible
event, the merged offer of the four-fold `∥ₐ⁺` reduces to `nothing`: `send`/
`receive` are declined by every (forwarding) node, and each `ring.j` is a
synchronisation whose recipient node `j` (also forwarding) offers nothing at
index `j`.  We read this off by direct reduction, exactly as
`dp-csp-deadlock-reachable`.

```agda
D′-VisHead : ∀ {i p} → VisHead (D′ i p)
D′-VisHead = _ , _ , refl , (λ _ _ → refl)

allVH : All (λ d → VisHead (Comp.proc d)) (scomp n0 ∷ scomp n1 ∷ scomp n2 ∷ scomp n3 ∷ [])
allVH = D′-VisHead ∷ D′-VisHead ∷ D′-VisHead ∷ D′-VisHead ∷ []

stuck-headed : VisHead stuckRing
stuck-headed = ∥ₐ⁺-headed (scomp n0) (scomp n1 ∷ scomp n2 ∷ scomp n3 ∷ []) allVH

stuck-IsStuck : IsStuck stuckRing
stuck-IsStuck (sRet eq) = case eq of λ ()
stuck-IsStuck (sSil eq) = case eq of λ ()
stuck-IsStuck (sTau {i = i} {a = a} refl br) with stuck-headed
... | (v , τc , refl , st) rewrite st i a = case br of λ ()
-- send: no forwarding node offers `send`
stuck-IsStuck (sVis {at = _ , send} {a = fzero , _}                      refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc fzero , _}                 refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc (fsuc fzero) , _}          refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , send} {a = fsuc (fsuc (fsuc fzero)) , _}   refl br) = case br of λ ()
-- receive: no node is at its destination, so none offers `receive`
stuck-IsStuck (sVis {at = _ , receive} {a = fzero , _}                    refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc fzero , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc (fsuc fzero) , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , receive} {a = fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
-- ring.j: node j declines the forward from its predecessor (it is full, forwarding elsewhere)
stuck-IsStuck (sVis {at = _ , ring} {a = fzero , _}                    refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , ring} {a = fsuc fzero , _}               refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , ring} {a = fsuc (fsuc fzero) , _}        refl br) = case br of λ ()
stuck-IsStuck (sVis {at = _ , ring} {a = fsuc (fsuc (fsuc fzero)) , _} refl br) = case br of λ ()
```

### §5.4 The deadlock theorem

```agda
naiveRing-deadlocks : HasDeadlock naiveRing
naiveRing-deadlocks =
  sendEv n0 n1 ∷ sendEv n1 n2 ∷ sendEv n2 n3 ∷ sendEv n3 n0 ∷ []
  , stuckRing , reach , stuck-IsStuck

¬naiveRing-deadlockFree : ¬ DeadlockFree naiveRing
¬naiveRing-deadlockFree = hasDeadlock⇒¬deadlockFree naiveRing-deadlocks
```

So `Ring :[deadlock free]` fails exactly as FDR reports: the naive one-packet
store-and-forward ring, once every node holds a remote packet, is a cycle of
blocked forwardings with no free slot anywhere to break it.
