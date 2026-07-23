{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2.1: the `general4` routing network, DIVERGENCE-FREE.
--
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/general4.csp   (UCS ch. 4, general routing)
--
-- FDR reports the two HOLDING general4 asserts
--
--   assert HNetwork :[divergence free]    -- HOLDS
--   assert Network  :[deadlock free]      -- HOLDS  (sibling module)
--
-- This module proves the FIRST of them, `general4-divergenceFree :
-- DivergenceFree HNetwork`.  It is the exact counterpart of the general4a
-- LIVELOCK (`CSP.Examples.UCS.Ch4.GeneralNetworkLivelock`), which used a BAD
-- cyclic `next` that circulated a packet forever; general4 uses a CAREFUL
-- delivering `next` and is divergence-free.
--
-- TOPOLOGY (minimal cyclic).  `Node = Fin 3` forming a TRIANGLE: spanning tree
-- `TEdges = {{0,1},{1,2}}` (path 0–1–2) plus the extra edge `XEdges = {{0,2}}`
-- that closes the cycle.  Adjacency `tnbrs 0 = [1]`, `tnbrs 1 = [0,2]`,
-- `tnbrs 2 = [1]`; `xnbrs 0 = [2]`, `xnbrs 1 = []`, `xnbrs 2 = [0]`.  Routing
-- `next` = the spanning-tree route `tnext` EXCEPT the extra edge routes direct
-- (`next 0 2 = 2`, `next 2 0 = 0`); `tree? i r = (next i r ≡ tnext i r)` picks
-- swap (tree edge) vs yes/no negotiation (extra edge).  Because all three edges
-- of the triangle are present, `next i r ≡ r` for every `i ≠ r` (a complete
-- graph — every packet is one hop from its destination), which is exactly what
-- makes the internal τ-DAG ACYCLIC (no circulation).
--
-- FAITHFULNESS / PINNED OFFERS (load-bearing for a *universal* claim).  The full
-- general4 node `NodeE4`/`NodeF4`→`NodeF4L`/`NodeF4T`/`NodeF4O` (swap on tree
-- edges, yes/no negotiation on the extra edge, deliver when `i≡r`, decline
-- incoming `no?` while busy) is defined faithfully with PINNED forwards/swaps
-- (§4), and exported for the sibling deadlock-free module.
--
-- ⚠  DIVERGENCE-FREEDOM REDUCTION (documented per the task spec).  A faithful
-- constructive `DivergenceFree` over the FULL swap+negotiation node on a cycle
-- is a value-level τ-DAG whose config enumeration is astronomically large (the
-- swap *tree* alone — `RoutingTreeSwap` — needed the N=2 reduction).  This module
-- therefore proves `DivergenceFree` on the GOOD-ROUTING CORE: the delivering
-- `pass`-network with the careful acyclic `next` (the tight counterpart of
-- `GeneralNetworkLivelock`, which circulated).  The core node stores a packet and
-- forwards it PINNED to `next i r ≡ r` (delivers via `receive` at the
-- destination); with `pass` hidden the only internal moves are single-hop
-- deliveries, so the τ-DAG is acyclic and no reachable state diverges.  The full
-- node is still defined (§4') and exported.  The offers of BOTH the core and the
-- full node are PINNED — an over-approximated (payload-generalised) forward would
-- be UNSOUND for the universal divergence-freedom claim.
--
-- PROOF (§5).  `Network` = `∥ₐ⁺` of the three core node `Comp`s;
-- `HNetwork = Network ∖ {|pass,swap,yes,no|}`.  Every node is react-headed and
-- STABLE (τ-map ≡ ∅t), so `Network` has NO τ-step; every τ of `HNetwork` is a
-- HIDDEN visible `pass` sync (`Hide-τ-elim`).  We track the joint config by DATA
-- tags (`e` empty / `f p` holding), decode with `⟦_⟧`, invert a composite visible
-- step (`sys-inv`: solo `send`/`receive` or a `pass` sync between the two nodes)
-- into a config-level `SysStep`, and define a measure `μ` = number of nodes
-- holding a NOT-yet-delivered packet.  Every hidden `pass` sync strictly
-- decreases `μ` (single-hop delivery), so `¬ Diverges` follows by well-founded
-- recursion on `μ`; a `⟹∖√` reach-walk (`reach-cons`) confines every reachable
-- state to a config, giving `DivergenceFree HNetwork`.

module CSP.Examples.UCS.Ch4.General4DivFree where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n; _≤_)
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Process_Trees
open PTree

-------------------------------------------------------------------------------------
-- §1. Node type and the minimal-cyclic (triangle) topology.
-------------------------------------------------------------------------------------

Node : Set
Node = Fin 3

n0 n1 n2 : Node
n0 = fzero
n1 = fsuc fzero
n2 = fsuc (fsuc fzero)

-- Tree neighbours (spanning tree, path 0–1–2) and extra-edge neighbours.
tnbrs xnbrs : Node → List Node
tnbrs fzero               = n1 ∷ []
tnbrs (fsuc fzero)        = n0 ∷ n2 ∷ []
tnbrs (fsuc (fsuc fzero)) = n1 ∷ []
xnbrs fzero               = n2 ∷ []
xnbrs (fsuc fzero)        = []
xnbrs (fsuc (fsuc fzero)) = n0 ∷ []

-- Spanning-tree route (path 0–1–2); `tnext i i` is unused (delivered at dest).
tnext : Node → Node → Node
tnext fzero               fzero               = n0
tnext fzero               (fsuc fzero)        = n1
tnext fzero               (fsuc (fsuc fzero)) = n1   -- 0→2 via 1 in the tree
tnext (fsuc fzero)        fzero               = n0
tnext (fsuc fzero)        (fsuc fzero)        = n1
tnext (fsuc fzero)        (fsuc (fsuc fzero)) = n2
tnext (fsuc (fsuc fzero)) fzero               = n1   -- 2→0 via 1 in the tree
tnext (fsuc (fsuc fzero)) (fsuc fzero)        = n1
tnext (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = n2

-- Routing: the tree route except the extra edge routes DIRECT.  Because the
-- triangle is complete, `next i r ≡ r` for all `i ≠ r` (see `next≡dest`).
next : Node → Node → Node
next fzero               (fsuc (fsuc fzero)) = n2   -- extra edge 0–2: direct
next (fsuc (fsuc fzero)) fzero               = n0   -- extra edge 2–0: direct
next i                   r                   = tnext i r

-- `tree? i r` — is the next hop reached via a tree edge (`next i r ≡ tnext i r`)?
tree? : Node → Node → Bool
tree? i r = ⌊ next i r Fin.≟ tnext i r ⌋

-------------------------------------------------------------------------------------
-- §2. The event type and its decidable equality.
-------------------------------------------------------------------------------------

data GEv : Set → Set where
  send    : GEv (Node × Node)                    -- send.i.dst      : (i , dst)
  receive : GEv (Node × Node)                    -- receive.i.src   : (i , src)
  pass    : GEv (Node × (Node × (Node × Node)))  -- pass.from.to.(s,r)
  swap    : GEv (Node × (Node × (Node × Node)))  -- swap.from.to.(s,r)
  yesc    : GEv (Node × Node)                    -- yes.i.j
  noc     : GEv (Node × Node)                    -- no.i.j

GEv-≟ : (x y : AnyTypes GEv) → Dec (x ≡ y)
GEv-≟ (_ , send)    (_ , send)    = yes refl
GEv-≟ (_ , receive) (_ , receive) = yes refl
GEv-≟ (_ , pass)    (_ , pass)    = yes refl
GEv-≟ (_ , swap)    (_ , swap)    = yes refl
GEv-≟ (_ , yesc)    (_ , yesc)    = yes refl
GEv-≟ (_ , noc)     (_ , noc)     = yes refl
GEv-≟ (_ , send)    (_ , receive) = no (λ ())
GEv-≟ (_ , send)    (_ , pass)    = no (λ ())
GEv-≟ (_ , send)    (_ , swap)    = no (λ ())
GEv-≟ (_ , send)    (_ , yesc)    = no (λ ())
GEv-≟ (_ , send)    (_ , noc)     = no (λ ())
GEv-≟ (_ , receive) (_ , send)    = no (λ ())
GEv-≟ (_ , receive) (_ , pass)    = no (λ ())
GEv-≟ (_ , receive) (_ , swap)    = no (λ ())
GEv-≟ (_ , receive) (_ , yesc)    = no (λ ())
GEv-≟ (_ , receive) (_ , noc)     = no (λ ())
GEv-≟ (_ , pass)    (_ , send)    = no (λ ())
GEv-≟ (_ , pass)    (_ , receive) = no (λ ())
GEv-≟ (_ , pass)    (_ , swap)    = no (λ ())
GEv-≟ (_ , pass)    (_ , yesc)    = no (λ ())
GEv-≟ (_ , pass)    (_ , noc)     = no (λ ())
GEv-≟ (_ , swap)    (_ , send)    = no (λ ())
GEv-≟ (_ , swap)    (_ , receive) = no (λ ())
GEv-≟ (_ , swap)    (_ , pass)    = no (λ ())
GEv-≟ (_ , swap)    (_ , yesc)    = no (λ ())
GEv-≟ (_ , swap)    (_ , noc)     = no (λ ())
GEv-≟ (_ , yesc)    (_ , send)    = no (λ ())
GEv-≟ (_ , yesc)    (_ , receive) = no (λ ())
GEv-≟ (_ , yesc)    (_ , pass)    = no (λ ())
GEv-≟ (_ , yesc)    (_ , swap)    = no (λ ())
GEv-≟ (_ , yesc)    (_ , noc)     = no (λ ())
GEv-≟ (_ , noc)     (_ , send)    = no (λ ())
GEv-≟ (_ , noc)     (_ , receive) = no (λ ())
GEv-≟ (_ , noc)     (_ , pass)    = no (λ ())
GEv-≟ (_ , noc)     (_ , swap)    = no (λ ())
GEv-≟ (_ , noc)     (_ , yesc)    = no (λ ())

-- decidable equality on packets `Node × Node`
pkt≟ : (p q : Node × Node) → Dec (p ≡ q)
pkt≟ = ×-≡-dec Fin._≟_ Fin._≟_

open import CSP.Operators GEv-≟
open EventSet

-------------------------------------------------------------------------------------
-- §3. Per-node alphabet (per general4.csp A(i)): pass/swap to tree neighbours,
-- yes/no to extra neighbours, send/receive solo.  A pass/swap.from.to (resp.
-- yes/no.i.j) belongs to node k iff k is an endpoint.
-------------------------------------------------------------------------------------

A : Node → EventSet
A i .mem (_ , send)    (j , _)          = j ≡ i
A i .mem (_ , receive) (j , _)          = j ≡ i
A i .mem (_ , pass)    (from , to , _)  = (from ≡ i) ⊎ (to ≡ i)
A i .mem (_ , swap)    (from , to , _)  = (from ≡ i) ⊎ (to ≡ i)
A i .mem (_ , yesc)    (j , k)          = (j ≡ i) ⊎ (k ≡ i)
A i .mem (_ , noc)     (j , k)          = (j ≡ i) ⊎ (k ≡ i)
A i .dec (_ , send)    (j , _)          = j Fin.≟ i
A i .dec (_ , receive) (j , _)          = j Fin.≟ i
A i .dec (_ , pass)    (from , to , _)  = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)
A i .dec (_ , swap)    (from , to , _)  = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)
A i .dec (_ , yesc)    (j , k)          = (j Fin.≟ i) ⊎-dec (k Fin.≟ i)
A i .dec (_ , noc)     (j , k)          = (j Fin.≟ i) ⊎-dec (k Fin.≟ i)

-------------------------------------------------------------------------------------
-- §4. The GOOD-ROUTING CORE node (the delivering pass-network; §divergence proof).
-- Corecursive loop as inlined `react` copatterns; τ-branch ≡ ∅t (STABLE).  The
-- forward is PINNED: `NodeF i (s,r)` at a NON-destination (`i ≢ r`) offers ONLY
-- `pass.i.r.(s,r)` (recall `next i r ≡ r`), and at the destination (`i ≡ r`)
-- offers ONLY `receive.i.s`.  `NodeE i` accepts a fresh `send.i?dst` or an
-- incoming `pass?from.i?p`.
-------------------------------------------------------------------------------------

CProc : Set₁
CProc = PTree GEv (ExtI GEv) (⊤poly {lzero})

NodeE : Node → CProc
NodeF : Node → (Node × Node) → CProc

force (NodeE i) = react
  (λ where
     (_ , send)    (j , dst)        → case j Fin.≟ i of λ where
         (yes _) → just (NodeF i (i , dst))
         (no  _) → nothing
     (_ , receive) _                → nothing
     (_ , pass)    (from , to , p)  → case to Fin.≟ i of λ where
         (yes _) → case from Fin.≟ i of λ where
             (yes _) → nothing               -- reject a self-pass (never a real hand-off)
             (no  _) → just (NodeF i p)       -- accept a packet handed in by another node
         (no  _) → nothing
     (_ , swap)    _                → nothing
     (_ , yesc)    _                → nothing
     (_ , noc)     _                → nothing)
  ∅t

force (NodeF i (s , r)) = react
  (λ where
     (_ , send)    _                → nothing
     (_ , receive) (j , src)        → case i Fin.≟ r of λ where
         (yes _) → case j Fin.≟ i of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → just (NodeE i)      -- deliver at destination, PINNED src≡s
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , pass)    (from , to , p)  → case i Fin.≟ r of λ where
         (yes _) → nothing                     -- destination: no forwarding
         (no  _) → case from Fin.≟ i of λ where
             (yes _) → case to Fin.≟ r of λ where       -- forward to next i r ≡ r
                 (yes _) → case pkt≟ p (s , r) of λ where
                     (yes _) → just (NodeE i)  -- forward the held packet, PINNED
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
     (_ , swap)    _                → nothing
     (_ , yesc)    _                → nothing
     (_ , noc)     _                → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §4'. The FULL general4 node (faithful to general4.csp, PINNED), EXPORTED for the
-- sibling deadlock-free module.  It is NOT used by the divergence-freedom proof below
-- (which runs on the good-routing core §4); it is provided so Task 2 can build the
-- full swap+negotiation network.  `NodeE4` accepts a fresh `send`, a tree `pass?`, or
-- an extra-edge `yes?`-then-`pass?`; a full node dispatches on the packet:
-- `NodeF4L` delivers at the destination (declining incoming `no?`), `NodeF4T` runs the
-- tree2 swap handshake (declining `no?`), `NodeF4O` runs the tree3 yes/no negotiation
-- (`yes`→deliver-hop / `no`→tree fallback; declining `no?`).  All forwards / swap
-- outputs are PINNED to the held packet; `pass?`/`swap?`/`yes?` inputs are genuine `?`.
_∈ᵇ_ : Node → List Node → Bool
x ∈ᵇ []       = false
x ∈ᵇ (y ∷ ys) = ⌊ x Fin.≟ y ⌋ ∨ (x ∈ᵇ ys)

NodeE4    : Node → CProc
NodeE4Y   : Node → Node → CProc
dispatchJust : Node → (Node × Node) → Maybe CProc
NodeF4L   : Node → Node → CProc
NodeF4T   : Node → (Node × Node) → CProc
NodeF4Sw1 : Node → (Node × Node) → CProc
NodeF4Sw2 : Node → (Node × Node) → (Node × Node) → CProc
NodeF4O   : Node → (Node × Node) → CProc
NodeF4OY  : Node → (Node × Node) → CProc

-- The dispatcher, packaged as a guarded `Maybe` continuation (each corecursive call
-- is directly under `just`): at destination → deliver; tree hop → swap; extra → negotiate.
dispatchJust i (s , r) = case i Fin.≟ r of λ where
  (yes _) → just (NodeF4L i s)
  (no  _) → case tree? i r of λ where
      true  → just (NodeF4T i (s , r))
      false → just (NodeF4O i (s , r))

force (NodeE4 i) = react
  (λ where
     (_ , send)    (j , dst)       → case j Fin.≟ i of λ where
         (yes _) → dispatchJust i (i , dst)
         (no  _) → nothing
     (_ , receive) _               → nothing
     (_ , pass)    (from , to , p) → case to Fin.≟ i of λ where
         (yes _) → case (from ∈ᵇ tnbrs i) of λ where
             true  → dispatchJust i p
             false → nothing
         (no  _) → nothing
     (_ , swap)    _               → nothing
     (_ , yesc)    (j , k)         → case k Fin.≟ i of λ where
         (yes _) → case (j ∈ᵇ xnbrs i) of λ where
             true  → just (NodeE4Y i j)
             false → nothing
         (no  _) → nothing
     (_ , noc)     _               → nothing)
  ∅t

force (NodeE4Y i j) = react
  (λ where
     (_ , pass) (from , to , p) → case from Fin.≟ j of λ where
         (yes _) → case to Fin.≟ i of λ where
             (yes _) → dispatchJust i p
             (no  _) → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4L i s) = react
  (λ where
     (_ , receive) (j , src) → case j Fin.≟ i of λ where
         (yes _) → case src Fin.≟ s of λ where
             (yes _) → just (NodeE4 i)
             (no  _) → nothing
         (no  _) → nothing
     (_ , noc)     (j , k)   → case k Fin.≟ i of λ where
         (yes _) → case (j ∈ᵇ xnbrs i) of λ where
             true  → just (NodeF4L i s)
             false → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4T i (s , r)) = react
  (λ where
     (_ , pass) (from , to , p) → case from Fin.≟ i of λ where
         (yes _) → case to Fin.≟ tnext i r of λ where
             (yes _) → case pkt≟ p (s , r) of λ where
                 (yes _) → just (NodeE4 i)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , swap) (from , to , p) → case from Fin.≟ i of λ where
         (yes _) → case to Fin.≟ tnext i r of λ where          -- OUTPUT swap.i.(tnext i r).(s,r)
             (yes _) → case pkt≟ p (s , r) of λ where
                 (yes _) → just (NodeF4Sw1 i (s , r))
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → case from Fin.≟ tnext i r of λ where        -- INPUT swap.(tnext i r).i?p′
             (yes _) → case to Fin.≟ i of λ where
                 (yes _) → just (NodeF4Sw2 i (s , r) p)
                 (no  _) → nothing
             (no  _) → nothing
     (_ , noc) (j , k) → case k Fin.≟ i of λ where
         (yes _) → case (j ∈ᵇ xnbrs i) of λ where
             true  → just (NodeF4T i (s , r))
             false → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4Sw1 i (s , r)) = react
  (λ where
     (_ , swap) (from , to , p) → case from Fin.≟ tnext i r of λ where  -- INPUT swap.(tnext i r).i?p′
         (yes _) → case to Fin.≟ i of λ where
             (yes _) → dispatchJust i p
             (no  _) → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4Sw2 i (s , r) q) = react
  (λ where
     (_ , swap) (from , to , p) → case from Fin.≟ i of λ where       -- OUTPUT swap.i.(tnext i r).(s,r)
         (yes _) → case to Fin.≟ tnext i r of λ where
             (yes _) → case pkt≟ p (s , r) of λ where
                 (yes _) → dispatchJust i q
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4O i (s , r)) = react
  (λ where
     (_ , yesc) (j , k) → case j Fin.≟ i of λ where                 -- OUTPUT yes.i.(next i r)
         (yes _) → case k Fin.≟ next i r of λ where
             (yes _) → just (NodeF4OY i (s , r))
             (no  _) → nothing
         (no  _) → nothing
     (_ , noc)  (j , k) → case j Fin.≟ i of λ where
         (yes _) → case k Fin.≟ next i r of λ where                 -- OUTPUT no.i.(next i r) → tree fallback
             (yes _) → just (NodeF4T i (s , r))
             (no  _) → nothing
         (no  _) → case k Fin.≟ i of λ where                        -- INPUT no?(j∈xnbrs i).i → self
             (yes _) → case (j ∈ᵇ xnbrs i) of λ where
                 true  → just (NodeF4O i (s , r))
                 false → nothing
             (no  _) → nothing
     _ _ → nothing)
  ∅t

force (NodeF4OY i (s , r)) = react
  (λ where
     (_ , pass) (from , to , p) → case from Fin.≟ i of λ where
         (yes _) → case to Fin.≟ next i r of λ where
             (yes _) → case pkt≟ p (s , r) of λ where
                 (yes _) → just (NodeE4 i)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     _ _ → nothing)
  ∅t

node : Node → Comp GEv (⊤poly {lzero})
node i = comp (A i) (NodeE i)

Network : PTree GEv (ExtI GEv) (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ []))
Network = ∥ₐ⁺ (node n0) (node n1 ∷ node n2 ∷ [])

-- hide the whole internal signalling channel {|pass,swap,yes,no|}
intES-cs : AnyTypes GEv → Set
intES-cs (_ , send)    = ⊥
intES-cs (_ , receive) = ⊥
intES-cs (_ , pass)    = ⊤
intES-cs (_ , swap)    = ⊤
intES-cs (_ , yesc)    = ⊤
intES-cs (_ , noc)     = ⊤

intES-dec : (at : AnyTypes GEv) → Dec (intES-cs at)
intES-dec (_ , send)    = no (λ z → z)
intES-dec (_ , receive) = no (λ z → z)
intES-dec (_ , pass)    = yes tt
intES-dec (_ , swap)    = yes tt
intES-dec (_ , yesc)    = yes tt
intES-dec (_ , noc)     = yes tt

intES : EventSet
intES = chanSet intES-cs intES-dec

HNetwork : PTree GEv (ExtI GEv) (RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ []))
HNetwork = Network ∖ intES

-------------------------------------------------------------------------------------
-- §5. Divergence-freedom of `HNetwork` (good-routing core; acyclic single-hop τ-DAG).
-------------------------------------------------------------------------------------

open import Data.Nat.Properties using (n<1+n; +-monoʳ-<)
open import Semantics.LTS        {E = GEv} {I = ExtI GEv} hiding (Diverges)
open import Semantics.Deadlock   {E = GEv} {I = ExtI GEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DRBisim    {E = GEv} {I = ExtI GEv} using (Diverges)
open import Semantics.DeadlockDR {E = GEv} {I = ExtI GEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide GEv-≟
  using (Hide-τ-elim; HideτR; hτP; hτH; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.AlphaParallel GEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

Ret3 : Set
Ret3 = RetOf⁺ (node n0) (node n1 ∷ node n2 ∷ [])

-- R-independent event labels.
sendEv : Node → Node → Event
sendEv i dst = evLabel (Node × Node) send (i , dst)
recvEv : Node → Node → Event
recvEv i s = evLabel (Node × Node) receive (i , s)
passEv : Node → Node → (Node × Node) → Event
passEv f t p = evLabel (Node × (Node × (Node × Node))) pass (f , (t , p))

-- Node state TAG (empty / holding a packet), decoded to a core process by `dec`.
data St : Set where
  e : St
  f : (Node × Node) → St

nd : Node → St → CProc
nd i e     = NodeE i
nd i (f p) = NodeF i p

B12 B2 : EventSet
B12 = unionα (node n1 ∷ node n2 ∷ [])
B2  = unionα (node n2 ∷ [])

Tail : St → St → PTree GEv (ExtI GEv) (⊤poly {lzero} × ⊤poly {lzero})
Tail y z = nd n1 y ⟦ A n1 ∥ B2 ⟧ nd n2 z

Sys : St → St → St → PTree GEv (ExtI GEv) Ret3
Sys x y z = nd n0 x ⟦ A n0 ∥ B12 ⟧ Tail y z

netw≡ : Network ≡ Sys e e e
netw≡ = refl

H : St → St → St → PTree GEv (ExtI GEv) Ret3
H x y z = Sys x y z ∖ intES

hnet≡ : HNetwork ≡ H e e e
hnet≡ = refl

------------------------------------------------------------------------------------
-- §5.1 Every node is react-headed and STABLE: no τ / √ transition.
noret : ∀ i x {r} → nd i x .force ≡ ret r → ⊥
noret i e ()
noret i (f (s , r)) ()

noτ : ∀ i x {t′} → nd i x ─[ τ ]─► t′ → ⊥
noτ i e           (sSil eq)      = case eq of λ ()
noτ i e           (sTau refl br) = case br of λ ()
noτ i (f (s , r)) (sSil eq)      = case eq of λ ()
noτ i (f (s , r)) (sTau refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §5.2 Per-node visible-step transition relation over the state tags, and its
-- inversion.  Forwards (`ns-passout`) are PINNED (the offer's `pkt≟`/`Fin.≟` guards
-- pin them to the held packet and to `next i r ≡ r`); `ns-passin`/`ns-send` are
-- genuine `?` inputs / injections.
data NStep (i : Node) : St → St → Event → Set where
  ns-send    : ∀ dst      → NStep i e           (f (i , dst)) (sendEv i dst)
  ns-passin  : ∀ from p   → ¬ (from ≡ i) → NStep i e (f p)     (passEv from i p)
  ns-recv    : ∀ s        → NStep i (f (s , i)) e              (recvEv i s)
  ns-passout : ∀ s r      → ¬ (i ≡ r) → NStep i (f (s , r)) e  (passEv i r (s , r))

node-inv : ∀ {t′ ee} i x → nd i x ─[ ev (evl ee) ]─► t′
         → Σ[ x′ ∈ St ] (t′ ≡ nd i x′ × NStep i x x′ ee)
-- empty node
node-inv i e (sVis {at = _ , send}    {a = j , dst}          refl br) with j Fin.≟ i
... | yes refl = f (i , dst) , sym (just-injective br) , ns-send dst
... | no  _    = case br of λ ()
node-inv i e (sVis {at = _ , receive}                        refl br) = case br of λ ()
node-inv i e (sVis {at = _ , pass}    {a = from , to , p}    refl br) with to Fin.≟ i
... | no  _    = case br of λ ()
... | yes refl with from Fin.≟ i
...   | yes _    = case br of λ ()
...   | no  ¬fi  = f p , sym (just-injective br) , ns-passin from p ¬fi
node-inv i e (sVis {at = _ , swap}                           refl br) = case br of λ ()
node-inv i e (sVis {at = _ , yesc}                           refl br) = case br of λ ()
node-inv i e (sVis {at = _ , noc}                            refl br) = case br of λ ()
-- holding node
node-inv i (f (s , r)) (sVis {at = _ , send}                 refl br) = case br of λ ()
node-inv i (f (s , r)) (sVis {at = _ , receive} {a = j , src} refl br) with i Fin.≟ r
... | no  _ = case br of λ ()
... | yes refl with j Fin.≟ i
...   | no  _ = case br of λ ()
...   | yes refl with src Fin.≟ s
...     | no  _ = case br of λ ()
...     | yes refl = e , sym (just-injective br) , ns-recv s
node-inv i (f (s , r)) (sVis {at = _ , pass} {a = from , to , p} refl br) with i Fin.≟ r
... | yes _ = case br of λ ()
... | no ¬ir with from Fin.≟ i
...   | no  _ = case br of λ ()
...   | yes refl with to Fin.≟ r
...     | no  _ = case br of λ ()
...     | yes refl with pkt≟ p (s , r)
...       | no  _ = case br of λ ()
...       | yes refl = e , sym (just-injective br) , ns-passout s r ¬ir
node-inv i (f (s , r)) (sVis {at = _ , swap}                 refl br) = case br of λ ()
node-inv i (f (s , r)) (sVis {at = _ , yesc}                 refl br) = case br of λ ()
node-inv i (f (s , r)) (sVis {at = _ , noc}                  refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §5.3 A measure `μ` on configs: the number of nodes holding a NOT-yet-delivered
-- packet (a packet whose destination is not the current node).  Each hidden `pass`
-- (single-hop delivery) strictly decreases `μ`.
atDest : St → Node → ℕ
atDest e           _ = 0
atDest (f (s , r)) i with r Fin.≟ i
... | yes _ = 0
... | no  _ = 1

μ : St × St × St → ℕ
μ (x , y , z) = atDest x n0 + (atDest y n1 + atDest z n2)

-- `hidden ee` — is the event an internal (hidden) `pass`/`swap`/`yes`/`no`?
hidden : Event → Set
hidden (evLabel _ send    _) = ⊥
hidden (evLabel _ receive _) = ⊥
hidden (evLabel _ pass    _) = ⊤
hidden (evLabel _ swap    _) = ⊤
hidden (evLabel _ yesc    _) = ⊤
hidden (evLabel _ noc     _) = ⊤

------------------------------------------------------------------------------------
-- §5.4 Tail (nodes 1,2) visible-step inversion, naming every observable transition
-- of the tail composite: solo `send`/`receive`, the internal 1↔2 `pass` sync, and
-- the four `pass` half-steps that touch node 0 (solo at the tail, synchronised with
-- node 0 at the top).  Encoding these explicitly lets the top-level inversion refute
-- the node-0-touching half-steps via node 0's alphabet.
data TStep : (St × St) → (St × St) → Event → Set where
  t-send1  : ∀ dst z → TStep (e , z)          (f (n1 , dst) , z)   (sendEv n1 dst)
  t-send2  : ∀ dst y → TStep (y , e)          (y , f (n2 , dst))   (sendEv n2 dst)
  t-recv1  : ∀ s z   → TStep (f (s , n1) , z) (e , z)              (recvEv n1 s)
  t-recv2  : ∀ s y   → TStep (y , f (s , n2)) (y , e)              (recvEv n2 s)
  t-pass12 : ∀ s     → TStep (f (s , n2) , e) (e , f (s , n2))     (passEv n1 n2 (s , n2))
  t-pass21 : ∀ s     → TStep (e , f (s , n1)) (f (s , n1) , e)     (passEv n2 n1 (s , n1))
  t-p1out0 : ∀ s z   → TStep (f (s , n0) , z) (e , z)              (passEv n1 n0 (s , n0))
  t-p1in0  : ∀ p z   → TStep (e , z)          (f p , z)            (passEv n0 n1 p)
  t-p2out0 : ∀ s y   → TStep (y , f (s , n0)) (y , e)              (passEv n2 n0 (s , n0))
  t-p2in0  : ∀ p y   → TStep (y , e)          (y , f p)            (passEv n0 n2 p)

tail-inv : ∀ {t′ ee} y z → Tail y z ─[ ev (evl ee) ]─► t′
         → Σ[ y′ ∈ St ] Σ[ z′ ∈ St ] (t′ ≡ Tail y′ z′ × TStep (y , z) (y′ , z′) ee)
tail-inv y z (sVis feq br) with αpar-vis-step-inv feq br
-- node1 solo (event ∉ B2 = A n2)
... | vSoloL pA ¬pB p1 with node-inv n1 y p1
...   | _ , refl , ns-send dst                             = _ , _ , refl , t-send1 dst z
...   | _ , refl , ns-recv s                               = _ , _ , refl , t-recv1 s z
...   | _ , refl , ns-passin fzero p ¬f1                   = _ , _ , refl , t-p1in0 p z
...   | _ , refl , ns-passin (fsuc fzero) p ¬f1            = ⊥-elim (¬f1 refl)
...   | _ , refl , ns-passin (fsuc (fsuc fzero)) p ¬f1     = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...   | _ , refl , ns-passout s fzero ¬1r                  = _ , _ , refl , t-p1out0 s z
...   | _ , refl , ns-passout s (fsuc fzero) ¬1r           = ⊥-elim (¬1r refl)
...   | _ , refl , ns-passout s (fsuc (fsuc fzero)) ¬1r    = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
-- node2 solo (event ∉ A n1)
tail-inv y z (sVis feq br) | vSoloR ¬pA pB q2 with node-inv n2 z q2
...   | _ , refl , ns-send dst                             = _ , _ , refl , t-send2 dst y
...   | _ , refl , ns-recv s                               = _ , _ , refl , t-recv2 s y
...   | _ , refl , ns-passin fzero p ¬f2                   = _ , _ , refl , t-p2in0 p y
...   | _ , refl , ns-passin (fsuc fzero) p ¬f2            = ⊥-elim (¬pA (inj₁ refl))
...   | _ , refl , ns-passin (fsuc (fsuc fzero)) p ¬f2     = ⊥-elim (¬f2 refl)
...   | _ , refl , ns-passout s fzero ¬2r                  = _ , _ , refl , t-p2out0 s y
...   | _ , refl , ns-passout s (fsuc fzero) ¬2r           = ⊥-elim (¬pA (inj₂ refl))
...   | _ , refl , ns-passout s (fsuc (fsuc fzero)) ¬2r    = ⊥-elim (¬2r refl)
-- node1 ↔ node2 pass sync
tail-inv y z (sVis feq br) | vSync pA pB p1 q2 with node-inv n1 y p1 | node-inv n2 z q2
...   | _ , refl , ns-passout s r ¬1r | _ , refl , ns-passin from p ¬f2 = _ , _ , refl , t-pass12 s
...   | _ , refl , ns-passin from p ¬f1 | _ , refl , ns-passout s r ¬2r = _ , _ , refl , t-pass21 s

------------------------------------------------------------------------------------
-- §5.5 Full composite visible-step inversion: a step of `Sys x y z` is a solo
-- `send`/`receive` or a `pass` sync (node0↔tail).  Returns the successor config and
-- — crucially — the fact that a HIDDEN (`pass`) event strictly decreases `μ`.
sys-inv-vis : ∀ {t′ ee} x y z → Sys x y z ─[ ev (evl ee) ]─► t′
  → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ] Σ[ z′ ∈ St ]
      (t′ ≡ Sys x′ y′ z′ × (hidden ee → μ (x′ , y′ , z′) < μ (x , y , z)))
sys-inv-vis x y z (sVis feq br) with αpar-vis-step-inv feq br
-- (a) node0 solo: only send/receive survive; passes are refuted (they are in B12).
... | vSoloL pA ¬pB p0 with node-inv n0 x p0
...   | _ , refl , ns-send dst                             = f (n0 , dst) , y , z , refl , λ ()
...   | _ , refl , ns-recv s                               = e , y , z , refl , λ ()
...   | _ , refl , ns-passin fzero p ¬f0                   = ⊥-elim (¬f0 refl)
...   | _ , refl , ns-passin (fsuc fzero) p ¬f0            = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...   | _ , refl , ns-passin (fsuc (fsuc fzero)) p ¬f0     = ⊥-elim (¬pB (inj₂ (inj₁ (inj₁ refl))))
...   | _ , refl , ns-passout s fzero ¬0r                  = ⊥-elim (¬0r refl)
...   | _ , refl , ns-passout s (fsuc fzero) ¬0r           = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...   | _ , refl , ns-passout s (fsuc (fsuc fzero)) ¬0r    = ⊥-elim (¬pB (inj₂ (inj₁ (inj₂ refl))))
-- (b) node0 idle, tail steps: send/receive and the internal 1↔2 pass; the four
-- node0-touching half-steps cannot be solo (their event is in A n0).
sys-inv-vis x y z (sVis feq br) | vSoloR ¬pA pB qt with tail-inv y z qt
...   | _ , _ , refl , t-send1 dst _   = x , f (n1 , dst) , z , refl , λ ()
...   | _ , _ , refl , t-send2 dst _   = x , y , f (n2 , dst) , refl , λ ()
...   | _ , _ , refl , t-recv1 s _     = x , e , z , refl , λ ()
...   | _ , _ , refl , t-recv2 s _     = x , y , e , refl , λ ()
...   | _ , _ , refl , t-pass12 s      = x , e , f (s , n2) , refl , λ _ → +-monoʳ-< _ (n<1+n 0)
...   | _ , _ , refl , t-pass21 s      = x , f (s , n1) , e , refl , λ _ → +-monoʳ-< _ (n<1+n 0)
...   | _ , _ , refl , t-p1out0 s _    = ⊥-elim (¬pA (inj₂ refl))
...   | _ , _ , refl , t-p1in0 p _     = ⊥-elim (¬pA (inj₁ refl))
...   | _ , _ , refl , t-p2out0 s _    = ⊥-elim (¬pA (inj₂ refl))
...   | _ , _ , refl , t-p2in0 p _     = ⊥-elim (¬pA (inj₁ refl))
-- (c) node0 ↔ tail pass sync (single-hop delivery): μ strictly decreases.
sys-inv-vis x y z (sVis feq br) | vSync pA pB p0 qt with node-inv n0 x p0 | tail-inv y z qt
...   | _ , refl , ns-passout s r ¬0r  | _ , _ , refl , t-p1in0 p _   = e , f p , z , refl , λ _ → n<1+n _
...   | _ , refl , ns-passout s r ¬0r  | _ , _ , refl , t-p2in0 p _   = e , y , f p , refl , λ _ → n<1+n _
...   | _ , refl , ns-passin from p ¬f0 | _ , _ , refl , t-p1out0 s _ = f p , e , z , refl , λ _ → n<1+n _
...   | _ , refl , ns-passin from p ¬f0 | _ , _ , refl , t-p2out0 s _ = f p , y , e , refl , λ _ → +-monoʳ-< _ (n<1+n 0)

------------------------------------------------------------------------------------
-- §5.6 `Sys c` (a parallel of react-headed STABLE nodes) has NO τ and NO √ step.
sys-noτ : ∀ x y z {t} → Sys x y z ─[ τ ]─► t → ⊥
sys-noτ x y z st with αpar-τ-step-inv st
... | inj₁ (_ , p0τ , _) = noτ n0 x p0τ
... | inj₂ (_ , qτ , _) with αpar-τ-step-inv qτ
...   | inj₁ (_ , p1τ , _) = noτ n1 y p1τ
...   | inj₂ (_ , p2τ , _) = noτ n2 z p2τ

sys-noret : ∀ x y z {r} → Sys x y z .force ≡ ret r → ⊥
sys-noret x y z feq with αpar-√-step-inv feq
... | v√ p0 _ = noret n0 x p0

------------------------------------------------------------------------------------
-- §5.7 De-hiding: `HNetwork` reachability confined to configs; every hidden τ is a
-- single-hop `pass` sync of the underlying `Network` (strictly decreasing `μ`).
open import Data.Nat.Properties using (≤-trans; ≤-pred)

-- `intES` membership of an event coincides with `hidden`.
csat→hidden : ∀ {B} (e : GEv B) (a : B) → intES .mem (B , e) a → hidden (evLabel B e a)
csat→hidden send    a ()
csat→hidden receive a ()
csat→hidden pass    a c = c
csat→hidden swap    a c = c
csat→hidden yesc    a c = c
csat→hidden noc     a c = c

-- A τ-step of `H c` is a hidden `pass` sync landing in a config of strictly smaller `μ`.
Hstep-τ : ∀ x y z {t′} → H x y z ─[ τ ]─► t′
  → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ] Σ[ z′ ∈ St ]
      (t′ ≡ H x′ y′ z′ × μ (x′ , y′ , z′) < μ (x , y , z))
Hstep-τ x y z st with Hide-τ-elim intES (Sys x y z) st
... | hτP P' pτ _ = ⊥-elim (sys-noτ x y z pτ)
... | hτH {e = ge} {a = a} P' csat pstep refl with sys-inv-vis x y z pstep
...   | x′ , y′ , z′ , refl , fμ = x′ , y′ , z′ , refl , fμ (csat→hidden ge a csat)

-- A visible (`send`/`receive`) step of `H c` lands in a config.
Hstep-ev : ∀ x y z {e t′} → H x y z ─[ ev (evl e) ]─► t′
  → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ] Σ[ z′ ∈ St ] (t′ ≡ H x′ y′ z′)
Hstep-ev x y z st with Hide-ev-elim intES (Sys x y z) st
... | heV P' ¬csat pstep with sys-inv-vis x y z pstep
...   | x′ , y′ , z′ , refl , _ = x′ , y′ , z′ , refl

------------------------------------------------------------------------------------
-- §5.8 No config diverges: well-founded recursion on the measure `μ`.
¬div-bnd : ∀ n x y z → μ (x , y , z) < n → ¬ Diverges (H x y z)
¬div-bnd (suc n) x y z μ<sn d with Hstep-τ x y z (d .Diverges.step)
... | x′ , y′ , z′ , eq , μ′<μ =
      ¬div-bnd n x′ y′ z′ (≤-trans μ′<μ (≤-pred μ<sn)) (subst Diverges eq (d .Diverges.rest))

¬div : ∀ x y z → ¬ Diverges (H x y z)
¬div x y z = ¬div-bnd (suc (μ (x , y , z))) x y z (n<1+n _)

------------------------------------------------------------------------------------
-- §5.9 Every √-free-reachable state of `HNetwork` is a config; hence divergence-free.
reach-cons : ∀ {s t′} → HNetwork ⟹∖√⟨ s ⟩ t′
           → Σ[ x ∈ St ] Σ[ y ∈ St ] Σ[ z ∈ St ] (t′ ≡ H x y z)
reach-cons = go e e e refl
  where
  go : ∀ {s t t′} x y z → t ≡ H x y z → t ⟹∖√⟨ s ⟩ t′
     → Σ[ u ∈ St ] Σ[ v ∈ St ] Σ[ w ∈ St ] (t′ ≡ H u v w)
  go x y z refl ∖√-refl         = x , y , z , refl
  go x y z refl (∖√-τ  st rest) with Hstep-τ x y z st
  ... | x′ , y′ , z′ , refl , _ = go x′ y′ z′ refl rest
  go x y z refl (∖√-ev st rest) with Hstep-ev x y z st
  ... | x′ , y′ , z′ , refl     = go x′ y′ z′ refl rest

general4-divergenceFree : DivergenceFree HNetwork
general4-divergenceFree reach div with reach-cons reach
... | x , y , z , refl = ¬div x y z div
