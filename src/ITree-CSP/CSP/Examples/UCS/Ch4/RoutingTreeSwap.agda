{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2.1: the SWAP store-and-forward routing *tree* is
-- DEADLOCK-FREE — the deadlock-free counterpart of the naive tree
-- (`RoutingTreeNaive`, which deadlocks by strong conflict).  Machine-readable
-- companion file:
--
--   fdr-examples/ucs/chapter04/tree2.csp   (UCS ch. 4 §4.2.1, the swap tree)
--
-- The naive tree deadlocks because two adjacent nodes, each holding a packet
-- destined *through* the other, form a STRONG CONFLICT: each offers only its
-- forwarding `pass.i.j`, and the intended recipient (also full, offering no
-- `pass` input) declines.  The swap network adds an EXCHANGE channel `swap`
-- letting two adjacent full nodes trade packets instead of deadlocking.  Per
-- `tree2.csp` (i ≠ r, j = next i r):
--
--   NodeE2 i        = send.i?dst → NodeF2 i (i,dst)
--                     □ pass?(j∈nbrs i).i?p → NodeF2 i p
--   NodeF2 i (s,r)  = if i≡r then receive.i.s → NodeE2 i
--                     else ( pass.i.j.(s,r) → NodeE2 i
--                          □ (swap.i.j.(s,r) → swap.j.i?p′ → NodeF2 i p′)
--                          □ (swap.j.i?p′ → swap.i.j.(s,r) → NodeF2 i p′) )
--
-- The two swap branches are the symmetric two-phase handshake: node i may go
-- FIRST (send its packet `swap.i.j.(s,r)`, then receive the neighbour's
-- `swap.j.i?p′`) or SECOND (receive `swap.j.i?p′` first, then send its own).
-- Because both branches are offered simultaneously, whichever adjacent node
-- "wins the race" the exchange completes — the strong conflict is broken.
--
-- ────────────────────────────────────────────────────────────────────────────
-- ⚠  TREE-REDUCTION (documented per the task spec).  A faithful (packet-PINNED)
-- DeadlockFree proof at the full N = 5 book tree is a value-level reachable-
-- config enumeration whose state space is astronomically large: every NodeF2
-- pins a specific packet from Node×Node, and the swap handshake adds two more
-- intermediate position classes per node.  The non-blocking RING companion
-- (`RoutingRingNonBlocking`) reached only N = 2 for the same reason, and the
-- swap two-phase handshake is strictly harder.  This module therefore proves
-- the swap-resolves-strong-conflict property at the SMALLEST tree that still
-- exhibits it: a **2-node edge** `0 — 1`.  Two adjacent full nodes each holding
-- a packet for the other are exactly the strong-conflict pair; `swap` lets them
-- exchange, and no reachable configuration is stuck.  Because the shared Task-1
-- scaffold (`RoutingTreeNaive`) is fixed at `Node = Fin 5`, the N = 2 instance
-- is a SELF-CONTAINED re-derivation of the scaffold (`Node = Fin 2`, its own
-- `TEv`/`TEv-≟`/`A`/`other`), not an import.
--
-- FAITHFULNESS (the load-bearing point for a *universal* DeadlockFree claim):
-- the forwards / swap-outputs are PINNED, NOT payload-discarded.  `NodeF2 i (s,r)`
-- forwards / swap-outputs the SPECIFIC held packet `(s,r)` toward `other i`
-- (see the `pkt≟ p (s,r)` guards); the swap-INPUT `swap.j.i?p′` accepts any
-- packet (a genuine `?` input), as does the `pass?…?p` / `send?dst` inputs.  An
-- over-approximated (payload-generalised output) model would be UNSOUND: it
-- could exhibit progress the real tree lacks.
--
-- PROOF APPROACH.  Every node is react-headed and STABLE (τ-map ≡ ∅t): no node
-- has a τ or √ transition, so the composite's only moves are VISIBLE (a solo
-- send/receive, or a pass/swap SYNC between the two adjacent nodes).  We track
-- each node by its reachable POSITION CLASS (empty NodeE2 / holding NodeF2 /
-- swap-phase-1 NodeSw1 / swap-phase-2 NodeSw2) and carry a joint reachability
-- predicate `TSys` with SIX constructors — the reachable occupancy pairs
-- (E,E), (F,E), (E,F), (F,F), plus the two paired handshake states (Sw1,Sw2)
-- and (Sw2,Sw1).  Handshake states are ALWAYS paired: a `swap` sync moves both
-- nodes in one step, so a lone NodeSw1 is unreachable.  `TSys` is closed under
-- stepping (`sys-inv`) and every `TSys` state can move (`enabled`): an empty
-- node sends, a node at its destination receives, and two full forwarding nodes
-- (the strong conflict) `swap`.  `Progress` and `DeadlockFree` follow.

module CSP.Examples.UCS.Ch4.RoutingTreeSwap where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. Node type and 2-node edge topology.
Node : Set
Node = Fin 2

n0 n1 : Node
n0 = fzero
n1 = fsuc fzero

-- The single neighbour of each node (the edge 0—1); doubles as `next i r` for the
-- unique tree path (there is only one other node to forward toward).
other : Node → Node
other fzero        = n1
other (fsuc fzero) = n0

-- Adjacency table (documentation / faithfulness; the offer maps use `other`).
nbrs : Node → List Node
nbrs fzero        = n1 ∷ []
nbrs (fsuc fzero) = n0 ∷ []

------------------------------------------------------------------------------------
-- §2. The event type and its decidable equality.
data TEv : Set → Set where
  send    : TEv (Node × Node)                    -- send.i.dst      : (i , dst)
  receive : TEv (Node × Node)                    -- receive.i.src   : (i , src)
  pass    : TEv (Node × (Node × (Node × Node)))  -- pass.i.j.(s,r)  : (i , (j , (s , r)))
  swap    : TEv (Node × (Node × (Node × Node)))  -- swap.i.j.(s,r)  : (i , (j , (s , r)))

TEv-≟ : (x y : AnyTypes TEv) → Dec (x ≡ y)
TEv-≟ (_ , send)    (_ , send)    = yes refl
TEv-≟ (_ , receive) (_ , receive) = yes refl
TEv-≟ (_ , pass)    (_ , pass)    = yes refl
TEv-≟ (_ , swap)    (_ , swap)    = yes refl
TEv-≟ (_ , send)    (_ , receive) = no (λ ())
TEv-≟ (_ , send)    (_ , pass)    = no (λ ())
TEv-≟ (_ , send)    (_ , swap)    = no (λ ())
TEv-≟ (_ , receive) (_ , send)    = no (λ ())
TEv-≟ (_ , receive) (_ , pass)    = no (λ ())
TEv-≟ (_ , receive) (_ , swap)    = no (λ ())
TEv-≟ (_ , pass)    (_ , send)    = no (λ ())
TEv-≟ (_ , pass)    (_ , receive) = no (λ ())
TEv-≟ (_ , pass)    (_ , swap)    = no (λ ())
TEv-≟ (_ , swap)    (_ , send)    = no (λ ())
TEv-≟ (_ , swap)    (_ , receive) = no (λ ())
TEv-≟ (_ , swap)    (_ , pass)    = no (λ ())

-- decidable equality on packets `Node × Node`
pkt≟ : (p q : Node × Node) → Dec (p ≡ q)
pkt≟ = ×-≡-dec Fin._≟_ Fin._≟_

open import CSP.Operators TEv-≟
open EventSet

------------------------------------------------------------------------------------
-- §3. Per-node alphabets.  Node i owns send.i, receive.i, and every pass/swap
-- endpoint it touches: a pass/swap.from.to belongs to A i iff i is sender or
-- receiver.  So send/receive fire SOLO; each pass.i.j / swap.i.j synchronises the
-- two adjacent nodes it connects.
A : Node → EventSet
A i .mem (_ , send)    (j , _)         = j ≡ i
A i .mem (_ , receive) (j , _)         = j ≡ i
A i .mem (_ , pass)    (from , to , _) = (from ≡ i) ⊎ (to ≡ i)
A i .mem (_ , swap)    (from , to , _) = (from ≡ i) ⊎ (to ≡ i)
A i .dec (_ , send)    (j , _)         = j Fin.≟ i
A i .dec (_ , receive) (j , _)         = j Fin.≟ i
A i .dec (_ , pass)    (from , to , _) = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)
A i .dec (_ , swap)    (from , to , _) = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)

------------------------------------------------------------------------------------
-- §4. The swap node and the tree.  Corecursive loop written as inlined `react`
-- copatterns (corecursive calls sit directly under `just`); τ-branch ≡ ∅t
-- throughout (every position is STABLE).
--
--   NodeE2 i           empty
--   NodeF2 i (s,r)     holding packet (s,r)  (destination if i≡r, else forwarding)
--   NodeSw1 i          swap phase 1: sent its packet, waiting for neighbour's
--   NodeSw2 i (s,r) p  swap phase 2: received p, still owes its (s,r) to neighbour
DProcT : Set₁
DProcT = PTree TEv (ExtI TEv) (⊤poly {lzero})

NodeE2  : Node → DProcT
NodeF2  : Node → (Node × Node) → DProcT
NodeSw1 : Node → DProcT
NodeSw2 : Node → (Node × Node) → (Node × Node) → DProcT

force (NodeE2 i) = react
  (λ where
     (_ , send)    (j , dst)       → case j Fin.≟ i of λ where
         (yes _) → just (NodeF2 i (i , dst))
         (no  _) → nothing
     (_ , receive) _               → nothing
     (_ , pass)    (from , to , p) → case to Fin.≟ i of λ where
         (yes _) → case from Fin.≟ other i of λ where
             (yes _) → just (NodeF2 i p)      -- accept a packet passed in from neighbour
             (no  _) → nothing
         (no  _) → nothing
     (_ , swap)    _               → nothing) -- empty node does not swap
  ∅t

force (NodeF2 i (s , r)) = react
  (λ where
     (_ , send)    _               → nothing
     (_ , receive) (j , src)       → case i Fin.≟ r of λ where
         (yes _) → case j Fin.≟ i of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → just (NodeE2 i)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , pass)    (from , to , p) → case i Fin.≟ r of λ where
         (yes _) → nothing                    -- destination: no forwarding
         (no  _) → case from Fin.≟ i of λ where
             (yes _) → case to Fin.≟ other i of λ where
                 (yes _) → case pkt≟ p (s , r) of λ where
                     (yes _) → just (NodeE2 i)          -- forward the held packet
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
     (_ , swap)    (from , to , p) → case i Fin.≟ r of λ where
         (yes _) → nothing                    -- destination: no swapping
         (no  _) → case from Fin.≟ i of λ where
             (yes _) → case to Fin.≟ other i of λ where      -- OUTPUT swap.i.(other i).(s,r)
                 (yes _) → case pkt≟ p (s , r) of λ where
                     (yes _) → just (NodeSw1 i)
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → case from Fin.≟ other i of λ where     -- INPUT swap.(other i).i?p
                 (yes _) → case to Fin.≟ i of λ where
                     (yes _) → just (NodeSw2 i (s , r) p)
                     (no  _) → nothing
                 (no  _) → nothing)
  ∅t

force (NodeSw1 i) = react
  (λ where
     (_ , send)    _               → nothing
     (_ , receive) _               → nothing
     (_ , pass)    _               → nothing
     (_ , swap)    (from , to , p) → case from Fin.≟ other i of λ where  -- INPUT swap.(other i).i?p
         (yes _) → case to Fin.≟ i of λ where
             (yes _) → just (NodeF2 i p)
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

force (NodeSw2 i (s , r) q) = react
  (λ where
     (_ , send)    _               → nothing
     (_ , receive) _               → nothing
     (_ , pass)    _               → nothing
     (_ , swap)    (from , to , p) → case from Fin.≟ i of λ where       -- OUTPUT swap.i.(other i).(s,r)
         (yes _) → case to Fin.≟ other i of λ where
             (yes _) → case pkt≟ p (s , r) of λ where
                 (yes _) → just (NodeF2 i q)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

swapNode : Node → Comp TEv (⊤poly {lzero})
swapNode i = comp (A i) (NodeE2 i)

swapTree : PTree TEv (ExtI TEv) (RetOf⁺ (swapNode n0) (swapNode n1 ∷ []))
swapTree = ∥ₐ⁺ (swapNode n0) (swapNode n1 ∷ [])

------------------------------------------------------------------------------------
-- §5. Verification machinery.
open import Semantics.LTS      {E = TEv} {I = ExtI TEv}
open import Semantics.Failures {E = TEv} {I = ExtI TEv} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = TEv} {I = ExtI TEv}
  using ( IsStuck; DeadlockFree; _⟹∖√⟨_⟩_; embed∖√ )
open import Semantics.DeadlockDR {E = TEv} {I = ExtI TEv}
  using ( Progress; progress⇒deadlockFree )
open import CSP.Laws.AlphaParallel TEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

-- The right-hand alphabet (the folded singleton tail) and the composite state.
B1 : EventSet
B1 = unionα (swapNode n1 ∷ [])

Sys : DProcT → DProcT → PTree TEv (ExtI TEv) (RetOf⁺ (swapNode n0) (swapNode n1 ∷ []))
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

tree≡ : swapTree ≡ Sys (NodeE2 n0) (NodeE2 n1)
tree≡ = refl

-- R-independent event labels.
sendEv : Node → Node → Event
sendEv i d = evLabel (Node × Node) send (i , d)
recvEv : Node → Node → Event
recvEv i s = evLabel (Node × Node) receive (i , s)
passEv : Node → Node → (Node × Node) → Event
passEv f t p = evLabel (Node × (Node × (Node × Node))) pass (f , (t , p))
swapEv : Node → Node → (Node × Node) → Event
swapEv f t p = evLabel (Node × (Node × (Node × Node))) swap (f , (t , p))

------------------------------------------------------------------------------------
-- §5.1 Node state TAGS (data), decoded to processes by ⟦_⟧.  Indexing the invariant
-- by these DATA tags rather than the raw process terms is essential: `NodeE2 n0` and
-- `NodeF2 n0 p` are distinct DEFINED terms that Agda's unifier cannot tell apart
-- (definitions are not injective), whereas the tag constructors `e0`/`f0 p` ARE
-- disjoint, so the closure proof can case-split node states.
data S0 : Set where
  e0   : S0
  f0   : (Node × Node) → S0
  sw10 : S0
  sw20 : (Node × Node) → (Node × Node) → S0
data S1 : Set where
  e1   : S1
  f1   : (Node × Node) → S1
  sw11 : S1
  sw21 : (Node × Node) → (Node × Node) → S1

⟦_⟧0 : S0 → DProcT
⟦ e0 ⟧0       = NodeE2 n0
⟦ f0 p ⟧0     = NodeF2 n0 p
⟦ sw10 ⟧0     = NodeSw1 n0
⟦ sw20 o c ⟧0 = NodeSw2 n0 o c
⟦_⟧1 : S1 → DProcT
⟦ e1 ⟧1       = NodeE2 n1
⟦ f1 p ⟧1     = NodeF2 n1 p
⟦ sw11 ⟧1     = NodeSw1 n1
⟦ sw21 o c ⟧1 = NodeSw2 n1 o c

-- Every node is react-headed (never `ret`) and stable (τ-map ≡ ∅t), so no τ/√ step.
noret0 : ∀ (x : S0) {r} → ⟦ x ⟧0 .force ≡ ret r → ⊥
noret0 e0 () ; noret0 (f0 (s , r)) () ; noret0 sw10 () ; noret0 (sw20 (s , r) c) ()
noτ0 : ∀ (x : S0) {t′} → ⟦ x ⟧0 ─[ τ ]─► t′ → ⊥
noτ0 e0            (sSil eq)      = case eq of λ ()
noτ0 e0            (sTau refl br) = case br of λ ()
noτ0 (f0 (s , r))    (sSil eq)      = case eq of λ ()
noτ0 (f0 (s , r))    (sTau refl br) = case br of λ ()
noτ0 sw10          (sSil eq)      = case eq of λ ()
noτ0 sw10          (sTau refl br) = case br of λ ()
noτ0 (sw20 (s , r) c)(sSil eq)      = case eq of λ ()
noτ0 (sw20 (s , r) c)(sTau refl br) = case br of λ ()
noτ1 : ∀ (y : S1) {t′} → ⟦ y ⟧1 ─[ τ ]─► t′ → ⊥
noτ1 e1            (sSil eq)      = case eq of λ ()
noτ1 e1            (sTau refl br) = case br of λ ()
noτ1 (f1 (s , r))    (sSil eq)      = case eq of λ ()
noτ1 (f1 (s , r))    (sTau refl br) = case br of λ ()
noτ1 sw11          (sSil eq)      = case eq of λ ()
noτ1 sw11          (sTau refl br) = case br of λ ()
noτ1 (sw21 (s , r) c)(sSil eq)      = case eq of λ ()
noτ1 (sw21 (s , r) c)(sTau refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §5.2 Per-node visible-step transition relations over the state TAGS.  Forward /
-- swap-OUTPUT constructors keep the recorded event value general (the offer-map
-- `pkt≟` / `src≟` guards in §4 PIN them to the held packet, but the closure proof
-- never needs that value); the swap-/pass-INPUT constructors are genuine `?` inputs.
data T0 : S0 → S0 → Event → Set₁ where
  t0-send    : ∀ dst     → T0 e0 (f0 (n0 , dst))            (sendEv n0 dst)
  t0-passin  : ∀ p       → T0 e0 (f0 p)                     (passEv n1 n0 p)
  t0-recv    : ∀ s src   → T0 (f0 (s , n0)) e0              (recvEv n0 src)
  t0-passout : ∀ s p     → T0 (f0 (s , n1)) e0              (passEv n0 n1 p)
  t0-swapout : ∀ s p     → T0 (f0 (s , n1)) sw10            (swapEv n0 n1 p)
  t0-swapin  : ∀ s p     → T0 (f0 (s , n1)) (sw20 (s , n1) p) (swapEv n1 n0 p)
  t0-sw1in   : ∀ p       → T0 sw10 (f0 p)                   (swapEv n1 n0 p)
  t0-sw2out  : ∀ s r q p → T0 (sw20 (s , r) q) (f0 q)       (swapEv n0 n1 p)

data T1 : S1 → S1 → Event → Set₁ where
  t1-send    : ∀ dst     → T1 e1 (f1 (n1 , dst))            (sendEv n1 dst)
  t1-passin  : ∀ p       → T1 e1 (f1 p)                     (passEv n0 n1 p)
  t1-recv    : ∀ s src   → T1 (f1 (s , n1)) e1              (recvEv n1 src)
  t1-passout : ∀ s p     → T1 (f1 (s , n0)) e1              (passEv n1 n0 p)
  t1-swapout : ∀ s p     → T1 (f1 (s , n0)) sw11            (swapEv n1 n0 p)
  t1-swapin  : ∀ s p     → T1 (f1 (s , n0)) (sw21 (s , n0) p) (swapEv n0 n1 p)
  t1-sw1in   : ∀ p       → T1 sw11 (f1 p)                   (swapEv n0 n1 p)
  t1-sw2out  : ∀ s r q p → T1 (sw21 (s , r) q) (f1 q)       (swapEv n1 n0 p)

-- node0 visible-step inversion: a visible step of ⟦ x ⟧0 lands in some tag x′ and is a T0.
n0-inv : ∀ {t′ e} (x : S0) → ⟦ x ⟧0 ─[ ev (evl e) ]─► t′
       → Σ[ x′ ∈ S0 ] (t′ ≡ ⟦ x′ ⟧0 × T0 x x′ e)
n0-inv e0 (sVis {at = _ , send} {a = fzero , dst}      refl br) = f0 (n0 , dst) , sym (just-injective br) , t0-send dst
n0-inv e0 (sVis {at = _ , send} {a = fsuc fzero , dst} refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , receive}                     refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , pass} {a = fzero , fzero , p}           refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , pass} {a = fsuc fzero , fzero , p}      refl br) = f0 p , sym (just-injective br) , t0-passin p
n0-inv e0 (sVis {at = _ , pass} {a = fzero , fsuc fzero , p}      refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , swap}                        refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , receive} {a = fzero , src}      refl br) with src Fin.≟ s
... | yes _ = e0 , sym (just-injective br) , t0-recv s src
... | no  _ = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , swap} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , pass} {a = fzero , fsuc fzero , p} refl br) with pkt≟ p (s , n1)
... | yes _ = e0 , sym (just-injective br) , t0-passout s p
... | no  _ = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , pass} {a = fzero , fzero , p}      refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , pass} {a = fsuc fzero , to , p}    refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , swap} {a = fzero , fsuc fzero , p} refl br) with pkt≟ p (s , n1)
... | yes _ = sw10 , sym (just-injective br) , t0-swapout s p
... | no  _ = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , swap} {a = fzero , fzero , p}           refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , swap} {a = fsuc fzero , fzero , p}      refl br) = sw20 (s , n1) p , sym (just-injective br) , t0-swapin s p
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , swap} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n0-inv sw10 (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv sw10 (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv sw10 (sVis {at = _ , pass} refl br) = case br of λ ()
n0-inv sw10 (sVis {at = _ , swap} {a = fsuc fzero , fzero , p}      refl br) = f0 p , sym (just-injective br) , t0-sw1in p
n0-inv sw10 (sVis {at = _ , swap} {a = fzero , to , p}             refl br) = case br of λ ()
n0-inv sw10 (sVis {at = _ , swap} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , pass} refl br) = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , swap} {a = fzero , fsuc fzero , p} refl br) with pkt≟ p (s , r)
... | yes _ = f0 q , sym (just-injective br) , t0-sw2out s r q p
... | no  _ = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , swap} {a = fzero , fzero , p}   refl br) = case br of λ ()
n0-inv (sw20 (s , r) q) (sVis {at = _ , swap} {a = fsuc fzero , to , p} refl br) = case br of λ ()

-- node1 visible-step inversion (i = n1 = fsuc fzero; other n1 = n0 = fzero).
n1-inv : ∀ {t′ e} (y : S1) → ⟦ y ⟧1 ─[ ev (evl e) ]─► t′
       → Σ[ y′ ∈ S1 ] (t′ ≡ ⟦ y′ ⟧1 × T1 y y′ e)
n1-inv e1 (sVis {at = _ , send} {a = fsuc fzero , dst} refl br) = f1 (n1 , dst) , sym (just-injective br) , t1-send dst
n1-inv e1 (sVis {at = _ , send} {a = fzero , dst}      refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , receive}                     refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , pass} {a = fzero , fsuc fzero , p}      refl br) = f1 p , sym (just-injective br) , t1-passin p
n1-inv e1 (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , pass} {a = fzero , fzero , p}           refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , pass} {a = fsuc fzero , fzero , p}      refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , swap}                        refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) with src Fin.≟ s
... | yes _ = e1 , sym (just-injective br) , t1-recv s src
... | no  _ = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , receive} {a = fzero , src} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , swap} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , pass} {a = fsuc fzero , fzero , p} refl br) with pkt≟ p (s , n0)
... | yes _ = e1 , sym (just-injective br) , t1-passout s p
... | no  _ = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , pass} {a = fzero , to , p}             refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , swap} {a = fsuc fzero , fzero , p} refl br) with pkt≟ p (s , n0)
... | yes _ = sw11 , sym (just-injective br) , t1-swapout s p
... | no  _ = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , swap} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , swap} {a = fzero , fsuc fzero , p} refl br) = sw21 (s , n0) p , sym (just-injective br) , t1-swapin s p
n1-inv (f1 (s , fzero)) (sVis {at = _ , swap} {a = fzero , fzero , p}      refl br) = case br of λ ()
n1-inv sw11 (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv sw11 (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv sw11 (sVis {at = _ , pass} refl br) = case br of λ ()
n1-inv sw11 (sVis {at = _ , swap} {a = fzero , fsuc fzero , p}    refl br) = f1 p , sym (just-injective br) , t1-sw1in p
n1-inv sw11 (sVis {at = _ , swap} {a = fzero , fzero , p}         refl br) = case br of λ ()
n1-inv sw11 (sVis {at = _ , swap} {a = fsuc fzero , to , p}       refl br) = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , pass} refl br) = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , swap} {a = fsuc fzero , fzero , p} refl br) with pkt≟ p (s , r)
... | yes _ = f1 q , sym (just-injective br) , t1-sw2out s r q p
... | no  _ = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , swap} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n1-inv (sw21 (s , r) q) (sVis {at = _ , swap} {a = fzero , to , p}              refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §5.3 The joint reachability predicate over the state tags: the SIX reachable
-- occupancy pairs.  Handshake pairs (sw10,sw21)/(sw20,sw11) are always PAIRED — a lone
-- swap-state is unreachable (a `swap` sync moves both operands in one step).
data Reach : S0 → S1 → Set where
  rEE  :             Reach e0            e1
  rFE  : ∀ p       → Reach (f0 p)        e1
  rEF  : ∀ p       → Reach e0            (f1 p)
  rFF  : ∀ p q     → Reach (f0 p)        (f1 q)
  rS12 : ∀ o c     → Reach sw10          (sw21 o c)
  rS21 : ∀ o c     → Reach (sw20 o c)    sw11

Sys⟦_,_⟧ : S0 → S1 → PTree TEv (ExtI TEv) (RetOf⁺ (swapNode n0) (swapNode n1 ∷ []))
Sys⟦ x , y ⟧ = Sys ⟦ x ⟧0 ⟦ y ⟧1

------------------------------------------------------------------------------------
-- §5.4 System single-step inversion: Reach is closed under stepping.  τ/√ are
-- impossible; a visible step routes as a solo send/receive or a pass/swap SYNC.  The
-- helpers keep `reach` abstract while the αpar inversion runs, then case-split it (a
-- DATA match on tag constructors) to PIN both node states.
soloL : ∀ {x y t0′} {X} {ee : TEv X} {a : X}
      → Reach x y → ¬ (B1 .mem (X , ee) a)
      → ⟦ x ⟧0 ─[ ev (evl (evLabel X ee a)) ]─► t0′
      → Σ[ x′ ∈ S0 ] Σ[ y′ ∈ S1 ] (Sys t0′ ⟦ y ⟧1 ≡ Sys⟦ x′ , y′ ⟧ × Reach x′ y′)
soloL {x} reach ¬pB p0 with n0-inv x p0
... | _ , refl , t0-send dst with reach
...   | rEE   = _ , _ , refl , rFE (n0 , dst)
...   | rEF q = _ , _ , refl , rFF (n0 , dst) q
soloL reach ¬pB p0 | _ , refl , t0-recv s src with reach
...   | rFE p   = _ , _ , refl , rEE
...   | rFF p q = _ , _ , refl , rEF q
soloL reach ¬pB p0 | _ , refl , t0-passin p       = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-passout s p    = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
soloL reach ¬pB p0 | _ , refl , t0-swapout s p    = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
soloL reach ¬pB p0 | _ , refl , t0-swapin s p     = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-sw1in p        = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-sw2out s r q p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))

soloR : ∀ {x y t1′} {X} {ee : TEv X} {a : X}
      → Reach x y → ¬ (A n0 .mem (X , ee) a)
      → ⟦ y ⟧1 ─[ ev (evl (evLabel X ee a)) ]─► t1′
      → Σ[ x′ ∈ S0 ] Σ[ y′ ∈ S1 ] (Sys ⟦ x ⟧0 t1′ ≡ Sys⟦ x′ , y′ ⟧ × Reach x′ y′)
soloR {x} {y} reach ¬pA q1 with n1-inv y q1
... | _ , refl , t1-send dst with reach
...   | rEE   = _ , _ , refl , rEF (n1 , dst)
...   | rFE p = _ , _ , refl , rFF p (n1 , dst)
soloR reach ¬pA q1 | _ , refl , t1-recv s src with reach
...   | rEF q   = _ , _ , refl , rEE
...   | rFF p q = _ , _ , refl , rFE p
soloR reach ¬pA q1 | _ , refl , t1-passin p       = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-passout s p    = ⊥-elim (¬pA (inj₂ refl))
soloR reach ¬pA q1 | _ , refl , t1-swapout s p    = ⊥-elim (¬pA (inj₂ refl))
soloR reach ¬pA q1 | _ , refl , t1-swapin s p     = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-sw1in p        = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-sw2out s r q p = ⊥-elim (¬pA (inj₂ refl))

sync : ∀ {x y t0′ t1′} {X} {ee : TEv X} {a : X}
     → Reach x y
     → ⟦ x ⟧0 ─[ ev (evl (evLabel X ee a)) ]─► t0′
     → ⟦ y ⟧1 ─[ ev (evl (evLabel X ee a)) ]─► t1′
     → Σ[ x′ ∈ S0 ] Σ[ y′ ∈ S1 ] (Sys t0′ t1′ ≡ Sys⟦ x′ , y′ ⟧ × Reach x′ y′)
sync {x} {y} reach p0 q1 with n0-inv x p0 | n1-inv y q1
... | _ , refl , t0-passout s p′    | _ , refl , t1-passin p″        = _ , _ , refl , rEF p′
... | _ , refl , t0-passin p′       | _ , refl , t1-passout s p″     = _ , _ , refl , rFE p′
... | _ , refl , t0-swapout s p′    | _ , refl , t1-swapin s′ p″     = _ , _ , refl , rS12 (s′ , n0) p′
... | _ , refl , t0-swapout s p′    | _ , refl , t1-sw1in p″         = case reach of λ ()
... | _ , refl , t0-sw2out s r q p′ | _ , refl , t1-swapin s′ p″     = case reach of λ ()
... | _ , refl , t0-sw2out s r q p′ | _ , refl , t1-sw1in p″         = _ , _ , refl , rFF q p″
... | _ , refl , t0-swapin s p′     | _ , refl , t1-swapout s′ p″    = _ , _ , refl , rS21 (s , n1) p′
... | _ , refl , t0-swapin s p′     | _ , refl , t1-sw2out s′ r′ q′ p″ = case reach of λ ()
... | _ , refl , t0-sw1in p′        | _ , refl , t1-swapout s′ p″    = case reach of λ ()
... | _ , refl , t0-sw1in p′        | _ , refl , t1-sw2out s′ r′ q′ p″ = _ , _ , refl , rFF p′ q′

sys-inv : ∀ {x y l t′} → Reach x y → Sys⟦ x , y ⟧ ─[ l ]─► t′
        → Σ[ x′ ∈ S0 ] Σ[ y′ ∈ S1 ] (t′ ≡ Sys⟦ x′ , y′ ⟧ × Reach x′ y′)
sys-inv {x} reach (sRet feq) with αpar-√-step-inv feq
... | v√ p0 _ = ⊥-elim (noret0 x p0)
sys-inv {x} {y} reach (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (_ , pτ , _) = ⊥-elim (noτ0 x pτ)
... | inj₂ (_ , qτ , _) = ⊥-elim (noτ1 y qτ)
sys-inv {x} {y} reach (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (_ , pτ , _) = ⊥-elim (noτ0 x pτ)
... | inj₂ (_ , qτ , _) = ⊥-elim (noτ1 y qτ)
sys-inv reach (sVis feq br) with αpar-vis-step-inv feq br
... | vSoloL pA ¬pB p0  = soloL reach ¬pB p0
... | vSoloR ¬pA pB q1  = soloR reach ¬pA q1
... | vSync pA pB p0 q1 = sync reach p0 q1

------------------------------------------------------------------------------------
-- §5.5 Reachability closure: every ⟹-reachable state is a reachable Reach config.
tree≡′ : swapTree ≡ Sys⟦ e0 , e1 ⟧
tree≡′ = refl

reach-cons : ∀ {s t′} → swapTree ⟹⟨ s ⟩ t′
           → Σ[ x ∈ S0 ] Σ[ y ∈ S1 ] (t′ ≡ Sys⟦ x , y ⟧ × Reach x y)
reach-cons = go rEE refl
  where
    go : ∀ {x y t s t′} → Reach x y → t ≡ Sys⟦ x , y ⟧ → t ⟹⟨ s ⟩ t′
       → Σ[ u ∈ S0 ] Σ[ v ∈ S1 ] (t′ ≡ Sys⟦ u , v ⟧ × Reach u v)
    go reach refl ⟹-refl         = _ , _ , refl , reach
    go reach refl (⟹-τ  st rest) = let (_ , _ , eq , reach′) = sys-inv reach st in go reach′ eq rest
    go reach refl (⟹-ev st rest) = let (_ , _ , eq , reach′) = sys-inv reach st in go reach′ eq rest

------------------------------------------------------------------------------------
-- §5.6 Every reachable configuration can MOVE.  Step helpers split the Fin-2 packet
-- components so the offer maps' `src≟` / `pkt≟` guards reduce definitionally.
step-recv0 : ∀ s → NodeF2 n0 (s , n0) ─[ ev (evl (recvEv n0 s)) ]─► NodeE2 n0
step-recv0 fzero        = sVis refl refl
step-recv0 (fsuc fzero) = sVis refl refl
step-recv1 : ∀ s → NodeF2 n1 (s , n1) ─[ ev (evl (recvEv n1 s)) ]─► NodeE2 n1
step-recv1 fzero        = sVis refl refl
step-recv1 (fsuc fzero) = sVis refl refl
step-swapOut0 : ∀ s → NodeF2 n0 (s , n1) ─[ ev (evl (swapEv n0 n1 (s , n1))) ]─► NodeSw1 n0
step-swapOut0 fzero        = sVis refl refl
step-swapOut0 (fsuc fzero) = sVis refl refl
step-swapOut1 : ∀ o c → NodeSw2 n1 o c ─[ ev (evl (swapEv n1 n0 o)) ]─► NodeF2 n1 c
step-swapOut1 (fzero , fzero)           c = sVis refl refl
step-swapOut1 (fzero , fsuc fzero)      c = sVis refl refl
step-swapOut1 (fsuc fzero , fzero)      c = sVis refl refl
step-swapOut1 (fsuc fzero , fsuc fzero) c = sVis refl refl
step-swapOut0S2 : ∀ o c → NodeSw2 n0 o c ─[ ev (evl (swapEv n0 n1 o)) ]─► NodeF2 n0 c
step-swapOut0S2 (fzero , fzero)           c = sVis refl refl
step-swapOut0S2 (fzero , fsuc fzero)      c = sVis refl refl
step-swapOut0S2 (fsuc fzero , fzero)      c = sVis refl refl
step-swapOut0S2 (fsuc fzero , fsuc fzero) c = sVis refl refl

enabled : ∀ {x y} → Reach x y
        → Σ[ l ∈ Label (RetOf⁺ (swapNode n0) (swapNode n1 ∷ [])) ] Σ[ t″ ∈ _ ] (Sys⟦ x , y ⟧ ─[ l ]─► t″)
-- an empty node sends solo.
enabled rEE           = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
enabled (rFE (s , r)) = _ , _ , αpar-soloR-step {at = _ , send} {a = n1 , n0} (λ ()) (inj₁ refl) refl refl refl
enabled (rEF (s , r)) = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
-- (F,F): a node at its destination delivers; two forwarders SWAP (breaks strong conflict).
enabled (rFF (s , fzero) (qt , qr)) =
  let (_ , _ , eqP , bP) = ev-inv (step-recv0 s)
  in _ , _ , αpar-soloL-step {at = _ , receive} {a = n0 , s} refl (λ { (inj₁ ()) ; (inj₂ ()) }) eqP bP refl
enabled (rFF (s , fsuc fzero) (t , fsuc fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-recv1 t)
  in _ , _ , αpar-soloR-step {at = _ , receive} {a = n1 , t} (λ ()) (inj₁ refl) refl eqQ bQ
enabled (rFF (s , fsuc fzero) (t , fzero)) =
  let (_ , _ , eqP , bP) = ev-inv (step-swapOut0 s)
  in _ , _ , αpar-sync-step {at = _ , swap} {a = n0 , (n1 , (s , n1))} (inj₁ refl) (inj₁ (inj₂ refl)) eqP bP refl refl
-- handshake states complete via the pending swap.
enabled (rS12 o c) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-swapOut1 o c)
  in _ , _ , αpar-sync-step {at = _ , swap} {a = n1 , (n0 , o)} (inj₂ refl) (inj₁ (inj₁ refl)) refl refl eqQ bQ
enabled (rS21 o c) =
  let (_ , _ , eqP , bP) = ev-inv (step-swapOut0S2 o c)
  in _ , _ , αpar-sync-step {at = _ , swap} {a = n0 , (n1 , o)} (inj₁ refl) (inj₁ (inj₂ refl)) eqP bP refl refl

------------------------------------------------------------------------------------
-- §5.7 THE THEOREM: the swap routing tree (2-node edge) is DEADLOCK-FREE.
swapTree-deadlockFree : DeadlockFree swapTree
swapTree-deadlockFree = progress⇒deadlockFree swap-progress
  where
    swap-progress : Progress swapTree
    swap-progress bs with reach-cons (embed∖√ bs)
    ... | (_ , _ , refl , reach) = enabled reach
