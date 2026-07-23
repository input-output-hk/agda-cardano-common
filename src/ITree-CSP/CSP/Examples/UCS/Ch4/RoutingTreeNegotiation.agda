{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the NEGOTIATING store-and-forward routing *tree* (tree3)
-- and its NEGOTIATION-STALEMATE LIVELOCK.
--
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/tree3.csp   (UCS ch. 4, the negotiation tree)
--
-- FDR reports two assertions on the negotiation tree:
--
--   assert Tree                          :[deadlock free]    -- HOLDS  (the SIBLING module proves it)
--   assert Tree ∖ diff(Events,{send,receive}) :[divergence free]  -- FAILS (proved here)
--
-- `TreeH = Tree ∖ diff(Events,{send,receive})` hides EVERY internal negotiation
-- channel (`pass`, `yes`, `no`), leaving only the observable `send`/`receive`.
-- Two ADJACENT busy nodes, each holding a packet routed *through* the other, run
-- the forwarding hand-shake forever: node `i` proposes `yes.i.(next i r)`, is
-- declined with `no`, and re-proposes, ad infinitum.  Each `no` is a
-- synchronisation between the two adjacent nodes; once the negotiation channel is
-- HIDDEN every such `no` becomes an internal τ, so the endless "shall I? — no"
-- exchange is an infinite τ-loop — divergence.  Nothing is ever delivered: the
-- source's "no progress".  This is the negotiation analogue of
-- `CSP.Examples.UCS.Ch4.TokenRing` (empty-token loop) and
-- `CSP.Examples.UCS.Ch4.GeneralNetworkLivelock` (packet circulation).
--
-- REDUCTION.  We take the minimal instance N = 2 (edge 0—1).  The payload proper
-- is trivial (`T = ⊤`), so a packet is just its routing header `(src , dst)`.
--
-- PINNED offers.  Every FORWARDING offer of every node state is PINNED to its
-- exact value (no value-generalisation), because these same node definitions are
-- re-used by the sibling `Tree :[deadlock free]` module, whose claim is
-- UNIVERSAL — a generalised offer there would be unsound.  Genuine INPUTS
-- (`send.i?dst`, `pass?p`, `yes?j`/`no?j` from a neighbour) are receptive over
-- their input domain, as CSP `?` inputs are; that is not value-generalisation.
--
-- MODELLING NOTE ON `pass`.  A `pass` hand-off carries the sender, the receiver
-- AND the packet `(src , dst)`, i.e. four `Node`s: `pass.from.to.(src,dst)`.  We
-- therefore type it `pass : NEv (Node × (Node × (Node × Node)))`, exactly as the
-- `RoutingTreeNaive` template does.  (The negotiation livelock never fires a
-- `pass`; the loop is purely the hidden `no` self-synchronisation.)

module CSP.Examples.UCS.Ch4.RoutingTreeNegotiation where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-------------------------------------------------------------------------------------
-- §1. Node type and tree topology (N = 2, edge 0—1)
-------------------------------------------------------------------------------------

Node : Set
Node = Fin 2

n0 n1 : Node
n0 = fzero
n1 = fsuc fzero

-- the sole neighbour of each node (nbrs is a singleton at N = 2)
nb : Node → Node
nb fzero        = n1
nb (fsuc fzero) = n0

nbrs : Node → List Node        -- 0 ↦ 1∷[] , 1 ↦ 0∷[]
nbrs fzero        = n1 ∷ []
nbrs (fsuc fzero) = n0 ∷ []

-- `next i r` = the neighbour of `i` on the path toward `r` (trivial at N = 2).
next : Node → Node → Node      -- next 0 1 = 1 , next 1 0 = 0
next fzero        _ = n1
next (fsuc fzero) _ = n0

-------------------------------------------------------------------------------------
-- §2. The event type and its decidable equality
-------------------------------------------------------------------------------------

data NEv : Set → Set where
  send    : NEv (Node × Node)                    -- send.i.dst      : (i , dst)
  receive : NEv (Node × Node)                    -- receive.i.src   : (i , src)
  pass    : NEv (Node × (Node × (Node × Node)))  -- pass.from.to.(s,r)
  yesc    : NEv (Node × Node)                    -- yes.i.j         : (i , j)
  noc     : NEv (Node × Node)                    -- no.i.j          : (i , j)

-- (`yesc`/`noc` avoid the `Relation.Nullary` `Dec` constructor names `yes`/`no`,
--  matching the convention of `General4DivFree`; they read as `yes`/`no` events.)
NEv-≟ : (x y : AnyTypes NEv) → Dec (x ≡ y)
NEv-≟ (_ , send)    (_ , send)    = yes refl
NEv-≟ (_ , receive) (_ , receive) = yes refl
NEv-≟ (_ , pass)    (_ , pass)    = yes refl
NEv-≟ (_ , yesc)    (_ , yesc)    = yes refl
NEv-≟ (_ , noc)     (_ , noc)     = yes refl
NEv-≟ (_ , send)    (_ , receive) = no (λ ())
NEv-≟ (_ , send)    (_ , pass)    = no (λ ())
NEv-≟ (_ , send)    (_ , yesc)    = no (λ ())
NEv-≟ (_ , send)    (_ , noc)     = no (λ ())
NEv-≟ (_ , receive) (_ , send)    = no (λ ())
NEv-≟ (_ , receive) (_ , pass)    = no (λ ())
NEv-≟ (_ , receive) (_ , yesc)    = no (λ ())
NEv-≟ (_ , receive) (_ , noc)     = no (λ ())
NEv-≟ (_ , pass)    (_ , send)    = no (λ ())
NEv-≟ (_ , pass)    (_ , receive) = no (λ ())
NEv-≟ (_ , pass)    (_ , yesc)    = no (λ ())
NEv-≟ (_ , pass)    (_ , noc)     = no (λ ())
NEv-≟ (_ , yesc)    (_ , send)    = no (λ ())
NEv-≟ (_ , yesc)    (_ , receive) = no (λ ())
NEv-≟ (_ , yesc)    (_ , pass)    = no (λ ())
NEv-≟ (_ , yesc)    (_ , noc)     = no (λ ())
NEv-≟ (_ , noc)     (_ , send)    = no (λ ())
NEv-≟ (_ , noc)     (_ , receive) = no (λ ())
NEv-≟ (_ , noc)     (_ , pass)    = no (λ ())
NEv-≟ (_ , noc)     (_ , yesc)    = no (λ ())

open import CSP.Operators NEv-≟
open EventSet

-------------------------------------------------------------------------------------
-- §3. Per-node alphabet
-------------------------------------------------------------------------------------

-- Node `i` owns `send.i`, `receive.i` (both solo), and every `yes`/`no`/`pass`
-- endpoint it touches: a `yes.a.b` (resp. `no.a.b`) belongs to `A i` when `i` is
-- either speaker `a` or listener `b`; a `pass.from.to` belongs to `A i` when `i`
-- is sender `from` or receiver `to`.  Thus each `yes.i.j` / `no.i.j` / `pass.i.j`
-- SYNCHRONISES the two adjacent nodes `i` and `j`.
A : Node → EventSet
A i .mem (_ , send)    (a , _)         = a ≡ i
A i .mem (_ , receive) (a , _)         = a ≡ i
A i .mem (_ , yesc)    (a , b)         = (a ≡ i) ⊎ (b ≡ i)
A i .mem (_ , noc)     (a , b)         = (a ≡ i) ⊎ (b ≡ i)
A i .mem (_ , pass)    (from , to , _) = (from ≡ i) ⊎ (to ≡ i)
A i .dec (_ , send)    (a , _)         = a Fin.≟ i
A i .dec (_ , receive) (a , _)         = a Fin.≟ i
A i .dec (_ , yesc)    (a , b)         = (a Fin.≟ i) ⊎-dec (b Fin.≟ i)
A i .dec (_ , noc)     (a , b)         = (a Fin.≟ i) ⊎-dec (b Fin.≟ i)
A i .dec (_ , pass)    (from , to , _) = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)

-------------------------------------------------------------------------------------
-- §4. The negotiation node, the tree, and its hidden form
-------------------------------------------------------------------------------------

NProc : Set₁
NProc = PTree NEv (ExtI NEv) (⊤poly {lzero})

-- NodeE3 i        — EMPTY node.  Either injects a fresh packet
--                   `send.i?dst → NodeF3 i (i,dst)`, or accepts a neighbour's
--                   proposal `yes.j.i` (j ∈ nbrs i) and then receives the packet
--                   `pass.j.i?p → NodeF3 i p`  (via the intermediate `PassInE`).
-- PassInE i j     — i has agreed to take a packet from j; awaits `pass.j.i?p`.
-- NodeF3 i (s,r)  — FULL node holding packet `(s,r)`.  If it is the destination
--                   (`r ≡ i`) it delivers `receive.i.s → NodeE3 i`; otherwise it
--                   negotiates forwarding to `next i r`:
--                     `yes.i.(next i r) → pass.i.(next i r).(s,r) → NodeE3 i`  (via
--                     `PassOutF`)  or is declined `no.i.(next i r) → NodeF3 i (s,r)`.
--                   In EITHER case it also ABSORBS a neighbour's decline
--                   `no.j.i → NodeF3 i (s,r)` (j ∈ nbrs i), unchanged.  Forwarding
--                   offers are PINNED to the exact value.
-- PassOutF i (s,r)— i has proposed and been accepted; emits `pass.i.(next i r).(s,r)`.
NodeE3  : Node → NProc
PassInE : Node → Node → NProc
NodeF3  : Node → (Node × Node) → NProc
PassOutF : Node → (Node × Node) → NProc

force (NodeE3 i) = react
  (λ where
     (_ , send)    (a , b) → case a Fin.≟ i of λ where
         (yes _) → just (NodeF3 i (i , b))
         (no  _) → nothing
     (_ , receive) _       → nothing
     (_ , pass)    _       → nothing
     (_ , yesc)    (a , b) → case b Fin.≟ i of λ where
         (yes _) → case a Fin.≟ nb i of λ where
             (yes _) → just (PassInE i a)        -- accept proposal from neighbour a
             (no  _) → nothing
         (no  _) → nothing
     (_ , noc)     _       → nothing)
  ∅t

force (PassInE i j) = react
  (λ where
     (_ , send)    _              → nothing
     (_ , receive) _              → nothing
     (_ , yesc)    _              → nothing
     (_ , noc)     _              → nothing
     (_ , pass)    (from , to , p) → case from Fin.≟ j of λ where
         (yes _) → case to Fin.≟ i of λ where
             (yes _) → just (NodeF3 i p)          -- receive packet p from j
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

force (NodeF3 i (s , r)) = react
  (λ where
     (_ , send)    _        → nothing
     (_ , receive) (a , b)  → case r Fin.≟ i of λ where
         (yes _) → case a Fin.≟ i of λ where
             (yes _) → case b Fin.≟ s of λ where
                 (yes _) → just (NodeE3 i)         -- destination: deliver receive.i.s
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , pass)    _        → nothing
     (_ , yesc)    (a , b)  → case r Fin.≟ i of λ where
         (yes _) → nothing                         -- destination: no forwarding
         (no  _) → case a Fin.≟ i of λ where
             (yes _) → case b Fin.≟ next i r of λ where
                 (yes _) → just (PassOutF i (s , r))  -- propose yes.i.(next i r)
                 (no  _) → nothing
             (no  _) → nothing
     (_ , noc)     (a , b)  → case b Fin.≟ i of λ where
         (yes _) → case a Fin.≟ nb i of λ where
             (yes _) → just (NodeF3 i (s , r))     -- absorb neighbour's decline
             (no  _) → nothing
         (no  _) → case r Fin.≟ i of λ where
             (yes _) → nothing                     -- destination: no forwarding
             (no  _) → case a Fin.≟ i of λ where
                 (yes _) → case b Fin.≟ next i r of λ where
                     (yes _) → just (NodeF3 i (s , r))  -- own decline no.i.(next i r)
                     (no  _) → nothing
                 (no  _) → nothing)
  ∅t

force (PassOutF i (s , r)) = react
  (λ where
     (_ , send)    _        → nothing
     (_ , receive) _        → nothing
     (_ , yesc)    _        → nothing
     (_ , noc)     _        → nothing
     (_ , pass)    (from , to , (s′ , r′)) → case from Fin.≟ i of λ where
         (yes _) → case to Fin.≟ next i r of λ where
             (yes _) → case s′ Fin.≟ s of λ where
                 (yes _) → case r′ Fin.≟ r of λ where
                     (yes _) → just (NodeE3 i)     -- emit pass.i.(next i r).(s,r), PINNED
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

node : Node → Comp NEv (⊤poly {lzero})
node i = comp (A i) (NodeE3 i)

RetR : Set
RetR = RetOf⁺ (node n0) (node n1 ∷ [])

Tree : PTree NEv (ExtI NEv) RetR
Tree = ∥ₐ⁺ (node n0) (node n1 ∷ [])

-- The hidden internal-negotiation channels: every `pass`, `yes`, `no` event.
int-cs : AnyTypes NEv → Set
int-cs (_ , send)    = ⊥
int-cs (_ , receive) = ⊥
int-cs (_ , pass)    = ⊤
int-cs (_ , yesc)    = ⊤
int-cs (_ , noc)     = ⊤

int-dec : (at : AnyTypes NEv) → Dec (int-cs at)
int-dec (_ , send)    = no (λ z → z)
int-dec (_ , receive) = no (λ z → z)
int-dec (_ , pass)    = yes tt
int-dec (_ , yesc)    = yes tt
int-dec (_ , noc)     = yes tt

intES : EventSet
intES = chanSet int-cs int-dec

TreeH : PTree NEv (ExtI NEv) RetR
TreeH = Tree ∖ intES

-------------------------------------------------------------------------------------
-- §5. Livelock: TreeH negotiates `no` forever between two adjacent busy nodes
-------------------------------------------------------------------------------------

open import Semantics.LTS       {E = NEv} {I = ExtI NEv} hiding (Diverges)
open import Semantics.Deadlock  {E = NEv} {I = ExtI NEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev)
open import Semantics.DRBisim   {E = NEv} {I = ExtI NEv} using (Diverges)
open import Semantics.DeadlockDR {E = NEv} {I = ExtI NEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide NEv-≟ using (Hide-keep; Hide-hidden)

-- The two intermediate/target configurations reached by the two `send`s.
--   config1  : node 0 holds (0,1) [wants to forward to 1], node 1 still empty
--   config-W : node 0 holds (0,1), node 1 holds (1,0) [each routed through the other]
config1 config-W : PTree NEv (ExtI NEv) RetR
config1  = ∥ₐ⁺ (comp (A n0) (NodeF3 n0 (n0 , n1))) (comp (A n1) (NodeE3 n1)          ∷ [])
config-W = ∥ₐ⁺ (comp (A n0) (NodeF3 n0 (n0 , n1))) (comp (A n1) (NodeF3 n1 (n1 , n0)) ∷ [])

-- W is the hidden both-busy state; the livelock lives here.
W : PTree NEv (ExtI NEv) RetR
W = config-W ∖ intES

sendEv : Node → Node → Event
sendEv i dst = evLabel (Node × Node) send (i , dst)

noEv : Node → Node → Event
noEv a b = evLabel (Node × Node) noc (a , b)

------------------------------------------------------------------------------------
-- §5.1 The reach: two solo `send`s inject a packet at each node.
------------------------------------------------------------------------------------

-- send.0.1 ∈ A 0 only, so it fires solo at the head of the fold.
Tree-send : Tree ─[ ev (evl (sendEv n0 n1)) ]─► config1
Tree-send = αpar-soloL-step {at = _ , send} {a = n0 , n1}
              refl
              (λ { (inj₁ ()) ; (inj₂ ()) })
              refl refl refl

-- send.1.0 ∈ A 1 only, so it fires solo in the tail composite.
config1-send : config1 ─[ ev (evl (sendEv n1 n0)) ]─► config-W
config1-send = αpar-soloR-step {at = _ , send} {a = n1 , n0}
                 (λ ()) (inj₁ refl) refl refl refl

-- `send` is not hidden, so each survives the hide as a visible `∖√-ev` step.
TreeH-send : TreeH ─[ ev (evl (sendEv n0 n1)) ]─► (config1 ∖ intES)
TreeH-send = Hide-keep intES Tree (λ ()) Tree-send

config1H-send : (config1 ∖ intES) ─[ ev (evl (sendEv n1 n0)) ]─► W
config1H-send = Hide-keep intES config1 (λ ()) config1-send

reach : TreeH ⟹∖√⟨ sendEv n0 n1 ∷ sendEv n1 n0 ∷ [] ⟩ W
reach = ∖√-ev TreeH-send (∖√-ev config1H-send ∖√-refl)

------------------------------------------------------------------------------------
-- §5.2 At W, `no.0.1` is a synchronisation that leaves both nodes UNCHANGED:
--   node 0 (holding (0,1), r=1≠0) fires its OWN decline  no.0.(next 0 1)=no.0.1,
--   node 1 (holding (1,0), r=0≠1) ABSORBS it as no?(j∈nbrs 1).1 = no.0.1.
-- So config-W ─no.0.1─► config-W.  As `no ∈ intES`, TreeH does a τ: W ─τ─► W.
------------------------------------------------------------------------------------

config-W-no : config-W ─[ ev (evl (noEv n0 n1)) ]─► config-W
config-W-no = αpar-sync-step {at = _ , noc} {a = n0 , n1}
                (inj₁ refl)          -- no.0.1 ∈ A 0  (a = 0 ≡ 0)
                (inj₁ (inj₂ refl))   -- no.0.1 ∈ A 1  (b = 1 ≡ 1)
                refl refl refl refl

W-τ : W ─[ τ ]─► W
W-τ = Hide-hidden intES config-W tt config-W-no

------------------------------------------------------------------------------------
-- §5.3 The 1-state τ-loop: W diverges.
------------------------------------------------------------------------------------

W-diverges : Diverges W
W-diverges .Diverges.next = W
W-diverges .Diverges.step = W-τ
W-diverges .Diverges.rest = W-diverges

------------------------------------------------------------------------------------
-- §5.4 The livelock theorem: `Tree ∖ diff(Events,{send,receive}) :[divergence free]` FAILS.
------------------------------------------------------------------------------------

tree3-livelocks :
  Σ[ s ∈ List Event ] Σ[ t′ ∈ PTree NEv (ExtI NEv) RetR ]
    (TreeH ⟹∖√⟨ s ⟩ t′ × Diverges t′)
tree3-livelocks = sendEv n0 n1 ∷ sendEv n1 n0 ∷ [] , W , reach , W-diverges

¬tree3-divergenceFree : ¬ DivergenceFree TreeH
¬tree3-divergenceFree df =
  let (s , t′ , reach′ , div) = tree3-livelocks in df reach′ div
