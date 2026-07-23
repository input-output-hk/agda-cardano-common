{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2.1: the `general4a` routing network and its livelock.
--
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/general4a.csp   (UCS ch. 4, general routing)
--
-- FDR reports
--
--   assert HNetwork :[divergence free]    -- FAILS
--
-- and this module proves the dual: HNetwork *does* diverge.  It is the FIRST
-- livelock/divergence in the port, an EXISTENTIAL `Diverges` witness.
--
-- WHAT IS ISOLATED.  The full `general4a` node runs a `swap`/`yes`/`no`
-- three-way handshake protocol whose purpose is DEADLOCK-freedom (making the
-- network never get stuck); that machinery is entirely orthogonal to the
-- livelock.  The livelock is created by the *message-circulation core*: a
-- packet that is handed round a directed cycle of nodes over an internal
-- `pass` channel and never delivered.  Once the `pass` channel is HIDDEN
-- (it is an internal wiring detail), the endless circulation becomes an
-- infinite τ-loop — divergence.  This module therefore models exactly that
-- core: a directed 3-cycle of forwarding nodes, `pass` hidden.
--
-- Node = Fin 3, directed 3-cycle  nextN 0 = 1, nextN 1 = 2, nextN 2 = 0.
-- Payload T = ⊤ (trivial), packet = (Node × Node) = (src , dst).
--
-- The construction mirrors, at the divergence level, the ch3 `DIV = AS ∖ {a}`
-- example (`CSP.Examples.TPC.Ch3.FailuresDivergences`): hiding an event that a
-- process keeps re-enabling turns it into an infinite τ-stream.  Here the
-- "kept re-enabled" event is the `pass` hand-off, re-created every time the
-- packet arrives at the next node; the τ-loop cycles through THREE carrying
-- configurations rather than two.

module CSP.Examples.UCS.Ch4.GeneralNetworkLivelock where

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
-- §1. Node type and cyclic topology
-------------------------------------------------------------------------------------

Node : Set
Node = Fin 3

n0 n1 n2 : Node
n0 = fzero
n1 = fsuc fzero
n2 = fsuc (fsuc fzero)

-- directed 3-cycle: 0 ↦ 1 ↦ 2 ↦ 0
nextN : Node → Node
nextN fzero               = n1
nextN (fsuc fzero)        = n2
nextN (fsuc (fsuc fzero)) = n0

-------------------------------------------------------------------------------------
-- §2. The event type and its decidable equality
-------------------------------------------------------------------------------------

data GEv : Set → Set where
  send    : GEv (Node × Node)                    -- send.i.dst      : (i , dst)
  receive : GEv (Node × Node)                    -- receive.i.src   : (i , src)
  pass    : GEv (Node × (Node × (Node × Node)))  -- pass.from.to.(src,dst)

GEv-≟ : (x y : AnyTypes GEv) → Dec (x ≡ y)
GEv-≟ (_ , send)    (_ , send)    = yes refl
GEv-≟ (_ , receive) (_ , receive) = yes refl
GEv-≟ (_ , pass)    (_ , pass)    = yes refl
GEv-≟ (_ , send)    (_ , receive) = no (λ ())
GEv-≟ (_ , send)    (_ , pass)    = no (λ ())
GEv-≟ (_ , receive) (_ , send)    = no (λ ())
GEv-≟ (_ , receive) (_ , pass)    = no (λ ())
GEv-≟ (_ , pass)    (_ , send)    = no (λ ())
GEv-≟ (_ , pass)    (_ , receive) = no (λ ())

open import CSP.Operators GEv-≟
open EventSet

-------------------------------------------------------------------------------------
-- §3. Per-node alphabet
-------------------------------------------------------------------------------------

-- Node `i` owns `send.i`, `receive.i` (both solo), and every `pass` event in which
-- it is either the sender (`from ≡ i`, i.e. `pass.i.(nextN i)`) or the receiver
-- (`to ≡ i`, i.e. `pass.(prev i).i`).  For the cyclic hand-offs actually generated
-- (`pass.k.(nextN k)`) this is exactly the two-node sync set `{ i , prev i }`.
A : Node → EventSet
A i .mem (_ , send)    (j , _)        = j ≡ i
A i .mem (_ , receive) (j , _)        = j ≡ i
A i .mem (_ , pass)    (from , to , _) = (from ≡ i) ⊎ (to ≡ i)
A i .dec (_ , send)    (j , _)        = j Fin.≟ i
A i .dec (_ , receive) (j , _)        = j Fin.≟ i
A i .dec (_ , pass)    (from , to , _) = (from Fin.≟ i) ⊎-dec (to Fin.≟ i)

-------------------------------------------------------------------------------------
-- §4. The forwarding node, the network, and its hidden form
-------------------------------------------------------------------------------------

GProc : Set₁
GProc = PTree GEv (ExtI GEv) (⊤poly {lzero})

-- NodeE i  — empty node.  Offers `send.i?dst → NodeF i (i,dst)`  and
--            `pass?from.i?p → NodeF i p` (accept a packet addressed here, store it).
-- NodeF i pkt — full node holding `pkt`.  ALWAYS forwards it on to the successor:
--            `pass.i.(nextN i).<any> → NodeE i`.  It never delivers (offers no
--            `receive`), so the packet circulates forever.  The forward is
--            value-generalised (it forwards regardless of the payload value);
--            this is sound for the existential divergence witness.
NodeE : Node → GProc
NodeF : Node → (Node × Node) → GProc

force (NodeE i) = react
  (λ where
     (_ , send)    (j , dst)         → case j Fin.≟ i of λ where
         (yes _) → just (NodeF i (j , dst))
         (no  _) → nothing
     (_ , receive) _                 → nothing
     (_ , pass)    (from , to , p)   → case to Fin.≟ i of λ where
         (yes _) → just (NodeF i p)
         (no  _) → nothing)
  ∅t

force (NodeF i pkt) = react
  (λ where
     (_ , send)    _               → nothing
     (_ , receive) _               → nothing
     (_ , pass)    (from , to , p) → case from Fin.≟ i of λ where
         (yes _) → case to Fin.≟ nextN i of λ where
             (yes _) → just (NodeE i)
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

nodeE : Node → Comp GEv (⊤poly {lzero})
nodeE i = comp (A i) (NodeE i)

nodeF : Node → (Node × Node) → Comp GEv (⊤poly {lzero})
nodeF i pkt = comp (A i) (NodeF i pkt)

Network : PTree GEv (ExtI GEv) (RetOf⁺ (nodeE n0) (nodeE n1 ∷ nodeE n2 ∷ []))
Network = ∥ₐ⁺ (nodeE n0) (nodeE n1 ∷ nodeE n2 ∷ [])

-- hide the entire internal `pass` channel (every `pass` event)
pass-cs : AnyTypes GEv → Set
pass-cs (_ , send)    = ⊥
pass-cs (_ , receive) = ⊥
pass-cs (_ , pass)    = ⊤

pass-dec : (at : AnyTypes GEv) → Dec (pass-cs at)
pass-dec (_ , send)    = no (λ z → z)
pass-dec (_ , receive) = no (λ z → z)
pass-dec (_ , pass)    = yes tt

passSet : EventSet
passSet = chanSet pass-cs pass-dec

HNetwork : PTree GEv (ExtI GEv) (RetOf⁺ (nodeE n0) (nodeE n1 ∷ nodeE n2 ∷ []))
HNetwork = Network ∖ passSet

-------------------------------------------------------------------------------------
-- §5. Livelock: HNetwork reaches a circulating state and then diverges
-------------------------------------------------------------------------------------

open import Semantics.LTS       {E = GEv} {I = ExtI GEv} hiding (Diverges)
open import Semantics.Deadlock  {E = GEv} {I = ExtI GEv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev)
open import Semantics.DRBisim   {E = GEv} {I = ExtI GEv} using (Diverges)
open import Semantics.DeadlockDR {E = GEv} {I = ExtI GEv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide GEv-≟ using (Hide-keep; Hide-hidden)

-- the destination the packet is addressed to (never delivered — nodes only forward)
d : Node
d = n1

Ret3 : Set
Ret3 = RetOf⁺ (nodeE n0) (nodeE n1 ∷ nodeE n2 ∷ [])

-- The three circulating configurations (the packet (n0 , d) held by node 0 / 1 / 2).
config0 config1 config2 : PTree GEv (ExtI GEv) Ret3
config0 = ∥ₐ⁺ (nodeF n0 (n0 , d)) (nodeE n1              ∷ nodeE n2              ∷ [])
config1 = ∥ₐ⁺ (nodeE n0)          (nodeF n1 (n0 , d)     ∷ nodeE n2              ∷ [])
config2 = ∥ₐ⁺ (nodeE n0)          (nodeE n1              ∷ nodeF n2 (n0 , d)     ∷ [])

-- The hidden (τ-cycling) circulating states.
circ0 circ1 circ2 : PTree GEv (ExtI GEv) Ret3
circ0 = config0 ∖ passSet
circ1 = config1 ∖ passSet
circ2 = config2 ∖ passSet

------------------------------------------------------------------------------------
-- §5.1 The reach: inject a packet at node 0 with the solo `send.0.d` visible step.
------------------------------------------------------------------------------------

sendEv : Node → Node → Event
sendEv i dst = evLabel (Node × Node) send (i , dst)

-- send.0.d is in A0 only, so it fires solo at the head of the fold.
Network-send : Network ─[ ev (evl (sendEv n0 d)) ]─► config0
Network-send = αpar-soloL-step {at = _ , send} {a = n0 , d}
                 refl
                 (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) })
                 refl refl refl

-- `send` is not hidden, so it survives the hide as a visible `∖√-ev` step.
HNetwork-send : HNetwork ─[ ev (evl (sendEv n0 d)) ]─► circ0
HNetwork-send = Hide-keep passSet Network (λ ()) Network-send

reach : HNetwork ⟹∖√⟨ sendEv n0 d ∷ [] ⟩ circ0
reach = ∖√-ev HNetwork-send ∖√-refl

------------------------------------------------------------------------------------
-- §5.2 The three visible `pass` hand-offs of the underlying Network.
--
-- Each is built through the two-layer `∥ₐ⁺` fold: the outer αpar of the head node
-- against the tail composite, and (via `ev-inv` of the inner step) the tail composite's
-- own αpar.  Membership witnesses use `A i .mem (pass) = (from≡i) ⊎ (to≡i)`.
------------------------------------------------------------------------------------

passEv : Node → Node → (Node × Node) → Event
passEv from to p = evLabel (Node × (Node × (Node × Node))) pass (from , to , p)

-- circ0 → circ1 : node 0 forwards to node 1 over pass.0.1.  Outer = sync (0 & tail),
-- inner = node 1 solo (node 2 not involved).
config0-pass : config0 ─[ ev (evl (passEv n0 n1 (n0 , d))) ]─► config1
config0-pass =
  let inner : ∥ₐ⁺ (nodeE n1) (nodeE n2 ∷ []) ─[ ev (evl (passEv n0 n1 (n0 , d))) ]─►
              ∥ₐ⁺ (nodeF n1 (n0 , d)) (nodeE n2 ∷ [])
      inner = αpar-soloL-step {at = _ , pass} {a = n0 , n1 , (n0 , d)}
                (inj₂ refl)
                (λ { (inj₁ (inj₁ ())) ; (inj₁ (inj₂ ())) ; (inj₂ ()) })
                refl refl refl
      (_ , _ , eqQ , bQ) = ev-inv inner
  in αpar-sync-step {at = _ , pass} {a = n0 , n1 , (n0 , d)}
       (inj₁ refl) (inj₁ (inj₂ refl)) refl refl eqQ bQ

-- circ1 → circ2 : node 1 forwards to node 2 over pass.1.2.  Outer = node 0 not
-- involved (solo-R into tail), inner = sync (node 1 & node 2).
config1-pass : config1 ─[ ev (evl (passEv n1 n2 (n0 , d))) ]─► config2
config1-pass =
  let inner : ∥ₐ⁺ (nodeF n1 (n0 , d)) (nodeE n2 ∷ []) ─[ ev (evl (passEv n1 n2 (n0 , d))) ]─►
              ∥ₐ⁺ (nodeE n1) (nodeF n2 (n0 , d) ∷ [])
      inner = αpar-sync-step {at = _ , pass} {a = n1 , n2 , (n0 , d)}
                (inj₁ refl) (inj₁ (inj₂ refl)) refl refl refl refl
      (_ , _ , eqQ , bQ) = ev-inv inner
  in αpar-soloR-step {at = _ , pass} {a = n1 , n2 , (n0 , d)}
       (λ { (inj₁ ()) ; (inj₂ ()) }) (inj₁ (inj₁ refl)) refl eqQ bQ

-- circ2 → circ0 : node 2 forwards to node 0 over pass.2.0.  Outer = sync (node 0
-- receives & tail), inner = node 2 solo (node 1 not involved).
config2-pass : config2 ─[ ev (evl (passEv n2 n0 (n0 , d))) ]─► config0
config2-pass =
  let inner : ∥ₐ⁺ (nodeE n1) (nodeF n2 (n0 , d) ∷ []) ─[ ev (evl (passEv n2 n0 (n0 , d))) ]─►
              ∥ₐ⁺ (nodeE n1) (nodeE n2 ∷ [])
      inner = αpar-soloR-step {at = _ , pass} {a = n2 , n0 , (n0 , d)}
                (λ { (inj₁ ()) ; (inj₂ ()) }) (inj₁ (inj₁ refl)) refl refl refl
      (_ , _ , eqQ , bQ) = ev-inv inner
  in αpar-sync-step {at = _ , pass} {a = n2 , n0 , (n0 , d)}
       (inj₂ refl) (inj₂ (inj₁ (inj₁ refl))) refl refl eqQ bQ

------------------------------------------------------------------------------------
-- §5.3 Each hidden `pass` becomes a τ (the ch3 `DIV` mechanism, `Hide-hidden`).
------------------------------------------------------------------------------------

circ0-τ : circ0 ─[ τ ]─► circ1
circ0-τ = Hide-hidden passSet config0 tt config0-pass

circ1-τ : circ1 ─[ τ ]─► circ2
circ1-τ = Hide-hidden passSet config1 tt config1-pass

circ2-τ : circ2 ─[ τ ]─► circ0
circ2-τ = Hide-hidden passSet config2 tt config2-pass

------------------------------------------------------------------------------------
-- §5.4 The 3-periodic τ-loop: circ0 diverges.
------------------------------------------------------------------------------------

circ0-diverges : Diverges circ0
circ1-diverges : Diverges circ1
circ2-diverges : Diverges circ2

circ0-diverges .Diverges.next = circ1
circ0-diverges .Diverges.step = circ0-τ
circ0-diverges .Diverges.rest = circ1-diverges

circ1-diverges .Diverges.next = circ2
circ1-diverges .Diverges.step = circ1-τ
circ1-diverges .Diverges.rest = circ2-diverges

circ2-diverges .Diverges.next = circ0
circ2-diverges .Diverges.step = circ2-τ
circ2-diverges .Diverges.rest = circ0-diverges

------------------------------------------------------------------------------------
-- §5.5 The livelock theorem: `HNetwork :[divergence free]` FAILS.
------------------------------------------------------------------------------------

generalNet-livelocks :
  Σ[ s ∈ List Event ] Σ[ t′ ∈ PTree GEv (ExtI GEv) Ret3 ]
    (HNetwork ⟹∖√⟨ s ⟩ t′ × Diverges t′)
generalNet-livelocks = sendEv n0 d ∷ [] , circ0 , reach , circ0-diverges

¬generalNet-divergenceFree : ¬ DivergenceFree HNetwork
¬generalNet-divergenceFree df =
  let (s , t′ , reach′ , div) = generalNet-livelocks in df reach′ div
