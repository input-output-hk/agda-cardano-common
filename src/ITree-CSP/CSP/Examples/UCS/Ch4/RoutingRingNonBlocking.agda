{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the NON-BLOCKING store-and-forward routing ring is
-- DEADLOCK-FREE — the deadlock-free counterpart of the naive ring
-- (`RoutingRingNaive`, which deadlocks).  Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/nonblock.csp   (UCS ch. 4 §4.2, the non-blocking ring)
--
-- Each node is a TWO-slot store-and-forward buffer.  Writing `p = (src,dst)`:
--
--   NodeE n          = ring.n?p → Node1 n p  □  send.n?dst → Node1 n (n,dst)
--   Node1 n (a,b)    = if n≡b then receive.n.a → NodeE n
--                      else (ring.n?p′ → Node2 n (a,b) p′  □  ring.(nextN n).(a,b) → NodeE n)
--   Node2 n (a,b) p′ = ring.(nextN n).(a,b) → Node1 n p′
--
-- The extra buffer slot (`Node2`) is what breaks the naive ring's deadlock: a
-- node holding ONE remote packet (`Node1 …` remote) still offers `ring.n?`
-- INPUT — it need not commit solely to its forwarding output — so a full cycle
-- of blocked forwardings can never form.
--
-- ────────────────────────────────────────────────────────────────────────────
-- ⚠  N-REDUCTION (documented per the task spec).  A faithful (packet-PINNED)
-- DeadlockFree proof at N = 4 is a value-level reachable-config enumeration whose
-- state space is astronomically large (each Node1/Node2 pins specific packets
-- from Node×Node).  This module therefore proves the contrast at the SMALLEST
-- ring that still exhibits it, **N = 2**, exactly as the spec sanctions ("the
-- non-blocking-vs-naive contrast holds for any N≥2").  Because the shared
-- scaffold in `RoutingRingNaive` is fixed to `Node = Fin 4` (its event payloads
-- are `Fin 4 …`), the N = 2 instance is a SELF-CONTAINED re-derivation of the
-- scaffold (`Node = Fin 2`, `nextN` mod 2, its own `REv`/`REv-≟`/`A`), rather
-- than an import.
--
-- FAITHFULNESS (the load-bearing point for a *universal* DeadlockFree claim):
-- the forwards are PINNED, NOT payload-discarded.  `Node1`/`Node2` forward the
-- SPECIFIC held packet `(a,b)` at index `nextN n` (see the `pkt≟ p (a,b)` guards
-- in their offer maps), and inputs/deliveries are the real events.  An
-- over-approximated (payload-generalised) model would be UNSOUND here: it could
-- exhibit progress the real ring lacks.
--
-- PROOF APPROACH.  Every node is react-headed and STABLE (τ-map ≡ ∅t), so a node
-- has NO τ/√ transition; hence the composite's only moves are VISIBLE (a solo
-- send/receive, or a ring sync between the two nodes).  We track each node by its
-- reachable POSITION CLASS (NodeE / Node1 pkt / Node2 pkt pkt′) and carry a joint
-- reachability predicate `RSys` whose eight constructors are exactly the reachable
-- occupancy pairs (0,0),(1,0),(0,1),(1,1),(2,0),(0,2),(2,1),(1,2).  The forbidden
-- all-full pair (2,2) is absent, and is unreachable BY CONSTRUCTION: a ring sync
-- always moves +1 packet to one node and −1 from the other, so no single step can
-- fill both nodes.  `RSys` is closed under stepping (`rsys-step`) and every `RSys`
-- state can move (`rsys-enabled`); `Progress` and `DeadlockFree` follow.

module CSP.Examples.UCS.Ch4.RoutingRingNonBlocking where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; #_) renaming (zero to fzero; suc to fsuc)
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
-- §1. Node type and ring arithmetic (N = 2).
Node : Set
Node = Fin 2

n0 n1 : Node
n0 = fzero
n1 = fsuc fzero

-- (i + 1) mod 2, as a concrete two-case function.
nextN : Node → Node
nextN fzero        = n1
nextN (fsuc fzero) = n0

------------------------------------------------------------------------------------
-- §2. The event type and its decidable equality.
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

-- decidable equality on packets `Node × Node`
pkt≟ : (p q : Node × Node) → Dec (p ≡ q)
pkt≟ = ×-≡-dec Fin._≟_ Fin._≟_

open import CSP.Operators REv-≟
open EventSet

------------------------------------------------------------------------------------
-- §3. Per-node alphabets.  Node i owns send.i, receive.i, and the two ring
-- endpoints it touches: ring.i (input from predecessor) and ring.(i+1)%2 (forward
-- to successor).
A : Node → EventSet
A i .mem (_ , send)    (j , _) = j ≡ i
A i .mem (_ , receive) (j , _) = j ≡ i
A i .mem (_ , ring)    (j , _) = (j ≡ i) ⊎ (j ≡ nextN i)
A i .dec (_ , send)    (j , _) = j Fin.≟ i
A i .dec (_ , receive) (j , _) = j Fin.≟ i
A i .dec (_ , ring)    (j , _) = (j Fin.≟ i) ⊎-dec (j Fin.≟ nextN i)

------------------------------------------------------------------------------------
-- §4. The non-blocking node and the ring.  Following the naive-ring idiom, the
-- corecursive loop is written as inlined `react` copatterns (the corecursive
-- calls sit directly under `just`), which the guardedness checker accepts.  The
-- τ-branch is `∅t` throughout: every position is STABLE (no internal choice).
DProcR : Set₁
DProcR = PTree REv (ExtI REv) (⊤poly {lzero})

NodeE : Node → DProcR
Node1 : Node → (Node × Node) → DProcR
Node2 : Node → (Node × Node) → (Node × Node) → DProcR

force (NodeE n) = react
  (λ where
     (_ , send)    (j , dst) → case j Fin.≟ n of λ where
         (yes _) → just (Node1 n (n , dst))
         (no  _) → nothing
     (_ , receive) _         → nothing
     (_ , ring)    (j , p)   → case j Fin.≟ n of λ where
         (yes _) → just (Node1 n p)
         (no  _) → nothing)
  ∅t

force (Node1 n (a , b)) = react
  (λ where
     (_ , send)    _         → nothing
     (_ , receive) (j , src) → case n Fin.≟ b of λ where
         (yes _) → case j Fin.≟ n of λ where
             (yes _) → case src Fin.≟ a of λ where
                 (yes _) → just (NodeE n)
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , ring)    (j , p)   → case n Fin.≟ b of λ where
         (yes _) → nothing                              -- local: only delivers
         (no  _) → case j Fin.≟ n of λ where
             (yes _) → just (Node2 n (a , b) p)         -- input into slot 2
             (no  _) → case j Fin.≟ nextN n of λ where
                 (yes _) → case pkt≟ p (a , b) of λ where
                     (yes _) → just (NodeE n)           -- forward the held packet
                     (no  _) → nothing
                 (no  _) → nothing)
  ∅t

force (Node2 n (a , b) p′) = react
  (λ where
     (_ , send)    _         → nothing
     (_ , receive) _         → nothing
     (_ , ring)    (j , p)   → case j Fin.≟ nextN n of λ where
         (yes _) → case pkt≟ p (a , b) of λ where
             (yes _) → just (Node1 n p′)               -- forward slot 1, keep slot 2
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

nbNode : Node → Comp REv (⊤poly {lzero})
nbNode n = comp (A n) (NodeE n)

nonBlockingRing : PTree REv (ExtI REv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
nonBlockingRing = ∥ₐ⁺ (nbNode n0) (nbNode n1 ∷ [])

------------------------------------------------------------------------------------
-- §5. Verification machinery.
open import Semantics.LTS      {E = REv} {I = ExtI REv}
open import Semantics.Failures {E = REv} {I = ExtI REv} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = REv} {I = ExtI REv}
  using ( IsStuck; DeadlockFree; _⟹∖√⟨_⟩_; embed∖√ )
open import Semantics.DeadlockDR {E = REv} {I = ExtI REv}
  using ( Progress; progress⇒deadlockFree )
open import CSP.Laws.AlphaParallel REv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

-- The right-hand alphabet (the folded tail, a singleton) and the composite state.
B1 : EventSet
B1 = unionα (nbNode n1 ∷ [])

Sys : DProcR → DProcR → PTree REv (ExtI REv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

ring≡ : nonBlockingRing ≡ Sys (NodeE n0) (NodeE n1)
ring≡ = refl

REvent : Set₁
REvent = Event

------------------------------------------------------------------------------------
-- §5.1 Per-node reachable POSITION CLASSES (existential in the pinned packets).
data Pos0 : DProcR → Set where
  e0 : Pos0 (NodeE n0)
  o0 : ∀ p   → Pos0 (Node1 n0 p)
  w0 : ∀ p q → Pos0 (Node2 n0 p q)
data Pos1 : DProcR → Set where
  e1 : Pos1 (NodeE n1)
  o1 : ∀ p   → Pos1 (Node1 n1 p)
  w1 : ∀ p q → Pos1 (Node2 n1 p q)

pos0-noret : ∀ {t x} → Pos0 t → t .force ≡ ret x → ⊥
pos0-noret e0 () ; pos0-noret (o0 _) () ; pos0-noret (w0 _ _) ()
pos1-noret : ∀ {t x} → Pos1 t → t .force ≡ ret x → ⊥
pos1-noret e1 () ; pos1-noret (o1 _) () ; pos1-noret (w1 _ _) ()

n0-noτ : ∀ {t t′} → Pos0 t → t ─[ τ ]─► t′ → ⊥
n0-noτ e0      (sSil eq)     = case eq of λ ()
n0-noτ e0      (sTau refl br) = case br of λ ()
n0-noτ (o0 _)  (sSil eq)     = case eq of λ ()
n0-noτ (o0 _)  (sTau refl br) = case br of λ ()
n0-noτ (w0 _ _)(sSil eq)     = case eq of λ ()
n0-noτ (w0 _ _)(sTau refl br) = case br of λ ()
n1-noτ : ∀ {t t′} → Pos1 t → t ─[ τ ]─► t′ → ⊥
n1-noτ e1      (sSil eq)     = case eq of λ ()
n1-noτ e1      (sTau refl br) = case br of λ ()
n1-noτ (o1 _)  (sSil eq)     = case eq of λ ()
n1-noτ (o1 _)  (sTau refl br) = case br of λ ()
n1-noτ (w1 _ _)(sSil eq)     = case eq of λ ()
n1-noτ (w1 _ _)(sTau refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §5.2 Per-node visible-step transition relations, indexed by the R-independent
-- event.  (Forward events keep the recorded event value general in `p`; the guards
-- in the node offer maps ensure they only fire at the PINNED held packet, but the
-- proof never needs that value, so it is not pinned in the index.)
data T0 : DProcR → DProcR → REvent → Set₁ where
  t0-send : ∀ dst      → T0 (NodeE n0) (Node1 n0 (n0 , dst)) (evLabel (Node × Node) send (n0 , dst))
  t0-in0  : ∀ p        → T0 (NodeE n0) (Node1 n0 p)          (evLabel (Node × (Node × Node)) ring (n0 , p))
  t0-recv : ∀ a src    → T0 (Node1 n0 (a , n0)) (NodeE n0)   (evLabel (Node × Node) receive (n0 , src))
  t0-in1  : ∀ a p      → T0 (Node1 n0 (a , n1)) (Node2 n0 (a , n1) p) (evLabel (Node × (Node × Node)) ring (n0 , p))
  t0-fwd1 : ∀ a p      → T0 (Node1 n0 (a , n1)) (NodeE n0)   (evLabel (Node × (Node × Node)) ring (n1 , p))
  t0-fwd2 : ∀ a b p′ p → T0 (Node2 n0 (a , b) p′) (Node1 n0 p′) (evLabel (Node × (Node × Node)) ring (n1 , p))

data T1 : DProcR → DProcR → REvent → Set₁ where
  t1-send : ∀ dst      → T1 (NodeE n1) (Node1 n1 (n1 , dst)) (evLabel (Node × Node) send (n1 , dst))
  t1-in1  : ∀ p        → T1 (NodeE n1) (Node1 n1 p)          (evLabel (Node × (Node × Node)) ring (n1 , p))
  t1-recv : ∀ a src    → T1 (Node1 n1 (a , n1)) (NodeE n1)   (evLabel (Node × Node) receive (n1 , src))
  t1-in2  : ∀ a p      → T1 (Node1 n1 (a , n0)) (Node2 n1 (a , n0) p) (evLabel (Node × (Node × Node)) ring (n1 , p))
  t1-fwd1 : ∀ a p      → T1 (Node1 n1 (a , n0)) (NodeE n1)   (evLabel (Node × (Node × Node)) ring (n0 , p))
  t1-fwd2 : ∀ a b p′ p → T1 (Node2 n1 (a , b) p′) (Node1 n1 p′) (evLabel (Node × (Node × Node)) ring (n0 , p))

-- node0 visible-step inversion.  (Packet `b`-components are split fzero/fsuc fzero so
-- the `n Fin.≟ b` guard reduces; the source-match `src Fin.≟ a` / forward-match
-- `pkt≟ p (a,b)` are resolved by `with`.)
n0-inv : ∀ {t t′ e} → Pos0 t → t ─[ ev (evl e) ]─► t′ → T0 t t′ e
n0-inv e0 (sVis {at = _ , send}    {a = fzero , dst}      refl br) = subst (λ z → T0 _ z _) (just-injective br) (t0-send dst)
n0-inv e0 (sVis {at = _ , send}    {a = fsuc fzero , dst} refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , receive}                        refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , ring}    {a = fzero , p}        refl br) = subst (λ z → T0 _ z _) (just-injective br) (t0-in0 p)
n0-inv e0 (sVis {at = _ , ring}    {a = fsuc fzero , p}   refl br) = case br of λ ()
n0-inv (o0 (a , fzero)) (sVis {at = _ , send}    refl br) = case br of λ ()
n0-inv (o0 (a , fzero)) (sVis {at = _ , receive} {a = fzero , src}      refl br) with src Fin.≟ a
... | yes _ = subst (λ z → T0 _ z _) (just-injective br) (t0-recv a src)
... | no  _ = case br of λ ()
n0-inv (o0 (a , fzero)) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) = case br of λ ()
n0-inv (o0 (a , fzero)) (sVis {at = _ , ring}    refl br) = case br of λ ()
n0-inv (o0 (a , fsuc fzero)) (sVis {at = _ , send}    refl br) = case br of λ ()
n0-inv (o0 (a , fsuc fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (o0 (a , fsuc fzero)) (sVis {at = _ , ring} {a = fzero , p}      refl br) = subst (λ z → T0 _ z _) (just-injective br) (t0-in1 a p)
n0-inv (o0 (a , fsuc fzero)) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) with pkt≟ p (a , n1)
... | yes _ = subst (λ z → T0 _ z _) (just-injective br) (t0-fwd1 a p)
... | no  _ = case br of λ ()
n0-inv (w0 (a , b) p′) (sVis {at = _ , send}    refl br) = case br of λ ()
n0-inv (w0 (a , b) p′) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (w0 (a , b) p′) (sVis {at = _ , ring} {a = fzero , p}      refl br) = case br of λ ()
n0-inv (w0 (a , b) p′) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) with pkt≟ p (a , b)
... | yes _ = subst (λ z → T0 _ z _) (just-injective br) (t0-fwd2 a b p′ p)
... | no  _ = case br of λ ()

-- node1 visible-step inversion (index n1; forward index nextN n1 = n0).
n1-inv : ∀ {t t′ e} → Pos1 t → t ─[ ev (evl e) ]─► t′ → T1 t t′ e
n1-inv e1 (sVis {at = _ , send}    {a = fsuc fzero , dst} refl br) = subst (λ z → T1 _ z _) (just-injective br) (t1-send dst)
n1-inv e1 (sVis {at = _ , send}    {a = fzero , dst}      refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , receive}                        refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , ring}    {a = fsuc fzero , p}   refl br) = subst (λ z → T1 _ z _) (just-injective br) (t1-in1 p)
n1-inv e1 (sVis {at = _ , ring}    {a = fzero , p}        refl br) = case br of λ ()
n1-inv (o1 (a , fsuc fzero)) (sVis {at = _ , send}    refl br) = case br of λ ()
n1-inv (o1 (a , fsuc fzero)) (sVis {at = _ , receive} {a = fsuc fzero , src} refl br) with src Fin.≟ a
... | yes _ = subst (λ z → T1 _ z _) (just-injective br) (t1-recv a src)
... | no  _ = case br of λ ()
n1-inv (o1 (a , fsuc fzero)) (sVis {at = _ , receive} {a = fzero , src} refl br) = case br of λ ()
n1-inv (o1 (a , fsuc fzero)) (sVis {at = _ , ring}    refl br) = case br of λ ()
n1-inv (o1 (a , fzero)) (sVis {at = _ , send}    refl br) = case br of λ ()
n1-inv (o1 (a , fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (o1 (a , fzero)) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) = subst (λ z → T1 _ z _) (just-injective br) (t1-in2 a p)
n1-inv (o1 (a , fzero)) (sVis {at = _ , ring} {a = fzero , p}      refl br) with pkt≟ p (a , n0)
... | yes _ = subst (λ z → T1 _ z _) (just-injective br) (t1-fwd1 a p)
... | no  _ = case br of λ ()
n1-inv (w1 (a , b) p′) (sVis {at = _ , send}    refl br) = case br of λ ()
n1-inv (w1 (a , b) p′) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (w1 (a , b) p′) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) = case br of λ ()
n1-inv (w1 (a , b) p′) (sVis {at = _ , ring} {a = fzero , p}      refl br) with pkt≟ p (a , b)
... | yes _ = subst (λ z → T1 _ z _) (just-injective br) (t1-fwd2 a b p′ p)
... | no  _ = case br of λ ()

------------------------------------------------------------------------------------
-- §5.3 The joint reachability predicate: the eight reachable occupancy pairs.  The
-- forbidden all-full pair (2,2) is ABSENT (unreachable by construction: a ring sync
-- always moves +1 packet to one node and −1 from the other).
data RSys : DProcR → DProcR → Set₁ where
  r-00 :             RSys (NodeE n0)      (NodeE n1)
  r-10 : ∀ p       → RSys (Node1 n0 p)    (NodeE n1)
  r-01 : ∀ p       → RSys (NodeE n0)      (Node1 n1 p)
  r-11 : ∀ p q     → RSys (Node1 n0 p)    (Node1 n1 q)
  r-20 : ∀ p q     → RSys (Node2 n0 p q)  (NodeE n1)
  r-02 : ∀ p q     → RSys (NodeE n0)      (Node2 n1 p q)
  r-21 : ∀ p q r   → RSys (Node2 n0 p q)  (Node1 n1 r)
  r-12 : ∀ p q r   → RSys (Node1 n0 p)    (Node2 n1 q r)

rsys-init : RSys (NodeE n0) (NodeE n1)
rsys-init = r-00

rsys-pos0 : ∀ {t0 t1} → RSys t0 t1 → Pos0 t0
rsys-pos0 r-00        = e0
rsys-pos0 (r-10 p)    = o0 p
rsys-pos0 (r-01 p)    = e0
rsys-pos0 (r-11 p q)  = o0 p
rsys-pos0 (r-20 p q)  = w0 p q
rsys-pos0 (r-02 p q)  = e0
rsys-pos0 (r-21 p q r)= w0 p q
rsys-pos0 (r-12 p q r)= o0 p
rsys-pos1 : ∀ {t0 t1} → RSys t0 t1 → Pos1 t1
rsys-pos1 r-00        = e1
rsys-pos1 (r-10 p)    = e1
rsys-pos1 (r-01 p)    = o1 p
rsys-pos1 (r-11 p q)  = o1 q
rsys-pos1 (r-20 p q)  = e1
rsys-pos1 (r-02 p q)  = w1 p q
rsys-pos1 (r-21 p q r)= o1 r
rsys-pos1 (r-12 p q r)= w1 q r

-- Solo-move config updates (an unchanged neighbour): factored out so they are shared
-- across the sibling `with`-clauses of `sys-inv`.
r-solo0-send : ∀ {t1} → Pos1 t1 → (dst : Node) → RSys (Node1 n0 (n0 , dst)) t1
r-solo0-send e1      dst = r-10 (n0 , dst)
r-solo0-send (o1 q)  dst = r-11 (n0 , dst) q
r-solo0-send (w1 q r) dst = r-12 (n0 , dst) q r
r-solo0-recv : ∀ {t1} → Pos1 t1 → RSys (NodeE n0) t1
r-solo0-recv e1       = r-00
r-solo0-recv (o1 q)   = r-01 q
r-solo0-recv (w1 q r) = r-02 q r
r-solo1-send : ∀ {t0} → Pos0 t0 → (dst : Node) → RSys t0 (Node1 n1 (n1 , dst))
r-solo1-send e0      dst = r-01 (n1 , dst)
r-solo1-send (o0 p)  dst = r-11 p (n1 , dst)
r-solo1-send (w0 p q) dst = r-21 p q (n1 , dst)
r-solo1-recv : ∀ {t0} → Pos0 t0 → RSys t0 (NodeE n1)
r-solo1-recv e0       = r-00
r-solo1-recv (o0 p)   = r-10 p
r-solo1-recv (w0 p q) = r-20 p q

------------------------------------------------------------------------------------
-- §5.4 The system single-step inversion: every step from a reachable state lands in a
-- reachable state (RSys is closed).  τ/√ are impossible (nodes are react-headed and
-- stable); visible steps route sync / solo-L / solo-R.
sys-inv : ∀ {t0 t1 l t′} → RSys t0 t1 → Sys t0 t1 ─[ l ]─► t′
        → Σ[ t0′ ∈ DProcR ] Σ[ t1′ ∈ DProcR ] (t′ ≡ Sys t0′ t1′ × RSys t0′ t1′)
-- √ : composite at ret ⇒ both operands at ret — impossible.
sys-inv rs (sRet feq) with αpar-√-step-inv feq
... | v√ p0 _ = ⊥-elim (pos0-noret (rsys-pos0 rs) p0)
-- τ : an operand τ — impossible (stable nodes).
sys-inv rs (sSil feq) with αpar-τ-step-inv (sSil feq)
... | inj₁ (_ , pτ , _) = ⊥-elim (n0-noτ (rsys-pos0 rs) pτ)
... | inj₂ (_ , qτ , _) = ⊥-elim (n1-noτ (rsys-pos1 rs) qτ)
sys-inv rs (sTau feq br) with αpar-τ-step-inv (sTau feq br)
... | inj₁ (_ , pτ , _) = ⊥-elim (n0-noτ (rsys-pos0 rs) pτ)
... | inj₂ (_ , qτ , _) = ⊥-elim (n1-noτ (rsys-pos1 rs) qτ)
-- visible : route.
sys-inv rs (sVis feq br) with αpar-vis-step-inv feq br
-- ── SYNC (ring hand-off): correlate the two node transitions by the shared event ──
... | vSync pA pB p0step q1step with n0-inv (rsys-pos0 rs) p0step | n1-inv (rsys-pos1 rs) q1step
...   | t0-in0 p        | t1-fwd1 c _        = _ , _ , refl , r-10 p
...   | t0-in0 p        | t1-fwd2 c b p′ _   = _ , _ , refl , r-11 p p′
...   | t0-in1 a p      | t1-fwd1 c _        = _ , _ , refl , r-20 (a , n1) p
...   | t0-in1 a p      | t1-fwd2 c b p′ _   = _ , _ , refl , r-21 (a , n1) p p′
...   | t0-fwd1 a _     | t1-in1 p           = _ , _ , refl , r-01 p
...   | t0-fwd1 a _     | t1-in2 c p         = _ , _ , refl , r-02 (c , n0) p
...   | t0-fwd2 a b p′ _ | t1-in1 p          = _ , _ , refl , r-11 p′ p
...   | t0-fwd2 a b p′ _ | t1-in2 c p        = _ , _ , refl , r-12 p′ (c , n0) p
-- ── SOLO-L (node0 alone): only send.n0 / receive.n0; ring events are in B1 (¬pB) ──
sys-inv rs (sVis feq br) | vSoloL pA ¬pB p0step with n0-inv (rsys-pos0 rs) p0step
...   | t0-send dst   = _ , _ , refl , r-solo0-send (rsys-pos1 rs) dst
...   | t0-recv a src = _ , _ , refl , r-solo0-recv (rsys-pos1 rs)
...   | t0-in0 p      = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...   | t0-in1 a p    = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...   | t0-fwd1 a p   = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...   | t0-fwd2 a b p′ p = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
-- ── SOLO-R (node1 alone): only send.n1 / receive.n1; ring events are in A0 (¬pA) ──
sys-inv rs (sVis feq br) | vSoloR ¬pA pB q1step with n1-inv (rsys-pos1 rs) q1step
...   | t1-send dst   = _ , _ , refl , r-solo1-send (rsys-pos0 rs) dst
...   | t1-recv a src = _ , _ , refl , r-solo1-recv (rsys-pos0 rs)
...   | t1-in1 p      = ⊥-elim (¬pA (inj₂ refl))
...   | t1-in2 a p    = ⊥-elim (¬pA (inj₂ refl))
...   | t1-fwd1 a p   = ⊥-elim (¬pA (inj₁ refl))
...   | t1-fwd2 a b p′ p = ⊥-elim (¬pA (inj₁ refl))

------------------------------------------------------------------------------------
-- §5.5 Reachability closure: every ⟹-reachable state of the ring is a reachable RSys
-- configuration.
reach-cons : ∀ {s t′} → nonBlockingRing ⟹⟨ s ⟩ t′
           → Σ[ t0 ∈ DProcR ] Σ[ t1 ∈ DProcR ] (t′ ≡ Sys t0 t1 × RSys t0 t1)
reach-cons = go rsys-init refl
  where
    go : ∀ {t0 t1 t s t′} → RSys t0 t1 → t ≡ Sys t0 t1 → t ⟹⟨ s ⟩ t′
       → Σ[ u0 ∈ DProcR ] Σ[ u1 ∈ DProcR ] (t′ ≡ Sys u0 u1 × RSys u0 u1)
    go rs refl ⟹-refl         = _ , _ , refl , rs
    go rs refl (⟹-τ  st rest) = let (_ , _ , eq , rs′) = sys-inv rs st in go rs′ eq rest
    go rs refl (⟹-ev st rest) = let (_ , _ , eq , rs′) = sys-inv rs st in go rs′ eq rest

------------------------------------------------------------------------------------
-- §5.6 Every reachable configuration can MOVE.  Nodes in NodeE fire `send` solo;
-- Node1-local fires `receive` solo; otherwise a ring hand-off syncs (the recipient of
-- a forward always has a free slot — that is exactly the non-blocking property).
-- Membership witnesses: `A i .mem (ring)(j,_) = (j≡i) ⊎ (j≡nextN i)`.
-- Node step lemmas: solo deliveries and ring forwards of the pinned held packet.  Packet
-- components are split fzero/fsuc fzero so the offer maps' `_Fin.≟_` / `pkt≟` guards reduce
-- definitionally (Node = Fin 2, so this is finite) and the offer equation is `refl`.  (Ring
-- INPUT offers reduce for ANY value — inputs accept anything — so those are `refl` inline.)
step-recv0 : ∀ a → Node1 n0 (a , n0) ─[ ev (evl (evLabel (Node × Node) receive (n0 , a))) ]─► NodeE n0
step-recv0 fzero        = sVis refl refl
step-recv0 (fsuc fzero) = sVis refl refl
step-recv1 : ∀ a → Node1 n1 (a , n1) ─[ ev (evl (evLabel (Node × Node) receive (n1 , a))) ]─► NodeE n1
step-recv1 fzero        = sVis refl refl
step-recv1 (fsuc fzero) = sVis refl refl
step-fwd0₁ : ∀ a → Node1 n0 (a , n1) ─[ ev (evl (evLabel (Node × (Node × Node)) ring (n1 , (a , n1)))) ]─► NodeE n0
step-fwd0₁ fzero        = sVis refl refl
step-fwd0₁ (fsuc fzero) = sVis refl refl
step-fwd0₂ : ∀ a b q → Node2 n0 (a , b) q ─[ ev (evl (evLabel (Node × (Node × Node)) ring (n1 , (a , b)))) ]─► Node1 n0 q
step-fwd0₂ fzero        fzero        q = sVis refl refl
step-fwd0₂ fzero        (fsuc fzero) q = sVis refl refl
step-fwd0₂ (fsuc fzero) fzero        q = sVis refl refl
step-fwd0₂ (fsuc fzero) (fsuc fzero) q = sVis refl refl
step-fwd1₂ : ∀ c d r → Node2 n1 (c , d) r ─[ ev (evl (evLabel (Node × (Node × Node)) ring (n0 , (c , d)))) ]─► Node1 n1 r
step-fwd1₂ fzero        fzero        r = sVis refl refl
step-fwd1₂ fzero        (fsuc fzero) r = sVis refl refl
step-fwd1₂ (fsuc fzero) fzero        r = sVis refl refl
step-fwd1₂ (fsuc fzero) (fsuc fzero) r = sVis refl refl

enabled : ∀ {t0 t1} → RSys t0 t1
        → Σ[ l ∈ Label (RetOf⁺ (nbNode n0) (nbNode n1 ∷ [])) ] Σ[ t″ ∈ _ ] (Sys t0 t1 ─[ l ]─► t″)
-- node0 = E : send.n0 solo.
enabled r-00       = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
enabled (r-01 q)   = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
enabled (r-02 q r) = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
-- node1 = E : send.n1 solo.
enabled (r-10 p)   = _ , _ , αpar-soloR-step {at = _ , send} {a = n1 , n0} (λ ()) (inj₁ refl) refl refl refl
enabled (r-20 p q) = _ , _ , αpar-soloR-step {at = _ , send} {a = n1 , n0} (λ ()) (inj₁ refl) refl refl refl
-- node0 = Node1-local : receive.n0 solo; node0 = Node1-remote : forward ring.n1 to node1.
enabled (r-11 (a , fzero)      q) =
  let (_ , _ , eqP , bP) = ev-inv (step-recv0 a)
  in _ , _ , αpar-soloL-step {at = _ , receive} {a = n0 , a} refl (λ { (inj₁ ()) ; (inj₂ ()) }) eqP bP refl
enabled (r-11 (a , fsuc fzero) (c , fzero)) =
  let (_ , _ , eqP , bP) = ev-inv (step-fwd0₁ a)
  in _ , _ , αpar-sync-step {at = _ , ring} {a = n1 , (a , n1)} (inj₂ refl) (inj₁ (inj₁ refl)) eqP bP refl refl
enabled (r-11 (a , fsuc fzero) (c , fsuc fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-recv1 c)
  in _ , _ , αpar-soloR-step {at = _ , receive} {a = n1 , c} (λ ()) (inj₁ refl) refl eqQ bQ
-- node0 = Node2 : forward ring.n1; node1 = Node1 free-slot (remote) accepts, else recv.n1 solo.
enabled (r-21 (a , b) q (c , fzero)) =
  let (_ , _ , eqP , bP) = ev-inv (step-fwd0₂ a b q)
  in _ , _ , αpar-sync-step {at = _ , ring} {a = n1 , (a , b)} (inj₂ refl) (inj₁ (inj₁ refl)) eqP bP refl refl
enabled (r-21 (a , b) q (c , fsuc fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-recv1 c)
  in _ , _ , αpar-soloR-step {at = _ , receive} {a = n1 , c} (λ ()) (inj₁ refl) refl eqQ bQ
-- node1 = Node2 : forward ring.n0; node0 = Node1 free-slot (remote) accepts, else recv.n0 solo.
enabled (r-12 (a , fsuc fzero) (c , d) r) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-fwd1₂ c d r)
  in _ , _ , αpar-sync-step {at = _ , ring} {a = n0 , (c , d)} (inj₁ refl) (inj₁ (inj₂ refl)) refl refl eqQ bQ
enabled (r-12 (a , fzero)      (c , d) r) =
  let (_ , _ , eqP , bP) = ev-inv (step-recv0 a)
  in _ , _ , αpar-soloL-step {at = _ , receive} {a = n0 , a} refl (λ { (inj₁ ()) ; (inj₂ ()) }) eqP bP refl

------------------------------------------------------------------------------------
-- §5.7 THE THEOREM: the non-blocking routing ring (N = 2) is DEADLOCK-FREE.
nonBlockingRing-deadlockFree : DeadlockFree nonBlockingRing
nonBlockingRing-deadlockFree = progress⇒deadlockFree nb-progress
  where
    nb-progress : Progress nonBlockingRing
    nb-progress bs with reach-cons (embed∖√ bs)
    ... | (_ , _ , refl , rs) = enabled rs
