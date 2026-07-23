{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the NEGOTIATING store-and-forward routing *tree* (tree3) is
-- DEADLOCK-FREE — the sibling claim to the divergence-freedom FAILURE proved in
-- `CSP.Examples.UCS.Ch4.RoutingTreeNegotiation`.  Machine-readable companion:
--
--   fdr-examples/ucs/chapter04/tree3.csp   (UCS ch. 4, the negotiation tree)
--
-- FDR reports two assertions on the negotiation tree:
--
--   assert Tree                              :[deadlock free]    -- HOLDS  (proved here)
--   assert Tree ∖ diff(Events,{send,receive}) :[divergence free]  -- FAILS (RoutingTreeNegotiation)
--
-- This module proves the FIRST: the *unhidden* `Tree` is DEADLOCK-FREE.  The point of
-- the source is that the tree is "deadlock free but may make no progress": every
-- reachable configuration can take SOME step, but that step may be the endless
-- negotiation self-loop `no.i.(next i r)` between two adjacent busy nodes (the very
-- loop that becomes a τ-divergence once the negotiation channels are hidden).  A `no`
-- exchange IS a move, so `Tree` never deadlocks, even though it need not progress —
-- deadlock-free ≠ divergence-free.
--
-- PINNED offers.  We reuse the EXACT node definitions of `RoutingTreeNegotiation`
-- (imported, not redefined); the forwarding offers there are PINNED to their held
-- packet.  `DeadlockFree` is UNIVERSAL, so we keep them pinned — no value
-- generalisation.
--
-- PROOF APPROACH (the `RoutingTreeSwap` DATA-TAG technique).  Every node is
-- react-headed and STABLE (τ-map ≡ ∅t): no τ/√ transition, so the composite's only
-- moves are VISIBLE — a solo send/receive, or a yes/no/pass SYNC between the two
-- adjacent nodes.  We track each node by a reachable POSITION TAG (empty `e`, full
-- `f p`, awaiting-pass `pin`, sending-pass `pout`), decode tags to processes via
-- `⟦_⟧`, and carry a joint reachability predicate `Reach` with SIX constructors — the
-- reachable occupancy pairs (E,E),(F,E),(E,F),(F,F) plus the two PAIRED pass-handshake
-- states (pout0,pin1),(pin0,pout1) (a `yes` sync moves both nodes at once, so a lone
-- handshake tag is unreachable).  `Reach` is closed under stepping (`sys-inv`) and
-- every `Reach` state can move (`enabled`): an empty node sends solo, a node at its
-- destination receives solo, and two forwarding nodes always `no`-negotiate (the
-- deadlock-free-but-no-progress loop).  `Progress` and `DeadlockFree` follow.
--
-- REDUCTION.  Minimal instance N = 2 (edge 0—1), matching `RoutingTreeNegotiation`.

module CSP.Examples.UCS.Ch4.RoutingTreeNegotiationDeadlockFree where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees
open PTree

open import CSP.Examples.UCS.Ch4.RoutingTreeNegotiation
  using ( NEv; NEv-≟; Node; n0; n1
        ; A; NodeE3; PassInE; NodeF3; PassOutF; node; NProc; RetR; Tree )
open import CSP.Operators NEv-≟
open EventSet

open NEv

open import Semantics.LTS       {E = NEv} {I = ExtI NEv}
open import Semantics.Failures   {E = NEv} {I = ExtI NEv} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock   {E = NEv} {I = ExtI NEv}
  using ( DeadlockFree; _⟹∖√⟨_⟩_; embed∖√ )
open import Semantics.DeadlockDR {E = NEv} {I = ExtI NEv}
  using ( Progress; progress⇒deadlockFree )
open import CSP.Laws.AlphaParallel NEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

------------------------------------------------------------------------------------
-- §1. R-independent event labels.
sendEv : Node → Node → Event
sendEv i d = evLabel (Node × Node) send (i , d)
recvEv : Node → Node → Event
recvEv i s = evLabel (Node × Node) receive (i , s)
passEv : Node → Node → (Node × Node) → Event
passEv f t p = evLabel (Node × (Node × (Node × Node))) pass (f , (t , p))
yesEv : Node → Node → Event
yesEv a b = evLabel (Node × Node) yesc (a , b)
noEv : Node → Node → Event
noEv a b = evLabel (Node × Node) noc (a , b)

------------------------------------------------------------------------------------
-- §2. Node state TAGS (data), decoded to processes by ⟦_⟧.  Indexing the invariant by
-- these disjoint tag constructors (not the raw, non-injective defined terms
-- `NodeE3`/`NodeF3 p`/…) lets the closure proof case-split node states.
--   e     empty (NodeE3)
--   f p   full, holding packet p (NodeF3 p; destination if r≡i else forwarding)
--   pin   awaiting a passed-in packet (PassInE — always from the neighbour)
--   pout  sending a passed-out packet (PassOutF)
data S0 : Set where
  e0   : S0
  f0   : (Node × Node) → S0
  pin0 : S0
  pout0 : (Node × Node) → S0
data S1 : Set where
  e1   : S1
  f1   : (Node × Node) → S1
  pin1 : S1
  pout1 : (Node × Node) → S1

⟦_⟧0 : S0 → NProc
⟦ e0 ⟧0      = NodeE3 n0
⟦ f0 p ⟧0    = NodeF3 n0 p
⟦ pin0 ⟧0    = PassInE n0 n1
⟦ pout0 p ⟧0 = PassOutF n0 p
⟦_⟧1 : S1 → NProc
⟦ e1 ⟧1      = NodeE3 n1
⟦ f1 p ⟧1    = NodeF3 n1 p
⟦ pin1 ⟧1    = PassInE n1 n0
⟦ pout1 p ⟧1 = PassOutF n1 p

-- Every node is react-headed (never `ret`) and stable (τ-map ≡ ∅t), so no τ/√ step.
noret0 : ∀ (x : S0) {r} → ⟦ x ⟧0 .force ≡ ret r → ⊥
noret0 e0 ()
noret0 (f0 (s , r)) ()
noret0 pin0 ()
noret0 (pout0 (s , r)) ()
noτ0 : ∀ (x : S0) {t′} → ⟦ x ⟧0 ─[ τ ]─► t′ → ⊥
noτ0 e0             (sSil eq)      = case eq of λ ()
noτ0 e0             (sTau refl br) = case br of λ ()
noτ0 (f0 (s , r))   (sSil eq)      = case eq of λ ()
noτ0 (f0 (s , r))   (sTau refl br) = case br of λ ()
noτ0 pin0           (sSil eq)      = case eq of λ ()
noτ0 pin0           (sTau refl br) = case br of λ ()
noτ0 (pout0 (s , r))(sSil eq)      = case eq of λ ()
noτ0 (pout0 (s , r))(sTau refl br) = case br of λ ()
noτ1 : ∀ (y : S1) {t′} → ⟦ y ⟧1 ─[ τ ]─► t′ → ⊥
noτ1 e1             (sSil eq)      = case eq of λ ()
noτ1 e1             (sTau refl br) = case br of λ ()
noτ1 (f1 (s , r))   (sSil eq)      = case eq of λ ()
noτ1 (f1 (s , r))   (sTau refl br) = case br of λ ()
noτ1 pin1           (sSil eq)      = case eq of λ ()
noτ1 pin1           (sTau refl br) = case br of λ ()
noτ1 (pout1 (s , r))(sSil eq)      = case eq of λ ()
noτ1 (pout1 (s , r))(sTau refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §3. Per-node visible-step transition relations over the state TAGS.
data T0 : S0 → S0 → Event → Set₁ where
  t0-send        : ∀ dst → T0 e0 (f0 (n0 , dst))               (sendEv n0 dst)
  t0-yesin       :         T0 e0 pin0                          (yesEv n1 n0)
  t0-passin      : ∀ p   → T0 pin0 (f0 p)                      (passEv n1 n0 p)
  t0-recv        : ∀ s src → T0 (f0 (s , n0)) e0               (recvEv n0 src)
  t0-absorb-dest : ∀ s   → T0 (f0 (s , n0)) (f0 (s , n0))      (noEv n1 n0)
  t0-yesout      : ∀ s   → T0 (f0 (s , n1)) (pout0 (s , n1))   (yesEv n0 n1)
  t0-absorb-fwd  : ∀ s   → T0 (f0 (s , n1)) (f0 (s , n1))      (noEv n1 n0)
  t0-decline     : ∀ s   → T0 (f0 (s , n1)) (f0 (s , n1))      (noEv n0 n1)
  t0-passout     : ∀ s r p → T0 (pout0 (s , r)) e0             (passEv n0 n1 p)

data T1 : S1 → S1 → Event → Set₁ where
  t1-send        : ∀ dst → T1 e1 (f1 (n1 , dst))               (sendEv n1 dst)
  t1-yesin       :         T1 e1 pin1                          (yesEv n0 n1)
  t1-passin      : ∀ p   → T1 pin1 (f1 p)                      (passEv n0 n1 p)
  t1-recv        : ∀ s src → T1 (f1 (s , n1)) e1               (recvEv n1 src)
  t1-absorb-dest : ∀ s   → T1 (f1 (s , n1)) (f1 (s , n1))      (noEv n0 n1)
  t1-yesout      : ∀ s   → T1 (f1 (s , n0)) (pout1 (s , n0))   (yesEv n1 n0)
  t1-absorb-fwd  : ∀ s   → T1 (f1 (s , n0)) (f1 (s , n0))      (noEv n0 n1)
  t1-decline     : ∀ s   → T1 (f1 (s , n0)) (f1 (s , n0))      (noEv n1 n0)
  t1-passout     : ∀ s r p → T1 (pout1 (s , r)) e1             (passEv n1 n0 p)

-- node0 visible-step inversion.  (n0 = fzero; nb n0 = n1; next n0 _ = n1.)
n0-inv : ∀ {t′ e} (x : S0) → ⟦ x ⟧0 ─[ ev (evl e) ]─► t′
       → Σ[ x′ ∈ S0 ] (t′ ≡ ⟦ x′ ⟧0 × T0 x x′ e)
n0-inv e0 (sVis {at = _ , send} {a = fzero , b}      refl br) = f0 (n0 , b) , sym (just-injective br) , t0-send b
n0-inv e0 (sVis {at = _ , send} {a = fsuc fzero , b} refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , receive}                   refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , pass}                      refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , yesc} {a = fsuc fzero , fzero} refl br) = pin0 , sym (just-injective br) , t0-yesin
n0-inv e0 (sVis {at = _ , yesc} {a = fzero , fzero}      refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , yesc} {a = _ , fsuc fzero}     refl br) = case br of λ ()
n0-inv e0 (sVis {at = _ , noc}                       refl br) = case br of λ ()

n0-inv pin0 (sVis {at = _ , send}    refl br) = case br of λ ()
n0-inv pin0 (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv pin0 (sVis {at = _ , yesc}    refl br) = case br of λ ()
n0-inv pin0 (sVis {at = _ , noc}     refl br) = case br of λ ()
n0-inv pin0 (sVis {at = _ , pass} {a = fsuc fzero , fzero , p}      refl br) = f0 p , sym (just-injective br) , t0-passin p
n0-inv pin0 (sVis {at = _ , pass} {a = fzero , to , p}             refl br) = case br of λ ()
n0-inv pin0 (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()

n0-inv (f0 (s , fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , receive} {a = fzero , b}      refl br) with b Fin.≟ s
... | yes _ = e0 , sym (just-injective br) , t0-recv s b
... | no  _ = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , receive} {a = fsuc fzero , b} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , yesc} refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fzero} refl br) = f0 (s , n0) , sym (just-injective br) , t0-absorb-dest s
n0-inv (f0 (s , fzero)) (sVis {at = _ , noc} {a = fzero , fzero}      refl br) = case br of λ ()
n0-inv (f0 (s , fzero)) (sVis {at = _ , noc} {a = _ , fsuc fzero}     refl br) = case br of λ ()

n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , yesc} {a = fzero , fsuc fzero} refl br) = pout0 (s , n1) , sym (just-injective br) , t0-yesout s
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , yesc} {a = fzero , fzero}      refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , yesc} {a = fsuc fzero , b}     refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fzero}      refl br) = f0 (s , n1) , sym (just-injective br) , t0-absorb-fwd s
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fzero , fzero}           refl br) = case br of λ ()
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fzero , fsuc fzero}      refl br) = f0 (s , n1) , sym (just-injective br) , t0-decline s
n0-inv (f0 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()

n0-inv (pout0 (s , r)) (sVis {at = _ , send}    refl br) = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , receive} refl br) = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , yesc}    refl br) = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , noc}     refl br) = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , pass} {a = fzero , fsuc fzero , s′ , r′} refl br) with s′ Fin.≟ s
... | no  _ = case br of λ ()
... | yes _ with r′ Fin.≟ r
...   | yes _ = e0 , sym (just-injective br) , t0-passout s r (s′ , r′)
...   | no  _ = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , pass} {a = fzero , fzero , p}     refl br) = case br of λ ()
n0-inv (pout0 (s , r)) (sVis {at = _ , pass} {a = fsuc fzero , to , p}   refl br) = case br of λ ()

-- node1 visible-step inversion.  (n1 = fsuc fzero; nb n1 = n0; next n1 _ = n0.)
n1-inv : ∀ {t′ e} (y : S1) → ⟦ y ⟧1 ─[ ev (evl e) ]─► t′
       → Σ[ y′ ∈ S1 ] (t′ ≡ ⟦ y′ ⟧1 × T1 y y′ e)
n1-inv e1 (sVis {at = _ , send} {a = fsuc fzero , b} refl br) = f1 (n1 , b) , sym (just-injective br) , t1-send b
n1-inv e1 (sVis {at = _ , send} {a = fzero , b}      refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , receive}                   refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , pass}                      refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , yesc} {a = fzero , fsuc fzero}      refl br) = pin1 , sym (just-injective br) , t1-yesin
n1-inv e1 (sVis {at = _ , yesc} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , yesc} {a = _ , fzero}              refl br) = case br of λ ()
n1-inv e1 (sVis {at = _ , noc}                       refl br) = case br of λ ()

n1-inv pin1 (sVis {at = _ , send}    refl br) = case br of λ ()
n1-inv pin1 (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv pin1 (sVis {at = _ , yesc}    refl br) = case br of λ ()
n1-inv pin1 (sVis {at = _ , noc}     refl br) = case br of λ ()
n1-inv pin1 (sVis {at = _ , pass} {a = fzero , fsuc fzero , p}      refl br) = f1 p , sym (just-injective br) , t1-passin p
n1-inv pin1 (sVis {at = _ , pass} {a = fsuc fzero , to , p}         refl br) = case br of λ ()
n1-inv pin1 (sVis {at = _ , pass} {a = fzero , fzero , p}           refl br) = case br of λ ()

n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , receive} {a = fsuc fzero , b} refl br) with b Fin.≟ s
... | yes _ = e1 , sym (just-injective br) , t1-recv s b
... | no  _ = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , receive} {a = fzero , b} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , yesc} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fzero , fsuc fzero} refl br) = f1 (s , n1) , sym (just-injective br) , t1-absorb-dest s
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()
n1-inv (f1 (s , fsuc fzero)) (sVis {at = _ , noc} {a = _ , fzero} refl br) = case br of λ ()

n1-inv (f1 (s , fzero)) (sVis {at = _ , send} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , pass} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , yesc} {a = fsuc fzero , fzero} refl br) = pout1 (s , n0) , sym (just-injective br) , t1-yesout s
n1-inv (f1 (s , fzero)) (sVis {at = _ , yesc} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , yesc} {a = fzero , b} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , noc} {a = fzero , fsuc fzero}      refl br) = f1 (s , n0) , sym (just-injective br) , t1-absorb-fwd s
n1-inv (f1 (s , fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fsuc fzero} refl br) = case br of λ ()
n1-inv (f1 (s , fzero)) (sVis {at = _ , noc} {a = fsuc fzero , fzero}      refl br) = f1 (s , n0) , sym (just-injective br) , t1-decline s
n1-inv (f1 (s , fzero)) (sVis {at = _ , noc} {a = fzero , fzero}           refl br) = case br of λ ()

n1-inv (pout1 (s , r)) (sVis {at = _ , send}    refl br) = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , receive} refl br) = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , yesc}    refl br) = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , noc}     refl br) = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , pass} {a = fsuc fzero , fzero , s′ , r′} refl br) with s′ Fin.≟ s
... | no  _ = case br of λ ()
... | yes _ with r′ Fin.≟ r
...   | yes _ = e1 , sym (just-injective br) , t1-passout s r (s′ , r′)
...   | no  _ = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , pass} {a = fsuc fzero , fsuc fzero , p} refl br) = case br of λ ()
n1-inv (pout1 (s , r)) (sVis {at = _ , pass} {a = fzero , to , p}              refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- §4. The joint reachability predicate over the state tags: the SIX reachable
-- occupancy pairs.  The pass-handshake pairs (pout0,pin1)/(pin0,pout1) are always
-- PAIRED — a lone handshake tag is unreachable (a `yes` sync moves both nodes).
data Reach : S0 → S1 → Set where
  rEE  :             Reach e0         e1
  rFE  : ∀ p       → Reach (f0 p)     e1
  rEF  : ∀ q       → Reach e0         (f1 q)
  rFF  : ∀ p q     → Reach (f0 p)     (f1 q)
  rP01 : ∀ p       → Reach (pout0 p)  pin1     -- node0 sending pass, node1 receiving
  rP10 : ∀ q       → Reach pin0       (pout1 q) -- node0 receiving pass, node1 sending

-- The right-hand alphabet (the folded singleton tail) and the composite state.
B1 : EventSet
B1 = unionα (node n1 ∷ [])

Sys : NProc → NProc → PTree NEv (ExtI NEv) RetR
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

Sys⟦_,_⟧ : S0 → S1 → PTree NEv (ExtI NEv) RetR
Sys⟦ x , y ⟧ = Sys ⟦ x ⟧0 ⟦ y ⟧1

------------------------------------------------------------------------------------
-- §5. Single-step inversion: Reach is closed under stepping.
soloL : ∀ {x y t0′} {X} {ee : NEv X} {a : X}
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
soloL reach ¬pB p0 | _ , refl , t0-yesin         = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-passin p      = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-absorb-dest s = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-yesout s      = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
soloL reach ¬pB p0 | _ , refl , t0-absorb-fwd s  = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
soloL reach ¬pB p0 | _ , refl , t0-decline s     = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
soloL reach ¬pB p0 | _ , refl , t0-passout s r p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))

soloR : ∀ {x y t1′} {X} {ee : NEv X} {a : X}
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
soloR reach ¬pA q1 | _ , refl , t1-yesin         = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-passin p      = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-absorb-dest s = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-yesout s      = ⊥-elim (¬pA (inj₂ refl))
soloR reach ¬pA q1 | _ , refl , t1-absorb-fwd s  = ⊥-elim (¬pA (inj₁ refl))
soloR reach ¬pA q1 | _ , refl , t1-decline s     = ⊥-elim (¬pA (inj₂ refl))
soloR reach ¬pA q1 | _ , refl , t1-passout s r p = ⊥-elim (¬pA (inj₂ refl))

sync : ∀ {x y t0′ t1′} {X} {ee : NEv X} {a : X}
     → Reach x y
     → ⟦ x ⟧0 ─[ ev (evl (evLabel X ee a)) ]─► t0′
     → ⟦ y ⟧1 ─[ ev (evl (evLabel X ee a)) ]─► t1′
     → Σ[ x′ ∈ S0 ] Σ[ y′ ∈ S1 ] (Sys t0′ t1′ ≡ Sys⟦ x′ , y′ ⟧ × Reach x′ y′)
sync {x} {y} reach p0 q1 with n0-inv x p0 | n1-inv y q1
-- yes handshake: an empty node accepts a neighbour's proposal.
... | _ , refl , t0-yesin           | _ , refl , t1-yesout s′       = _ , _ , refl , rP10 (s′ , n0)
... | _ , refl , t0-yesout s        | _ , refl , t1-yesin           = _ , _ , refl , rP01 (s , n1)
-- no negotiation: the deadlock-free-but-no-progress self-loops.
... | _ , refl , t0-absorb-dest s   | _ , refl , t1-decline s′      = _ , _ , refl , rFF (s , n0) (s′ , n0)
... | _ , refl , t0-absorb-fwd s    | _ , refl , t1-decline s′      = _ , _ , refl , rFF (s , n1) (s′ , n0)
... | _ , refl , t0-decline s       | _ , refl , t1-absorb-dest s′  = _ , _ , refl , rFF (s , n1) (s′ , n1)
... | _ , refl , t0-decline s       | _ , refl , t1-absorb-fwd s′   = _ , _ , refl , rFF (s , n1) (s′ , n0)
-- pass hand-off: the sender emits, the receiver takes the packet.
... | _ , refl , t0-passin p        | _ , refl , t1-passout s r p′  = _ , _ , refl , rFE p
... | _ , refl , t0-passout s r p   | _ , refl , t1-passin p′       = _ , _ , refl , rEF p

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
-- §6. Reachability closure: every ⟹-reachable state is a reachable Reach config.
tree≡′ : Tree ≡ Sys⟦ e0 , e1 ⟧
tree≡′ = refl

reach-cons : ∀ {s t′} → Tree ⟹⟨ s ⟩ t′
           → Σ[ x ∈ S0 ] Σ[ y ∈ S1 ] (t′ ≡ Sys⟦ x , y ⟧ × Reach x y)
reach-cons = go rEE refl
  where
    go : ∀ {x y t s t′} → Reach x y → t ≡ Sys⟦ x , y ⟧ → t ⟹⟨ s ⟩ t′
       → Σ[ u ∈ S0 ] Σ[ v ∈ S1 ] (t′ ≡ Sys⟦ u , v ⟧ × Reach u v)
    go reach refl ⟹-refl         = _ , _ , refl , reach
    go reach refl (⟹-τ  st rest) = let (_ , _ , eq , reach′) = sys-inv reach st in go reach′ eq rest
    go reach refl (⟹-ev st rest) = let (_ , _ , eq , reach′) = sys-inv reach st in go reach′ eq rest

------------------------------------------------------------------------------------
-- §7. Every reachable configuration can MOVE.  Step helpers split the Fin-2 packet
-- components so the offer maps' equality guards reduce definitionally.
step-recv0 : ∀ s → NodeF3 n0 (s , n0) ─[ ev (evl (recvEv n0 s)) ]─► NodeE3 n0
step-recv0 fzero        = sVis refl refl
step-recv0 (fsuc fzero) = sVis refl refl
step-recv1 : ∀ s → NodeF3 n1 (s , n1) ─[ ev (evl (recvEv n1 s)) ]─► NodeE3 n1
step-recv1 fzero        = sVis refl refl
step-recv1 (fsuc fzero) = sVis refl refl
step-passout0 : ∀ s r → PassOutF n0 (s , r) ─[ ev (evl (passEv n0 n1 (s , r))) ]─► NodeE3 n0
step-passout0 fzero        fzero        = sVis refl refl
step-passout0 fzero        (fsuc fzero) = sVis refl refl
step-passout0 (fsuc fzero) fzero        = sVis refl refl
step-passout0 (fsuc fzero) (fsuc fzero) = sVis refl refl
step-passout1 : ∀ s r → PassOutF n1 (s , r) ─[ ev (evl (passEv n1 n0 (s , r))) ]─► NodeE3 n1
step-passout1 fzero        fzero        = sVis refl refl
step-passout1 fzero        (fsuc fzero) = sVis refl refl
step-passout1 (fsuc fzero) fzero        = sVis refl refl
step-passout1 (fsuc fzero) (fsuc fzero) = sVis refl refl

enabled : ∀ {x y} → Reach x y
        → Σ[ l ∈ Label RetR ] Σ[ t″ ∈ _ ] (Sys⟦ x , y ⟧ ─[ l ]─► t″)
-- an empty node sends solo.
enabled rEE           = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
enabled (rFE (s , r)) = _ , _ , αpar-soloR-step {at = _ , send} {a = n1 , n0} (λ ()) (inj₁ refl) refl refl refl
enabled (rEF (s , r)) = _ , _ , αpar-soloL-step {at = _ , send} {a = n0 , n0} refl (λ { (inj₁ ()) ; (inj₂ ()) }) refl refl refl
-- (F,F): a node at its destination delivers; two forwarders `no`-negotiate (the loop).
enabled (rFF (s , fzero) (qt , qr)) =
  let (_ , _ , eqP , bP) = ev-inv (step-recv0 s)
  in _ , _ , αpar-soloL-step {at = _ , receive} {a = n0 , s} refl (λ { (inj₁ ()) ; (inj₂ ()) }) eqP bP refl
enabled (rFF (s , fsuc fzero) (t , fsuc fzero)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-recv1 t)
  in _ , _ , αpar-soloR-step {at = _ , receive} {a = n1 , t} (λ ()) (inj₁ refl) refl eqQ bQ
enabled (rFF (s , fsuc fzero) (t , fzero)) =
  _ , _ , αpar-sync-step {at = _ , noc} {a = n0 , n1} (inj₁ refl) (inj₁ (inj₂ refl)) refl refl refl refl
-- handshake states complete via the pending pass.
enabled (rP01 (s , r)) =
  let (_ , _ , eqP , bP) = ev-inv (step-passout0 s r)
  in _ , _ , αpar-sync-step {at = _ , pass} {a = n0 , (n1 , (s , r))} (inj₁ refl) (inj₁ (inj₂ refl)) eqP bP refl refl
enabled (rP10 (s , r)) =
  let (_ , _ , eqQ , bQ) = ev-inv (step-passout1 s r)
  in _ , _ , αpar-sync-step {at = _ , pass} {a = n1 , (n0 , (s , r))} (inj₂ refl) (inj₁ (inj₁ refl)) refl refl eqQ bQ

------------------------------------------------------------------------------------
-- §8. THE THEOREM: the negotiation routing tree (tree3, N = 2) is DEADLOCK-FREE
-- (though NOT divergence-free — see `RoutingTreeNegotiation`).
tree3-deadlockFree : DeadlockFree Tree
tree3-deadlockFree = progress⇒deadlockFree tr-progress
  where
    tr-progress : Progress Tree
    tr-progress bs with reach-cons (embed∖√ bs)
    ... | (_ , _ , refl , reach) = enabled reach
