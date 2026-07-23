{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the NON-BLOCKING store-and-forward routing ring is
-- DIVERGENCE-FREE once its internal `ring` channel is hidden.  Machine-readable
-- companion file:
--
--   fdr-examples/ucs/chapter04/nonblock.csp   (UCS ch. 4 §4.2, the non-blocking ring)
--
-- FDR reports the HOLDING assert
--
--   assert RingH :[divergence free]      -- HOLDS ("cannot diverge at all")
--
-- with `RingH = Ring \ {| ring |}` the ring with its internal forwarding channel
-- hidden.  This module proves `nonBlockingRing-divergenceFree : DivergenceFree RingH`.
--
-- REUSE OF THE COMMITTED MODEL.  We import the committed N = 2 non-blocking ring
-- verbatim from `CSP.Examples.UCS.Ch4.RoutingRingNonBlocking` — `Node = Fin 2`,
-- `nextN`, the event type `REv` (`send`/`receive`/`ring`), the per-node alphabet
-- `A`, the two-slot store-and-forward node `NodeE`/`Node1`/`Node2` (offers PINNED:
-- forwards fire only at the SPECIFIC held packet, deliveries at the destination),
-- and `nonBlockingRing = ∥ₐ⁺ (nbNode n0) (nbNode n1 ∷ [])`.  The offers are PINNED,
-- NOT payload-generalised: `DivergenceFree` is a UNIVERSAL claim and an
-- over-approximated forward would be UNSOUND.
--
-- CONTRAST WITH THE LIVELOCKS (`GeneralNetworkLivelock`, the tokring).  The naive
-- token-ring circulates an EMPTY token forever, so hiding `ring` produces an
-- infinite τ-loop (livelock).  The non-blocking ring has NO empty-token
-- circulation: the ONLY internal action is a `ring` sync that forwards a HELD
-- packet ONE HOP toward its destination.  At N = 2 a single hop delivers the
-- packet to its destination node (whence the only further move is a VISIBLE
-- `receive`, not a hidden τ).  So the internal τ-DAG is ACYCLIC and terminates.
--
-- PROOF (acyclic single-hop τ-DAG, mirroring `General4DivFree`).  Every node is
-- react-headed and STABLE (τ-map ≡ ∅t), so `Cfg` (the parallel of the two nodes)
-- has NO τ / √ step; every τ of `Cfg ∖ ring` is a HIDDEN `ring` sync
-- (`Hide-τ-elim`).  We track the joint config by state TAGS (`e` empty / `o p`
-- one packet / `w p q` two packets), invert a composite visible step
-- (`sys-inv-vis`: solo `send`/`receive` or a `ring` sync between the two nodes),
-- and carry a per-node validity predicate `Held` (a `Node2`-slot-1 packet is
-- always remote).  The measure `μ` = total remaining forward-hops of the in-flight
-- packets (1 per held packet whose holder is not its destination, else 0).  Every
-- hidden `ring` sync moves a held packet from a non-destination holder to its
-- destination node, strictly decreasing `μ`; `¬ Diverges` then follows by
-- well-founded recursion on `μ`, and a `⟹∖√` reach-walk confines every reachable
-- state to a config, giving `DivergenceFree RingH`.

module CSP.Examples.UCS.Ch4.RoutingRingNonBlockingDivFree where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties
  using (+-comm; +-assoc; +-identityʳ; +-monoˡ-<; ≤-trans; ≤-pred; n<1+n)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import Process_Trees
open PTree

open import CSP.Examples.UCS.Ch4.RoutingRingNonBlocking
  using ( Node; n0; n1; nextN; REv; send; receive; ring; REv-≟; A; pkt≟
        ; NodeE; Node1; Node2; nonBlockingRing; nbNode; DProcR; Sys )

open import CSP.Operators REv-≟
open EventSet

open import Semantics.LTS        {E = REv} {I = ExtI REv} hiding (Diverges)
open import Semantics.Deadlock   {E = REv} {I = ExtI REv}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)
open import Semantics.DRBisim    {E = REv} {I = ExtI REv} using (Diverges)
open import Semantics.DeadlockDR {E = REv} {I = ExtI REv} using (DivergenceFree)
open import CSP.Laws.Traces.TraceLawsHide REv-≟
  using (Hide-τ-elim; HideτR; hτP; hτH; Hide-ev-elim; HideevR; heV; he√)
open import CSP.Laws.AlphaParallel REv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )

-------------------------------------------------------------------------------------
-- §1. Hiding the internal `ring` channel.  `ringES` is ⊤ on every `ring.*`,
-- ⊥ on `send`/`receive` — the channel-level set `{| ring |}`.
-------------------------------------------------------------------------------------

ringES-cs : AnyTypes REv → Set
ringES-cs (_ , send)    = ⊥
ringES-cs (_ , receive) = ⊥
ringES-cs (_ , ring)    = ⊤

ringES-dec : (at : AnyTypes REv) → Dec (ringES-cs at)
ringES-dec (_ , send)    = no (λ z → z)
ringES-dec (_ , receive) = no (λ z → z)
ringES-dec (_ , ring)    = yes tt

ringES : EventSet
ringES = chanSet ringES-cs ringES-dec

RingH : PTree REv (ExtI REv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
RingH = nonBlockingRing ∖ ringES

-------------------------------------------------------------------------------------
-- §2. Config tags and the composite.  A node is `e` (empty), `o p` (holding one
-- packet), or `w p q` (holding two).  `Cfg x y` is the parallel of the two nodes.
-------------------------------------------------------------------------------------

data St : Set where
  e : St
  o : (Node × Node) → St
  w : (Node × Node) → (Node × Node) → St

nd : Node → St → DProcR
nd i e       = NodeE i
nd i (o p)   = Node1 i p
nd i (w p q) = Node2 i p q

Cfg : St → St → PTree REv (ExtI REv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
Cfg x y = Sys (nd n0 x) (nd n1 y)

H : St → St → PTree REv (ExtI REv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
H x y = Cfg x y ∖ ringES

-- R-independent event labels.
sendEv : Node → Node → Event
sendEv i dst = evLabel (Node × Node) send (i , dst)
recvEv : Node → Node → Event
recvEv i s = evLabel (Node × Node) receive (i , s)
ringEv : Node → (Node × Node) → Event
ringEv j p = evLabel (Node × (Node × Node)) ring (j , p)

-------------------------------------------------------------------------------------
-- §3. Per-node validity: a `Node2` (`w`) slot-1 packet is always REMOTE (its dest
-- differs from the holder).  Reachable by construction — see `sys-inv-vis`.
-------------------------------------------------------------------------------------

data Held : Node → St → Set where
  he : ∀ {i}         → Held i e
  ho : ∀ {i} p       → Held i (o p)
  hw : ∀ {i a b q}   → ¬ (i ≡ b) → Held i (w (a , b) q)

held-w : ∀ {i a b q} → Held i (w (a , b) q) → ¬ (i ≡ b)
held-w (hw ¬e) = ¬e

-------------------------------------------------------------------------------------
-- §4. The measure `μ`: total remaining forward-hops of the in-flight packets.  At
-- N = 2, a packet with dest `b` held at node `i` is 0 hops away iff `b ≡ i`, else 1.
-------------------------------------------------------------------------------------

atd : Node → Node → ℕ          -- atd i b : hops of a dest-`b` packet held at node `i`
atd fzero        fzero        = 0
atd fzero        (fsuc fzero) = 1
atd (fsuc fzero) fzero        = 1
atd (fsuc fzero) (fsuc fzero) = 0

hop : Node → (Node × Node) → ℕ
hop i (_ , b) = atd i b

μnode : Node → St → ℕ
μnode i e       = 0
μnode i (o p)   = hop i p
μnode i (w p q) = hop i p + hop i q

μ : St → St → ℕ
μ x y = μnode n0 x + μnode n1 y

-- A single hop toward the destination strictly decreases the packet's hop-count.
hopdec : ∀ i a b → ¬ (i ≡ b) → hop (nextN i) (a , b) < hop i (a , b)
hopdec fzero        a fzero        ¬e = ⊥-elim (¬e refl)
hopdec fzero        a (fsuc fzero) ¬e = s≤s z≤n
hopdec (fsuc fzero) a fzero        ¬e = s≤s z≤n
hopdec (fsuc fzero) a (fsuc fzero) ¬e = ⊥-elim (¬e refl)

-- `hidden ee` — is the event an internal (hidden) `ring`?
hidden : Event → Set
hidden (evLabel _ send    _) = ⊥
hidden (evLabel _ receive _) = ⊥
hidden (evLabel _ ring    _) = ⊤

-------------------------------------------------------------------------------------
-- §5. Per-node steps.  Forwards (`ns-fwd-1`/`ns-fwd-2`) are PINNED (the offer's
-- `pkt≟`/`Fin.≟` guards pin the event to the held packet and to index `nextN i`);
-- `ns-in-e`/`ns-in-1`/`ns-send` are genuine inputs/injections.
-------------------------------------------------------------------------------------

data NStep (i : Node) : St → St → Event → Set where
  ns-send  : ∀ dst   → NStep i e (o (i , dst)) (sendEv i dst)
  ns-in-e  : ∀ p     → NStep i e (o p) (ringEv i p)
  ns-recv  : ∀ a     → NStep i (o (a , i)) e (recvEv i a)
  ns-in-1  : ∀ a b p → ¬ (i ≡ b) → NStep i (o (a , b)) (w (a , b) p) (ringEv i p)
  ns-fwd-1 : ∀ a b   → ¬ (i ≡ b) → NStep i (o (a , b)) e (ringEv (nextN i) (a , b))
  ns-fwd-2 : ∀ a b q → NStep i (w (a , b) q) (o q) (ringEv (nextN i) (a , b))

node-inv : ∀ i x {t′} {ee : Event} → nd i x ─[ ev (evl ee) ]─► t′
         → Σ[ x′ ∈ St ] (t′ ≡ nd i x′ × NStep i x x′ ee)
-- empty node
node-inv i e (sVis {at = _ , send} {a = j , dst} refl br) with j Fin.≟ i
... | yes refl = o (i , dst) , sym (just-injective br) , ns-send dst
... | no  _    = case br of λ ()
node-inv i e (sVis {at = _ , receive} refl br) = case br of λ ()
node-inv i e (sVis {at = _ , ring} {a = j , p} refl br) with j Fin.≟ i
... | yes refl = o p , sym (just-injective br) , ns-in-e p
... | no  _    = case br of λ ()
-- holding one packet: o (a , b)
node-inv i (o (a , b)) (sVis {at = _ , send} refl br) = case br of λ ()
node-inv i (o (a , b)) (sVis {at = _ , receive} {a = j , src} refl br) with i Fin.≟ b
... | no  _ = case br of λ ()
... | yes refl with j Fin.≟ i
...   | no  _ = case br of λ ()
...   | yes refl with src Fin.≟ a
...     | no  _ = case br of λ ()
...     | yes refl = e , sym (just-injective br) , ns-recv a
node-inv i (o (a , b)) (sVis {at = _ , ring} {a = j , p} refl br) with i Fin.≟ b
... | yes _ = case br of λ ()
... | no ¬ib with j Fin.≟ i
...   | yes refl = w (a , b) p , sym (just-injective br) , ns-in-1 a b p ¬ib
...   | no  _ with j Fin.≟ nextN i
...     | no  _ = case br of λ ()
...     | yes refl with pkt≟ p (a , b)
...       | no  _ = case br of λ ()
...       | yes refl = e , sym (just-injective br) , ns-fwd-1 a b ¬ib
-- holding two packets: w (a , b) q
node-inv i (w (a , b) q) (sVis {at = _ , send} refl br) = case br of λ ()
node-inv i (w (a , b) q) (sVis {at = _ , receive} refl br) = case br of λ ()
node-inv i (w (a , b) q) (sVis {at = _ , ring} {a = j , p} refl br) with j Fin.≟ nextN i
... | no  _ = case br of λ ()
... | yes refl with pkt≟ p (a , b)
...   | no  _ = case br of λ ()
...   | yes refl = o q , sym (just-injective br) , ns-fwd-2 a b q

-------------------------------------------------------------------------------------
-- §6. Node stability: react-headed, no τ / no √.
-------------------------------------------------------------------------------------

noτ : ∀ i s {t′} → nd i s ─[ τ ]─► t′ → ⊥
noτ i e       (sSil eq)      = case eq of λ ()
noτ i e       (sTau refl br) = case br of λ ()
noτ i (o p)   (sSil eq)      = case eq of λ ()
noτ i (o p)   (sTau refl br) = case br of λ ()
noτ i (w p q) (sSil eq)      = case eq of λ ()
noτ i (w p q) (sTau refl br) = case br of λ ()

noret : ∀ i s {r} → nd i s .force ≡ ret r → ⊥
noret i e       ()
noret i (o p)   ()
noret i (w p q) ()

sys-noτ : ∀ x y {t} → Cfg x y ─[ τ ]─► t → ⊥
sys-noτ x y st with αpar-τ-step-inv st
... | inj₁ (_ , p0τ , _) = noτ n0 x p0τ
... | inj₂ (_ , q1τ , _) = noτ n1 y q1τ

sys-noret : ∀ x y {r} → Cfg x y .force ≡ ret r → ⊥
sys-noret x y feq with αpar-√-step-inv feq
... | v√ p0 _ = noret n0 x p0

-------------------------------------------------------------------------------------
-- §7. Composite visible-step inversion.  A step of `Cfg x y` is a solo
-- `send`/`receive` (μ unconstrained: send/receive are NOT hidden) or a `ring` sync
-- (hidden), which is a single-hop delivery strictly DECREASING `μ`.  `Held` is
-- preserved (closed under stepping).
-------------------------------------------------------------------------------------

-- rearrange `X + K ≡ μ'`, `Y + K ≡ μ`, `X < Y` into `μ' < μ`.
shuffle : ∀ {X Y} K {M' M : ℕ} → X < Y → X + K ≡ M' → Y + K ≡ M → M' < M
shuffle K core eq' eq = subst₂ _<_ eq' eq (+-monoˡ-< K core)

sys-inv-vis : ∀ x y {t′} {ee : Event} → Held n0 x → Held n1 y
  → Cfg x y ─[ ev (evl ee) ]─► t′
  → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ]
      (t′ ≡ Cfg x′ y′ × Held n0 x′ × Held n1 y′ × (hidden ee → μ x′ y′ < μ x y))
sys-inv-vis x y hx hy (sVis feq br) with αpar-vis-step-inv feq br
-- ── node0 solo: only send/receive; ring events are in B1 (¬pB) ──────────────────
... | vSoloL pA ¬pB p0 with node-inv n0 x p0
...   | o (n0 , dst) , refl , ns-send dst = o (n0 , dst) , y , refl , ho _ , hy , λ ()
...   | e , refl , ns-recv a              = e , y , refl , he , hy , λ ()
...   | o p , refl , ns-in-e p            = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...   | w (a , b) p , refl , ns-in-1 a b p ¬ib = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...   | e , refl , ns-fwd-1 a b ¬ib       = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...   | o q , refl , ns-fwd-2 a b q       = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
-- ── node1 solo: only send/receive; ring events are in A n0 (¬pA) ─────────────────
sys-inv-vis x y hx hy (sVis feq br) | vSoloR ¬pA pB q1 with node-inv n1 y q1
...   | o (n1 , dst) , refl , ns-send dst = x , o (n1 , dst) , refl , hx , ho _ , λ ()
...   | e , refl , ns-recv a              = x , e , refl , hx , he , λ ()
...   | o p , refl , ns-in-e p            = ⊥-elim (¬pA (inj₂ refl))
...   | w (a , b) p , refl , ns-in-1 a b p ¬ib = ⊥-elim (¬pA (inj₂ refl))
...   | e , refl , ns-fwd-1 a b ¬ib       = ⊥-elim (¬pA (inj₁ refl))
...   | o q , refl , ns-fwd-2 a b q       = ⊥-elim (¬pA (inj₁ refl))
-- ── node0 ↔ node1 `ring` sync (single-hop delivery): μ strictly decreases ────────
sys-inv-vis x y hx hy (sVis feq br) | vSync pA pB p0 q1
  with node-inv n0 x p0 | node-inv n1 y q1
-- forwarder = node1 (to nextN n1 = n0); input = node0
...   | o p , refl , ns-in-e p           | e , refl , ns-fwd-1 c d ¬n1d =
        o (c , d) , e , refl , ho _ , he ,
          λ _ → shuffle 0 (hopdec n1 c d ¬n1d) refl (+-identityʳ _)
...   | o p , refl , ns-in-e p           | o q , refl , ns-fwd-2 c d q =
        o (c , d) , o q , refl , ho _ , ho _ ,
          λ _ → shuffle (hop n1 q) (hopdec n1 c d (held-w hy)) refl refl
...   | w (a , b) p , refl , ns-in-1 a b p ¬n0b | e , refl , ns-fwd-1 c d ¬n1d =
        w (a , b) (c , d) , e , refl , hw ¬n0b , he ,
          λ _ → shuffle (hop n0 (a , b)) (hopdec n1 c d ¬n1d)
                  (trans (+-comm (hop n0 (c , d)) (hop n0 (a , b)))
                         (sym (+-identityʳ (hop n0 (a , b) + hop n0 (c , d)))))
                  (+-comm (hop n1 (c , d)) (hop n0 (a , b)))
...   | w (a , b) p , refl , ns-in-1 a b p ¬n0b | o q , refl , ns-fwd-2 c d q =
        w (a , b) (c , d) , o q , refl , hw ¬n0b , ho _ ,
          λ _ → shuffle (hop n0 (a , b) + hop n1 q) (hopdec n1 c d (held-w hy))
                  (trans (sym (+-assoc (hop n0 (c , d)) (hop n0 (a , b)) (hop n1 q)))
                         (cong (_+ hop n1 q) (+-comm (hop n0 (c , d)) (hop n0 (a , b)))))
                  (trans (sym (+-assoc (hop n1 (c , d)) (hop n0 (a , b)) (hop n1 q)))
                         (trans (cong (_+ hop n1 q) (+-comm (hop n1 (c , d)) (hop n0 (a , b))))
                                (+-assoc (hop n0 (a , b)) (hop n1 (c , d)) (hop n1 q))))
-- forwarder = node0 (to nextN n0 = n1); input = node1
...   | e , refl , ns-fwd-1 a b ¬n0b     | o p , refl , ns-in-e p =
        e , o (a , b) , refl , he , ho _ ,
          λ _ → shuffle 0 (hopdec n0 a b ¬n0b) (+-identityʳ _) refl
...   | e , refl , ns-fwd-1 a b ¬n0b     | w (c , d) p , refl , ns-in-1 c d p ¬n1d =
        e , w (c , d) (a , b) , refl , he , hw ¬n1d ,
          λ _ → shuffle (hop n1 (c , d)) (hopdec n0 a b ¬n0b)
                  (+-comm (hop n1 (a , b)) (hop n1 (c , d))) refl
...   | o q , refl , ns-fwd-2 a b q      | o p , refl , ns-in-e p =
        o q , o (a , b) , refl , ho _ , ho _ ,
          λ _ → shuffle (hop n0 q) (hopdec n0 a b (held-w hx))
                  (+-comm (hop n1 (a , b)) (hop n0 q))
                  (sym (+-identityʳ (hop n0 (a , b) + hop n0 q)))
...   | o q , refl , ns-fwd-2 a b q      | w (c , d) p , refl , ns-in-1 c d p ¬n1d =
        o q , w (c , d) (a , b) , refl , ho _ , hw ¬n1d ,
          λ _ → shuffle (hop n0 q + hop n1 (c , d)) (hopdec n0 a b (held-w hx))
                  (trans (+-comm (hop n1 (a , b)) (hop n0 q + hop n1 (c , d)))
                         (+-assoc (hop n0 q) (hop n1 (c , d)) (hop n1 (a , b))))
                  (sym (+-assoc (hop n0 (a , b)) (hop n0 q) (hop n1 (c , d))))

-------------------------------------------------------------------------------------
-- §8. De-hiding: `H` reachability confined to configs; a hidden τ is a single-hop
-- `ring` sync of `Cfg` strictly decreasing `μ`.
-------------------------------------------------------------------------------------

csat→hidden : ∀ {B} (e : REv B) (a : B) → ringES .mem (B , e) a → hidden (evLabel B e a)
csat→hidden send    a ()
csat→hidden receive a ()
csat→hidden ring    a c = c

Hstep-τ : ∀ x y → Held n0 x → Held n1 y → {t′ : _} → H x y ─[ τ ]─► t′
  → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ]
      (t′ ≡ H x′ y′ × Held n0 x′ × Held n1 y′ × μ x′ y′ < μ x y)
Hstep-τ x y hx hy st with Hide-τ-elim ringES (Cfg x y) st
... | hτP P' pτ _ = ⊥-elim (sys-noτ x y pτ)
... | hτH {e = ge} {a = a} P' csat pstep refl with sys-inv-vis x y hx hy pstep
...   | x′ , y′ , refl , hx′ , hy′ , fμ =
        x′ , y′ , refl , hx′ , hy′ , fμ (csat→hidden ge a csat)

Hstep-ev : ∀ x y → Held n0 x → Held n1 y → {ev0 : Event} {t′ : _}
         → H x y ─[ ev (evl ev0) ]─► t′
         → Σ[ x′ ∈ St ] Σ[ y′ ∈ St ] (t′ ≡ H x′ y′ × Held n0 x′ × Held n1 y′)
Hstep-ev x y hx hy st with Hide-ev-elim ringES (Cfg x y) st
... | heV P' ¬csat pstep with sys-inv-vis x y hx hy pstep
...   | x′ , y′ , refl , hx′ , hy′ , _ = x′ , y′ , refl , hx′ , hy′

-------------------------------------------------------------------------------------
-- §9. No config diverges (well-founded recursion on `μ`); reachability closure;
-- the theorem.
-------------------------------------------------------------------------------------

¬div-bnd : ∀ n x y → Held n0 x → Held n1 y → μ x y < n → ¬ Diverges (H x y)
¬div-bnd (suc n) x y hx hy μ<sn d with Hstep-τ x y hx hy (d .Diverges.step)
... | x′ , y′ , eq , hx′ , hy′ , μ′<μ =
      ¬div-bnd n x′ y′ hx′ hy′ (≤-trans μ′<μ (≤-pred μ<sn)) (subst Diverges eq (d .Diverges.rest))

¬div : ∀ x y → Held n0 x → Held n1 y → ¬ Diverges (H x y)
¬div x y hx hy = ¬div-bnd (suc (μ x y)) x y hx hy (n<1+n _)

reach-cons : ∀ {s t′} → RingH ⟹∖√⟨ s ⟩ t′
           → Σ[ x ∈ St ] Σ[ y ∈ St ] (t′ ≡ H x y × Held n0 x × Held n1 y)
reach-cons r = go e e he he refl r
  where
  go : ∀ {s t t′} x y → Held n0 x → Held n1 y → t ≡ H x y → t ⟹∖√⟨ s ⟩ t′
     → Σ[ u ∈ St ] Σ[ v ∈ St ] (t′ ≡ H u v × Held n0 u × Held n1 v)
  go x y hx hy refl ∖√-refl        = x , y , refl , hx , hy
  go x y hx hy refl (∖√-τ  st rest) with Hstep-τ x y hx hy st
  ... | x′ , y′ , refl , hx′ , hy′ , _ = go x′ y′ hx′ hy′ refl rest
  go x y hx hy refl (∖√-ev st rest) with Hstep-ev x y hx hy st
  ... | x′ , y′ , refl , hx′ , hy′     = go x′ y′ hx′ hy′ refl rest

nonBlockingRing-divergenceFree : DivergenceFree RingH
nonBlockingRing-divergenceFree reach div with reach-cons reach
... | x , y , refl , hx , hy = ¬div x y hx hy div
