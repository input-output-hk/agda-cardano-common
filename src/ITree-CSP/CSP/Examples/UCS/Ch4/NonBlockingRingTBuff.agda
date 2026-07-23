{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the NON-BLOCKING routing ring, observed only on its
-- N1→N2 port, is a bounded FIFO buffer.  Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/nonblock.csp   (UCS ch. 4 §4.2, the `TBuff` assert)
--
-- The source asserts, over the store-and-forward non-blocking ring `RingH`:
--
--   TBuff(<>)    = send.N1.N2?m -> TBuff(<m>)
--   TBuff(s^<m>) = receive.N2.N1.m -> TBuff(s)
--                  [] #s<capacity-1 & (STOP |~| send.N1.N2?m' -> TBuff(<m'>^s^<m>))
--   assert TBuff(<>) [T= RingH \ diff({|send,receive|},{|send.N1.N2,receive.N2.N1|})
--
-- i.e. the ring, with the internal `ring` channel AND every `send`/`receive`
-- EXCEPT the N1→N2 port hidden, trace-refines a bounded FIFO of capacity
-- `2*N-1`.  The source notes `T = {0,1}` is what makes this an in-order CONTENT
-- correctness statement (with a single value it would only prove the bound).
--
-- ────────────────────────────────────────────────────────────────────────────
-- MODEL.  N = 2, `T = Bool`, N1 = 0, N2 = 1, capacity = 2*N-1 = 3.  Packet =
-- `Node × Node × Bool` = (src , dst , payload).  `send` is restricted to
-- dst ≠ n (a node never sends to itself), so at N = 2 there are exactly two
-- flows: the observed 0→1 forward flow (`send.0.1` / `receive.1.0`) and the
-- hidden 1→0 reverse flow (`send.1.0` / `receive.0.1`); `ring.*` is hidden.
--
-- ⚠  REUSE IS IMPOSSIBLE.  The committed ring model `RoutingRingNonBlocking`
-- drops the payload (`T = ⊤`, packet = src × dst) — its `send`/`receive` carry
-- no `m`.  `TBuff` observes `send.0.1.m`/`receive.1.0.m` WITH a `Bool` payload,
-- so this module RE-DERIVES the non-blocking node with a `Bool` payload.
--
-- ⚠  PINNED.  `Node1`/`Node2` forward the SPECIFIC held packet `(a,b,m)` at
-- index `nextN n` and deliver only the pinned `(a,m)` (the `pkt≟`/`src ≟ a`/
-- `m ≟ m'` guards in the offer maps).  Offers are NEVER value-generalised — an
-- over-approximated model would exhibit content the real ring never delivers.

module CSP.Examples.UCS.Ch4.NonBlockingRingTBuff where

open import Level using () renaming (zero to lzero)
open import Data.Fin using (Fin; #_) renaming (zero to fzero; suc to fsuc)
import Data.Fin as Fin
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; not; _∧_; T; if_then_else_)
open import Data.Bool.Properties using (T?) renaming (_≟_ to _B≟_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_; ⌊_⌋)
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

nextN : Node → Node
nextN fzero        = n1
nextN (fsuc fzero) = n0

------------------------------------------------------------------------------------
-- §2. The Bool-payload event type and its decidable equality.
data BEv : Set → Set where
  send    : BEv (Node × Node × Bool)             -- send.i.dst.m       : (i , dst , m)
  receive : BEv (Node × Node × Bool)             -- receive.i.src.m    : (i , src , m)
  ring    : BEv (Node × (Node × Node × Bool))    -- ring.j.(s,r,m)     : (j , (s , r , m))

BEv-≟ : (x y : AnyTypes BEv) → Dec (x ≡ y)
BEv-≟ (_ , send)    (_ , send)    = yes refl
BEv-≟ (_ , receive) (_ , receive) = yes refl
BEv-≟ (_ , ring)    (_ , ring)    = yes refl
BEv-≟ (_ , send)    (_ , receive) = no (λ ())
BEv-≟ (_ , send)    (_ , ring)    = no (λ ())
BEv-≟ (_ , receive) (_ , send)    = no (λ ())
BEv-≟ (_ , receive) (_ , ring)    = no (λ ())
BEv-≟ (_ , ring)    (_ , send)    = no (λ ())
BEv-≟ (_ , ring)    (_ , receive) = no (λ ())

-- decidable equality on packets `Node × Node × Bool`
pkt≟ : (p q : Node × Node × Bool) → Dec (p ≡ q)
pkt≟ = ×-≡-dec Fin._≟_ (×-≡-dec Fin._≟_ _B≟_)

open import CSP.Operators BEv-≟
open EventSet

------------------------------------------------------------------------------------
-- §3. Per-node alphabets (payload-independent; only the node index matters).
A : Node → EventSet
A i .mem (_ , send)    (j , _) = j ≡ i
A i .mem (_ , receive) (j , _) = j ≡ i
A i .mem (_ , ring)    (j , _) = (j ≡ i) ⊎ (j ≡ nextN i)
A i .dec (_ , send)    (j , _) = j Fin.≟ i
A i .dec (_ , receive) (j , _) = j Fin.≟ i
A i .dec (_ , ring)    (j , _) = (j Fin.≟ i) ⊎-dec (j Fin.≟ nextN i)

------------------------------------------------------------------------------------
-- §4. The non-blocking node (Bool-payload, PINNED).  Every position is STABLE
-- (τ-map ≡ ∅t).  `send` restricted to dst ≠ n.
DProcB : Set₁
DProcB = PTree BEv (ExtI BEv) (⊤poly {lzero})

NodeE : Node → DProcB
Node1 : Node → (Node × Node × Bool) → DProcB
Node2 : Node → (Node × Node × Bool) → (Node × Node × Bool) → DProcB

force (NodeE n) = react
  (λ where
     (_ , send)    (j , dst , m) → case j Fin.≟ n of λ where
         (yes _) → case dst Fin.≟ n of λ where
             (yes _) → nothing                          -- dst = n forbidden
             (no  _) → just (Node1 n (n , dst , m))
         (no  _) → nothing
     (_ , receive) _             → nothing
     (_ , ring)    (j , p)       → case j Fin.≟ n of λ where
         (yes _) → just (Node1 n p)
         (no  _) → nothing)
  ∅t

force (Node1 n (a , b , m)) = react
  (λ where
     (_ , send)    _              → nothing
     (_ , receive) (j , src , m′) → case n Fin.≟ b of λ where
         (yes _) → case j Fin.≟ n of λ where
             (yes _) → case src Fin.≟ a of λ where
                 (yes _) → case m′ B≟ m of λ where
                     (yes _) → just (NodeE n)
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , ring)    (j , p)        → case n Fin.≟ b of λ where
         (yes _) → nothing                              -- local: only delivers
         (no  _) → case j Fin.≟ n of λ where
             (yes _) → just (Node2 n (a , b , m) p)     -- input into slot 2
             (no  _) → case j Fin.≟ nextN n of λ where
                 (yes _) → case pkt≟ p (a , b , m) of λ where
                     (yes _) → just (NodeE n)           -- forward the held packet
                     (no  _) → nothing
                 (no  _) → nothing)
  ∅t

force (Node2 n (a , b , m) p′) = react
  (λ where
     (_ , send)    _        → nothing
     (_ , receive) _        → nothing
     (_ , ring)    (j , p)  → case j Fin.≟ nextN n of λ where
         (yes _) → case pkt≟ p (a , b , m) of λ where
             (yes _) → just (Node1 n p′)               -- forward slot 1, keep slot 2
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

nbNode : Node → Comp BEv (⊤poly {lzero})
nbNode n = comp (A n) (NodeE n)

Ring : PTree BEv (ExtI BEv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
Ring = ∥ₐ⁺ (nbNode n0) (nbNode n1 ∷ [])

------------------------------------------------------------------------------------
-- §5. The observation-hiding set.  Hide `{| ring |}` and every `send`/`receive`
-- EXCEPT the N1→N2 port `send.0.1.*` / `receive.1.0.*`.
sendObs? recvObs? : Node → Node → Bool
sendObs? i dst = ⌊ i Fin.≟ n0 ⌋ ∧ ⌊ dst Fin.≟ n1 ⌋
recvObs? i src = ⌊ i Fin.≟ n1 ⌋ ∧ ⌊ src Fin.≟ n0 ⌋

obsES : EventSet
obsES .mem (_ , send)    (i , dst , m) = T (not (sendObs? i dst))
obsES .mem (_ , receive) (i , src , m) = T (not (recvObs? i src))
obsES .mem (_ , ring)    _             = T true
obsES .dec (_ , send)    (i , dst , m) = T? (not (sendObs? i dst))
obsES .dec (_ , receive) (i , src , m) = T? (not (recvObs? i src))
obsES .dec (_ , ring)    _             = T? true

RingObs : PTree BEv (ExtI BEv) (RetOf⁺ (nbNode n0) (nbNode n1 ∷ []))
RingObs = Ring ∖ obsES

------------------------------------------------------------------------------------
-- §6. The bounded FIFO `TBuff` (capacity = 2*N-1 = 3).
--
-- Written in the inlined-`react` idiom (its forward steps then hold by `refl`).
-- This is the TRACE-FAITHFUL presentation of the source's
--   receive.1.0.head → TBuff tail  □  (#s<cap) & (STOP ⊓ send.0.1?m → TBuff …)
-- : since `⊓`/`STOP` add no traces beyond the union, the trace set is exactly
-- the source's — the internal choice and its STOP branch are absorbed into a
-- single stable node offering `receive.1.0.head` (when non-empty) and
-- `send.0.1?m` (when `length < capacity`).  Oldest at the head; `send` appends
-- at the back (`∷ʳ`), `receive` delivers the head.
-- The FIFO's return type matches the ring's `RetOf⁺` (= ⊤ × ⊤) so both sides of
-- the refinement live at the same `R` (neither ever terminates; `R` is phantom).
BProc : Set₁
BProc = PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})

capacity : ℕ
capacity = 3

TBuff : List Bool → BProc
force (TBuff cs) = react
  (λ where
     (_ , send)    (i , dst , m) → case i Fin.≟ n0 of λ where
         (yes _) → case dst Fin.≟ n1 of λ where
             (yes _) → case length cs <ᵇ capacity of λ where
                 true  → just (TBuff (cs ∷ʳ m))
                 false → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , receive) (i , src , m) → case cs of λ where
         []       → nothing
         (x ∷ xs) → case i Fin.≟ n1 of λ where
             (yes _) → case src Fin.≟ n0 of λ where
                 (yes _) → case m B≟ x of λ where
                     (yes _) → just (TBuff xs)
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
     (_ , ring)    _             → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §7. The refinement  TBuff [] ⊑T RingObs  via a contents-`List Bool` weak simulation.
------------------------------------------------------------------------------------

open import Data.Unit using () renaming (tt to ⋆)   -- element of `T true = ⊤`

open import Semantics.LTS       {E = BEv} {I = ExtI BEv}
open import Semantics.WeakBisim {E = BEv} {I = ExtI BEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures  {E = BEv} {I = ExtI BEv} using (_⊑T_; traces)
open import Semantics.WeakSim   {E = BEv} {I = ExtI BEv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = BEv} {I = ExtI BEv}
open import CSP.Laws.AlphaParallel BEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )
open import CSP.Laws.Traces.TraceLawsHide BEv-≟
  using ( Hide-ev-elim; Hide-τ-elim; HideevR; heV; he√; HideτR; hτP; hτH )

-- §7.1 The composite `Sys` and its initial identification with `Ring`.
B1 : EventSet
B1 = unionα (nbNode n1 ∷ [])

Sys : DProcB → DProcB → PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

-- §7.2 Reachable per-node states (tags carrying only the relevant payloads).  At N=2
-- there are two flows: 0→1 forward (`send.0.1`/`receive.1.0`) and 1→0 reverse.  Each
-- node holds ≤ 1 forward packet, so the 0→1 contents never exceed length 2 ≤ capacity.
data St0 : Set where
  e0  :               St0            -- NodeE n0
  o0f : Bool →        St0            -- Node1 n0 (0,1,m)   forward held  (to forward via ring.1)
  o0r : Bool →        St0            -- Node1 n0 (1,0,m)   reverse local (to deliver receive.0.1)
  w0  : Bool → Bool → St0            -- Node2 n0 (0,1,mf)(1,0,mr)

data St1 : Set where
  e1  :               St1            -- NodeE n1
  o1f : Bool →        St1            -- Node1 n1 (0,1,m)   forward local (to deliver receive.1.0)
  o1r : Bool →        St1            -- Node1 n1 (1,0,m)   reverse held  (to forward via ring.0)
  w1  : Bool → Bool → St1            -- Node2 n1 (1,0,mr)(0,1,mf)

nd0 : St0 → DProcB
nd0 e0        = NodeE n0
nd0 (o0f m)   = Node1 n0 (n0 , n1 , m)
nd0 (o0r m)   = Node1 n0 (n1 , n0 , m)
nd0 (w0 mf mr) = Node2 n0 (n0 , n1 , mf) (n1 , n0 , mr)

nd1 : St1 → DProcB
nd1 e1        = NodeE n1
nd1 (o1f m)   = Node1 n1 (n0 , n1 , m)
nd1 (o1r m)   = Node1 n1 (n1 , n0 , m)
nd1 (w1 mr mf) = Node2 n1 (n1 , n0 , mr) (n0 , n1 , mf)

Cfg : St0 → St1 → PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})
Cfg s0 s1 = Sys (nd0 s0) (nd1 s1)

-- §7.3 The 0→1 contents (oldest first: node1's forward packet is closest to delivery).
c1 : St1 → List Bool
c1 e1        = []
c1 (o1f x)   = x ∷ []
c1 (o1r _)   = []
c1 (w1 _ y)  = y ∷ []

content : St0 → St1 → List Bool
content e0        s1 = c1 s1
content (o0f a)   s1 = c1 s1 ∷ʳ a
content (o0r _)   s1 = c1 s1
content (w0 a _)  s1 = c1 s1 ∷ʳ a

-- reverse-inject at node1 (e1 → o1r) leaves the forward contents unchanged (s0 abstract).
c-send1 : ∀ s0 m → content s0 (o1r m) ≡ content s0 e1
c-send1 e0       m = refl
c-send1 (o0f a)  m = refl
c-send1 (o0r a)  m = refl
c-send1 (w0 a b) m = refl

-- §7.4 Nodes are react-headed and STABLE (no √, no τ).
noRet0 : ∀ s0 {r} → PTree.force (nd0 s0) ≡ ret r → ⊥
noRet0 e0 () ; noRet0 (o0f _) () ; noRet0 (o0r _) () ; noRet0 (w0 _ _) ()
noRet1 : ∀ s1 {r} → PTree.force (nd1 s1) ≡ ret r → ⊥
noRet1 e1 () ; noRet1 (o1f _) () ; noRet1 (o1r _) () ; noRet1 (w1 _ _) ()

noτ0 : ∀ s0 {t′} → nd0 s0 ─[ τ ]─► t′ → ⊥
noτ0 e0        (sSil eq) = case eq of λ () ; noτ0 e0        (sTau refl br) = case br of λ ()
noτ0 (o0f _)   (sSil eq) = case eq of λ () ; noτ0 (o0f _)   (sTau refl br) = case br of λ ()
noτ0 (o0r _)   (sSil eq) = case eq of λ () ; noτ0 (o0r _)   (sTau refl br) = case br of λ ()
noτ0 (w0 _ _)  (sSil eq) = case eq of λ () ; noτ0 (w0 _ _)  (sTau refl br) = case br of λ ()
noτ1 : ∀ s1 {t′} → nd1 s1 ─[ τ ]─► t′ → ⊥
noτ1 e1        (sSil eq) = case eq of λ () ; noτ1 e1        (sTau refl br) = case br of λ ()
noτ1 (o1f _)   (sSil eq) = case eq of λ () ; noτ1 (o1f _)   (sTau refl br) = case br of λ ()
noτ1 (o1r _)   (sSil eq) = case eq of λ () ; noτ1 (o1r _)   (sTau refl br) = case br of λ ()
noτ1 (w1 _ _)  (sSil eq) = case eq of λ () ; noτ1 (w1 _ _)  (sTau refl br) = case br of λ ()

-- §7.5 Per-node visible-step transition relations (indexed by the R-independent event).
Ev : Set₁
Ev = Event

sL rL : Node × Node × Bool → Ev
sL p = evLabel (Node × Node × Bool) send p
rL p = evLabel (Node × Node × Bool) receive p
gL : Node × (Node × Node × Bool) → Ev
gL p = evLabel (Node × (Node × Node × Bool)) ring p

data T0 : St0 → DProcB → Ev → Set₁ where
  t0-send : ∀ m     → T0 e0         (nd0 (o0f m))              (sL (n0 , n1 , m))
  t0-in   : ∀ p     → T0 e0         (Node1 n0 p)               (gL (n0 , p))
  t0-in2  : ∀ m p   → T0 (o0f m)    (Node2 n0 (n0 , n1 , m) p) (gL (n0 , p))
  t0-fwd1 : ∀ m     → T0 (o0f m)    (nd0 e0)                   (gL (n1 , (n0 , n1 , m)))
  t0-recv : ∀ m     → T0 (o0r m)    (nd0 e0)                   (rL (n0 , n1 , m))
  t0-fwd2 : ∀ mf mr → T0 (w0 mf mr) (nd0 (o0r mr))             (gL (n1 , (n0 , n1 , mf)))

data T1 : St1 → DProcB → Ev → Set₁ where
  t1-send : ∀ m     → T1 e1         (nd1 (o1r m))              (sL (n1 , n0 , m))
  t1-in   : ∀ p     → T1 e1         (Node1 n1 p)               (gL (n1 , p))
  t1-in2  : ∀ m p   → T1 (o1r m)    (Node2 n1 (n1 , n0 , m) p) (gL (n1 , p))
  t1-fwd1 : ∀ m     → T1 (o1r m)    (nd1 e1)                   (gL (n0 , (n1 , n0 , m)))
  t1-recv : ∀ m     → T1 (o1f m)    (nd1 e1)                   (rL (n1 , n0 , m))
  t1-fwd2 : ∀ mr mf → T1 (w1 mr mf) (nd1 (o1f mf))             (gL (n0 , (n1 , n0 , mr)))

inv0 : ∀ s0 {t′ e} → nd0 s0 ─[ ev (evl e) ]─► t′ → T0 s0 t′ e
inv0 e0 (sVis {at = _ , send} {a = fzero , fzero , m} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , send} {a = fzero , fsuc fzero , m} refl br) =
  subst (λ z → T0 e0 z _) (just-injective br) (t0-send m)
inv0 e0 (sVis {at = _ , send} {a = fsuc fzero , dst , m} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , ring} {a = fzero , p} refl br) =
  subst (λ z → T0 e0 z _) (just-injective br) (t0-in p)
inv0 e0 (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) = case br of λ ()
inv0 (o0f m) (sVis {at = _ , send} refl br) = case br of λ ()
inv0 (o0f m) (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 (o0f m) (sVis {at = _ , ring} {a = fzero , p} refl br) =
  subst (λ z → T0 (o0f m) z _) (just-injective br) (t0-in2 m p)
inv0 (o0f m) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) with pkt≟ p (n0 , n1 , m)
... | yes refl = subst (λ z → T0 (o0f m) z _) (just-injective br) (t0-fwd1 m)
... | no  _    = case br of λ ()
inv0 (o0r m) (sVis {at = _ , send} refl br) = case br of λ ()
inv0 (o0r m) (sVis {at = _ , receive} {a = fzero , fzero , m′} refl br) = case br of λ ()
inv0 (o0r m) (sVis {at = _ , receive} {a = fzero , fsuc fzero , m′} refl br) with m′ B≟ m
... | yes refl = subst (λ z → T0 (o0r m) z _) (just-injective br) (t0-recv m)
... | no  _    = case br of λ ()
inv0 (o0r m) (sVis {at = _ , receive} {a = fsuc fzero , src , m′} refl br) = case br of λ ()
inv0 (o0r m) (sVis {at = _ , ring} refl br) = case br of λ ()
inv0 (w0 mf mr) (sVis {at = _ , send} refl br) = case br of λ ()
inv0 (w0 mf mr) (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 (w0 mf mr) (sVis {at = _ , ring} {a = fzero , p} refl br) = case br of λ ()
inv0 (w0 mf mr) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) with pkt≟ p (n0 , n1 , mf)
... | yes refl = subst (λ z → T0 (w0 mf mr) z _) (just-injective br) (t0-fwd2 mf mr)
... | no  _    = case br of λ ()

inv1 : ∀ s1 {t′ e} → nd1 s1 ─[ ev (evl e) ]─► t′ → T1 s1 t′ e
inv1 e1 (sVis {at = _ , send} {a = fsuc fzero , fsuc fzero , m} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , send} {a = fsuc fzero , fzero , m} refl br) =
  subst (λ z → T1 e1 z _) (just-injective br) (t1-send m)
inv1 e1 (sVis {at = _ , send} {a = fzero , dst , m} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) =
  subst (λ z → T1 e1 z _) (just-injective br) (t1-in p)
inv1 e1 (sVis {at = _ , ring} {a = fzero , p} refl br) = case br of λ ()
inv1 (o1f m) (sVis {at = _ , send} refl br) = case br of λ ()
inv1 (o1f m) (sVis {at = _ , receive} {a = fsuc fzero , fzero , m′} refl br) with m′ B≟ m
... | yes refl = subst (λ z → T1 (o1f m) z _) (just-injective br) (t1-recv m)
... | no  _    = case br of λ ()
inv1 (o1f m) (sVis {at = _ , receive} {a = fsuc fzero , fsuc fzero , m′} refl br) = case br of λ ()
inv1 (o1f m) (sVis {at = _ , receive} {a = fzero , src , m′} refl br) = case br of λ ()
inv1 (o1f m) (sVis {at = _ , ring} refl br) = case br of λ ()
inv1 (o1r m) (sVis {at = _ , send} refl br) = case br of λ ()
inv1 (o1r m) (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 (o1r m) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) =
  subst (λ z → T1 (o1r m) z _) (just-injective br) (t1-in2 m p)
inv1 (o1r m) (sVis {at = _ , ring} {a = fzero , p} refl br) with pkt≟ p (n1 , n0 , m)
... | yes refl = subst (λ z → T1 (o1r m) z _) (just-injective br) (t1-fwd1 m)
... | no  _    = case br of λ ()
inv1 (w1 mr mf) (sVis {at = _ , send} refl br) = case br of λ ()
inv1 (w1 mr mf) (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 (w1 mr mf) (sVis {at = _ , ring} {a = fsuc fzero , p} refl br) = case br of λ ()
inv1 (w1 mr mf) (sVis {at = _ , ring} {a = fzero , p} refl br) with pkt≟ p (n1 , n0 , mr)
... | yes refl = subst (λ z → T1 (w1 mr mf) z _) (just-injective br) (t1-fwd2 mr mf)
... | no  _    = case br of λ ()

-- §7.6 TBuff forward steps (its react offers reduce, so these hold by `refl`).
tb-recv : ∀ x xs → TBuff (x ∷ xs) ─[ ev (evl (rL (n1 , n0 , x))) ]─► TBuff xs
tb-recv true  xs = sVis {at = (Node × Node × Bool) , receive} {a = n1 , n0 , true}  refl refl
tb-recv false xs = sVis {at = (Node × Node × Bool) , receive} {a = n1 , n0 , false} refl refl

-- send from the two possible contents shapes (length 0 / 1 < capacity, so offers fire).
tb-send0 : ∀ m → TBuff [] ─[ ev (evl (sL (n0 , n1 , m))) ]─► TBuff (m ∷ [])
tb-send0 m = sVis {at = (Node × Node × Bool) , send} {a = n0 , n1 , m} refl refl
tb-send1 : ∀ x m → TBuff (x ∷ []) ─[ ev (evl (sL (n0 , n1 , m))) ]─► TBuff (x ∷ m ∷ [])
tb-send1 x m = sVis {at = (Node × Node × Bool) , send} {a = n0 , n1 , m} refl refl

-- §7.7 The weak-simulation relation: each reachable `RingObs` config ↔ `TBuff` contents.
data RR : PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero}) → BProc → Set₁ where
  rr : ∀ s0 s1 → RR (Cfg s0 s1 ∖ obsES) (TBuff (content s0 s1))

-- §7.8 Forward matching of a VISIBLE (observed) move.
fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero} × ⊤poly {lzero})} {p′}
     → RR p q → p ─[ ev l ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × RR p′ q′)
fwdE (rr s0 s1) stp with Hide-ev-elim obsES (Cfg s0 s1) stp
... | he√ eqf = ⊥-elim (case αpar-√-step-inv eqf of λ { (v√ p0 _) → noRet0 s0 p0 })
... | heV P′ ¬c pstp with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
...     | vSync pA pB p0s p1s with inv0 s0 p0s
...       | t0-send m      = case pB of λ { (inj₁ ()) ; (inj₂ ()) }
...       | t0-recv m      = case pB of λ { (inj₁ ()) ; (inj₂ ()) }
...       | t0-in p        = ⊥-elim (¬c ⋆)
...       | t0-in2 m p     = ⊥-elim (¬c ⋆)
...       | t0-fwd1 m      = ⊥-elim (¬c ⋆)
...       | t0-fwd2 mf mr  = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s with inv0 s0 p0s
...       | t0-recv m      = ⊥-elim (¬c ⋆)
...       | t0-in p        = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...       | t0-in2 m p     = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...       | t0-fwd1 m      = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...       | t0-fwd2 mf mr  = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...       | t0-send m with s1
...         | e1     = _ , wev τ*-refl (tb-send0 m)   τ*-refl , rr (o0f m) e1
...         | o1f x  = _ , wev τ*-refl (tb-send1 x m) τ*-refl , rr (o0f m) (o1f x)
...         | o1r x  = _ , wev τ*-refl (tb-send0 m)   τ*-refl , rr (o0f m) (o1r x)
...         | w1 x y = _ , wev τ*-refl (tb-send1 y m) τ*-refl , rr (o0f m) (w1 x y)
fwdE (rr s0 s1) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s with inv1 s1 p1s
...       | t1-send m      = ⊥-elim (¬c ⋆)
...       | t1-in p        = ⊥-elim (¬pA (inj₂ refl))
...       | t1-in2 m p     = ⊥-elim (¬pA (inj₂ refl))
...       | t1-fwd1 m      = ⊥-elim (¬pA (inj₁ refl))
...       | t1-fwd2 mr mf  = ⊥-elim (¬pA (inj₁ refl))
...       | t1-recv m with s0
...         | e0     = _ , wev τ*-refl (tb-recv m (content e0 e1))      τ*-refl , rr e0 e1
...         | o0f a  = _ , wev τ*-refl (tb-recv m (content (o0f a) e1)) τ*-refl , rr (o0f a) e1
...         | o0r a  = _ , wev τ*-refl (tb-recv m (content (o0r a) e1)) τ*-refl , rr (o0r a) e1
...         | w0 a b = _ , wev τ*-refl (tb-recv m (content (w0 a b) e1)) τ*-refl , rr (w0 a b) e1

-- §7.9 Forward matching of a τ (hidden) move: `TBuff` stays put, contents preserved.
fwdT : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × RR p′ q′)
fwdT (rr s0 s1) stp with Hide-τ-elim obsES (Cfg s0 s1) stp
... | hτP P′ pτ refl with αpar-τ-step-inv pτ
...   | inj₁ (_ , t0τ , _) = ⊥-elim (noτ0 s0 t0τ)
...   | inj₂ (_ , t1τ , _) = ⊥-elim (noτ1 s1 t1τ)
fwdT (rr s0 s1) stp | hτH P′ csat pstp refl with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
...     | vSoloL pA ¬pB p0s with inv0 s0 p0s
...       | t0-send m     = ⊥-elim csat
...       | t0-in p       = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...       | t0-in2 m p    = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...       | t0-fwd1 m     = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...       | t0-fwd2 mf mr = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
...       | t0-recv m     = _ , wτ τ*-refl , rr e0 s1
fwdT (rr s0 s1) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s with inv1 s1 p1s
...       | t1-recv m     = ⊥-elim csat
...       | t1-in p       = ⊥-elim (¬pA (inj₂ refl))
...       | t1-in2 m p    = ⊥-elim (¬pA (inj₂ refl))
...       | t1-fwd1 m     = ⊥-elim (¬pA (inj₁ refl))
...       | t1-fwd2 mr mf = ⊥-elim (¬pA (inj₁ refl))
...       | t1-send m     = TBuff (content s0 e1) , wτ τ*-refl ,
                            subst (λ w → RR (Cfg s0 (o1r m) ∖ obsES) (TBuff w))
                                  (c-send1 s0 m) (rr s0 (o1r m))
fwdT (rr s0 s1) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s
      with inv0 s0 p0s | inv1 s1 p1s
-- ring.1 forward hops (node0 forwards (0,1,mf); node1 accepts)
...   | t0-fwd1 mf     | t1-in _        = _ , wτ τ*-refl , rr e0       (o1f mf)
...   | t0-fwd1 mf     | t1-in2 mr _    = _ , wτ τ*-refl , rr e0       (w1 mr mf)
...   | t0-fwd2 mf mr  | t1-in _        = _ , wτ τ*-refl , rr (o0r mr) (o1f mf)
...   | t0-fwd2 mf mr  | t1-in2 mr′ _   = _ , wτ τ*-refl , rr (o0r mr) (w1 mr′ mf)
-- ring.0 reverse hops (node1 forwards (1,0,mr); node0 accepts)
...   | t0-in _        | t1-fwd1 mr     = _ , wτ τ*-refl , rr (o0r mr)  e1
...   | t0-in _        | t1-fwd2 mr mf  = _ , wτ τ*-refl , rr (o0r mr)  (o1f mf)
...   | t0-in2 mf _    | t1-fwd1 mr     = _ , wτ τ*-refl , rr (w0 mf mr) e1
...   | t0-in2 mf _    | t1-fwd2 mr mf′ = _ , wτ τ*-refl , rr (w0 mf mr) (o1f mf′)

module M = WSimFromRel RR fwdE fwdT

-- assert  TBuff(<>) [T= RingH∖diff(…)   (traces RingObs ⊆ traces (TBuff []))
nonblock-TBuff : TBuff [] ⊑T RingObs
nonblock-TBuff = wsim→⊑T (M.rel→wsim (rr e0 e1))
