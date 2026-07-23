{-# OPTIONS --guardedness #-}

-- UCS chapter 4 §4.2: the TOKEN ring, observed only on its N1→N2 port, is a
-- bounded FIFO buffer.  Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/tokring.csp   (UCS ch. 4 §4.2, the `TBuff` assert)
--
-- The token ring circulates a SINGLE token around the ring.  A node holding the
-- EMPTY token may inject a packet (turning the token FULL); the full token is
-- forwarded hop-by-hop over the hidden `ring` channel until it reaches its
-- destination, which delivers the packet (`receive`) and frees the token again.
-- Observed only on the N1→N2 port (`send.0.1` / `receive.1.0`), with the internal
-- `ring` channel AND every other `send`/`receive` hidden, the ring trace-refines a
-- bounded FIFO.
--
--   assert TBuff(<>) [T= TokRingH \ diff({|send,receive|},{|send.N1.N2,receive.N2.N1|})
--
-- ────────────────────────────────────────────────────────────────────────────
-- MODEL.  N = 2, tokens = 1, `T = Bool`, N1 = 0, N2 = 1.  A token is `Empty` or
-- `Full (src , dst , payload)`.  Because there is only ONE token, at most one
-- forward packet is ever in flight on the observed 0→1 port, so the observed
-- content never exceeds length 1; the capacity bound `capacity = tokens = 2` (as
-- in the source's `TBuff`) is therefore satisfied with room to spare (a cap-2
-- FIFO's trace set is a superset of the ring's).
--
-- The initial ring holds the single (empty) token at node 0: `Init 0 = NodeR 0`,
-- `Init 1 = NodeE 1`.  The empty-token circulation is a hidden `ring` τ (matched
-- by `TBuff` staying put — ignored by trace refinement).
--
-- ⚠  RE-DERIVED with a `Bool` payload (the committed `CSP.Examples.UCS.Ch4.TokenRing`
-- carries `T = ⊤`, no payload; `TBuff` observes `send.0.1.m`/`receive.1.0.m` WITH a
-- `Bool` payload, so this module re-derives the token node payload-carrying).
--
-- ⚠  PINNED.  `NodeF` forwards / delivers the SPECIFIC held packet `(s,r,m)` (the
-- `pkt≟`/`src ≟ s`/`m′ ≟ m` guards); `NodeR` sends with `dst ≠ n`.  Offers are
-- NEVER value-generalised — an over-approximated model would exhibit content the
-- real ring never delivers.
--
-- This mirrors the reviewed sibling `CSP.Examples.UCS.Ch4.NonBlockingRingTBuff`
-- (Task 1); the difference is the ring node (a single circulating TOKEN rather
-- than per-node store-and-forward slots), so the reachable state space is smaller
-- (6 config-shapes, content length ≤ 1).

module CSP.Examples.UCS.Ch4.TokenRingTBuff where

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
-- §2. Tokens, the Bool-payload event type, and its decidable equality.
data Token : Set where
  Empty : Token
  Full  : (Node × Node × Bool) → Token          -- Full (src , dst , payload)

data BEv : Set → Set where
  send    : BEv (Node × Node × Bool)             -- send.i.dst.m    : (i , dst , m)
  receive : BEv (Node × Node × Bool)             -- receive.i.src.m : (i , src , m)
  ring    : BEv (Node × Token)                   -- ring.j.tok      : (j , tok)

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
-- §4. The token node (Bool-payload, PINNED).  Every position is STABLE (τ-map ≡ ∅t).
--
-- NodeE n       — EMPTY node (does not hold the token).  Accepts the token from its
--                 predecessor: `ring.n.Empty → NodeR n`, `ring.n.(Full p) → NodeF n p`.
-- NodeR n       — node holding the EMPTY token.  Either injects a fresh packet
--                 `send.n.dst.m (dst ≠ n) → NodeF n (n , dst , m)` or forwards the
--                 empty token `ring.(nextN n).Empty → NodeE n`.
-- NodeF n (s,r,m) — node holding a FULL token.  If it is the destination (`r ≡ n`)
--                 it delivers `receive.n.s.m → NodeR n`; otherwise it forwards
--                 `ring.(nextN n).(Full (s,r,m)) → NodeE n` at the PINNED value.
DProcB : Set₁
DProcB = PTree BEv (ExtI BEv) (⊤poly {lzero})

NodeE : Node → DProcB
NodeR : Node → DProcB
NodeF : Node → (Node × Node × Bool) → DProcB

force (NodeE n) = react
  (λ where
     (_ , send)    _            → nothing
     (_ , receive) _            → nothing
     (_ , ring)    (j , Empty)  → case j Fin.≟ n of λ where
         (yes _) → just (NodeR n)
         (no  _) → nothing
     (_ , ring)    (j , Full p) → case j Fin.≟ n of λ where
         (yes _) → just (NodeF n p)
         (no  _) → nothing)
  ∅t

force (NodeR n) = react
  (λ where
     (_ , send)    (j , dst , m) → case j Fin.≟ n of λ where
         (yes _) → case dst Fin.≟ n of λ where
             (yes _) → nothing                          -- no self-send: dst ≢ n
             (no  _) → just (NodeF n (n , dst , m))
         (no  _) → nothing
     (_ , receive) _             → nothing
     (_ , ring)    (j , Empty)   → case j Fin.≟ nextN n of λ where
         (yes _) → just (NodeE n)
         (no  _) → nothing
     (_ , ring)    (j , Full _)  → nothing)
  ∅t

force (NodeF n (s , r , m)) = react
  (λ where
     (_ , send)    _                     → nothing
     (_ , receive) (j , src , m′)        → case r Fin.≟ n of λ where
         (yes _) → case j Fin.≟ n of λ where
             (yes _) → case src Fin.≟ s of λ where
                 (yes _) → case m′ B≟ m of λ where
                     (yes _) → just (NodeR n)
                     (no  _) → nothing
                 (no  _) → nothing
             (no  _) → nothing
         (no  _) → nothing
     (_ , ring)    (j , Empty)           → nothing
     (_ , ring)    (j , Full (s′ , r′ , m′)) → case r Fin.≟ n of λ where
         (yes _) → nothing                              -- destination: deliver, never forward
         (no  _) → case j Fin.≟ nextN n of λ where
             (yes _) → case pkt≟ (s′ , r′ , m′) (s , r , m) of λ where
                 (yes _) → just (NodeE n)               -- forward the held packet, PINNED
                 (no  _) → nothing
             (no  _) → nothing)
  ∅t

-- Initial ring: node 0 holds the (single, empty) token; node 1 is empty.
Init : Node → DProcB
Init fzero        = NodeR n0
Init (fsuc fzero) = NodeE n1

tkNode : Node → Comp BEv (⊤poly {lzero})
tkNode i = comp (A i) (Init i)

TokRing : PTree BEv (ExtI BEv) (RetOf⁺ (tkNode n0) (tkNode n1 ∷ []))
TokRing = ∥ₐ⁺ (tkNode n0) (tkNode n1 ∷ [])

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

TokRingObs : PTree BEv (ExtI BEv) (RetOf⁺ (tkNode n0) (tkNode n1 ∷ []))
TokRingObs = TokRing ∖ obsES

------------------------------------------------------------------------------------
-- §6. The bounded FIFO `TBuff` (capacity = tokens = 2).
--
-- Same trace-faithful FIFO as Task 1: a single stable node offering
-- `receive.1.0.head` (when non-empty) and `send.0.1?m` (when `length < capacity`).
-- Oldest at the head; `send` appends at the back (`∷ʳ`), `receive` delivers the head.
BProc : Set₁
BProc = PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})

capacity : ℕ
capacity = 2

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
-- §7. The refinement  TBuff [] ⊑T TokRingObs  via a contents-`List Bool` weak simulation.
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

-- §7.1 The composite `Sys` and its initial identification with `TokRing`.
B1 : EventSet
B1 = unionα (tkNode n1 ∷ [])

Sys : DProcB → DProcB → PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})
Sys t0 t1 = t0 ⟦ A n0 ∥ B1 ⟧ t1

-- §7.2 Reachable per-node states.  Only ONE node ever holds the token, so each is
-- EMPTY / holds-empty-token / holds-a-full-token (forward 0→1 or reverse 1→0).
data St0 : Set where
  e0  :        St0            -- NodeE n0
  r0  :        St0            -- NodeR n0            (holds empty token)
  f0f : Bool → St0            -- NodeF n0 (0,1,m)    forward packet held  (to forward via ring.1)
  f0r : Bool → St0            -- NodeF n0 (1,0,m)    reverse packet held  (to deliver receive.0.1)

data St1 : Set where
  e1  :        St1            -- NodeE n1
  r1  :        St1            -- NodeR n1            (holds empty token)
  f1f : Bool → St1            -- NodeF n1 (0,1,m)    forward packet held  (to deliver receive.1.0)
  f1r : Bool → St1            -- NodeF n1 (1,0,m)    reverse packet held  (to forward via ring.0)

nd0 : St0 → DProcB
nd0 e0      = NodeE n0
nd0 r0      = NodeR n0
nd0 (f0f m) = NodeF n0 (n0 , n1 , m)
nd0 (f0r m) = NodeF n0 (n1 , n0 , m)

nd1 : St1 → DProcB
nd1 e1      = NodeE n1
nd1 r1      = NodeR n1
nd1 (f1f m) = NodeF n1 (n0 , n1 , m)
nd1 (f1r m) = NodeF n1 (n1 , n0 , m)

Cfg : St0 → St1 → PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero})
Cfg s0 s1 = Sys (nd0 s0) (nd1 s1)

-- §7.3 Nodes are react-headed and STABLE (no √, no τ).
noRet0 : ∀ s0 {r} → PTree.force (nd0 s0) ≡ ret r → ⊥
noRet0 e0 () ; noRet0 r0 () ; noRet0 (f0f _) () ; noRet0 (f0r _) ()
noRet1 : ∀ s1 {r} → PTree.force (nd1 s1) ≡ ret r → ⊥
noRet1 e1 () ; noRet1 r1 () ; noRet1 (f1f _) () ; noRet1 (f1r _) ()

noτ0 : ∀ s0 {t′} → nd0 s0 ─[ τ ]─► t′ → ⊥
noτ0 e0      (sSil eq) = case eq of λ () ; noτ0 e0      (sTau refl br) = case br of λ ()
noτ0 r0      (sSil eq) = case eq of λ () ; noτ0 r0      (sTau refl br) = case br of λ ()
noτ0 (f0f _) (sSil eq) = case eq of λ () ; noτ0 (f0f _) (sTau refl br) = case br of λ ()
noτ0 (f0r _) (sSil eq) = case eq of λ () ; noτ0 (f0r _) (sTau refl br) = case br of λ ()
noτ1 : ∀ s1 {t′} → nd1 s1 ─[ τ ]─► t′ → ⊥
noτ1 e1      (sSil eq) = case eq of λ () ; noτ1 e1      (sTau refl br) = case br of λ ()
noτ1 r1      (sSil eq) = case eq of λ () ; noτ1 r1      (sTau refl br) = case br of λ ()
noτ1 (f1f _) (sSil eq) = case eq of λ () ; noτ1 (f1f _) (sTau refl br) = case br of λ ()
noτ1 (f1r _) (sSil eq) = case eq of λ () ; noτ1 (f1r _) (sTau refl br) = case br of λ ()

noSys√ : ∀ s0 s1 {r} → (Cfg s0 s1) .force ≡ ret r → ⊥
noSys√ s0 s1 eqf = case αpar-√-step-inv eqf of λ { (v√ p0 _) → noRet0 s0 p0 }

-- §7.4 Per-node visible-step transition relations (indexed by the R-independent event).
Ev : Set₁
Ev = Event

sL rL : Node × Node × Bool → Ev
sL p = evLabel (Node × Node × Bool) send p
rL p = evLabel (Node × Node × Bool) receive p
gL : Node × Token → Ev
gL p = evLabel (Node × Token) ring p

data T0 : St0 → DProcB → Ev → Set₁ where
  t0e-accE  :         T0 e0      (NodeR n0)               (gL (n0 , Empty))
  t0e-accF  : ∀ p   → T0 e0      (NodeF n0 p)             (gL (n0 , Full p))
  t0r-send  : ∀ m   → T0 r0      (NodeF n0 (n0 , n1 , m)) (sL (n0 , n1 , m))
  t0r-fwdE  :         T0 r0      (NodeE n0)               (gL (n1 , Empty))
  t0ff-fwd  : ∀ m   → T0 (f0f m) (NodeE n0)               (gL (n1 , Full (n0 , n1 , m)))
  t0fr-recv : ∀ m   → T0 (f0r m) (NodeR n0)               (rL (n0 , n1 , m))

data T1 : St1 → DProcB → Ev → Set₁ where
  t1e-accE  :         T1 e1      (NodeR n1)               (gL (n1 , Empty))
  t1e-accF  : ∀ p   → T1 e1      (NodeF n1 p)             (gL (n1 , Full p))
  t1r-send  : ∀ m   → T1 r1      (NodeF n1 (n1 , n0 , m)) (sL (n1 , n0 , m))
  t1r-fwdE  :         T1 r1      (NodeE n1)               (gL (n0 , Empty))
  t1ff-recv : ∀ m   → T1 (f1f m) (NodeR n1)               (rL (n1 , n0 , m))
  t1fr-fwd  : ∀ m   → T1 (f1r m) (NodeE n1)               (gL (n0 , Full (n1 , n0 , m)))

inv0 : ∀ s0 {t′ e} → nd0 s0 ─[ ev (evl e) ]─► t′ → T0 s0 t′ e
inv0 e0 (sVis {at = _ , send} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , ring} {a = fzero , Empty} refl br) =
  subst (λ z → T0 e0 z _) (just-injective br) t0e-accE
inv0 e0 (sVis {at = _ , ring} {a = fsuc fzero , Empty} refl br) = case br of λ ()
inv0 e0 (sVis {at = _ , ring} {a = fzero , Full p} refl br) =
  subst (λ z → T0 e0 z _) (just-injective br) (t0e-accF p)
inv0 e0 (sVis {at = _ , ring} {a = fsuc fzero , Full p} refl br) = case br of λ ()
inv0 r0 (sVis {at = _ , send} {a = fzero , fzero , m} refl br) = case br of λ ()
inv0 r0 (sVis {at = _ , send} {a = fzero , fsuc fzero , m} refl br) =
  subst (λ z → T0 r0 z _) (just-injective br) (t0r-send m)
inv0 r0 (sVis {at = _ , send} {a = fsuc fzero , dst , m} refl br) = case br of λ ()
inv0 r0 (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 r0 (sVis {at = _ , ring} {a = fzero , Empty} refl br) = case br of λ ()
inv0 r0 (sVis {at = _ , ring} {a = fsuc fzero , Empty} refl br) =
  subst (λ z → T0 r0 z _) (just-injective br) t0r-fwdE
inv0 r0 (sVis {at = _ , ring} {a = j , Full p} refl br) = case br of λ ()
inv0 (f0f m) (sVis {at = _ , send} refl br) = case br of λ ()
inv0 (f0f m) (sVis {at = _ , receive} refl br) = case br of λ ()
inv0 (f0f m) (sVis {at = _ , ring} {a = j , Empty} refl br) = case br of λ ()
inv0 (f0f m) (sVis {at = _ , ring} {a = fzero , Full p} refl br) = case br of λ ()
inv0 (f0f m) (sVis {at = _ , ring} {a = fsuc fzero , Full (s′ , r′ , m′)} refl br)
  with pkt≟ (s′ , r′ , m′) (n0 , n1 , m)
... | yes refl = subst (λ z → T0 (f0f m) z _) (just-injective br) (t0ff-fwd m)
... | no  _    = case br of λ ()
inv0 (f0r m) (sVis {at = _ , send} refl br) = case br of λ ()
inv0 (f0r m) (sVis {at = _ , receive} {a = fzero , fzero , m′} refl br) = case br of λ ()
inv0 (f0r m) (sVis {at = _ , receive} {a = fzero , fsuc fzero , m′} refl br) with m′ B≟ m
... | yes refl = subst (λ z → T0 (f0r m) z _) (just-injective br) (t0fr-recv m)
... | no  _    = case br of λ ()
inv0 (f0r m) (sVis {at = _ , receive} {a = fsuc fzero , src , m′} refl br) = case br of λ ()
inv0 (f0r m) (sVis {at = _ , ring} {a = j , Empty} refl br) = case br of λ ()
inv0 (f0r m) (sVis {at = _ , ring} {a = j , Full p} refl br) = case br of λ ()

inv1 : ∀ s1 {t′ e} → nd1 s1 ─[ ev (evl e) ]─► t′ → T1 s1 t′ e
inv1 e1 (sVis {at = _ , send} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , ring} {a = fzero , Empty} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , ring} {a = fsuc fzero , Empty} refl br) =
  subst (λ z → T1 e1 z _) (just-injective br) t1e-accE
inv1 e1 (sVis {at = _ , ring} {a = fzero , Full p} refl br) = case br of λ ()
inv1 e1 (sVis {at = _ , ring} {a = fsuc fzero , Full p} refl br) =
  subst (λ z → T1 e1 z _) (just-injective br) (t1e-accF p)
inv1 r1 (sVis {at = _ , send} {a = fsuc fzero , fsuc fzero , m} refl br) = case br of λ ()
inv1 r1 (sVis {at = _ , send} {a = fsuc fzero , fzero , m} refl br) =
  subst (λ z → T1 r1 z _) (just-injective br) (t1r-send m)
inv1 r1 (sVis {at = _ , send} {a = fzero , dst , m} refl br) = case br of λ ()
inv1 r1 (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 r1 (sVis {at = _ , ring} {a = fzero , Empty} refl br) =
  subst (λ z → T1 r1 z _) (just-injective br) t1r-fwdE
inv1 r1 (sVis {at = _ , ring} {a = fsuc fzero , Empty} refl br) = case br of λ ()
inv1 r1 (sVis {at = _ , ring} {a = j , Full p} refl br) = case br of λ ()
inv1 (f1f m) (sVis {at = _ , send} refl br) = case br of λ ()
inv1 (f1f m) (sVis {at = _ , receive} {a = fsuc fzero , fzero , m′} refl br) with m′ B≟ m
... | yes refl = subst (λ z → T1 (f1f m) z _) (just-injective br) (t1ff-recv m)
... | no  _    = case br of λ ()
inv1 (f1f m) (sVis {at = _ , receive} {a = fsuc fzero , fsuc fzero , m′} refl br) = case br of λ ()
inv1 (f1f m) (sVis {at = _ , receive} {a = fzero , src , m′} refl br) = case br of λ ()
inv1 (f1f m) (sVis {at = _ , ring} {a = j , Empty} refl br) = case br of λ ()
inv1 (f1f m) (sVis {at = _ , ring} {a = j , Full p} refl br) = case br of λ ()
inv1 (f1r m) (sVis {at = _ , send} refl br) = case br of λ ()
inv1 (f1r m) (sVis {at = _ , receive} refl br) = case br of λ ()
inv1 (f1r m) (sVis {at = _ , ring} {a = j , Empty} refl br) = case br of λ ()
inv1 (f1r m) (sVis {at = _ , ring} {a = fsuc fzero , Full p} refl br) = case br of λ ()
inv1 (f1r m) (sVis {at = _ , ring} {a = fzero , Full (s′ , r′ , m′)} refl br)
  with pkt≟ (s′ , r′ , m′) (n1 , n0 , m)
... | yes refl = subst (λ z → T1 (f1r m) z _) (just-injective br) (t1fr-fwd m)
... | no  _    = case br of λ ()

-- §7.5 TBuff forward steps (its react offers reduce, so these hold by `refl`).
tb-recv : ∀ x xs → TBuff (x ∷ xs) ─[ ev (evl (rL (n1 , n0 , x))) ]─► TBuff xs
tb-recv true  xs = sVis {at = (Node × Node × Bool) , receive} {a = n1 , n0 , true}  refl refl
tb-recv false xs = sVis {at = (Node × Node × Bool) , receive} {a = n1 , n0 , false} refl refl

tb-send0 : ∀ m → TBuff [] ─[ ev (evl (sL (n0 , n1 , m))) ]─► TBuff (m ∷ [])
tb-send0 m = sVis {at = (Node × Node × Bool) , send} {a = n0 , n1 , m} refl refl

-- §7.6 The weak-simulation relation.  Reachable configs are enumerated by `Reach`
-- (6 shapes, content length ≤ 1); `RR` keeps the node states s0/s1 ABSTRACT (so the
-- composite's `.force` stays stuck on `nd0 s0`/`nd1 s1`, which lets the α-parallel
-- inversion infer the alphabets `A n0`/`B1`), pinning them only via the `Reach`
-- witness — which is split AFTER the inversion.
data Reach : St0 → St1 → List Bool → Set where
  reachA :        Reach r0      e1      []             -- (NodeR 0, NodeE 1)
  reachB : ∀ m →  Reach (f0f m) e1      (m ∷ [])       -- (NodeF 0 (0,1,m), NodeE 1)
  reachC : ∀ m →  Reach e0      (f1f m) (m ∷ [])       -- (NodeE 0, NodeF 1 (0,1,m))
  reachD :        Reach e0      r1      []             -- (NodeE 0, NodeR 1)
  reachE : ∀ m →  Reach e0      (f1r m) []             -- (NodeE 0, NodeF 1 (1,0,m))
  reachF : ∀ m →  Reach (f0r m) e1      []             -- (NodeF 0 (1,0,m), NodeE 1)

data RR : PTree BEv (ExtI BEv) (⊤poly {lzero} × ⊤poly {lzero}) → BProc → Set₁ where
  rr : ∀ s0 s1 cs → Reach s0 s1 cs → RR (Cfg s0 s1 ∖ obsES) (TBuff cs)

-- §7.7 Forward matching of a VISIBLE (observed) move.
fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero} × ⊤poly {lzero})} {p′}
     → RR p q → p ─[ ev l ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × RR p′ q′)
fwdE (rr s0 s1 cs rc) stp with Hide-ev-elim obsES (Cfg s0 s1) stp
... | he√ eqf = ⊥-elim (noSys√ s0 s1 eqf)
... | heV P′ ¬c pstp with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
-- VISIBLE SYNC : sync events are all `ring` (hidden) → contradict via ¬c, or the
-- solo node fires a send/receive that cannot be in the other alphabet.
...     | vSync pA pB p0s p1s with rc
...       | reachA with inv0 r0 p0s
...         | t0r-send m = case pB of λ { (inj₁ ()) ; (inj₂ ()) }
...         | t0r-fwdE   = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reachB m
      with inv0 (f0f m) p0s
...         | t0ff-fwd m = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reachC m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬c ⋆)
...         | t0e-accF p = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reachD
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬c ⋆)
...         | t0e-accF p = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reachE m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬c ⋆)
...         | t0e-accF p = ⊥-elim (¬c ⋆)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reachF m
      with inv0 (f0r m) p0s
...         | t0fr-recv m = case pB of λ { (inj₁ ()) ; (inj₂ ()) }
-- VISIBLE SOLO-LEFT : the only observed left move is `send.0.1` (from `r0`).
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s with rc
...       | reachA with inv0 r0 p0s
...         | t0r-send m = _ , wev τ*-refl (tb-send0 m) τ*-refl , rr (f0f m) e1 (m ∷ []) (reachB m)
...         | t0r-fwdE   = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reachB m
      with inv0 (f0f m) p0s
...         | t0ff-fwd m = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reachC m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reachD
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reachE m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reachF m
      with inv0 (f0r m) p0s
...         | t0fr-recv m = ⊥-elim (¬c ⋆)              -- receive.0.1 is hidden
-- VISIBLE SOLO-RIGHT : the only observed right move is `receive.1.0` (from `f1f`).
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s with rc
...       | reachA with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reachB m
      with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reachC m
      with inv1 (f1f m) p1s
...         | t1ff-recv m = _ , wev τ*-refl (tb-recv m []) τ*-refl , rr e0 r1 [] reachD
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reachD
      with inv1 r1 p1s
...         | t1r-send m = ⊥-elim (¬c ⋆)               -- send.1.0 is hidden
...         | t1r-fwdE   = ⊥-elim (¬pA (inj₁ refl))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reachE m
      with inv1 (f1r m) p1s
...         | t1fr-fwd m = ⊥-elim (¬pA (inj₁ refl))
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reachF m
      with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))

-- §7.8 Forward matching of a τ (hidden) move: `TBuff` stays put, contents preserved.
fwdT : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × RR p′ q′)
fwdT (rr s0 s1 cs rc) stp with Hide-τ-elim obsES (Cfg s0 s1) stp
... | hτP P′ pτ refl with αpar-τ-step-inv pτ
...   | inj₁ (_ , t0τ , _) = ⊥-elim (noτ0 s0 t0τ)
...   | inj₂ (_ , t1τ , _) = ⊥-elim (noτ1 s1 t1τ)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
-- HIDDEN SOLO-LEFT : reverse `receive.0.1` (from `f0r`) is a real hidden move.
...     | vSoloL pA ¬pB p0s with rc
...       | reachA with inv0 r0 p0s
...         | t0r-send m = ⊥-elim csat              -- send.0.1 is observed, not hidden
...         | t0r-fwdE   = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reachB m
      with inv0 (f0f m) p0s
...         | t0ff-fwd m = ⊥-elim (¬pB (inj₁ (inj₁ refl)))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reachC m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reachD
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reachE m
      with inv0 e0 p0s
...         | t0e-accE   = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
...         | t0e-accF p = ⊥-elim (¬pB (inj₁ (inj₂ refl)))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reachF m
      with inv0 (f0r m) p0s
...         | t0fr-recv m = _ , wτ τ*-refl , rr r0 e1 [] reachA
-- HIDDEN SOLO-RIGHT : reverse `send.1.0` (from `r1`) is a real hidden move.
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s with rc
...       | reachA with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reachB m
      with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reachC m
      with inv1 (f1f m) p1s
...         | t1ff-recv m = ⊥-elim csat              -- receive.1.0 is observed, not hidden
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reachD
      with inv1 r1 p1s
...         | t1r-send m = _ , wτ τ*-refl , rr e0 (f1r m) [] (reachE m)
...         | t1r-fwdE   = ⊥-elim (¬pA (inj₁ refl))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reachE m
      with inv1 (f1r m) p1s
...         | t1fr-fwd m = ⊥-elim (¬pA (inj₁ refl))
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reachF m
      with inv1 e1 p1s
...         | t1e-accE   = ⊥-elim (¬pA (inj₂ refl))
...         | t1e-accF p = ⊥-elim (¬pA (inj₂ refl))
-- HIDDEN SYNC : the four `ring` hops (empty forward, full forward, empty back, full back).
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s with rc
...       | reachA with inv0 r0 p0s | inv1 e1 p1s
...         | t0r-fwdE | t1e-accE = _ , wτ τ*-refl , rr e0 r1 [] reachD
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reachB m
      with inv0 (f0f m) p0s | inv1 e1 p1s
...         | t0ff-fwd m | t1e-accF p = _ , wτ τ*-refl , rr e0 (f1f m) (m ∷ []) (reachC m)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reachC m
      with inv1 (f1f m) p1s
...         | t1ff-recv m = case pA of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reachD
      with inv0 e0 p0s | inv1 r1 p1s
...         | t0e-accE | t1r-fwdE = _ , wτ τ*-refl , rr r0 e1 [] reachA
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reachE m
      with inv0 e0 p0s | inv1 (f1r m) p1s
...         | t0e-accF p | t1fr-fwd m = _ , wτ τ*-refl , rr (f0r m) e1 [] (reachF m)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reachF m
      with inv0 (f0r m) p0s
...         | t0fr-recv m = case pB of λ { (inj₁ ()) ; (inj₂ ()) }

module M = WSimFromRel RR fwdE fwdT

-- assert  TBuff(<>) [T= TokRingH∖diff(…)   (traces TokRingObs ⊆ traces (TBuff []))
tokring-TBuff : TBuff [] ⊑T TokRingObs
tokring-TBuff = wsim→⊑T (M.rel→wsim (rr r0 e1 [] reachA))
