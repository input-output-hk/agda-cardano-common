{-# OPTIONS --guardedness #-}

-- UCS chapter 4: the SLIDING WINDOW PROTOCOL (SWP), pipelining witnesses.
-- Modelled after swp.csp (UCS ch. 4, Bill Roscoe).  Reduced: window W = 2,
-- SEQ = Fin 3, DATA = Bool, bounded-loss channels at L = 2.  Offers PINNED.
-- (Structural template: CSP.Examples.UCS.Ch4.ABP — the window-1 case.)
--
-- swp.csp (modelled fragment):
--   SEND: a window of ≤ W unacked (seq,data); left?x accepted when not full
--         (record (nextseq,x), advance nextseq mod 3); a!(seq,x) may (re)transmit
--         any in-flight packet; d?ack cumulatively slides the window.
--   REC(exp): b?(s,dat) -> if s==exp then right!dat -> c!exp -> REC(exp+1)
--                                    else c!(exp-1) -> REC(exp)   (re-ack, discard)
--   BE(n)/BE'(n): bounded-loss 1-place channels (as abp.csp), L = 2.
--   SystemW = SEND [|{|a,d|}|] ((BE ||| BE') [|{|b,c|}|] REC);  SWPH = SystemW \ {|a,b,c,d|}
--   COPY = left?x -> right!x -> COPY   (the one-place buffer, for the contrast)
--
-- HEADLINE (deferred, ABP-style): BUFF W [FD= SWPH.  THIS module proves the
-- existential pipelining witnesses swp-delivers2 / swp-beats-copy instead.
--
-- MODEL REDUCTIONS (documented per the task spec).  Faithful to swp.csp except:
--   * Window bound W = 2         (the .csp is parametric in W; W = 2 is the
--                                 smallest window that exhibits pipelining, i.e.
--                                 two packets in flight without waiting for an ack).
--   * SEQ = Fin 3                (sequence numbers mod 3, the smallest modulus
--                                 that can distinguish a window of 2 in-flight
--                                 packets from a stale/wrapped sequence number).
--   * DATA = Bool                (as in the ABP reduction).
--   * L = 2                      (bounded-loss channels, as in abp.csp / ABP.agda).
--
-- FAITHFULNESS: the sender's (re)transmission `a!(seq,x)`, the channels' forwards
-- `b!(s,dat)` / `d!ack`, and the receiver's acks/deliveries `right!dat` / `c!ackv`
-- are all PINNED (the offer fires only at the SPECIFIC held value), exactly as in
-- swp.csp.  An over-approximated (payload-discarded) model would be UNSOUND.
--
-- The recursive processes are written as inlined `react` copatterns (corecursive
-- calls sit DIRECTLY under `just`, guarded by the enclosing `react`), following
-- CSP.Examples.UCS.Ch4.ABP.  Every intermediate output / internal-choice state is
-- therefore its OWN copattern node (`BEout`/`BElossy`/`RECdel`/`RECack`/… ): the
-- `_⟶_` / `_⊓_` operators cannot be used inside `just` because they wrap the
-- corecursive call in a function application, which the guardedness checker rejects.

module CSP.Examples.UCS.Ch4.SlidingWindow where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; Σ; Σ-syntax)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. The event type and its decidable equality.
--   left, right : external interface, carry a DATA value (Bool).
--   a, b        : data channel (a into the channel, b out), carry (SEQ , DATA).
--   c, d        : ack  channel (c into the channel, d out), carry a SEQ.
data SWPEv : Set → Set where
  left  : SWPEv Bool            -- external input
  right : SWPEv Bool            -- external output
  a     : SWPEv (Fin 3 × Bool)  -- data channel in : (seq , data)
  b     : SWPEv (Fin 3 × Bool)  -- data channel out
  c     : SWPEv (Fin 3)         -- ack channel in  : seq
  d     : SWPEv (Fin 3)         -- ack channel out

SWPEv-≟ : (x y : AnyTypes SWPEv) → Dec (x ≡ y)
SWPEv-≟ (_ , left)  (_ , left)  = yes refl
SWPEv-≟ (_ , right) (_ , right) = yes refl
SWPEv-≟ (_ , a)     (_ , a)     = yes refl
SWPEv-≟ (_ , b)     (_ , b)     = yes refl
SWPEv-≟ (_ , c)     (_ , c)     = yes refl
SWPEv-≟ (_ , d)     (_ , d)     = yes refl
SWPEv-≟ (_ , left)  (_ , right) = no (λ ())
SWPEv-≟ (_ , left)  (_ , a)     = no (λ ())
SWPEv-≟ (_ , left)  (_ , b)     = no (λ ())
SWPEv-≟ (_ , left)  (_ , c)     = no (λ ())
SWPEv-≟ (_ , left)  (_ , d)     = no (λ ())
SWPEv-≟ (_ , right) (_ , left)  = no (λ ())
SWPEv-≟ (_ , right) (_ , a)     = no (λ ())
SWPEv-≟ (_ , right) (_ , b)     = no (λ ())
SWPEv-≟ (_ , right) (_ , c)     = no (λ ())
SWPEv-≟ (_ , right) (_ , d)     = no (λ ())
SWPEv-≟ (_ , a)     (_ , left)  = no (λ ())
SWPEv-≟ (_ , a)     (_ , right) = no (λ ())
SWPEv-≟ (_ , a)     (_ , b)     = no (λ ())
SWPEv-≟ (_ , a)     (_ , c)     = no (λ ())
SWPEv-≟ (_ , a)     (_ , d)     = no (λ ())
SWPEv-≟ (_ , b)     (_ , left)  = no (λ ())
SWPEv-≟ (_ , b)     (_ , right) = no (λ ())
SWPEv-≟ (_ , b)     (_ , a)     = no (λ ())
SWPEv-≟ (_ , b)     (_ , c)     = no (λ ())
SWPEv-≟ (_ , b)     (_ , d)     = no (λ ())
SWPEv-≟ (_ , c)     (_ , left)  = no (λ ())
SWPEv-≟ (_ , c)     (_ , right) = no (λ ())
SWPEv-≟ (_ , c)     (_ , a)     = no (λ ())
SWPEv-≟ (_ , c)     (_ , b)     = no (λ ())
SWPEv-≟ (_ , c)     (_ , d)     = no (λ ())
SWPEv-≟ (_ , d)     (_ , left)  = no (λ ())
SWPEv-≟ (_ , d)     (_ , right) = no (λ ())
SWPEv-≟ (_ , d)     (_ , a)     = no (λ ())
SWPEv-≟ (_ , d)     (_ , b)     = no (λ ())
SWPEv-≟ (_ , d)     (_ , c)     = no (λ ())

open import CSP.Operators SWPEv-≟
open EventSet
open import Semantics.LTS      {E = SWPEv} {I = ExtI SWPEv}
open import Semantics.Failures {E = SWPEv} {I = ExtI SWPEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Traces.TraceLawsParallel SWPEv-≟
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsHide     SWPEv-≟
  using (Hide-keep; Hide-hidden; Hide-τ)

SProc : Set₁
SProc = PTree SWPEv (ExtI SWPEv) (⊤poly {lzero})

-- DecEq (Fin 3 × Bool) for pinning the `a`/`b` channel outputs.
instance
  DecEq-F×B : DecEq (Fin 3 × Bool)
  DecEq-F×B ._≟_ = ×-≡-dec _F≟_ _B≟_

------------------------------------------------------------------------------------
-- §2. Sequence-number successor/predecessor mod 3, and the sender's window type.
suc3 : Fin 3 → Fin 3
suc3 fzero               = fsuc fzero
suc3 (fsuc fzero)        = fsuc (fsuc fzero)
suc3 (fsuc (fsuc fzero)) = fzero

pred3 : Fin 3 → Fin 3
pred3 fzero               = fsuc (fsuc fzero)
pred3 (fsuc fzero)        = fzero
pred3 (fsuc (fsuc fzero)) = fsuc fzero

data Win : Set where
  w0 : Win                                     -- window empty
  w1 : (Fin 3 × Bool) → Win                    -- one packet in flight
  w2 : (Fin 3 × Bool) → (Fin 3 × Bool) → Win   -- two in flight (full, W = 2)

------------------------------------------------------------------------------------
-- §3. Forward declarations of every corecursive node.
SEND      : Win → Fin 3 → SProc
REC       : Fin 3 → SProc
RECdel    : Bool → Fin 3 → Fin 3 → SProc   -- pending right!dat, then ack, then REC nx
RECack    : Fin 3 → Fin 3 → SProc          -- pending c!ackv, then REC nx
BE        : Fin 2 → SProc                  -- data channel a → b
BEout     : (Fin 3 × Bool) → SProc         -- pending b!p, then BE (fsuc fzero)
BElossy   : (Fin 3 × Bool) → SProc         -- (b!p → BE 1) ⊓ (lose → BE 0)
BE′       : Fin 2 → SProc                  -- ack channel c → d
BE′out    : Fin 3 → SProc
BE′lossy  : Fin 3 → SProc
COPY      : SProc
COPYout   : Bool → SProc

------------------------------------------------------------------------------------
-- §4. The sender.
-- swp.csp:
--   SEND: a window of ≤ W unacked (seq,data); left?x accepted when not full
--         (record (nextseq,x), advance nextseq mod 3); a!(seq,x) may (re)transmit
--         any in-flight packet; d?ack cumulatively slides the window.

-- empty window: accept left (→ w1), ignore stray ack.
force (SEND w0 nx) = react
  (λ where
     (_ , left)  x → just (SEND (w1 (nx , x)) (suc3 nx))
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → just (SEND w0 nx))
  ∅t

-- one in flight p: accept left (→ w2), (re)transmit p on a (PINNED), ack slides.
force (SEND (w1 p) nx) = react
  (λ where
     (_ , left)  x → just (SEND (w2 p (nx , x)) (suc3 nx))
     (_ , right) _ → nothing
     (_ , a)     q → case q ≟ p of λ where
         (yes _) → just (SEND (w1 p) nx)
         (no  _) → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     ack → case ack F≟ proj₁ p of λ where
         (yes _) → just (SEND w0 nx)
         (no  _) → just (SEND (w1 p) nx))
  ∅t

-- window full (p oldest, q newest): no left; (re)transmit p or q on a (PINNED);
-- ack of p's seq slides to w1 q.
force (SEND (w2 p q) nx) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     r → case r ≟ p of λ where
         (yes _) → just (SEND (w2 p q) nx)
         (no  _) → case r ≟ q of λ where
             (yes _) → just (SEND (w2 p q) nx)
             (no  _) → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     ack → case ack F≟ proj₁ q of λ where
         (yes _) → just (SEND w0 nx)
         (no  _) → case ack F≟ proj₁ p of λ where
             (yes _) → just (SEND (w1 q) nx)
             (no  _) → just (SEND (w2 p q) nx))
  ∅t

SND : SProc
SND = SEND w0 fzero

------------------------------------------------------------------------------------
-- §5. The receiver.
-- swp.csp:
--   REC(exp): b?(s,dat) -> if s==exp then right!dat -> c!exp -> REC(exp+1)
--                                    else c!(exp-1) -> REC(exp)   (re-ack, discard)

-- expect seq `exp`: on match deliver+ack+advance, on mismatch re-ack and discard.
force (REC exp) = react
  (λ where
     (_ , left)  _         → nothing
     (_ , right) _         → nothing
     (_ , a)     _         → nothing
     (_ , b)     (s , dat) → case s F≟ exp of λ where
         (yes _) → just (RECdel dat exp (suc3 exp))
         (no  _) → just (RECack (pred3 exp) exp)
     (_ , c)     _         → nothing
     (_ , d)     _         → nothing)
  ∅t

-- pending PINNED delivery `right!dat`, then the ack, then REC nx.
force (RECdel dat ackv nx) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) y → case y B≟ dat of λ where
         (yes _) → just (RECack ackv nx)
         (no  _) → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → nothing)
  ∅t

-- pending PINNED ack `c!ackv`, then REC nx.
force (RECack ackv nx) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     t → case t F≟ ackv of λ where
         (yes _) → just (REC nx)
         (no  _) → nothing
     (_ , d)     _ → nothing)
  ∅t

RCV : SProc
RCV = REC fzero

------------------------------------------------------------------------------------
-- §6. The bounded-loss channels (L = 2).
-- swp.csp:
--   BE(n)/BE'(n): bounded-loss 1-place channels (as abp.csp), L = 2.
-- Here BE is the data channel a → b, BE' the ack channel c → d.  n : Fin 2;
-- n = 0 must forward, n = 1 may forward OR lose (drop the value, drop to n = 0).

-- n = 0: no loss branch — must forward the held (s,x) on b.
force (BE fzero) = react
  (λ where
     (_ , left)  _       → nothing
     (_ , right) _       → nothing
     (_ , a)     (s , x) → just (BEout (s , x))
     (_ , b)     _       → nothing
     (_ , c)     _       → nothing
     (_ , d)     _       → nothing)
  ∅t

-- n = 1: forward on b, OR lose and drop to n = 0.
force (BE (fsuc fzero)) = react
  (λ where
     (_ , left)  _       → nothing
     (_ , right) _       → nothing
     (_ , a)     (s , x) → just (BElossy (s , x))
     (_ , b)     _       → nothing
     (_ , c)     _       → nothing
     (_ , d)     _       → nothing)
  ∅t

-- pending PINNED output `b!p`, then reset to BE (L-1).
force (BEout p) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     q → case q ≟ p of λ where
         (yes _) → just (BE (fsuc fzero))
         (no  _) → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → nothing)
  ∅t

-- internal choice (forward the held value) ⊓ (lose it, drop to n = 0); written as a
-- bare `react ∅v` with two τ-branches at fin index 0 / 1 (an inlined `_⊓_`).
force (BElossy p) = react ∅v
  (λ where
     (_ , base _)              _                     → nothing
     (_ , pair _ _)            _                     → nothing
     (_ , fin)                 (lift fzero)          → just (BEout p)
     (_ , fin)                 (lift (fsuc fzero))   → just (BE fzero)
     (_ , fin)                 (lift (fsuc (fsuc _))) → nothing)

force (BE′ fzero) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     t → just (BE′out t)
     (_ , d)     _ → nothing)
  ∅t

force (BE′ (fsuc fzero)) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     t → just (BE′lossy t)
     (_ , d)     _ → nothing)
  ∅t

-- pending PINNED output `d!t`, then reset to BE' (L-1).
force (BE′out t) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     u → case u F≟ t of λ where
         (yes _) → just (BE′ (fsuc fzero))
         (no  _) → nothing)
  ∅t

force (BE′lossy t) = react ∅v
  (λ where
     (_ , base _)              _                     → nothing
     (_ , pair _ _)            _                     → nothing
     (_ , fin)                 (lift fzero)          → just (BE′out t)
     (_ , fin)                 (lift (fsuc fzero))   → just (BE′ fzero)
     (_ , fin)                 (lift (fsuc (fsuc _))) → nothing)

------------------------------------------------------------------------------------
-- §7. Sync sets, the system, hiding, and COPY.
--   {|a,d|} between SND and the channel/receiver block; {|b,c|} between the two
--   channels and the receiver; {|a,b,c,d|} hidden in SWPH.
adES bcES intES : EventSet
adES .mem (_ , a) _     = ⊤poly {lzero}
adES .mem (_ , d) _     = ⊤poly {lzero}
adES .mem (_ , left)  _ = ⊥
adES .mem (_ , right) _ = ⊥
adES .mem (_ , b) _     = ⊥
adES .mem (_ , c) _     = ⊥
adES .dec (_ , a) _     = yes tt
adES .dec (_ , d) _     = yes tt
adES .dec (_ , left)  _ = no (λ z → z)
adES .dec (_ , right) _ = no (λ z → z)
adES .dec (_ , b) _     = no (λ z → z)
adES .dec (_ , c) _     = no (λ z → z)

bcES .mem (_ , b) _     = ⊤poly {lzero}
bcES .mem (_ , c) _     = ⊤poly {lzero}
bcES .mem (_ , left)  _ = ⊥
bcES .mem (_ , right) _ = ⊥
bcES .mem (_ , a) _     = ⊥
bcES .mem (_ , d) _     = ⊥
bcES .dec (_ , b) _     = yes tt
bcES .dec (_ , c) _     = yes tt
bcES .dec (_ , left)  _ = no (λ z → z)
bcES .dec (_ , right) _ = no (λ z → z)
bcES .dec (_ , a) _     = no (λ z → z)
bcES .dec (_ , d) _     = no (λ z → z)

intES .mem (_ , a) _     = ⊤poly {lzero}
intES .mem (_ , b) _     = ⊤poly {lzero}
intES .mem (_ , c) _     = ⊤poly {lzero}
intES .mem (_ , d) _     = ⊤poly {lzero}
intES .mem (_ , left)  _ = ⊥
intES .mem (_ , right) _ = ⊥
intES .dec (_ , a) _     = yes tt
intES .dec (_ , b) _     = yes tt
intES .dec (_ , c) _     = yes tt
intES .dec (_ , d) _     = yes tt
intES .dec (_ , left)  _ = no (λ z → z)
intES .dec (_ , right) _ = no (λ z → z)

-- swp.csp:
--   SystemW = SEND [|{|a,d|}|] ((BE ||| BE') [|{|b,c|}|] REC)
SystemW : SProc
SystemW = Par⊤ adES SND (Par⊤ bcES (BE (fsuc fzero) ⦀ BE′ (fsuc fzero)) RCV)

-- The hidden system:  SystemW \ {|a,b,c,d|}
SWPH : SProc
SWPH = SystemW ∖ intES

-- swp.csp:  COPY = left?x -> right!x -> COPY   (the one-place buffer, for contrast).
force COPY = react
  (λ where
     (_ , left)  x → just (COPYout x)
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → nothing)
  ∅t

force (COPYout x) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) y → case y B≟ x of λ where
         (yes _) → just COPY
         (no  _) → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §B. PIPELINED IN-ORDER DELIVERY: the trace witness `swp-delivers2`.
--
-- SWPH can perform  left true · left false · right true · right false — i.e. it
-- ACCEPTS a SECOND message (left false) while the first (left true) is still
-- unacknowledged (window W = 2), and then delivers both in order.  This is the
-- pipelining a one-place COPY buffer cannot do.  Built as one finite forward
-- ⟹ derivation of 11 composite steps (4 visible left/right, 7 hidden a/b/c/loss).
------------------------------------------------------------------------------------

-- §B.1  State abbreviations for the four components along the trajectory.
-- SEND states (nextseq threaded mod 3):
sA sB sC : SProc
sA = SEND w0 fzero                                             -- empty window
sB = SEND (w1 (fzero , true)) (fsuc fzero)                     -- (0,t) in flight
sC = SEND (w2 (fzero , true) (fsuc fzero , false))            -- (0,t),(1,f) in flight
       (fsuc (fsuc fzero))

-- data-channel BE states:
beA beB beC beD beE : SProc
beA = BE (fsuc fzero)              -- ready (n = 1)
beB = BElossy (fzero , true)       -- holding (0,t), may fwd/lose
beC = BEout (fzero , true)         -- about to emit b.(0,t)
beD = BElossy (fsuc fzero , false) -- holding (1,f)
beE = BEout (fsuc fzero , false)   -- about to emit b.(1,f)

-- ack-channel BE′ states:
be′A be′B : SProc
be′A = BE′ (fsuc fzero)             -- ready (n = 1)
be′B = BE′lossy fzero               -- holding ack 0

-- receiver states:
rA rB rC rD rE rF : SProc
rA = REC fzero                                            -- expect seq 0
rB = RECdel true fzero (fsuc fzero)                       -- deliver t, then ack 0
rC = RECack fzero (fsuc fzero)                            -- ack 0, then expect 1
rD = REC (fsuc fzero)                                     -- expect seq 1
rE = RECdel false (fsuc fzero) (fsuc (fsuc fzero))        -- deliver f, then ack 1
rF = RECack (fsuc fzero) (fsuc (fsuc fzero))              -- ack 1, then expect 2

-- §B.2  Component (leaf) steps.  Each is one `sVis`/`sTau … refl refl`: the state's
-- `force` copattern reduces (first refl), and the offer/branch reduces on the concrete
-- value (second refl; the `case _≟_ of yes` collapses).

-- SEND accepts left true from the empty window (records (0,t), nextseq 0 → 1).
send-accept0 : sA ─[ ev (evl (evLabel Bool left true)) ]─► sB
send-accept0 = sVis {at = Bool , left} {a = true} refl refl

-- SEND accepts a SECOND message left false while (0,t) is unacked (→ full window).
send-accept1 : sB ─[ ev (evl (evLabel Bool left false)) ]─► sC
send-accept1 = sVis {at = Bool , left} {a = false} refl refl

-- SEND (re)transmits the in-flight (0,t) on a (pinned; window unchanged).
send-retx-w1 : sB ─[ ev (evl (evLabel (Fin 3 × Bool) a (fzero , true))) ]─► sB
send-retx-w1 = sVis {at = (Fin 3 × Bool) , a} {a = fzero , true} refl refl

-- SEND (re)transmits the newer (1,f) from the full window (pinned; unchanged).
send-retx-w2 : sC ─[ ev (evl (evLabel (Fin 3 × Bool) a (fsuc fzero , false))) ]─► sC
send-retx-w2 = sVis {at = (Fin 3 × Bool) , a} {a = fsuc fzero , false} refl refl

-- BE (n = 1) receives (s,x) on a and holds it (may forward or lose).
be-recv : ∀ (s : Fin 3) (x : Bool)
        → beA ─[ ev (evl (evLabel (Fin 3 × Bool) a (s , x))) ]─► BElossy (s , x)
be-recv s x = sVis {at = (Fin 3 × Bool) , a} {a = s , x} refl refl

-- BElossy takes the FORWARD τ-branch (internal choice fin 0 → BEout).
be-fwd : ∀ (p : Fin 3 × Bool) → BElossy p ─[ τ ]─► BEout p
be-fwd p = sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

-- BEout emits the held packet on b (pinned), resetting BE to n = 1.
be-emit0 : beC ─[ ev (evl (evLabel (Fin 3 × Bool) b (fzero , true))) ]─► beA
be-emit0 = sVis {at = (Fin 3 × Bool) , b} {a = fzero , true} refl refl

be-emit1 : beE ─[ ev (evl (evLabel (Fin 3 × Bool) b (fsuc fzero , false))) ]─► beA
be-emit1 = sVis {at = (Fin 3 × Bool) , b} {a = fsuc fzero , false} refl refl

-- REC receives a matching b.(exp,dat) and enters its delivery state.
rec-recv0 : rA ─[ ev (evl (evLabel (Fin 3 × Bool) b (fzero , true))) ]─► rB
rec-recv0 = sVis {at = (Fin 3 × Bool) , b} {a = fzero , true} refl refl

rec-recv1 : rD ─[ ev (evl (evLabel (Fin 3 × Bool) b (fsuc fzero , false))) ]─► rE
rec-recv1 = sVis {at = (Fin 3 × Bool) , b} {a = fsuc fzero , false} refl refl

-- REC delivers the pinned payload on right, then pends the ack.
rec-deliver0 : rB ─[ ev (evl (evLabel Bool right true)) ]─► rC
rec-deliver0 = sVis {at = Bool , right} {a = true} refl refl

rec-deliver1 : rE ─[ ev (evl (evLabel Bool right false)) ]─► rF
rec-deliver1 = sVis {at = Bool , right} {a = false} refl refl

-- REC emits the pinned ack on c, advancing the expected sequence.
rec-ack0 : rC ─[ ev (evl (evLabel (Fin 3) c fzero)) ]─► rD
rec-ack0 = sVis {at = Fin 3 , c} {a = fzero} refl refl

-- BE′ (n = 1) receives an ack on c and holds it.
be′-recv : ∀ (t : Fin 3) → be′A ─[ ev (evl (evLabel (Fin 3) c t)) ]─► BE′lossy t
be′-recv t = sVis {at = Fin 3 , c} {a = t} refl refl

-- §B.3  Composite-state builders.  The whole system is
--   (Par⊤ adES snd (Par⊤ bcES (be ⦀ be′) rec)) ∖ intES  — abbreviated by its four
-- component states (snd , be , be′ , rec).
mkMID : SProc → SProc → SProc → SProc
mkMID be be′ rec = Par⊤ bcES (be ⦀ be′) rec

mkSys : SProc → SProc → SProc → SProc → SProc
mkSys snd be be′ rec = Par⊤ adES snd (mkMID be be′ rec)

mkH : SProc → SProc → SProc → SProc → SProc
mkH snd be be′ rec = (mkSys snd be be′ rec) ∖ intES

-- §B.4  The 11 composite steps.  Each wraps a component `sVis`/`sTau` in the
-- Par-*/Hide-* intro lemmas per the derivation table (V = visible/kept, H = hidden→τ).
-- The membership/non-offer witnesses: `tt` for a/b/c/d ∈ the sync/hide set; `λ z → z`
-- for the ⊥-membership of left/right (and of every event ∉ a channel's set); `refl`
-- for the idle operand's non-offer (`viewV (force _) _ ≡ nothing`, which computes).

-- 1. left true (V): SEND w0 0 → w1(0,t) solo (MID idle on left).
step1 : mkH sA beA be′A rA ─[ ev (evl (evLabel Bool left true)) ]─► mkH sB beA be′A rA
step1 = Hide-keep intES (mkSys sA beA be′A rA) (λ z → z)
          (Par-soloL adES (λ _ _ → tt) sA (mkMID beA be′A rA) (λ z → z) send-accept0 refl)

-- 2. a.(0,t) (H): SEND retransmits (0,t) ↔ BE1 receives it → BElossy(0,t).
step2 : mkH sB beA be′A rA ─[ τ ]─► mkH sB beB be′A rA
step2 = Hide-hidden intES (mkSys sB beA be′A rA) tt
          (Par-sync adES (λ _ _ → tt) sB (mkMID beA be′A rA) tt
             send-retx-w1
             (Par-soloL bcES (λ _ _ → tt) (beA ⦀ be′A) rA (λ z → z)
                (Par-soloL ∅ES (λ _ _ → tt) beA be′A (λ z → z) (be-recv fzero true) refl)
                refl))

-- 3. left false (V): SEND w1(0,t) → w2(0,t)(1,f) — PIPELINING: 2nd accept while unacked.
step3 : mkH sB beB be′A rA ─[ ev (evl (evLabel Bool left false)) ]─► mkH sC beB be′A rA
step3 = Hide-keep intES (mkSys sB beB be′A rA) (λ z → z)
          (Par-soloL adES (λ _ _ → tt) sB (mkMID beB be′A rA) (λ z → z) send-accept1 refl)

-- §B.5  reach2: the two-in-flight reach (steps 1–3), reused by Task 3.
S₂ : SProc
S₂ = (Par⊤ adES (SEND (w2 (fzero , true) (fsuc fzero , false)) (fsuc (fsuc fzero)))
        (Par⊤ bcES (BElossy (fzero , true) ⦀ BE′ (fsuc fzero)) (REC fzero))) ∖ intES

reach2 : SWPH ⟹⟨ evl (evLabel Bool left true) ∷ evl (evLabel Bool left false) ∷ [] ⟩ S₂
reach2 = ⟹-ev step1 (⟹-τ step2 (⟹-ev step3 ⟹-refl))

-- 4. τ (H): BElossy(0,t) forwards → BEout(0,t).
step4 : mkH sC beB be′A rA ─[ τ ]─► mkH sC beC be′A rA
step4 = Hide-τ intES (mkSys sC beB be′A rA)
          (Par-τ-R adES (λ _ _ → tt) sC (mkMID beB be′A rA)
             (Par-τ-L bcES (λ _ _ → tt) (beB ⦀ be′A) rA
                (Par-τ-L ∅ES (λ _ _ → tt) beB be′A (be-fwd (fzero , true)))))

-- 5. b.(0,t) (H): BEout(0,t) emits ↔ REC0 receives → RECdel t 0 1.
step5 : mkH sC beC be′A rA ─[ τ ]─► mkH sC beA be′A rB
step5 = Hide-hidden intES (mkSys sC beC be′A rA) tt
          (Par-soloR adES (λ _ _ → tt) sC (mkMID beC be′A rA) (λ z → z)
             (Par-sync bcES (λ _ _ → tt) (beC ⦀ be′A) rA tt
                (Par-soloL ∅ES (λ _ _ → tt) beC be′A (λ z → z) be-emit0 refl)
                rec-recv0)
             refl)

-- 6. right true (V): REC delivers the first payload.
step6 : mkH sC beA be′A rB ─[ ev (evl (evLabel Bool right true)) ]─► mkH sC beA be′A rC
step6 = Hide-keep intES (mkSys sC beA be′A rB) (λ z → z)
          (Par-soloR adES (λ _ _ → tt) sC (mkMID beA be′A rB) (λ z → z)
             (Par-soloR bcES (λ _ _ → tt) (beA ⦀ be′A) rB (λ z → z) rec-deliver0 refl)
             refl)

-- 7. c.0 (H): REC acks 0 ↔ BE′1 receives it → BE′lossy 0; REC advances to expect 1.
step7 : mkH sC beA be′A rC ─[ τ ]─► mkH sC beA be′B rD
step7 = Hide-hidden intES (mkSys sC beA be′A rC) tt
          (Par-soloR adES (λ _ _ → tt) sC (mkMID beA be′A rC) (λ z → z)
             (Par-sync bcES (λ _ _ → tt) (beA ⦀ be′A) rC tt
                (Par-soloR ∅ES (λ _ _ → tt) beA be′A (λ z → z) (be′-recv fzero) refl)
                rec-ack0)
             refl)

-- 8. a.(1,f) (H): SEND retransmits (1,f) ↔ BE1 receives it → BElossy(1,f).
step8 : mkH sC beA be′B rD ─[ τ ]─► mkH sC beD be′B rD
step8 = Hide-hidden intES (mkSys sC beA be′B rD) tt
          (Par-sync adES (λ _ _ → tt) sC (mkMID beA be′B rD) tt
             send-retx-w2
             (Par-soloL bcES (λ _ _ → tt) (beA ⦀ be′B) rD (λ z → z)
                (Par-soloL ∅ES (λ _ _ → tt) beA be′B (λ z → z) (be-recv (fsuc fzero) false) refl)
                refl))

-- 9. τ (H): BElossy(1,f) forwards → BEout(1,f).
step9 : mkH sC beD be′B rD ─[ τ ]─► mkH sC beE be′B rD
step9 = Hide-τ intES (mkSys sC beD be′B rD)
          (Par-τ-R adES (λ _ _ → tt) sC (mkMID beD be′B rD)
             (Par-τ-L bcES (λ _ _ → tt) (beD ⦀ be′B) rD
                (Par-τ-L ∅ES (λ _ _ → tt) beD be′B (be-fwd (fsuc fzero , false)))))

-- 10. b.(1,f) (H): BEout(1,f) emits ↔ REC1 receives → RECdel f 1 2.
step10 : mkH sC beE be′B rD ─[ τ ]─► mkH sC beA be′B rE
step10 = Hide-hidden intES (mkSys sC beE be′B rD) tt
          (Par-soloR adES (λ _ _ → tt) sC (mkMID beE be′B rD) (λ z → z)
             (Par-sync bcES (λ _ _ → tt) (beE ⦀ be′B) rD tt
                (Par-soloL ∅ES (λ _ _ → tt) beE be′B (λ z → z) be-emit1 refl)
                rec-recv1)
             refl)

-- 11. right false (V): REC delivers the second payload — in order.
step11 : mkH sC beA be′B rE ─[ ev (evl (evLabel Bool right false)) ]─► mkH sC beA be′B rF
step11 = Hide-keep intES (mkSys sC beA be′B rE) (λ z → z)
          (Par-soloR adES (λ _ _ → tt) sC (mkMID beA be′B rE) (λ z → z)
             (Par-soloR bcES (λ _ _ → tt) (beA ⦀ be′B) rE (λ z → z) rec-deliver1 refl)
             refl)

-- §B.6  The headline trace witness: SWPH delivers two messages in order,
-- accepting the second before the first is acknowledged (pipelining).
swp-delivers2 : traces SWPH
  ( evl (evLabel Bool left  true)  ∷ evl (evLabel Bool left  false)
  ∷ evl (evLabel Bool right true)  ∷ evl (evLabel Bool right false) ∷ [] )
swp-delivers2 = _ , (⟹-ev step1 (⟹-τ step2 (⟹-ev step3
                    (⟹-τ step4 (⟹-τ step5 (⟹-ev step6 (⟹-τ step7
                    (⟹-τ step8 (⟹-τ step9 (⟹-τ step10 (⟹-ev step11 ⟹-refl))))))))) ))

------------------------------------------------------------------------------------
-- §C. THE ONE-PLACE-BUFFER CONTRAST: `swp-beats-copy`.
--
-- COPY = left?x -> right!x -> COPY is a one-place buffer: it MUST deliver the first
-- message before accepting a second.  SWPH, with window W = 2, can accept a second
-- `left` while the first is still in flight (see reach2 / swp-delivers2).  Hence SWPH
-- has a trace (left true · left false) that COPY does NOT — so COPY does NOT refine
-- SWPH in the traces model.  This is the strict "SWP is more than a one-place buffer".
------------------------------------------------------------------------------------

-- COPY has no τ-step: `force COPY = react … ∅t`, so a τ can come neither from `sil`
-- (head is `react`, not `sil`) nor from the τ-branch (`∅t _ _ = nothing`, never `just`).
copy-noτ : ∀ {t : SProc} → COPY ─[ τ ]─► t → ⊥
copy-noτ (sSil ())
copy-noτ (sTau refl ())

-- Likewise COPYout has no τ-step.
copyout-noτ : ∀ {x : Bool} {t : SProc} → COPYout x ─[ τ ]─► t → ⊥
copyout-noτ (sSil ())
copyout-noτ (sTau refl ())

-- The contrast: COPY does NOT refine SWPH in the traces model.
--
-- Instantiate the hypothesis at s₀ = [left true, left false] and feed it SWPH's trace
-- (S₂ , reach2).  It must return a COPY-derivation of the same trace, which is absurd:
--   * the first move cannot be a τ (copy-noτ); it must offer `left true`, reaching
--     `COPYout true` (the only `left` continuation);
--   * from `COPYout true` the next move again cannot be a τ (copyout-noτ), and its
--     `left` offer is `nothing`, so any visible step on `left false` forces
--     `nothing ≡ just _` — impossible.
swp-beats-copy : ¬ (COPY ⊑T SWPH)
swp-beats-copy ref
  with ref (evl (evLabel Bool left true) ∷ evl (evLabel Bool left false) ∷ [])
           (S₂ , reach2)
... | _ , ⟹-τ st _                                       = copy-noτ st
... | _ , ⟹-ev (sVis refl refl) (⟹-τ st _)              = copyout-noτ st
... | _ , ⟹-ev (sVis refl refl) (⟹-ev (sVis refl ()) _)
