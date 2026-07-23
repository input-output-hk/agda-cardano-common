{-# OPTIONS --guardedness #-}

-- UCS chapter 4: the ALTERNATING BIT PROTOCOL (ABP) as a one-place buffer.
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/abp.csp   (UCS ch. 4, "abp.csp", Bill Roscoe)
--
-- The headline FDR assert this module's model is built to support (Task 2) is
--
--   assert COPY [FD= SystemBE2 \ {|a,b,c,d|}
--
-- i.e. the ABP with its internal channels hidden refines the one-place buffer
-- COPY in the failures-divergences model.  SystemBE2 uses the bounded-loss
-- channels BE/BE' and the DIVERGENCE-FREE receiver REC2 (the receiver that
-- avoids infinite internal traces).  The refinement task (Task 2) inherits the
-- certified `¬-divergent→normal` bridge; this module is the reachable-config
-- CHECKPOINT that makes that task tractable.
--
-- ────────────────────────────────────────────────────────────────────────────
-- MODEL REDUCTIONS (documented per the task spec).  Faithful to abp.csp except:
--   * DATA = TAG = Bool          (the .csp uses {0,1} for both; Bool here).
--   * L = 2                      (the .csp uses L = 3 bounded-loss channels; the
--                                 property holds for any L ≥ 1, so the smallest
--                                 interesting bound L = 2 is used — deliver, or
--                                 lose once then must deliver).
--   * Receiver = REC2            (the divergence-free receiver, per SystemBE2).
--   * Null = `nothing`           (the sender's "no pending value" state).
--
-- FAITHFULNESS: the sender's data output `a!bit!v`, the channels' forwards
-- `b!(t,x)` / `d!t`, and the receiver's acks/deliveries `right!data` / `c!(1-bit)`
-- are all PINNED (the offer fires only at the SPECIFIC held value), exactly as in
-- abp.csp.  An over-approximated (payload-discarded) model would be UNSOUND.
--
-- The recursive processes are written as inlined `react` copatterns (corecursive
-- calls sit DIRECTLY under `just`, guarded by the enclosing `react`), following the
-- routing examples in this directory.  Every intermediate output / internal-choice
-- state is therefore its OWN copattern node (`BEout`/`BElossy`/`RECack`/… ): the
-- `_!_⟶_` / `_⊓_` operators cannot be used inside `just` because they wrap the
-- corecursive call in a function application, which the guardedness checker rejects.

module CSP.Examples.UCS.Ch4.ABP where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Product.Properties using () renaming (≡-dec to ×-≡-dec)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; _≟_)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. The event type and its decidable equality.
--   left, right : external interface, carry a DATA value (Bool).
--   a, b        : data channel (a into the channel, b out), carry (TAG , DATA).
--   c, d        : ack  channel (c into the channel, d out), carry a TAG.
data ABPEv : Set → Set where
  left  : ABPEv Bool            -- external input
  right : ABPEv Bool            -- external output
  a     : ABPEv (Bool × Bool)   -- data channel in : (tag , data)
  b     : ABPEv (Bool × Bool)   -- data channel out: (tag , data)
  c     : ABPEv Bool            -- ack  channel in : tag
  d     : ABPEv Bool            -- ack  channel out: tag

ABPEv-≟ : (x y : AnyTypes ABPEv) → Dec (x ≡ y)
ABPEv-≟ (_ , left)  (_ , left)  = yes refl
ABPEv-≟ (_ , right) (_ , right) = yes refl
ABPEv-≟ (_ , a)     (_ , a)     = yes refl
ABPEv-≟ (_ , b)     (_ , b)     = yes refl
ABPEv-≟ (_ , c)     (_ , c)     = yes refl
ABPEv-≟ (_ , d)     (_ , d)     = yes refl
ABPEv-≟ (_ , left)  (_ , right) = no (λ ())
ABPEv-≟ (_ , left)  (_ , a)     = no (λ ())
ABPEv-≟ (_ , left)  (_ , b)     = no (λ ())
ABPEv-≟ (_ , left)  (_ , c)     = no (λ ())
ABPEv-≟ (_ , left)  (_ , d)     = no (λ ())
ABPEv-≟ (_ , right) (_ , left)  = no (λ ())
ABPEv-≟ (_ , right) (_ , a)     = no (λ ())
ABPEv-≟ (_ , right) (_ , b)     = no (λ ())
ABPEv-≟ (_ , right) (_ , c)     = no (λ ())
ABPEv-≟ (_ , right) (_ , d)     = no (λ ())
ABPEv-≟ (_ , a)     (_ , left)  = no (λ ())
ABPEv-≟ (_ , a)     (_ , right) = no (λ ())
ABPEv-≟ (_ , a)     (_ , b)     = no (λ ())
ABPEv-≟ (_ , a)     (_ , c)     = no (λ ())
ABPEv-≟ (_ , a)     (_ , d)     = no (λ ())
ABPEv-≟ (_ , b)     (_ , left)  = no (λ ())
ABPEv-≟ (_ , b)     (_ , right) = no (λ ())
ABPEv-≟ (_ , b)     (_ , a)     = no (λ ())
ABPEv-≟ (_ , b)     (_ , c)     = no (λ ())
ABPEv-≟ (_ , b)     (_ , d)     = no (λ ())
ABPEv-≟ (_ , c)     (_ , left)  = no (λ ())
ABPEv-≟ (_ , c)     (_ , right) = no (λ ())
ABPEv-≟ (_ , c)     (_ , a)     = no (λ ())
ABPEv-≟ (_ , c)     (_ , b)     = no (λ ())
ABPEv-≟ (_ , c)     (_ , d)     = no (λ ())
ABPEv-≟ (_ , d)     (_ , left)  = no (λ ())
ABPEv-≟ (_ , d)     (_ , right) = no (λ ())
ABPEv-≟ (_ , d)     (_ , a)     = no (λ ())
ABPEv-≟ (_ , d)     (_ , b)     = no (λ ())
ABPEv-≟ (_ , d)     (_ , c)     = no (λ ())

open import CSP.Operators ABPEv-≟
open EventSet

-- DecEq (Bool × Bool) for pinning the `a`/`b` channel outputs.
instance
  DecEq-B×B : DecEq (Bool × Bool)
  DecEq-B×B ._≟_ = ×-≡-dec _B≟_ _B≟_

AProc : Set₁
AProc = PTree ABPEv (ExtI ABPEv) (⊤poly {lzero})

L : ℕ
L = 2

------------------------------------------------------------------------------------
-- §2. Forward declarations of every corecursive node.
SEND       : Maybe Bool → Bool → AProc
REC2       : Bool → AProc
RECdeliver : Bool → Bool → Bool → AProc   -- pending right!dat, then ack, then next bit
RECack     : Bool → Bool → AProc          -- pending c!ackTag, then next bit
BE         : Fin L → AProc                -- data channel a → b
BEout      : (Bool × Bool) → AProc        -- pending b!(t,x), then BE (L-1)
BElossy    : (Bool × Bool) → AProc        -- (b!(t,x) → BE (L-1)) ⊓ BE 0  (inlined ⊓)
BE′        : Fin L → AProc                -- ack  channel c → d
BE′out     : Bool → AProc                 -- pending d!t, then BE' (L-1)
BE′lossy   : Bool → AProc                 -- (d!t → BE' (L-1)) ⊓ BE' 0    (inlined ⊓)
COPY       : AProc
COPYout    : Bool → AProc                 -- pending right!x, then COPY

------------------------------------------------------------------------------------
-- §3. The sender.
-- abp.csp:
--   SEND(v,bit) = (if v==Null then left?x -> SEND(x,1-bit) else a!bit!v -> SEND(v,bit))
--                 [] d?ack -> (if ack==bit then SEND(Null,bit) else SEND(v,bit))
--   SND = SEND(Null,1)      (Null = nothing, 1 = true; first input then gets bit = false)

-- SEND Null bit: offer `left?x` (seed a value, flip the bit) and `d?ack` (drain an
-- acknowledgement — with no pending value both ack cases return to SEND Null bit).
force (SEND nothing bit) = react
  (λ where
     (_ , left)  x → just (SEND (just x) (not bit))
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → just (SEND nothing bit))
  ∅t

-- SEND (just v) bit: offer the PINNED output `a!bit!v` (fires only at (bit,v)) and
-- `d?ack` (ack==bit ⇒ clear to Null; else keep the value).
force (SEND (just v) bit) = react
  (λ where
     (_ , left)  _       → nothing
     (_ , right) _       → nothing
     (_ , a)     (t , x) → case t B≟ bit of λ where
         (yes _) → case x B≟ v of λ where
             (yes _) → just (SEND (just v) bit)
             (no  _) → nothing
         (no  _) → nothing
     (_ , b)     _       → nothing
     (_ , c)     _       → nothing
     (_ , d)     ack     → case ack B≟ bit of λ where
         (yes _) → just (SEND nothing bit)
         (no  _) → just (SEND (just v) bit))
  ∅t

SND : AProc
SND = SEND nothing true

------------------------------------------------------------------------------------
-- §4. The divergence-free receiver.
-- abp.csp:
--   REC2(bit) = b?tag?data ->
--     (if tag==bit then right!data -> c!(1-bit) -> REC2(1-bit)
--                  else            c!(1-bit) -> REC2(bit))
--   RCV2 = REC2(0)
force (REC2 bit) = react
  (λ where
     (_ , left)  _         → nothing
     (_ , right) _         → nothing
     (_ , a)     _         → nothing
     (_ , b)     (t , dat) → case t B≟ bit of λ where
         (yes _) → just (RECdeliver dat (not bit) (not bit))   -- deliver, ack, flip
         (no  _) → just (RECack (not bit) bit)                 -- re-ack, keep bit
     (_ , c)     _         → nothing
     (_ , d)     _         → nothing)
  ∅t

-- pending `right!dat`, then the acknowledgement `c!ackTag`, then REC2 nextBit.
force (RECdeliver dat ackTag nextBit) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) y → case y B≟ dat of λ where
         (yes _) → just (RECack ackTag nextBit)
         (no  _) → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     _ → nothing
     (_ , d)     _ → nothing)
  ∅t

-- pending `c!ackTag`, then REC2 nextBit.
force (RECack ackTag nextBit) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) _ → nothing
     (_ , a)     _ → nothing
     (_ , b)     _ → nothing
     (_ , c)     t → case t B≟ ackTag of λ where
         (yes _) → just (REC2 nextBit)
         (no  _) → nothing
     (_ , d)     _ → nothing)
  ∅t

RCV2 : AProc
RCV2 = REC2 false

------------------------------------------------------------------------------------
-- §5. The bounded-loss channels (L = 2).
-- abp.csp:
--   BE(ic,oc,n)  = ic?tag?data -> (if n==0 then oc!tag!data -> BE(ic,oc,L-1)
--                                  else (oc!tag!data -> BE(ic,oc,L-1)) |~| BE(ic,oc,n-1))
--   BE'(ic,oc,n) = ic?tag     -> (if n==0 then oc!tag     -> BE'(ic,oc,L-1)
--                                  else (oc!tag     -> BE'(ic,oc,L-1)) |~| BE'(ic,oc,n-1))
-- Here BE is the data channel a → b, BE' the ack channel c → d.  n : Fin 2;
-- n = 0 must forward, n = 1 may forward OR lose (drop the value, drop to n = 0).

-- n = 0: no loss branch — must forward the held (t,x) on b.
force (BE fzero) = react
  (λ where
     (_ , left)  _       → nothing
     (_ , right) _       → nothing
     (_ , a)     (t , x) → just (BEout (t , x))
     (_ , b)     _       → nothing
     (_ , c)     _       → nothing
     (_ , d)     _       → nothing)
  ∅t

-- n = 1: forward on b, OR lose and drop to n = 0.
force (BE (fsuc fzero)) = react
  (λ where
     (_ , left)  _       → nothing
     (_ , right) _       → nothing
     (_ , a)     (t , x) → just (BElossy (t , x))
     (_ , b)     _       → nothing
     (_ , c)     _       → nothing
     (_ , d)     _       → nothing)
  ∅t

-- pending PINNED output `b!(t,x)`, then reset to BE (L-1).
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
     (_ , base _)             _                    → nothing
     (_ , pair _ _)           _                    → nothing
     (_ , fin)                (lift fzero)         → just (BEout p)
     (_ , fin)                (lift (fsuc fzero))  → just (BE fzero)
     (_ , fin)                (lift (fsuc (fsuc _))) → nothing)

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
     (_ , d)     u → case u B≟ t of λ where
         (yes _) → just (BE′ (fsuc fzero))
         (no  _) → nothing)
  ∅t

force (BE′lossy t) = react ∅v
  (λ where
     (_ , base _)             _                    → nothing
     (_ , pair _ _)           _                    → nothing
     (_ , fin)                (lift fzero)         → just (BE′out t)
     (_ , fin)                (lift (fsuc fzero))  → just (BE′ fzero)
     (_ , fin)                (lift (fsuc (fsuc _))) → nothing)

------------------------------------------------------------------------------------
-- §6. Sync sets, the system, hiding, and COPY.
--   {|a,d|} between SND and the channel/receiver block; {|b,c|} between the two
--   channels and the receiver; {|a,b,c,d|} hidden in SysH.
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

-- abp.csp:
--   SystemBE2 = SND [|{|a,d|}|] ((BE(a,b,L-1) ||| BE'(c,d,L-1)) [|{|b,c|}|] RCV2)
SystemBE2 : AProc
SystemBE2 = Par⊤ adES SND (Par⊤ bcES (BE (fsuc fzero) ⦀ BE′ (fsuc fzero)) RCV2)

-- The hidden system:  SystemBE2 \ {|a,b,c,d|}
SysH : AProc
SysH = SystemBE2 ∖ intES

-- abp.csp:  COPY = left?x -> right!x -> COPY   (the one-place buffer spec).
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
-- §7. Reachable-config characterisation (data-tag technique).
--
-- Each of the four components is tracked by a DATA tag decoded to its process state
-- by `⟦_⟧·`.  Indexing configurations by these tags (rather than by the raw process
-- terms) is what lets a closure proof case-split node states: `BE (fsuc fzero)` and
-- `BEout p` are distinct DEFINED terms Agda's unifier cannot tell apart, whereas the
-- tag constructors `bIdle …`/`bOut …` ARE disjoint (cf. RoutingTreeSwap `S0`/`S1`).
--
-- The composite decode `⟦_⟧` rebuilds the SystemBE2 shape, `refl`-bridged to
-- SystemBE2 at the initial config (`system≡`).  The reachability CLOSURE lemma
-- (`SysH ⟹∖√⟨ s ⟩ t′ → Σ[ cfg ] t′ ≡ ⟦ cfg ⟧ ∖ intES`) would be the load-bearing
-- step for the refinement — it is NOT proved here (DEFERRED: the closure spans 594
-- reachable configs; see ABPRefinement and Laws_status).  This scaffold is the
-- foundation a future attempt would build it on.

-- Sender phase × bit (+ held value when non-Null).
data SendS : Set where
  sNull : Bool → SendS           -- SEND nothing bit
  sVal  : Bool → Bool → SendS    -- SEND (just v) bit   (fields: v , bit)

-- Data channel a→b: idle at counter n, or pending output / lossy choice of packet p.
data DataS : Set where
  bIdle : Fin L → DataS
  bOut  : (Bool × Bool) → DataS
  bLoss : (Bool × Bool) → DataS

-- Ack channel c→d: idle at counter n, or pending output / lossy choice of tag t.
data AckS : Set where
  aIdle : Fin L → AckS
  aOut  : Bool → AckS
  aLoss : Bool → AckS

-- Receiver phase.
data RecS : Set where
  rIdle : Bool → RecS                 -- REC2 bit
  rDel  : Bool → Bool → Bool → RecS   -- RECdeliver dat ackTag nextBit
  rAck  : Bool → Bool → RecS          -- RECack ackTag nextBit

record Cfg : Set where
  constructor cfg
  field
    sndS : SendS      -- sender
    datS : DataS      -- data channel (BE, a→b)
    ackS : AckS       -- ack  channel (BE', c→d)
    recS : RecS       -- receiver
open Cfg

⟦_⟧snd : SendS → AProc
⟦ sNull bit ⟧snd = SEND nothing bit
⟦ sVal v bit ⟧snd = SEND (just v) bit

⟦_⟧dat : DataS → AProc
⟦ bIdle n ⟧dat = BE n
⟦ bOut p ⟧dat  = BEout p
⟦ bLoss p ⟧dat = BElossy p

⟦_⟧ack : AckS → AProc
⟦ aIdle n ⟧ack = BE′ n
⟦ aOut t ⟧ack  = BE′out t
⟦ aLoss t ⟧ack = BE′lossy t

⟦_⟧rec : RecS → AProc
⟦ rIdle bit ⟧rec       = REC2 bit
⟦ rDel dat ack nx ⟧rec = RECdeliver dat ack nx
⟦ rAck ack nx ⟧rec     = RECack ack nx

-- The composite decode: the SystemBE2 shape, per-component states plugged in.
⟦_⟧ : Cfg → AProc
⟦ cfg s dc ac rc ⟧ =
  Par⊤ adES ⟦ s ⟧snd (Par⊤ bcES (⟦ dc ⟧dat ⦀ ⟦ ac ⟧ack) ⟦ rc ⟧rec)

-- Initial configuration: SND = SEND nothing true; channels at L-1 = fsuc fzero;
-- RCV2 = REC2 false.
cfg₀ : Cfg
cfg₀ = cfg (sNull true) (bIdle (fsuc fzero)) (aIdle (fsuc fzero)) (rIdle false)

-- The refl bridge: SystemBE2 is exactly the decode of the initial config.
system≡ : SystemBE2 ≡ ⟦ cfg₀ ⟧
system≡ = refl
