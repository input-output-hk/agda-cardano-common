module CSP.Examples.Cardano_network.NetModel where

open import Data.Nat using (ℕ; suc; _+_; _<_)
open import Data.Nat.Properties using (≤-reflexive)
open import Data.Nat.Solver using (module +-*-Solver)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

-- Per-leaf position enums --------------------------------------------------

data IP : Set where I0 I1 I2 Ig : IP        -- Inputs:      I0 await-input, I1 offer-sndmsg, I2 await-rcvack, Ig restart-guard
data TP : Set where T0 T1 Tg : TP           -- Transmitter: T0 await-sndmsg, T1 offer-tx, Tg guard
data RP : Set where R0 R1 Rg : RP           -- RcvAck:      R0 await-ack, R1 offer-rcvack, Rg guard
data OP : Set where O0 O1 O2 Og : OP        -- Outputs:     O0 await-rcvmsg, O1 offer-output, O2 offer-sndack, Og guard
data CP : Set where Rc0 Rc1 Rcg : CP        -- Receiver:    Rc0 await-tx, Rc1 offer-rcvmsg, Rcg guard
data SP : Set where Sa0 Sa1 Sag : SP        -- SndAck:      Sa0 await-sndack, Sa1 offer-ack, Sag guard

-- Global control state = product of the six leaves -------------------------

record CS : Set where
  constructor mkCS
  field
    inp : IP
    tr  : TP
    ra  : RP
    out : OP
    rc  : CP
    sa  : SP

open CS public

-- Initial state ------------------------------------------------------------

cs0 : CS
cs0 = mkCS I0 T0 R0 O0 Rc0 Sa0

-- Internal transition relation --------------------------------------------
--
-- Each constructor is GATED on the source state via implicit-field
-- constraints written through the record pattern in the source position,
-- and the target is the source with exactly the relevant fields changed.
-- The gate equalities are enforced by demanding the source state has the
-- required positions in those fields (the unconstrained fields are
-- universally quantified, so they must agree between source and target).

infix 4 _⇒ᵢ_

data _⇒ᵢ_ : CS → CS → Set where
  -- Syncs (decrease μ by 2): both endpoints must be at the right position.
  sndmsg : ∀ {r o c s}            → mkCS I1 T0 r o c s  ⇒ᵢ  mkCS I2 T1 r o c s
  tx     : ∀ {i r o s}            → mkCS i  T1 r o Rc0 s ⇒ᵢ  mkCS i  Tg r o Rc1 s
  rcvmsg : ∀ {i t r s}            → mkCS i  t  r O0 Rc1 s ⇒ᵢ  mkCS i  t  r O1 Rcg s
  sndack : ∀ {i t r c}            → mkCS i  t  r O2 c Sa0 ⇒ᵢ  mkCS i  t  r Og c Sa1
  ack    : ∀ {i t o c}            → mkCS i  t  R0 o c Sa1 ⇒ᵢ  mkCS i  t  R1 o c Sag
  rcvack : ∀ {t o c s}            → mkCS I2 t  R1 o c s   ⇒ᵢ  mkCS Ig t  Rg o c s
  -- Guards (decrease μ by 1): single leaf returns from its guard position.
  gI     : ∀ {t r o c s}          → mkCS Ig t  r  o  c  s  ⇒ᵢ  mkCS I0 t  r  o  c  s
  gT     : ∀ {i r o c s}          → mkCS i  Tg r  o  c  s  ⇒ᵢ  mkCS i  T0 r  o  c  s
  gR     : ∀ {i t o c s}          → mkCS i  t  Rg o  c  s  ⇒ᵢ  mkCS i  t  R0 o  c  s
  gO     : ∀ {i t r c s}          → mkCS i  t  r  Og c  s  ⇒ᵢ  mkCS i  t  r  O0 c  s
  gRc    : ∀ {i t r o s}          → mkCS i  t  r  o  Rcg s ⇒ᵢ  mkCS i  t  r  o  Rc0 s
  gSa    : ∀ {i t r o c}          → mkCS i  t  r  o  c  Sag ⇒ᵢ mkCS i  t  r  o  c  Sa0

-- Visible transition relation ---------------------------------------------

data Label : Set where input output : Label

infix 4 _⇒ᵥ_

data _⇒ᵥ_ : CS → CS → Set where
  input  : ∀ {t r o c s} → mkCS I0 t r o  c s ⇒ᵥ mkCS I1 t r o  c s
  output : ∀ {i t r c s} → mkCS i  t r O1 c s ⇒ᵥ mkCS i  t r O2 c s

-- Measure ------------------------------------------------------------------

-- DEVIATION FROM THE SPEC'S COST NUMBERS (deliberate; explained here).
--
-- The spec's literal table (await = 3 … guard = 1 for the non-input leaves) makes
-- `μ-dec` FALSE: every guard transition g* : guardPos → awaitPos would raise μ from
-- 1 back up to 3 (a +2 *increase*), because for those leaves the await is the costliest
-- position yet it is the *target* of the reset.  A single per-leaf-cost SUM that strictly
-- decreases on EVERY internal edge cannot assign a leaf both a "high await / low guard"
-- (so the productive await→offer→guard chain decreases) and have guard→await decrease —
-- that is a 3-cycle in the per-leaf cost, impossible for any ℕ ranking.
--
-- The spec's INPUT leaf already gets this right: await I0 = 0 (dormant, no pending work)
-- and the re-arming I0→I1 is a *visible* (`_⇒ᵥ_`) move, not internal — so the input leaf
-- has no internal cost-cycle.  We adopt exactly that, consistent, design for ALL leaves:
--   await  = 0   (dormant; only re-armed by an upstream sync or a visible event)
--   guard  = 1   (so the reset guard*  : guard → await  drops μ by exactly 1, as the spec
--                 intends "guards decrease by 1")
--   offer/intermediate positions take the (verified) values below so that every sync also
--   strictly decreases.  With this table EVERY internal edge drops μ by exactly 1.
-- All twelve deltas were checked to equal 1; `μ-dec` below proves it with no axioms.

costI : IP → ℕ
costI I0 = 0
costI I1 = 8
costI I2 = 3
costI Ig = 1

costT : TP → ℕ
costT T0 = 0
costT T1 = 4
costT Tg = 1

costR : RP → ℕ
costR R0 = 0
costR R1 = 0
costR Rg = 1

costO : OP → ℕ
costO O0 = 0
costO O1 = 0
costO O2 = 4
costO Og = 1

costC : CP → ℕ
costC Rc0 = 0
costC Rc1 = 2
costC Rcg = 1

costS : SP → ℕ
costS Sa0 = 0
costS Sa1 = 2
costS Sag = 1

μ : CS → ℕ
μ c = costI (inp c) + costT (tr c) + costR (ra c) + costO (out c) + costC (rc c) + costS (sa c)

-- THE KEY LEMMA -----------------------------------------------------------

open +-*-Solver

-- With the cost table above, EVERY internal edge drops μ by exactly 1, i.e.
--   μ c ≡ suc (μ c′).
-- For each constructor the four/five unchanged leaves appear identically on both
-- sides (as the opaque cost terms a,b,c,d,e), and the two/one changed leaves are
-- concrete, so the identity is a linear ℕ polynomial equality discharged by the
-- commutative-semiring `solve`r.  `μ-dec` then follows by reflexivity of ≤.

μ-step : ∀ {c c′} → c ⇒ᵢ c′ → μ c ≡ suc (μ c′)
-- sndmsg : I1(8)+T0(0)  →  I2(3)+T1(4)   [a=R b=O c=C d=S]
μ-step (sndmsg {r} {o} {c} {s}) =
  solve 4 (λ a b c d → con 8 :+ con 0 :+ a :+ b :+ c :+ d
                     := con 1 :+ (con 3 :+ con 4 :+ a :+ b :+ c :+ d)) refl
    (costR r) (costO o) (costC c) (costS s)
-- tx : T1(4)+Rc0(0)  →  Tg(1)+Rc1(2)   [a=I b=R c=O d=S]
μ-step (tx {i} {r} {o} {s}) =
  solve 4 (λ a b c d → a :+ con 4 :+ b :+ c :+ con 0 :+ d
                     := con 1 :+ (a :+ con 1 :+ b :+ c :+ con 2 :+ d)) refl
    (costI i) (costR r) (costO o) (costS s)
-- rcvmsg : O0(0)+Rc1(2)  →  O1(0)+Rcg(1)   [a=I b=T c=R d=S]
μ-step (rcvmsg {i} {t} {r} {s}) =
  solve 4 (λ a b c d → a :+ b :+ c :+ con 0 :+ con 2 :+ d
                     := con 1 :+ (a :+ b :+ c :+ con 0 :+ con 1 :+ d)) refl
    (costI i) (costT t) (costR r) (costS s)
-- sndack : O2(4)+Sa0(0)  →  Og(1)+Sa1(2)   [a=I b=T c=R d=C]
μ-step (sndack {i} {t} {r} {c}) =
  solve 4 (λ a b c d → a :+ b :+ c :+ con 4 :+ d :+ con 0
                     := con 1 :+ (a :+ b :+ c :+ con 1 :+ d :+ con 2)) refl
    (costI i) (costT t) (costR r) (costC c)
-- ack : R0(0)+Sa1(2)  →  R1(0)+Sag(1)   [a=I b=T c=O d=C]
μ-step (ack {i} {t} {o} {c}) =
  solve 4 (λ a b c d → a :+ b :+ con 0 :+ c :+ d :+ con 2
                     := con 1 :+ (a :+ b :+ con 0 :+ c :+ d :+ con 1)) refl
    (costI i) (costT t) (costO o) (costC c)
-- rcvack : I2(3)+R1(0)  →  Ig(1)+Rg(1)   [a=T b=O c=C d=S]
μ-step (rcvack {t} {o} {c} {s}) =
  solve 4 (λ a b c d → con 3 :+ a :+ con 0 :+ b :+ c :+ d
                     := con 1 :+ (con 1 :+ a :+ con 1 :+ b :+ c :+ d)) refl
    (costT t) (costO o) (costC c) (costS s)
-- gI : Ig(1) → I0(0)   [a=T b=R c=O d=C e=S]
μ-step (gI {t} {r} {o} {c} {s}) =
  solve 5 (λ a b c d e → con 1 :+ a :+ b :+ c :+ d :+ e
                       := con 1 :+ (con 0 :+ a :+ b :+ c :+ d :+ e)) refl
    (costT t) (costR r) (costO o) (costC c) (costS s)
-- gT : Tg(1) → T0(0)   [a=I b=R c=O d=C e=S]
μ-step (gT {i} {r} {o} {c} {s}) =
  solve 5 (λ a b c d e → a :+ con 1 :+ b :+ c :+ d :+ e
                       := con 1 :+ (a :+ con 0 :+ b :+ c :+ d :+ e)) refl
    (costI i) (costR r) (costO o) (costC c) (costS s)
-- gR : Rg(1) → R0(0)   [a=I b=T c=O d=C e=S]
μ-step (gR {i} {t} {o} {c} {s}) =
  solve 5 (λ a b c d e → a :+ b :+ con 1 :+ c :+ d :+ e
                       := con 1 :+ (a :+ b :+ con 0 :+ c :+ d :+ e)) refl
    (costI i) (costT t) (costO o) (costC c) (costS s)
-- gO : Og(1) → O0(0)   [a=I b=T c=R d=C e=S]
μ-step (gO {i} {t} {r} {c} {s}) =
  solve 5 (λ a b c d e → a :+ b :+ c :+ con 1 :+ d :+ e
                       := con 1 :+ (a :+ b :+ c :+ con 0 :+ d :+ e)) refl
    (costI i) (costT t) (costR r) (costC c) (costS s)
-- gRc : Rcg(1) → Rc0(0)   [a=I b=T c=R d=O e=S]
μ-step (gRc {i} {t} {r} {o} {s}) =
  solve 5 (λ a b c d e → a :+ b :+ c :+ d :+ con 1 :+ e
                       := con 1 :+ (a :+ b :+ c :+ d :+ con 0 :+ e)) refl
    (costI i) (costT t) (costR r) (costO o) (costS s)
-- gSa : Sag(1) → Sa0(0)   [a=I b=T c=R d=O e=C]
μ-step (gSa {i} {t} {r} {o} {c}) =
  solve 5 (λ a b c d e → a :+ b :+ c :+ d :+ e :+ con 1
                       := con 1 :+ (a :+ b :+ c :+ d :+ e :+ con 0)) refl
    (costI i) (costT t) (costR r) (costO o) (costC c)

μ-dec : ∀ {c c′} → c ⇒ᵢ c′ → μ c′ < μ c
μ-dec t = ≤-reflexive (sym (μ-step t))
