{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — per-link mux ABSTRACT STATE (`PerLink.State`).
--
-- The foundation layer of the `perLink-single` campaign: a multi-instance
-- generalisation of `NetModel`'s single-instance p1 automaton.  Where
-- `NetModel` tracks six per-leaf position enums for ONE mini-protocol
-- instance, this module tracks, for a whole TCP link `l`:
--
--   · a per-instance INPUT phase vector   `iph : PhV IPh (linkConfig l)`
--   · a per-instance OUTPUT phase vector  `oph : PhV OPh (linkConfig l)`
--   · the four SHARED one-place buffers as registers
--        `tb rb : MBuf`  (Transmitter / Receiver — carry a `Data` payload)
--        `sb ab : ABuf`  (SndAck / RcvAck  — carry only `Dir × IDs`).
--
-- Payload lives IN the phase constructors (`i1 : Data → IPh`, …): with a
-- per-instance vector several cells may hold DIFFERENT in-flight payloads
-- at once, so a single global `d` index (as in p1) will not do — this is
-- the binding design decision inherited from the perLink Phase-2 spike.
--
-- The internal `_⇒ᵢ_` and visible `_⇒ᵥ⟨_⟩_` transition relations are the
-- membership-indexed multi-instance generalisation of `NetModel`'s
-- `_⇒ᵢ_`/`_⇒ᵥ_`: each mux move is one constructor and, for a singleton
-- config `linkConfig l = c ∷ []`, they project constructor-for-constructor
-- onto `NetModel`'s (see the inline cross-reference on each constructor).
--
-- The measure `μ` sums per-cell costs over the two vectors plus the four
-- register costs; `μ-dec` proves EVERY internal edge drops `μ` by exactly
-- one, reusing `NetModel`'s verified cost table split per cell/register.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.Nat.Properties using (≤-reflexive; +-assoc; +-cancelʳ-≡)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (DecEq)

open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (Dir; IDs)

module CSP.Examples.Cardano_network.NetworkVerification.PerLink.State
  (p : Params) (Data : Set) ⦃ _ : DecEq Data ⦄ where

open import CSP.Examples.Cardano_network.Net p using (Link)
open Params p using (numLinks; linkConfig)

------------------------------------------------------------------------
-- Phase types (payload-carrying constructors — spike Q1 deviation).
------------------------------------------------------------------------

-- Input-cell phase: home / holding x pre-sndmsg / sent, awaiting rcvack / guard.
-- Mirrors `NetModel.IP` (I0 I1 I2 Ig), payload attached to i1/i2/ig.
data IPh : Set where
  i0 : IPh
  i1 : Data → IPh
  i2 : Data → IPh
  ig : Data → IPh

-- Output-cell phase: home / holding x pre-output / output done, pre-sndack / guard.
-- Mirrors `NetModel.OP` (O0 O1 O2 Og), payload attached to o1/o2/og.
data OPh : Set where
  o0 : OPh
  o1 : Data → OPh
  o2 : Data → OPh
  og : Data → OPh

-- Message buffer register (Transmitter `tb` and Receiver `rb`): free / holding
-- instance (d,id)'s payload x / guard.  Mirrors `NetModel.TP`/`CP`.  The `grd`
-- constructor keeps (d,id,x) so a decoder can name the post-emit derivative and
-- the loop-restart τ.
data MBuf : Set where
  free : MBuf
  hold : Dir → IDs → Data → MBuf
  grd  : Dir → IDs → Data → MBuf

-- Ack buffer register (SndAck `sb` and RcvAck `ab`): free / holding instance
-- (d,id) / guard.  Mirrors `NetModel.SP`/`RP`.  Ack channels are ⊤-carried, so
-- no `Data` payload; `grd` keeps (d,id) for the same reason as `MBuf.grd`.
data ABuf : Set where
  free : ABuf
  hold : Dir → IDs → ABuf
  grd  : Dir → IDs → ABuf

------------------------------------------------------------------------
-- Phase vectors aligned to a config list (our own `All`, to sidestep the
-- stdlib `All` []/∷ name-clash; overloaded ctors resolve by type).
------------------------------------------------------------------------

-- A phase vector: one `P` per entry of the index list `xs`.
data PhV (P : Set) : List (Dir × IDs) → Set where
  []  : PhV P []
  _∷_ : ∀ {x xs} → P → PhV P xs → PhV P (x ∷ xs)

-- read the phase at a membership position
getPh : ∀ {P xs} → PhV P xs → ∀ {x} → x ∈ xs → P
getPh (ph ∷ _)  (here _)  = ph
getPh (_  ∷ ps) (there m) = getPh ps m

-- overwrite the phase at a membership position
setPh : ∀ {P xs} → PhV P xs → ∀ {x} → x ∈ xs → P → PhV P xs
setPh (_  ∷ ps) (here _)  v = v ∷ ps
setPh (ph ∷ ps) (there m) v = ph ∷ setPh ps m v

------------------------------------------------------------------------
-- Mux state and its initial (all-home / all-free) configuration.
------------------------------------------------------------------------

-- The abstract mux state for link `l`: the two per-instance phase vectors
-- plus the four shared one-place buffers as registers.
record MuxState (l : Link) : Set where
  constructor mkMux
  field
    iph : PhV IPh (linkConfig l)   -- input cells
    oph : PhV OPh (linkConfig l)   -- output cells
    tb  : MBuf                     -- Transmitter register
    rb  : MBuf                     -- Receiver register
    sb  : ABuf                     -- SndAck register
    ab  : ABuf                     -- RcvAck register
open MuxState public

-- all-home Input vector, built by recursion so it reduces with the decoder
homeI : (xs : List (Dir × IDs)) → PhV IPh xs
homeI []       = []
homeI (_ ∷ xs) = i0 ∷ homeI xs

-- all-home Output vector
homeO : (xs : List (Dir × IDs)) → PhV OPh xs
homeO []       = []
homeO (_ ∷ xs) = o0 ∷ homeO xs

-- the initial mux state: every cell home, every buffer free
initial : (l : Link) → MuxState l
initial l = mkMux (homeI (linkConfig l)) (homeO (linkConfig l)) free free free free

------------------------------------------------------------------------
-- Internal transition relation `_⇒ᵢ_`.
--
-- Multi-instance generalisation of `NetModel._⇒ᵢ_`.  Cell moves are gated
-- by a membership position `mem` plus an equality on `getPh`; register
-- moves pattern-match the register constructor directly.  For a singleton
-- config each constructor projects onto the `NetModel` one named beside it.
------------------------------------------------------------------------

infix 4 _⇒ᵢ_

data _⇒ᵢ_ {l : Link} : MuxState l → MuxState l → Set where
  -- sndmsg handoff Input→Transmitter  (NetModel.sndmsg : I1 T0 → I2 T1)
  sndmsg : ∀ {is os rb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh is mem ≡ i1 x
         → mkMux is os free rb sb ab
             ⇒ᵢ mkMux (setPh is mem (i2 x)) os (hold d id x) rb sb ab
  -- tx handoff Transmitter→Receiver   (NetModel.tx : T1 Rc0 → Tg Rc1)
  tx     : ∀ {is os sb ab d id x}
         → mkMux is os (hold d id x) free sb ab
             ⇒ᵢ mkMux is os (grd d id x) (hold d id x) sb ab
  -- rcvmsg handoff Receiver→Output    (NetModel.rcvmsg : O0 Rc1 → O1 Rcg)
  rcvmsg : ∀ {is os tb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh os mem ≡ o0
         → mkMux is os tb (hold d id x) sb ab
             ⇒ᵢ mkMux is (setPh os mem (o1 x)) tb (grd d id x) sb ab
  -- sndack handoff Output→SndAck      (NetModel.sndack : O2 Sa0 → Og Sa1)
  sndack : ∀ {is os tb rb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh os mem ≡ o2 x
         → mkMux is os tb rb free ab
             ⇒ᵢ mkMux is (setPh os mem (og x)) tb rb (hold d id) ab
  -- ack handoff SndAck→RcvAck         (NetModel.ack : R0 Sa1 → R1 Sag)
  ack    : ∀ {is os tb rb d id}
         → mkMux is os tb rb (hold d id) free
             ⇒ᵢ mkMux is os tb rb (grd d id) (hold d id)
  -- rcvack handoff RcvAck→Input       (NetModel.rcvack : I2 R1 → Ig Rg)
  rcvack : ∀ {is os tb rb sb d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh is mem ≡ i2 x
         → mkMux is os tb rb sb (hold d id)
             ⇒ᵢ mkMux (setPh is mem (ig x)) os tb rb sb (grd d id)
  -- Input-cell loop-restart guard τ   (NetModel.gI : Ig → I0)
  gI     : ∀ {is os tb rb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh is mem ≡ ig x
         → mkMux is os tb rb sb ab
             ⇒ᵢ mkMux (setPh is mem i0) os tb rb sb ab
  -- Output-cell loop-restart guard τ  (NetModel.gO : Og → O0)
  gO     : ∀ {is os tb rb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh os mem ≡ og x
         → mkMux is os tb rb sb ab
             ⇒ᵢ mkMux is (setPh os mem o0) tb rb sb ab
  -- Transmitter loop-restart guard τ  (NetModel.gT : Tg → T0)
  gT     : ∀ {is os rb sb ab d id x}
         → mkMux is os (grd d id x) rb sb ab ⇒ᵢ mkMux is os free rb sb ab
  -- Receiver loop-restart guard τ     (NetModel.gRc : Rcg → Rc0)
  gRc    : ∀ {is os tb sb ab d id x}
         → mkMux is os tb (grd d id x) sb ab ⇒ᵢ mkMux is os tb free sb ab
  -- SndAck loop-restart guard τ       (NetModel.gSa : Sag → Sa0)
  gSa    : ∀ {is os tb rb ab d id}
         → mkMux is os tb rb (grd d id) ab ⇒ᵢ mkMux is os tb rb free ab
  -- RcvAck loop-restart guard τ       (NetModel.gR : Rg → R0)
  gR     : ∀ {is os tb rb sb d id}
         → mkMux is os tb rb sb (grd d id) ⇒ᵢ mkMux is os tb rb sb free

------------------------------------------------------------------------
-- Visible transition relation `_⇒ᵥ⟨_⟩_`, labelled by the fired event.
--
-- `NetModel._⇒ᵥ_` carries only a nullary `Label`; here the label must
-- name the instance and payload of the fired input/output so downstream
-- tasks can connect it to the concrete `Net` LTS event.
------------------------------------------------------------------------

-- Visible-event label: an input or output of instance (d,id) carrying x.
data VLabel : Set where
  inp : Dir → IDs → Data → VLabel
  out : Dir → IDs → Data → VLabel

infix 4 _⇒ᵥ⟨_⟩_

data _⇒ᵥ⟨_⟩_ {l : Link} : MuxState l → VLabel → MuxState l → Set where
  -- environment fires input at a home cell   (NetModel.input : I0 → I1)
  input  : ∀ {is os tb rb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh is mem ≡ i0
         → mkMux is os tb rb sb ab
             ⇒ᵥ⟨ inp d id x ⟩ mkMux (setPh is mem (i1 x)) os tb rb sb ab
  -- environment observes output of a ready cell (NetModel.output : O1 → O2)
  output : ∀ {is os tb rb sb ab d id x} (mem : (d , id) ∈ linkConfig l)
         → getPh os mem ≡ o1 x
         → mkMux is os tb rb sb ab
             ⇒ᵥ⟨ out d id x ⟩ mkMux is (setPh os mem (o2 x)) tb rb sb ab

------------------------------------------------------------------------
-- Measure `μ` and the strict-decrease lemma `μ-dec`.
--
-- Cost table = `NetModel`'s verified one, split per cell / register:
--   IPh   i0 0 · i1 8 · i2 3 · ig 1        (costI)
--   OPh   o0 0 · o1 0 · o2 4 · og 1        (costO)
--   MBuf  Transmitter tb : free 0 · hold 4 · grd 1   (costTb)
--         Receiver    rb : free 0 · hold 2 · grd 1   (costRb)
--   ABuf  SndAck sb : free 0 · hold 2 · grd 1        (costSb)
--         RcvAck ab : free 0 · hold 0 · grd 1        (costAb)
-- With this table EVERY internal edge drops the summed μ by exactly one.
------------------------------------------------------------------------

-- input-cell cost
costI : IPh → ℕ
costI i0     = 0
costI (i1 _) = 8
costI (i2 _) = 3
costI (ig _) = 1

-- output-cell cost
costO : OPh → ℕ
costO o0     = 0
costO (o1 _) = 0
costO (o2 _) = 4
costO (og _) = 1

-- Transmitter register cost
costTb : MBuf → ℕ
costTb free         = 0
costTb (hold _ _ _) = 4
costTb (grd _ _ _)  = 1

-- Receiver register cost
costRb : MBuf → ℕ
costRb free         = 0
costRb (hold _ _ _) = 2
costRb (grd _ _ _)  = 1

-- SndAck register cost
costSb : ABuf → ℕ
costSb free       = 0
costSb (hold _ _) = 2
costSb (grd _ _)  = 1

-- RcvAck register cost
costAb : ABuf → ℕ
costAb free       = 0
costAb (hold _ _) = 0
costAb (grd _ _)  = 1

-- sum a per-phase cost over a phase vector
μV : ∀ {P xs} → (P → ℕ) → PhV P xs → ℕ
μV cost []        = 0
μV cost (ph ∷ ps) = cost ph + μV cost ps

-- the total measure of a mux state
μ : ∀ {l} → MuxState l → ℕ
μ st = μV costI (iph st) + μV costO (oph st)
     + costTb (tb st) + costRb (rb st) + costSb (sb st) + costAb (ab st)

-- replacing cell `mem` re-balances the vector sum: (new sum) + (old cost) =
-- (old sum) + (new cost).  The subtraction-free equation used by `μV-drop`.
μV-set : ∀ {P xs} (cost : P → ℕ) (ps : PhV P xs) {x} (mem : x ∈ xs) (v : P)
       → μV cost (setPh ps mem v) + cost (getPh ps mem) ≡ μV cost ps + cost v
μV-set cost (ph ∷ ps) (here refl) v =
  solve 3 (λ cv m cp → cv :+ m :+ cp := cp :+ m :+ cv) refl
    (cost v) (μV cost ps) (cost ph)
  where open +-*-Solver
μV-set cost (ph ∷ ps) (there m) v =
  trans (+-assoc (cost ph) (μV cost (setPh ps m v)) (cost (getPh ps m)))
        (trans (cong (cost ph +_) (μV-set cost ps m v))
               (sym (+-assoc (cost ph) (μV cost ps) (cost v))))

-- from `co ≡ k + cn` and `a' + co ≡ a + cn`, conclude `a ≡ a' + k`.
shift : ∀ {a a'} (k : ℕ) {co cn : ℕ} → co ≡ k + cn → a' + co ≡ a + cn → a ≡ a' + k
shift {a} {a'} k {co} {cn} eqc eq =
  sym (+-cancelʳ-≡ cn (a' + k) a
        (trans (+-assoc a' k cn)
               (trans (cong (a' +_) (sym eqc)) eq)))

-- replacing cell `mem` (phase `u`, cost `k + cost v`) by `v` drops the vector
-- sum by exactly `k`: `μV cost ps ≡ μV cost (setPh ps mem v) + k`.
μV-drop : ∀ {P xs} (cost : P → ℕ) (ps : PhV P xs) {x} (mem : x ∈ xs)
          (u v : P) (k : ℕ)
        → getPh ps mem ≡ u → cost u ≡ k + cost v
        → μV cost ps ≡ μV cost (setPh ps mem v) + k
μV-drop cost ps mem u v k gu cu =
  shift k cu
    (subst (λ z → μV cost (setPh ps mem v) + cost z ≡ μV cost ps + cost v)
           gu (μV-set cost ps mem v))

open +-*-Solver

-- every internal edge drops μ by exactly one: `μ st ≡ suc (μ st′)`.
μ-step : ∀ {l} {st st′ : MuxState l} → st ⇒ᵢ st′ → μ st ≡ suc (μ st′)
-- sndmsg: iph 8→3, tb 0→4   (net −1)
μ-step (sndmsg {is = is} {os = os} {rb = rb} {sb = sb} {ab = ab} {x = x} mem gi)
  rewrite μV-drop costI is mem (i1 x) (i2 x) 5 gi refl =
  solve 5 (λ P O R S A → (P :+ con 5) :+ O :+ con 0 :+ R :+ S :+ A
                       := con 1 :+ (P :+ O :+ con 4 :+ R :+ S :+ A)) refl
    (μV costI (setPh is mem (i2 x))) (μV costO os) (costRb rb) (costSb sb) (costAb ab)
-- tx: tb 4→1, rb 0→2   (net −1)
μ-step (tx {is = is} {os = os} {sb = sb} {ab = ab}) =
  solve 4 (λ Ci O S A → Ci :+ O :+ con 4 :+ con 0 :+ S :+ A
                      := con 1 :+ (Ci :+ O :+ con 1 :+ con 2 :+ S :+ A)) refl
    (μV costI is) (μV costO os) (costSb sb) (costAb ab)
-- rcvmsg: oph 0→0, rb 2→1   (net −1)
μ-step (rcvmsg {is = is} {os = os} {tb = tb} {sb = sb} {ab = ab} {x = x} mem gi)
  rewrite μV-drop costO os mem o0 (o1 x) 0 gi refl =
  solve 5 (λ Ci Q T S A → Ci :+ (Q :+ con 0) :+ T :+ con 2 :+ S :+ A
                        := con 1 :+ (Ci :+ Q :+ T :+ con 1 :+ S :+ A)) refl
    (μV costI is) (μV costO (setPh os mem (o1 x))) (costTb tb) (costSb sb) (costAb ab)
-- sndack: oph 4→1, sb 0→2   (net −1)
μ-step (sndack {is = is} {os = os} {tb = tb} {rb = rb} {ab = ab} {x = x} mem gi)
  rewrite μV-drop costO os mem (o2 x) (og x) 3 gi refl =
  solve 5 (λ Ci Q T R A → Ci :+ (Q :+ con 3) :+ T :+ R :+ con 0 :+ A
                        := con 1 :+ (Ci :+ Q :+ T :+ R :+ con 2 :+ A)) refl
    (μV costI is) (μV costO (setPh os mem (og x))) (costTb tb) (costRb rb) (costAb ab)
-- ack: sb 2→1, ab 0→0   (net −1)
μ-step (ack {is = is} {os = os} {tb = tb} {rb = rb}) =
  solve 4 (λ Ci O T R → Ci :+ O :+ T :+ R :+ con 2 :+ con 0
                      := con 1 :+ (Ci :+ O :+ T :+ R :+ con 1 :+ con 0)) refl
    (μV costI is) (μV costO os) (costTb tb) (costRb rb)
-- rcvack: iph 3→1, ab 0→1   (net −1)
μ-step (rcvack {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {x = x} mem gi)
  rewrite μV-drop costI is mem (i2 x) (ig x) 2 gi refl =
  solve 5 (λ P O T R S → (P :+ con 2) :+ O :+ T :+ R :+ S :+ con 0
                       := con 1 :+ (P :+ O :+ T :+ R :+ S :+ con 1)) refl
    (μV costI (setPh is mem (ig x))) (μV costO os) (costTb tb) (costRb rb) (costSb sb)
-- gI: iph 1→0   (net −1)
μ-step (gI {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {x = x} mem gi)
  rewrite μV-drop costI is mem (ig x) i0 1 gi refl =
  solve 6 (λ P O T R S A → (P :+ con 1) :+ O :+ T :+ R :+ S :+ A
                         := con 1 :+ (P :+ O :+ T :+ R :+ S :+ A)) refl
    (μV costI (setPh is mem i0)) (μV costO os) (costTb tb) (costRb rb) (costSb sb) (costAb ab)
-- gO: oph 1→0   (net −1)
μ-step (gO {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb} {ab = ab} {x = x} mem gi)
  rewrite μV-drop costO os mem (og x) o0 1 gi refl =
  solve 6 (λ Ci Q T R S A → Ci :+ (Q :+ con 1) :+ T :+ R :+ S :+ A
                          := con 1 :+ (Ci :+ Q :+ T :+ R :+ S :+ A)) refl
    (μV costI is) (μV costO (setPh os mem o0)) (costTb tb) (costRb rb) (costSb sb) (costAb ab)
-- gT: tb 1→0   (net −1)
μ-step (gT {is = is} {os = os} {rb = rb} {sb = sb} {ab = ab}) =
  solve 5 (λ Ci O R S A → Ci :+ O :+ con 1 :+ R :+ S :+ A
                        := con 1 :+ (Ci :+ O :+ con 0 :+ R :+ S :+ A)) refl
    (μV costI is) (μV costO os) (costRb rb) (costSb sb) (costAb ab)
-- gRc: rb 1→0   (net −1)
μ-step (gRc {is = is} {os = os} {tb = tb} {sb = sb} {ab = ab}) =
  solve 5 (λ Ci O T S A → Ci :+ O :+ T :+ con 1 :+ S :+ A
                        := con 1 :+ (Ci :+ O :+ T :+ con 0 :+ S :+ A)) refl
    (μV costI is) (μV costO os) (costTb tb) (costSb sb) (costAb ab)
-- gSa: sb 1→0   (net −1)
μ-step (gSa {is = is} {os = os} {tb = tb} {rb = rb} {ab = ab}) =
  solve 5 (λ Ci O T R A → Ci :+ O :+ T :+ R :+ con 1 :+ A
                        := con 1 :+ (Ci :+ O :+ T :+ R :+ con 0 :+ A)) refl
    (μV costI is) (μV costO os) (costTb tb) (costRb rb) (costAb ab)
-- gR: ab 1→0   (net −1)
μ-step (gR {is = is} {os = os} {tb = tb} {rb = rb} {sb = sb}) =
  solve 5 (λ Ci O T R S → Ci :+ O :+ T :+ R :+ S :+ con 1
                        := con 1 :+ (Ci :+ O :+ T :+ R :+ S :+ con 0)) refl
    (μV costI is) (μV costO os) (costTb tb) (costRb rb) (costSb sb)

-- every internal edge strictly decreases the measure
μ-dec : ∀ {l} {st st′ : MuxState l} → st ⇒ᵢ st′ → μ st′ < μ st
μ-dec t = ≤-reflexive (sym (μ-step t))
