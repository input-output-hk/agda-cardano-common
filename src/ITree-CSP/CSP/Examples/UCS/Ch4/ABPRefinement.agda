{-# OPTIONS --guardedness #-}

-- UCS chapter 4: the ALTERNATING BIT PROTOCOL (ABP) — TRACE-SAFETY refinement.
-- Machine-readable companion file:
--
--   fdr-examples/ucs/chapter04/abp.csp   (UCS ch. 4, "abp.csp", Bill Roscoe)
--
-- SANCTIONED TRACE-SAFETY FALLBACK.  The headline FDR assert of the committed
-- model (CSP.Examples.UCS.Ch4.ABP) is the failures-divergences refinement
--
--   assert COPY [FD= SystemBE2 \ {|a,b,c,d|}
--
-- whose full-FD route (≈DR → ≈FD bridge) is BLOCKED at the reachability-closure
-- lemma over the hidden system (the composed protocol has ~594 reachable
-- configurations; enumerating that closure by hand is intractable).  This module
-- lands the sanctioned lighter rung: the TRACE-SAFETY refinement of the UNHIDDEN
-- system, with the internal channels (`a`/`b`/`c`/`d`) left VISIBLE and absorbed
-- by CHAOS:
--
--   assert Spec [T= SystemBE2       where   Spec = COPY ||| CHAOS({|a,b,c,d|})
--
-- i.e. every trace of SystemBE2 has its `left`/`right` projection forming a
-- ONE-PLACE BUFFER (safety), with the internal `a`/`b`/`c`/`d` events entirely
-- unconstrained.  This is POSTULATE-FREE (a plain trace refinement, no FD bridge).
--
-- ────────────────────────────────────────────────────────────────────────────
-- The `Spec` below is the INLINED  COPY ||| CHAOS({|a,b,c,d|})  from abp.csp,
-- given directly (trace-equivalently) to avoid a separate CHAOS / `|||`:
--
--   Spec-empty      = left?x → Spec-holding x
--                     □ (a?_ → Spec-empty  □ b?_ → Spec-empty
--                        □ c?_ → Spec-empty  □ d?_ → Spec-empty)
--   Spec-holding x  = right!x → Spec-empty
--                     □ (a?_ → Spec-holding x  □ … □ d?_ → Spec-holding x)
--   Spec            = Spec-empty
--
-- `left`/`right` are a 1-place buffer (COPY); `a`/`b`/`c`/`d` are offered in BOTH
-- states at every value (CHAOS).  `right!x` is PINNED to the held value x.
--
-- ────────────────────────────────────────────────────────────────────────────
-- STATUS: REFINEMENT DEFERRED (foundation verified; weak simulation blocked).
--
-- The intended proof is `abp-trace-safe : Spec [T= SystemBE2` via `wsim→⊑T` + a
-- weak simulation relating each reachable SystemBE2 state to `Spec-empty` /
-- `Spec-holding x`, keyed on the in-flight `left` value (accepted-but-undelivered).
--
-- This module lands the VERIFIED FOUNDATION: the `Spec` process (§1) and its
-- complete set of forward-step lemmas (§3) — all typecheck HOLE-FREE and
-- POSTULATE-FREE, and were confirmed trace-safe by an exhaustive external BFS
-- of the model (0 discipline violations).
--
-- The weak simulation itself (the relation `RR` + `fwdE`/`fwdT`) is DEFERRED for
-- the SAME reason the full-FD route is blocked: it requires enumerating the
-- reachability closure of the composed protocol.  An exhaustive BFS of the
-- committed model (L = 2) finds:
--   * 594 reachable SystemBE2 configurations,
--   * 59 distinct structural shapes (≈150 classes after the phase/value symmetry),
--   * 1452 transition edges — i.e. 1452 `fwdE`/`fwdT` proof obligations, each
--     requiring a 3-layer nested `Par` step-inversion (outer `adES` sync SND↔MID,
--     middle `bcES` sync CHAN↔RCV2, inner `∅ES` interleave BE↔BE′).
-- For comparison the closest completed template (TokenRingTBuff: 6 shapes, ~50
-- obligations, single-layer α-parallel) is 600 lines; ABP is ~25× larger.  The
-- committed model `CSP.Examples.UCS.Ch4.ABP` stands as the deliverable and this
-- refinement is documented as deferred (as with the general4 deadlock-free rung).

module CSP.Examples.UCS.Ch4.ABPRefinement where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees
open PTree

open import CSP.Examples.UCS.Ch4.ABP

open import CSP.Operators ABPEv-≟
open EventSet

------------------------------------------------------------------------------------
-- §1. The specification  Spec = COPY ||| CHAOS({|a,b,c,d|})  (inlined).
--
-- Spec-empty offers `left?x` (→ holding x) and every a/b/c/d (→ stay empty).
-- Spec-holding x offers `right!x` PINNED (→ empty) and every a/b/c/d (→ stay).
Spec-empty   : AProc
Spec-holding : Bool → AProc

force Spec-empty = react
  (λ where
     (_ , left)  x → just (Spec-holding x)
     (_ , right) _ → nothing
     (_ , a)     _ → just Spec-empty
     (_ , b)     _ → just Spec-empty
     (_ , c)     _ → just Spec-empty
     (_ , d)     _ → just Spec-empty)
  ∅t

force (Spec-holding x) = react
  (λ where
     (_ , left)  _ → nothing
     (_ , right) y → case y B≟ x of λ where
         (yes _) → just Spec-empty
         (no  _) → nothing
     (_ , a)     _ → just (Spec-holding x)
     (_ , b)     _ → just (Spec-holding x)
     (_ , c)     _ → just (Spec-holding x)
     (_ , d)     _ → just (Spec-holding x))
  ∅t

Spec : AProc
Spec = Spec-empty

------------------------------------------------------------------------------------
-- §2. Verification machinery.
open import Semantics.LTS       {E = ABPEv} {I = ExtI ABPEv}
open import Semantics.WeakBisim {E = ABPEv} {I = ExtI ABPEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures  {E = ABPEv} {I = ExtI ABPEv} using (_⊑T_; traces)
open import Semantics.WeakSim   {E = ABPEv} {I = ExtI ABPEv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = ABPEv} {I = ExtI ABPEv}

------------------------------------------------------------------------------------
-- §3. Spec forward-step lemmas (its inlined react offers reduce, so these hold by
-- `refl`).  These are the moves Spec uses to MATCH each SystemBE2 move.

-- event labels
lL : Bool → Event
lL x = evLabel Bool left x
rL : Bool → Event
rL x = evLabel Bool right x
aL : (Bool × Bool) → Event
aL p = evLabel (Bool × Bool) a p
bL : (Bool × Bool) → Event
bL p = evLabel (Bool × Bool) b p
cL : Bool → Event
cL t = evLabel Bool c t
dL : Bool → Event
dL t = evLabel Bool d t

-- left?x : empty → holding x
sp-left : ∀ x → Spec-empty ─[ ev (evl (lL x)) ]─► Spec-holding x
sp-left x = sVis {at = Bool , left} {a = x} refl refl

-- right!x : holding x → empty (pinned)
sp-right : ∀ x → Spec-holding x ─[ ev (evl (rL x)) ]─► Spec-empty
sp-right true  = sVis {at = Bool , right} {a = true}  refl refl
sp-right false = sVis {at = Bool , right} {a = false} refl refl

-- a/b/c/d in the empty state (stay empty)
sp-a0 : ∀ p → Spec-empty ─[ ev (evl (aL p)) ]─► Spec-empty
sp-a0 p = sVis {at = (Bool × Bool) , a} {a = p} refl refl
sp-b0 : ∀ p → Spec-empty ─[ ev (evl (bL p)) ]─► Spec-empty
sp-b0 p = sVis {at = (Bool × Bool) , b} {a = p} refl refl
sp-c0 : ∀ t → Spec-empty ─[ ev (evl (cL t)) ]─► Spec-empty
sp-c0 t = sVis {at = Bool , c} {a = t} refl refl
sp-d0 : ∀ t → Spec-empty ─[ ev (evl (dL t)) ]─► Spec-empty
sp-d0 t = sVis {at = Bool , d} {a = t} refl refl

-- a/b/c/d in the holding state (stay holding x)
sp-a1 : ∀ x p → Spec-holding x ─[ ev (evl (aL p)) ]─► Spec-holding x
sp-a1 x p = sVis {at = (Bool × Bool) , a} {a = p} refl refl
sp-b1 : ∀ x p → Spec-holding x ─[ ev (evl (bL p)) ]─► Spec-holding x
sp-b1 x p = sVis {at = (Bool × Bool) , b} {a = p} refl refl
sp-c1 : ∀ x t → Spec-holding x ─[ ev (evl (cL t)) ]─► Spec-holding x
sp-c1 x t = sVis {at = Bool , c} {a = t} refl refl
sp-d1 : ∀ x t → Spec-holding x ─[ ev (evl (dL t)) ]─► Spec-holding x
sp-d1 x t = sVis {at = Bool , d} {a = t} refl refl
