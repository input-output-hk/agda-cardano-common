{-# OPTIONS --guardedness #-}

-- SPIKE: the (stable) failures model on the pure-react LTS.
-- A failure is a (trace, refusal) pair: a τ-abstracting visible trace `s` reaching a
-- state that refuses the event set `X`.  Plus trace/failure refinement preorders:
-- `_⊑T_` (traces), `_⊇F_` (failures only) and Roscoe's `_⊑F_`, which is the PAIR.
--
-- Both orders are built on a CONTAINMENT PRIMITIVE (`_⊇T_`, `_⊇F_`): the traces model
-- `T`'s refinement is trace containment alone, the stable-failures model `𝓕`'s is
-- trace containment AND failure containment. Naming both containments uniformly makes
-- that model structure explicit instead of incidental.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary using (Preorder; IsPreorder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; isEquivalence)

open import Process_Trees

module Semantics.Failures {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Refusals  {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
-- only `stable-force-eq` is needed below; `Semantics.Stability` sits UPSTREAM of this
-- module (it depends only on `LTS`/`WeakBisim`), so importing it here creates no cycle
open import Semantics.Stability {ℓ} {ℓe} {ℓi} {E} {I} using (stable-force-eq)

-- τ-abstracting big-step: p performs the visible trace s (τ's are silent) reaching q
data _⟹⟨_⟩_ {ℓr} {R : Set ℓr}
    : PTree E I R → List (Event√ R) → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ⟹-refl : ∀ {p} → p ⟹⟨ [] ⟩ p
  ⟹-τ    : ∀ {p q r s}             → p ─[ τ ]─► q    → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
  ⟹-ev   : ∀ {p q r s} {e : Event√ R} → p ─[ ev e ]─► q → q ⟹⟨ s ⟩ r → p ⟹⟨ e ∷ s ⟩ r

-- traces and (stable) failures
traces : ∀ {ℓr} {R : Set ℓr} → PTree E I R → List (Event√ R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
traces P s = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ P′)

failures : ∀ {ℓr ℓx} {R : Set ℓr}
         → PTree E I R → List (Event√ R) → (Event√ R → Set ℓx)
         → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓx)
failures P s X = Σ[ P′ ∈ PTree E I _ ] (P ⟹⟨ s ⟩ P′ × Refuses P′ X)

-- CONTAINMENT PRIMITIVE.  Direction follows the argument order: `P ⊇T Q` says P's
-- traces CONTAIN Q's, which is what refinement in the traces model amounts to — the
-- same convention as `_⊇F_` below (`⊇`, not `⊆`, because with P on the left it is
-- P's set that contains Q's).
_⊇T_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
P ⊇T Q = ∀ s → traces Q s → traces P s

-- refinement: P ⊑ Q  iff  Q's behaviours are among P's.  Refinement in the TRACES
-- MODEL is exactly trace containment.  `_⊑T_` stays the name callers use for it (same
-- policy as `_⊑F_` below); `_⊇T_` above is the primitive it is DEFINITIONALLY built
-- from, so every existing `⊑ᵀ` lemma keeps typechecking with no edit.
_⊑T_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
P ⊑T Q = P ⊇T Q

-- FAILURE CONTAINMENT ALONE — the weaker HALF of `_⊑F_` below, and NOT a refinement
-- order in Roscoe's sense.  A trace that never reaches a stable state carries no
-- failure at all, so this obligation is VACUOUS exactly where the implementation
-- diverges: `deadlock ⊇F (a ⟶ div)` holds even though `deadlock` has no ⟨a⟩ trace
-- (machine-checked in `CSP.Examples.RefinementOrderCounterexamples`).  Kept because
-- several results genuinely establish only this half, and because it is the right
-- building block: `_⊑F_` is `_⊑T_` paired with it.
--
-- POLICY: `_⊇F_` is kept only (a) as a proof component that feeds a corresponding
-- `_⊑F_` result within the same module, wrapped `private` at each such use, and (b) as
-- the subject of the deliberate negative control in
-- `CSP.Examples.RefinementOrderCounterexamples`, which is exactly what shows `_⊑F_`
-- must carry a trace component at all. Ordinary callers should always state and consume
-- refinement at `_⊑F_`, never at bare `_⊇F_`.
_⊇F_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
_⊇F_ {ℓr = ℓr} {R = R} P Q = ∀ s (X : Event√ R → Set ℓr) → failures Q s X → failures P s X

-- ROSCOE'S STABLE-FAILURES REFINEMENT.  The 𝓕 model represents a process as the PAIR
-- (traces P , failures P), so refinement is trace containment AND failure containment.
-- Comparing failures alone (`_⊇F_` above) is STRICTLY WEAKER: it would make `Stop`
-- refine `a ⟶ div`, which FDR 4.2.7 rejects with a TRACE counterexample
-- ("Error Event: a"; `docs/fdr/2026-09-08-refinement-orders.csp`).
_⊑F_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr)
P ⊑F Q = (P ⊇T Q) × (P ⊇F Q)

-- the trace component of a stable-failures refinement (formerly a REFUTED implication;
-- under the corrected `_⊑F_` it is a projection)
⊑F→⊑T : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → P ⊑F Q → P ⊑T Q
⊑F→⊑T = proj₁

-- …and its failure component
⊑F→⊇F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} → P ⊑F Q → P ⊇F Q
⊑F→⊇F = proj₂

-- all three refinements are preorders
⊑T-refl  : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑T P
⊑T-refl P s t = t
⊑T-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑T Q → Q ⊑T S → P ⊑T S
⊑T-trans pq qs s t = pq s (qs s t)

⊇F-refl  : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊇F P
⊇F-refl P s X f = f
⊇F-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊇F Q → Q ⊇F S → P ⊇F S
⊇F-trans pq qs s X f = pq s X (qs s X f)

⊑F-refl  : ∀ {ℓr} {R : Set ℓr} (P : PTree E I R) → P ⊑F P
⊑F-refl P = ⊑T-refl P , ⊇F-refl P
⊑F-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R} → P ⊑F Q → Q ⊑F S → P ⊑F S
⊑F-trans (pqT , pqF) (qsT , qsF) = ⊑T-trans pqT qsT , ⊇F-trans pqF qsF

-------------------------------------------------------------------------------------
-- FORCE-EQUAL TREES ARE ⊑F-INTERCHANGEABLE.
--
-- `PTree` is a COINDUCTIVE record, so it has no η: a defined process `P` and an
-- explicitly-unfolded one-step FSM `Q` with `PTree.force P ≡ PTree.force Q` need NOT
-- be the propositionally-equal same term (e.g. `Skip >> P` vs `P`).  But every step of
-- the LTS reads its source tree only through `force`, so `_⊑F_` is force-invariant —
-- exactly the situation a calibrated leaf spec is in.  This is the `⊑F` sibling of
-- `Semantics.FailuresDivergences.force-≡→⊑FD` (that module sits DOWNSTREAM of this one,
-- so it cannot be reused directly); the three helpers below are private local
-- transcriptions of its `step-force-≡`/`Refuses-force-≡`/`failures-force-≡`, kept
-- private so they cannot collide with those public names when both modules are opened
-- unqualified by a downstream consumer.
-------------------------------------------------------------------------------------

private
  -- a step reads its source only through `force`, so an equal force admits the same step
  step-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q t : PTree E I R} {l : Label R}
               → PTree.force p ≡ PTree.force q → q ─[ l ]─► t → p ─[ l ]─► t
  step-force-≡ eq (sRet ef)    = sRet (trans eq ef)
  step-force-≡ eq (sSil ef)    = sSil (trans eq ef)
  step-force-≡ eq (sVis ef ej) = sVis (trans eq ef) ej
  step-force-≡ eq (sTau ef ej) = sTau (trans eq ef) ej

  -- `Refuses` reads its tree only through `force` (stability is a `force` predicate,
  -- and every `Offers` witness is a step out of the root)
  Refuses-force-≡ : ∀ {ℓr ℓx} {R : Set ℓr} {p q : PTree E I R} {X : Event√ R → Set ℓx}
                   → PTree.force p ≡ PTree.force q → Refuses q X → Refuses p X
  Refuses-force-≡ {p = p} {q = q} eq (st , noff) =
    stable-force-eq {p = p} {q = q} eq st
    , λ e Xe (t′ , step) → noff e Xe (t′ , step-force-≡ (sym eq) step)

  -- …hence so does a failure: a non-trivial run transports its first step to the new
  -- root, and a 0-step run reflects the endpoint's refusal back through the equal force
  failures-force-≡ : ∀ {ℓr ℓx} {R : Set ℓr} {p q : PTree E I R}
                     {s : List (Event√ R)} {X : Event√ R → Set ℓx}
                   → PTree.force p ≡ PTree.force q → failures q s X → failures p s X
  failures-force-≡ {p = p} eq (_ , ⟹-refl , ref) = p , ⟹-refl , Refuses-force-≡ eq ref
  failures-force-≡ eq (w , ⟹-τ  step rest , ref) = w , ⟹-τ  (step-force-≡ eq step) rest , ref
  failures-force-≡ eq (w , ⟹-ev step rest , ref) = w , ⟹-ev (step-force-≡ eq step) rest , ref

  -- …and so does a TRACE: same transport, with no refusal to carry along
  traces-force-≡ : ∀ {ℓr} {R : Set ℓr} {p q : PTree E I R} {s : List (Event√ R)}
                 → PTree.force p ≡ PTree.force q → traces q s → traces p s
  traces-force-≡ {p = p} eq (_ , ⟹-refl)        = p , ⟹-refl
  traces-force-≡ eq (w , ⟹-τ  step rest)        = w , ⟹-τ  (step-force-≡ eq step) rest
  traces-force-≡ eq (w , ⟹-ev step rest)        = w , ⟹-ev (step-force-≡ eq step) rest

-- ONE-DIRECTIONAL bridge: if a defined process and an explicitly-unfolded FSM agree on
-- their `force`, the FSM's failures are among the process's — the exact fact a
-- calibrated leaf spec needs to relate a `_>>=_`/`iter`-built process to its hand-drawn
-- unfolding without building a full `FSim`/`Bisim`
force-≡→⊑T : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
           → PTree.force P ≡ PTree.force Q → P ⊑T Q
force-≡→⊑T eq s t = traces-force-≡ eq t

force-≡→⊇F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
            → PTree.force P ≡ PTree.force Q → P ⊇F Q
force-≡→⊇F eq s X f = failures-force-≡ eq f

force-≡→⊑F : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
           → PTree.force P ≡ PTree.force Q → P ⊑F Q
force-≡→⊑F eq = force-≡→⊑T eq , force-≡→⊇F eq

-- TWO-DIRECTIONAL version: force-equality gives failure-refinement both ways, since the
-- equality itself is symmetric
force-≡→⊑F-both : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
                 → PTree.force P ≡ PTree.force Q → (P ⊑F Q) × (Q ⊑F P)
force-≡→⊑F-both eq = force-≡→⊑F eq , force-≡→⊑F (sym eq)

-- deadlock's only failure is the empty trace refusing anything (it is maximally refusing)
deadlock-failure : ∀ {ℓr ℓx} {R : Set ℓr} {X : Event√ R → Set ℓx} → failures deadlock [] X
deadlock-failure = deadlock , ⟹-refl , deadlock-refuses

-------------------------------------------------------------------------------------
-- TRACES are respected by weak bisimulation (traces-respects-≈).
-- (FAILURES are NOT — see div≈deadlock below; that needs divergence-respecting bisim.)
-------------------------------------------------------------------------------------

-- a leading τ* run is silent, so it doesn't change the trace
τ*-then : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s}
        → p ─[τ*]─► q → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
τ*-then τ*-refl           tr = tr
τ*-then (τ*-step pτ rest) tr = ⟹-τ pτ (τ*-then rest tr)

weaken-τ : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s}
         → p ═[ τ ]═► q → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
weaken-τ (wτ pre) tr = τ*-then pre tr

weaken-ev : ∀ {ℓr} {R : Set ℓr} {p q r : PTree E I R} {s} {e : Event√ R}
          → p ═[ ev e ]═► q → q ⟹⟨ s ⟩ r → p ⟹⟨ e ∷ s ⟩ r
weaken-ev (wev pre evs post) tr = τ*-then pre (⟹-ev evs (τ*-then post tr))

-- appending a (silent) τ*-run to the end of a big-step keeps the same trace
⟹-then-τ* : ∀ {ℓr} {R : Set ℓr} {P Q Q′ : PTree E I R} {s}
           → P ⟹⟨ s ⟩ Q → Q ─[τ*]─► Q′ → P ⟹⟨ s ⟩ Q′
⟹-then-τ* ⟹-refl         tτ = τ*-then tτ ⟹-refl
⟹-then-τ* (⟹-τ pτ rest)   tτ = ⟹-τ pτ (⟹-then-τ* rest tτ)
⟹-then-τ* (⟹-ev pev rest) tτ = ⟹-ev pev (⟹-then-τ* rest tτ)

-- bisimilar processes simulate each other's traces
trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
          → Wbisim R P Q → P ⟹⟨ s ⟩ P′
          → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × Wbisim R P′ Q′)
trace-sim p≈q ⟹-refl = _ , ⟹-refl , p≈q
trace-sim p≈q (⟹-τ pτ rest)  with p≈q .Wbisim.fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≈q₁ with trace-sim p₁≈q₁ rest
...   | Q′ , q⟹ , p′≈q′ = Q′ , weaken-τ qτ q⟹ , p′≈q′
trace-sim p≈q (⟹-ev pev rest) with p≈q .Wbisim.fwd .WSimF.on-ev pev
... | _ , qev , p₁≈q₁ with trace-sim p₁≈q₁ rest
...   | Q′ , q⟹ , p′≈q′ = Q′ , weaken-ev qev q⟹ , p′≈q′

-- weak bisimulation ⇒ trace equivalence (both directions)
traces-≈→ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} {s}
          → Wbisim R P Q → traces P s → traces Q s
traces-≈→ p≈q (_ , tr) with trace-sim p≈q tr
... | Q′ , q⟹ , _ = Q′ , q⟹

traces-respects-≈ : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} {s}
                  → Wbisim R P Q → (traces P s → traces Q s) × (traces Q s → traces P s)
traces-respects-≈ p≈q = traces-≈→ p≈q , traces-≈→ (wbisim-sym p≈q)

-------------------------------------------------------------------------------------
-- Why FAILURES are not respected: the divergent process div (= sil div, an infinite
-- τ-loop) is weakly bisimilar to deadlock — yet failures div = ∅ (div is never stable)
-- while failures deadlock ∋ ([] , X).  So failures-respects-≈ is FALSE for plain weak
-- bisimulation; it requires divergence-respecting (or stable/branching) bisimulation.
-------------------------------------------------------------------------------------

div≈deadlock : ∀ {ℓr} {R : Set ℓr} → Wbisim R (div {E = E} {I = I}) deadlock
div≈deadlock .Wbisim.fwd .WSimF.on-ev  (sRet ())
div≈deadlock .Wbisim.fwd .WSimF.on-ev  (sVis eq _) = ⊥-elim (sil≢react eq)
div≈deadlock .Wbisim.fwd .WSimF.on-tau (sSil refl) = deadlock , wτ τ*-refl , div≈deadlock
div≈deadlock .Wbisim.fwd .WSimF.on-tau (sTau eq _) = ⊥-elim (sil≢react eq)
div≈deadlock .Wbisim.bwd .WSimF.on-ev  (sRet ())
div≈deadlock .Wbisim.bwd .WSimF.on-ev  (sVis refl ())
div≈deadlock .Wbisim.bwd .WSimF.on-tau (sSil ())
div≈deadlock .Wbisim.bwd .WSimF.on-tau (sTau refl ())

⊑T-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑T-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≡_
  ; _≲_        = _⊑T_
  ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl → ⊑T-refl _ }
      ; trans         = ⊑T-trans
      }
  }

⊑F-preorder : ∀ {ℓr} (R : Set ℓr) → Preorder _ _ _
⊑F-preorder R = record
  { Carrier    = PTree E I R
  ; _≈_        = _≡_
  ; _≲_        = _⊑F_
  ; isPreorder = record
      { isEquivalence = isEquivalence
      ; reflexive     = λ { refl → ⊑F-refl _ }
      ; trans         = ⊑F-trans
      }
  }
