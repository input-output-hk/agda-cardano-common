{-# OPTIONS --guardedness #-}

-------------------------------------------------------------------------------------
-- TWO MACHINE-CHECKED REFUTATIONS: no BARE failures-containment order implies the
-- trace order.  (Roscoe's `_⊑F_` does — it is the PAIR — which is why it is defined
-- that way; see §1.)
--
-- The positive (divergence-free) repairs live in `Semantics.RefinementOrders`; this
-- module is the negative control that shows the divergence-freedom hypothesis there is
-- not decoration.  Style follows `CSP.Examples.InvariantMini` Parts 2/3: a tiny local
-- alphabet, processes built directly from `PTree.force`, no CSP operators, no Cardano.
--
-- §1  `⊇F ⟹ ⊑T` is FALSE.      Witness `Stop ⊇F (a ⟶ div)`, and `Stop` has no ⟨a⟩.
--     `Q = a ⟶ div` never stabilises after `a`, so `failures Q ⟨a⟩ X` is EMPTY and the
--     failure-containment obligation at `⟨a⟩` is vacuous.
--
--     ⚠ THIS SECTION USED TO BE STATED AT `_⊑F_`, AND IT IS THE REASON `_⊑F_` CHANGED.
--     `Semantics.Failures._⊑F_` is now Roscoe's stable-failures refinement, the PAIR
--     `(P ⊑T Q) × (P ⊇F Q)`, so `⊑F ⟹ ⊑T` is now TRUE BY PROJECTION (`⊑F→⊑T` below).
--     What remains false — and is what the old statement actually established — is the
--     implication from the FAILURES HALF `_⊇F_` alone.  FDR 4.2.7 agrees: `assert STOP
--     [F= (a -> DIV)` fails there with a TRACE counterexample ("Error Event: a"), so
--     comparing failures alone was never `[F=`.  See `docs/fdr/2026-09-08-refinement-orders.csp`.
--
-- §2  `⊇F⊥ ⟹ ⊑T` — and hence `⊑FD ⟹ ⊑T` — is FALSE too, for a DIFFERENT reason, and
--     this one is worth spelling out because it contradicts the textbook slogan.  In
--     the classical FD model `T(P)` is divergence-CLOSED, so `⊑FD ⟹ ⊑T` holds there.
--     Here `traces` is the RAW LTS trace set while `divergences`/`failures⊥` are
--     divergence-strict: `divergences P s` only witnesses a run on a PREFIX of `s`.
--     So `div` (which refines everything in `⊑FD`, being the FD bottom) has `[]` as its
--     ONLY trace, and `div ⊑FD (a ⟶ Stop)` while `¬ (div ⊑T (a ⟶ Stop))`.
--     Moral: a `⊑FD` fact constrains traces only alongside divergence-freedom of the
--     SPECIFICATION — that is `Semantics.RefinementOrders.⊑FD→⊑T-df`.  Unlike §1 this
--     one is NOT repaired by the `_⊑F_` fix: `_⊇F⊥_`/`_⊑FD_` still carry no trace
--     component.
--
-- Nothing here is postulated and nothing is left as a hole.
-------------------------------------------------------------------------------------

open import Level using (0ℓ) renaming (suc to ℓsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees

module CSP.Examples.RefinementOrderCounterexamples where

-------------------------------------------------------------------------------------
-- §0  A one-event alphabet and the four processes.
-------------------------------------------------------------------------------------

-- the single ⊤-carried channel `a` (declared before the module header's imports use it)
data Ev : Set → Set where
  a : Ev ⊤

open import Semantics.LTS       {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev}
  using (Event√; evl; evLabel; ev; τ; _─[_]─►_; sRet; sSil; sVis; sTau)
open import Semantics.Refusals  {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev}
  using (Refuses; deadlock-refuses; deadlock-no-offer)
open import Semantics.Failures  {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures; _⊑T_; _⊑F_; _⊇F_; ⊑F→⊑T)
open import Semantics.DRBisim   {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev}
  using (Diverges; div-diverges)
open import Semantics.Stability {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev} using (stable-not-sil)
open import Semantics.FailuresDivergences {0ℓ} {0ℓ} {ℓsuc 0ℓ} {Ev} {ExtI Ev}
  using (IsDivergence; divergences; failures⊥; _⊇F⊥_; _⊇D_; _⊑FD_)

-- the value type of every process here
Ret : Set
Ret = ⊤ {0ℓ}

-- shorthand for a process tree over this alphabet
Proc : Set₁
Proc = PTree Ev (ExtI Ev) Ret

-- the visible event `a`
evA : Event√ Ret
evA = evl (evLabel (⊤ {0ℓ}) a tt)

-- `a ⟶ div` : offers `a`, then spins silently forever (never stabilises again)
aDiv : Proc
PTree.force aDiv = react (λ { (_ , a) _ → just div }) (λ _ _ → nothing)

-- `a ⟶ Stop` : offers `a`, then deadlocks
aStop : Proc
PTree.force aStop = react (λ { (_ , a) _ → just deadlock }) (λ _ _ → nothing)

-------------------------------------------------------------------------------------
-- §0.1  Facts about `div` and `deadlock` on this alphabet.
-------------------------------------------------------------------------------------

-- every τ-successor of `div` is `div` again
div-τ : {t : Proc} → div ─[ τ ]─► t → t ≡ div
div-τ (sSil eq)   = sym (sil-injective eq)
div-τ (sTau eq _) = ⊥-elim (sil≢react eq)

-- `div` has no visible step at all
div-no-ev : {t : Proc} {e : Event√ Ret} → ¬ (div ─[ ev e ]─► t)
div-no-ev (sRet ())
div-no-ev (sVis eq _) = ⊥-elim (sil≢react eq)

-- `div` is not stable (its force is `sil`)
div-not-stable : ¬ (isStable (div {E = Ev} {I = ExtI Ev} {R = Ret}))
div-not-stable st = stable-not-sil {R = Ret} {t = div} {u = div} st refl

-- hence every run out of `div` is empty and stays at `div`
div-run : {t : Proc} {s : List (Event√ Ret)} → div ⟹⟨ s ⟩ t → s ≡ [] × t ≡ div
div-run ⟹-refl        = refl , refl
div-run (⟹-τ st rest) with div-τ st
... | refl                = div-run rest
div-run (⟹-ev st _)   = ⊥-elim (div-no-ev st)

-- `deadlock` performs no visible trace at all
deadlock-no-run : {t : Proc} {e : Event√ Ret} {s : List (Event√ Ret)}
                → ¬ (deadlock ⟹⟨ e ∷ s ⟩ t)
deadlock-no-run (⟹-τ (sSil ()) _)
deadlock-no-run (⟹-τ (sTau refl ()) _)
deadlock-no-run (⟹-ev st _) = deadlock-no-offer st

-------------------------------------------------------------------------------------
-- §1  `⊇F ⟹ ⊑T` is FALSE:  `Stop ⊇F (a ⟶ div)`  but  `¬ (Stop ⊑T (a ⟶ div))`.
-------------------------------------------------------------------------------------

-- `a ⟶ div` has no τ-move of its own
aDiv-no-τ : {t : Proc} → ¬ (aDiv ─[ τ ]─► t)
aDiv-no-τ (sSil ())
aDiv-no-τ (sTau refl ())

-- …and its only visible step is `a`, landing in `div`
aDiv-ev : {t : Proc} {e : Event√ Ret} → aDiv ─[ ev e ]─► t → t ≡ div
aDiv-ev (sRet ())
aDiv-ev (sVis {at = _ , a} refl refl) = refl

-- every FAILURE of `a ⟶ div` sits at the EMPTY trace: after `a` the process spins,
-- so it never reaches a stable state and carries no failure there
aDiv-failure-[] : {X : Event√ Ret → Set 0ℓ} {s : List (Event√ Ret)}
                → failures aDiv s X → s ≡ []
aDiv-failure-[] (_ , ⟹-refl , _)            = refl
aDiv-failure-[] (_ , ⟹-τ st _ , _)          = ⊥-elim (aDiv-no-τ st)
aDiv-failure-[] (P′ , ⟹-ev st rest , (stb , _)) with aDiv-ev st
... | refl with div-run rest
...   | refl , refl                          = ⊥-elim (div-not-stable stb)

-- `Stop` contains every FAILURE of `a ⟶ div` (vacuously past `⟨a⟩`).  Note this is
-- `_⊇F_`, NOT `_⊑F_`: the trace half fails, which is exactly the point of §1.
Stop⊇F-aDiv : deadlock ⊇F aDiv
Stop⊇F-aDiv s X f with aDiv-failure-[] f
... | refl = deadlock , ⟹-refl , deadlock-refuses

-- but `Stop` does not refine it in the TRACE order: `⟨a⟩` is a trace of `a ⟶ div` only
¬Stop⊑T-aDiv : ¬ (deadlock ⊑T aDiv)
¬Stop⊑T-aDiv le with le (evA ∷ []) (div , ⟹-ev (sVis refl refl) ⟹-refl)
... | _ , run = deadlock-no-run run

-- DELIVERABLE 2: bare FAILURE CONTAINMENT does NOT imply the trace order.  This is the
-- fact that forced `_⊑F_` to be the (traces, failures) PAIR rather than failures alone.
⊇F→⊑T-FALSE : ¬ (∀ {P Q : Proc} → P ⊇F Q → P ⊑T Q)
⊇F→⊑T-FALSE h = ¬Stop⊑T-aDiv (h Stop⊇F-aDiv)

-- …and the contrast: for the REPAIRED `_⊑F_` the implication is now trivially true,
-- because the trace component is one of the two conjuncts.  Kept beside the refutation
-- so the two statements cannot be confused for one another again.
⊑F→⊑T-TRUE : ∀ {P Q : Proc} → P ⊑F Q → P ⊑T Q
⊑F→⊑T-TRUE = ⊑F→⊑T

-- the corollary the refutation buys: `Stop` is NOT a `⊑F` refinement of `a ⟶ div`,
-- matching FDR's rejection of `assert STOP [F= (a -> DIV)` on a trace counterexample
¬Stop⊑F-aDiv : ¬ (deadlock ⊑F aDiv)
¬Stop⊑F-aDiv h = ¬Stop⊑T-aDiv (⊑F→⊑T h)

-------------------------------------------------------------------------------------
-- §2  `⊇F⊥ ⟹ ⊑T` and `⊑FD ⟹ ⊑T` are FALSE:  `div ⊑FD (a ⟶ Stop)` but `div` has no
--     `⟨a⟩` trace.  `div` is the FD bottom, yet the TRACE bottom is `RUN`, not `div`.
-------------------------------------------------------------------------------------

-- every trace is a divergence of `div` (its empty prefix already diverges)
div-divergences : {s : List (Event√ Ret)} → divergences div s
div-divergences {s} = record
  { prefix = [] ; suffix = s ; split = refl
  ; witness = div ; reach = ⟹-refl ; divwit = div-diverges }

-- so `div` refines EVERY process in the divergence-strict orders
div⊇F⊥ : {Q : Proc} → div ⊇F⊥ Q
div⊇F⊥ _ = inj₂ div-divergences

div⊑FD : {Q : Proc} → div ⊑FD Q
div⊑FD = div⊇F⊥ , λ _ → div-divergences

-- but `div` performs no visible event, so it does not refine `a ⟶ Stop` on traces
¬div⊑T-aStop : ¬ (div ⊑T aStop)
¬div⊑T-aStop le with le (evA ∷ []) (deadlock , ⟹-ev (sVis refl refl) ⟹-refl)
... | _ , run with div-run run
...   | () , _

-- DELIVERABLE 1 (REFUTED): neither `⊇F⊥` nor `⊑FD` implies the trace order
⊇F⊥→⊑T-FALSE : ¬ (∀ {P Q : Proc} → P ⊇F⊥ Q → P ⊑T Q)
⊇F⊥→⊑T-FALSE h = ¬div⊑T-aStop (h div⊇F⊥)

⊑FD→⊑T-FALSE : ¬ (∀ {P Q : Proc} → P ⊑FD Q → P ⊑T Q)
⊑FD→⊑T-FALSE h = ¬div⊑T-aStop (h div⊑FD)
