{-
  Basic-process laws (Stop, Ret/Skip, guard, Run, Run′) — both trace
  and failures/divergences lemmas.
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; cong)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; [_]; length; reverse; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Class.DecEq using (DecEq; _≟_)
open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences

module CSP.Laws.BasicProcesses
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces
open Failures

-- Aliases used by the FD section (Skip/guard lemmas use ⊤′ and tt′)
private
  ⊤′ = ⊤
  tt′ = tt

-----------------------------------------------------------------------------
-- Trace lemmas
-- (from CSP.Laws.Traces, lines 43–231)
-----------------------------------------------------------------------------

-----------------------------------------------------------------
-- Stop makes no τ step
Stop-no-τ :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
  → Stop ─[ τ ]─► t′
  → ⊥
Stop-no-τ tr = τ-from-force-vis-impossible refl tr

-- Stop makes no ev step
-- If nothing ≡ just t', then we can produce ⊥
Stop-no-evl :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}
  → Stop ─[ ev (evl (evLabel A e a)) ]─► t′
  → ⊥
Stop-no-evl {t′ = t′} {A = A} {e = e} {a = a} tr with ev-ndbr tr
... | inj₁ (f , force≡vis , f-eq) =
  nothing≢just
    (subst (λ g → g (A , e) a ≡ just _)
           (vis-injective (sym force≡vis))   -- f ≡ λ _ _ → nothing
           f-eq)                        -- f (A , e) a ≡ just t′
  where
    nothing≢just : nothing ≡ just _ → ⊥
    nothing≢just ()
-- mix disjunct from ev-ndbr is impossible: force Stop ≡ vis _, not mix.
... | inj₂ (_ , _ , force≡mix , _) = vis≢mix force≡mix

-- Stop makes no tick step
Stop-no-√ :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R} {x : R}
  → Stop ─[ ev (√ x) ]─► t′
  → ⊥
Stop-no-√ (sRet force≡ret) = case force≡ret of λ ()

-- Stop makes no ev step
-- If nothing ≡ just t', then we can produce ⊥
Stop-no-ev :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
    {e : Event√ E R}
  → Stop ─[ ev e ]─► t′
  → ⊥
Stop-no-ev {e = evl (evLabel _ _ _)} step = Stop-no-evl step
Stop-no-ev {e = √ x}                  step = Stop-no-√  step

-- Stop makes no visible transition
Stop-no-steps : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)} {t′ : ITree E I R}
  → Stop ═⟨ s ⟩═► t′
  → s ≡ []
Stop-no-steps bNil          = refl
Stop-no-steps (bTau τ-step _)  = ⊥-elim (Stop-no-τ τ-step)
Stop-no-steps (bStep ev-step _) = ⊥-elim (Stop-no-ev ev-step)

-- The traces of Stop is empty
Stop-traces-empty : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)}
  → traces {I = I} Stop s
  → s ≡ []
Stop-traces-empty (_ , der) = Stop-no-steps der

{-
Stop-traces-empty : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
    {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} Stop s
  → s ≡ []
Stop-traces-empty {ℓr = ℓr} tr = Stop-traces-empty {R = (⊤ {ℓr})} tr
-}

-- Any ITree refines Stop
⊑ᵀ-Stop : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (t : ITree E I R)
  → t ⊑ᵀ Stop
⊑ᵀ-Stop t (_ , der) with Stop-no-steps der
... | refl = t , bNil

-----------------------------------------------------------------------------------------
-- Terminate and Skip
Ret-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {x : R} {s : List (Event√ E R)}
  → traces {I = I} (Ret x) s
  → s ≡ [] ⊎ s ≡ (√ x ∷ [])
Ret-trace (_ , bNil) = inj₁ refl
Ret-trace (_ , bTau (sSil ()) _)
Ret-trace (_ , bTau (sNdbr () _) _)
Ret-trace (_ , bStep (sRet refl) bNil) = inj₂ refl
Ret-trace (_ , bStep (sRet refl) (bTau (sSil ()) _))
Ret-trace (_ , bStep (sRet refl) (bTau (sNdbr () _) _))
Ret-trace (_ , bStep (sRet refl) (bStep (sRet ()) _))
Ret-trace (_ , bStep (sRet refl) (bStep (sVis refl ()) _))

Skip-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
  {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} Skip s
  → s ≡ [] ⊎ s ≡ (√ tt ∷ [])
Skip-trace tr = Ret-trace tr

-----------------------------------------------------------------------------------------
-- Guard

guard-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi}
    {b : Bool} {s : List (Event√ E (⊤ {ℓr}))}
  → traces {I = I} (guard b) s
  → (b ≡ true  × (s ≡ [] ⊎ s ≡ (√ tt ∷ [])))
  ⊎ (b ≡ false × s ≡ [])

guard-trace {b = true}  tr = inj₁ (refl , Skip-trace tr)
guard-trace {b = false} tr = inj₂ (refl , Stop-traces-empty tr)

-----------------------------------------------------------------------------------------
-- Run

-- √ x is not in the trace of Run
Run-no-Ret : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)} {x : R}
  → traces {I = I} Run s
  → √ x ∉ s
-- Case 1: The trace is empty.
-- We don't care what the resulting ITree is, so we use _ for the first part of the pair.
Run-no-Ret (_ , bNil) ()

-- The Tau case is impossible because Run is a 'vis' node
Run-no-Ret (_ , bTau (sSil ()) _)
Run-no-Ret (_ , bTau (sNdbr () _) _)

-- The step case.
-- 'bStep' proves that Run transitioned to a new state (which is also Run) via a visible event.
Run-no-Ret (._ , bStep (sVis refl refl) step-proof) (here ())
Run-no-Ret (._ , bStep (sVis refl refl) step-proof) (there mem) =
  Run-no-Ret (_ , step-proof) mem

-- Every event in the traces of Run is a visible event.
Run-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)}
  → traces {I = I} Run s
  → ∀ {e} → e ∈ s → ∃ λ (lbl : Event E) → e ≡ evl lbl
Run-trace (_ , bNil) ()

-- By matching on (sVis refl refl), you prove to Agda that:
-- 1. The event is exactly what Run defines.
-- 2. The NEXT state (t') is exactly Run.
Run-trace (._ , bStep (sVis refl refl) big-step) (here refl) =
  _ , refl

-- Now Agda knows 'big-step' has type 'Run ═⟨ tail ⟩═► t''
Run-trace (._ , bStep (sVis refl refl) big-step) (there mem) =
  Run-trace (_ , big-step) mem

-- Handle the impossible Tau case similarly if needed
Run-trace (_ , bTau (sSil ()) _) _

-----------------------------------------------------------------------------------------
-- Run on a subset of events

Run′-trace : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (es : AnyTypes E → Set) (dec : (at : AnyTypes E) → Dec (es at))
  {s : List (Event√ E R)}
  → traces {I = I} (Run′ es dec) s
  → ∀ {e} → e ∈ s → ∃ λ (lbl : Event E) → (e ≡ evl lbl) × (es (Event.A lbl , Event.e lbl))

Run′-trace es dec (_ , bNil) ()
Run′-trace es dec (_ , bTau (sSil ()) _) _
Run′-trace es dec (_ , bStep (sRet ()) _) _
Run′-trace es dec (_ , bStep {el = evl (evLabel A action response)}
                              -- We use refl for eq-force to unify f with the case-logic
                              (sVis {at = at} {a = a} refl eq-just)
                              big-step) mem
  with dec at | mem
-- Branch: No ¬p.
-- Since we matched eq-force with refl, eq-just now has type:
-- (case dec at of ...) ≡ just t'.
-- In this branch, that simplifies to: nothing ≡ just t'.
... | no ¬p      | _         = ⊥-elim (case eq-just of λ ())

-- Branch: Yes p.
-- Here, (case dec at of ...) simplifies to: just (Run' es dec) ≡ just t'.
-- Thus t' is unified with Run' es dec.
... | yes p      | here refl = evLabel A action response , refl , p
... | yes p      | there m   = Run′-trace es dec (_ , subst (λ t → t ═⟨ _ ⟩═► _) t'-eq big-step) m
    where
      -- Extract t' ≡ Run' es dec from (just (Run' es dec) ≡ just t')
      t'-eq : _ ≡ Run′ es dec
      t'-eq with dec at
      ... | yes _ = sym (just-injective eq-just)
      ... | no ¬p = contradiction p ¬p

-----------------------------------------------------------------------------
-- FD lemmas
-- (from CSP.Laws.FailuresDivergences, lines 53–261)
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Stop
-- Stop is stable, refuses every event set, has only the empty failure trace,
-- and never diverges.

Stop-isStable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              → isStable (Stop {E = E} {I = I} {R = R})
Stop-isStable = tt₀

Stop-ref-all : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               (B : Event√ E R → Set ℓB)
             → _ref_ {E = E} {I = I} {R = R} (Stop {E = E} {I = I} {R = R}) B
Stop-ref-all {I = I} {R = R} B =
  ref-stable {E = E} {I = I} {R = R}
             (Stop-isStable {I = I} {R = R})
             (λ e _ step → Stop-no-ev step)

-- Every failure trace of Stop is empty.
Stop-failures-empty : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                       {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
                     → failures {E = E} {I = I} {R = R}
                                (Stop {E = E} {I = I} {R = R}) s B → s ≡ []
Stop-failures-empty (_ , reach , _) = Stop-no-steps reach

¬-Divergent-Stop : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  → ¬ (Divergent {E = E} {I = I} {R = R}
                                 (Stop {E = E} {I = I} {R = R}))
¬-Divergent-Stop d = Stop-no-τ (Divergent.step d)

Stop-no-divergences : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                       {s : List (Event√ E R)}
                     → ¬ divergences {E = E} {I = I} {R = R}
                                     (Stop {E = E} {I = I} {R = R}) s
Stop-no-divergences d = aux (d .IsDivergence.reach) (d .IsDivergence.divwit)
  where
    aux : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {prefix : List (Event√ E R)} {witness : ITree E I R}
        → Stop {E = E} {I = I} {R = R} ═⟨ prefix ⟩═► witness
        → Divergent witness → ⊥
    aux bNil dW = ¬-Divergent-Stop dW
    aux (bTau τ-step _) _ = Stop-no-τ τ-step
    aux (bStep ev-step _) _ = Stop-no-ev ev-step

-- Note: `Stop = deadlock` (definitionally, see CSP.Definitions.Basic_Processes), so all the
-- `Stop-*` lemmas above also serve as `deadlock-*` lemmas — used below for the
-- post-`√` residual of `Ret`.

-----------------------------------------------------------------------------------------
-- Ret x
-- Ret x is unstable (force = ret x). It can only do `ev (√ x)` then deadlock.
-- Failure traces are [] or [√ x]; refusal sets that exclude √ x are refused.
-- Ret x never diverges.

¬-Divergent-Ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} {x : R}
                → ¬ Divergent {E = E} {I = I} {R = R} (Ret {E = E} {I = I} x)
¬-Divergent-Ret d with Divergent.step d
... | sSil ()
... | sNdbr () _

Ret-failures-trace : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                       {x : R} {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
                     → failures {E = E} {I = I} {R = R} (Ret {E = E} {I = I} x) s B
                     → s ≡ [] ⊎ s ≡ √ x ∷ []
Ret-failures-trace (_ , reach , _) = Ret-trace (_ , reach)

Ret-no-divergences : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                      {x : R} {s : List (Event√ E R)}
                    → ¬ divergences {E = E} {I = I} {R = R}
                                    (Ret {E = E} {I = I} x) s
Ret-no-divergences d = aux (d .IsDivergence.reach) (d .IsDivergence.divwit)
  where
    aux : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {x : R} {prefix : List (Event√ E R)} {witness : ITree E I R}
        → Ret {E = E} {I = I} x ═⟨ prefix ⟩═► witness
        → Divergent witness → ⊥
    aux bNil dW = ¬-Divergent-Ret dW
    aux (bTau (sSil ()) _) _
    aux (bTau (sNdbr () _) _) _
    aux (bStep (sRet refl) bNil) dW = ¬-Divergent-Stop dW
    aux (bStep (sRet refl) (bTau τ-step _)) _ = Stop-no-τ τ-step
    aux (bStep (sRet refl) (bStep ev-step _)) _ = Stop-no-ev ev-step
    aux (bStep (sVis () _) _) _

-----------------------------------------------------------------------------------------
-- Skip = Ret tt
-- All Skip lemmas reduce to Ret lemmas at x = tt.

Skip-failures-trace : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi}
                       {s : List (Event√ E (⊤′ {ℓr}))}
                       {B : Event√ E (⊤′ {ℓr}) → Set ℓB}
                     → failures {E = E} {I = I} {R = ⊤′ {ℓr}}
                                (Skip {ℓr = ℓr} {E = E} {I = I}) s B
                     → s ≡ [] ⊎ s ≡ √ tt′ ∷ []
Skip-failures-trace = Ret-failures-trace

Skip-no-divergences : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi}
                       {s : List (Event√ E (⊤′ {ℓr}))}
                     → ¬ divergences {E = E} {I = I} {R = ⊤′ {ℓr}}
                                     (Skip {ℓr = ℓr} {E = E} {I = I}) s
Skip-no-divergences = Ret-no-divergences

-----------------------------------------------------------------------------------------
-- guard b
-- guard true = Skip; guard false = Stop.

guard-failures-trace : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi}
                        {b : Bool} {s : List (Event√ E (⊤′ {ℓr}))}
                        {B : Event√ E (⊤′ {ℓr}) → Set ℓB}
                      → failures {E = E} {I = I} {R = ⊤′ {ℓr}}
                                 (guard {ℓr = ℓr} {E = E} {I = I} b) s B
                      → (b ≡ true  × (s ≡ [] ⊎ s ≡ √ tt′ ∷ []))
                      ⊎ (b ≡ false × s ≡ [])
guard-failures-trace {b = true}  fl = inj₁ (refl , Skip-failures-trace fl)
guard-failures-trace {b = false} fl = inj₂ (refl , Stop-failures-empty fl)

guard-no-divergences : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi}
                        {b : Bool} {s : List (Event√ E (⊤′ {ℓr}))}
                      → ¬ divergences {E = E} {I = I} {R = ⊤′ {ℓr}}
                                      (guard {ℓr = ℓr} {E = E} {I = I} b) s
guard-no-divergences {b = true}  = Skip-no-divergences
guard-no-divergences {b = false} = Stop-no-divergences

-----------------------------------------------------------------------------------------
-- Run
-- `force Run = vis (λ _ _ → just Run)`, so Run is stable, never τ-steps,
-- never tick-steps, and accepts every visible event back to itself.  Every
-- bigstep ends at Run, refusal sets contain no visible event, and Run
-- never diverges.

Run-isStable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             → isStable {E = E} {I = I} {R = R} Run
Run-isStable = tt₀

Run-no-τ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {Q : ITree E I R}
         → Run {E = E} {I = I} {R = R} ─[ τ ]─► Q → ⊥
Run-no-τ tr = τ-from-force-vis-impossible refl tr

Run-no-√ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {x : R} {Q : ITree E I R}
         → Run {E = E} {I = I} {R = R} ─[ ev (√ x) ]─► Q → ⊥
Run-no-√ (sRet eq) = case eq of λ ()

¬-Divergent-Run : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                → ¬ Divergent (Run {E = E} {I = I} {R = R})
¬-Divergent-Run d = Run-no-τ (Divergent.step d)

-- Run accepts every visible event, looping back to itself.
Run-step : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {A : Set ℓ} (e : E A) (a : A)
         → Run {E = E} {I = I} {R = R} ─[ ev (evl (evLabel A e a)) ]─► Run
Run-step {A = A} e a = sVis {at = A , e} {a = a} refl refl

-- A bigstep from Run lands at Run again.
Run-bigstep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {s : List (Event√ E R)} {Q : ITree E I R}
            → Run ═⟨ s ⟩═► Q
            → Q ≡ Run
Run-bigstep bNil = refl
Run-bigstep (bTau τ-step _) = ⊥-elim (Run-no-τ τ-step)
Run-bigstep (bStep {el = √ _} step _) = ⊥-elim (Run-no-√ step)
Run-bigstep (bStep {el = evl _} (sVis refl refl) rest) = Run-bigstep rest

-- Run's refusal sets contain no visible event.
Run-ref-no-vis :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {B : Event√ E R → Set ℓB}
  → Run {E = E} {I = I} {R = R} ref B
  → ∀ {A : Set ℓ} (e : E A) (a : A) → ¬ B (evl (evLabel A e a))
Run-ref-no-vis (ref-tick step _) _ _ _ = Run-no-√ step
Run-ref-no-vis (ref-stable _ noev) e a Bea =
  noev (evl (evLabel _ e a)) Bea (Run-step e a)

-- Converse: if `B` excludes every visible event, then `B` is a refusal of
-- Run.  `ref-tick` is impossible (no `√`-step from Run), and `ref-stable`
-- discharges every visible event via `no-vis`.
ref-Run :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {B : Event√ E R → Set ℓB}
  → (∀ {A : Set ℓ} (e : E A) (a : A) → ¬ B (evl (evLabel A e a)))
  → Run {E = E} {I = I} {R = R} ref B
ref-Run {ℓi = ℓi} {ℓr = ℓr} {I = I} {R = R} {B = B} no-vis =
  ref-stable {P = Run} (Run-isStable {ℓi = ℓi} {ℓr = ℓr} {I = I} {R = R}) noev
  where
    noev : ∀ e → B e → ∀ {Q : ITree E _ _} → ¬ (Run ─[ ev e ]─► Q)
    noev (√ _) _ step = Run-no-√ step
    noev (evl (evLabel _ e a)) Be (sVis refl _) = no-vis e a Be

-- Failure-trace decomposition for Run: every event in `s` is visible, and
-- `B` contains no visible event.
Run-failures-trace :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → failures {I = I} (Run {R = R}) s B
  → (∀ {e : Event√ E R} → e ∈ s → ∃ λ (lbl : Event E) → e ≡ evl lbl)
  × (∀ {A : Set ℓ} (e : E A) (a : A) → ¬ B (evl (evLabel A e a)))
Run-failures-trace (Q , reach , refusal)
  with Run-bigstep reach
... | refl = Run-trace (Q , reach) , Run-ref-no-vis refusal

-- Run never diverges, hence has no divergence traces.
Run-no-divergences :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (Event√ E R)}
  → ¬ divergences {I = I} (Run {R = R}) s
Run-no-divergences d
  with Run-bigstep (d .IsDivergence.reach)
... | refl = ¬-Divergent-Run (d .IsDivergence.divwit)
