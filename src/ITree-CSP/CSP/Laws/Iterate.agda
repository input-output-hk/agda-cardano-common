{-
  Trace lemmas for iter / iter-bind (and downstream loop / loop0 / loopc / while
  once those are extracted).
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (¬_;Dec; yes; no; contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; [_]; length; reverse; map; foldr; downFrom)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; cong)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base using () renaming (tt to tt₀)

open import Class.DecEq using (DecEq; _≟_)
open import Prelude using (to-witness; just-to-witness)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences

module CSP.Laws.Iterate
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces
open Failures

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

import CSP.Definitions.Iterate {ℓ} {ℓe} {E} as CSPIter
open CSPIter E-≟

import CSP.Laws.Bind {ℓ} {ℓe} {E} as CSPBind
open CSPBind E-≟

-----------------------------------------------------------------------------
-- Trace lemmas
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- iter-bind

-- Specifically for iter-bind, similar to bindSplit or iterSplit.
-- Uses direct bigsteps (not Σ-pair traces) so endpoints are pinned and
-- t-final tracks the trace's actual endpoint.  This lets downstream intros
-- (loop-failures-intro etc.) land at a specific endpoint matching the
-- LoopSplit's parameter.
data IterGBindSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
  (t-final : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Case 1: c is still executing.  Bigstep ends at c'; t-final = iter-bind c' body.
  in-c : ∀ {c'} {s : List (Event E)}
       → c ═⟨ map evl s ⟩═► c'
       → t-final ≡ iter-bind c' body
       → IterGBindSplit c body t-final (map evl s)

  -- Case 2: c finished with √(inj₁ a').  iter-bind hands off to iter body a',
  -- whose continuation reaches t-final after s2 events.
  in-loop' : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → s ≡ map evl s1 ++ s2
       → c ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
       → iter body a' ═⟨ s2 ⟩═► t-final
       → IterGBindSplit c body t-final s

  -- Case 3: c finished with √(inj₂ r).  iter-bind terminates at ret r,
  -- whose continuation reaches t-final after s2 events.
  in-done' : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → s ≡ map evl s1 ++ s2
       → c ═⟨ map evl s1 ++ [ √ (inj₂ r) ] ⟩═► deadlock
       → Ret {I = ExtI I} r ═⟨ s2 ⟩═► t-final
       → IterGBindSplit c body t-final s

-- A helper to allow us to induct on the transition directly for iter-bind.
-- Returns IterGBindSplit at the *specific* t-f endpoint (no Σ wrapper) so
-- callers can attach refusals/divergences without endpoint mismatch.
iter-bind-trace-helper : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
   {s : List (Event√ E R)} {t-f : ITree E (ExtI I) R}
   → iter-bind c body ═⟨ s ⟩═► t-f
   → IterGBindSplit c body t-f s

iter-bind-trace-helper c body bNil = in-c bNil refl

iter-bind-trace-helper c body (bTau (sSil {t = next} eq-f) big-step) with c .force in c-eq | eq-f
... | sil c' | refl =
    case iter-bind-trace-helper c' body big-step of λ where
      (in-c c-step eq) → in-c (bTau (sSil c-eq) c-step) eq
      (in-loop' eq-s c-step trk2) → in-loop' eq-s (bTau (sSil c-eq) c-step) trk2
      (in-done' eq-s c-step trk2) → in-done' eq-s (bTau (sSil c-eq) c-step) trk2
... | ret (inj₁ a') | refl =
    in-loop' refl (bStep (sRet c-eq) bNil) big-step
... | ret (inj₂ r) | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()

iter-bind-trace-helper c body (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body big-step of λ where
      (in-c c-step eq) → in-c (bTau (sNdbr c-eq fi-eq) c-step) eq
      (in-loop' eq-s c-step trk2) → in-loop' eq-s (bTau (sNdbr c-eq fi-eq) c-step) trk2
      (in-done' eq-s c-step trk2) → in-done' eq-s (bTau (sNdbr c-eq fi-eq) c-step) trk2
... | nothing | ()

iter-bind-trace-helper c body (bTau (sNdbr eq-f eq-j) big-step) | sil _   | ()
iter-bind-trace-helper c body (bTau (sNdbr eq-f eq-j) big-step) | vis _   | ()
iter-bind-trace-helper c body (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₂ _) | ()

iter-bind-trace-helper c body (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body big-step of λ where
      (in-c {s = sP} c-step eq) →
          in-c {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP}
                (bStep (sVis c-eq fi-eq) c-step) eq
      (in-loop' eq-s c-step trk2) →
          in-loop' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                    (bStep (sVis c-eq fi-eq) c-step) trk2
      (in-done' eq-s c-step trk2) →
          in-done' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                    (bStep (sVis c-eq fi-eq) c-step) trk2
... | nothing | ()

iter-bind-trace-helper c body (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
iter-bind-trace-helper c body (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()
iter-bind-trace-helper c body (bStep (sVis eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body (bStep (sVis eq-f eq-j) big-step) | ret (inj₂ _) | ()

iter-bind-trace-helper c body (bStep (sRet {x = res} eq-f) big-step) with c .force in c-eq | eq-f
... | ret (inj₂ r) | refl =
    in-done' {s1 = []} refl (bStep (sRet c-eq) bNil) (bStep (sRet refl) big-step)
... | ret (inj₁ a') | ()

iter-bind-trace-helper c body (bStep (sRet eq-f) big-step) | sil _        | ()
iter-bind-trace-helper c body (bStep (sRet eq-f) big-step) | vis _        | ()
iter-bind-trace-helper c body (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
iter-bind-trace-helper c body (bStep (sRet eq-f) big-step) | mix _ _      | ()

iter-bind-trace-helper c body (bTau (sMixSlide eq-f) big-step) with c .force in c-eq | eq-f
... | mix _ Qt | refl =
    case iter-bind-trace-helper Qt body big-step of λ where
      (in-c c-step eq) → in-c (bTau (sMixSlide c-eq) c-step) eq
      (in-loop' eq-s c-step trk2) → in-loop' eq-s (bTau (sMixSlide c-eq) c-step) trk2
      (in-done' eq-s c-step trk2) → in-done' eq-s (bTau (sMixSlide c-eq) c-step) trk2
... | sil _        | ()
... | ret (inj₁ _) | ()
... | ret (inj₂ _) | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()

iter-bind-trace-helper c body (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | mix f _ | refl with f at a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body big-step of λ where
      (in-c {s = sP} c-step eq) →
          in-c {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP}
                (bStep (sMixVis c-eq fi-eq) c-step) eq
      (in-loop' eq-s c-step trk2) →
          in-loop' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                    (bStep (sMixVis c-eq fi-eq) c-step) trk2
      (in-done' eq-s c-step trk2) →
          in-done' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                    (bStep (sMixVis c-eq fi-eq) c-step) trk2
... | nothing | ()
iter-bind-trace-helper c body (bStep (sMixVis eq-f eq-j) big-step) | sil _        | ()
iter-bind-trace-helper c body (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₂ _) | ()
iter-bind-trace-helper c body (bStep (sMixVis eq-f eq-j) big-step) | vis _        | ()
iter-bind-trace-helper c body (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-----------------------------------------------------------------------------------------
-- iter

data IterSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A) (t-final : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Direct-bigstep constructors (no Σ-pair traces).  This pins the
  -- bigstep's endpoint visibly so downstream LoopSplit/WhileSplit can
  -- propagate it.

  in-body : ∀ {P'} {s : List (Event E)}
       → (body a) ═⟨ map evl s ⟩═► P'
       → t-final ≡ iter-bind P' body
       → IterSplit body a t-final (map evl s)

  in-loop : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → s ≡ map evl s1 ++ s2
       → (body a) ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
       → (Tau (iter body a')) ═⟨ s2 ⟩═► t-final
       → IterSplit body a t-final s

  in-done : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → s ≡ map evl s1 ++ s2
       → (body a) ═⟨ map evl s1 ++ [ √ (inj₂ r) ] ⟩═► deadlock
       → Ret {I = ExtI I} r ═⟨ s2 ⟩═► t-final
       → IterSplit body a t-final s

iter-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A)
   {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
   → iter body a ═⟨ s ⟩═► Q
   → IterSplit body a Q s

iter-trace body a bNil = in-body bNil refl

iter-trace body a (bTau (sSil {t = next} eq-f) big-step)
    with body a .force in b-eq
... | ret (inj₁ a') with eq-f
...                  | refl  =
    in-loop refl (bStep (sRet b-eq) bNil) (bTau (sSil refl) big-step)

iter-trace body a (bTau (sSil {t = next} eq-f) big-step)
  | ret (inj₂ r) =
    in-done refl (bStep (sRet b-eq) bNil) (bTau (sSil eq-f) big-step)

iter-trace body a (bTau (sSil {t = next} eq-f) big-step)
  | sil c with eq-f
...        | refl =
    case iter-bind-trace-helper c body big-step of λ where
      (in-c c-step eq-P) → in-body (bTau (sSil b-eq) c-step) eq-P
      (in-loop' eq-s c-step k-step) →
          in-loop eq-s (bTau (sSil b-eq) c-step) (bTau (sSil refl) k-step)
      (in-done' eq-s c-step trK) →
          in-done eq-s (bTau (sSil b-eq) c-step) trK

iter-trace body a (bTau (sSil {t = next} eq-f) big-step)
  | vis f = case eq-f of λ ()

iter-trace body a (bTau (sSil {t = next} eq-f) big-step)
  | ndbr f wi wa wp = case eq-f of λ ()

iter-trace body a (bTau (sNdbr {i = i} {a = a'} eq-f eq-j) big-step)
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp with eq-f
...   | refl with f i a' in fi-eq | eq-j
...     | just t' | refl =
        case iter-bind-trace-helper t' body big-step of λ where
          (in-c c-step eq-P) → in-body (bTau (sNdbr b-eq fi-eq) c-step) eq-P
          (in-loop' eq-s c-step k-step) →
              in-loop eq-s
                  (bTau (sNdbr b-eq fi-eq) c-step)
                  (bTau (sSil refl) k-step)
          (in-done' eq-s c-step trK) →
              in-done eq-s (bTau (sNdbr b-eq fi-eq) c-step) trK
...     | nothing | ()

iter-trace body a (bStep (sVis {at = at} {a = a'} eq-f eq-j) big-step)
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()
... | vis f with eq-f
...   | refl with f at a' in fi-eq | eq-j
...     | just t' | refl =
        case iter-bind-trace-helper t' body big-step of λ where
          (in-c {s = sP} c-step eq-P) →
              in-body (bStep (sVis b-eq fi-eq) c-step) eq-P
          (in-loop' eq-s c-step k-step) →
              in-loop (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (bStep (sVis b-eq fi-eq) c-step)
                  (bTau (sSil refl) k-step)
          (in-done' eq-s c-step trK) →
              in-done (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (bStep (sVis b-eq fi-eq) c-step) trK

iter-trace body a (bStep (sRet {x = x} eq-f) big-step)
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   =
    in-done {s1 = []} refl
        (bStep (sRet b-eq) bNil)
        (bStep (sRet eq-f) big-step)
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()
... | mix _ _        = case eq-f of λ ()

iter-trace body a (bTau (sMixSlide eq-f) big-step)
    with body a .force in b-eq
... | mix _ Qt with eq-f
...   | refl =
    case iter-bind-trace-helper Qt body big-step of λ where
      (in-c c-step eq-P) → in-body (bTau (sMixSlide b-eq) c-step) eq-P
      (in-loop' eq-s c-step k-step) →
          in-loop eq-s
              (bTau (sMixSlide b-eq) c-step)
              (bTau (sSil refl) k-step)
      (in-done' eq-s c-step trK) →
          in-done eq-s (bTau (sMixSlide b-eq) c-step) trK
iter-trace body a (bTau (sMixSlide eq-f) big-step) | ret (inj₁ _) = case eq-f of λ ()
iter-trace body a (bTau (sMixSlide eq-f) big-step) | ret (inj₂ _) = case eq-f of λ ()
iter-trace body a (bTau (sMixSlide eq-f) big-step) | sil _        = case eq-f of λ ()
iter-trace body a (bTau (sMixSlide eq-f) big-step) | vis _        = case eq-f of λ ()
iter-trace body a (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ = case eq-f of λ ()

iter-trace body a (bStep (sMixVis {at = at} {a = a'} eq-f eq-j) big-step)
    with body a .force in b-eq
... | mix f _ with eq-f
...   | refl with f at a' in fi-eq | eq-j
...     | just t' | refl =
        case iter-bind-trace-helper t' body big-step of λ where
          (in-c {s = sP} c-step eq-P) →
              in-body (bStep (sMixVis b-eq fi-eq) c-step) eq-P
          (in-loop' eq-s c-step k-step) →
              in-loop (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (bStep (sMixVis b-eq fi-eq) c-step)
                  (bTau (sSil refl) k-step)
          (in-done' eq-s c-step trK) →
              in-done (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (bStep (sMixVis b-eq fi-eq) c-step) trK
...     | nothing | ()
iter-trace body a (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₁ _) = case eq-f of λ ()
iter-trace body a (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₂ _) = case eq-f of λ ()
iter-trace body a (bStep (sMixVis eq-f eq-j) big-step) | sil _        = case eq-f of λ ()
iter-trace body a (bStep (sMixVis eq-f eq-j) big-step) | vis _        = case eq-f of λ ()
iter-trace body a (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ = case eq-f of λ ()

-----------------------------------------------------------------------------------------
-- loop : specialisation of iter for the step `body a >>= λ a' → Ret (inj₁ a')`.

private
  loopStep : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
           → HKTree E (ExtI I) A → A → ITree E (ExtI I) (A ⊎ R)
  loopStep body a = body a >>= λ a' → Ret (inj₁ a')

  whileStep : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
            → (A → Bool) → HKTree E (ExtI I) A → A → ITree E (ExtI I) (A ⊎ A)
  whileStep cond body a = body a >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')

-- LoopSplit specialises IterSplit: the step never returns `inj₂ r`, so there
-- is no `in-done` case.  `in-body` lives inside one body invocation,
-- `in-loop` after the body has signalled completion of one iteration with
-- a witness `√ a'`.
data LoopSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (body : HKTree E (ExtI I) A) (a : A) (t-final : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  -- in-body uses a *direct* bigstep ending at P' (not a Σ-pair traces),
  -- so the bigstep's endpoint matches the eq field's P' (rather than
  -- being a separate existential).  This is essential for downstream
  -- intros to land at a specific endpoint matching t-final.
  in-body : ∀ {P' : ITree E (ExtI I) (A ⊎ R)} {s : List (Event E)}
          → (loopStep {R = R} body a) ═⟨ map evl s ⟩═► P'
          → t-final ≡ iter-bind P' (loopStep {R = R} body)
          → LoopSplit body a t-final (map evl s)
  -- in-loop: loopStep tick ends at deadlock (sRet's destination), then
  -- Tau-loop continuation ends at t-final.  This pins t-final = the
  -- continuation's endpoint, again essential for intros.
  in-loop : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
          → s ≡ map evl s1 ++ s2
          → (loopStep {R = R} body a) ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
          → (Tau (loop {R = R} body a')) ═⟨ s2 ⟩═► t-final
          → LoopSplit body a t-final s

-- WhileSplit, in the same relaxed bind-shaped style as LoopSplit.  cond's
-- result (true/false) is implicit in the inj₁/inj₂ tag of the trace's √.
-- Unlike LoopSplit, the in-done case is reachable (whileStep can return
-- inj₂ when cond a' is false), so we keep all three constructors.
data WhileSplit {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
  (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
  (t-final : ITree E (ExtI I) A)
  : List (Event√ E A) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi) where
  -- Direct bigsteps; same rationale as LoopSplit.
  in-body : ∀ {P' : ITree E (ExtI I) (A ⊎ A)} {s : List (Event E)}
          → (whileStep cond body a) ═⟨ map evl s ⟩═► P'
          → t-final ≡ iter-bind P' (whileStep cond body)
          → WhileSplit cond body a t-final (map evl s)
  in-loop : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E A)} {s}
          → s ≡ map evl s1 ++ s2
          → (whileStep cond body a) ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
          → (Tau (while cond body a')) ═⟨ s2 ⟩═► t-final
          → WhileSplit cond body a t-final s
  in-done : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E A)} {s}
          → s ≡ map evl s1 ++ s2
          → (whileStep cond body a) ═⟨ map evl s1 ++ [ √ (inj₂ a') ] ⟩═► deadlock
          → (Ret {I = ExtI I} a') ═⟨ s2 ⟩═► t-final
          → WhileSplit cond body a t-final s

-- Decompose an equality (xs1 ++ [√ x] ≡ xs2 ++ [√ y]) where xs1, xs2
-- are pure `map evl` lists. Yields xs1 ≡ xs2 (as Event-lists) and x ≡ y.
private
  -- Head extraction for ∷-equality.
  ∷-head-eq : ∀ {ℓα} {A : Set ℓα} {x y : A} {xs ys : List A}
            → x ∷ xs ≡ y ∷ ys → x ≡ y
  ∷-head-eq refl = refl

  ∷-tail-eq : ∀ {ℓα} {A : Set ℓα} {x y : A} {xs ys : List A}
            → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  ∷-tail-eq refl = refl

  -- evl is injective (as a constructor).
  evl-inj : ∀ {ℓα} {α : Set ℓα} {x y : Event E} → evl {R = α} x ≡ evl y → x ≡ y
  evl-inj refl = refl

  evl-tick-eq : ∀ {ℓα} {α : Set ℓα}
              → (xs1 xs2 : List (Event E)) {x y : α}
              → map (evl {R = α}) xs1 ++ [ √ x ] ≡ map (evl {R = α}) xs2 ++ [ √ y ]
              → xs1 ≡ xs2 × x ≡ y
  evl-tick-eq []         []         refl = refl , refl
  evl-tick-eq []         (_ ∷ [])     ()
  evl-tick-eq []         (_ ∷ _ ∷ _)  ()
  evl-tick-eq (_ ∷ [])     []         ()
  evl-tick-eq (_ ∷ _ ∷ _)  []         ()
  evl-tick-eq (e1 ∷ xs1) (e2 ∷ xs2)  eq =
    let head-eq = evl-inj (∷-head-eq eq)
        tail-eq = ∷-tail-eq eq
        (eq-xs , eq-xy) = evl-tick-eq xs1 xs2 tail-eq
    in cong₂ _∷_ head-eq eq-xs , eq-xy
    where open import Relation.Binary.PropositionalEquality using (cong₂)

  -- `√ x` is never in the image of `map evl`.
  no-√-evl : ∀ {ℓr'} {R' : Set ℓr'} {x : R'}
           → (xs ys : List (Event E))
           → map (evl {R = R'}) xs ++ [ √ x ] ≢ map (evl {R = R'}) ys
  no-√-evl []       []       ()
  no-√-evl []       (_ ∷ _)  ()
  no-√-evl (_ ∷ _)  []       ()
  no-√-evl (_ ∷ xs) (_ ∷ ys) eq = no-√-evl xs ys (∷-tail-eq eq)

  inj₁-injective : ∀ {ℓα ℓβ} {A' : Set ℓα} {B : Set ℓβ} {x y : A'}
                 → inj₁ {B = B} x ≡ inj₁ y → x ≡ y
  inj₁-injective refl = refl

  inj₂-vs-inj₁ : ∀ {ℓα ℓβ} {A' : Set ℓα} {B : Set ℓβ} {x : B} {y : A'}
               → inj₂ {A = A'} x ≡ inj₁ {B = B} y → ⊥
  inj₂-vs-inj₁ ()

  -- `map evl` is injective at the Event E level.  Used to bridge the two
  -- `Event√ E X`-typed lists that appear in iter-bind contexts (X = A ⊎ R
  -- inside the bind, X = R outside).
  map-evl-injective : ∀ {ℓr'} {R' : Set ℓr'}
                    → (xs ys : List (Event E))
                    → map (evl {R = R'}) xs ≡ map (evl {R = R'}) ys
                    → xs ≡ ys
  map-evl-injective []       []       refl = refl
  map-evl-injective []       (_ ∷ _)  ()
  map-evl-injective (_ ∷ _)  []       ()
  map-evl-injective (e1 ∷ xs) (e2 ∷ ys) eq =
    let head-eq : e1 ≡ e2
        head-eq = evl-inj (∷-head-eq eq)
        tail-eq : xs ≡ ys
        tail-eq = map-evl-injective xs ys (∷-tail-eq eq)
    in cong₂ _∷_ head-eq tail-eq
    where open import Relation.Binary.PropositionalEquality using (cong₂)

-- loop-trace : eliminate a bigstep of `loop body a` ending at Q into a
-- LoopSplit at endpoint Q.  Direct (no Σ-pair) so refusals at Q transport.
loop-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
   → loop body a ═⟨ s ⟩═► Q
   → LoopSplit body a Q s
loop-trace {I = I} {R = R} body a bs
  with iter-trace (loopStep body) a bs
... | IterSplit.in-body {P' = Pstep} {s = sB} bsB eq =
    in-body {P' = Pstep} {s = sB} bsB eq
... | IterSplit.in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-loopStep trk =
    in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-loopStep trk
loop-trace {ℓi = ℓi} {ℓr = ℓr} {I = I} {A = A} {R = R} body a bs
   | IterSplit.in-done {r = r} {s1 = s1} {s2 = s2} eq-s bs-step tr-ret =
    ⊥-elim (loopStep-never-returns-inj₂ (body a) s1 r bs-step)
  where
    -- loopStep's handler is `λ a' → Ret (inj₁ a')`; a bigstep of the bind
    -- ending in √(inj₂ r') is impossible.  Direct induction on the bigstep
    -- (bypasses bind-trace-helper, which would hit the same `map evl`
    -- unification issue Agda struggles with).  Generalises over P so the
    -- recursive calls work on body sub-states.
    loopStep-never-returns-inj₂
      : (P : ITree E (ExtI I) A)
        (s1' : List (Event E)) (r' : R) {Pe : ITree E (ExtI I) (A ⊎ R)}
      → (P >>= λ a' → Ret (inj₁ a')) ═⟨ map evl s1' ++ [ √ (inj₂ r') ] ⟩═► Pe
      → ⊥

    -- s1' = []: trace = [√(inj₂ r')].  Only sRet matches; analyse P.force.
    loopStep-never-returns-inj₂ P [] r' (bStep (sRet eq-f) bNil)
      with P .force in p-eq | eq-f
    ... | ret _        | ()  -- bind force = ret(inj₁ _) ≠ ret(inj₂ r')
    ... | sil _        | ()
    ... | vis _        | ()
    ... | ndbr _ _ _ _ | ()
    ... | mix _ _      | ()
    loopStep-never-returns-inj₂ P [] r' (bStep (sRet _) (bTau step _)) =
        τ-from-force-vis-impossible refl step

    -- s1' = e ∷ s1'': trace head is evl e.  Visible steps consume it.
    loopStep-never-returns-inj₂ P (_ ∷ s1'')
      r' (bStep (sVis {at = at} {a = a} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
    ... | vis fP | refl with fP at a in fi-eq | eq-j
    ... | just c | refl = loopStep-never-returns-inj₂ c s1'' r' rest
    ... | nothing | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sVis eq-f eq-j) rest)
        | ret _        | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sVis eq-f eq-j) rest)
        | sil _        | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sVis eq-f eq-j) rest)
        | ndbr _ _ _ _ | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sVis eq-f eq-j) rest)
        | mix _ _      | ()

    loopStep-never-returns-inj₂ P (_ ∷ s1'')
      r' (bStep (sMixVis {at = at} {a = a} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
    ... | mix fP _ | refl with fP at a in fi-eq | eq-j
    ... | just c | refl = loopStep-never-returns-inj₂ c s1'' r' rest
    ... | nothing | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sMixVis eq-f eq-j) rest)
        | ret _        | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sMixVis eq-f eq-j) rest)
        | sil _        | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sMixVis eq-f eq-j) rest)
        | vis _        | ()
    loopStep-never-returns-inj₂ P (_ ∷ s1'') r' (bStep (sMixVis eq-f eq-j) rest)
        | ndbr _ _ _ _ | ()

    -- τ-steps: trace unchanged; case-analyze P.force, recurse on body's substate.
    loopStep-never-returns-inj₂ P s1' r' (bTau (sSil {t = next} eq-f) rest)
      with P .force in p-eq | eq-f
    ... | sil c | refl = loopStep-never-returns-inj₂ c s1' r' rest
    ... | ret _        | ()
    ... | vis _        | ()
    ... | ndbr _ _ _ _ | ()
    ... | mix _ _      | ()

    loopStep-never-returns-inj₂ P s1' r' (bTau (sNdbr {i = i} {a = a} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
    ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
    ... | just c | refl = loopStep-never-returns-inj₂ c s1' r' rest
    ... | nothing | ()
    loopStep-never-returns-inj₂ P s1' r' (bTau (sNdbr eq-f eq-j) rest)
        | ret _        | ()
    loopStep-never-returns-inj₂ P s1' r' (bTau (sNdbr eq-f eq-j) rest)
        | sil _        | ()
    loopStep-never-returns-inj₂ P s1' r' (bTau (sNdbr eq-f eq-j) rest)
        | vis _        | ()
    loopStep-never-returns-inj₂ P s1' r' (bTau (sNdbr eq-f eq-j) rest)
        | mix _ _      | ()

    loopStep-never-returns-inj₂ P s1' r' (bTau (sMixSlide eq-f) rest)
      with P .force in p-eq | eq-f
    ... | mix _ Qt-body | refl = loopStep-never-returns-inj₂ Qt-body s1' r' rest
    ... | ret _        | ()
    ... | sil _        | ()
    ... | vis _        | ()
    ... | ndbr _ _ _ _ | ()

-----------------------------------------------------------------------------------------
-- while-trace : pass-through from iter-trace (whileStep cond body).
-- With WhileSplit's relaxed bind-shape, the three IterSplit cases map
-- directly to WhileSplit's three constructors.

while-trace : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {Q : ITree E (ExtI I) A}
   → while cond body a ═⟨ s ⟩═► Q
   → WhileSplit cond body a Q s
while-trace cond body a bs with iter-trace (whileStep cond body) a bs
... | IterSplit.in-body {P' = Pstep} {s = sB} bsB eq =
    in-body {P' = Pstep} {s = sB} bsB eq
... | IterSplit.in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-step trk =
    in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-step trk
... | IterSplit.in-done {r = r} {s1 = s1} {s2 = s2} eq-s bs-step tr-ret =
    in-done {a' = r} {s1 = s1} {s2 = s2} eq-s bs-step tr-ret

-----------------------------------------------------------------------------------------
-- iter-bind force / continuation helpers, lift helpers, and loop-trace-intro.
-- These mirror Bind.agda's bind-force-* / lift-bind-bigstep template.
-- The named continuations themselves live next to iter-bind's definition
-- in CSP.Definitions.Operators so the force clauses reduce to them.
-----------------------------------------------------------------------------------------

-- Continuation reduction lemmas: when the inner continuation returns
-- `just t′`, the iter-bind continuation returns `just (iter-bind t′ k)`.

iter-bind-cont-vis-just : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                        → (k : A → ITree E (ExtI I) (A ⊎ R))
                        → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
                        → (at : AnyTypes E) (a : proj₁ at)
                        → ∀ {t′} → f at a ≡ just t′
                        → iter-bind-cont-vis k f at a ≡ just (iter-bind t′ k)
iter-bind-cont-vis-just k f at a {t′} eq-j with f at a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

iter-bind-cont-ndbr-just : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                         → (k : A → ITree E (ExtI I) (A ⊎ R))
                         → (f : (ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R))))
                         → (ai : AnyTypes (ExtI I)) (a : proj₁ ai)
                         → ∀ {t′} → f ai a ≡ just t′
                         → iter-bind-cont-ndbr k f ai a ≡ just (iter-bind t′ k)
iter-bind-cont-ndbr-just k f ai a {t′} eq-j with f ai a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

iter-bind-cont-mix-just : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                        → (k : A → ITree E (ExtI I) (A ⊎ R))
                        → (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
                        → (at : AnyTypes E) (a : proj₁ at)
                        → ∀ {t′} → f at a ≡ just t′
                        → iter-bind-cont-mix k f at a ≡ just (iter-bind t′ k)
iter-bind-cont-mix-just k f at a {t′} eq-j with f at a
... | just _  = case eq-j of λ { refl → refl }
... | nothing = case eq-j of λ ()

-- Force lemmas for iter-bind.  Each lemma derives `force (iter-bind c k) ≡ …`
-- from the matching `force c ≡ …` (using the iter-bind definition in
-- CSP.Definitions.Operators).

iter-bind-force-sil : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                    → (c : ITree E (ExtI I) (A ⊎ R)) {c′ : ITree E (ExtI I) (A ⊎ R)}
                    → (k : A → ITree E (ExtI I) (A ⊎ R))
                    → ITree.force c ≡ sil c′
                    → ITree.force (iter-bind c k) ≡ sil (iter-bind c′ k)
iter-bind-force-sil c k eq with c .force
... | sil _        = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

iter-bind-force-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                     → (c : ITree E (ExtI I) (A ⊎ R))
                     → {f : (ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) (A ⊎ R)))}
                     → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f wi wa)}
                     → (k : A → ITree E (ExtI I) (A ⊎ R))
                     → ITree.force c ≡ ndbr f wi wa wp
                     → ITree.force (iter-bind c k) ≡ ndbr (iter-bind-cont-ndbr k f) wi wa (iter-bind-cont-ndbr-witness k f wp)
iter-bind-force-ndbr c k eq with c .force
... | ndbr _ _ _ _ = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | mix _ _      = case eq of λ ()

iter-bind-force-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                    → (c : ITree E (ExtI I) (A ⊎ R))
                    → {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
                    → (k : A → ITree E (ExtI I) (A ⊎ R))
                    → ITree.force c ≡ vis f
                    → ITree.force (iter-bind c k) ≡ vis (iter-bind-cont-vis k f)
iter-bind-force-vis c k eq with c .force
... | vis _        = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

iter-bind-force-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                    → (c : ITree E (ExtI I) (A ⊎ R))
                    → {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R)))}
                    → {Qt : ITree E (ExtI I) (A ⊎ R)}
                    → (k : A → ITree E (ExtI I) (A ⊎ R))
                    → ITree.force c ≡ mix f Qt
                    → ITree.force (iter-bind c k) ≡ mix (iter-bind-cont-mix k f) (iter-bind Qt k)
iter-bind-force-mix c k eq with c .force
... | mix _ _      = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()

-- ret-inj₁: when `force c ≡ ret (inj₁ a′)`, iter-bind τ-steps to `iter k a′`.
iter-bind-force-ret-inj₁ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                         → (c : ITree E (ExtI I) (A ⊎ R)) {a′ : A}
                         → (k : A → ITree E (ExtI I) (A ⊎ R))
                         → ITree.force c ≡ ret (inj₁ a′)
                         → ITree.force (iter-bind c k) ≡ sil (iter k a′)
iter-bind-force-ret-inj₁ c k eq with c .force
... | ret (inj₁ _) = case eq of λ { refl → refl }
... | ret (inj₂ _) = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

-- ret-inj₂: when `force c ≡ ret (inj₂ r)`, iter-bind terminates at ret r.
iter-bind-force-ret-inj₂ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
                         → (c : ITree E (ExtI I) (A ⊎ R)) {r : R}
                         → (k : A → ITree E (ExtI I) (A ⊎ R))
                         → ITree.force c ≡ ret (inj₂ r)
                         → ITree.force (iter-bind c k) ≡ ret r
iter-bind-force-ret-inj₂ c k eq with c .force
... | ret (inj₂ _) = case eq of λ { refl → refl }
... | ret (inj₁ _) = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

-----------------------------------------------------------------------------------------
-- lift-iter-bind-bigstep : lift a c-bigstep through iter-bind.
-- Traces here are pure-evl (`map evl s`), so no sRet steps appear.

lift-iter-bind-bigstep
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (k : A → ITree E (ExtI I) (A ⊎ R))
      (s : List (Event E)) {c′ : ITree E (ExtI I) (A ⊎ R)}
    → c ═⟨ map evl s ⟩═► c′
    → iter-bind c k ═⟨ map evl s ⟩═► iter-bind c′ k

lift-iter-bind-bigstep c k [] bNil = bNil

-- τ via sSil
lift-iter-bind-bigstep c k s (bTau (sSil {t = c′} eq-f) rest) =
    bTau (sSil (iter-bind-force-sil c k eq-f)) (lift-iter-bind-bigstep c′ k s rest)

-- τ via sNdbr
lift-iter-bind-bigstep c k s (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                          {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bTau (sNdbr (iter-bind-force-ndbr c k eq-f) (iter-bind-cont-ndbr-just k f i a eq-j))
         (lift-iter-bind-bigstep t′ k s rest)

-- τ via sMixSlide
lift-iter-bind-bigstep c k s (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
    bTau (sMixSlide (iter-bind-force-mix c k eq-f)) (lift-iter-bind-bigstep Qt k s rest)

-- visible step via sVis
lift-iter-bind-bigstep c k (_ ∷ s′) (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bStep (sVis (iter-bind-force-vis c k eq-f) (iter-bind-cont-vis-just k f at a eq-j))
          (lift-iter-bind-bigstep t′ k s′ rest)

-- visible step via sMixVis
lift-iter-bind-bigstep c k (_ ∷ s′) (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bStep (sMixVis (iter-bind-force-mix c k eq-f) (iter-bind-cont-mix-just k f at a eq-j))
          (lift-iter-bind-bigstep t′ k s′ rest)

-----------------------------------------------------------------------------------------
-- lift-iter-bind-bigstep-tick : handles c ending with √(inj₁ a').  After
-- the √, iter-bind takes a τ-step to (iter k a').  Returns the iter-bind
-- state reached after consuming `s1` plus a force-equality showing the
-- iter-bind state is poised to τ-step to (iter k a').

lift-iter-bind-bigstep-tick
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (k : A → ITree E (ExtI I) (A ⊎ R))
      {a′ : A} (s1 : List (Event E)) {c-end : ITree E (ExtI I) (A ⊎ R)}
    → c ═⟨ map evl s1 ++ [ √ (inj₁ a′) ] ⟩═► c-end
    → Σ (ITree E (ExtI I) R) λ P-iter →
        iter-bind c k ═⟨ map evl s1 ⟩═► P-iter
        × ITree.force P-iter ≡ sil (iter k a′)

-- Last step: sRet fires √(inj₁ a′) (s1 = []).
lift-iter-bind-bigstep-tick c k [] (bStep (sRet eq-f) bNil) =
    iter-bind c k , bNil , iter-bind-force-ret-inj₁ c k eq-f
-- After sRet, we are at deadlock which cannot take a τ-step — impossible.
lift-iter-bind-bigstep-tick c k [] (bStep (sRet eq-f) (bTau step _)) =
    ⊥-elim (τ-from-force-vis-impossible refl step)

-- τ via sSil
lift-iter-bind-bigstep-tick c k s1 (bTau (sSil {t = next} eq-f) rest) =
    case lift-iter-bind-bigstep-tick next k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sSil (iter-bind-force-sil c k eq-f)) bs , f-eq

-- τ via sNdbr
lift-iter-bind-bigstep-tick c k s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                                {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick t′ k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sNdbr (iter-bind-force-ndbr c k eq-f)
                                (iter-bind-cont-ndbr-just k f i a eq-j)) bs , f-eq

-- τ via sMixSlide
lift-iter-bind-bigstep-tick c k s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
    case lift-iter-bind-bigstep-tick Qt k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sMixSlide (iter-bind-force-mix c k eq-f)) bs , f-eq

-- visible step via sVis
lift-iter-bind-bigstep-tick c k (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick t′ k s1' rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bStep (sVis (iter-bind-force-vis c k eq-f)
                                (iter-bind-cont-vis-just k f at a eq-j)) bs , f-eq

-- visible step via sMixVis
lift-iter-bind-bigstep-tick c k (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick t′ k s1' rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bStep (sMixVis (iter-bind-force-mix c k eq-f)
                                   (iter-bind-cont-mix-just k f at a eq-j)) bs , f-eq

-----------------------------------------------------------------------------------------
-- loop-trace-intro : reassemble a LoopSplit into a trace of `loop body a`.

loop-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {t-f : ITree E (ExtI I) R}
   → LoopSplit body a t-f s
   → traces (loop body a) s

-- in-body
loop-trace-intro body a (in-body {P' = P'} {s = s} bs-loopStep eq) =
    iter-bind P' (loopStep body) ,
    lift-iter-bind-bigstep (loopStep body a) (loopStep body) s bs-loopStep

-- in-loop: bfe-step gives a continuation bigstep landing at t-f; bfe-nil
-- (s2 = []) means t-f = Tau (loop body a') — a corner case where the
-- Σ-output endpoint (P-iter) has the same force as t-f but isn't visibly
-- equal as ITree.  Callers that need t-f exactly should restrict to the
-- bfe-step case (Tau-loop can't host a refusal anyway, so failures intros
-- aren't hit by bfe-nil).
loop-trace-intro {R = R} body a (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                          eq-s bs-loopStep bs-trk)
  with lift-iter-bind-bigstep-tick (loopStep body a) (loopStep body) s1 bs-loopStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           _ , subst (λ s* → loop body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
...    | bfe-nil refl _   =
           P-iter ,
           subst (λ s* → loop body a ═⟨ s* ⟩═► P-iter)
                 (sym (trans eq-s (++-identityʳ (map evl s1))))
                 bs-s1

-----------------------------------------------------------------------------------------
-- lift-iter-bind-bigstep-tick-done : handles c ending with √(inj₂ r).
-- After the √, iter-bind transitions to ret r (terminating with value r).

lift-iter-bind-bigstep-tick-done
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (k : A → ITree E (ExtI I) (A ⊎ R))
      {r : R} (s1 : List (Event E)) {c-end : ITree E (ExtI I) (A ⊎ R)}
    → c ═⟨ map evl s1 ++ [ √ (inj₂ r) ] ⟩═► c-end
    → Σ (ITree E (ExtI I) R) λ P-iter →
        iter-bind c k ═⟨ map evl s1 ⟩═► P-iter
        × ITree.force P-iter ≡ ret r

-- Last step: sRet fires √(inj₂ r) (s1 = []).
lift-iter-bind-bigstep-tick-done c k [] (bStep (sRet eq-f) bNil) =
    iter-bind c k , bNil , iter-bind-force-ret-inj₂ c k eq-f
lift-iter-bind-bigstep-tick-done c k [] (bStep (sRet eq-f) (bTau step _)) =
    ⊥-elim (τ-from-force-vis-impossible refl step)

-- τ via sSil
lift-iter-bind-bigstep-tick-done c k s1 (bTau (sSil {t = next} eq-f) rest) =
    case lift-iter-bind-bigstep-tick-done next k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sSil (iter-bind-force-sil c k eq-f)) bs , f-eq

-- τ via sNdbr
lift-iter-bind-bigstep-tick-done c k s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                                      {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick-done t′ k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sNdbr (iter-bind-force-ndbr c k eq-f)
                                (iter-bind-cont-ndbr-just k f i a eq-j)) bs , f-eq

-- τ via sMixSlide
lift-iter-bind-bigstep-tick-done c k s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
    case lift-iter-bind-bigstep-tick-done Qt k s1 rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bTau (sMixSlide (iter-bind-force-mix c k eq-f)) bs , f-eq

-- visible step via sVis
lift-iter-bind-bigstep-tick-done c k (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick-done t′ k s1' rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bStep (sVis (iter-bind-force-vis c k eq-f)
                                (iter-bind-cont-vis-just k f at a eq-j)) bs , f-eq

-- visible step via sMixVis
lift-iter-bind-bigstep-tick-done c k (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-iter-bind-bigstep-tick-done t′ k s1' rest of λ where
      (P-iter , bs , f-eq) →
          P-iter , bStep (sMixVis (iter-bind-force-mix c k eq-f)
                                   (iter-bind-cont-mix-just k f at a eq-j)) bs , f-eq

-----------------------------------------------------------------------------------------
-- while-trace-intro : reassemble a WhileSplit into a trace of `while cond body a`.

while-trace-intro : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {t-f : ITree E (ExtI I) A}
   → WhileSplit cond body a t-f s
   → traces (while cond body a) s

-- in-body: still inside whileStep cond body a's execution.
while-trace-intro cond body a (in-body {P' = P'} {s = s} bs-while refl) =
    iter-bind P' (whileStep cond body) ,
    lift-iter-bind-bigstep (whileStep cond body a) (whileStep cond body) s bs-while

-- in-loop: whileStep finished with √(inj₁ a').
while-trace-intro cond body a (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                        eq-s bs-while bs-trk)
  with lift-iter-bind-bigstep-tick (whileStep cond body a) (whileStep cond body) s1 bs-while
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           _ , subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
...    | bfe-nil refl _   =
           P-iter ,
           subst (λ s* → while cond body a ═⟨ s* ⟩═► P-iter)
                 (sym (trans eq-s (++-identityʳ (map evl s1))))
                 bs-s1

-- in-done: whileStep finished with √(inj₂ a').
while-trace-intro cond body a (in-done {a' = a'} {s1 = s1} {s2 = s2}
                                        eq-s bs-while bs-ret)
  with lift-iter-bind-bigstep-tick-done (whileStep cond body a) (whileStep cond body) s1 bs-while
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-ret
...    | bfe-step bs-rest =
           _ , subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
...    | bfe-nil refl _   =
           P-iter ,
           subst (λ s* → while cond body a ═⟨ s* ⟩═► P-iter)
                 (sym (trans eq-s (++-identityʳ (map evl s1))))
                 bs-s1

-----------------------------------------------------------------------------------------
-- loop0 / loopc trace specializations.  Both `loop0 body` and `loopc body`
-- definitionally equal `loop (λ _ → body) tt`, so the trace lemmas reduce
-- to LoopSplit at A := ⊤, a := tt.

Loop0Split : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → ITree E (ExtI I) ⊤ → ITree E (ExtI I) R
           → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Loop0Split body t-final s = LoopSplit (λ _ → body) tt t-final s

loop0-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
   → loop0 body ═⟨ s ⟩═► Q
   → Loop0Split body Q s
loop0-trace body bs = loop-trace (λ _ → body) tt bs

loop0-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {t-f : ITree E (ExtI I) R}
   → Loop0Split body t-f s
   → traces (loop0 body) s
loop0-trace-intro body sp = loop-trace-intro (λ _ → body) tt sp

-- loopc ≡ loop0 definitionally.  Aliases.
LoopcSplit : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → ITree E (ExtI I) ⊤ → ITree E (ExtI I) R
           → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
LoopcSplit = Loop0Split

loopc-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
   → loopc body ═⟨ s ⟩═► Q
   → LoopcSplit body Q s
loopc-trace = loop0-trace

loopc-trace-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {t-f : ITree E (ExtI I) R}
   → LoopcSplit body t-f s
   → traces (loopc body) s
loopc-trace-intro = loop0-trace-intro

-----------------------------------------------------------------------------------------
-- Phase D — Algebraic identities.

-- loop-unfold-T : `loop body a` and `body a >>= λ a' → Tau (loop body a')`
-- have the same set of traces.

-- Forward direction: every trace of the unfolded form is a trace of loop.
loop-unfold-T-fwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   → loop {R = R} body a ⊑ᵀ (body a >>= λ a' → Tau (loop body a'))
loop-unfold-T-fwd {R = R} body a tr-rhs
    with bind-trace (body a) (λ a' → Tau (loop body a')) tr-rhs
... | t-f , in-P {P' = P-end} {s = s'} bs-body refl =
    -- Body is still running.  Lift body's bigstep to loopStep's, then to loop.
    loop-trace-intro body a
       (in-body {P' = P-end >>= λ a' → Ret (inj₁ a')}
                {s = s'}
                (lift-bind-bigstep (body a) (λ a' → Ret (inj₁ a')) s' bs-body)
                refl)
... | t-f , in-k r s1 s2 eq-s (P-end , bs-body-tick) bs-tau
    with lift-bind-bigstep-tick (body a) (λ a' → Ret (inj₁ a')) s1 bs-body-tick
... | P-bind , bs-s1 , f-eq =
    subst (λ s* → traces (loop body a) s*) (sym eq-s)
       (loop-trace-intro {R = R} body a {t-f = t-f}
          (in-loop {a' = r} {s1 = s1} {s2 = s2} refl
                   (bigstep-concat bs-s1 (bStep (sRet f-eq) bNil))
                   bs-tau))

-----------------------------------------------------------------------------------------
-- Body-bigstep extractors for the loop-unfold-T-bwd / FD direction.
-- These bypass the BindSplit unification issue by inducting directly on
-- the bigstep.  Specialized to k = Ret ∘ inj₁ (loopStep's handler) where
-- the handler has only one possible step (sRet); pure-evl bigsteps then
-- can never have body in force=ret state (force=ret would force sRet to
-- fire √, contradicting pure-evl).

private
  -- Pure-evl: body cannot have force=ret throughout (else √ would appear).
  body-pre-pure
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (P : ITree E (ExtI I) A)
        (s : List (Event E)) {Q : ITree E (ExtI I) (A ⊎ R)}
      → (P >>= (λ a' → Ret (inj₁ {B = R} a'))) ═⟨ map evl s ⟩═► Q
      → Σ (ITree E (ExtI I) A) (λ P-end → P ═⟨ map evl s ⟩═► P-end)

  body-pre-pure P [] bNil = P , bNil

  body-pre-pure P s (bTau (sSil {t = next} eq-f) rest) with P .force in p-eq | eq-f
  ... | sil c | refl =
      case body-pre-pure c s rest of λ where
        (P-end , bs) → P-end , bTau (sSil p-eq) bs
  -- body.force ∈ {ret, vis, ndbr, mix} → bind.force ∉ {sil}, so eq-f impossible.
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-pre-pure P s (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                  {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure c s rest of λ where
        (P-end , bs) → P-end , bTau (sNdbr p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure P s (bTau (sNdbr eq-f eq-j) rest) | ret _   | ()
  body-pre-pure P s (bTau (sNdbr eq-f eq-j) rest) | sil _   | ()
  body-pre-pure P s (bTau (sNdbr eq-f eq-j) rest) | vis _   | ()
  body-pre-pure P s (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  body-pre-pure {R = R} P s (bTau (sMixSlide {Qt = Qt} eq-f) rest) with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
      case body-pre-pure {R = R} Qt-body s rest of λ where
        (P-end , bs) → P-end , bTau (sMixSlide p-eq) bs
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  body-pre-pure P (_ ∷ s') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure c s' rest of λ where
        (P-end , bs) → P-end , bStep (sVis p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  body-pre-pure P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  body-pre-pure P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-pre-pure P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  body-pre-pure P (_ ∷ s') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure c s' rest of λ where
        (P-end , bs) → P-end , bStep (sMixVis p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  body-pre-pure P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  body-pre-pure P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-pre-pure P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

  -- For a bigstep of `body >>= Ret-inj₁` ending with √(inj₁ a'), extract
  -- body's bigstep ending with √ a' over the same s1.  At the tick step,
  -- body has body.force = ret a'.
  body-tick-from-loopStep
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (P : ITree E (ExtI I) A) {a′ : A}
        (s1 : List (Event E)) {Q : ITree E (ExtI I) (A ⊎ R)}
      → (P >>= (λ a' → Ret (inj₁ {B = R} a'))) ═⟨ map evl s1 ++ [ √ (inj₁ a′) ] ⟩═► Q
      → Σ (ITree E (ExtI I) A) (λ P-end → P ═⟨ map evl s1 ++ [ √ a′ ] ⟩═► P-end)

  -- Last step: sRet from `body >>= Ret-inj₁`.  Force(body >>= Ret-inj₁) ≡ ret(inj₁ a′).
  -- Body's force must be ret a′ (the only case that makes bind's force = ret).
  body-tick-from-loopStep P [] (bStep (sRet eq-f) bNil)
    with P .force in p-eq | eq-f
  ... | ret _ | refl = deadlock , bStep (sRet p-eq) bNil
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-tick-from-loopStep P [] (bStep (sRet eq-f) (bTau step _)) =
      ⊥-elim (τ-from-force-vis-impossible refl step)

  -- τ via sSil
  body-tick-from-loopStep P s1 (bTau (sSil {t = next} eq-f) rest) with P .force in p-eq | eq-f
  ... | sil c | refl =
      case body-tick-from-loopStep c s1 rest of λ where
        (P-end , bs) → P-end , bTau (sSil p-eq) bs
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-tick-from-loopStep P s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                            {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-loopStep c s1 rest of λ where
        (P-end , bs) → P-end , bTau (sNdbr p-eq fi-eq) bs
  ... | nothing | ()
  body-tick-from-loopStep P s1 (bTau (sNdbr eq-f eq-j) rest) | ret _   | ()
  body-tick-from-loopStep P s1 (bTau (sNdbr eq-f eq-j) rest) | sil _   | ()
  body-tick-from-loopStep P s1 (bTau (sNdbr eq-f eq-j) rest) | vis _   | ()
  body-tick-from-loopStep P s1 (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  body-tick-from-loopStep {R = R} P s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
      case body-tick-from-loopStep {R = R} Qt-body s1 rest of λ where
        (P-end , bs) → P-end , bTau (sMixSlide p-eq) bs
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  body-tick-from-loopStep P (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-loopStep c s1' rest of λ where
        (P-end , bs) → P-end , bStep (sVis p-eq fi-eq) bs
  ... | nothing | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  body-tick-from-loopStep P (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-loopStep c s1' rest of λ where
        (P-end , bs) → P-end , bStep (sMixVis p-eq fi-eq) bs
  ... | nothing | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-loopStep P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

-- Backward direction: every trace of `loop body a` is a trace of the unfolded form.
loop-unfold-T-bwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   → (body a >>= λ a' → Tau (loop {R = R} body a')) ⊑ᵀ loop body a
loop-unfold-T-bwd {R = R} body a {s = s} (Q , reach)
    with loop-trace body a reach
... | in-body {P' = Pstep} {s = sB} bs-loopStep eq =
    case body-pre-pure {R = R} (body a) sB bs-loopStep of λ where
      (P-body , bs-body) →
        bind-trace-intro (body a) (λ a' → Tau (loop body a'))
          (BindSplit.in-P {P' = P-body} {s = sB} bs-body refl)
... | in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-loopStep bs-trk =
    case body-tick-from-loopStep {R = R} (body a) s1 bs-loopStep of λ where
      (P-body-tick-end , bs-body-tick) →
        subst (λ s* → traces (body a >>= λ a'' → Tau (loop body a'')) s*)
              (sym eq-s)
              (bind-trace-intro (body a) (λ a' → Tau (loop body a'))
                 (BindSplit.in-k a' s1 s2 refl
                                 (P-body-tick-end , bs-body-tick)
                                 bs-trk))

-----------------------------------------------------------------------------------------
-- loop0 / loopc / while unfold-T (algebraic identities).

loop0-unfold-T-fwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   → loop0 {R = R} body ⊑ᵀ (body >> Tau (loop0 body))
loop0-unfold-T-fwd body tr-rhs = loop-unfold-T-fwd (λ _ → body) tt tr-rhs

loop0-unfold-T-bwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   → (body >> Tau (loop0 {R = R} body)) ⊑ᵀ loop0 body
loop0-unfold-T-bwd body tr-loop = loop-unfold-T-bwd (λ _ → body) tt tr-loop

-- loopc ≡ loop0 definitionally.
loopc≡loop0 : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   → loopc {R = R} body ≡ loop0 body
loopc≡loop0 body = refl

loopc-unfold-T-fwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   → loopc {R = R} body ⊑ᵀ (body >> Tau (loopc body))
loopc-unfold-T-fwd = loop0-unfold-T-fwd

loopc-unfold-T-bwd : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   → (body >> Tau (loopc {R = R} body)) ⊑ᵀ loopc body
loopc-unfold-T-bwd = loop0-unfold-T-bwd

-- while-unfold-T-fwd: trace of `body a >>= λ a' → if cond a' then Tau …  else Ret a'`
-- is a trace of `while cond body a`.
while-unfold-T-fwd : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   → while cond body a ⊑ᵀ
       (body a >>= λ a' → if cond a' then Tau (while cond body a') else Ret a')
while-unfold-T-fwd cond body a tr-rhs
    with bind-trace (body a) (λ a' → if cond a' then Tau (while cond body a') else Ret a') tr-rhs
... | t-f , in-P {P' = P-end} {s = s'} bs-body refl =
    while-trace-intro cond body a
       (in-body {P' = P-end >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')}
                {s = s'}
                (lift-bind-bigstep (body a)
                       (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')) s' bs-body)
                refl)
... | t-f , in-k r s1 s2 eq-s (P-end , bs-body-tick) bs-handler
    with lift-bind-bigstep-tick (body a)
            (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
            s1 bs-body-tick
... | P-bind , bs-s1 , f-eq with cond r in cr-eq
...    | true  =
    subst (λ s* → traces (while cond body a) s*) (sym eq-s)
       (while-trace-intro cond body a {t-f = t-f}
          (in-loop {a' = r} {s1 = s1} {s2 = s2} refl
                   (bigstep-concat bs-s1 (bStep (sRet f-eq) bNil))
                   bs-handler))
...    | false =
    subst (λ s* → traces (while cond body a) s*) (sym eq-s)
       (while-trace-intro cond body a {t-f = t-f}
          (in-done {a' = r} {s1 = s1} {s2 = s2} refl
                   (bigstep-concat bs-s1 (bStep (sRet f-eq) bNil))
                   bs-handler))

-- body-tick-from-whileStep-inj₁ : like body-tick-from-loopStep but for
-- whileStep's handler.  Final step has body.force = ret a′ AND cond a′ = true.
private
  body-tick-from-whileStep-inj₁
    : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
        (cond : A → Bool) (P : ITree E (ExtI I) A) {a′ : A}
        (s1 : List (Event E)) {Q : ITree E (ExtI I) (A ⊎ A)}
      → (P >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
         ═⟨ map evl s1 ++ [ √ (inj₁ a′) ] ⟩═► Q
      → Σ (ITree E (ExtI I) A)
          (λ P-end → P ═⟨ map evl s1 ++ [ √ a′ ] ⟩═► P-end)
          × cond a′ ≡ true

  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil)
    with P .force in p-eq
  ... | ret r with cond r in cr-eq
  ...   | true with eq-f
  ...     | refl = (deadlock , bStep (sRet p-eq) bNil) , cr-eq
  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil) | ret r | false with eq-f
  ... | ()
  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil) | sil _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil) | vis _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil) | ndbr _ _ _ _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) bNil) | mix _ _ with eq-f
  ... | ()

  body-tick-from-whileStep-inj₁ cond P [] (bStep (sRet eq-f) (bTau step _)) =
      ⊥-elim (τ-from-force-vis-impossible refl step)

  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sSil {t = next} eq-f) rest)
    with P .force in p-eq | eq-f
  ... | sil c | refl =
      case body-tick-from-whileStep-inj₁ cond c s1 rest of λ where
        ((P-end , bs) , ct) → (P-end , bTau (sSil p-eq) bs) , ct
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                                       {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₁ cond c s1 rest of λ where
        ((P-end , bs) , ct) → (P-end , bTau (sNdbr p-eq fi-eq) bs) , ct
  ... | nothing | ()
  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | ret _ | ()
  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | sil _ | ()
  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | vis _ | ()
  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  body-tick-from-whileStep-inj₁ cond P s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
      case body-tick-from-whileStep-inj₁ cond Qt-body s1 rest of λ where
        ((P-end , bs) , ct) → (P-end , bTau (sMixSlide p-eq) bs) , ct
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′}
                                                              eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₁ cond c s1' rest of λ where
        ((P-end , bs) , ct) → (P-end , bStep (sVis p-eq fi-eq) bs) , ct
  ... | nothing | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′}
                                                                 eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₁ cond c s1' rest of λ where
        ((P-end , bs) , ct) → (P-end , bStep (sMixVis p-eq fi-eq) bs) , ct
  ... | nothing | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-whileStep-inj₁ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

  -- Sibling for the in-done case: trace ends in √(inj₂ a′), so cond a′ = false.
  body-tick-from-whileStep-inj₂
    : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
        (cond : A → Bool) (P : ITree E (ExtI I) A) {a′ : A}
        (s1 : List (Event E)) {Q : ITree E (ExtI I) (A ⊎ A)}
      → (P >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
         ═⟨ map evl s1 ++ [ √ (inj₂ a′) ] ⟩═► Q
      → Σ (ITree E (ExtI I) A)
          (λ P-end → P ═⟨ map evl s1 ++ [ √ a′ ] ⟩═► P-end)
          × cond a′ ≡ false

  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil)
    with P .force in p-eq
  ... | ret r with cond r in cr-eq
  ...   | false with eq-f
  ...     | refl = (deadlock , bStep (sRet p-eq) bNil) , cr-eq
  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil) | ret r | true with eq-f
  ... | ()
  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil) | sil _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil) | vis _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil) | ndbr _ _ _ _ with eq-f
  ... | ()
  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) bNil) | mix _ _ with eq-f
  ... | ()

  body-tick-from-whileStep-inj₂ cond P [] (bStep (sRet eq-f) (bTau step _)) =
      ⊥-elim (τ-from-force-vis-impossible refl step)

  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sSil {t = next} eq-f) rest)
    with P .force in p-eq | eq-f
  ... | sil c | refl =
      case body-tick-from-whileStep-inj₂ cond c s1 rest of λ where
        ((P-end , bs) , cf) → (P-end , bTau (sSil p-eq) bs) , cf
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                                       {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₂ cond c s1 rest of λ where
        ((P-end , bs) , cf) → (P-end , bTau (sNdbr p-eq fi-eq) bs) , cf
  ... | nothing | ()
  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | ret _ | ()
  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | sil _ | ()
  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | vis _ | ()
  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  body-tick-from-whileStep-inj₂ cond P s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
      case body-tick-from-whileStep-inj₂ cond Qt-body s1 rest of λ where
        ((P-end , bs) , cf) → (P-end , bTau (sMixSlide p-eq) bs) , cf
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′}
                                                              eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₂ cond c s1' rest of λ where
        ((P-end , bs) , cf) → (P-end , bStep (sVis p-eq fi-eq) bs) , cf
  ... | nothing | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′}
                                                                 eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-tick-from-whileStep-inj₂ cond c s1' rest of λ where
        ((P-end , bs) , cf) → (P-end , bStep (sMixVis p-eq fi-eq) bs) , cf
  ... | nothing | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-tick-from-whileStep-inj₂ cond P (_ ∷ s1') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

  -- body-pre-pure for the while handler.  Identical analysis to body-pre-pure;
  -- the handler's ret-shape is preserved.
  body-pre-pure-while
    : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
        (cond : A → Bool) (P : ITree E (ExtI I) A)
        (s : List (Event E)) {Q : ITree E (ExtI I) (A ⊎ A)}
      → (P >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
         ═⟨ map evl s ⟩═► Q
      → Σ (ITree E (ExtI I) A) (λ P-end → P ═⟨ map evl s ⟩═► P-end)
  body-pre-pure-while cond P [] bNil = P , bNil
  body-pre-pure-while cond P s (bTau (sSil {t = next} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | sil c | refl =
      case body-pre-pure-while cond c s rest of λ where
        (P-end , bs) → P-end , bTau (sSil p-eq) bs
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  body-pre-pure-while cond P s (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                            {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure-while cond c s rest of λ where
        (P-end , bs) → P-end , bTau (sNdbr p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure-while cond P s (bTau (sNdbr eq-f eq-j) rest) | ret _ | ()
  body-pre-pure-while cond P s (bTau (sNdbr eq-f eq-j) rest) | sil _ | ()
  body-pre-pure-while cond P s (bTau (sNdbr eq-f eq-j) rest) | vis _ | ()
  body-pre-pure-while cond P s (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  body-pre-pure-while cond P s (bTau (sMixSlide {Qt = Qt} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
      case body-pre-pure-while cond Qt-body s rest of λ where
        (P-end , bs) → P-end , bTau (sMixSlide p-eq) bs
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  body-pre-pure-while cond P (_ ∷ s') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure-while cond c s' rest of λ where
        (P-end , bs) → P-end , bStep (sVis p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  body-pre-pure-while cond P (_ ∷ s') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl =
      case body-pre-pure-while cond c s' rest of λ where
        (P-end , bs) → P-end , bStep (sMixVis p-eq fi-eq) bs
  ... | nothing | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  body-pre-pure-while cond P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

-- while-unfold-T-bwd: trace of `while cond body a` is a trace of the
-- unfolded form.
while-unfold-T-bwd : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   → (body a >>= λ a' → if cond a' then Tau (while cond body a') else Ret a')
      ⊑ᵀ while cond body a
while-unfold-T-bwd cond body a {s = s} (Q , reach)
    with while-trace cond body a reach
... | in-body {P' = Pstep} {s = sB} bs-whileStep eq =
    case body-pre-pure-while cond (body a) sB bs-whileStep of λ where
      (P-body , bs-body) →
        bind-trace-intro (body a)
          (λ a' → if cond a' then Tau (while cond body a') else Ret a')
          (BindSplit.in-P {P' = P-body} {s = sB} bs-body refl)
... | in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-whileStep bs-trk =
    case body-tick-from-whileStep-inj₁ cond (body a) s1 bs-whileStep of λ where
      ((P-body-tick , bs-body-tick) , cond-true) →
        subst (λ s* → traces (body a >>= λ a'' →
                              if cond a'' then Tau (while cond body a'') else Ret a'') s*)
              (sym eq-s)
              (bind-trace-intro (body a)
                 (λ a'' → if cond a'' then Tau (while cond body a'') else Ret a'')
                 (BindSplit.in-k a' s1 s2 refl
                                 (P-body-tick , bs-body-tick)
                                 (subst (λ b → (if b then Tau (while cond body a') else Ret a')
                                                ═⟨ s2 ⟩═► Q)
                                        (sym cond-true) bs-trk)))
... | in-done {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-whileStep bs-ret =
    case body-tick-from-whileStep-inj₂ cond (body a) s1 bs-whileStep of λ where
      ((P-body-tick , bs-body-tick) , cond-false) →
        subst (λ s* → traces (body a >>= λ a'' →
                              if cond a'' then Tau (while cond body a'') else Ret a'') s*)
              (sym eq-s)
              (bind-trace-intro (body a)
                 (λ a'' → if cond a'' then Tau (while cond body a'') else Ret a'')
                 (BindSplit.in-k a' s1 s2 refl
                                 (P-body-tick , bs-body-tick)
                                 (subst (λ b → (if b then Tau (while cond body a') else Ret a')
                                                ═⟨ s2 ⟩═► Q)
                                        (sym cond-false) bs-ret)))

-----------------------------------------------------------------------------------------
-- Phase E — Failures laws.

-- LoopFailureSplit: a LoopSplit at endpoint Q plus a refusal Q ref B.
-- With direct-bigstep LoopSplit + direct-Q loop-trace, Q is pinned to
-- the input failure's endpoint, so the refusal transports cleanly through
-- loop-trace-intro.
data LoopFailureSplit {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (body : HKTree E (ExtI I) A) (a : A) (B : Event√ E R → Set ℓB)
    : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB) where
  loop-fail : ∀ {Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
            → LoopSplit body a Q s
            → Q ref B
            → LoopFailureSplit body a B s

loop-failures-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures (loop body a) s B
   → LoopFailureSplit body a B s
loop-failures-elim body a (Q , reach , ref) =
    loop-fail (loop-trace body a reach) ref

-- Tau-no-ref: a Tau-shaped state cannot host any refusal.  Used below
-- to discharge the in-loop / bfe-nil corner case structurally instead
-- of via postulate.
private
  Tau-no-ref : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {X : ITree E (ExtI I) R} {B : Event√ E R → Set ℓB}
             → Tau X ref B → ⊥
  Tau-no-ref (ref-stable st _)         = st  -- isStable (Tau X) = ⊥
  Tau-no-ref (ref-tick (sRet ())   _)  -- force(Tau X) = sil ≠ ret

loop-failures-intro : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopFailureSplit body a B s
   → failures (loop body a) s B

-- in-body: LoopSplit's eq makes t-f = iter-bind P' (loopStep body); the
-- lift produces a bigstep ending exactly at this t-f, so ref transports.
loop-failures-intro body a (loop-fail (in-body {P' = P'} {s = s} bs-loopStep refl) ref) =
    iter-bind P' (loopStep body) ,
    lift-iter-bind-bigstep (loopStep body a) (loopStep body) s bs-loopStep ,
    ref

-- in-loop: inline loop-trace-intro's logic.  bigstep-force-eq dispatches:
-- bfe-step → bigstep-concat yields a bigstep at t-f; bfe-nil forces
-- t-f = Tau (loop body a'), so ref is impossible (Tau-no-ref).
loop-failures-intro {R = R} body a
                    (loop-fail (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                         eq-s bs-loopStep bs-trk) ref)
  with lift-iter-bind-bigstep-tick (loopStep body a) (loopStep body) s1 bs-loopStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           _ , subst (λ s* → loop body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
             , ref
...    | bfe-nil refl Tau≡tf =
           ⊥-elim (Tau-no-ref (subst (λ X → _ref_ X _) (sym Tau≡tf) ref))

-- WhileFailureSplit and elim/intro.
data WhileFailureSplit {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
    (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A) (B : Event√ E A → Set ℓB)
    : List (Event√ E A) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓB) where
  while-fail : ∀ {Q : ITree E (ExtI I) A} {s : List (Event√ E A)}
             → WhileSplit cond body a Q s
             → Q ref B
             → WhileFailureSplit cond body a B s

while-failures-elim : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {B : Event√ E A → Set ℓB}
   → failures (while cond body a) s B
   → WhileFailureSplit cond body a B s
while-failures-elim cond body a (Q , reach , ref) =
    while-fail (while-trace cond body a reach) ref

while-failures-intro : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {B : Event√ E A → Set ℓB}
   → WhileFailureSplit cond body a B s
   → failures (while cond body a) s B

-- in-body: like loop's in-body.
while-failures-intro cond body a
                     (while-fail (in-body {P' = P'} {s = s} bs-whileStep refl) ref) =
    iter-bind P' (whileStep cond body) ,
    lift-iter-bind-bigstep (whileStep cond body a) (whileStep cond body) s bs-whileStep ,
    ref

-- in-loop: same dispatch as loop, with Tau-no-ref for bfe-nil.
while-failures-intro cond body a
                     (while-fail (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                          eq-s bs-whileStep bs-trk) ref)
  with lift-iter-bind-bigstep-tick (whileStep cond body a) (whileStep cond body) s1 bs-whileStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           _ , subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
             , ref
...    | bfe-nil refl Tau≡tf =
           ⊥-elim (Tau-no-ref (subst (λ X → _ref_ X _) (sym Tau≡tf) ref))

-- in-done: whileStep finished with √(inj₂ a'); the continuation is `Ret a'`.
-- bfe-nil here yields t-f = Ret a' (force = ret a'), which CAN host a
-- refusal — but only via ref-tick.  Transport that refusal to the
-- bigstep's actual endpoint P-iter (which has the same force ret a').
while-failures-intro {ℓi = ℓi} {I = I} {A = A} cond body a
                     (while-fail (in-done {a' = a'} {s1 = s1} {s2 = s2}
                                          eq-s bs-whileStep bs-ret) ref)
  with lift-iter-bind-bigstep-tick-done (whileStep cond body a) (whileStep cond body) s1 bs-whileStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-ret
...    | bfe-step bs-rest =
           _ , subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                     (sym eq-s)
                     (bigstep-concat bs-s1 bs-rest)
             , ref
...    | bfe-nil refl Ret≡tf =
           P-iter ,
           subst (λ s* → while cond body a ═⟨ s* ⟩═► P-iter)
                 (sym (trans eq-s (++-identityʳ (map evl s1))))
                 bs-s1 ,
           ret-ref-transport f-eq (subst (λ X → _ref_ X _) (sym Ret≡tf) ref)
  where
    -- Transport a refusal at `Ret a'` to any tree with the same force.
    ret-ref-transport : ∀ {ℓB} {Y : ITree E (ExtI I) A} {a′ : A}
                         {B : Event√ E A → Set ℓB}
                     → ITree.force Y ≡ ret a′
                     → _ref_ {ℓB = ℓB} (Ret a′) B
                     → _ref_ {ℓB = ℓB} Y B
    ret-ref-transport _ (ref-stable st _) = ⊥-elim st
    ret-ref-transport f-eqY (ref-tick (sRet refl) ¬Bx) =
        ref-tick (sRet f-eqY) ¬Bx

-- loop0 / loopc failures specializations.
Loop0FailureSplit : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  → ITree E (ExtI I) ⊤ → (Event√ E R → Set ℓB)
                  → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB)
Loop0FailureSplit body B s = LoopFailureSplit (λ _ → body) tt B s

loop0-failures-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures (loop0 body) s B
   → Loop0FailureSplit body B s
loop0-failures-elim body f = loop-failures-elim (λ _ → body) tt f

loop0-failures-intro : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → Loop0FailureSplit body B s
   → failures (loop0 body) s B
loop0-failures-intro body sp = loop-failures-intro (λ _ → body) tt sp

LoopcFailureSplit : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  → ITree E (ExtI I) ⊤ → (Event√ E R → Set ℓB)
                  → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB)
LoopcFailureSplit = Loop0FailureSplit

loopc-failures-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures (loopc body) s B
   → LoopcFailureSplit body B s
loopc-failures-elim = loop0-failures-elim

loopc-failures-intro : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopcFailureSplit body B s
   → failures (loopc body) s B
loopc-failures-intro = loop0-failures-intro

-----------------------------------------------------------------------------------------
-- Phase F — Divergences laws.
-- Same simple-wrapper pattern as Phase E.  An IsDivergence (loop body a) s
-- decomposes into a prefix/suffix split + LoopSplit at the divergent
-- witness + Divergent witness.

data LoopDivergenceSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (body : HKTree E (ExtI I) A) (a : A)
    : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  loop-div : ∀ {Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
             (prefix : List (Event√ E R)) (suffix : List (Event√ E R))
           → s ≡ prefix ++ suffix
           → LoopSplit body a Q prefix
           → Divergent Q
           → LoopDivergenceSplit body a s

loop-divergences-elim : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)}
   → divergences (loop body a) s
   → LoopDivergenceSplit body a s
loop-divergences-elim body a d =
    loop-div (IsDivergence.prefix d) (IsDivergence.suffix d)
             (IsDivergence.split d)
             (loop-trace body a (IsDivergence.reach d))
             (IsDivergence.divwit d)

-- Divergent depends only on the τ-step structure, which depends only on
-- force.  So a divergent witness transports across trees with equal force.
divergent-force-transport : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                            {Y Z : ITree E (ExtI I) R}
                          → ITree.force Y ≡ ITree.force Z
                          → Divergent Z
                          → Divergent Y
divergent-force-transport feq d .Divergent.next    = d .Divergent.next
divergent-force-transport feq d .Divergent.step    = transport-step feq (d .Divergent.step)
  where
    transport-step : ∀ {Y Z t}
                   → ITree.force Y ≡ ITree.force Z
                   → Z ─[ Label.τ ]─► t
                   → Y ─[ Label.τ ]─► t
    transport-step feq (sSil eq-f)       = sSil      (trans feq eq-f)
    transport-step feq (sNdbr eq-f eq-j) = sNdbr     (trans feq eq-f) eq-j
    transport-step feq (sMixSlide eq-f)  = sMixSlide (trans feq eq-f)
divergent-force-transport feq d .Divergent.diverge = d .Divergent.diverge

-- Intro: in-body and bfe-step cases construct directly.  bfe-nil at
-- in-loop has t-f = Tau (loop body a'); the bigstep lands at P-iter,
-- but P-iter and Tau share force = sil (loop body a'), so the
-- divergence transports via divergent-force-transport.
loop-divergences-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)}
   → LoopDivergenceSplit body a s
   → divergences (loop body a) s

loop-divergences-intro body a (loop-div prefix suffix
                                         split-eq
                                         (in-body {P' = P'} {s = sB} bs-loopStep refl)
                                         divwit) =
    record
      { prefix  = prefix
      ; suffix  = suffix
      ; split   = split-eq
      ; witness = iter-bind P' (loopStep body)
      ; reach   = lift-iter-bind-bigstep (loopStep body a) (loopStep body) sB bs-loopStep
      ; divwit  = divwit
      }

loop-divergences-intro {R = R} body a
                       (loop-div prefix suffix split-eq
                                 (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                           eq-s bs-loopStep bs-trk)
                                 divwit)
  with lift-iter-bind-bigstep-tick (loopStep body a) (loopStep body) s1 bs-loopStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           record
             { prefix  = prefix
             ; suffix  = suffix
             ; split   = split-eq
             ; witness = _
             ; reach   = subst (λ s* → loop body a ═⟨ s* ⟩═► _)
                               (sym eq-s)
                               (bigstep-concat bs-s1 bs-rest)
             ; divwit  = divwit
             }
...    | bfe-nil refl Tau≡tf =
           record
             { prefix  = prefix
             ; suffix  = suffix
             ; split   = split-eq
             ; witness = P-iter
             ; reach   = subst (λ s* → loop body a ═⟨ s* ⟩═► P-iter)
                               (sym (trans eq-s (++-identityʳ (map evl s1))))
                               bs-s1
             ; divwit  = divergent-force-transport
                            (trans f-eq (cong ITree.force Tau≡tf))
                            divwit
             }

data WhileDivergenceSplit {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
    (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
    : List (Event√ E A) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi) where
  while-div : ∀ {Q : ITree E (ExtI I) A} {s : List (Event√ E A)}
              (prefix : List (Event√ E A)) (suffix : List (Event√ E A))
            → s ≡ prefix ++ suffix
            → WhileSplit cond body a Q prefix
            → Divergent Q
            → WhileDivergenceSplit cond body a s

while-divergences-elim : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)}
   → divergences (while cond body a) s
   → WhileDivergenceSplit cond body a s
while-divergences-elim cond body a d =
    while-div (IsDivergence.prefix d) (IsDivergence.suffix d)
              (IsDivergence.split d)
              (while-trace cond body a (IsDivergence.reach d))
              (IsDivergence.divwit d)

-- Ret-not-divergent: Ret a' has force = ret a', and no τ-step constructor
-- fires from force = ret (sSil/sNdbr/sMixSlide all require sil/ndbr/mix).
-- So Divergent (Ret a') is absurd.
private
  Ret-not-divergent : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} (a′ : R)
                    → Divergent (Ret {E = E} {I = ExtI I} a′) → ⊥
  Ret-not-divergent a′ d with d .Divergent.step
  ... | sSil ()
  ... | sNdbr () _
  ... | sMixSlide ()

while-divergences-intro : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)}
   → WhileDivergenceSplit cond body a s
   → divergences (while cond body a) s

while-divergences-intro cond body a
                        (while-div prefix suffix split-eq
                                   (in-body {P' = P'} {s = sB} bs-whileStep refl)
                                   divwit) =
    record
      { prefix  = prefix
      ; suffix  = suffix
      ; split   = split-eq
      ; witness = iter-bind P' (whileStep cond body)
      ; reach   = lift-iter-bind-bigstep
                    (whileStep cond body a) (whileStep cond body) sB bs-whileStep
      ; divwit  = divwit
      }

while-divergences-intro cond body a
                        (while-div prefix suffix split-eq
                                   (in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                             eq-s bs-whileStep bs-trk)
                                   divwit)
  with lift-iter-bind-bigstep-tick (whileStep cond body a) (whileStep cond body) s1 bs-whileStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-trk
...    | bfe-step bs-rest =
           record
             { prefix  = prefix
             ; suffix  = suffix
             ; split   = split-eq
             ; witness = _
             ; reach   = subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                               (sym eq-s)
                               (bigstep-concat bs-s1 bs-rest)
             ; divwit  = divwit
             }
...    | bfe-nil refl Tau≡tf =
           record
             { prefix  = prefix
             ; suffix  = suffix
             ; split   = split-eq
             ; witness = P-iter
             ; reach   = subst (λ s* → while cond body a ═⟨ s* ⟩═► P-iter)
                               (sym (trans eq-s (++-identityʳ (map evl s1))))
                               bs-s1
             ; divwit  = divergent-force-transport
                            (trans f-eq (cong ITree.force Tau≡tf))
                            divwit
             }

while-divergences-intro cond body a
                        (while-div prefix suffix split-eq
                                   (in-done {a' = a'} {s1 = s1} {s2 = s2}
                                             eq-s bs-whileStep bs-ret)
                                   divwit)
  with lift-iter-bind-bigstep-tick-done (whileStep cond body a) (whileStep cond body) s1 bs-whileStep
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-ret
...    | bfe-step bs-rest =
           record
             { prefix  = prefix
             ; suffix  = suffix
             ; split   = split-eq
             ; witness = _
             ; reach   = subst (λ s* → while cond body a ═⟨ s* ⟩═► _)
                               (sym eq-s)
                               (bigstep-concat bs-s1 bs-rest)
             ; divwit  = divwit
             }
...    | bfe-nil refl Ret≡tf =
           ⊥-elim (Ret-not-divergent a'
                     (divergent-force-transport (cong ITree.force Ret≡tf) divwit))

-- loop0 / loopc divergences specializations.
Loop0DivergenceSplit : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                     → ITree E (ExtI I) ⊤
                     → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Loop0DivergenceSplit body s = LoopDivergenceSplit (λ _ → body) tt s

loop0-divergences-elim : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)}
   → divergences (loop0 body) s
   → Loop0DivergenceSplit body s
loop0-divergences-elim body d = loop-divergences-elim (λ _ → body) tt d

loop0-divergences-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)}
   → Loop0DivergenceSplit body s
   → divergences (loop0 body) s
loop0-divergences-intro body sp = loop-divergences-intro (λ _ → body) tt sp

LoopcDivergenceSplit : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                     → ITree E (ExtI I) ⊤
                     → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
LoopcDivergenceSplit = Loop0DivergenceSplit

loopc-divergences-elim : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)}
   → divergences (loopc body) s
   → LoopcDivergenceSplit body s
loopc-divergences-elim = loop0-divergences-elim

loopc-divergences-intro : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)}
   → LoopcDivergenceSplit body s
   → divergences (loopc body) s
loopc-divergences-intro = loop0-divergences-intro

-----------------------------------------------------------------------------------------
-- Phase G — failures⊥ laws.  failures⊥ P s B = failures P s B ⊎ divergences P s.

loop-failures⊥-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures⊥ (loop body a) s B
   → LoopFailureSplit body a B s ⊎ LoopDivergenceSplit body a s
loop-failures⊥-elim body a (inj₁ f) = inj₁ (loop-failures-elim body a f)
loop-failures⊥-elim body a (inj₂ d) = inj₂ (loop-divergences-elim body a d)

loop-failures⊥-intro-failures : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopFailureSplit body a B s
   → failures⊥ (loop body a) s B
loop-failures⊥-intro-failures body a sp = inj₁ (loop-failures-intro body a sp)

loop-failures⊥-intro-divergent : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopDivergenceSplit body a s
   → failures⊥ (loop body a) s B
loop-failures⊥-intro-divergent body a sp = inj₂ (loop-divergences-intro body a sp)

while-failures⊥-elim : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {B : Event√ E A → Set ℓB}
   → failures⊥ (while cond body a) s B
   → WhileFailureSplit cond body a B s ⊎ WhileDivergenceSplit cond body a s
while-failures⊥-elim cond body a (inj₁ f) = inj₁ (while-failures-elim cond body a f)
while-failures⊥-elim cond body a (inj₂ d) = inj₂ (while-divergences-elim cond body a d)

while-failures⊥-intro-failures : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {B : Event√ E A → Set ℓB}
   → WhileFailureSplit cond body a B s
   → failures⊥ (while cond body a) s B
while-failures⊥-intro-failures cond body a sp = inj₁ (while-failures-intro cond body a sp)

while-failures⊥-intro-divergent : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) (body : HKTree E (ExtI I) A) (a : A)
   {s : List (Event√ E A)} {B : Event√ E A → Set ℓB}
   → WhileDivergenceSplit cond body a s
   → failures⊥ (while cond body a) s B
while-failures⊥-intro-divergent cond body a sp = inj₂ (while-divergences-intro cond body a sp)

-- loop0 / loopc failures⊥ specializations.
loop0-failures⊥-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures⊥ (loop0 body) s B
   → Loop0FailureSplit body B s ⊎ Loop0DivergenceSplit body s
loop0-failures⊥-elim body f = loop-failures⊥-elim (λ _ → body) tt f

loop0-failures⊥-intro-failures : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → Loop0FailureSplit body B s
   → failures⊥ (loop0 body) s B
loop0-failures⊥-intro-failures body sp = loop-failures⊥-intro-failures (λ _ → body) tt sp

loop0-failures⊥-intro-divergent : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → Loop0DivergenceSplit body s
   → failures⊥ (loop0 body) s B
loop0-failures⊥-intro-divergent body sp = loop-failures⊥-intro-divergent (λ _ → body) tt sp

loopc-failures⊥-elim : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → failures⊥ (loopc body) s B
   → LoopcFailureSplit body B s ⊎ LoopcDivergenceSplit body s
loopc-failures⊥-elim = loop0-failures⊥-elim

loopc-failures⊥-intro-failures : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopcFailureSplit body B s
   → failures⊥ (loopc body) s B
loopc-failures⊥-intro-failures = loop0-failures⊥-intro-failures

loopc-failures⊥-intro-divergent : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   (body : ITree E (ExtI I) ⊤)
   {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
   → LoopcDivergenceSplit body s
   → failures⊥ (loopc body) s B
loopc-failures⊥-intro-divergent = loop0-failures⊥-intro-divergent

-----------------------------------------------------------------------------------------
-- Phase H — ⊑ᵀ monotonicity.

-- Helper: Tau-loop refinement.  From a trace of `Tau (loop body' a)`,
-- produce a trace of `Tau (loop body a)`.  Wraps loop-mono-⊑ᵀ at a.
{-# TERMINATING #-}
loop-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   {body body′ : HKTree E (ExtI I) A}
   → (∀ a → body a ⊑ᵀ body′ a)
   → ∀ a → loop {R = R} body a ⊑ᵀ loop body′ a

loop-mono-⊑ᵀ {body = body} {body′ = body′} body⊑body′ a (Q , reach)
    with loop-trace body′ a reach
... | in-body {P' = P'} {s = sB} bs-loopStep' refl =
    -- Body still running.  Extract body′'s bigstep, apply refinement,
    -- lift to loopStep body, reassemble loop via loop-trace-intro.
    let (P-body′ , bs-body′) = body-pre-pure (body′ a) sB bs-loopStep'
        (P-body  , bs-body)  = body⊑body′ a (P-body′ , bs-body′)
    in loop-trace-intro body a
         (in-body {P' = P-body >>= λ a' → Ret (inj₁ a')}
                  {s = sB}
                  (lift-bind-bigstep (body a) (λ a' → Ret (inj₁ a')) sB bs-body)
                  refl)

loop-mono-⊑ᵀ {body = body} {body′ = body′} body⊑body′ a
             (Q , reach) | in-loop {a' = a'} {s1 = s1} {s2 = s2}
                                    eq-s bs-loopStep' bs-trk' =
    -- Body finished one iteration, then continuation.
    -- 1. Extract body′'s tick at √ a', apply refinement → body's tick.
    -- 2. Build loopStep body's tick (bigstep ending at deadlock) by
    --    extending body's tick through Ret-inj₁ then sRet.
    -- 3. Recurse on bs-trk' (a trace of Tau (loop body′ a')) to get a
    --    trace of Tau (loop body a').  This is the Tau-loop refinement,
    --    which decomposes the leading sSil and recursively applies
    --    loop-mono-⊑ᵀ at a'.
    let (P-body′-tick , bs-body′-tick) =
          body-tick-from-loopStep (body′ a) s1 bs-loopStep'
        (P-body-tick , bs-body-tick) =
          body⊑body′ a (P-body′-tick , bs-body′-tick)
        (P-bind , bs-s1 , f-eq) =
          lift-bind-bigstep-tick (body a) (λ a' → Ret (inj₁ a')) s1 bs-body-tick
        loopStep-body-tick : (body a >>= λ a' → Ret (inj₁ a'))
                              ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
        loopStep-body-tick = bigstep-concat bs-s1 (bStep (sRet f-eq) bNil)
        bs-trk-body : traces (Tau (loop body a')) s2
        bs-trk-body = Tau-loop-mono (_ , bs-trk')
    in subst (λ s* → traces (loop body a) s*) (sym eq-s)
         (loop-trace-intro body a
            (in-loop {a' = a'} {s1 = s1} {s2 = s2} refl
                     loopStep-body-tick
                     (proj₂ bs-trk-body)))
  where
    Tau-loop-mono : traces (Tau (loop body′ a')) s2 → traces (Tau (loop body a')) s2
    Tau-loop-mono (t-fk , bNil) = Tau (loop body a') , bNil
    Tau-loop-mono (t-fk , bTau (sSil refl) bs-loop) =
        let (t-fk′ , bs-loop′) = loop-mono-⊑ᵀ body⊑body′ a' (t-fk , bs-loop)
        in t-fk′ , bTau (sSil refl) bs-loop′
    Tau-loop-mono (t-fk , bTau (sNdbr () _) _)
    Tau-loop-mono (t-fk , bTau (sMixSlide ()) _)
    Tau-loop-mono (t-fk , bStep (sVis () _) _)
    Tau-loop-mono (t-fk , bStep (sRet ()) _)
    Tau-loop-mono (t-fk , bStep (sMixVis () _) _)

{-# TERMINATING #-}
while-mono-⊑ᵀ : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
   (cond : A → Bool) {body body′ : HKTree E (ExtI I) A}
   → (∀ a → body a ⊑ᵀ body′ a)
   → ∀ a → while cond body a ⊑ᵀ while cond body′ a

while-mono-⊑ᵀ cond {body = body} {body′ = body′} body⊑body′ a (Q , reach)
    with while-trace cond body′ a reach
... | in-body {P' = P'} {s = sB} bs-whileStep' refl =
    let (P-body′ , bs-body′) = body-pre-pure-while cond (body′ a) sB bs-whileStep'
        (P-body  , bs-body)  = body⊑body′ a (P-body′ , bs-body′)
    in while-trace-intro cond body a
         (in-body {P' = P-body >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')}
                  {s = sB}
                  (lift-bind-bigstep (body a)
                       (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')) sB bs-body)
                  refl)

while-mono-⊑ᵀ cond {body = body} {body′ = body′} body⊑body′ a (Q , reach)
    | in-loop {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-whileStep' bs-trk' =
    let ((P-body′-tick , bs-body′-tick) , cond-true) =
          body-tick-from-whileStep-inj₁ cond (body′ a) s1 bs-whileStep'
        (P-body-tick , bs-body-tick) =
          body⊑body′ a (P-body′-tick , bs-body′-tick)
        (P-bind , bs-s1 , f-eq-body) =
          lift-bind-bigstep-tick (body a)
            (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')) s1 bs-body-tick
        f-eq : ITree.force P-bind ≡ ret (inj₁ a')
        f-eq = subst (λ b → ITree.force P-bind ≡ ret (if b then inj₁ a' else inj₂ a'))
                     cond-true f-eq-body
        whileStep-body-tick : (body a >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
                               ═⟨ map evl s1 ++ [ √ (inj₁ a') ] ⟩═► deadlock
        whileStep-body-tick = bigstep-concat bs-s1 (bStep (sRet f-eq) bNil)
        bs-trk-body : traces (Tau (while cond body a')) s2
        bs-trk-body = Tau-while-mono (_ , bs-trk')
    in subst (λ s* → traces (while cond body a) s*) (sym eq-s)
         (while-trace-intro cond body a
            (in-loop {a' = a'} {s1 = s1} {s2 = s2} refl
                     whileStep-body-tick
                     (proj₂ bs-trk-body)))
  where
    Tau-while-mono : traces (Tau (while cond body′ a')) s2 → traces (Tau (while cond body a')) s2
    Tau-while-mono (t-fk , bNil) = Tau (while cond body a') , bNil
    Tau-while-mono (t-fk , bTau (sSil refl) bs-loop) =
        let (t-fk′ , bs-loop′) = while-mono-⊑ᵀ cond body⊑body′ a' (t-fk , bs-loop)
        in t-fk′ , bTau (sSil refl) bs-loop′
    Tau-while-mono (t-fk , bTau (sNdbr () _) _)
    Tau-while-mono (t-fk , bTau (sMixSlide ()) _)
    Tau-while-mono (t-fk , bStep (sVis () _) _)
    Tau-while-mono (t-fk , bStep (sRet ()) _)
    Tau-while-mono (t-fk , bStep (sMixVis () _) _)

while-mono-⊑ᵀ cond {body = body} {body′ = body′} body⊑body′ a (Q , reach)
    | in-done {a' = a'} {s1 = s1} {s2 = s2} eq-s bs-whileStep' bs-ret =
    let ((P-body′-tick , bs-body′-tick) , cond-false) =
          body-tick-from-whileStep-inj₂ cond (body′ a) s1 bs-whileStep'
        (P-body-tick , bs-body-tick) =
          body⊑body′ a (P-body′-tick , bs-body′-tick)
        (P-bind , bs-s1 , f-eq-body) =
          lift-bind-bigstep-tick (body a)
            (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')) s1 bs-body-tick
        f-eq : ITree.force P-bind ≡ ret (inj₂ a')
        f-eq = subst (λ b → ITree.force P-bind ≡ ret (if b then inj₁ a' else inj₂ a'))
                     cond-false f-eq-body
        whileStep-body-tick : (body a >>= λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
                               ═⟨ map evl s1 ++ [ √ (inj₂ a') ] ⟩═► deadlock
        whileStep-body-tick = bigstep-concat bs-s1 (bStep (sRet f-eq) bNil)
    in subst (λ s* → traces (while cond body a) s*) (sym eq-s)
         (while-trace-intro cond body a
            (in-done {a' = a'} {s1 = s1} {s2 = s2} refl
                     whileStep-body-tick
                     bs-ret))

loop0-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → body ⊑ᵀ body′
   → loop0 {R = R} body ⊑ᵀ loop0 body′
loop0-mono-⊑ᵀ b⊑b′ = loop-mono-⊑ᵀ (λ _ → b⊑b′) tt

loopc-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
   {body body′ : ITree E (ExtI I) ⊤}
   → body ⊑ᵀ body′
   → loopc {R = R} body ⊑ᵀ loopc body′
loopc-mono-⊑ᵀ = loop0-mono-⊑ᵀ

-----------------------------------------------------------------------------------------
-- Iter-bind failures/divergences elim/intro (foundation for Phase I monos).
--
-- IterBindFailureSplit mirrors BindFailureSplit (from Bind.agda) but for
-- `iter-bind c body` instead of `c >>= k`.  A failure of iter-bind has
-- three structural sources, paralleling IterGBindSplit's three cases:
--
--   1. fail-in-c  : c is still executing at a stable state c'' that
--                   refuses B (events lifted from c's vis-continuation).
--   2. fail-in-loop' : c finished with √(inj₁ a'), then iter body a'
--                      developed a failure on s2.
--   3. fail-in-done' : c finished with √(inj₂ r), then Ret r developed
--                      a failure on s2.
--
-- iter-bind-failures-elim dispatches via iter-bind-trace-helper on the
-- failure's reach, then in each case constructs the corresponding
-- IterBindFailureSplit constructor.  Same `with c .force in p-eq`
-- pattern as bind-failures-elim, plus an extra `iter-bind-cont-vis`
-- step for events refused at iter-bind's vis state.
--
-- Work-in-progress: only the data type is defined here.  The elim/intro
-- functions and the divergence sibling will follow once a Bind-style
-- lift-iter-bind-step-ev and iter-bind-force-vis-inv are in place.

-----------------------------------------------------------------------------------------
-- B-AR : cross-level refusal-predicate lift used by the Phase I monos.
--
-- Failures of `loop body a = iter-bind (body a >>= Ret-inj₁) (body a >>= Ret-inj₁)`
-- live at predicate level `Event√ E R → Set ℓB`, while failures of the body
-- (an `ITree E (ExtI I) (A ⊎ R)`) live at predicate level
-- `Event√ E (A ⊎ R) → Set ℓB`.  The monos must translate the loop-side `B`
-- to a body-side predicate `B-AR B` that:
--
--   * agrees with `B` on visible events (`evl e`), so a body refusal of
--     `evl e` directly underwrites a loop-side refusal;
--   * never refuses a loop-continuation tick `√ (inj₁ _)` (since iter
--     internally absorbs `inj₁ _` ticks as τ-steps into the next iteration),
--     hence `Lift ℓB ⊥` — vacuous, freely passable;
--   * agrees with `B` on done ticks `√ (inj₂ r)` lifted from `√ r`.
--
-- Living at level `ℓB` keeps the predicate compatible with body's `⊑F⊥` /
-- `⊑D`, which the four monos invoke at the same `ℓB`.
B-AR : ∀ {ℓr ℓB} {A : Set ℓ} {R : Set ℓr}
     → (B : Event√ E R → Set ℓB)
     → Event√ E (A ⊎ R) → Set ℓB
B-AR B (evl e)       = B (evl e)
B-AR {ℓB = ℓB} B (√ (inj₁ _)) = Lift ℓB ⊥
B-AR B (√ (inj₂ r))  = B (√ r)

-- B-A : inverse-direction predicate transport (opposite of `B-AR`).
--
-- Converts a bind-side refusal predicate over `Event√ E (A ⊎ R)` to a
-- body-side predicate over `Event√ E A`.  Visible events pass through
-- unchanged; a body tick `√ a` is routed to the inner-bind tick
-- `√ (inj₁ a)` produced by `body a >>= Ret-inj₁`.
--
-- Used by Obstacle 3's failures-side `*-mono-⊑F⊥` discharge: after
-- `B-AR B` lifts the outer loop-level `B` to the inner-bind level,
-- `B-A` lifts further to the body's own level so the hypothesis
-- `bF⊑ a : body a ⊑F⊥ body′ a` can consume it.  Composition behaviour:
-- `B-A (B-AR B) (evl e) = B (evl e)` (visible events propagate) and
-- `B-A (B-AR B) (√ a) = Lift ℓB ⊥` (body ticks become vacuous, since
-- iter absorbs them as τ-steps).
B-A : ∀ {ℓr ℓB} {A : Set ℓ} {R : Set ℓr}
    → (B′ : Event√ E (A ⊎ R) → Set ℓB)
    → Event√ E A → Set ℓB
B-A B′ (evl e) = B′ (evl e)
B-A B′ (√ a)   = B′ (√ (inj₁ a))

-- B-A-h : generalised inverse-direction predicate transport via an
-- arbitrary tag-rewrite `h : A → S`.  Visible events pass through
-- unchanged; a body tick `√ a` is routed to the inner-bind tick
-- `√ (h a)`.  Specialises:
--   * `h = inj₁ : A → A ⊎ R` recovers `B-A` above (used by loopStep).
--   * `h = λ a' → if cond a' then inj₁ a' else inj₂ a'` (used by whileStep).
B-A-h : ∀ {ℓs ℓB} {A : Set ℓ} {S : Set ℓs}
      → (h : A → S)
      → (B′ : Event√ E S → Set ℓB)
      → Event√ E A → Set ℓB
B-A-h h B′ (evl e) = B′ (evl e)
B-A-h h B′ (√ a)   = B′ (√ (h a))

data IterBindFailureSplit {ℓi ℓr ℓB}
    {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (c : ITree E (ExtI I) (A ⊎ R))
    (body : A → ITree E (ExtI I) (A ⊎ R))
    (B : Event√ E R → Set ℓB)
    : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB) where

  -- c executes to a stable state c'' refusing events whose lifts B
  -- forbids at the iter-bind level.
  fail-in-c : ∀ {s : List (Event E)} {c'' : ITree E (ExtI I) (A ⊎ R)}
            → c ═⟨ map evl s ⟩═► c''
            → isStable c''
            → (∀ (e : Event E) {c''' : ITree E (ExtI I) (A ⊎ R)}
                 → B (evl e) → ¬ (c'' ─[ ev (evl e) ]─► c'''))
            → IterBindFailureSplit c body B (map evl s)

  -- c finished with √(inj₁ a') after s1 (visible events); iter body a'
  -- then developed a failure on s2.
  fail-in-loop' : ∀ {s : List (Event√ E R)}
                → (a' : A) (s1 : List (Event E)) (s2 : List (Event√ E R))
                → s ≡ map evl s1 ++ s2
                → traces c (map evl s1 ++ [ √ (inj₁ a') ])
                → failures (iter body a') s2 B
                → IterBindFailureSplit c body B s

  -- c finished with √(inj₂ r) after s1; Ret r then developed a failure on s2.
  -- (Ret r refusing B is non-vacuous only when B doesn't forbid √ r.)
  fail-in-done' : ∀ {s : List (Event√ E R)}
                → (r : R) (s1 : List (Event E)) (s2 : List (Event√ E R))
                → s ≡ map evl s1 ++ s2
                → traces c (map evl s1 ++ [ √ (inj₂ r) ])
                → failures (Ret {I = ExtI I} r) s2 B
                → IterBindFailureSplit c body B s

-- Lift a visible step at c through iter-bind, mirroring lift-bind-step-ev.
lift-iter-bind-step-ev
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (body : A → ITree E (ExtI I) (A ⊎ R))
      {e : Event E} {c' : ITree E (ExtI I) (A ⊎ R)}
    → c ─[ ev (evl e) ]─► c'
    → iter-bind c body ─[ ev (evl e) ]─► iter-bind c' body
lift-iter-bind-step-ev c body (sVis {f = f} {at = at} {a = a} eq-f eq-j) =
    sVis (iter-bind-force-vis c body eq-f) (iter-bind-cont-vis-just body f at a eq-j)
lift-iter-bind-step-ev c body (sMixVis {f = f} {at = at} {a = a} eq-f eq-j) =
    sMixVis (iter-bind-force-mix c body eq-f) (iter-bind-cont-mix-just body f at a eq-j)

-- Inversion: force (iter-bind c body) ≡ ret x  ⇒  force c ≡ ret (inj₂ x).
-- (inj₁ a' would yield sil, vis/sil/ndbr/mix on c would not yield ret.)
iter-bind-force-ret-inv-aux
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {c : ITree E (ExtI I) (A ⊎ R)}
      {body : A → ITree E (ExtI I) (A ⊎ R)} {x : R}
      (nk : NodeKind E (ExtI I) (A ⊎ R)) → ITree.force c ≡ nk
    → ITree.force (iter-bind c body) ≡ ret x
    → ITree.force c ≡ ret (inj₂ x)
iter-bind-force-ret-inv-aux {c = c} {body = body} (ret (inj₂ r)) c-eq eq
    with iter-bind-force-ret-inj₂ c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ { refl → c-eq }
iter-bind-force-ret-inv-aux {c = c} {body = body} (ret (inj₁ a')) c-eq eq
    with iter-bind-force-ret-inj₁ c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
iter-bind-force-ret-inv-aux {c = c} {body = body} (sil _)        c-eq eq
    with iter-bind-force-sil c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
iter-bind-force-ret-inv-aux {c = c} {body = body} (vis _)        c-eq eq
    with iter-bind-force-vis c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
iter-bind-force-ret-inv-aux {c = c} {body = body} (ndbr _ _ _ _) c-eq eq
    with iter-bind-force-ndbr c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
iter-bind-force-ret-inv-aux {c = c} {body = body} (mix _ _)      c-eq eq
    with iter-bind-force-mix c body c-eq
... | f-eq = case trans (sym f-eq) eq of λ ()

iter-bind-force-ret-inv
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (body : A → ITree E (ExtI I) (A ⊎ R)) {x : R}
    → ITree.force (iter-bind c body) ≡ ret x
    → ITree.force c ≡ ret (inj₂ x)
iter-bind-force-ret-inv c body eq =
    iter-bind-force-ret-inv-aux {c = c} {body = body} (c .force) refl eq

-- iter-bind-failures-elim : a failure of (iter-bind c body) splits as
-- one of the three IterBindFailureSplit cases.  Mirrors bind-failures-elim.
iter-bind-failures-elim
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (body : A → ITree E (ExtI I) (A ⊎ R))
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → failures (iter-bind c body) s B
    → IterBindFailureSplit c body B s
iter-bind-failures-elim c body {s = s} {B = B} (Q , reach , ref)
                        with iter-bind-trace-helper c body reach
... | in-loop' {a' = a'} {s1 = s1} {s2 = s2} eq-s tr-tick bs-iter =
      fail-in-loop' a' s1 s2 eq-s (deadlock , tr-tick) (Q , bs-iter , ref)
... | in-done' {r = r} {s1 = s1} {s2 = s2} eq-s tr-tick bs-ret =
      fail-in-done' r s1 s2 eq-s (deadlock , tr-tick) (Q , bs-ret , ref)
iter-bind-failures-elim c body {s = .(map evl s')} {B = B}
                        (Q , reach , ref-stable st no-ev)
                        | in-c {c' = c''} {s = s'} bs-c refl
    with c'' .force in p-eq
... | vis f =
        fail-in-c bs-c (vis-isStable {P = c''} p-eq)
          (λ e {c'''} Be step →
              no-ev (evl e) Be (lift-iter-bind-step-ev c'' body step))
... | ret (inj₁ a') = ⊥-elim st
... | ret (inj₂ r)  = ⊥-elim st
... | sil c''-next  = ⊥-elim st
... | ndbr f wi wa wp = ⊥-elim st
... | mix f Qt      = ⊥-elim st
iter-bind-failures-elim c body {s = .(map evl s')} {B = B}
                        (Q , reach , ref-tick {x = x} step ¬Bx)
                        | in-c {c' = c''} {s = s'} bs-c refl =
    -- (iter-bind c'' body) fires √ x.  Invert to c'' at ret (inj₂ x).
    let force-iter-ret : ITree.force (iter-bind c'' body) ≡ ret x
        force-iter-ret = proj₁ (√-is-ret step)
        c''-ret : ITree.force c'' ≡ ret (inj₂ x)
        c''-ret = iter-bind-force-ret-inv c'' body force-iter-ret
        bs-tick : c ═⟨ map evl s' ++ [ √ (inj₂ x) ] ⟩═► deadlock
        bs-tick = extend-bigstep-tick bs-c c''-ret
        ref-Ret = ref-tick (sRet refl) ¬Bx
    in fail-in-done' x s' [] (sym (++-identityʳ (map evl s')))
                     (deadlock , bs-tick)
                     (Ret x , bNil , ref-Ret)

-- iter-bind-failures-intro : reassemble an IterBindFailureSplit into a
-- failure of (iter-bind c body).  Mirrors bind-failures-intro.
--
-- Case 1 (fail-in-c): c-bigstep lifts through iter-bind via
--   `lift-iter-bind-bigstep`; the residual `iter-bind c'' body` inherits
--   c''-stable's vis-shape, and a refusal at iter-bind is built by
--   inverting an iter-bind step back to a c'' step (see `invert-step`).
-- Case 2 (fail-in-loop'): lift c's tick-bigstep, take one τ-step into
--   `iter body a'` via the f-eq, then concat with bs-iter.
-- Case 3 (fail-in-done'): lift c's tick-done-bigstep, dispatch
--   `bigstep-force-eq` on bs-ret; bfe-nil corner case transports ref via
--   force-equality.
iter-bind-failures-intro
  : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {c : ITree E (ExtI I) (A ⊎ R)}
      {body : A → ITree E (ExtI I) (A ⊎ R)}
      {B : Event√ E R → Set ℓB}
      {s : List (Event√ E R)}
    → IterBindFailureSplit c body B s
    → failures (iter-bind c body) s B

-- Case 1: lift c's bigstep, build refusal on (iter-bind c'' body) by
-- inverting iter-bind steps back to c''.
iter-bind-failures-intro {I = I} {A = A} {R = R} {c = c} {body = body} {B = B}
                         (fail-in-c {s = sB} {c'' = c''} bs-c c''-stable no-ev) =
    iter-bind c'' body ,
    lift-iter-bind-bigstep c body sB bs-c ,
    case-on-stable c''-stable
  where
    case-on-stable : isStable c'' → (iter-bind c'' body) ref B
    case-on-stable st with c'' .force in p-eq
    ... | vis fc'' =
          ref-stable
            (vis-isStable {P = iter-bind c'' body}
                          (iter-bind-force-vis c'' body p-eq))
            (λ e Be step → refusal-on-iter e Be step)
      where
        -- Invert a step on (iter-bind c'' body) back to a step on c''.
        invert-step : ∀ {e : Event√ E R} {t : ITree E (ExtI I) R}
                    → (iter-bind c'' body) ─[ ev e ]─► t
                    → Σ (Event E) λ e' → e ≡ evl e' ×
                         Σ (ITree E (ExtI I) (A ⊎ R)) λ Q' →
                           c'' ─[ ev (evl e') ]─► Q'
        invert-step {e} (sVis {f = f'} {at = at} {a = a} {t′ = tgt} eq-f eq-j) =
            cont-inv (fc'' at a) refl
          where
            f≡icv : f' ≡ iter-bind-cont-vis body fc''
            f≡icv = vis-injective
                      (trans (sym eq-f) (iter-bind-force-vis c'' body p-eq))
            eq-j' : iter-bind-cont-vis body fc'' at a ≡ just tgt
            eq-j' = subst (λ g → g at a ≡ just tgt) f≡icv eq-j
            cont-inv : (m : Maybe (ITree E (ExtI I) (A ⊎ R)))
                     → fc'' at a ≡ m
                     → Σ (Event E) λ e' → e ≡ evl e' ×
                         Σ (ITree E (ExtI I) (A ⊎ R)) λ Q' →
                           c'' ─[ ev (evl e') ]─► Q'
            cont-inv nothing fia-eq =
                ⊥-elim
                  (case trans (sym (cont-vis-nothing fc'' at a fia-eq)) eq-j'
                        of λ ())
              where
                cont-vis-nothing
                  : ∀ (f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (A ⊎ R))))
                      (at : AnyTypes E) (a : proj₁ at)
                    → f at a ≡ nothing
                    → iter-bind-cont-vis body f at a ≡ nothing
                cont-vis-nothing f at a eq-n with f at a
                ... | nothing = refl
                ... | just _  = case eq-n of λ ()
            cont-inv (just t′) fia-eq =
                evLabel (proj₁ at) (proj₂ at) a , refl ,
                t′ , sVis p-eq fia-eq
        invert-step {e} (sMixVis eq-f _) =
            case trans (sym (iter-bind-force-vis c'' body p-eq)) eq-f of λ ()
        invert-step {e} (sRet eq-f) =
            case trans (sym (iter-bind-force-vis c'' body p-eq)) eq-f of λ ()

        refusal-on-iter : ∀ {Q'} (e : Event√ E R)
                        → B e
                        → (iter-bind c'' body) ─[ ev e ]─► Q' → ⊥
        refusal-on-iter e Be step with invert-step step
        ... | e' , refl , Q'' , step-c'' = no-ev e' Be step-c''
    ... | ret (inj₁ _)  = ⊥-elim st
    ... | ret (inj₂ _)  = ⊥-elim st
    ... | sil _         = ⊥-elim st
    ... | ndbr _ _ _ _  = ⊥-elim st
    ... | mix _ _       = ⊥-elim st

-- Case 2: c traces visibly to √(inj₁ a'); iter body a' then fails on s2.
iter-bind-failures-intro {I = I} {R = R} {c = c} {body = body} {B = B}
                         (fail-in-loop' a' s1 s2 eq-s
                                        (_ , tr-tick) (Q , bs-iter , ref))
  with lift-iter-bind-bigstep-tick c body s1 tr-tick
... | P-iter , bs-s1 , f-eq =
      Q ,
      subst (λ s* → iter-bind c body ═⟨ s* ⟩═► Q) (sym eq-s)
            (bigstep-concat bs-s1 (bTau (sSil f-eq) bs-iter)) ,
      ref

-- Case 3: c traces visibly to √(inj₂ r); Ret r then fails on s2.
iter-bind-failures-intro {I = I} {R = R} {c = c} {body = body} {B = B}
                         (fail-in-done' r s1 s2 eq-s
                                        (_ , tr-tick) (Q , bs-ret , ref))
  with lift-iter-bind-bigstep-tick-done c body s1 tr-tick
... | P-iter , bs-s1 , f-eq with bigstep-force-eq f-eq bs-ret
...    | bfe-step bs-rest =
           Q ,
           subst (λ s* → iter-bind c body ═⟨ s* ⟩═► Q) (sym eq-s)
                 (bigstep-concat bs-s1 bs-rest) ,
           ref
...    | bfe-nil refl Ret≡Q =
           P-iter ,
           subst (λ s* → iter-bind c body ═⟨ s* ⟩═► P-iter)
                 (sym (trans eq-s (++-identityʳ (map evl s1))))
                 bs-s1 ,
           ret-ref-transport f-eq (subst (λ X → _ref_ X B) (sym Ret≡Q) ref)
  where
    -- Transport a refusal at Ret r to any tree with the same force.
    ret-ref-transport : ∀ {Y : ITree E (ExtI I) R}
                      → ITree.force Y ≡ ret r
                      → _ref_ (Ret r) B
                      → _ref_ Y B
    ret-ref-transport _ (ref-stable st _) = ⊥-elim st
    ret-ref-transport f-eqY (ref-tick (sRet refl) ¬Bx) =
        ref-tick (sRet f-eqY) ¬Bx

-----------------------------------------------------------------------------------------
-- IterBindDivergenceSplit / iter-bind-divergences-elim.
--
-- Sibling of IterBindFailureSplit / iter-bind-failures-elim for divergences.
-- A divergence of `iter-bind c body` decomposes into one of three sources,
-- mirroring the failures-elim dispatch and Bind.agda's redesigned
-- BindDivergenceSplit (avoiding the unconstructive `div-in-P` shape):
--
--   1. div-in-c     : c visibly traces to some c''; (iter-bind c'' body)
--                     still diverges on the suffix.  Mirrors `bds-tau-after`.
--   2. div-in-loop' : c fires √(inj₁ a') after s1; iter body a' diverges
--                     on the suffix.  Mirrors `bds-handoff`.
--   3. div-in-done' : c fires √(inj₂ r) after s1; Ret r "diverges" on the
--                     suffix.  Included for symmetry with the failures
--                     three-way split; constructively unreachable because
--                     `Ret r` has no τ-step (and therefore is not Divergent),
--                     but the constructor accepts the witness without
--                     forcing the caller to discharge that fact here.
-----------------------------------------------------------------------------------------

data IterBindDivergenceSplit {ℓi ℓr}
    {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
    (c : ITree E (ExtI I) (A ⊎ R))
    (body : A → ITree E (ExtI I) (A ⊎ R))
    : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- c visibly traces through s-plain to c''; (iter-bind c'' body) then
  -- diverges on s2.  Keeps the divergent witness inside iter-bind, exactly
  -- what iter-bind-trace-helper's in-c branch hands us.
  div-in-c : {s : List (Event√ E R)}
           → (s-plain : List (Event E)) (s2 : List (Event√ E R))
           → s ≡ map evl s-plain ++ s2
           → (c'' : ITree E (ExtI I) (A ⊎ R))
           → c ═⟨ map evl s-plain ⟩═► c''
           → divergences (iter-bind c'' body) s2
           → IterBindDivergenceSplit c body s

  -- Hand-off into the loop body: c fires √(inj₁ a') after s1; iter body a'
  -- diverges on s2.
  div-in-loop' : {s : List (Event√ E R)}
               → (a' : A) (s1 : List (Event E)) (s2 : List (Event√ E R))
               → s ≡ map evl s1 ++ s2
               → traces c (map evl s1 ++ [ √ (inj₁ a') ])
               → divergences (iter body a') s2
               → IterBindDivergenceSplit c body s

  -- Hand-off to done: c fires √(inj₂ r); Ret r "diverges" on s2.
  -- (Vacuous in practice — Ret r has no τ-step.)
  div-in-done' : {s : List (Event√ E R)}
               → (r : R) (s1 : List (Event E)) (s2 : List (Event√ E R))
               → s ≡ map evl s1 ++ s2
               → traces c (map evl s1 ++ [ √ (inj₂ r) ])
               → divergences (Ret {I = ExtI I} r) s2
               → IterBindDivergenceSplit c body s

-- iter-bind-divergences-elim : decompose an iter-bind divergence via
-- iter-bind-trace-helper on the divergence's reach.  Each helper-branch
-- maps to the matching constructor of IterBindDivergenceSplit.
iter-bind-divergences-elim
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (c : ITree E (ExtI I) (A ⊎ R))
      (body : A → ITree E (ExtI I) (A ⊎ R))
      {s : List (Event√ E R)}
    → divergences (iter-bind c body) s
    → IterBindDivergenceSplit c body s
iter-bind-divergences-elim c body {s = s} d
    with iter-bind-trace-helper c body (d .IsDivergence.reach)
-- in-loop' branch: c hands off to iter body a' after firing √(inj₁ a').
... | in-loop' {a' = a'} {s1 = s1} {s2 = s2} eq-s tr-tick bs-iter =
      div-in-loop' a' s1
                   (s2 ++ d .IsDivergence.suffix)
                   (trans (d .IsDivergence.split)
                          (trans (cong (_++ d .IsDivergence.suffix) eq-s)
                                 (++-assoc (map evl s1) s2 (d .IsDivergence.suffix))))
                   (deadlock , tr-tick)
                   (record { prefix  = s2
                           ; suffix  = d .IsDivergence.suffix
                           ; split   = refl
                           ; witness = d .IsDivergence.witness
                           ; reach   = bs-iter
                           ; divwit  = d .IsDivergence.divwit })
  where open import Data.List.Properties using (++-assoc)
-- in-done' branch: c hands off to Ret r after firing √(inj₂ r).  Vacuous
-- (Ret r is non-Divergent), but constructed for symmetry.
... | in-done' {r = r} {s1 = s1} {s2 = s2} eq-s tr-tick bs-ret =
      div-in-done' r s1
                   (s2 ++ d .IsDivergence.suffix)
                   (trans (d .IsDivergence.split)
                          (trans (cong (_++ d .IsDivergence.suffix) eq-s)
                                 (++-assoc (map evl s1) s2 (d .IsDivergence.suffix))))
                   (deadlock , tr-tick)
                   (record { prefix  = s2
                           ; suffix  = d .IsDivergence.suffix
                           ; split   = refl
                           ; witness = d .IsDivergence.witness
                           ; reach   = bs-ret
                           ; divwit  = d .IsDivergence.divwit })
  where open import Data.List.Properties using (++-assoc)
-- in-c branch: divergence stays inside (iter-bind c'' body) after the
-- visible reach.  Keep the witness there; do not try to lift to Divergent c.
... | in-c {c' = c''} {s = s-plain} bs-c refl =
      div-in-c s-plain
               (d .IsDivergence.suffix)
               (d .IsDivergence.split)
               c''
               bs-c
               (record { prefix  = []
                       ; suffix  = d .IsDivergence.suffix
                       ; split   = refl
                       ; witness = iter-bind c'' body
                       ; reach   = bNil
                       ; divwit  = d .IsDivergence.divwit })

-----------------------------------------------------------------------------------------
-- iter-bind-divergences-intro : reassemble an IterBindDivergenceSplit into
-- a divergence of (iter-bind c body).  Mirrors iter-bind-failures-intro.
--
-- Case 1 (div-in-c)     : lift the c-bigstep through iter-bind via
--                         `lift-iter-bind-bigstep`; concat with the residual
--                         IsDivergence at (iter-bind c'' body).
-- Case 2 (div-in-loop') : lift c's tick-bigstep, take one τ-step into
--                         (iter body a') via the f-eq, then concat with the
--                         residual IsDivergence at (iter body a').
-- Case 3 (div-in-done') : vacuous — Ret r is non-divergent.  Discharge via
--                         a small inline absurdity on the divergence at Ret r.
iter-bind-divergences-intro
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {c : ITree E (ExtI I) (A ⊎ R)}
      {body : A → ITree E (ExtI I) (A ⊎ R)}
      {s : List (Event√ E R)}
    → IterBindDivergenceSplit c body s
    → divergences (iter-bind c body) s

-- Case 1: c traces visibly to c''; iter-bind c'' body then diverges on s2.
iter-bind-divergences-intro {I = I} {R = R} {c = c} {body = body}
                            (div-in-c s-plain s2 eq-s c'' bs-c d'') =
    record
      { prefix  = map evl s-plain ++ d'' .IsDivergence.prefix
      ; suffix  = d'' .IsDivergence.suffix
      ; split   = trans eq-s
                    (trans (cong (map evl s-plain ++_) (d'' .IsDivergence.split))
                           (sym (++-assoc (map evl s-plain)
                                          (d'' .IsDivergence.prefix)
                                          (d'' .IsDivergence.suffix))))
      ; witness = d'' .IsDivergence.witness
      ; reach   = bigstep-concat
                    (lift-iter-bind-bigstep c body s-plain bs-c)
                    (d'' .IsDivergence.reach)
      ; divwit  = d'' .IsDivergence.divwit
      }
  where open import Data.List.Properties using (++-assoc)

-- Case 2: c traces visibly to √(inj₁ a'); iter body a' then diverges on s2.
iter-bind-divergences-intro {I = I} {R = R} {c = c} {body = body}
                            (div-in-loop' a' s1 s2 eq-s
                                          (_ , tr-tick) d-iter)
  with lift-iter-bind-bigstep-tick c body s1 tr-tick
... | P-iter , bs-s1 , f-eq =
      record
        { prefix  = map evl s1 ++ d-iter .IsDivergence.prefix
        ; suffix  = d-iter .IsDivergence.suffix
        ; split   = trans eq-s
                      (trans (cong (map evl s1 ++_) (d-iter .IsDivergence.split))
                             (sym (++-assoc (map evl s1)
                                            (d-iter .IsDivergence.prefix)
                                            (d-iter .IsDivergence.suffix))))
        ; witness = d-iter .IsDivergence.witness
        ; reach   = bigstep-concat bs-s1
                      (bTau (sSil f-eq) (d-iter .IsDivergence.reach))
        ; divwit  = d-iter .IsDivergence.divwit
        }
  where open import Data.List.Properties using (++-assoc)

-- Case 3: c traces visibly to √(inj₂ r); Ret r then "diverges" on s2.
-- Vacuous: Ret r has no τ-step, so it (and everything reachable from it via
-- the only available step `sRet` into deadlock) cannot host a Divergent.
iter-bind-divergences-intro {I = I} {R = R} {c = c} {body = body}
                            (div-in-done' r s1 s2 eq-s
                                          (_ , tr-tick) d-ret) =
    ⊥-elim (Ret-divergent-impossible (d-ret .IsDivergence.reach)
                                     (d-ret .IsDivergence.divwit))
  where
    -- A Divergent witness reachable from `Ret r` is absurd: the only
    -- bigsteps from `Ret r` end at `Ret r` (bNil) or `deadlock` (after
    -- sRet), neither of which can take a τ-step.
    Ret-divergent-impossible
      : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} {r : R}
          {s : List (Event√ E R)} {Q : ITree E (ExtI I) R}
      → Ret {I = ExtI I} r ═⟨ s ⟩═► Q
      → Divergent Q → ⊥
    Ret-divergent-impossible bNil dv =
        no-τ-from-ret refl (dv .Divergent.step)
    Ret-divergent-impossible (bTau τ-step _) _ =
        no-τ-from-ret refl τ-step
    Ret-divergent-impossible (bStep (sRet _) rest) dv =
        no-τ-from-deadlock-bigstep rest (dv .Divergent.step)
    Ret-divergent-impossible (bStep (sVis eq-f _) _) _ =
        case eq-f of λ ()
    Ret-divergent-impossible (bStep (sMixVis eq-f _) _) _ =
        case eq-f of λ ()

-----------------------------------------------------------------------------------------
-- Phase I — ⊑F⊥ / ⊑D / ⊑FD monotonicity.
--
-- Discharge sketch (recipe documented; full proof deferred):
--   * Use `iter-bind-{failures,divergences}-elim` to decompose Q-side
--     failure⊥ / divergence on `loop body′ a` = `iter-bind (loopStep body′ a)
--     (loopStep body′)` into its three constructors.
--   * `fail-in-loop'` / `div-in-loop'` : recurse on s2 via `loop-mono-⊑F⊥`
--     / `loop-mono-⊑D` at a' (same `{-# TERMINATING #-}` pattern as
--     `loop-mono-⊑ᵀ`), wiring the body's tick via `body-tick-from-loopStep`
--     and re-lift via `bind-trace-helper` to translate body′'s tick to
--     body's tick under `body⊑F⊥`.
--   * `fail-in-c` / `div-in-c` : bridge the c''-side stable refusal
--     (resp. divergence in iter-bind c'' body′) to a body-side
--     refusal/divergence via `bind-failures-elim`/`bind-divergences-elim`
--     on `loopStep body′ a = body′ a >>= Ret-inj₁`.  The `BindFailureSplit
--     fail-in-k` corner case is structurally absurd because c'' is
--     vis-shaped while Ret-inj₁ r has ret-shape.  Cross-level: the
--     input B : Event√ E R → Set ℓB lifts to B-AR : Event√ E (A ⊎ R)
--     → Set ℓB via `evl`-agreement and `Lift ⊥` on √-events; the lift
--     leaves `bind-failures-intro` invariant on the `fail-in-P` branch.
--   * `fail-in-done'` (loop only) : vacuous via `loopStep-never-returns-inj₂`
--     (private to `loop-trace`'s where-clause; re-derivable inline).
--   * For `while`, `fail-in-done'` / `div-in-done'` are reachable when
--     `cond a' = false`: handle symmetrically to `fail-in-loop'` but
--     with the `Ret a'` residual instead of `loop body′ a'`.
--
-- The iter-bind-{failures,divergences}-{elim,intro} foundation needed
-- here is in place (Phase I prerequisites, just above).  Discharging
-- the four monos in full requires:
--   * Two bind-mono lemmas for the pure-continuation special case
--     (`loopStep`-mono / `whileStep`-mono at ⊑F⊥ / ⊑D).
--   * Cross-level B-AR lifts (refusal predicate transport).
--   * Inversions for the structural absurdities (mainly
--     `loopStep-never-returns-inj₂`).
-- Estimated ~400 LOC; deferred to a focused follow-up session per the
-- plan document.

-----------------------------------------------------------------------------------------
-- Phase I.0 — bind-mono helpers for the pure-Ret continuations used by
-- `loopStep` and `whileStep`.
--
-- These four helpers say: if `body ⊑F⊥/⊑D body′` pointwise, then the
-- bind-extended `loopStep body / whileStep body` refines `loopStep body′
-- / whileStep body′` in the same order.  The continuations are pure-Ret
-- (`λ a' → Ret (inj₁ a')` for loopStep, and a conditional Ret for
-- whileStep), so this is the special case `(body a >>= k) ⊑ (body′ a >>= k)`
-- for a fixed pure-Ret `k`.
--
-- Discharge sketch (recipe; the fully discharged proofs descend into
-- `bind-{failures,divergences}-{elim,intro}` plus a small Ret-continuation
-- divergence inversion).  The structure of each ⊑F⊥ proof is:
--
--   * Decompose the body′-side failure⊥ via `bind-failures-elim` /
--     `bind-divergences-elim`.
--
--   * `fail-in-P bs-P′ stable no-ev` : direct body′ failure.
--     Build `failures⊥ (body′ a) (map evl s) B = inj₁ (P'' , bs-P′ ,
--     ref-stable stable no-ev)`, route through `bF⊑ a`, then sub-split
--     the result on inj₁/inj₂.  In the inj₁ sub-case rebuild via
--     `bind-failures-intro (fail-in-P …)` on the body side; in the
--     inj₂ sub-case rebuild via `bind-divergences-intro (bds-tau-after
--     [] s refl (body a) bNil <inner>)` where `<inner>` requires a
--     trivial lift of a body-side `Divergent` into `(body a >>= k)`-side
--     `Divergent` (Divergent-bind-left).
--
--   * `fail-in-k r s1 s2 eq-s tr-tick fl-kr` : body′ fires √ then
--     k r refuses.  k r = Ret(h r) is structurally rigid: by inversion
--     fl-kr is either a stable refusal of `Ret(h r)` (which can only
--     happen via `ref-tick` since Ret has no vis) or absurd.
--     Build a body′-failure⊥ from `tr-tick : traces (body′ a) (s1 ++ [√r])`
--     using a `ref-stable` on `deadlock` (the bigstep ends at deadlock
--     by `extend-bigstep-tick`); route through `bF⊑ a`; rebuild a
--     body-side bigstep to deadlock and re-emit via `fail-in-k` (with
--     the same fl-kr — fl-kr lives at the bound level, B-side, and is
--     orthogonal to the body switch).
--
--   * Divergence branch via `bind-divergences-elim`:
--
--     * `bds-handoff r s1 s2 eq-s tr-tick dv-kr` : dv-kr is a divergence
--       of Ret(h r), which is absurd (via `Ret-divergent-impossible` —
--       no τ from `ret`).
--
--     * `bds-tau-after s-plain s2 eq P'' bs-P d-inner` : the residual
--       divergence is inside `(P'' >>= k)`.  Invert via
--       `bind-pure-ret-divergences-inv` (postulated below — the genuine
--       obstacle, see its doc) to get `divergences P'' s2'` and from
--       this build `divergences (body′ a) (map evl s-plain ++ s2')`.
--       Route through `bF⊑ a` (via `inj₂ d-body′`) to get the body-side
--       divergence; rebuild as `bds-tau-after` on the body side.
--
-- For `⊑D` variants: same structure, only the divergence branch.
--
-- The proofs are mechanical given the inversion `bind-pure-ret-divergences-inv`
-- below.  Pending that single coinductive inversion, the four helpers
-- are themselves postulated here to unblock Phase I.1–I.4 (which depend
-- on them as black boxes).
--
-- Genuine obstacle, documented:
--
--   `bind-pure-ret-divergences-inv` requires showing that a divergence
--   of `P >>= λ a → Ret (h a)` factors as a divergence of P at a
--   corresponding trace.  The continuation `λ a → Ret (h a)` produces
--   no τ-outgoing from `ret r` (since `Ret (h a)` has force `ret (h a)`
--   whose only outgoing is `sRet` into `deadlock`, no `sSil`/`sNdbr`/
--   `sMixSlide`).  Hence in `(P >>= λ a → Ret (h a)).force`'s τ-loop,
--   each τ-step must descend through `>>=` via a τ-step of P (the
--   k-side is τ-quiescent).  Proving this constructively requires a
--   coinductive inversion of `Divergent (P >>= k)` to `Divergent P`,
--   in the special case `k = λ a → Ret (h a)`.  This is routine but
--   non-trivial coinductive bookkeeping; postulated here.

private
  -- Single-step inversion through `>>= (λ r → Ret (h r))`.  The pure-Ret
  -- continuation is τ-quiescent (force (Ret x) ≡ ret x has no sil/ndbr/
  -- mix outgoing), so every τ-step of (Q >>= k) must come from a τ-step
  -- of Q itself.  We pinpoint the Q-side step and the residual
  -- Divergent of (Q' >>= k) so the caller can recurse coinductively.
  bind-pure-ret-step-inv
    : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        (Q : ITree E (ExtI I) R) (h : R → S)
        {T : ITree E (ExtI I) S}
      → (Q >>= λ r → Ret (h r)) ─[ τ ]─► T
      → Divergent T
      → Σ (ITree E (ExtI I) R) λ Q' →
          (Q ─[ τ ]─► Q') × Divergent (Q' >>= λ r → Ret (h r))
  -- sSil branch: pattern-match on Q.force; only `sil c'` is consistent.
  -- The `with Q .force in q-eq` triggers bind's force-with reduction
  -- via the same case-split, so eq-f's type reduces to the concrete
  -- shape on each branch without explicit `rewrite bind-force-*`
  -- helpers — those previously caused RewritesNothing warnings.
  bind-pure-ret-step-inv Q h (sSil eq-f) dT with Q .force in q-eq
  ... | sil c'       = c' , sSil q-eq , subst Divergent (sym (sil-injective eq-f)) dT
  ... | ret _        = case eq-f of λ ()
  ... | vis _        = case eq-f of λ ()
  ... | ndbr _ _ _ _ = case eq-f of λ ()
  ... | mix _ _      = case eq-f of λ ()
  -- sNdbr branch: only Q.force = ndbr is consistent; sub-case on fQ i a.
  bind-pure-ret-step-inv {S = S} Q h
      (sNdbr {i = i} {a = a} eq-f eq-j) dT with Q .force in q-eq
  ... | ret _        = case eq-f of λ ()
  ... | sil _        = case eq-f of λ ()
  ... | vis _        = case eq-f of λ ()
  ... | mix _ _      = case eq-f of λ ()
  ... | ndbr fQ wiQ waQ wpQ with eq-f
  ...   | refl with fQ i a in fia-eq
  ...     | just t'  = t' , sNdbr q-eq fia-eq ,
                       subst Divergent (sym (just-injective eq-j)) dT
  ...     | nothing  = case eq-j of λ ()
  -- sMixSlide branch: only Q.force = mix is consistent.
  bind-pure-ret-step-inv Q h (sMixSlide eq-f) dT with Q .force in q-eq
  ... | ret _        = case eq-f of λ ()
  ... | sil _        = case eq-f of λ ()
  ... | vis _        = case eq-f of λ ()
  ... | ndbr _ _ _ _ = case eq-f of λ ()
  ... | mix fM Qt with eq-f
  ...   | refl       = Qt , sMixSlide q-eq , dT

-- Layer 1: coinductive lift of Divergent through pure-Ret bind.
-- Productivity: the recursive call sits directly under the
-- `.Divergent.diverge` copattern, matching the convention of
-- `step-sil-diverges` / `div-diverges` in FailuresDivergences.agda.
-- The `where`-bound `aux` is *not* a coinductive function — it is a
-- single Σ-tuple value reused across three copattern clauses, which
-- Agda accepts without breaking productivity.
--
-- Un-privatized for use in `CSP.Laws.Iterate_Bisim`'s
-- `tail-on-div-construct` discharge (mirrors the un-privatization
-- pattern of commit `8e6791b`).  `bind-pure-ret-step-inv` above
-- remains private; private definitions are still in lexical scope
-- here.
Divergent-bind-pure-ret-inv
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {Q : ITree E (ExtI I) R} (h : R → S)
    → Divergent (Q >>= λ r → Ret (h r))
    → Divergent Q
Divergent-bind-pure-ret-inv {Q = Q} h d .Divergent.next =
    proj₁ (bind-pure-ret-step-inv Q h
            (d .Divergent.step) (d .Divergent.diverge))
Divergent-bind-pure-ret-inv {Q = Q} h d .Divergent.step =
    proj₁ (proj₂ (bind-pure-ret-step-inv Q h
                   (d .Divergent.step) (d .Divergent.diverge)))
Divergent-bind-pure-ret-inv {Q = Q} h d .Divergent.diverge =
    Divergent-bind-pure-ret-inv h
      (proj₂ (proj₂ (bind-pure-ret-step-inv Q h
                      (d .Divergent.step) (d .Divergent.diverge))))

private
  -- Ret (h r) has only ret-shape; it cannot τ-step itself, and any
  -- bigstep from it lands at Ret (h r) (bNil) or deadlock (after sRet);
  -- neither can host a Divergent.
  Ret-no-Divergent
    : ∀ {ℓi' ℓs'} {I' : Set ℓ → Set ℓi'} {S' : Set ℓs'} {x : S'}
        {s' : List (Event√ E S')} {Q' : ITree E (ExtI I') S'}
      → Ret {I = ExtI I'} x ═⟨ s' ⟩═► Q'
      → Divergent Q' → ⊥
  Ret-no-Divergent bNil dv =
      no-τ-from-ret refl (dv .Divergent.step)
  Ret-no-Divergent (bTau τ-step _) _ =
      no-τ-from-ret refl τ-step
  Ret-no-Divergent (bStep (sRet _) rest) dv =
      no-τ-from-deadlock-bigstep rest (dv .Divergent.step)
  Ret-no-Divergent (bStep (sVis eq-f _) _) _ =
      case eq-f of λ ()
  Ret-no-Divergent (bStep (sMixVis eq-f _) _) _ =
      case eq-f of λ ()

  -- Layer 2: trace-level inversion.  We split d via bind-divergences-elim:
  -- the bds-handoff arm is absurd (Ret can't host Divergent), and the
  -- bds-tau-after arm reduces to peeling one more visible reach via
  -- bind-trace-helper, then invoking Layer 1 on the remaining
  -- Divergent (P''' >>= k).  This is a one-shot peeling — no recursion
  -- on the divergence chain — so the function terminates.
  bind-pure-ret-divergences-inv
    : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        (P : ITree E (ExtI I) R) (h : R → S)
        {s : List (Event√ E S)}
      → divergences (P >>= λ r → Ret (h r)) s
      → Σ (List (Event√ E R)) λ s' → divergences P s'
  bind-pure-ret-divergences-inv P h {s = s} d
      with bind-divergences-elim P (λ r → Ret (h r)) d
  ... | bds-handoff r s1 s2 eq-s tr-tick dv-Ret =
        ⊥-elim (Ret-no-Divergent
                  (dv-Ret .IsDivergence.reach)
                  (dv-Ret .IsDivergence.divwit))
  ... | bds-tau-after s-plain s2 eq-s P'' bs-P d-inner
        with bind-trace-helper P'' (λ r → Ret (h r))
                               (d-inner .IsDivergence.witness)
                               (d-inner .IsDivergence.reach)
  ...   | in-P {P' = P'''} {s = s-rest} bs-P''-to-P''' wit-eq =
          map evl s-plain ++ map evl s-rest ,
          record
            { prefix  = map evl s-plain ++ map evl s-rest
            ; suffix  = []
            ; split   = sym (++-identityʳ (map evl s-plain ++ map evl s-rest))
            ; witness = P'''
            ; reach   = bigstep-concat bs-P bs-P''-to-P'''
            ; divwit  = Divergent-bind-pure-ret-inv h
                          (subst Divergent wit-eq
                                 (d-inner .IsDivergence.divwit))
            }
  ...   | in-k r s1 s2-k eq-rest tr-P''-tick bs-Ret-to-wit =
          ⊥-elim (Ret-no-Divergent
                    bs-Ret-to-wit
                    (d-inner .IsDivergence.divwit))

  -- map-evl-split: when an `Event√` list of the form `map evl zs`
  -- (purely visible, no √) is split as `xs ++ ys`, both halves are
  -- themselves images of `map evl` for some underlying `Event E` lists.
  -- Useful when transporting a body-side divergence whose total trace
  -- equals `map evl s-plain` into a per-half lift via `lift-bind-bigstep`.
  map-evl-split
    : ∀ {ℓr} {R : Set ℓr}
        (zs : List (Event E)) (xs ys : List (Event√ E R))
      → xs ++ ys ≡ map evl zs
      → Σ (List (Event E)) λ xs0 → Σ (List (Event E)) λ ys0 →
          (zs ≡ xs0 ++ ys0) × (xs ≡ map evl xs0) × (ys ≡ map evl ys0)
  map-evl-split []         []         []         refl =
      [] , [] , refl , refl , refl
  map-evl-split []         []         (_ ∷ _)    ()
  map-evl-split []         (_ ∷ _)    _          ()
  map-evl-split (z ∷ zs')  []         ys         eq =
      [] , z ∷ zs' , refl , refl , eq
  map-evl-split (z ∷ zs')  (x ∷ xs'') ys eq =
    let h-eq : x ≡ evl z
        h-eq = ∷-head-eq eq
        t-eq : xs'' ++ ys ≡ map evl zs'
        t-eq = ∷-tail-eq eq
        rec = map-evl-split zs' xs'' ys t-eq
        xs0    = proj₁ rec
        ys0    = proj₁ (proj₂ rec)
        zs-eq  = proj₁ (proj₂ (proj₂ rec))
        pre-eq = proj₁ (proj₂ (proj₂ (proj₂ rec)))
        suf-eq = proj₂ (proj₂ (proj₂ (proj₂ rec)))
    in z ∷ xs0 , ys0 ,
       cong (z ∷_) zs-eq ,
       cong₂ _∷_ h-eq pre-eq ,
       suf-eq
    where open import Relation.Binary.PropositionalEquality using (cong₂)

  -- Step lift: every τ-step of Q to its `next` becomes a τ-step of
  -- `(Q >>= k)` to `(next >>= k)`.  Used in `Divergent-bind-left` to
  -- avoid `with` on a coinductive copattern clause.
bind-left-step-lift
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (Q : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {next : ITree E (ExtI I) R}
    → Q ─[ τ ]─► next
    → (Q >>= k) ─[ τ ]─► (next >>= k)
bind-left-step-lift Q k (sSil eq-f) =
    sSil (bind-force-sil Q k eq-f)
bind-left-step-lift Q k (sNdbr {f = f} {i = i} {a = a} eq-f eq-j) =
    sNdbr (bind-force-ndbr Q k eq-f)
          (bind-cont-ndbr-just k f i a eq-j)
bind-left-step-lift Q k (sMixSlide eq-f) =
    sMixSlide (bind-force-mix Q k eq-f)

-- Divergent-bind-left: every τ-step of Q lifts to a τ-step of (Q >>= k).
-- Productivity: the recursive call sits directly under the
-- `.Divergent.diverge` copattern, mirroring `Divergent-bind-pure-ret-inv`.
Divergent-bind-left
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {Q : ITree E (ExtI I) R} (k : R → ITree E (ExtI I) S)
    → Divergent Q → Divergent (Q >>= k)
Divergent-bind-left {Q = Q} k d .Divergent.next =
    d .Divergent.next >>= k
Divergent-bind-left {Q = Q} k d .Divergent.step =
    bind-left-step-lift Q k (d .Divergent.step)
Divergent-bind-left {Q = Q} k d .Divergent.diverge =
    Divergent-bind-left k (d .Divergent.diverge)

-- iter-bind sibling of bind-left-step-lift: every τ-step of Q lifts
-- to a τ-step of (iter-bind Q body) via the iter-bind force-equality
-- lemmas (which mirror bind-force-* in structure).
iter-bind-left-step-lift
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      (Q : ITree E (ExtI I) (A ⊎ R))
      (body : A → ITree E (ExtI I) (A ⊎ R))
      {Q' : ITree E (ExtI I) (A ⊎ R)}
    → Q ─[ τ ]─► Q'
    → (iter-bind Q body) ─[ τ ]─► (iter-bind Q' body)
iter-bind-left-step-lift Q body (sSil eq-f) =
    sSil (iter-bind-force-sil Q body eq-f)
iter-bind-left-step-lift Q body (sNdbr {f = f} {i = i} {a = a} eq-f eq-j) =
    sNdbr (iter-bind-force-ndbr Q body eq-f)
          (iter-bind-cont-ndbr-just body f i a eq-j)
iter-bind-left-step-lift Q body (sMixSlide eq-f) =
    sMixSlide (iter-bind-force-mix Q body eq-f)

-- Divergent-iter-bind-left: every τ-step of Q lifts to a τ-step of
-- (iter-bind Q body), so a divergence of Q yields a divergence of
-- (iter-bind Q body).  Mirrors Divergent-bind-left.  Productivity: the
-- recursive call sits directly under the `.Divergent.diverge` copattern.
Divergent-iter-bind-left
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {Q : ITree E (ExtI I) (A ⊎ R)}
      (body : A → ITree E (ExtI I) (A ⊎ R))
    → Divergent Q → Divergent (iter-bind Q body)
Divergent-iter-bind-left {Q = Q} body d .Divergent.next =
    iter-bind (d .Divergent.next) body
Divergent-iter-bind-left {Q = Q} body d .Divergent.step =
    iter-bind-left-step-lift Q body (d .Divergent.step)
Divergent-iter-bind-left {Q = Q} body d .Divergent.diverge =
    Divergent-iter-bind-left body (d .Divergent.diverge)

-- ----------------------------------------------------------------
-- Obstacle 3 prerequisite (stage 1): `deadlock` refuses every B.
--
-- `deadlock = vis (λ _ _ → nothing)` is vis-shaped (so `isStable
-- deadlock` reduces to `⊤`), and admits no LTS step on any event:
--   * `sRet eq` would need `force deadlock ≡ ret _`  — absurd
--   * `sVis refl eq` unifies the vis-function with `λ _ _ → nothing`,
--      leaving `eq : nothing ≡ just _` — absurd
--   * `sMixVis eq _` would need `force deadlock ≡ mix _ _` — absurd
-- This mirrors `deadlock-no-step` in `ITree_Relations.DRWeakBisim`,
-- inlined here to avoid an extra import for one short lemma.
deadlock-ref : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {B : Event√ E R → Set ℓB}
             → _ref_ (deadlock {E = E} {I = ExtI I} {R = R}) B
deadlock-ref =
    ref-stable tt₀ λ where
      _ _ (sRet ())
      _ _ (sVis refl ())
      _ _ (sMixVis () _)

-- ----------------------------------------------------------------
-- Obstacle 3 prerequisite (stage 2): every bigstep from any P that
-- consumes a √-suffix lands at `deadlock`.
--
-- This is the bigstep companion of `deadlock-no-step`.  The proof is a
-- structural induction on the bigstep:
--
--   * `bTau _ rest` preserves the trace, so recurse on `rest`.
--   * `bStep step rest` at `s1 = []` forces the step to consume the
--      lone `√ r`; the only `─[ev (√ r)]─►`-constructor is `sRet`, whose
--      target is `deadlock`.  The residual `rest : deadlock ═⟨ [] ⟩═► Q`
--      is then resolved by the local `deadlock-bigstep-[]` helper.
--   * `bStep step rest` at `s1 = e ∷ s1'` consumes an `evl e`, leaving
--      `rest` to handle `map evl s1' ++ [√ r]` — recurse with `s1'`.
--
-- The `sVis`/`sMixVis` arms at `s1 = []` and the `sRet` arm at
-- `s1 = e ∷ _` are auto-pruned by Agda: their step labels (resp.
-- `evl _` and `√ x`) cannot unify with the required head of the trace.
deadlock-bigstep-[]
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {Q : ITree E (ExtI I) R}
    → deadlock ═⟨ [] ⟩═► Q → Q ≡ deadlock
deadlock-bigstep-[] bNil                    = refl
deadlock-bigstep-[] (bTau (sSil ())     _)
deadlock-bigstep-[] (bTau (sNdbr () _)  _)
deadlock-bigstep-[] (bTau (sMixSlide ()) _)

tick-bigstep-lands-at-deadlock
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E (ExtI I) R}
      {s1 : List (Event E)} {r : R}
    → P ═⟨ map evl s1 ++ [ √ r ] ⟩═► Q
    → Q ≡ deadlock
tick-bigstep-lands-at-deadlock {s1 = []}      (bTau _ rest) =
    tick-bigstep-lands-at-deadlock {s1 = []} rest
tick-bigstep-lands-at-deadlock {s1 = []}      (bStep (sRet _) rest) =
    deadlock-bigstep-[] rest
tick-bigstep-lands-at-deadlock {s1 = e ∷ s1'} (bTau _ rest) =
    tick-bigstep-lands-at-deadlock {s1 = e ∷ s1'} rest
tick-bigstep-lands-at-deadlock {s1 = e ∷ s1'} (bStep _ rest) =
    tick-bigstep-lands-at-deadlock {s1 = s1'} rest

  -- ----------------------------------------------------------------
  -- The four bind-mono helpers themselves.
  --
  -- Status (2026-05-18): all four `*-mono-{⊑F⊥,⊑D}` lemmas are
  -- discharged.  The `*-mono-⊑D` pair appears just below (Obstacle 2
  -- resolved via `Divergent-bind-left`).  The `*-mono-⊑F⊥` pair
  -- follows after the `⊑D` pair (Obstacle 3 resolved by routing the
  -- body′-side `failure⊥` at predicate `B-A B`, sub-splitting, and
  -- rebuilding via `lift-body-ref-to-bind`).
    --
    -- Previous status notes (preserved for posterity).  Intended discharge route
    -- (see the section header for the recipe) decomposes the body′-side
    -- failure⊥ / divergence via `bind-{failures,divergences}-elim`,
    -- routes each non-absurd arm through the body-level hypothesis
    -- `bF⊑` / `bD⊑`, and rebuilds on the body side via the matching
    -- `-intro`.  The `bds-handoff` and `fail-in-k` arms are routine
    -- (Ret-no-Divergent / structural Ret refusal) but two genuine
    -- obstacles remain that block the `bds-tau-after` arm; both are
    -- *trace-alignment* obstacles arising because the bind continuation
    -- `k = λ a' → Ret (h a')` rewrites event tags from `Event√ E A` to
    -- `Event√ E (loop-tag A R)` / `Event√ E (while-tag A)`.
    --
    -- Obstacle 1 (trace-aligned bind-pure-ret divergences inversion):
    --
    --   The current `bind-pure-ret-divergences-inv` (lines 2932-2963)
    --   produces *some* trace `s'` in `List (Event√ E R)` together with
    --   `divergences P s'`, but the relationship between `s'` and the
    --   original `s : List (Event√ E S)` is opaque — `s'` is the
    --   visible-projection `map evl s-plain ++ map evl s-rest`, while
    --   `s` is `map evl s-plain ++ s2` with `s2 : List (Event√ E S)`.
    --   The √-tagged tails differ by the `h`-rewrite (e.g. `√ (h r)` on
    --   the S-side vs. `√ r` on the R-side), so a `divergences body′ s′`
    --   produced by inversion cannot in general be re-projected back
    --   to a divergence at the original `s`.  To close the proof we
    --   would need a strengthened inversion of the form
    --
    --     bind-pure-ret-divergences-inv-aligned
    --       : divergences (P >>= λ r → Ret (h r)) s
    --       → Σ s' [ divergences P s' × s ≡ map (mapEv h) s' ++ extra ]
    --
    --   which preserves the visible-trace alignment up to the
    --   `h`-rewrite on √-tags.  This requires an extra coinductive
    --   layer over `bind-trace-helper` that threads tag-rewriting
    --   through the bigstep concatenation.  Routine but ~80-100 LOC.
    --
    -- Obstacle 2 (trace-aligned right-monotonicity of `>>=` on
    --   divergence): even with Obstacle 1 solved, the `bds-tau-after`
    --   arm gives a body′-side divergence `divergences body′ a s′`.
    --   Routing through `bD⊑ a` yields `divergences body a s′`.  To
    --   rebuild as `divergences (body a >>= k) s` we need to lift the
    --   body-side divergence's bigstep `body a ═⟨ prefix′ ⟩═► W` to
    --   `body a >>= k ═⟨ map (mapEv h) prefix′ ⟩═► (W >>= k)` and to
    --   transport `Divergent W` to `Divergent (W >>= k)` (the
    --   "Divergent-bind-left" lemma — straightforward by coinduction
    --   on the τ-step of W: every τ of W induces a τ of W >>= k via
    --   `bind-force-{sil,ndbr,mix}`).  This Divergent-bind-left lemma
    --   is roughly 30 LOC by mirroring `Divergent-bind-pure-ret-inv`
    --   in the reverse direction.
    --
    -- Obstacle 3 (failures-side: the `fail-in-k` arm needs a body′
    --   failure constructed from the bigstep-to-√ together with a
    --   trivial refusal at deadlock).  The trivial-refusal-at-deadlock
    --   is straightforward, but routing it through `bF⊑ a` and then
    --   rebuilding the body-side `fail-in-k` requires inverting the
    --   resulting body-side `failures⊥` back into a bigstep-to-√ at
    --   the same trace `s1 ++ [√ r]`.  When the body-side returns
    --   `inj₁` we get a body failure (with some refusal) — we must
    --   extract the bigstep component while discarding the refusal;
    --   when it returns `inj₂` we get a body divergence at
    --   `s1 ++ [√ r]`, which needs to be re-attached to the original
    --   k-side failure via `bind-divergences-intro (bds-handoff …)`.
    --   The structure is mechanical but the refusal-shape bookkeeping
    --   is fiddly (~60 LOC).
    --
    --   Concrete prerequisites for a future attempt:
    --     * `deadlock-ref : ∀ B → deadlock ref B` — `ref-stable` on the
    --       `vis (λ _ _ → nothing)`-shape of `deadlock`, refusing every
    --       event via `deadlock-no-step` (already in DRWeakBisim.agda).
    --     * `tick-bigstep-lands-at-deadlock`
    --         : P ═⟨ map evl s1 ++ [√ r] ⟩═► Q → Q ≡ deadlock
    --       Structural induction on the bigstep; the `bStep (sRet eq) rest`
    --       case forces `rest : deadlock ═⟨ [] ⟩═► Q` whose only inhabitant
    --       is `bNil`.  ~30–50 LOC.
    --     * A `B-A` predicate-transport in the OPPOSITE direction of
    --       `B-AR` (line 2247): converts a bind-side refusal predicate
    --       `Event√ E (A ⊎ R) → Set ℓB` to a body-side predicate on
    --       `Event√ E A → Set ℓB`, mapping `√ a ↦ √ (inj₁ a)`.  Needed
    --       to route the outer `B` to a body-side B′ for `bF⊑ a`.
    --
    --   PITFALL discovered during a prior dispatch attempt: the
    --   "shortcut" of postulating `bF⊑ → bD⊑` (deriving ⊑D from ⊑F⊥) is
    --   UNSOUND in this codebase.  Routing a divergence-input through
    --   `⊑F⊥` constructively can return `inj₁ <body-failure>` rather than
    --   `inj₂ <body-divergence>`, and there is no axiom F2-style closure
    --   here that recovers the divergence.  Do NOT introduce such a
    --   postulate.  The divergence-input branch of `*Step-mono-⊑F⊥` must
    --   handle the `inj₁`-sub-case directly (rebuilding a failure at the
    --   bind level from a body-level failure plus refusal transport).
    --
    -- Status update: the two `*-mono-⊑D` lemmas have been DISCHARGED below
    -- using `Divergent-bind-left` (Obstacle 2 resolved) together with the
    -- existing `Divergent-bind-pure-ret-inv` (Layer 1) and a new local
    -- helper `map-evl-split` that recovers the underlying `Event E` lists
    -- from a body-side prefix/suffix split.  Obstacle 1 is sidestepped
    -- because the body-side reach is purely visible (it lives inside the
    -- `bds-tau-after` arm), so the body-level divergence inherits the
    -- same `map evl s-plain` trace from the body′-level divergence with
    -- no √-tag rewriting needed.
    --
    -- (Status update 2026-05-18: both `*-mono-⊑F⊥` lemmas are now
    -- DISCHARGED below, after `*-mono-⊑D`.  Obstacle 3 is resolved by
    -- routing the body′-side failure⊥ at predicate `B-A B`, then
    -- sub-splitting and rebuilding via a custom `lift-body-ref-to-bind`
    -- helper that maps a body refusal at `B-A B` to a (body >>= k)
    -- refusal at `B`.  See the comment at `loopStep-mono-⊑F⊥` below.
    -- The original obstacle-3 prerequisites — `deadlock-ref`,
    -- `tick-bigstep-lands-at-deadlock` (above), and `B-A` (line 2268) —
    -- are exactly what the new discharge consumes.)

-- Re-open the previous private block.  The helpers dedented above
-- (bind-left-step-lift through tick-bigstep-lands-at-deadlock) are
-- now public; everything from `loopStep-mono-⊑D` onward stays private.
private
  -- Discharged: divergence-side monotonicity for `loopStep` and `whileStep`.
  -- Routes through (Obstacle 2 resolved) `Divergent-bind-left` and (the
  -- previously-noted Obstacle 1 sidestepped by) `Divergent-bind-pure-ret-inv`
  -- combined with `map-evl-split`.  No trace-rewriting alignment is needed
  -- because the body's continuation `λ a' → Ret (inj₁ a')` is τ-quiescent,
  -- so the divergence must live inside body′; routing through `bD⊑` rebuilds
  -- a body-side divergence at the same visible reach.
  loopStep-mono-⊑D : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
      {body body′ : HKTree E (ExtI I) A}
    → (∀ a → body a ⊑D body′ a)
    → ∀ a → loopStep {R = R} body a ⊑D loopStep body′ a
  loopStep-mono-⊑D {I = I} {A = A} {R = R} {body = body} {body′ = body′}
                   bD⊑ a {s = s} dv
      with bind-divergences-elim (body′ a) (λ a' → Ret (inj₁ a')) dv
  ... | bds-handoff r s1 s2 eq-s tr-tick dv-Ret =
        ⊥-elim (Ret-no-Divergent
                  (dv-Ret .IsDivergence.reach)
                  (dv-Ret .IsDivergence.divwit))
  ... | bds-tau-after s-plain s2 eq-s P'' bs-P d-inner
        with bind-trace-helper P'' (λ a' → Ret (inj₁ a'))
                              (d-inner .IsDivergence.witness)
                              (d-inner .IsDivergence.reach)
  ...   | in-k r s1-h s2-h eq-h tr-tick-h bs-Ret =
          ⊥-elim (Ret-no-Divergent bs-Ret (d-inner .IsDivergence.divwit))
  ...   | in-P {P' = P'''} {s = s-rest} bs-P''-to-P''' wit-eq =
          result
    where
      open import Data.List.Properties using (++-assoc; ++-identityʳ)

      k : A → ITree E (ExtI I) (A ⊎ R)
      k = λ a' → Ret (inj₁ a')

      -- Lift Divergent (d-inner.witness) — via wit-eq — to Divergent (P''' >>= k),
      -- then via Layer 1 to Divergent P'''.
      dwit-P''' : Divergent P'''
      dwit-P''' = Divergent-bind-pure-ret-inv inj₁
                    (subst Divergent wit-eq (d-inner .IsDivergence.divwit))

      -- Compose visible reaches: body′ a → P'' → P'''.
      bs-body′-to-P''' : body′ a ═⟨ map evl s-plain ++ map evl s-rest ⟩═► P'''
      bs-body′-to-P''' = bigstep-concat bs-P bs-P''-to-P'''

      -- Body′-side divergence at the full visible reach, empty suffix.
      dv-body′ : divergences (body′ a) (map evl s-plain ++ map evl s-rest)
      dv-body′ = record
        { prefix  = map evl s-plain ++ map evl s-rest
        ; suffix  = []
        ; split   = sym (++-identityʳ _)
        ; witness = P'''
        ; reach   = bs-body′-to-P'''
        ; divwit  = dwit-P'''
        }

      -- Route through the body hypothesis (same total trace preserved by ⊑D).
      dv-body : divergences (body a) (map evl s-plain ++ map evl s-rest)
      dv-body = bD⊑ a dv-body′

      -- The body-side reach trace is all visible (`map evl _`), so its
      -- prefix and suffix split as `map evl pre0` and `map evl suf0`.
      pre+suf-eq : dv-body .IsDivergence.prefix ++ dv-body .IsDivergence.suffix
                 ≡ map evl (s-plain ++ s-rest)
      pre+suf-eq =
        trans (sym (dv-body .IsDivergence.split))
              (map-evl-++ s-plain s-rest)
        where
          map-evl-++ : ∀ {ℓr'} {R' : Set ℓr'} (xs ys : List (Event E))
                     → map (evl {R = R'}) xs ++ map (evl {R = R'}) ys
                     ≡ map (evl {R = R'}) (xs ++ ys)
          map-evl-++ []       ys = refl
          map-evl-++ (x ∷ xs) ys = cong (evl x ∷_) (map-evl-++ xs ys)

      split-data : Σ (List (Event E)) λ pre0 → Σ (List (Event E)) λ suf0 →
                     (s-plain ++ s-rest ≡ pre0 ++ suf0)
                   × (dv-body .IsDivergence.prefix ≡ map evl pre0)
                   × (dv-body .IsDivergence.suffix ≡ map evl suf0)
      split-data = map-evl-split (s-plain ++ s-rest)
                     (dv-body .IsDivergence.prefix)
                     (dv-body .IsDivergence.suffix)
                     pre+suf-eq

      pre0 = proj₁ split-data
      suf0 = proj₁ (proj₂ split-data)
      zs-eq  = proj₁ (proj₂ (proj₂ split-data))
      pre-eq = proj₁ (proj₂ (proj₂ (proj₂ split-data)))

      -- Re-typed body-side bigstep at trace `map evl pre0`.
      bs-body-pre0 : body a ═⟨ map evl pre0 ⟩═► dv-body .IsDivergence.witness
      bs-body-pre0 =
        subst (λ x → body a ═⟨ x ⟩═► dv-body .IsDivergence.witness)
              pre-eq
              (dv-body .IsDivergence.reach)

      -- Lift into bind.
      bs-bind-pre0 : (body a >>= k) ═⟨ map evl pre0 ⟩═►
                       (dv-body .IsDivergence.witness >>= k)
      bs-bind-pre0 = lift-bind-bigstep (body a) k pre0 bs-body-pre0

      map-evl-++ : ∀ {ℓr'} {R' : Set ℓr'} (xs ys : List (Event E))
                 → map (evl {R = R'}) (xs ++ ys)
                 ≡ map (evl {R = R'}) xs ++ map (evl {R = R'}) ys
      map-evl-++ []       ys = refl
      map-evl-++ (x ∷ xs) ys = cong (evl x ∷_) (map-evl-++ xs ys)

      mapL : List (Event E) → List (Event√ E (A ⊎ R))
      mapL = map evl

      -- d-inner.prefix ≡ map evl s-rest by the `in-P {s = s-rest}` pattern;
      -- so s2 ≡ map evl s-rest ++ d-inner.suffix via d-inner.split.
      s2-eq : s2 ≡ map evl s-rest ++ d-inner .IsDivergence.suffix
      s2-eq = d-inner .IsDivergence.split

      -- s ≡ mapL pre0 ++ (mapL suf0 ++ d-inner.suffix).
      split-eq : s ≡ mapL pre0 ++ (mapL suf0 ++ d-inner .IsDivergence.suffix)
      split-eq =
        trans eq-s
          (trans (cong (map evl s-plain ++_) s2-eq)
            (trans (sym (++-assoc (map evl s-plain) (map evl s-rest) _))
              (trans (cong (_++ d-inner .IsDivergence.suffix)
                           (sym (map-evl-++ s-plain s-rest)))
                (trans (cong (λ x → map evl x ++ _) zs-eq)
                  (trans (cong (_++ d-inner .IsDivergence.suffix)
                               (map-evl-++ pre0 suf0))
                    (++-assoc (mapL pre0) (mapL suf0) _))))))

      result : divergences (loopStep body a) s
      result = record
        { prefix  = mapL pre0
        ; suffix  = mapL suf0 ++ d-inner .IsDivergence.suffix
        ; split   = split-eq
        ; witness = dv-body .IsDivergence.witness >>= k
        ; reach   = bs-bind-pre0
        ; divwit  = Divergent-bind-left k (dv-body .IsDivergence.divwit)
        }

  whileStep-mono-⊑D : ∀ {ℓi} {I : Set ℓ → Set ℓi} {A : Set ℓ}
      (cond : A → Bool) {body body′ : HKTree E (ExtI I) A}
    → (∀ a → body a ⊑D body′ a)
    → ∀ a → whileStep cond body a ⊑D whileStep cond body′ a
  whileStep-mono-⊑D {I = I} {A = A} cond {body = body} {body′ = body′}
                    bD⊑ a {s = s} dv
      with bind-divergences-elim (body′ a)
             (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a')) dv
  ... | bds-handoff r s1 s2 eq-s tr-tick dv-Ret =
        ⊥-elim (Ret-no-Divergent
                  (dv-Ret .IsDivergence.reach)
                  (dv-Ret .IsDivergence.divwit))
  ... | bds-tau-after s-plain s2 eq-s P'' bs-P d-inner
        with bind-trace-helper P''
                              (λ a' → Ret (if cond a' then inj₁ a' else inj₂ a'))
                              (d-inner .IsDivergence.witness)
                              (d-inner .IsDivergence.reach)
  ...   | in-k r s1-h s2-h eq-h tr-tick-h bs-Ret =
          ⊥-elim (Ret-no-Divergent bs-Ret (d-inner .IsDivergence.divwit))
  ...   | in-P {P' = P'''} {s = s-rest} bs-P''-to-P''' wit-eq =
          result
    where
      open import Data.List.Properties using (++-assoc; ++-identityʳ)

      h : A → A ⊎ A
      h = λ a' → if cond a' then inj₁ a' else inj₂ a'

      k : A → ITree E (ExtI I) (A ⊎ A)
      k = λ a' → Ret (h a')

      dwit-P''' : Divergent P'''
      dwit-P''' = Divergent-bind-pure-ret-inv h
                    (subst Divergent wit-eq (d-inner .IsDivergence.divwit))

      bs-body′-to-P''' : body′ a ═⟨ map evl s-plain ++ map evl s-rest ⟩═► P'''
      bs-body′-to-P''' = bigstep-concat bs-P bs-P''-to-P'''

      dv-body′ : divergences (body′ a) (map evl s-plain ++ map evl s-rest)
      dv-body′ = record
        { prefix  = map evl s-plain ++ map evl s-rest
        ; suffix  = []
        ; split   = sym (++-identityʳ _)
        ; witness = P'''
        ; reach   = bs-body′-to-P'''
        ; divwit  = dwit-P'''
        }

      dv-body : divergences (body a) (map evl s-plain ++ map evl s-rest)
      dv-body = bD⊑ a dv-body′

      pre+suf-eq : dv-body .IsDivergence.prefix ++ dv-body .IsDivergence.suffix
                 ≡ map evl (s-plain ++ s-rest)
      pre+suf-eq =
        trans (sym (dv-body .IsDivergence.split))
              (map-evl-++ s-plain s-rest)
        where
          map-evl-++ : ∀ {ℓr'} {R' : Set ℓr'} (xs ys : List (Event E))
                     → map (evl {R = R'}) xs ++ map (evl {R = R'}) ys
                     ≡ map (evl {R = R'}) (xs ++ ys)
          map-evl-++ []       ys = refl
          map-evl-++ (x ∷ xs) ys = cong (evl x ∷_) (map-evl-++ xs ys)

      split-data : Σ (List (Event E)) λ pre0 → Σ (List (Event E)) λ suf0 →
                     (s-plain ++ s-rest ≡ pre0 ++ suf0)
                   × (dv-body .IsDivergence.prefix ≡ map evl pre0)
                   × (dv-body .IsDivergence.suffix ≡ map evl suf0)
      split-data = map-evl-split (s-plain ++ s-rest)
                     (dv-body .IsDivergence.prefix)
                     (dv-body .IsDivergence.suffix)
                     pre+suf-eq

      pre0 = proj₁ split-data
      suf0 = proj₁ (proj₂ split-data)
      zs-eq  = proj₁ (proj₂ (proj₂ split-data))
      pre-eq = proj₁ (proj₂ (proj₂ (proj₂ split-data)))

      bs-body-pre0 : body a ═⟨ map evl pre0 ⟩═► dv-body .IsDivergence.witness
      bs-body-pre0 =
        subst (λ x → body a ═⟨ x ⟩═► dv-body .IsDivergence.witness)
              pre-eq
              (dv-body .IsDivergence.reach)

      bs-bind-pre0 : (body a >>= k) ═⟨ map evl pre0 ⟩═►
                       (dv-body .IsDivergence.witness >>= k)
      bs-bind-pre0 = lift-bind-bigstep (body a) k pre0 bs-body-pre0

      map-evl-++ : ∀ {ℓr'} {R' : Set ℓr'} (xs ys : List (Event E))
                 → map (evl {R = R'}) (xs ++ ys)
                 ≡ map (evl {R = R'}) xs ++ map (evl {R = R'}) ys
      map-evl-++ []       ys = refl
      map-evl-++ (x ∷ xs) ys = cong (evl x ∷_) (map-evl-++ xs ys)

      mapL : List (Event E) → List (Event√ E (A ⊎ A))
      mapL = map evl

      s2-eq : s2 ≡ map evl s-rest ++ d-inner .IsDivergence.suffix
      s2-eq = d-inner .IsDivergence.split

      split-eq : s ≡ mapL pre0 ++ (mapL suf0 ++ d-inner .IsDivergence.suffix)
      split-eq =
        trans eq-s
          (trans (cong (map evl s-plain ++_) s2-eq)
            (trans (sym (++-assoc (map evl s-plain) (map evl s-rest) _))
              (trans (cong (_++ d-inner .IsDivergence.suffix)
                           (sym (map-evl-++ s-plain s-rest)))
                (trans (cong (λ x → map evl x ++ _) zs-eq)
                  (trans (cong (_++ d-inner .IsDivergence.suffix)
                               (map-evl-++ pre0 suf0))
                    (++-assoc (mapL pre0) (mapL suf0) _))))))

      result : divergences (whileStep cond body a) s
      result = record
        { prefix  = mapL pre0
        ; suffix  = mapL suf0 ++ d-inner .IsDivergence.suffix
        ; split   = split-eq
        ; witness = dv-body .IsDivergence.witness >>= k
        ; reach   = bs-bind-pre0
        ; divwit  = Divergent-bind-left k (dv-body .IsDivergence.divwit)
        }

  -- ----------------------------------------------------------------
  -- Discharged: failures-⊥ side monotonicity for `loopStep` and `whileStep`.
  --
  -- Obstacle 3 (failures-side refusal bookkeeping) is resolved here.
  -- The body′-side `failure⊥` is decomposed via `bind-{failures,
  -- divergences}-elim`; each non-absurd arm is routed through the body
  -- hypothesis `bF⊑ a` at predicate `B-A-h h B`, then sub-split on
  -- the inj₁ (body failure) / inj₂ (body divergence) disjuncts:
  --
  --   * inj₁ (body failure):
  --       fail-in-P arm: rebuild a bind-side failure at trace
  --         `map evl s'` via `lift-bind-bigstep` and the local helper
  --         `lift-body-ref-to-bind` (which lifts `W ref (B-A-h h B)`
  --         to `(W >>= λ a' → Ret (h a')) ref B`).
  --       fail-in-k arm: by `tick-bigstep-lands-at-deadlock`, the body
  --         failure's witness ≡ deadlock, so the bigstep proves
  --         `traces (body a) (map evl s1 ++ [√ r])`.  Reattach the
  --         k-side failure via `bind-failures-intro (fail-in-k …)`.
  --
  --   * inj₂ (body divergence):
  --       fail-in-P arm: same trace-lifting recipe as `*-mono-⊑D` (uses
  --         `map-evl-split` + `lift-bind-bigstep` + `Divergent-bind-left`).
  --       fail-in-k arm: by `prefix-tick-split` either the divergence's
  --         prefix lives entirely in `map evl s1` (lift to bind, extend
  --         via `div-extension-closed`) or the prefix swallows the √
  --         (`Divergent` on deadlock — absurd via `Divergent-bind-left`'s
  --         lifting + deadlock-no-step contradiction; here we use
  --         `tick-bigstep-lands-at-deadlock` + `no-τ-from-vis` directly).
  --
  -- The divergence-side arm of the input (`failures⊥` is failures ⊎
  -- divergences) is the same shape as `*-mono-⊑D`'s body — we factor
  -- it through that lemma by reusing its result.

  -- Generic refusal lift: `W ref (B-A-h h B)` ⇒ `(W >>= Ret-h) ref B`.
  -- Used in both the `fail-in-P` failure-rebuild and (indirectly via
  -- the proof structure) the broader `*-mono-⊑F⊥` discharge.
  lift-body-ref-to-bind
    : ∀ {ℓi' ℓs' ℓB} {I' : Set ℓ → Set ℓi'} {A' : Set ℓ} {S' : Set ℓs'}
        (W : ITree E (ExtI I') A') (h : A' → S')
        {B : Event√ E S' → Set ℓB}
      → W ref (B-A-h h B) → (W >>= λ a' → Ret (h a')) ref B
  lift-body-ref-to-bind {I' = I'} {A' = A'} {S' = S'}
                        W h {B = B} (ref-stable W-st no-ev)
      with W .force in p-eq
  ... | vis fW =
        ref-stable
          (vis-isStable {P = W >>= λ a' → Ret (h a')}
                        (bind-force-vis W (λ a' → Ret (h a')) p-eq))
          (λ e Be step → refusal-on-bind e Be step)
    where
      open import Data.Maybe using (Maybe; just; nothing)
      k' : _ → ITree E (ExtI I') _
      k' = λ a' → Ret (h a')
      -- Invert a bind step back to a W step (mirrors `invert-step` in
      -- `bind-failures-intro`'s `fail-in-P` case).
      invert-step
        : ∀ {e : Event√ E S'} {t : ITree E (ExtI I') S'}
        → (W >>= k') ─[ ev e ]─► t
        → Σ (Event E) λ e' → e ≡ evl e' ×
             Σ (ITree E (ExtI I') A') λ Q' → W ─[ ev (evl e') ]─► Q'
      invert-step {e} (sVis {f = f'} {at = at} {a = a} {t′ = tgt} eq-f eq-j) =
          cont-inv (fW at a) refl
        where
          f≡bcv : f' ≡ bind-cont-vis k' fW
          f≡bcv = vis-injective
                    (trans (sym eq-f) (bind-force-vis W k' p-eq))
          eq-j' : bind-cont-vis k' fW at a ≡ just tgt
          eq-j' = subst (λ g → g at a ≡ just tgt) f≡bcv eq-j
          cont-inv : (m : Maybe (ITree E (ExtI I') A'))
                   → fW at a ≡ m
                   → Σ (Event E) λ e' → e ≡ evl e' ×
                       Σ (ITree E (ExtI I') A') λ Q' →
                         W ─[ ev (evl e') ]─► Q'
          cont-inv nothing fia-eq =
              ⊥-elim
                (case trans (sym (bind-cont-vis-nothing k' fW at a fia-eq))
                            eq-j'
                      of λ ())
          cont-inv (just t′) fia-eq =
              evLabel (proj₁ at) (proj₂ at) a , refl ,
              t′ , sVis p-eq fia-eq
      invert-step {e} (sMixVis eq-f _) =
          case trans (sym (bind-force-vis W k' p-eq)) eq-f of λ ()
      invert-step {e} (sRet eq-f) =
          case trans (sym (bind-force-vis W k' p-eq)) eq-f of λ ()

      refusal-on-bind : ∀ {Q'} (e : Event√ E S')
                      → B e → (W >>= k') ─[ ev e ]─► Q' → ⊥
      refusal-on-bind e Be step with invert-step step
      ... | e' , refl , Q'' , step-W = no-ev (evl e') Be step-W
  ... | ret _        = ⊥-elim W-st
  ... | sil _        = ⊥-elim W-st
  ... | ndbr _ _ _ _ = ⊥-elim W-st
  ... | mix _ _      = ⊥-elim W-st
  lift-body-ref-to-bind W h {B = B} (ref-tick {x = x} step ¬Bx) =
      let (force-W-ret , _) = √-is-ret step
          force-bind : ITree.force (W >>= λ a' → Ret (h a'))
                       ≡ ret (h x)
          force-bind = bind-force-ret W (λ a' → Ret (h a')) force-W-ret
      in ref-tick (sRet force-bind) ¬Bx

-- prefix-tick-split: given `pre ++ suf = map evl s1 ++ [√ r]`, either
-- (case L) pre is a purely-visible prefix of `map evl s1` and suf
-- carries the trailing [√ r], or (case R) pre swallows the √ entirely
-- (suf = []).  Used in the failure-side `fail-in-k` discharge to
-- dispatch a body divergence whose prefix may or may not include the
-- final √-tick.
prefix-tick-split
  : ∀ {ℓr'} {R' : Set ℓr'} (s1 : List (Event E)) {r : R'}
      (pre suf : List (Event√ E R'))
    → pre ++ suf ≡ map evl s1 ++ [ √ r ]
    → (Σ (List (Event E)) λ pre0 → Σ (List (Event E)) λ suf0 →
         (s1 ≡ pre0 ++ suf0)
       × (pre ≡ map evl pre0)
       × (suf ≡ map evl suf0 ++ [ √ r ]))
    ⊎ (pre ≡ map evl s1 ++ [ √ r ] × suf ≡ [])
prefix-tick-split []         []         suf eq =
    inj₁ ([] , [] , refl , refl , eq)
prefix-tick-split []         (p ∷ []) []  eq =
    -- pre = [p]; the entire eq forces p ≡ √ r.
    inj₂ ( eq , refl )
prefix-tick-split []         (p ∷ []) (_ ∷ _) eq =
    case ∷-tail-eq eq of λ ()
prefix-tick-split []         (p ∷ _ ∷ _) suf eq =
    case ∷-tail-eq eq of λ ()
prefix-tick-split (e ∷ s1') []         suf eq =
    -- pre is empty; the whole suf is `map evl (e ∷ s1') ++ [√ r]`.
    inj₁ ([] , e ∷ s1' , refl , refl , eq)
prefix-tick-split (e ∷ s1') (p ∷ pre') suf eq =
    let h-eq : p ≡ evl e
        h-eq = ∷-head-eq eq
        t-eq : pre' ++ suf ≡ map evl s1' ++ [ √ _ ]
        t-eq = ∷-tail-eq eq
    in case prefix-tick-split s1' pre' suf t-eq of λ where
         (inj₁ (pre0 , suf0 , s1-eq , pre-eq , suf-eq)) →
           inj₁ ( e ∷ pre0 , suf0
                , cong (e ∷_) s1-eq
                , trans (cong (_∷ pre') h-eq)
                        (cong (evl e ∷_) pre-eq)
                , suf-eq )
         (inj₂ (pre-eq , suf-eq)) →
           inj₂ ( trans (cong (_∷ pre') h-eq)
                        (cong (evl e ∷_) pre-eq)
                , suf-eq )

-- Helper: Divergent deadlock is absurd.  `deadlock = vis (λ _ _ → nothing)`
-- is vis-shaped, hence has no τ outgoing.
Divergent-deadlock-absurd
  : ∀ {ℓi' ℓr'} {I' : Set ℓ → Set ℓi'} {R' : Set ℓr'}
  → Divergent {E = E} {I = ExtI I'} {R = R'} deadlock → ⊥
Divergent-deadlock-absurd d with d .Divergent.step
... | sSil      ()
... | sNdbr     () _
... | sMixSlide ()

  -- ----------------------------------------------------------------
  -- Phase I.0b — failures-side monotonicity for `loopStep` / `whileStep`.
  --
  -- Status (2026-05-18): the failure-INPUT case of these two lemmas is
  -- discharged constructively via `bind-failures-elim`, `bF⊑ a`,
  -- `lift-body-ref-to-bind`, and the obstacle-3 prerequisites
  -- (`deadlock-ref`, `tick-bigstep-lands-at-deadlock`, `B-A`/`B-A-h`,
  -- `Divergent-deadlock-absurd`, `prefix-tick-split`).  See the
  -- skeleton in `step-mono-⊑F⊥-aux`'s `(inj₁ f)` clause for the recipe.
  --
  -- However, the divergence-INPUT case is genuinely OBSTRUCTED in the
  -- constructive setting given only the `⊑F⊥` hypothesis on `body`:
  -- routing a body′-divergence through `bF⊑ a` may return `inj₁`
  -- (a body failure at the visible reach trace) rather than `inj₂`
  -- (a body divergence at the same trace).  In the `inj₁` sub-case we
  -- need a bind-side `failures⊥` at the FULL trace `s = map evl s-plain
  -- ++ s2`, but the body failure is at only the visible-reach prefix
  -- `map evl s-plain ++ map evl s-rest` (which is a strict prefix of
  -- `s` whenever `d-inner.suffix ≠ []`).  Extending a failure trace in
  -- general is unsound (`refuse-extension-bigstep` would be
  -- equivalent to the prohibited `bF⊑ → bD⊑` shortcut).
  --
  -- A correct discharge requires either:
  --   (a) an additional `bD⊑ : ∀ a → body a ⊑D body′ a` hypothesis
  --       alongside `bF⊑` (the same shape as the public
  --       `loop-mono-⊑D` postulate below already uses), routed via
  --       `*-mono-⊑D`'s recipe in the divergence-input branch; OR
  --   (b) a strengthened `⊑F⊥` that records WHERE divergence
  --       lives (analogous to FD's D1 axiom), so the divergence-input
  --       branch can lift the failure-arm to a divergence on `body`.
  --
  -- Option (a) is the pragmatic CSP-FD approach and matches the
  -- public lemmas' signatures.  Discharging the inner `*Step-mono-⊑F⊥`
  -- helpers under (a) is a mechanical extension of the current code;
  -- it requires changing both helper signatures to take `bD⊑` and
  -- inlining the `*-mono-⊑D` discharge in the divergence-input branch.
  --
  -- Both `loopStep-mono-⊑F⊥` and `whileStep-mono-⊑F⊥` are discharged
  -- below (after `step-mono-⊑F⊥-aux-failure`) under option (a): they
  -- take an additional `bD⊑ : ∀ a → body a ⊑D body′ a` hypothesis
  -- alongside `bF⊑`.  The failure-input branch is routed through
  -- `step-mono-⊑F⊥-aux-failure` (which only needs `bF⊑`), while the
  -- divergence-input branch reuses the `loopStep-mono-⊑D` /
  -- `whileStep-mono-⊑D` recipes already discharged above.
  --
  -- See the call sites for how the extra `bD⊑` hypothesis is threaded
  -- through `loop-mono-⊑FD` / `while-mono-⊑FD` (where both `bF⊑` and
  -- `bD⊑` are already in scope).

  -- step-mono-⊑F⊥-aux-failure : the (failure-INPUT) arm only of the
  -- two `*Step-mono-⊑F⊥` lemmas, which IS discharged constructively
  -- from just `bF⊑`.  This consumes a `failures (body′ a >>= k) s B`
  -- (NOT a `failures⊥`) and yields a `failures⊥ (body a >>= k) s B`.
  -- It is the proof skeleton that would be embedded in a future,
  -- properly-discharged `*Step-mono-⊑F⊥` taking an additional
  -- `bD⊑ : ∀ a → body a ⊑D body′ a` hypothesis.  (Such a discharge
  -- would also need a divergence-arm based on `*-mono-⊑D`'s recipe.)
  --
  -- Status: typechecks; not currently consumed.  Kept for documentation
  -- and as ready-to-use infrastructure for the option-(a) follow-up.
private
  step-mono-⊑F⊥-aux-failure
    : ∀ {ℓi ℓs ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ} {S : Set ℓs}
        (h : A → S)
        (body body′ : HKTree E (ExtI I) A)
      → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body′ a))
      → ∀ a {s : List (Event√ E S)}
          {B : Event√ E S → Set ℓB}
      → failures (body′ a >>= λ a' → Ret (h a')) s B
      → failures⊥ {ℓB = ℓB} (body  a >>= λ a' → Ret (h a')) s B
  step-mono-⊑F⊥-aux-failure {I = I} {A = A} {S = S} h body body′ bF⊑ a
                    {s = s} {B = B} f = failure-case f
    where
      open import Data.List.Properties using (++-assoc; ++-identityʳ)
      k : A → ITree E (ExtI I) S
      k = λ a' → Ret (h a')

      map-evl-++-S : (xs ys : List (Event E))
                   → map (evl {R = S}) (xs ++ ys)
                   ≡ map (evl {R = S}) xs ++ map (evl {R = S}) ys
      map-evl-++-S []       ys = refl
      map-evl-++-S (x ∷ xs) ys = cong (evl x ∷_) (map-evl-++-S xs ys)

      -- no-ev-adapt: convert a fail-in-P's `(e : Event E)` refusal-blocker
      -- into a `ref-stable`'s `(e : Event√ E A)` refusal-blocker on the
      -- body′ side.  Routes `evl e` directly; rules out `√ a` via the
      -- stable shape.
      no-ev-adapt
        : ∀ {ℓB} {B : Event√ E S → Set ℓB}
            {P'' : ITree E (ExtI I) A}
        → isStable P''
        → (∀ (e : Event E) {Q' : ITree E (ExtI I) A}
             → B (evl e) → ¬ (P'' ─[ ev (evl e) ]─► Q'))
        → (∀ (e : Event√ E A) → B-A-h h B e
            → ∀ {Q : ITree E (ExtI I) A}
            → ¬ (P'' ─[ ev e ]─► Q))
      no-ev-adapt {P'' = P''} st no-ev (evl e) Be step = no-ev e Be step
      no-ev-adapt {P'' = P''} st no-ev (√ a)   Bsa (sRet eq-ret)
          with P'' .force | st
      ... | vis _ | _ = case eq-ret of λ ()

      -- Lift body' divergence at a purely-visible trace `map evl s'` to
      -- a bind-side divergence at the same trace.  Mirrors the
      -- `bds-tau-after` arm of `*-mono-⊑D`.
      lift-body-div-visible
        : ∀ (s' : List (Event E))
        → divergences (body a) (map evl s')
        → divergences (body a >>= k) (map evl s')
      lift-body-div-visible s' dv-body =
        let pre+suf-eq : dv-body .IsDivergence.prefix
                         ++ dv-body .IsDivergence.suffix
                         ≡ map evl s'
            pre+suf-eq = sym (dv-body .IsDivergence.split)
            split-data = map-evl-split s'
                           (dv-body .IsDivergence.prefix)
                           (dv-body .IsDivergence.suffix)
                           pre+suf-eq
            pre0   = proj₁ split-data
            suf0   = proj₁ (proj₂ split-data)
            zs-eq  = proj₁ (proj₂ (proj₂ split-data))
            pre-eq = proj₁ (proj₂ (proj₂ (proj₂ split-data)))
            suf-eq = proj₂ (proj₂ (proj₂ (proj₂ split-data)))
            bs-body-pre0 : body a ═⟨ map evl pre0 ⟩═►
                             dv-body .IsDivergence.witness
            bs-body-pre0 =
              subst (λ x → body a ═⟨ x ⟩═► dv-body .IsDivergence.witness)
                    pre-eq
                    (dv-body .IsDivergence.reach)
            bs-bind-pre0 : (body a >>= k) ═⟨ map evl pre0 ⟩═►
                             (dv-body .IsDivergence.witness >>= k)
            bs-bind-pre0 = lift-bind-bigstep (body a) k pre0 bs-body-pre0
        in record
             { prefix  = map evl pre0
             ; suffix  = map evl suf0
             ; split   = trans (cong (map evl) zs-eq) (map-evl-++-S pre0 suf0)
             ; witness = dv-body .IsDivergence.witness >>= k
             ; reach   = bs-bind-pre0
             ; divwit  = Divergent-bind-left k (dv-body .IsDivergence.divwit)
             }

      failure-case : failures (body′ a >>= k) s B
                   → failures⊥ (body  a >>= k) s B
      failure-case f-bind with bind-failures-elim (body′ a) k f-bind
      -- fail-in-P: body′ stable failure at trace `map evl s'`.
      ... | fail-in-P {s = s'} {P'' = P''} bs-P′ stable no-ev =
            -- Build body′ failure at predicate (B-A-h h B).  The
            -- `ref-stable` constructor wants a refusal at the body's
            -- event type `Event√ E A`; we adapt by pattern-matching
            -- on the event to extract the underlying visible `Event E`.
            dispatch-fail-in-P s'
              (bF⊑ a (inj₁ (P'' , bs-P′
                          , ref-stable stable
                              (no-ev-adapt {P'' = P''} stable no-ev))))
        where
          dispatch-fail-in-P : (s' : List (Event E))
                             → failures⊥ (body a) (map evl s') (B-A-h h B)
                             → failures⊥ (body a >>= k) (map evl s') B
          dispatch-fail-in-P s' (inj₁ (W , bs-body , ref-body)) =
              inj₁ ( W >>= k
                   , lift-bind-bigstep (body a) k s' bs-body
                   , lift-body-ref-to-bind W h ref-body )
          dispatch-fail-in-P s' (inj₂ dv-body) =
              inj₂ (lift-body-div-visible s' dv-body)

      -- fail-in-k: body′ tick at √ r, then Ret (h r) fails on s2.
      failure-case f-bind | fail-in-k r s1 s2 eq-s
                                     (T-tick , bs-tick) fl-kr =
          let body′-trace-tick :
                body′ a ═⟨ map evl s1 ++ [ √ r ] ⟩═► T-tick
              body′-trace-tick = bs-tick
              T-eq : T-tick ≡ deadlock
              T-eq = tick-bigstep-lands-at-deadlock {s1 = s1} bs-tick
              bs-deadlock : body′ a ═⟨ map evl s1 ++ [ √ r ] ⟩═► deadlock
              bs-deadlock = subst (λ X → body′ a ═⟨ _ ⟩═► X) T-eq bs-tick
              f-body′ : failures (body′ a) (map evl s1 ++ [ √ r ])
                                  (B-A-h h B)
              f-body′ = deadlock , bs-deadlock , deadlock-ref
              fb-body : failures⊥ (body a) (map evl s1 ++ [ √ r ])
                                   (B-A-h h B)
              fb-body = bF⊑ a (inj₁ f-body′)
          in dispatch-fail-in-k r s1 s2 eq-s
                                 (T-tick , bs-tick) fl-kr fb-body
        where
          dispatch-fail-in-k
            : (r : A) (s1 : List (Event E))
              (s2 : List (Event√ E S))
              (eq-s : s ≡ map evl s1 ++ s2)
              (tr-tick-bind : traces (body′ a) (map evl s1 ++ [ √ r ]))
              (fl-kr : failures (k r) s2 B)
              (fb-body : failures⊥ (body a) (map evl s1 ++ [ √ r ])
                                    (B-A-h h B))
            → failures⊥ (body a >>= k) s B
          dispatch-fail-in-k r s1 s2 eq-s tr-tick-bind fl-kr
                             (inj₁ (W , bs-body-tick , ref-body)) =
              -- Body failure at trace map evl s1 ++ [√ r]: by
              -- `tick-bigstep-lands-at-deadlock`, W ≡ deadlock; the
              -- bigstep is exactly a body trace.  Rebuild via fail-in-k.
              inj₁ ( bind-failures-intro (body a) k
                       (fail-in-k r s1 s2 eq-s
                                  (W , bs-body-tick) fl-kr) )
          dispatch-fail-in-k r s1 s2 eq-s tr-tick-bind fl-kr
                             (inj₂ dv-body) =
              -- Body divergence at trace map evl s1 ++ [√ r].
              -- Dispatch on whether the divergence's prefix swallows
              -- the √ or stays purely visible.
              case prefix-tick-split s1
                     (dv-body .IsDivergence.prefix)
                     (dv-body .IsDivergence.suffix)
                     (sym (dv-body .IsDivergence.split))
                of λ where
                  (inj₁ (pre0 , suf0 , s1-eq , pre-eq , suf-eq)) →
                    -- Prefix purely visible.  Lift to bind-side divergence
                    -- at map evl pre0, then extend to s = map evl s1 ++ s2.
                    let bs-body-pre0 :
                          body a ═⟨ map evl pre0 ⟩═►
                            dv-body .IsDivergence.witness
                        bs-body-pre0 =
                          subst (λ x →
                                   body a ═⟨ x ⟩═► dv-body .IsDivergence.witness)
                                pre-eq
                                (dv-body .IsDivergence.reach)
                        bs-bind-pre0 :
                          (body a >>= k) ═⟨ map evl pre0 ⟩═►
                            (dv-body .IsDivergence.witness >>= k)
                        bs-bind-pre0 =
                          lift-bind-bigstep (body a) k pre0 bs-body-pre0
                        dv-bind-pre0 :
                          divergences (body a >>= k) (map evl pre0)
                        dv-bind-pre0 = record
                          { prefix  = map evl pre0
                          ; suffix  = []
                          ; split   = sym (++-identityʳ _)
                          ; witness = dv-body .IsDivergence.witness >>= k
                          ; reach   = bs-bind-pre0
                          ; divwit  =
                              Divergent-bind-left k
                                (dv-body .IsDivergence.divwit)
                          }
                        -- Extend: map evl pre0 ++ (map evl suf0 ++ s2)
                        --       = map evl s1 ++ s2  (= s, via eq-s).
                        ext-eq : s ≡ map evl pre0
                                     ++ (map evl suf0 ++ s2)
                        ext-eq =
                          trans eq-s
                            (trans (cong (λ x → map evl x ++ s2) s1-eq)
                              (trans (cong (_++ s2) (map-evl-++-S pre0 suf0))
                                     (++-assoc (map evl pre0)
                                               (map evl suf0) s2)))
                    in inj₂ (subst (divergences (body a >>= k)) (sym ext-eq)
                              (div-extension-closed {t = map evl suf0 ++ s2}
                                                    dv-bind-pre0))
                  (inj₂ (pre-eq , suf-eq)) →
                    -- Prefix swallows √ r: the divergence's bigstep
                    -- lands at deadlock; Divergent deadlock is absurd.
                    let bs-to-W :
                          body a ═⟨ map evl s1 ++ [ √ r ] ⟩═►
                            dv-body .IsDivergence.witness
                        bs-to-W =
                          subst (λ x →
                                   body a ═⟨ x ⟩═►
                                     dv-body .IsDivergence.witness)
                                pre-eq
                                (dv-body .IsDivergence.reach)
                        W-deadlock : dv-body .IsDivergence.witness ≡ deadlock
                        W-deadlock =
                          tick-bigstep-lands-at-deadlock {s1 = s1} bs-to-W
                    in ⊥-elim (Divergent-deadlock-absurd
                                 (subst Divergent W-deadlock
                                        (dv-body .IsDivergence.divwit)))

  -- loopStep-mono-⊑F⊥ / whileStep-mono-⊑F⊥ : option-(a) discharge.
  -- Dispatch on the disjoint sum that defines `failures⊥`: the
  -- failure-input arm reuses `step-mono-⊑F⊥-aux-failure` (the helper
  -- just above) — that arm only needs `bF⊑`; the divergence-input arm
  -- reuses `loopStep-mono-⊑D` / `whileStep-mono-⊑D` and consumes the
  -- extra `bD⊑` hypothesis.
  loopStep-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
      {R : Set ℓr} {body body′ : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body′ a))
    → (∀ a → body a ⊑D body′ a)
    → ∀ a → _⊑F⊥_ {ℓB = ℓB} (loopStep {R = R} body a) (loopStep body′ a)
  loopStep-mono-⊑F⊥ {R = R} {body = body} {body′ = body′} bF⊑ bD⊑ a (inj₁ f) =
      step-mono-⊑F⊥-aux-failure (inj₁ {B = R}) body body′ bF⊑ a f
  loopStep-mono-⊑F⊥             {body = body} {body′ = body′} bF⊑ bD⊑ a (inj₂ d) =
      inj₂ (loopStep-mono-⊑D bD⊑ a d)

  whileStep-mono-⊑F⊥ : ∀ {ℓi ℓB} {I : Set ℓ → Set ℓi} {A : Set ℓ}
      (cond : A → Bool) {body body′ : HKTree E (ExtI I) A}
    → (∀ a → _⊑F⊥_ {ℓB = ℓB} (body a) (body′ a))
    → (∀ a → body a ⊑D body′ a)
    → ∀ a → _⊑F⊥_ {ℓB = ℓB} (whileStep cond body a) (whileStep cond body′ a)
  whileStep-mono-⊑F⊥ cond {body = body} {body′ = body′} bF⊑ bD⊑ a (inj₁ f) =
      step-mono-⊑F⊥-aux-failure
        (λ a' → if cond a' then inj₁ a' else inj₂ a') body body′ bF⊑ a f
  whileStep-mono-⊑F⊥ cond {body = body} {body′ = body′} bF⊑ bD⊑ a (inj₂ d) =
      inj₂ (whileStep-mono-⊑D cond bD⊑ a d)

  -- (Divergence-input arm of the failed `step-mono-⊑F⊥-aux` discharge
  -- has been removed.  See the `loopStep-mono-⊑F⊥` definition above
  -- for the option-(a) discharge: signature was:
  --
  --   step-mono-⊑F⊥-aux-divergence
  --     : ∀ ... (h : A → S) (body body′ : HKTree E (ExtI I) A)
  --     → (∀ a → body a ⊑D body′ a)  -- (added bD⊑ hypothesis)
  --     → ∀ a {s B}
  --     → divergences (body′ a >>= λ a' → Ret (h a')) s
  --     → divergences (body  a >>= λ a' → Ret (h a')) s
  --
  -- with the body identical to `*-mono-⊑D`'s `bds-tau-after/in-P`
  -- case.  Combined with `step-mono-⊑F⊥-aux-failure` above, this
  -- yields a complete discharge of `*Step-mono-⊑F⊥` under the
  -- option-(a) hypothesis shape.
  --
  -- The original attempted discharge code (with the divergence arm)
  -- is preserved below as a block comment for reference.

{-
      divergence-case : divergences (body′ a >>= k) s
                      → failures⊥ (body  a >>= k) s B
      divergence-case dv-bind
          with bind-divergences-elim (body′ a) k dv-bind
      ... | bds-handoff r s1 s2 eq-s tr-tick dv-Ret =
            ⊥-elim (Ret-no-Divergent
                      (dv-Ret .IsDivergence.reach)
                      (dv-Ret .IsDivergence.divwit))
      ... | bds-tau-after s-plain s2 eq-s P'' bs-P d-inner
            with bind-trace-helper P'' k
                                   (d-inner .IsDivergence.witness)
                                   (d-inner .IsDivergence.reach)
      ...   | in-k r s1-h s2-h eq-h tr-tick-h bs-Ret =
              ⊥-elim (Ret-no-Divergent bs-Ret
                                       (d-inner .IsDivergence.divwit))
      ...   | in-P {P' = P'''} {s = s-rest} bs-P''-to-P''' wit-eq =
              -- Build body′-divergence at trace map evl (s-plain ++ s-rest).
              let dwit-P''' : Divergent P'''
                  dwit-P''' =
                    Divergent-bind-pure-ret-inv h
                      (subst Divergent wit-eq
                             (d-inner .IsDivergence.divwit))
                  bs-body′-to-P''' :
                    body′ a ═⟨ map evl s-plain ++ map evl s-rest ⟩═► P'''
                  bs-body′-to-P''' = bigstep-concat bs-P bs-P''-to-P'''
                  dv-body′ : divergences (body′ a)
                                          (map evl s-plain ++ map evl s-rest)
                  dv-body′ = record
                    { prefix  = map evl s-plain ++ map evl s-rest
                    ; suffix  = []
                    ; split   = sym (++-identityʳ _)
                    ; witness = P'''
                    ; reach   = bs-body′-to-P'''
                    ; divwit  = dwit-P'''
                    }
                  -- Route through bF⊑ at predicate B-A-h h B.
                  fb-body : failures⊥ (body a)
                                       (map evl s-plain ++ map evl s-rest)
                                       (B-A-h h B)
                  fb-body = bF⊑ a (inj₂ dv-body′)
              in dispatch fb-body
        where
          mapL : List (Event E) → List (Event√ E S)
          mapL = map evl

          dispatch : failures⊥ (body a) (map evl s-plain ++ map evl s-rest)
                                (B-A-h h B)
                   → failures⊥ (body a >>= k) s B
          -- Body failure sub-case: rebuild a bind-side FAILURE.
          dispatch (inj₁ (W , bs-body-W , ref-W)) =
              -- bs-body-W : body a ═⟨ map evl s-plain ++ map evl s-rest ⟩═► W
              -- Split the trace via map-evl-++-A; this gives us
              -- bs-body-W : body a ═⟨ map evl (s-plain ++ s-rest) ⟩═► W.
              let bs-merged : body a ═⟨ map evl (s-plain ++ s-rest) ⟩═► W
                  bs-merged =
                    subst (λ t → body a ═⟨ t ⟩═► W)
                          (map-evl-++-A s-plain s-rest)
                          bs-body-W
                  bs-bind : (body a >>= k) ═⟨ map evl (s-plain ++ s-rest) ⟩═►
                              (W >>= k)
                  bs-bind = lift-bind-bigstep (body a) k
                                              (s-plain ++ s-rest) bs-merged
                  bs-bind-back :
                    (body a >>= k) ═⟨ map evl s-plain ++ map evl s-rest ⟩═►
                      (W >>= k)
                  bs-bind-back =
                    subst (λ t → (body a >>= k) ═⟨ t ⟩═► (W >>= k))
                          (sym (map-evl-++-A s-plain s-rest))
                          bs-bind
                  -- Compose with d-inner.suffix to get total trace.
                  -- s ≡ map evl s-plain ++ s2; s2 ≡ map evl s-rest
                  --                                ++ d-inner.suffix.
                  s2-eq : s2 ≡ map evl s-rest ++ d-inner .IsDivergence.suffix
                  s2-eq = d-inner .IsDivergence.split
                  split-eq : s ≡ (map evl s-plain ++ map evl s-rest)
                                  ++ d-inner .IsDivergence.suffix
                  split-eq =
                    trans eq-s
                      (trans (cong (map evl s-plain ++_) s2-eq)
                             (sym (++-assoc (map evl s-plain)
                                            (map evl s-rest) _)))
                  -- The failure-witness state `W >>= k` refuses B by
                  -- lift-body-ref-to-bind.  Combined with the bigstep,
                  -- this is a `failures (body a >>= k) s B`.
                  -- We need a bigstep at trace s, but bs-bind-back only
                  -- reaches `(W >>= k)` at `map evl s-plain ++ map evl s-rest`.
                  -- Construct the full failure record at trace s by
                  -- using bigstep-concat with bNil + suffix expansion.
                  -- But failures expects an existential — we factor
                  -- via subst on the equality `split-eq`.
                  ref-bind : (W >>= k) ref B
                  ref-bind = lift-body-ref-to-bind W h ref-W
                  -- The failure's bigstep must lead at trace s.  We use
                  -- subst on split-eq to retype bs-bind-back.  But
                  -- bs-bind-back ends at map evl s-plain ++ map evl s-rest,
                  -- not at s.  Failures don't require the bigstep to
                  -- equal s — they require existence of *some* state at
                  -- trace s refusing B.  Since W >>= k already refuses B
                  -- and is reached at prefix-of-s (the body's traced part),
                  -- we need to take a longer bigstep that consumes the
                  -- suffix d-inner.suffix.  That's only possible if
                  -- (W >>= k) actually traces through d-inner.suffix —
                  -- which we don't know.
                  --
                  -- Resolution: by D1 (divergence strictness, axiomatized
                  -- through failures⊥'s coupling), any extension of a
                  -- divergence-trace is a failure for any refusal.  Since
                  -- body′ diverges through (s-plain ++ s-rest) and beyond,
                  -- and bF⊑ preserves failures⊥, we get a body-side
                  -- *divergence* not a failure here.  But constructively
                  -- bF⊑ could return inj₁ a failure.  The failure ends
                  -- at W; we can extend the bigstep to W by `traces-cons`
                  -- through `d-inner.suffix` ONLY IF W's force-eq propagates
                  -- the bind-shape — i.e., IF (W >>= k) traces through
                  -- d-inner.suffix.  W refuses everything in B, but the
                  -- bigstep we need extends the failure to s, and the
                  -- extended state must refuse B too.
                  --
                  -- Conservative simplification: re-emit as a failure⊥
                  -- at trace (map evl s-plain ++ map evl s-rest), then
                  -- adjust to s via the failure-extension principle:
                  -- (P ═⟨ t ⟩═► W' refusing B) gives `failures P t B`,
                  -- and trace extension to t ++ tail requires the tail
                  -- to be traceable from W'.  We CANNOT in general do
                  -- this.  Pragmatic workaround: cast the failure as a
                  -- *divergence* by appealing to `dv-body′` directly —
                  -- since body′ diverges at this trace and bF⊑ is
                  -- supposed to map divergences to divergences (or
                  -- failures), but to produce a bind-side `failures⊥` at
                  -- trace s we can wrap the body failure as a
                  -- `divergence` of body via the FD model's D1 axiom.
                  --
                  -- We discharge by EXTENDING the failure trace via a
                  -- "stuck-at-W" tail: since W ref B (refuses everything
                  -- in B), and W stays put on any step matching B-A-h h B,
                  -- the failure at any extended trace would require new
                  -- traces leading to a new refusing state.  We cannot
                  -- universally extend.  So we sidestep by routing the
                  -- output through the divergence injection — but we
                  -- don't have a divergence witness either.
                  --
                  -- Last resort: build the failure⊥ at the SHORTER trace
                  -- (s-plain ++ s-rest) and rely on the outer `bind-
                  -- failures-intro` infrastructure to extend to s.
                  -- This requires writing a failure-extension lemma —
                  -- ~10 LOC.  For now, leave a HOLE here and document.
                  fext : failures (body a >>= k) s B
                  fext = (W >>= k) ,
                         subst (λ t → (body a >>= k) ═⟨ t ⟩═► (W >>= k))
                               (sym split-eq)
                               (bigstep-concat bs-bind-back
                                  (refuse-extension-bigstep
                                    (W >>= k) (d-inner .IsDivergence.suffix)
                                    ref-bind)) ,
                         ref-bind
              in inj₁ fext
            where
              -- A vis-stable (or √-firing) state refusing B traces
              -- "trivially" through any further trace by remaining stuck.
              -- Concretely, every step away from a `ref-stable`-refusing
              -- state is blocked (no-ev), and every step from a `ref-tick`
              -- refusal is the √-step itself — which lands at deadlock,
              -- and deadlock has bigsteps only to deadlock at [], not
              -- through arbitrary suffixes.
              --
              -- We do NOT need this in full generality: since the failure
              -- arises from `bF⊑ a (inj₂ dv-body′)` and `dv-body′` is a
              -- DIVERGENCE, the contrapositive of bF⊑ tells us body must
              -- ALSO diverge here (in some weak sense).  But constructively
              -- bF⊑ may return a body failure — and we need to plumb it
              -- through.  Stub here with a postulate-equivalent reduction:
              postulate
                refuse-extension-bigstep
                  : ∀ {ℓi' ℓs' ℓB} {I' : Set ℓ → Set ℓi'} {S' : Set ℓs'}
                      (Q : ITree E (ExtI I') S')
                      (tail : List (Event√ E S'))
                      {B' : Event√ E S' → Set ℓB}
                    → Q ref B'
                    → Q ═⟨ tail ⟩═► Q
              -- ^^^ this is itself unsound in general (a refusing state
              -- may not bigstep through arbitrary suffixes).  See
              -- discussion in the comment above — this `inj₁` sub-case
              -- of the divergence input remains genuinely OBSTRUCTED.
          -- Body divergence sub-case: identical to `*-mono-⊑D`'s
          -- `bds-tau-after/in-P` case.
          dispatch (inj₂ dv-body) =
            let pre+suf-eq : dv-body .IsDivergence.prefix
                             ++ dv-body .IsDivergence.suffix
                             ≡ map evl (s-plain ++ s-rest)
                pre+suf-eq =
                  trans (sym (dv-body .IsDivergence.split))
                        (map-evl-++-A s-plain s-rest)
                split-data = map-evl-split (s-plain ++ s-rest)
                               (dv-body .IsDivergence.prefix)
                               (dv-body .IsDivergence.suffix)
                               pre+suf-eq
                pre0 = proj₁ split-data
                suf0 = proj₁ (proj₂ split-data)
                zs-eq = proj₁ (proj₂ (proj₂ split-data))
                pre-eq = proj₁ (proj₂ (proj₂ (proj₂ split-data)))
                bs-body-pre0 : body a ═⟨ map evl pre0 ⟩═►
                                 dv-body .IsDivergence.witness
                bs-body-pre0 =
                  subst (λ x →
                           body a ═⟨ x ⟩═► dv-body .IsDivergence.witness)
                        pre-eq
                        (dv-body .IsDivergence.reach)
                bs-bind-pre0 :
                  (body a >>= k) ═⟨ map evl pre0 ⟩═►
                    (dv-body .IsDivergence.witness >>= k)
                bs-bind-pre0 =
                  lift-bind-bigstep (body a) k pre0 bs-body-pre0
                s2-eq : s2 ≡ map evl s-rest ++ d-inner .IsDivergence.suffix
                s2-eq = d-inner .IsDivergence.split
                split-eq : s ≡ mapL pre0
                              ++ (mapL suf0 ++ d-inner .IsDivergence.suffix)
                split-eq =
                  trans eq-s
                    (trans (cong (map evl s-plain ++_) s2-eq)
                      (trans (sym (++-assoc (map evl s-plain)
                                            (map evl s-rest) _))
                        (trans (cong (_++ d-inner .IsDivergence.suffix)
                                     (sym (map-evl-++-rev s-plain s-rest)))
                          (trans (cong (λ x → map evl x ++ _) zs-eq)
                            (trans (cong (_++ d-inner .IsDivergence.suffix)
                                         (map-evl-++-rev pre0 suf0))
                              (++-assoc (mapL pre0) (mapL suf0) _))))))
            in inj₂ (record
                 { prefix  = mapL pre0
                 ; suffix  = mapL suf0 ++ d-inner .IsDivergence.suffix
                 ; split   = split-eq
                 ; witness = dv-body .IsDivergence.witness >>= k
                 ; reach   = bs-bind-pre0
                 ; divwit  = Divergent-bind-left k
                              (dv-body .IsDivergence.divwit)
                 })
-}

-- Bind-shape preservation along a no-tick bigstep.
--
-- A bigstep that starts at `P >>= (λ a' → Ret (inj₁ a'))` and consumes
-- only `evl` events (no √) must land at a state whose `.force` matches
-- the `.force` of `Q >>= (λ a' → Ret (inj₁ a'))` for some Q reachable
-- from P.
--
-- NOTE: formerly used by `loop-mono-⊑F⊥`'s in-body / ref-tick / inj₂
-- arm (now retired — F⊥ monotonicity is discharged via the
-- bisim-based `loop-mono-⊑F⊥-via-bisim` in `CSP.Laws.Iterate_Bisim`,
-- re-exported as `loop-mono-⊑F⊥` from `CSP.Laws.Iterate_FD`).  Kept
-- here as a general bind-shape utility.
private
  pure-bind-bigstep-shape
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (P : ITree E (ExtI I) A) (s : List (Event E))
        {W : ITree E (ExtI I) (A ⊎ R)}
      → (P >>= (λ a' → Ret (inj₁ {B = R} a'))) ═⟨ map evl s ⟩═► W
      → Σ (ITree E (ExtI I) A) λ Q →
          ITree.force W ≡ ITree.force (Q >>= (λ a' → Ret (inj₁ {B = R} a')))

  pure-bind-bigstep-shape P [] bNil = P , refl

  pure-bind-bigstep-shape {R = R} P s (bTau (sSil {t = next} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | sil c | refl = pure-bind-bigstep-shape {R = R} c s rest
  ... | ret _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  pure-bind-bigstep-shape {R = R} P s
      (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                   {i = i} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | ndbr fP _ _ _ | refl with fP i a in fi-eq | eq-j
  ... | just c | refl = pure-bind-bigstep-shape {R = R} c s rest
  ... | nothing | ()
  pure-bind-bigstep-shape P s (bTau (sNdbr eq-f eq-j) rest) | ret _   | ()
  pure-bind-bigstep-shape P s (bTau (sNdbr eq-f eq-j) rest) | sil _   | ()
  pure-bind-bigstep-shape P s (bTau (sNdbr eq-f eq-j) rest) | vis _   | ()
  pure-bind-bigstep-shape P s (bTau (sNdbr eq-f eq-j) rest) | mix _ _ | ()

  pure-bind-bigstep-shape {R = R} P s (bTau (sMixSlide {Qt = Qt} eq-f) rest)
      with P .force in p-eq | eq-f
  ... | mix _ Qt-body | refl =
        pure-bind-bigstep-shape {R = R} Qt-body s rest
  ... | ret _        | ()
  ... | sil _        | ()
  ... | vis _        | ()
  ... | ndbr _ _ _ _ | ()

  pure-bind-bigstep-shape {R = R} P (_ ∷ s')
      (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | vis fP | refl with fP at a in fi-eq | eq-j
  ... | just c | refl = pure-bind-bigstep-shape {R = R} c s' rest
  ... | nothing | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ret _        | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | sil _        | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sVis eq-f eq-j) rest) | mix _ _      | ()

  pure-bind-bigstep-shape {R = R} P (_ ∷ s')
      (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest)
      with P .force in p-eq | eq-f
  ... | mix fP _ | refl with fP at a in fi-eq | eq-j
  ... | just c | refl = pure-bind-bigstep-shape {R = R} c s' rest
  ... | nothing | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ret _        | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | sil _        | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | ndbr _ _ _ _ | ()
  pure-bind-bigstep-shape P (_ ∷ s') (bStep (sMixVis eq-f eq-j) rest) | vis _        | ()

  -- Direct corollary: a no-tick bigstep from a pure-Ret-inj₁ bind state
  -- cannot land at `ret (inj₂ r)`.  (Used to discharge the moral-absurdity
  -- in `loop-mono-⊑F⊥`'s in-body / ref-tick / inj₂ arm.)
  pure-bind-no-tick-bigstep-no-inj₂
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
        (P : ITree E (ExtI I) A) {s : List (Event E)}
        {W : ITree E (ExtI I) (A ⊎ R)} {r : R}
      → (P >>= (λ a' → Ret (inj₁ {B = R} a'))) ═⟨ map evl s ⟩═► W
      → ITree.force W ≢ ret (inj₂ r)
  pure-bind-no-tick-bigstep-no-inj₂ {R = R} P {s = s} bs eq-ret-inj₂ =
      let kk : _ → ITree E (ExtI _) _
          kk = λ a' → Ret (inj₁ {B = R} a')
          shape = pure-bind-bigstep-shape P s bs
          Q     = proj₁ shape
          f-eq  = proj₂ shape  -- ITree.force W ≡ ITree.force (Q >>= kk)
          bind-eq : ITree.force (Q >>= kk) ≡ ret (inj₂ _)
          bind-eq = trans (sym f-eq) eq-ret-inj₂
          inv = bind-force-ret-inv Q kk bind-eq
          q       = proj₁ inv
          eq-kq   = proj₂ (proj₂ inv) -- ITree.force (kk q) ≡ ret (inj₂ r)
      in case eq-kq of λ ()

-- NOTE: `loop-mono-⊑D` was formerly postulated here.  It is now
-- discharged in `CSP.Laws.Iterate_Bisim` as `loop-mono-⊑D-via-bisim`
-- (the `Loop-Sim.on-div` field is built from the real `tail-on-div-lift`
-- construction) and re-exported as `loop-mono-⊑D` from
-- `CSP.Laws.Iterate_FD`.
-- NOTE: `while-mono-⊑F⊥` and `while-mono-⊑D` were formerly postulated
-- here.  They are now discharged in `CSP.Laws.Iterate_Bisim` as
-- `while-mono-⊑F⊥-via-bisim` / `while-mono-⊑D-via-bisim` (using the tag
-- `whileTag cond`, so the generic iter `Loop-Sim` is definitionally a
-- `Loop-Sim` on `while`) and re-exported as `while-mono-⊑F⊥` /
-- `while-mono-⊑D` from `CSP.Laws.Iterate_FD`.  The derived
-- `while-mono-⊑FD` likewise now lives in `CSP.Laws.Iterate_FD`.

