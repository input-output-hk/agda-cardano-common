{-
  Trace and failures/divergences laws for sliding choice _▷_.
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; [_]; length; reverse; map; foldr; downFrom)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; sym; trans; subst; cong; inspect)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)

open import Class.DecEq using (DecEq; _≟_)
open import Prelude using (to-witness; just-to-witness)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences

module CSP.Laws.Bind
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Label
open Event√
open Traces
open Failures
open IsDivergence

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open import CSP.Laws.BasicProcesses {ℓ} {ℓe} {E} E-≟

-----------------------------------------------------------------------------------------
-- Bind >>=
-- traces [P >>= Q] =
-- traces [P ; Q] = {trp : traces [P] | ✓ ∉ trp • trp } ∪
--                  {trp : traces [P] ; trq : traces [Q] | ✓ ∉ trp ∧ trp ⌢ ⟨✓⟩ ∈ traces [P] • trp ⌢ trq }

-- BindSplit tracks the specific endpoint t-final: in-P carries the
-- P-bigstep landing at P' (so t-final ≡ P' >>= k), and in-k carries
-- the (k r)-bigstep landing at t-final.  This strong form lets the
-- FD lemmas reuse `bind-trace-helper` directly — no separate "strong"
-- elimination function is needed.
data BindSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (k : R → ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  -- Case 1: P is still executing; bigstep lands at P', and t-final ≡ P' >>= k.
  in-P : ∀ {P'} {s : List (Event E)}
       → P ═⟨ map evl s ⟩═► P'
       → t-final ≡ (P' >>= k)
       → BindSplit P k t-final (map evl s)

  -- Case 2: P finished with √ r after s1; (k r) bigsteps through s2 to t-final.
  in-k : ∀ {s : List (Event√ E S)}
       → (r : R)
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from k (can include √ S)
       → (s ≡ map evl s1 ++ s2)            -- s1 is lifted to S-type to join s2
       → traces P (map evl s1 ++ [ √ r ])  -- s1 is lifted to R-type to match P
       → (k r) ═⟨ s2 ⟩═► t-final           -- (k r)-bigstep landing at t-final
       → BindSplit P k t-final s


-- Inducts on the transition proof directly.  The returned BindSplit
-- carries the *specific* outer endpoint t-f and the (k r)-bigstep
-- landing at t-f, so the FD lemmas (bind-failures-elim,
-- bind-divergences-elim) call this directly when they need to track
-- a specific endpoint.
bind-trace-helper : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)} (t-f : ITree E (ExtI I) S)
   → (P >>= k) ═⟨ s ⟩═► t-f
   → BindSplit P k t-f s

-- Base Case
bind-trace-helper P k t-f bNil = in-P bNil refl

-- 1. Handling Silent Steps (Tau via sSil)
bind-trace-helper P k t-f (bTau (sSil {t = next} eq-f) big-step) with P .force in p-eq | eq-f
... | sil c | refl =
    case bind-trace-helper c k t-f big-step of λ where
      (in-P c-step eq) →
          in-P (bTau (sSil p-eq) c-step) eq
      (in-k r s1 s2 eq-s (P' , c-step) bs-k) →
          in-k r s1 s2 eq-s (P' , bTau (sSil p-eq) c-step) bs-k

... | ret r' | eq-f' =
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bTau (sSil eq-f') big-step)

... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace-helper P' k t-f big-step of λ where
      (in-P c-step eq) →
          in-P (bTau (sNdbr p-eq fi-eq) c-step) eq
      (in-k r s1 s2 eq-s (P'' , c-step) bs-k) →
          in-k r s1 s2 eq-s (P'' , bTau (sNdbr p-eq fi-eq) c-step) bs-k
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
    | ret r' | eq-f' =
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bTau (sNdbr eq-f' eq-j) big-step)

-- Absurd cases
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | sil _ | ()
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ()

-- 3. Handling Visible Steps (e via sVis)
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace-helper P' k t-f big-step of λ where
      (in-P {s = sP} c-step eq) →
          in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP}
               (bStep (sVis p-eq fi-eq) c-step) eq
      (in-k r s1 s2 eq-s (P'' , c-step) bs-k) →
          in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2
                (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                (P'' , bStep (sVis p-eq fi-eq) c-step) bs-k
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
    | ret r' | eq-f' =
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bStep (sVis eq-f' eq-j) big-step)

-- Absurd cases
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-- 4. Handling Termination (The hand-off to k via sRet)
bind-trace-helper P k t-f (bStep (sRet {x = r} eq-f) big-step) with P .force in p-eq | eq-f
... | ret r' | eq-f' =
    -- Hand-off point: s1 is empty ([]). P's trace is done.
    -- The rest of the transition (big-step) belongs to (k r').
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bStep (sRet eq-f') big-step)

-- Absurd cases
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | vis _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | mix _ _      | ()

-- 5. bTau via sMixSlide. force(P >>= k) ≡ mix _ Qt, with Qt = (Qt-orig >>= k).
bind-trace-helper P k t-f (bTau (sMixSlide eq-f) big-step) with P .force in p-eq | eq-f
... | mix _ Qt | refl =
    case bind-trace-helper Qt k t-f big-step of λ where
      (in-P c-step eq) →
          in-P (bTau (sMixSlide p-eq) c-step) eq
      (in-k r s1 s2 eq-s (Q' , c-step) bs-k) →
          in-k r s1 s2 eq-s (Q' , bTau (sMixSlide p-eq) c-step) bs-k
-- Hand-off: P at ret r' means force(P >>= k) = (k r').force; the τ-step belongs to k.
... | ret r' | eq-f' =
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bTau (sMixSlide eq-f') big-step)
-- Absurd cases: P.force is not mix, so eq-f : ≡ mix _ _ is impossible.
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 6. bStep via sMixVis. force(P >>= k) ≡ mix lifted-fP Qt; sub-case on fP at a.
bind-trace-helper P k t-f (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | mix fP _ | refl with fP at a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace-helper P' k t-f big-step of λ where
      (in-P {s = sP} c-step eq) →
          in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP}
               (bStep (sMixVis p-eq fi-eq) c-step) eq
      (in-k r s1 s2 eq-s (P'' , c-step) bs-k) →
          in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2
                (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s)
                (P'' , bStep (sMixVis p-eq fi-eq) c-step) bs-k
... | nothing | ()
-- Hand-off: P at ret r' means the step belongs to k.
bind-trace-helper P k t-f (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
    | ret r' | eq-f' =
    in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (bStep (sMixVis eq-f' eq-j) big-step)
-- Absurd cases.
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | vis _        | ()
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

bind-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)}
   → traces (P >>= k) s
   → Σ (ITree E (ExtI I) S) (λ t-f → BindSplit P k t-f s)
bind-trace P k (t-f , tr) = t-f , bind-trace-helper P k t-f tr

------------------------------------------------------------------------
-- Introduction direction for `bind-trace`.
-- Given a BindSplit witness, build a trace of (P >>= k).
------------------------------------------------------------------------

-- Helper A: lift a bigstep of P (R-typed events) to a bigstep of (P >>= k) (S-typed events).
-- The trace lists are both `map evl s` for the same underlying s : List (Event E),
-- but have different return-type parameters (Event√ E R vs Event√ E S).
-- Termination: structural induction on the bigstep.
-- Force lemmas for >>= : derive force (P >>= k) ≡ ... from force P ≡ ...
-- We use `with P .force | eq | (P >>= k) .force` so that after matching the
-- first two components, Agda can reduce (P >>= k) .force by the _>>=_ definition.
bind-force-sil
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) {c : ITree E (ExtI I) R}
      (k : R → ITree E (ExtI I) S)
    → ITree.force P ≡ sil c
    → ITree.force (P >>= k) ≡ sil (c >>= k)
bind-force-sil P k eq with P .force
... | sil _        = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

bind-force-ndbr
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R)
      {f : (ai : AnyTypes (ExtI I)) → ContinueType ai (Maybe (ITree E (ExtI I) R))}
      {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f wi wa)}
      (k : R → ITree E (ExtI I) S)
    → ITree.force P ≡ ndbr f wi wa wp
    → ITree.force (P >>= k) ≡ ndbr (bind-cont-ndbr k f) wi wa (bind-cont-ndbr-witness k f wp)
bind-force-ndbr P k eq with P .force
... | ndbr _ _ _ _ = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | mix _ _      = case eq of λ ()

bind-force-vis
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R)
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      (k : R → ITree E (ExtI I) S)
    → ITree.force P ≡ vis f
    → ITree.force (P >>= k) ≡ vis (bind-cont-vis k f)
bind-force-vis P k eq with P .force
... | vis _        = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

bind-force-mix
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R)
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      (k : R → ITree E (ExtI I) S)
    → ITree.force P ≡ mix f Qt
    → ITree.force (P >>= k) ≡ mix (bind-cont-mix k f) (Qt >>= k)
bind-force-mix P k eq with P .force
... | mix _ _      = case eq of λ { refl → refl }
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()

bind-force-ret
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) {r : R}
      (k : R → ITree E (ExtI I) S)
    → ITree.force P ≡ ret r
    → ITree.force (P >>= k) ≡ ITree.force (k r)
bind-force-ret P k eq with P .force
... | ret _        = case eq of λ { refl → refl }
... | sil _        = case eq of λ ()
... | vis _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()

-- Strong: lands at (P' >>= k) for the specific endpoint P' of the input
-- bigstep, not a Σ-quantified endpoint.  Callers (bind-trace-intro,
-- bind-failures-intro) need the specific endpoint to typecheck.
lift-bind-bigstep
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      (s : List (Event E)) {P' : ITree E (ExtI I) R}
    → P ═⟨ map evl s ⟩═► P'
    → (P >>= k) ═⟨ map evl s ⟩═► (P' >>= k)

lift-bind-bigstep P k [] bNil = bNil

-- τ via sSil: P steps silently, so does P >>= k
lift-bind-bigstep P k s (bTau (sSil {t = c} eq-f) rest) =
    bTau (sSil (bind-force-sil P k eq-f)) (lift-bind-bigstep c k s rest)

-- τ via sNdbr: P branches internally, so does P >>= k
lift-bind-bigstep P k s (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                      {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bTau (sNdbr (bind-force-ndbr P k eq-f) (bind-cont-ndbr-just k f i a eq-j))
         (lift-bind-bigstep t′ k s rest)

-- τ via sMixSlide: P slides from mix to fallback, so does P >>= k
lift-bind-bigstep P k s (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
    bTau (sMixSlide (bind-force-mix P k eq-f)) (lift-bind-bigstep Qt k s rest)

-- visible step via sVis: trace head consumed, recurse on tail
lift-bind-bigstep P k (_ ∷ s') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bStep (sVis (bind-force-vis P k eq-f) (bind-cont-vis-just k f at a eq-j))
          (lift-bind-bigstep t′ k s' rest)

-- visible step via sMixVis: trace head consumed, recurse on tail
lift-bind-bigstep P k (_ ∷ s') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    bStep (sMixVis (bind-force-mix P k eq-f) (bind-cont-mix-just k f at a eq-j))
          (lift-bind-bigstep t′ k s' rest)

-- Helper B: lift a bigstep of P ending with sRet (trace = map evl s1 ++ [ √ r ]).
-- Returns: the state of (P >>= k) after processing s1, plus a proof that its force
-- equals force (k r).
lift-bind-bigstep-tick
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {r : R} (s1 : List (Event E)) {t-final : ITree E (ExtI I) R}
    → P ═⟨ map evl s1 ++ [ √ r ] ⟩═► t-final
    → Σ (ITree E (ExtI I) S) λ P-bind →
        (P >>= k) ═⟨ map evl s1 ⟩═► P-bind
        × ITree.force P-bind ≡ ITree.force (k r)

-- Last step: sRet fires √ r (s1 = []).
-- sRet goes to deadlock; bNil gives deadlock as t-final. bind-force-ret gives force equality.
lift-bind-bigstep-tick P k [] (bStep (sRet {x = r} eq-f) bNil) =
    P >>= k , bNil , bind-force-ret P k eq-f
-- After sRet, we are at deadlock which cannot take a τ-step — impossible.
lift-bind-bigstep-tick P k [] (bStep (sRet eq-f) (bTau step _)) =
    ⊥-elim (τ-from-force-vis-impossible refl step)

-- τ via sSil
lift-bind-bigstep-tick P k s1 (bTau (sSil {t = c} eq-f) rest) =
    case lift-bind-bigstep-tick c k s1 rest of λ where
      (P-bind , bs , f-eq) → P-bind , bTau (sSil (bind-force-sil P k eq-f)) bs , f-eq

-- τ via sNdbr
lift-bind-bigstep-tick P k s1 (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                           {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-bind-bigstep-tick t′ k s1 rest of λ where
      (P-bind , bs , f-eq) → P-bind , bTau (sNdbr (bind-force-ndbr P k eq-f)
                                                    (bind-cont-ndbr-just k f i a eq-j)) bs , f-eq

-- τ via sMixSlide
lift-bind-bigstep-tick P k s1 (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
    case lift-bind-bigstep-tick Qt k s1 rest of λ where
      (P-bind , bs , f-eq) → P-bind , bTau (sMixSlide (bind-force-mix P k eq-f)) bs , f-eq

-- visible step via sVis: head of s1 consumed
lift-bind-bigstep-tick P k (_ ∷ s1') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-bind-bigstep-tick t′ k s1' rest of λ where
      (P-bind , bs , f-eq) → P-bind , bStep (sVis (bind-force-vis P k eq-f)
                                                    (bind-cont-vis-just k f at a eq-j)) bs , f-eq

-- visible step via sMixVis
lift-bind-bigstep-tick P k (_ ∷ s1') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
    case lift-bind-bigstep-tick t′ k s1' rest of λ where
      (P-bind , bs , f-eq) → P-bind , bStep (sMixVis (bind-force-mix P k eq-f)
                                                       (bind-cont-mix-just k f at a eq-j)) bs , f-eq

-- Helper C: concatenate two bigsteps.
bigstep-concat
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P P' P'' : ITree E (ExtI I) R} {s1 s2 : List (Event√ E R)}
    → P  ═⟨ s1 ⟩═► P'
    → P' ═⟨ s2 ⟩═► P''
    → P  ═⟨ s1 ++ s2 ⟩═► P''
bigstep-concat bNil           bs2 = bs2
bigstep-concat (bTau  step rest) bs2 = bTau  step (bigstep-concat rest bs2)
bigstep-concat (bStep step rest) bs2 = bStep step (bigstep-concat rest bs2)

-- Helper D: reattach a bigstep to a tree with the same force.
-- bfe-nil distinguishes the empty case (where Q ≡ t, useful for FD
-- intros); bfe-step rewires the first step's force-eq and reuses rest.
data BigstepForceEq {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     (P Q : ITree E I R) (t : ITree E I R) (s : List (Event√ E R))
     : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  bfe-nil  : s ≡ [] → Q ≡ t → BigstepForceEq P Q t s
  bfe-step : P ═⟨ s ⟩═► t → BigstepForceEq P Q t s

bigstep-force-eq
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E (ExtI I) R} {t : ITree E (ExtI I) R}
      {s : List (Event√ E R)}
    → ITree.force P ≡ ITree.force Q
    → Q ═⟨ s ⟩═► t
    → BigstepForceEq P Q t s
bigstep-force-eq _  bNil                                = bfe-nil refl refl
bigstep-force-eq eq (bTau  (sSil       eq-f) rest)      = bfe-step (bTau  (sSil       (trans eq eq-f)) rest)
bigstep-force-eq eq (bTau  (sNdbr      eq-f eq-j) rest) = bfe-step (bTau  (sNdbr      (trans eq eq-f) eq-j) rest)
bigstep-force-eq eq (bTau  (sMixSlide  eq-f) rest)      = bfe-step (bTau  (sMixSlide  (trans eq eq-f)) rest)
bigstep-force-eq eq (bStep (sVis       eq-f eq-j) rest) = bfe-step (bStep (sVis       (trans eq eq-f) eq-j) rest)
bigstep-force-eq eq (bStep (sRet       eq-f) rest)      = bfe-step (bStep (sRet       (trans eq eq-f)) rest)
bigstep-force-eq eq (bStep (sMixVis    eq-f eq-j) rest) = bfe-step (bStep (sMixVis    (trans eq eq-f) eq-j) rest)

bind-trace-intro : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
    {s : List (Event√ E S)} {t-final : ITree E (ExtI I) S}
  → BindSplit P k t-final s
  → traces (P >>= k) s

-- Case 1: P is still executing.  Lift P's bigstep through >>= .
bind-trace-intro P k (in-P {s = s'} bs-P _) =
  _ , lift-bind-bigstep P k s' bs-P

-- Case 2: P finished with value r, then k r provides the rest.
bind-trace-intro P k (in-k r s1 s2 eq-s (_ , tr-P-tick) bs-k) =
  subst (traces (P >>= k)) (sym eq-s) result
  where
    open import Data.List.Properties using (++-identityʳ)
    result : traces (P >>= k) (map evl s1 ++ s2)
    result with lift-bind-bigstep-tick P k s1 tr-P-tick
    ... | P-bind , bs-s1 , f-eq with bigstep-force-eq f-eq bs-k
    ...     | bfe-step bs-rest = _ , bigstep-concat bs-s1 bs-rest
    ...     | bfe-nil refl _   =
                P-bind ,
                subst (λ s* → (P >>= k) ═⟨ s* ⟩═► P-bind)
                      (sym (++-identityʳ (map evl s1))) bs-s1

------------------------------------------------------------------------
-- Monotonicity of _>>=_ under _⊑ᵀ_.
------------------------------------------------------------------------
>>=-mono-⊑ᵀ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
                {P P′ : ITree E (ExtI I) R}
                {k k′ : R → ITree E (ExtI I) S}
              → P ⊑ᵀ P′ → (∀ r → k r ⊑ᵀ k′ r)
              → (P >>= k) ⊑ᵀ (P′ >>= k′)
>>=-mono-⊑ᵀ {P = P} {P′ = P′} {k = k} {k′ = k′} P⊑P′ k⊑k′ tr-rhs
  with bind-trace P′ k′ tr-rhs
... | T-f , in-P {P' = P'} bs-P′ _ =
    let (X , bs-X) = P⊑P′ (P' , bs-P′)
    in bind-trace-intro P k (in-P {P' = X} bs-X refl)
... | T-f , in-k r s1 s2 eq-s tr-P′ bs-k′ =
    let (Y , bs-Y) = k⊑k′ r (T-f , bs-k′)
    in bind-trace-intro P k
         (in-k {t-final = Y} r s1 s2 eq-s (P⊑P′ tr-P′) bs-Y)

>>-mono-⊑ᵀ : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
               {P P′ : ITree E (ExtI I) R}
               {Q Q′ : ITree E (ExtI I) S}
             → P ⊑ᵀ P′ → Q ⊑ᵀ Q′
             → (P >> Q) ⊑ᵀ (P′ >> Q′)
>>-mono-⊑ᵀ P⊑P′ Q⊑Q′ = >>=-mono-⊑ᵀ P⊑P′ (λ _ → Q⊑Q′)

>=>-mono-⊑ᵀ : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi}
                {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
                {f f′ : R → ITree E (ExtI I) S}
                {g g′ : S → ITree E (ExtI I) T}
              → (∀ r → f r ⊑ᵀ f′ r)
              → (∀ s → g s ⊑ᵀ g′ s)
              → (∀ r → (f >=> g) r ⊑ᵀ (f′ >=> g′) r)
>=>-mono-⊑ᵀ f⊑f′ g⊑g′ r = >>=-mono-⊑ᵀ (f⊑f′ r) g⊑g′


-----------------------------------------------------------------------------------------
-- Bind >>

-- Strong form (matches BindSplit): in-P₀ carries the P-bigstep landing at P',
-- and in-Q₀ carries the Q-bigstep landing at t-final.
data Bind₀Split {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (Q : ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  in-P₀ : ∀ {P'} {s : List (Event E)}
       → P ═⟨ map evl s ⟩═► P'
       → t-final ≡ (_>>_ {R = R} P' Q)
       → Bind₀Split P Q t-final (map evl s)

  in-Q₀ : ∀ {s : List (Event√ E S)}
       → (r : R)
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from Q
       → (s ≡ map evl s1 ++ s2)
       → traces P (map evl s1 ++ [ √ r ])
       → Q ═⟨ s2 ⟩═► t-final
       → Bind₀Split P Q t-final s

bind₀-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   {s : List (Event√ E S)}
   (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
   → traces (P >> Q) s
   → Σ (ITree E (ExtI I) S) (λ t-f → Bind₀Split P Q t-f s)
bind₀-trace {ℓr = ℓr} {R = R} {s = s} P Q tr =
  let (t-f , bsplit) = bind-trace P (λ _ → Q) tr
  in t-f , help bsplit
    where
      help : ∀ {t-f} → BindSplit {ℓr = ℓr} {R = R} P (λ _ → Q) t-f _ → Bind₀Split P Q t-f _
      help (in-P {P' = P'} bs trP) =
        in-P₀ {P' = P'} bs trP
      help (in-k r s1 s2 eq trP bs-Q) =
        in-Q₀ r s1 s2 eq trP bs-Q

-----------------------------------------------------------------------------------------
-- Kleisli composition >=> or ⨾

-- Strong form (matches BindSplit): in-Pᵏ carries the (P x)-bigstep landing
-- at P', and in-Qᵏ carries the (Q r)-bigstep landing at t-final.
data KleisliSplit {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T) (x : R) (t-final : ITree E (ExtI I) T)
  : List (Event√ E T) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ ℓt) where

  in-Pᵏ : ∀ {P'} {s : List (Event E)}
       → (P x) ═⟨ map evl s ⟩═► P'
       → t-final ≡ (P' >>= Q)
       → KleisliSplit P Q x t-final (map evl s)

  in-Qᵏ : ∀ {s : List (Event√ E T)}
       → (r : S) (s1 : List (Event E)) (s2 : List (Event√ E T))
       → (s ≡ map evl s1 ++ s2)
       → traces (P x) (map evl s1 ++ [ √ r ])
       → (Q r) ═⟨ s2 ⟩═► t-final
       → KleisliSplit P Q x t-final s

kleisli-trace : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  {s : List (Event√ E T)} (x : R)
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T)
  → traces ((P >=> Q) x) s
  → Σ (ITree E (ExtI I) T) (λ t-f → KleisliSplit P Q x t-f s)
kleisli-trace {S = S} {T = T} {s = s} x P Q tr =
  let (t-f , bsplit) = bind-trace (P x) Q tr
  in t-f , help bsplit
  where
    help : ∀ {t-f} → BindSplit {R = S} {S = T} (P x) Q t-f s → KleisliSplit P Q x t-f s
    help (in-P {P' = P'} bs trP) =
      in-Pᵏ bs trP
    help (in-k r s1 s2 eq trP bs-Q) =
      in-Qᵏ r s1 s2 eq trP bs-Q

-----------------------------------------------------------------------------------------
-- Bind  P >>= k  /  P >> Q  /  P >=> Q
--
-- We expose two decomposition data types `BindFailureSplit` /
-- `BindDivergenceSplit`, mirroring `BindSplit` from `CSP.Laws.Traces`,
-- plus the four elim/intro functions for failures and divergences.


-- Inversion: force (P >>= k) ≡ ret x  ⇒  P at ret r, k r at ret x.
bind-force-ret-inv-aux
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {P : ITree E (ExtI I) R} {k : R → ITree E (ExtI I) S} {x : S}
      (nk : NodeKind E (ExtI I) R) → ITree.force P ≡ nk
    → ITree.force (P >>= k) ≡ ret x
    → Σ R λ r → ITree.force P ≡ ret r × ITree.force (k r) ≡ ret x
bind-force-ret-inv-aux {P = P} {k = k} (ret r) p-eq eq =
    r , p-eq , trans (sym (bind-force-ret P k p-eq)) eq
bind-force-ret-inv-aux {P = P} {k = k} (sil _)        p-eq eq
    with bind-force-sil P k p-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
bind-force-ret-inv-aux {P = P} {k = k} (vis _)        p-eq eq
    with bind-force-vis P k p-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
bind-force-ret-inv-aux {P = P} {k = k} (ndbr _ _ _ _) p-eq eq
    with bind-force-ndbr P k p-eq
... | f-eq = case trans (sym f-eq) eq of λ ()
bind-force-ret-inv-aux {P = P} {k = k} (mix _ _)      p-eq eq
    with bind-force-mix P k p-eq
... | f-eq = case trans (sym f-eq) eq of λ ()

bind-force-ret-inv
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S) {x : S}
    → ITree.force (P >>= k) ≡ ret x
    → Σ R λ r → ITree.force P ≡ ret r × ITree.force (k r) ≡ ret x
bind-force-ret-inv P k eq = bind-force-ret-inv-aux {P = P} {k = k} (P .force) refl eq

-- Constructor for isStable from a vis-shaped force equation.
vis-isStable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} {P : ITree E I R}
                 {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
               → ITree.force P ≡ vis f → isStable P
vis-isStable {P = P} eq with P .force
... | vis _        = tt₀
... | ret _        = case eq of λ ()
... | sil _        = case eq of λ ()
... | ndbr _ _ _ _ = case eq of λ ()
... | mix _ _      = case eq of λ ()


-- Liftnn an ev-step of P through >>= : if P fires ev e to Q', then
-- (P >>= k) fires ev e to (Q' >>= k).  Inverts the bind-cont reduction.
lift-bind-step-ev
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {e : Event E} {Q' : ITree E (ExtI I) R}
    → P ─[ ev (evl e) ]─► Q'
    → (P >>= k) ─[ ev (evl e) ]─► (Q' >>= k)
lift-bind-step-ev P k (sVis {f = f} {at = at} {a = a} eq-f eq-j) =
    sVis (bind-force-vis P k eq-f) (bind-cont-vis-just k f at a eq-j)
lift-bind-step-ev P k (sMixVis {f = f} {at = at} {a = a} eq-f eq-j) =
    sMixVis (bind-force-mix P k eq-f) (bind-cont-mix-just k f at a eq-j)

-- Same-force transports ev-steps (forward direction).
force-eq-trans-ev
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q t : ITree E I R} {e : Event√ E R}
    → ITree.force P ≡ ITree.force Q
    → Q ─[ ev e ]─► t
    → P ─[ ev e ]─► t
force-eq-trans-ev eq (sRet     eq-f)      = sRet     (trans eq eq-f)
force-eq-trans-ev eq (sVis     eq-f eq-j) = sVis     (trans eq eq-f) eq-j
force-eq-trans-ev eq (sMixVis  eq-f eq-j) = sMixVis  (trans eq eq-f) eq-j


-- Extend a bigstep that lands at a ret-state by one √ step.
extend-bigstep-tick
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P P'' : ITree E I R} {r : R} {s : List (Event√ E R)}
    → P ═⟨ s ⟩═► P'' → ITree.force P'' ≡ ret r
    → P ═⟨ s ++ [ √ r ] ⟩═► deadlock
extend-bigstep-tick bNil eq-r =
    bStep (sRet eq-r) bNil
extend-bigstep-tick (bTau step rest) eq-r =
    bTau step (extend-bigstep-tick rest eq-r)
extend-bigstep-tick (bStep step rest) eq-r =
    bStep step (extend-bigstep-tick rest eq-r)

-- Coinductive lift: Divergent transports along force-equality.
Divergent-force-eq
  : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E I R}
    → ITree.force P ≡ ITree.force Q
    → Divergent Q → Divergent P
Divergent-force-eq {P = P} {Q = Q} eq dQ .Divergent.next = dQ .Divergent.next
Divergent-force-eq eq dQ .Divergent.step
    with dQ .Divergent.step
... | sSil      eq-f      = sSil      (trans eq eq-f)
... | sNdbr     eq-f eq-j = sNdbr     (trans eq eq-f) eq-j
... | sMixSlide eq-f      = sMixSlide (trans eq eq-f)
Divergent-force-eq eq dQ .Divergent.diverge = dQ .Divergent.diverge

------------------------------------------------------------------------
-- BindFailureSplit / BindDivergenceSplit
------------------------------------------------------------------------

data BindFailureSplit {ℓi ℓr ℓs ℓB}
    {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
    (B : Event√ E S → Set ℓB)
    : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ lsuc ℓB) where

  fail-in-P : {s : List (Event E)} {P'' : ITree E (ExtI I) R}
            → P ═⟨ map evl s ⟩═► P''
            → isStable P''
            → (∀ (e : Event E) {Q' : ITree E (ExtI I) R}
                 → B (evl e) → ¬ (P'' ─[ ev (evl e) ]─► Q'))
            → BindFailureSplit P k B (map evl s)

  fail-in-k : {s : List (Event√ E S)}
            → (r : R) (s1 : List (Event E)) (s2 : List (Event√ E S))
            → s ≡ map evl s1 ++ s2
            → traces P (map evl s1 ++ [ √ r ])
            → failures (k r) s2 B
            → BindFailureSplit P k B s

-- Redesigned BindDivergenceSplit: avoids the original `div-in-P` constructor
-- which required `Divergent P` (constructively unknowable from `Divergent (P >>= k)`).
-- The replacement `bds-tau-after` keeps `Divergent (P'' >>= k)` directly — exactly
-- what `bind-trace-helper`'s in-P branch hands us — sidestepping the LEM/König obstacle.
data BindDivergenceSplit {ℓi ℓr ℓs}
    {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
    : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where

  -- Hand-off: P visibly traces through s1 then fires √ r; k r diverges on s2.
  bds-handoff : {s : List (Event√ E S)}
              → (r : R) (s1 : List (Event E)) (s2 : List (Event√ E S))
              → s ≡ map evl s1 ++ s2
              → traces P (map evl s1 ++ [ √ r ])
              → divergences (k r) s2
              → BindDivergenceSplit P k s

  -- P visibly traces through s-plain to P''; (P'' >>= k) then diverges on s2.
  -- This keeps the divergent witness inside (P'' >>= k) — no need to decide
  -- whether divergence stays in P or hands off later.
  bds-tau-after : {s : List (Event√ E S)}
                → (s-plain : List (Event E)) (s2 : List (Event√ E S))
                → s ≡ map evl s-plain ++ s2
                → (P'' : ITree E (ExtI I) R)
                → P ═⟨ map evl s-plain ⟩═► P''
                → divergences (P'' >>= k) s2
                → BindDivergenceSplit P k s

------------------------------------------------------------------------
-- bind-failures-elim
-- A failure of P >>= k splits either as a failure of P proper, or as
-- P firing √ r followed by a failure of k r.
------------------------------------------------------------------------

bind-failures-elim
  : ∀ {ℓi ℓr ℓs ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {s : List (Event√ E S)} {B : Event√ E S → Set ℓB}
    → failures (P >>= k) s B
    → BindFailureSplit P k B s
bind-failures-elim {I = I} {S = S} P k {s = s} {B = B} (Q , reach , ref)
                   with bind-trace-helper P k Q reach
... | in-k r s1 s2 eq-s tr-P-tick bs-kr =
      fail-in-k r s1 s2 eq-s tr-P-tick (Q , bs-kr , ref)
bind-failures-elim {I = I} {S = S} P k {s = .(map evl s')} {B = B}
                   (Q , reach , ref-stable st no-ev)
                   | in-P {P' = P''} {s = s'} bs-P refl
    with P'' .force in p-eq
... | vis fP'' =
        fail-in-P bs-P (vis-isStable {P = P''} p-eq)
          (λ e {Q'} Be step →
              no-ev (evl e) Be (lift-bind-step-ev P'' k step))
... | ret r = ret-case
  where
    open import Data.List.Properties using (++-identityʳ)
    bs-tick : P ═⟨ map evl s' ++ [ √ r ] ⟩═► deadlock
    bs-tick = extend-bigstep-tick bs-P p-eq
    -- We dispatch on `(k r).force` to construct (k r) ref B.  Since
    -- `force (P'' >>= k) ≡ force (k r)` and (P'' >>= k) is stable,
    -- (k r) must be vis-shaped.
    ret-case : BindFailureSplit P k B (map evl s')
    ret-case with (k r) .force in kr-eq
    ... | vis f =
            fail-in-k r s' [] (sym (++-identityʳ (map evl s')))
                      (deadlock , bs-tick)
                      (k r , bNil ,
                       ref-stable (vis-isStable {P = k r} kr-eq)
                                  (λ e Be step →
                                     no-ev e Be (lift-step-to-bind step)))
            where
              -- Lift step from (k r) to (P'' >>= k) via force-equality.
              lift-step-to-bind :
                ∀ {e : Event√ E S} {t : ITree E (ExtI I) S}
                → (k r) ─[ ev e ]─► t → (P'' >>= k) ─[ ev e ]─► t
              lift-step-to-bind step =
                force-eq-trans-ev (bind-force-ret P'' k p-eq) step
    -- Other (k r).force cases: (P'' >>= k) has the same force as (k r),
    -- so `isStable (P'' >>= k)` reduces to ⊥ in each case.
    ... | ret _        = ⊥-elim st
    ... | sil _        = ⊥-elim st
    ... | ndbr _ _ _ _ = ⊥-elim st
    ... | mix _ _      = ⊥-elim st
... | sil _        = ⊥-elim st
... | ndbr _ _ _ _ = ⊥-elim st
... | mix _ _      = ⊥-elim st
bind-failures-elim {I = I} {S = S} P k {s = .(map evl s')} {B = B}
                   (Q , reach , ref-tick {x = x} step ¬Bx)
                   | in-P {P' = P''} {s = s'} bs-P refl =
    -- (P'' >>= k) fires √ x.  Invert: P'' is at ret r and (k r) at ret x.
    let (r , p-ret , kr-ret) =
          bind-force-ret-inv P'' k (proj₁ (√-is-ret step))
        bs-tick : P ═⟨ map evl s' ++ [ √ r ] ⟩═► deadlock
        bs-tick = extend-bigstep-tick bs-P p-ret
        ref-kr : (k r) ref B
        ref-kr = ref-tick (sRet kr-ret) ¬Bx
    in fail-in-k r s' [] (sym (++-identityʳ (map evl s')))
                 (deadlock , bs-tick)
                 (k r , bNil , ref-kr)
  where open import Data.List.Properties using (++-identityʳ)

------------------------------------------------------------------------
-- bind-failures-intro
-- Given a BindFailureSplit witness, construct a failure of (P >>= k).
------------------------------------------------------------------------

bind-failures-intro
  : ∀ {ℓi ℓr ℓs ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {s : List (Event√ E S)} {B : Event√ E S → Set ℓB}
    → BindFailureSplit P k B s
    → failures (P >>= k) s B

-- Case 1: a P-failure.  Lift the P-bigstep through `>>=` to (P >>= k);
-- the residual (P'' >>= k) is vis-shaped (since P'' is), and refuses
-- exactly the events that P'' refused.
bind-failures-intro {I = I} {R = R} {S = S} P k {B = B}
                    (fail-in-P {s = s} {P'' = P''} bs-P P''-stable refusal) =
    (P'' >>= k) , lift-bind-bigstep P k s bs-P ,
    case-on-stable P''-stable
  where
    case-on-stable : isStable P'' → (P'' >>= k) ref B
    case-on-stable st with P'' .force in p-eq
    ... | vis fP'' =
          ref-stable
            (vis-isStable {P = P'' >>= k} (bind-force-vis P'' k p-eq))
            (λ e Be step → refusal-on-bind e Be step)
          where
            -- Invert an (P'' >>= k) ev-step back to a P'' ev-step.
            invert-step : ∀ {e : Event√ E S} {t : ITree E (ExtI I) S}
                        → (P'' >>= k) ─[ ev e ]─► t
                        → Σ (Event E) λ e' → e ≡ evl e' ×
                             Σ (ITree E (ExtI I) R) λ Q' → P'' ─[ ev (evl e') ]─► Q'
            invert-step {e} (sVis {f = f'} {at = at} {a = a} {t′ = tgt} eq-f eq-j) =
              cont-inv (fP'' at a) refl
              where
                f≡bcv : f' ≡ bind-cont-vis k fP''
                f≡bcv = vis-injective (trans (sym eq-f) (bind-force-vis P'' k p-eq))
                eq-j' : bind-cont-vis k fP'' at a ≡ just tgt
                eq-j' = subst (λ g → g at a ≡ just tgt) f≡bcv eq-j
                cont-inv : (m : Maybe (ITree E (ExtI I) R))
                         → fP'' at a ≡ m
                         → Σ (Event E) λ e' → e ≡ evl e' ×
                             Σ (ITree E (ExtI I) R) λ Q' → P'' ─[ ev (evl e') ]─► Q'
                cont-inv nothing  fia-eq =
                    ⊥-elim (case trans (sym (bind-cont-vis-nothing k fP'' at a fia-eq))
                                       eq-j'
                                 of λ ())
                cont-inv (just t′) fia-eq =
                    evLabel (proj₁ at) (proj₂ at) a , refl ,
                    t′ , sVis p-eq fia-eq
            invert-step {e} (sMixVis eq-f _) =
              case trans (sym (bind-force-vis P'' k p-eq)) eq-f of λ ()
            invert-step {e} (sRet eq-f) =
              case trans (sym (bind-force-vis P'' k p-eq)) eq-f of λ ()

            refusal-on-bind : ∀ {Q'} (e : Event√ E S)
                            → B e
                            → (P'' >>= k) ─[ ev e ]─► Q' → ⊥
            refusal-on-bind e Be step with invert-step step
            ... | e' , refl , Q' , step-P'' = refusal e' Be step-P''
    ... | ret _        = ⊥-elim st
    ... | sil _        = ⊥-elim st
    ... | ndbr _ _ _ _ = ⊥-elim st
    ... | mix _ _      = ⊥-elim st

-- Case 2: a k-failure after P fires √ r.  Stitch together via bigstep concat.
bind-failures-intro {I = I} {R = R} {S = S} P k {B = B}
                    (fail-in-k {s = s} r s1 s2 eq-s
                               (T-tick , tr-P-tick) (Q-k , bs-k , ref-k)) =
    subst (λ s* → failures (P >>= k) s* B) (sym eq-s) bind-failure
  where
    open import Data.List.Properties using (++-identityʳ)
    bind-failure : failures (P >>= k) (map evl s1 ++ s2) B
    bind-failure with lift-bind-bigstep-tick P k s1 tr-P-tick
    ... | P-bind , bs-s1 , f-eq with bigstep-force-eq f-eq bs-k
    ...     | bfe-step bs-s2 =
              -- Non-empty bigstep: endpoint is Q-k, refusal carries directly.
              Q-k , bigstep-concat bs-s1 bs-s2 , ref-k
    bind-failure | P-bind , bs-s1 , f-eq | bfe-nil refl kr≡Qk =
              -- Empty bigstep: s2 = [], Q-k = k r.  bigstep ends at P-bind;
              -- refusal must be transported via f-eq.  We rely on
              -- Q-k = k r (kr≡Qk) so f-eq becomes (force P-bind ≡ force Q-k).
              P-bind ,
              subst (λ s* → (P >>= k) ═⟨ s* ⟩═► P-bind)
                    (sym (++-identityʳ (map evl s1))) bs-s1 ,
              transport-ref ref-k
      where
        -- f-eq has type force P-bind ≡ force (k r); kr≡Qk : k r ≡ Q-k.
        f-eq' : ITree.force P-bind ≡ ITree.force Q-k
        f-eq' rewrite (sym kr≡Qk) = f-eq
        transport-ref : Q-k ref B → P-bind ref B
        transport-ref (ref-stable Qk-st no-ev) =
            stable-case Qk-st no-ev
          where
            stable-case : isStable Q-k
                        → (∀ e → B e → ∀ {Q'} → ¬ (Q-k ─[ ev e ]─► Q'))
                        → P-bind ref B
            stable-case st no-ev' with Q-k .force in qk-eq
            ... | vis f =
                  ref-stable
                    (vis-isStable {P = P-bind} (trans f-eq' qk-eq))
                    (λ e Be step →
                        no-ev' e Be (force-eq-trans-ev (sym f-eq') step))
            ... | ret _        = ⊥-elim st
            ... | sil _        = ⊥-elim st
            ... | ndbr _ _ _ _ = ⊥-elim st
            ... | mix _ _      = ⊥-elim st
        transport-ref (ref-tick step ¬B) =
            ref-tick (force-eq-trans-ev f-eq' step) ¬B

------------------------------------------------------------------------
-- bind-divergences-elim
--
-- Decompose `divergences (P >>= k) s` via `bind-trace-helper` on the
-- reach-prefix:
--   * in-k branch  → `bds-handoff` (P fired √ r; rest in k r).
--   * in-P branch  → `bds-tau-after` (P traced to P''; (P'' >>= k) still
--                    diverges on the suffix).
-- The in-P arm keeps the divergent witness inside `(P'' >>= k)` rather
-- than trying to lift it to `Divergent P`, which avoids the classical
-- reasoning the old `div-in-P` constructor required.
------------------------------------------------------------------------

bind-divergences-elim
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {s : List (Event√ E S)}
    → divergences (P >>= k) s
    → BindDivergenceSplit P k s
bind-divergences-elim P k {s = s} d
    with bind-trace-helper P k (d .IsDivergence.witness) (d .IsDivergence.reach)
-- in-k branch: P hands off to k r after firing √.
... | in-k r s1 s2 eq-s tr-P-tick bs-kr =
      bds-handoff r s1
                  (s2 ++ d .IsDivergence.suffix)
                  (trans (d .IsDivergence.split)
                         (trans (cong (_++ d .IsDivergence.suffix) eq-s)
                                (++-assoc (map evl s1) s2 (d .IsDivergence.suffix))))
                  tr-P-tick
                  (record { prefix  = s2
                          ; suffix  = d .IsDivergence.suffix
                          ; split   = refl
                          ; witness = d .IsDivergence.witness
                          ; reach   = bs-kr
                          ; divwit  = d .IsDivergence.divwit })
  where open import Data.List.Properties using (++-assoc)
-- in-P branch: divergence happens inside (P'' >>= k) after the visible reach.
... | in-P {P' = P''} {s = s-plain} bs-P refl =
      bds-tau-after s-plain
                    (d .IsDivergence.suffix)
                    (d .IsDivergence.split)
                    P''
                    bs-P
                    (record { prefix  = []
                            ; suffix  = d .IsDivergence.suffix
                            ; split   = refl
                            ; witness = P'' >>= k
                            ; reach   = bNil
                            ; divwit  = d .IsDivergence.divwit })

------------------------------------------------------------------------
-- bind-divergences-intro
-- Stitch a P/k decomposition back into a (P >>= k) divergence.
--   bds-handoff   : P fires √ r after s1, then k r diverges on s2.
--   bds-tau-after : P traces visibly to P''; the (P'' >>= k) divergence
--                   is already given.  Just prepend the lifted reach.
------------------------------------------------------------------------

bind-divergences-intro
  : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
      {s : List (Event√ E S)}
    → BindDivergenceSplit P k s
    → divergences (P >>= k) s
-- bds-handoff: lift the P-tick-bigstep, concat with k-divergence.
bind-divergences-intro P k {s = s}
                       (bds-handoff r s1 s2 eq-s (T-tick , bs-P-tick) dv-k) =
    subst (divergences (P >>= k)) (sym eq-s) result
  where
    open import Data.List.Properties using (++-assoc)
    result : divergences (P >>= k) (map evl s1 ++ s2)
    result with lift-bind-bigstep-tick P k s1 bs-P-tick
    ... | P-bind , bs-s1 , f-eq with bigstep-force-eq f-eq (dv-k .IsDivergence.reach)
    ...     | bfe-step bs-rest =
              -- non-empty bigstep: lands at dv-k's witness directly.
              record { prefix  = map evl s1 ++ dv-k .IsDivergence.prefix
                     ; suffix  = dv-k .IsDivergence.suffix
                     ; split   = trans (cong (map evl s1 ++_) (dv-k .IsDivergence.split))
                                       (sym (++-assoc (map evl s1) _ _))
                     ; witness = dv-k .IsDivergence.witness
                     ; reach   = bigstep-concat bs-s1 bs-rest
                     ; divwit  = dv-k .IsDivergence.divwit }
    ...     | bfe-nil refl kr≡witness =
              -- empty bigstep: dv-k.prefix = []; witness was k r.
              -- The (P >>= k) bigstep bs-s1 lands at P-bind whose force
              -- equals (k r).force.  Transport Divergent (k r) to
              -- Divergent P-bind via Divergent-force-eq.
              record { prefix  = map evl s1
                     ; suffix  = dv-k .IsDivergence.suffix
                     ; split   = trans
                                  (cong (map evl s1 ++_) (dv-k .IsDivergence.split))
                                  (cong (map evl s1 ++_)
                                        (sym (cong (_++ dv-k .IsDivergence.suffix)
                                                   (refl {x = []}))))
                     ; witness = P-bind
                     ; reach   = bs-s1
                     ; divwit  =
                         Divergent-force-eq
                           (trans f-eq (cong ITree.force kr≡witness))
                           (dv-k .IsDivergence.divwit)
                     }
-- bds-tau-after: lift the visible reach, then concat with the inner
-- (P'' >>= k) divergence.  No coinductive lift needed — the inner
-- IsDivergence already supplies its own divergent witness.
bind-divergences-intro {I = I} {R = R} {S = S} P k {s = s}
                       (bds-tau-after s-plain s2 eq-s P'' bs-P d-inner) =
    record { prefix  = map evl s-plain ++ d-inner .IsDivergence.prefix
           ; suffix  = d-inner .IsDivergence.suffix
           ; split   = trans eq-s
                       (trans (cong (map evl s-plain ++_) (d-inner .IsDivergence.split))
                              (sym (++-assoc (map evl s-plain)
                                             (d-inner .IsDivergence.prefix)
                                             (d-inner .IsDivergence.suffix))))
           ; witness = d-inner .IsDivergence.witness
           ; reach   = bigstep-concat (lift-bind-bigstep P k s-plain bs-P)
                                      (d-inner .IsDivergence.reach)
           ; divwit  = d-inner .IsDivergence.divwit
           }
  where open import Data.List.Properties using (++-assoc)
