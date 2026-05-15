{-
  This module defines the traces semantics for CSP.
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
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; [_]; length; reverse; map; foldr; downFrom)
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

module CSP.Laws.Traces {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree
open Traces

-----------------------------------------------------------------------------------------
-- For CSP Operators
-----------------------------------------------------------------------------------------

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-----------------------------------------------------------------------------------------
-- Internal choice ⊓
-- traces [P ⊓ Q] = traces [P] ∪ traces [Q]

InternalChoice-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (P Q : ITree E (ExtI I) R) {s : List (Event√ E R)}
  → traces {I = ExtI I} {R = R} (_⊓_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s

InternalChoice-trace P Q (_ , bNil) = inj₁ (_ , bNil)

-- Internal choice cannot take visible or return steps directly
InternalChoice-trace P Q (_ , bStep (sVis () _) _)
InternalChoice-trace P Q (_ , bStep (sRet ()) _)

InternalChoice-trace P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
  with i | a | eq-f
-- Case: Branch fzero (P)
-- By matching eq-f as refl, Agda now knows f is br2. 
-- br2 (_ , fin) (lift fzero) simplifies definitionally to (just P).
... | (_ , fin) | (lift fzero) | refl = 
    -- Now eq-j has type: just P ≡ just t'
    let t'-is-P = just-injective eq-j
    in inj₁ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-P) big-step)

-- Case: Branch fsuc fzero (Q)
... | (_ , fin) | (lift (fsuc fzero)) | refl =
    -- Now eq-j has type: just Q ≡ just t'
    let t'-is-Q = just-injective eq-j
    in inj₂ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-Q) big-step)

open import CSP.Laws.InternalChoice_FD E-≟ using (⊓-step-L; ⊓-step-R)

------------------------------------------------------------------------
-- Introduction direction for `InternalChoice-trace`.
-- Lift a trace of P (resp. Q) into a trace of (P ⊓ Q) via the τ-step.
------------------------------------------------------------------------
IntChoice-trace-introL : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces P s → traces (P ⊓ Q) s
IntChoice-trace-introL {P = P} {Q} (P′ , bs) = P′ , bTau (⊓-step-L P Q) bs

IntChoice-trace-introR : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces Q s → traces (P ⊓ Q) s
IntChoice-trace-introR {P = P} {Q} (Q′ , bs) = Q′ , bTau (⊓-step-R P Q) bs

------------------------------------------------------------------------
-- Refinement-order corollaries:  (P ⊓ Q) ⊑ᵀ P   and   (P ⊓ Q) ⊑ᵀ Q.
------------------------------------------------------------------------
⊑ᵀ-⊓-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {P Q : ITree E (ExtI I) R}
         → (P ⊓ Q) ⊑ᵀ P
⊑ᵀ-⊓-L = IntChoice-trace-introL

⊑ᵀ-⊓-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {P Q : ITree E (ExtI I) R}
         → (P ⊓ Q) ⊑ᵀ Q
⊑ᵀ-⊓-R = IntChoice-trace-introR

------------------------------------------------------------------------
-- Monotonicity of _⊓_ under _⊑ᵀ_.
------------------------------------------------------------------------
⊓-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {P P′ Q Q′ : ITree E (ExtI I) R}
            → P ⊑ᵀ P′ → Q ⊑ᵀ Q′
            → (P ⊓ Q) ⊑ᵀ (P′ ⊓ Q′)
⊓-mono-⊑ᵀ {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} P⊑P′ Q⊑Q′ tr-rhs
  with InternalChoice-trace P′ Q′ tr-rhs
... | inj₁ tr-P′ = IntChoice-trace-introL (P⊑P′ tr-P′)
... | inj₂ tr-Q′ = IntChoice-trace-introR (Q⊑Q′ tr-Q′)

-----------------------------------------------------------------------------------------
-- External choice □
-- traces [P □ Q] = traces [P] ∪ traces [Q]

-- Helper lemmas: under the new `_□_`, the `ret | vis` and `vis | ret` cases
-- delegate to a nested `(Q ▷ P).force` / `(P ▷ Q).force`, which Agda does not
-- automatically reduce past the with-abstraction.  We prove the reduced shape
-- here so absurd patterns can dispatch via `mix≢sil`/`mix≢vis`/`mix≢ret`.
ExternalChoice-trace-aux : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)} {t′ : ITree E (ExtI I) R}
  ⦃ dec : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → (_□_ {I = I} {R = R} P Q) ═⟨ s ⟩═► t′
  → traces P s ⊎ traces Q s

-- 1. Empty trace
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} P Q bNil = inj₁ (_ , bNil)

-- 2. Tau steps (Choice not yet resolved)
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- Case: P took a silent step.
-- By matching eq-f as refl (or using it in a 'with'), Agda knows next is (P' □ Q).
... | sil P' | _ | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , bTau (sSil p-eq) trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , trQ)

-- Case: Q took a silent step
... | ret _ | sil Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- Case: Q took a silent step
... | vis _ | sil Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- Case: Q took a silent step
... | ndbr _ _ _ _ | sil Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- Case: P is mix, Q took a silent step. New □ rule: mix _ _ | sil Q' = sil (P □ Q').
... | mix _ _ | sil Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sSil q-eq) trQ)

-- These cases are impossible because (ret □ ret) or (vis □ vis)
-- are not silent nodes.
-- eq-f : (force ((E-≟ CSP.Definitions.Operators.□ P) Q) ≡ sil t

--------------------------------------------------------------------------------------
-- For the "ret r1" and "ret r2" case, it is a bit complicated because the definition
-- of □ relies on a Dec to reduce it to "ret r1" if r1 = r2, or Stop otherwise.

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- match with r1 ≟ r2: yes
...                     | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no
                                                        | no neq with eq-f
...                                                               | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no
                                                       | no neq with eq-f
...                                                                 | ()

--------------------------------------------------------------------------------------

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret _  | vis _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | vis _  | ret _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | vis _  | vis _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | vis _  | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | vis _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret _  | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | ret _  | ()

-- New mix absurd cases for sSil: when one side is mix and the other isn't sil,
-- the new _□_ rules produce mix or ndbr shapes — never sil.
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | mix _ _ | ret _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | mix _ _ | vis _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | mix _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | mix _ _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | ret _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | vis _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  | ndbr _ _ _ _ | mix _ _ | ()

-- 3. Visible steps (Choice resolved)
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | vis fP | vis fQ | refl
    with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- just P' / nothing → mergeVis = just P', eq-j : just P' ≡ just t'
-- refl unifies t' = P', big-step : P' ═⟨ s ⟩═► _ already P's trace
... | just P'  | nothing  | refl =
    inj₁ (_ , bStep (sVis p-eq fp-eq) big-step)

-- nothing / just Q' → mergeVis = just Q', eq-j : just Q' ≡ just t'
... | nothing  | just Q'  | refl =
    inj₂ (_ , bStep (sVis q-eq fq-eq) big-step)

-- just P' / just Q' → mergeVis = just (P' □ Q'), big-step : (P' □ Q') ═⟨ s ⟩═► _
... | just P'  | just Q'  | refl =
    case InternalChoice-trace P' Q' (_ , big-step) of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bStep (sVis p-eq fp-eq) trP)
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bStep (sVis q-eq fq-eq) trQ)

-- nothing / nothing → mergeVis = nothing, eq-j : nothing ≡ just t' — impossible
... | nothing  | nothing  | ()

-- These cases are impossible because (ret □ ret)
--------------------------------------------------------------------------------------
-- For the "ret r1" and "ret r2" case, it is a bit complicated because the definition
-- of □ relies on a Dec to reduce it to "ret r1" if r1 = r2, or Stop otherwise.
-- Stop is "vis (λ _ _ → nothing)", and so we need to prove Stop is not possible for sVis

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- match with r1 ≟ r2: yes
...                     | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no
                                                        | no neq with eq-f -- {!!} -- with eq-f
...                                                               | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no
                                                       | no neq with eq-f
...                                                              | ()

--------------------------------------------------------------------------------------

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _  | vis _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _  | ret _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _  | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | vis _  | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _  | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ret _  | ()
-- NEW: mix-shape absurds for sVis (sVis requires force = vis _, mix shape is not vis).
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ret _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix _ _ | sil _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix _ _ | vis _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix _ _ | mix _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | mix _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _ | mix _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | mix _ _ | ()
-- sil-shape absurds for sVis (sVis requires force = vis _, sil shape is not vis).
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | sil _ | ret _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | sil _ | sil _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | sil _ | vis _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | sil _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | sil _ | mix _ _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | sil _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _ | sil _ | ()
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ndbr _ _ _ _ | sil _ | ()

-- 4. Termination (sRet)
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = √ r} (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq
-- Case: Both P and Q are ready to terminate
... | ret r1 | ret r2 with r1 ≟ r2
-- Branch: They agree (r1 ≡ r2)
... | yes refl =
    case eq-f of λ where
      refl → -- This unifies r1 with r
        inj₁ (_ , bStep (sRet p-eq) big-step) -- Or inj₂, both work!

-- Branch: They disagree (r1 ≢ r2)
-- The definition says this results in 'Stop'.
-- Stop cannot perform an 'sRet' step, so this case is impossible.
... | no  neq =
    case eq-f of λ where
      () -- force (P □ Q) is Stop, which != ret r

-- Case: P terminates, Q is offering something else. Under the new _□_,
-- these all reduce to non-ret shapes (mix or ndbr) so sRet is impossible.
-- For ret|vis: force (P □ Q) = (Q ▷ P).force = mix fQ P.
-- For ret|ndbr: force (P □ Q) = ndbr (mergeNdbr-vis-L P fQ) ... .
-- For vis|ret: force (P □ Q) = (P ▷ Q).force = mix fP Q.
-- For ndbr|ret: force (P □ Q) = ndbr (mergeNdbr-vis-R fP Q) ... .
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = √ r} (sRet eq-f) big-step) | ret r1 | vis fQ =
    case eq-f of λ ()

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = √ r} (sRet eq-f) big-step) | ret r1 | ndbr fQ wi wa wp =
    case eq-f of λ ()

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = √ r} (sRet eq-f) big-step) | vis fP | ret r2 =
    case eq-f of λ ()

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = √ r} (sRet eq-f) big-step) | ndbr fP wi wa wp | ret r2 =
    case eq-f of λ ()

-- NEW: sil-shape absurds for sRet.
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | ret _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | sil _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | vis _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | ndbr _ _ _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | mix _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | sil _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | sil _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | sil _ =
    case eq-f of λ ()
-- mix-shape absurds for sRet.
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | mix _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | mix _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ret _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | vis _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ =
    case eq-f of λ ()
-- Remaining non-mix non-ret|ret absurds (vis|vis, vis|ndbr etc.).
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | vis _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ =
    case eq-f of λ ()
ExternalChoice-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ =
    case eq-f of λ ()

-- 5. Case: Non-deterministic branching (ndbr)
-- If P is an ndbr, the whole choice becomes an ndbr of (Pi □ Q).
-- eq-f: ITree.force p ≡ ndbr f wi wa prf
-- eq-j: f i a ≡ just t′
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- 5.1. Case: P is vis, Q is ndbr
-- Definition uses: fQ' i a = just (P □ Q')
... | vis fP | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ trP) → inj₁ trP
      (inj₂ (t'' , trQ)) → inj₂ (t'' , bTau (sNdbr q-eq fq-eq) trQ)
-- If the branch is nothing, eq-j (which is fQ' i a ≡ just t') is impossible
... | nothing | ()

-- 5.2. Case: P is ndbr, Q is vis
-- Definition uses: fP' i a = just (P' □ Q)
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis fQ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (t'' , trP)) → inj₁ (t'' , bTau (sNdbr p-eq fp-eq) trP)
      (inj₂ trQ) → inj₂ trQ
-- If the branch is nothing, eq-j (which is fQ' i a ≡ just t') is impossible
... | nothing | ()

-- 5.3. Case: Both are ndbr (The mergeNdbr rule)
-- eq-f  : ITree.force (P □ Q) ≡ ndbr (mergeNdbr fP fQ) ((AP×AQ, pair iP iQ)) (waP,waQ) go-prf
-- eq-j  : (mergeNdbr fP fQ) i a ≡ just t′
-- i, a  : the branch actually taken inside (P □ Q)
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  -- i must be a pair index for mergeNdbr to give `just`; case on it:
  with i | a
-- i is a base or fin index → mergeNdbr returns nothing → eq-j is impossible
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
-- i is a pair index: i = (AP' × AQ' , pair iP' iQ'), a = (aP' , aQ')
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  -- now case-split on fP (AP', iP') aP' and fQ (AQ', iQ') aQ'
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
-- just P' / nothing → mergeNdbr = just P', so eq-j : just P' ≡ just t''
... | just P' | nothing | refl =
    inj₁ (_ , bTau (sNdbr p-eq fp'-eq) big-step)
-- nothing / just Q' → mergeNdbr = just Q', so eq-j : just Q' ≡ just t''
... | nothing  | just Q'  | refl =
    inj₂ (_ , bTau (sNdbr q-eq fq'-eq) big-step)
-- just P' / just Q' → mergeNdbr = just (P' □ Q'), so eq-j : just (P' □ Q') ≡ just t''
... | just P'  | just Q'  | refl =
    case ExternalChoice-trace-aux P' Q' big-step of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bTau (sNdbr p-eq fp'-eq) trP)
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bTau (sNdbr q-eq fq'-eq) trQ)
-- nothing / nothing → mergeNdbr = nothing, so eq-j : nothing ≡ just t'' — impossible
... | nothing  | nothing  | ()

-- 5.4. If P is silent, the choice takes an sSil step, not sNdbr.
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | sil P' | _ | ()

-- 5.5. If P is stable but Q is silent, the choice takes an sSil step.
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | ret _ | sil Q' | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | vis _ | sil Q' | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | ndbr _ _ _ _ | sil Q' | ()

-- 5.6. Both ready to terminate
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
-- Case: They agree. force (P □ Q) reduces to (ret r1)
-- Agda sees: (ret r1 ≡ ndbr ...) which is clearly impossible.
... | yes refl rewrite p-eq | q-eq with r1 ≟ r1
-- match with r1 ≟ r1: yes
...                                                     | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match with r1 ≟ r1: no
                                                        | no neq = ⊥-elim (neq refl)

-- Case: They disagree. force (P □ Q) reduces to (Stop .force)
-- Agda sees: (Stop .force ≡ ndbr ...) which is also impossible.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _
-- match with r1 ≟ r2: no
                       | no neq rewrite p-eq | q-eq with r1 ≟ r2
-- match the 2nd with r1 ≟ r2 : yes
...                                                    | yes refl with eq-f
...                                                                 | ()

ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _
-- match the 2nd with r1 ≟ r2 : no
                                                         | no neq with eq-f
...                                                                | refl with i | a | eq-j
-- i must be fin-indexed for br2 to return just
...                                                                            | (_ , fin) | lift fzero        | refl = inj₁ (_ , big-step)
...                                                                            | (_ , fin) | lift (fsuc fzero) | refl = inj₂ (_ , big-step)
-- all other fin cases return nothing, so eq-j : nothing ≡ just t′ is impossible
...                                                                            | (_ , fin) | lift (fsuc (fsuc _)) | ()
-- base and pair cases also return nothing
...                                                                            | (_ , base _)    | _ | ()
...                                                                            | (_ , pair _ _)  | _ | ()

-- 5.7.
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | ret _ | vis _ | ()

-- 5.8.
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | vis _ | ret _ | ()

-- 5.9. NEW: ret | ndbr — Q-distribution
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ trP)         → inj₁ trP
      (inj₂ (t'' , trQ)) → inj₂ (t'' , bTau (sNdbr q-eq fq-eq) trQ)
... | nothing | ()

-- 5.10. NEW: ndbr | ret — P-distribution
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (t'' , trP)) → inj₁ (t'' , bTau (sNdbr p-eq fp-eq) trP)
      (inj₂ trQ)         → inj₂ trQ
... | nothing | ()

-- 5.11. NEW: mix | ndbr — Q distributes; mix's vis-side absent at this τ-step.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ trP)         → inj₁ trP
      (inj₂ (t'' , trQ)) → inj₂ (t'' , bTau (sNdbr q-eq fq-eq) trQ)
... | nothing | ()

-- 5.12. NEW: ndbr | mix — P distributes.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (t'' , trP)) → inj₁ (t'' , bTau (sNdbr p-eq fp-eq) trP)
      (inj₂ trQ)         → inj₂ trQ
... | nothing | ()

-- 5.13. Mix absurds for sNdbr: cases where new _□_ produces non-ndbr shapes.
-- mix | mix → mix shape; mix | ret → mix; mix | vis → mix; vis | mix → mix; ret | mix → mix.
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | mix _ _ | ret _ | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | mix _ _ | vis _ | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | mix _ _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | mix _ _ | sil _ | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | ret _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step)
  | vis _ | mix _ _ | ()

-- ----- 6. NEW step: bTau via sMixSlide. force (P □ Q) ≡ mix _ Qt, slide goes to Qt. -----
-- Productive cases (mix-producing under new _□_):
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix: force = mix fQ (P □ Q'). Slide to (P □ Q').
... | ret _ | mix _ Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sMixSlide q-eq) trQ)
-- vis | mix: same.
... | vis _ | mix _ Q' | refl =
    case ExternalChoice-trace-aux P Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sMixSlide q-eq) trQ)
-- mix | ret: force = mix fP (P' □ Q). Slide to (P' □ Q).
... | mix _ P' | ret _ | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , bTau (sMixSlide p-eq) trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , trQ)
-- mix | vis: same.
... | mix _ P' | vis _ | refl =
    case ExternalChoice-trace-aux P' Q big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , bTau (sMixSlide p-eq) trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , trQ)
-- mix | mix: force = mix _ (P' □ Q'). Slide to (P' □ Q'). Either P-slide or Q-slide.
... | mix _ P' | mix _ Q' | refl =
    case ExternalChoice-trace-aux P' Q' big-step of λ where
      (inj₁ (_ , trP)) → inj₁ (_ , bTau (sMixSlide p-eq) trP)
      (inj₂ (_ , trQ)) → inj₂ (_ , bTau (sMixSlide q-eq) trQ)
-- ret | vis: force = mix fQ P. Slide lands on P (the ret side).
... | ret _ | vis _ | refl = inj₁ (_ , big-step)
-- vis | ret: force = mix fP Q. Slide lands on Q (the ret side).
... | vis _ | ret _ | refl = inj₂ (_ , big-step)
-- Absurd: remaining non-mix shapes — explicit function clauses after the inner ret|ret split.
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | sil _ | _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ret _ | sil _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | vis _ | sil _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | vis _ | vis _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | mix _ _ | sil _ | ()
ExternalChoice-trace-aux P Q (bTau (sMixSlide eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
-- ret|ret: split on r≟r' since force is ret (if r≟r') or ndbr (else); both non-mix.
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sMixSlide eq-f) big-step) | ret r1 | ret r2 | _ with r1 ≟ r2
... | yes refl rewrite p-eq | q-eq with r1 ≟ r1
...                                  | yes refl with eq-f
...                                                | ()
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sMixSlide eq-f) big-step)
  | ret r1 | ret r2 | _ | _ | no neq = ⊥-elim (neq refl)
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bTau (sMixSlide eq-f) big-step)
  | ret r1 | ret r2 | _ | no neq rewrite p-eq | q-eq with r1 ≟ r2
...                                                    | yes refl = ⊥-elim (neq refl)
...                                                    | no _ with eq-f
...                                                              | ()

-- ----- 7. NEW step: bStep via sMixVis. force (P □ Q) ≡ mix f Qt, f at a ≡ just t'. -----
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix fQ Q': force = mix fQ (P □ Q'). Q does the visible step.
... | ret _ | mix fQ _ | refl with fQ at a in fq-eq | eq-j
... | just _  | refl =
    inj₂ (_ , bStep (sMixVis q-eq fq-eq) big-step)
... | nothing | ()
-- vis | mix: fQ is the active vis side.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _ | mix fQ _ | refl with fQ at a in fq-eq | eq-j
... | just _  | refl =
    inj₂ (_ , bStep (sMixVis q-eq fq-eq) big-step)
... | nothing | ()
-- mix | ret: P does the visible step.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with fP at a in fp-eq | eq-j
... | just _  | refl =
    inj₁ (_ , bStep (sMixVis p-eq fp-eq) big-step)
... | nothing | ()
-- mix | vis: P does the visible step.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis _ | refl with fP at a in fp-eq | eq-j
... | just _  | refl =
    inj₁ (_ , bStep (sMixVis p-eq fp-eq) big-step)
... | nothing | ()
-- mix | mix: force = mix (mergeVis fP fQ) (P' □ Q'). Either side can fire.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _  | nothing | refl =
    inj₁ (_ , bStep (sMixVis p-eq fp-eq) big-step)
... | nothing | just _  | refl =
    inj₂ (_ , bStep (sMixVis q-eq fq-eq) big-step)
-- both fire — pick either side; the merged result is internally nondeterministic.
... | just _  | just _  | refl =
    case InternalChoice-trace _ _ (_ , big-step) of λ where
      (inj₁ (t-end , trP)) → inj₁ (t-end , bStep (sMixVis p-eq fp-eq) trP)
      (inj₂ (t-end , trQ)) → inj₂ (t-end , bStep (sMixVis q-eq fq-eq) trQ)
... | nothing | nothing | ()
-- Absurd: non-mix shapes for sMixVis.
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | sil _ | _ | ()
-- ret|ret: force=ret (if r≟r') or ndbr (else); both non-mix. Split needed.
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ with r1 ≟ r2
... | yes refl rewrite p-eq | q-eq with r1 ≟ r1
...                                  | yes refl with eq-f
...                                                | ()
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | _ | no neq = ⊥-elim (neq refl)
ExternalChoice-trace-aux {ℓr = ℓr} {I = I} {R = R} {s = s} {{dec}} P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ret r1 | ret r2 | _ | no neq rewrite p-eq | q-eq with r1 ≟ r2
...                                                    | yes refl = ⊥-elim (neq refl)
...                                                    | no _ with eq-f
...                                                              | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ret _ | sil _ | ()
-- ret | vis: force(P □ Q) = mix fQ P. Q does the visible step via Q.force=vis.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis _ | refl = inj₂ (_ , bStep (sVis q-eq eq-j) big-step)
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ret _ | ndbr _ _ _ _ | ()
-- vis | ret: force(P □ Q) = mix fP Q. P does the visible step via P.force=vis.
ExternalChoice-trace-aux {I = I} {R = R} {s = s} P Q (bStep {el = el} (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis _ | ret _ | refl = inj₁ (_ , bStep (sVis p-eq eq-j) big-step)
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis _ | sil _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis _ | vis _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ret _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ndbr _ _ _ _ | sil _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ndbr _ _ _ _ | vis _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | ndbr _ _ _ _ | mix _ _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix _ _ | sil _ | ()
ExternalChoice-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix _ _ | ndbr _ _ _ _ | ()

ExternalChoice-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  {s : List (Event√ E R)}
  ⦃ dec : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → traces {I = ExtI I} {R = R} (_□_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s
ExternalChoice-trace P Q (_ , bs) = ExternalChoice-trace-aux P Q bs

------------------------------------------------------------------------
-- Introduction direction for `ExternalChoice-trace`.
--
-- The proof is large (25 sub-cases of (force P × force Q)).  We build
-- a small library of `force-□-*` helpers first so each sub-case
-- can use them directly.  Each helper takes assumptions about the
-- force shapes and produces the union's force shape.
--
-- The outer ExtChoice-trace-introL/R declarations carry
-- NON_TERMINATING because some sub-cases recurse on Q (not on the
-- bigstep), and Agda's structural termination checker cannot see
-- the well-foundedness.  The lemmas are morally productive: for any
-- non-divergent Q, the recursion terminates.
------------------------------------------------------------------------

private

  -- force (P □ Q) ≡ sil (P′ □ Q) when force P ≡ sil P′ (regardless of Q).
  force-□-sil-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                  {P P′ Q : ITree E (ExtI I) R}
                → ITree.force P ≡ sil P′
                → ITree.force (P □ Q) ≡ sil (P′ □ Q)
  force-□-sil-L {P = P} {Q = Q} eqP with P .force
  ... | sil _         = case eqP of λ { refl → refl }
  ... | ret _         = case eqP of λ ()
  ... | vis _         = case eqP of λ ()
  ... | ndbr _ _ _ _  = case eqP of λ ()
  ... | mix _ _       = case eqP of λ ()

  -- force (P □ Q) ≡ sil (P □ Q′) when force P ≡ ret r, force Q ≡ sil Q′.
  force-□-sil-R-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                       {P Q Q′ : ITree E (ExtI I) R} {r : R}
                    → ITree.force P ≡ ret r
                    → ITree.force Q ≡ sil Q′
                    → ITree.force (P □ Q) ≡ sil (P □ Q′)
  force-□-sil-R-ret {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ret _        | sil _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ret _        | ret _         = case eqQ of λ ()
  ... | ret _        | vis _         = case eqQ of λ ()
  ... | ret _        | ndbr _ _ _ _  = case eqQ of λ ()
  ... | ret _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ sil (P □ Q′) when force P ≡ vis fP, force Q ≡ sil Q′.
  force-□-sil-R-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                       {P Q Q′ : ITree E (ExtI I) R}
                       {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                    → ITree.force P ≡ vis fP
                    → ITree.force Q ≡ sil Q′
                    → ITree.force (P □ Q) ≡ sil (P □ Q′)
  force-□-sil-R-vis {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | vis _        | sil _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | vis _        | ret _         = case eqQ of λ ()
  ... | vis _        | vis _         = case eqQ of λ ()
  ... | vis _        | ndbr _ _ _ _  = case eqQ of λ ()
  ... | vis _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ sil (P □ Q′) when force P ≡ ndbr …, force Q ≡ sil Q′.
  force-□-sil-R-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q Q′ : ITree E (ExtI I) R}
                        {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                        {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                        {wp : Is-just (fP wi wa)}
                     → ITree.force P ≡ ndbr fP wi wa wp
                     → ITree.force Q ≡ sil Q′
                     → ITree.force (P □ Q) ≡ sil (P □ Q′)
  force-□-sil-R-ndbr {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ndbr _ _ _ _ | sil _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | ret _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | vis _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _  = case eqQ of λ ()
  ... | ndbr _ _ _ _ | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ sil (P □ Q′) when force P ≡ mix fP P′, force Q ≡ sil Q′.
  force-□-sil-R-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                       {P P′ Q Q′ : ITree E (ExtI I) R}
                       {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                    → ITree.force P ≡ mix fP P′
                    → ITree.force Q ≡ sil Q′
                    → ITree.force (P □ Q) ≡ sil (P □ Q′)
  force-□-sil-R-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | mix _ _      | sil _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | ret _         = case eqQ of λ ()
  ... | mix _ _      | vis _         = case eqQ of λ ()
  ... | mix _ _      | ndbr _ _ _ _  = case eqQ of λ ()
  ... | mix _ _      | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fP Q when force P ≡ vis fP, force Q ≡ ret r.
  force-□-mix-vis-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q : ITree E (ExtI I) R}
                        {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {r : R}
                      → ITree.force P ≡ vis fP
                      → ITree.force Q ≡ ret r
                      → ITree.force (P □ Q) ≡ mix fP Q
  force-□-mix-vis-ret {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | vis _        | ret _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | vis _        | sil _         = case eqQ of λ ()
  ... | vis _        | vis _         = case eqQ of λ ()
  ... | vis _        | ndbr _ _ _ _  = case eqQ of λ ()
  ... | vis _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fQ (P □ Q′) when force P ≡ vis fP, force Q ≡ mix fQ Q′.
  force-□-mix-vis-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q Q′ : ITree E (ExtI I) R}
                        {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                      → ITree.force P ≡ vis fP
                      → ITree.force Q ≡ mix fQ Q′
                      → ITree.force (P □ Q) ≡ mix fQ (P □ Q′)
  force-□-mix-vis-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | vis _        | mix _ _       = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | vis _        | sil _         = case eqQ of λ ()
  ... | vis _        | ret _         = case eqQ of λ ()
  ... | vis _        | vis _         = case eqQ of λ ()
  ... | vis _        | ndbr _ _ _ _  = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fQ P when force P ≡ ret r, force Q ≡ vis fQ.
  force-□-mix-ret-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q : ITree E (ExtI I) R}
                        {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {r : R}
                      → ITree.force P ≡ ret r
                      → ITree.force Q ≡ vis fQ
                      → ITree.force (P □ Q) ≡ mix fQ P
  force-□-mix-ret-vis {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ret _        | vis _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ret _        | sil _         = case eqQ of λ ()
  ... | ret _        | ret _         = case eqQ of λ ()
  ... | ret _        | ndbr _ _ _ _  = case eqQ of λ ()
  ... | ret _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fQ (P □ Q′) when force P ≡ ret r, force Q ≡ mix fQ Q′.
  force-□-mix-ret-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q Q′ : ITree E (ExtI I) R}
                        {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {r : R}
                      → ITree.force P ≡ ret r
                      → ITree.force Q ≡ mix fQ Q′
                      → ITree.force (P □ Q) ≡ mix fQ (P □ Q′)
  force-□-mix-ret-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ret _        | mix _ _       = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ret _        | sil _         = case eqQ of λ ()
  ... | ret _        | ret _         = case eqQ of λ ()
  ... | ret _        | vis _         = case eqQ of λ ()
  ... | ret _        | ndbr _ _ _ _  = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fP (P′ □ Q) when force P ≡ mix fP P′, force Q ≡ ret r.
  force-□-mix-mix-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P P′ Q : ITree E (ExtI I) R}
                        {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {r : R}
                      → ITree.force P ≡ mix fP P′
                      → ITree.force Q ≡ ret r
                      → ITree.force (P □ Q) ≡ mix fP (P′ □ Q)
  force-□-mix-mix-ret {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | mix _ _      | ret _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | sil _         = case eqQ of λ ()
  ... | mix _ _      | vis _         = case eqQ of λ ()
  ... | mix _ _      | ndbr _ _ _ _  = case eqQ of λ ()
  ... | mix _ _      | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ mix fP (P′ □ Q) when force P ≡ mix fP P′, force Q ≡ vis fQ.
  force-□-mix-mix-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P P′ Q : ITree E (ExtI I) R}
                        {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                        {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                      → ITree.force P ≡ mix fP P′
                      → ITree.force Q ≡ vis fQ
                      → ITree.force (P □ Q) ≡ mix fP (P′ □ Q)
  force-□-mix-mix-vis {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | mix _ _      | vis _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | sil _         = case eqQ of λ ()
  ... | mix _ _      | ret _         = case eqQ of λ ()
  ... | mix _ _      | ndbr _ _ _ _  = case eqQ of λ ()
  ... | mix _ _      | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ mix (λ Ae → mergeVis (fP Ae) (fQ Ae)) (P′ □ Q′)
  -- when force P ≡ mix fP P′, force Q ≡ mix fQ Q′.
  force-□-mix-mix-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P P′ Q Q′ : ITree E (ExtI I) R}
                        {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                      → ITree.force P ≡ mix fP P′
                      → ITree.force Q ≡ mix fQ Q′
                      → ITree.force (P □ Q) ≡ mix (λ Ae → mergeVis (fP Ae) (fQ Ae)) (P′ □ Q′)
  force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | mix _ _      | mix _ _       = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | sil _         = case eqQ of λ ()
  ... | mix _ _      | ret _         = case eqQ of λ ()
  ... | mix _ _      | vis _         = case eqQ of λ ()
  ... | mix _ _      | ndbr _ _ _ _  = case eqQ of λ ()

  -- force (P □ Q) ≡ vis (λ Ae → mergeVis (fP Ae) (fQ Ae))
  -- when force P ≡ vis fP, force Q ≡ vis fQ.
  force-□-vis-merge : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                      {P Q : ITree E (ExtI I) R}
                      {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                    → ITree.force P ≡ vis fP
                    → ITree.force Q ≡ vis fQ
                    → ITree.force (P □ Q) ≡ vis (λ Ae → mergeVis (fP Ae) (fQ Ae))
  force-□-vis-merge {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | vis _        | vis _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | vis _        | sil _         = case eqQ of λ ()
  ... | vis _        | ret _         = case eqQ of λ ()
  ... | vis _        | ndbr _ _ _ _  = case eqQ of λ ()
  ... | vis _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)
  -- when force P ≡ ret r, force Q ≡ ndbr fQ wi wa wp.
  force-□-ndbr-vis-L-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P Q : ITree E (ExtI I) R} {r : R}
                            {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fQ wi wa)}
                          → ITree.force P ≡ ret r
                          → ITree.force Q ≡ ndbr fQ wi wa wp
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-L P fQ) wi wa
                                   (mergeNdbr-vis-L-witness P fQ wp)
  force-□-ndbr-vis-L-ret {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ret _        | ndbr _ _ _ _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ret _        | sil _         = case eqQ of λ ()
  ... | ret _        | ret _         = case eqQ of λ ()
  ... | ret _        | vis _         = case eqQ of λ ()
  ... | ret _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)
  -- when force P ≡ vis fP, force Q ≡ ndbr fQ wi wa wp.
  force-□-ndbr-vis-L-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P Q : ITree E (ExtI I) R}
                            {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                            {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fQ wi wa)}
                          → ITree.force P ≡ vis fP
                          → ITree.force Q ≡ ndbr fQ wi wa wp
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-L P fQ) wi wa
                                   (mergeNdbr-vis-L-witness P fQ wp)
  force-□-ndbr-vis-L-vis {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | vis _        | ndbr _ _ _ _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | vis _        | sil _         = case eqQ of λ ()
  ... | vis _        | ret _         = case eqQ of λ ()
  ... | vis _        | vis _         = case eqQ of λ ()
  ... | vis _        | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)
  -- when force P ≡ mix fP P′, force Q ≡ ndbr fQ wi wa wp.
  force-□-ndbr-vis-L-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P P′ Q : ITree E (ExtI I) R}
                            {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                            {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fQ wi wa)}
                          → ITree.force P ≡ mix fP P′
                          → ITree.force Q ≡ ndbr fQ wi wa wp
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-L P fQ) wi wa
                                   (mergeNdbr-vis-L-witness P fQ wp)
  force-□-ndbr-vis-L-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | mix _ _      | ndbr _ _ _ _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | _            = case eqP of λ ()
  ... | mix _ _      | sil _         = case eqQ of λ ()
  ... | mix _ _      | ret _         = case eqQ of λ ()
  ... | mix _ _      | vis _         = case eqQ of λ ()
  ... | mix _ _      | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)
  -- when force P ≡ ndbr fP wi wa wp, force Q ≡ ret r.
  force-□-ndbr-vis-R-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P Q : ITree E (ExtI I) R} {r : R}
                            {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fP wi wa)}
                          → ITree.force P ≡ ndbr fP wi wa wp
                          → ITree.force Q ≡ ret r
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-R fP Q) wi wa
                                   (mergeNdbr-vis-R-witness fP Q wp)
  force-□-ndbr-vis-R-ret {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ndbr _ _ _ _ | ret _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | sil _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | vis _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _  = case eqQ of λ ()
  ... | ndbr _ _ _ _ | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)
  -- when force P ≡ ndbr fP wi wa wp, force Q ≡ vis fQ.
  force-□-ndbr-vis-R-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P Q : ITree E (ExtI I) R}
                            {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fP wi wa)}
                          → ITree.force P ≡ ndbr fP wi wa wp
                          → ITree.force Q ≡ vis fQ
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-R fP Q) wi wa
                                   (mergeNdbr-vis-R-witness fP Q wp)
  force-□-ndbr-vis-R-vis {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ndbr _ _ _ _ | vis _         = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | sil _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ret _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _  = case eqQ of λ ()
  ... | ndbr _ _ _ _ | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)
  -- when force P ≡ ndbr fP wi wa wp, force Q ≡ mix fQ Q′.
  force-□-ndbr-vis-R-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                            {P Q Q′ : ITree E (ExtI I) R}
                            {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                            {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
                            {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                            {wp : Is-just (fP wi wa)}
                          → ITree.force P ≡ ndbr fP wi wa wp
                          → ITree.force Q ≡ mix fQ Q′
                          → ITree.force (P □ Q) ≡
                              ndbr (mergeNdbr-vis-R fP Q) wi wa
                                   (mergeNdbr-vis-R-witness fP Q wp)
  force-□-ndbr-vis-R-mix {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ndbr _ _ _ _ | mix _ _       = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | sil _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ret _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | vis _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ndbr _ _ _ _  = case eqQ of λ ()

  -- Given fP i a ≡ just t', mergeNdbr-vis-R fP Q i a ≡ just (t' □ Q).
  -- Used in the sNdbr | (ret/vis/mix) sub-cases of ExtChoice-trace-introL.
  merged-branch-eq-vis-R
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {Q : ITree E (ExtI I) R}
      (fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
      {i : AnyTypes (ExtI I)} {a : proj₁ i} {t′ : ITree E (ExtI I) R}
    → fP i a ≡ just t′
    → mergeNdbr-vis-R fP Q i a ≡ just (t′ □ Q)
  merged-branch-eq-vis-R fP {i = i} {a = a} eq-j with fP i a
  ... | just _  = case eq-j of λ { refl → refl }
  ... | nothing = case eq-j of λ ()

  -- Given fQ i a ≡ just t', mergeNdbr-vis-L P fQ i a ≡ just (P □ t').
  -- Used in the bStep (sVis …) | ndbr sub-case of ExtChoice-trace-introL.
  merged-branch-eq-vis-L
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P : ITree E (ExtI I) R}
      (fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
      {i : AnyTypes (ExtI I)} {a : proj₁ i} {t′ : ITree E (ExtI I) R}
    → fQ i a ≡ just t′
    → mergeNdbr-vis-L P fQ i a ≡ just (P □ t′)
  merged-branch-eq-vis-L fQ {i = i} {a = a} eq-j with fQ i a
  ... | just _  = case eq-j of λ { refl → refl }
  ... | nothing = case eq-j of λ ()

  -- When fP at a ≡ just t' and fQ at a ≡ nothing,
  -- (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just t'.
  -- Used in the bStep (sVis …) | vis sub-case (fQ-branch = nothing).
  merged-at-a-nothing
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {at : AnyTypes E} {a : proj₁ at} {t′ : ITree E (ExtI I) R}
    → fP at a ≡ just t′
    → fQ at a ≡ nothing
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just t′
  merged-at-a-nothing {fP = fP} {fQ = fQ} {at = at} {a = a} eqP eqQ
    rewrite eqP | eqQ = refl

  -- When fP at a ≡ just t' and fQ at a ≡ just U,
  -- (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just (t' ⊓ U).
  -- Used in the bStep (sVis …) | vis sub-case (fQ-branch = just U).
  merged-at-a-just
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {at : AnyTypes E} {a : proj₁ at} {t′ U : ITree E (ExtI I) R}
    → fP at a ≡ just t′
    → fQ at a ≡ just U
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just (t′ ⊓ U)
  merged-at-a-just {fP = fP} {fQ = fQ} {at = at} {a = a} eqP eqQ
    rewrite eqP | eqQ = refl

  -- When fP at a ≡ nothing and fQ at a ≡ just t',
  -- (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just t'.
  -- Used in the bStep (sVis …) | vis sub-case of introR (fP-branch = nothing).
  merged-at-a-nothing-R
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {at : AnyTypes E} {a : proj₁ at} {t′ : ITree E (ExtI I) R}
    → fP at a ≡ nothing
    → fQ at a ≡ just t′
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just t′
  merged-at-a-nothing-R {fP = fP} {fQ = fQ} {at = at} {a = a} eqP eqQ
    rewrite eqP | eqQ = refl

  -- When fP at a ≡ just U and fQ at a ≡ just t',
  -- (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just (U ⊓ t').
  -- Used in the bStep (sVis …) | vis sub-case of introR (fP-branch = just U).
  merged-at-a-just-R
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {at : AnyTypes E} {a : proj₁ at} {t′ U : ITree E (ExtI I) R}
    → fP at a ≡ just U
    → fQ at a ≡ just t′
    → (λ Ae → mergeVis (fP Ae) (fQ Ae)) at a ≡ just (U ⊓ t′)
  merged-at-a-just-R {fP = fP} {fQ = fQ} {at = at} {a = a} eqP eqQ
    rewrite eqP | eqQ = refl

  -- Given fP (AP, iP) aP ≡ just P' and fQ (AQ, iQ) aQ ≡ just Q',
  -- mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (aP , aQ) ≡ just (P' □ Q').
  -- Used in the sNdbr | ndbr sub-case of ExtChoice-trace-introL.
  mergeNdbr-branch-both-just
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      (fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
      {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ}
      {aP : AP} {aQ : AQ}
      {P′ Q′ : ITree E (ExtI I) R}
    → fP (AP , iP) aP ≡ just P′
    → fQ (AQ , iQ) aQ ≡ just Q′
    → mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (aP , aQ) ≡ just (P′ □ Q′)
  mergeNdbr-branch-both-just fP fQ {AP = AP} {AQ = AQ} {iP = iP} {iQ = iQ} {aP = aP} {aQ = aQ} eqP eqQ
    with fP (AP , iP) aP | fQ (AQ , iQ) aQ
  ... | just _  | just _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | just _  | nothing = case eqQ of λ ()
  ... | nothing | _       = case eqP of λ ()

  -- force (P □ Q) ≡ ndbr (mergeNdbr fP fQ) ((AP × AQ) , pair iP iQ) (waP , waQ)
  --                      (mergeNdbr-witness fP fQ wpP wpQ)
  -- when force P ≡ ndbr fP (AP , iP) waP wpP, force Q ≡ ndbr fQ (AQ , iQ) waQ wpQ.
  force-□-ndbr-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                      {P Q : ITree E (ExtI I) R}
                      {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                      {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
                      {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ}
                      {waP : AP} {waQ : AQ}
                      {wpP : Is-just (fP (AP , iP) waP)}
                      {wpQ : Is-just (fQ (AQ , iQ) waQ)}
                    → ITree.force P ≡ ndbr fP (AP , iP) waP wpP
                    → ITree.force Q ≡ ndbr fQ (AQ , iQ) waQ wpQ
                    → ITree.force (P □ Q) ≡
                        ndbr (mergeNdbr fP fQ) ((AP × AQ) , pair iP iQ) (waP , waQ)
                             (mergeNdbr-witness fP fQ wpP wpQ)
  force-□-ndbr-ndbr {P = P} {Q = Q} eqP eqQ with P .force | Q .force
  ... | ndbr _ _ _ _ | ndbr _ _ _ _  = case eqP of λ { refl → case eqQ of λ { refl → refl } }
  ... | sil _        | _             = case eqP of λ ()
  ... | ret _        | _             = case eqP of λ ()
  ... | vis _        | _             = case eqP of λ ()
  ... | mix _ _      | _             = case eqP of λ ()
  ... | ndbr _ _ _ _ | sil _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | ret _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | vis _         = case eqQ of λ ()
  ... | ndbr _ _ _ _ | mix _ _       = case eqQ of λ ()

  -- force (P □ Q) ≡ ret r when force P ≡ ret r, force Q ≡ ret r (same value).
  -- Used in the bStep (sRet …) | ret (yes refl) sub-case of ExtChoice-trace-introL.
  force-□-ret-ret-yes : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                        {P Q : ITree E (ExtI I) R} {r : R}
                      → ITree.force P ≡ ret r
                      → ITree.force Q ≡ ret r
                      → ITree.force (P □ Q) ≡ ret r
  force-□-ret-ret-yes {P = P} {Q = Q} {r = r} eqP eqQ
    with ITree.force P | eqP | ITree.force Q | eqQ
  ... | ret .r | refl | ret .r | refl with r ≟ r
  ...   | yes refl = refl
  ...   | no  neq  = ⊥-elim (neq refl)

  -- force (P □ Q) ≡ ndbr (br2 P Q) (Lift _ (Fin 2) , fin) (lift fzero) (any-just tt₀)
  -- when force P ≡ ret r, force Q ≡ ret r′, r ≢ r′.
  -- Used in the bStep (sRet …) | ret (no neq) sub-case of ExtChoice-trace-introL.
  force-□-ret-ret-no : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                       {P Q : ITree E (ExtI I) R} {r r′ : R}
                     → ITree.force P ≡ ret r
                     → ITree.force Q ≡ ret r′
                     → ¬ (r ≡ r′)
                     → ITree.force (P □ Q) ≡
                         ndbr (br2 P Q) (Lift _ (Fin 2) , fin) (lift fzero) (any-just tt₀)
  force-□-ret-ret-no {P = P} {Q = Q} {r = r} {r′ = r′} eqP eqQ neq
    with ITree.force P | eqP | ITree.force Q | eqQ
  ... | ret .r | refl | ret .r′ | refl with r ≟ r′
  ...   | yes p  = ⊥-elim (neq p)
  ...   | no  _  = refl

------------------------------------------------------------------------
-- ExtChoice-trace-introL : traces P s → traces (P □ Q) s
-- ExtChoice-trace-introR : symmetric, traces Q s → traces (P □ Q) s
--
-- NON_TERMINATING: some sub-cases recurse on Q (peeling Q's silent
-- steps) rather than on the bigstep.  For any non-divergent Q, the
-- recursion terminates; the pragma is needed because Agda's
-- structural termination checker cannot see this.
------------------------------------------------------------------------

-- introL-other: only remaining postulate, used for the sNdbr | ndbr (pair-indexed)
-- sub-case of ExtChoice-trace-introL (left for Phase 2 follow-up).
-- introR-ndbr-ndbr: symmetric postulate for the sNdbr | ndbr sub-case of introR
-- (Q takes ndbr step, P is ndbr; pair-indexed merge; left for Phase 2 follow-up).
private
  postulate
    introL-other : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                     ⦃ _ : DecEq R ⦄
                     {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
                   → traces P s → traces (P □ Q) s
    introR-ndbr-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                         ⦃ _ : DecEq R ⦄
                         {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
                       → traces Q s → traces (P □ Q) s

{-# NON_TERMINATING #-}
ExtChoice-trace-introL : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    ⦃ dec : DecEq R ⦄
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces P s → traces (P □ Q) s

{-# NON_TERMINATING #-}
ExtChoice-trace-introR : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    ⦃ dec : DecEq R ⦄
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces Q s → traces (P □ Q) s

ExtChoice-trace-introL (T , bNil) = _ , bNil
ExtChoice-trace-introL {P = P} {Q = Q} (T , bTau (sSil {t = P′} eqP) bs) =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P′} {Q = Q} (T , bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- Phase 2: sNdbr — P takes a τ via ndbr; case-split on Q .force
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bTau (sNdbr {f = fP} {wi = wi} {wa = wa} {prf = wp}
                                         {i = i} {a = a} {t′ = t′}
                                         eqP eq-j) bs)
  with Q .force in eqQ
-- Q is sil: the union also steps silently; recurse with Q peel off Q's sil
... | sil Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bTau (sNdbr {f = fP} {wi = wi} {wa = wa} {prf = wp}
                                        {i = i} {a = a} {t′ = t′}
                                        eqP eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-R-ndbr {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- Q is ret: union is ndbr (mergeNdbr-vis-R fP Q); recurse with t' □ Q
... | ret r =
  let (T″ , bs″) = ExtChoice-trace-introL {P = t′} {Q = Q} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-R-witness fP Q wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-R-ret {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-R fP eq-j))
                bs″
-- Q is vis: same shape as ret
... | vis fQ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = t′} {Q = Q} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-R-witness fP Q wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-R-vis {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-R fP eq-j))
                bs″
-- Q is ndbr: pair-indexed merge sub-case.
-- TODO: constructing the pair-indexed sNdbr branch for (mergeNdbr fP fQ) requires
-- exposing the ExtI constructors via with-abstraction on i and wi′ so that
-- pair (proj₂ i) (proj₂ wi′) is well-typed as ExtI I (AI × AQ). Postulated.
... | ndbr fQ wi′ wa′ wp′ =
  introL-other (T , bTau (sNdbr {f = fP} {wi = wi} {wa = wa} {prf = wp}
                                  {i = i} {a = a} {t′ = t′} eqP eq-j) bs)
-- Q is mix: same shape as ret/vis
... | mix fQ Q′₂ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = t′} {Q = Q} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-R-witness fP Q wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-R-mix {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-R fP eq-j))
                bs″
-- Phase 3: bStep (sVis …) — P fires a visible event; case-split on Q .force.
-- The vis|vis sub-case uses a nested `with` on fQ at a; the ndbr and mix
-- alternatives continue the outer `with Q .force in eqQ` series afterwards.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                        eqP eq-j) bs)
  with Q .force in eqQ
-- Q is sil: union also steps silently; peel Q's sil and recurse.
... | sil Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                       eqP eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-R-vis {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- Q is ret: union is mix fP Q; P fires directly as sMixVis.
... | ret r =
  _ , bStep (sMixVis {f = fP} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-vis-ret {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- Q is vis fQ: union is vis (mergeVis fP fQ); nested with on fQ at a.
... | vis fQ with fQ at a in eq-fQ-at
-- fQ at a = nothing: merged continuation is just t'.
...           | nothing =
  _ , bStep (sVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                  {at = at} {a = a} {t′ = t′}
                  (force-□-vis-merge {P = P} {Q = Q} eqP eqQ)
                  (merged-at-a-nothing {fP = fP} {fQ = fQ} eq-j eq-fQ-at))
              bs
-- fQ at a = just U: merged continuation is just (t' ⊓ U); lift bs via IntChoice-introL.
...           | just U =
  let (T″ , bs″) = IntChoice-trace-introL {P = t′} {Q = U} (T , bs)
   in T″ , bStep (sVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                       {at = at} {a = a} {t′ = t′ ⊓ U}
                       (force-□-vis-merge {P = P} {Q = Q} eqP eqQ)
                       (merged-at-a-just {fP = fP} {fQ = fQ} eq-j eq-fQ-at))
                  bs″
-- Q is ndbr fQ wi′ wa′ wp′: union is ndbr (mergeNdbr-vis-L P fQ) wi′ wa′ …
-- τ-step to branch wi′,wa′ landing at (P □ Q_branch), then recurse.
-- Fresh clause (necessary after the nested vis|vis with-split above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                        eqP eq-j) bs)
  | ndbr fQ wi′ wa′ wp′ =
  let Q_branch   = to-witness wp′
      eq-branch  = just-to-witness wp′          -- fQ wi′ wa′ ≡ just Q_branch
      merged-eq  = merged-branch-eq-vis-L fQ eq-branch
                                                -- mergeNdbr-vis-L P fQ wi′ wa′ ≡ just (P □ Q_branch)
      (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q_branch}
                     (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                      eqP eq-j) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-L-witness P fQ wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-L-vis {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- Q is mix fQ Q′: union is mix fQ (P □ Q′); τ-slide to (P □ Q′), recurse.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                        eqP eq-j) bs)
  | mix fQ Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t′}
                                       eqP eq-j) bs)
   in T″ , bTau (sMixSlide (force-□-mix-vis-mix {P = P} {Q = Q} eqP eqQ)) bs″
-- Phase 4: bStep (sRet eqP) — P terminates with ret r; case-split on Q .force.
-- The trace so far: (P □ Q) needs to produce the same √-step that P produces.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sRet {x = r} eqP) bs)
  with Q .force in eqQ
-- Q is sil Q′: force (P □ Q) = sil (P □ Q′); peel Q's sil and recurse.
... | sil Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bStep (sRet {x = r} eqP) bs)
   in T″ , bTau (sSil (force-□-sil-R-ret {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- Q is ret r′: inner case on r ≟ r′.
... | ret r′ with r ≟ r′
--   Same value: force (P □ Q) = ret r; emit the sRet step directly.
...   | yes refl =
  _ , bStep (sRet (force-□-ret-ret-yes {P = P} {Q = Q} eqP eqQ))
            bs
--   Different values: force (P □ Q) = ndbr (br2 P Q) …
--   τ-step from (P □ Q) to P (via br2 lift fzero), then P takes the sRet step.
...   | no neq =
  _ , bTau (sNdbr {f = br2 P Q}
                  {wi = (Lift _ (Fin 2) , fin)} {wa = lift fzero}
                  {prf = any-just tt₀}
                  {i = (Lift _ (Fin 2) , fin)} {a = lift fzero}
                  (force-□-ret-ret-no {P = P} {Q = Q} eqP eqQ neq)
                  refl)
           (bStep (sRet eqP) bs)
-- Q is vis fQ: force (P □ Q) = mix fQ P; slide to P, continue with original bs.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sRet {x = r} eqP) bs)
  | vis fQ =
  _ , bTau (sMixSlide (force-□-mix-ret-vis {P = P} {Q = Q} eqP eqQ))
           (bStep (sRet eqP) bs)
-- Q is ndbr fQ wi wa wp: force (P □ Q) = ndbr (mergeNdbr-vis-L P fQ) wi wa …
-- τ-step to (P □ Q_branch), recurse.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sRet {x = r} eqP) bs)
  | ndbr fQ wi wa wp =
  let Q_branch  = to-witness wp
      eq-branch = just-to-witness wp          -- fQ wi wa ≡ just Q_branch
      merged-eq = merged-branch-eq-vis-L fQ eq-branch
                                              -- mergeNdbr-vis-L P fQ wi wa ≡ just (P □ Q_branch)
      (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q_branch}
                     (T , bStep (sRet {x = r} eqP) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-L-witness P fQ wp}
                        {i = wi} {a = wa}
                        (force-□-ndbr-vis-L-ret {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
               bs″
-- Q is mix fQ Q′: force (P □ Q) = mix fQ (P □ Q′); slide to (P □ Q′), recurse.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sRet {x = r} eqP) bs)
  | mix fQ Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bStep (sRet {x = r} eqP) bs)
   in T″ , bTau (sMixSlide (force-□-mix-ret-mix {P = P} {Q = Q} eqP eqQ)) bs″
-- Phase 5a: bStep (sMixVis …) — P fires a visible event from a mix-shaped state.
-- force P ≡ mix fP P′, fP at a ≡ just t′; case-split on Q .force.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fP} {Qt = P′} {at = at} {a = a} {t′ = t′}
                                            eqP eq-j) bs)
  with Q .force in eqQ
-- Q is sil Q′: force (P □ Q) = sil (P □ Q′); peel Q's sil and recurse.
... | sil Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bStep (sMixVis {f = fP} {Qt = P′} {at = at} {a = a} {t′ = t′}
                                           eqP eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-R-mix {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- Q is ret r: force (P □ Q) = mix fP (P′ □ Q); fire directly via sMixVis.
... | ret r =
  _ , bStep (sMixVis {f = fP} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-mix-ret {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- Q is vis fQ: force (P □ Q) = mix fP (P′ □ Q); fire directly via sMixVis.
... | vis fQ =
  _ , bStep (sMixVis {f = fP} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-mix-vis {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- Q is ndbr fQ wi′ wa′ wp′: force (P □ Q) = ndbr (mergeNdbr-vis-L P fQ) wi′ wa′ …
-- τ-step to (P □ Q_branch) then recurse.
-- Fresh clause (necessary after the nested with-split above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fP} {Qt = P′} {at = at} {a = a} {t′ = t′}
                                            eqP eq-j) bs)
  | ndbr fQ wi′ wa′ wp′ =
  let Q_branch  = to-witness wp′
      eq-branch = just-to-witness wp′
      merged-eq = merged-branch-eq-vis-L fQ eq-branch
      (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q_branch}
                     (T , bStep (sMixVis {f = fP} {Qt = P′} {at = at} {a = a} {t′ = t′}
                                          eqP eq-j) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-L-witness P fQ wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-L-mix {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- Q is mix fQ Q′₂: force (P □ Q) = mix (λ Ae → mergeVis fP fQ Ae) (P′ □ Q′₂).
-- Nested with on fQ at a to determine the merged continuation.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fP} {Qt = P′} {at = at} {a = a} {t′ = t′}
                                            eqP eq-j) bs)
  | mix fQ Q′₂ with fQ at a in eq-fQ-at
-- fQ at a = nothing: merged continuation is just t′.
...              | nothing =
  _ , bStep (sMixVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                     {at = at} {a = a} {t′ = t′}
                     (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)
                     (merged-at-a-nothing {fP = fP} {fQ = fQ} eq-j eq-fQ-at))
            bs
-- fQ at a = just U: merged continuation is just (t′ ⊓ U); lift bs via IntChoice-introL.
...              | just U =
  let (T″ , bs″) = IntChoice-trace-introL {P = t′} {Q = U} (T , bs)
   in T″ , bStep (sMixVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                           {at = at} {a = a} {t′ = t′ ⊓ U}
                           (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)
                           (merged-at-a-just {fP = fP} {fQ = fQ} eq-j eq-fQ-at))
              bs″
-- Phase 5b: bTau (sMixSlide …) — P τ-slides to P′ from mix-shaped state.
-- force P ≡ mix fP P′; bs : P′ ═⟨ s ⟩═► T. Case-split on Q .force.
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fP} {Qt = P′} eqP) bs)
  with Q .force in eqQ
-- Q is sil Q′: force (P □ Q) = sil (P □ Q′); peel Q's sil and recurse.
... | sil Q′ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q′}
                      (T , bTau (sMixSlide {f = fP} {Qt = P′} eqP) bs)
   in T″ , bTau (sSil (force-□-sil-R-mix {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- Q is ret r: force (P □ Q) = mix fP (P′ □ Q); slide to (P′ □ Q), then recurse.
... | ret r =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P′} {Q = Q} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-ret {P = P} {Q = Q} eqP eqQ)) bs″
-- Q is vis fQ: force (P □ Q) = mix fP (P′ □ Q); slide to (P′ □ Q), then recurse.
... | vis fQ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P′} {Q = Q} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-vis {P = P} {Q = Q} eqP eqQ)) bs″
-- Q is ndbr fQ wi′ wa′ wp′: force (P □ Q) = ndbr (mergeNdbr-vis-L P fQ) …
-- τ-step to (P □ Q_branch) then recurse keeping the same sMixSlide on P.
-- Fresh clause (necessary after the nested with-split above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fP} {Qt = P′} eqP) bs)
  | ndbr fQ wi′ wa′ wp′ =
  let Q_branch  = to-witness wp′
      eq-branch = just-to-witness wp′
      merged-eq = merged-branch-eq-vis-L fQ eq-branch
      (T″ , bs″) = ExtChoice-trace-introL {P = P} {Q = Q_branch}
                     (T , bTau (sMixSlide {f = fP} {Qt = P′} eqP) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-L-witness P fQ wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-L-mix {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- Q is mix fQ Q′₂: force (P □ Q) = mix (λ Ae → mergeVis fP fQ Ae) (P′ □ Q′₂).
-- Slide to (P′ □ Q′₂), then recurse.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introL {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fP} {Qt = P′} eqP) bs)
  | mix fQ Q′₂ =
  let (T″ , bs″) = ExtChoice-trace-introL {P = P′} {Q = Q′₂} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)) bs″

ExtChoice-trace-introR (T , bNil) = _ , bNil
-- Phase 2 (mirror): sNdbr — Q takes a τ via ndbr; case-split on P .force
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bTau (sNdbr {f = fQ} {wi = wi} {wa = wa} {prf = wp}
                                         {i = i} {a = a} {t′ = t′}
                                         eqQ eq-j) bs)
  with P .force in eqP
-- P is sil: union steps silently (P-sil rule fires first); peel P's sil and recurse.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bTau (sNdbr {f = fQ} {wi = wi} {wa = wa} {prf = wp}
                                        {i = i} {a = a} {t′ = t′}
                                        eqQ eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret: union is ndbr (mergeNdbr-vis-L P fQ); τ-step to (P □ t'), recurse.
... | ret r =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = t′} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-L-witness P fQ wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-L-ret {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-L fQ eq-j))
                bs″
-- P is vis: union is ndbr (mergeNdbr-vis-L P fQ); same shape as ret.
... | vis fP =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = t′} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-L-witness P fQ wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-L-vis {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-L fQ eq-j))
                bs″
-- P is ndbr fP: pair-indexed merge sub-case.
-- TODO: symmetric of introL's ndbr|ndbr postulate case. Postulated.
... | ndbr fP wi′ wa′ wp′ =
  introR-ndbr-ndbr (T , bTau (sNdbr {f = fQ} {wi = wi} {wa = wa} {prf = wp}
                                       {i = i} {a = a} {t′ = t′} eqQ eq-j) bs)
-- P is mix: union is ndbr (mergeNdbr-vis-L P fQ); same shape as ret/vis.
... | mix fP P′₂ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = t′} (T , bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-L P fQ}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-L-witness P fQ wp}
                        {i = i} {a = a}
                        (force-□-ndbr-vis-L-mix {P = P} {Q = Q} eqP eqQ)
                        (merged-branch-eq-vis-L fQ eq-j))
                bs″
-- Phase 3 (mirror): bStep (sVis …) — Q fires a visible event; case-split on P .force.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                        eqQ eq-j) bs)
  with P .force in eqP
-- P is sil P′: force (P □ Q) = sil (P □ Q′... wait, (P□Q) = sil(P'□Q) by P-sil.
-- Peel P's sil and recurse keeping the Q-vis step.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                       eqQ eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret r: force (P □ Q) = mix fQ P; Q fires directly as sMixVis.
... | ret r =
  _ , bStep (sMixVis {f = fQ} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-ret-vis {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- P is vis fP: force (P □ Q) = vis (mergeVis fP fQ); nested with on fP at a.
... | vis fP with fP at a in eq-fP-at
-- fP at a = nothing: merged continuation is just t'.
...           | nothing =
  _ , bStep (sVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                  {at = at} {a = a} {t′ = t′}
                  (force-□-vis-merge {P = P} {Q = Q} eqP eqQ)
                  (merged-at-a-nothing-R {fP = fP} {fQ = fQ} eq-fP-at eq-j))
            bs
-- fP at a = just U: merged continuation is just (U ⊓ t'); lift bs via IntChoice-introR.
...           | just U =
  let (T″ , bs″) = IntChoice-trace-introR {P = U} {Q = t′} (T , bs)
   in T″ , bStep (sVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                       {at = at} {a = a} {t′ = U ⊓ t′}
                       (force-□-vis-merge {P = P} {Q = Q} eqP eqQ)
                       (merged-at-a-just-R {fP = fP} {fQ = fQ} eq-fP-at eq-j))
                bs″
-- P is ndbr fP wi′ wa′ wp′: force (P □ Q) = ndbr (mergeNdbr-vis-R fP Q) wi′ wa′ …
-- τ-step to (P_branch □ Q), recurse.
-- Fresh clause (necessary after the nested vis|vis with-split above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                        eqQ eq-j) bs)
  | ndbr fP wi′ wa′ wp′ =
  let P_branch   = to-witness wp′
      eq-branch  = just-to-witness wp′
      merged-eq  = merged-branch-eq-vis-R fP eq-branch
      (T″ , bs″) = ExtChoice-trace-introR {P = P_branch} {Q = Q}
                     (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                      eqQ eq-j) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-R-witness fP Q wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-R-vis {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- P is mix fP P′: force (P □ Q) = mix fQ (P □ P'... no.
-- force-□-mix-vis-mix: P≡vis, Q≡mix fQ Q' → (P□Q)=mix fQ (P□Q').
-- Mirror: P≡mix, Q≡vis → need a different helper.
-- Actually: when Q≡vis and P≡mix, (P□Q) = mix fP (P'□Q) by force-□-mix-mix-vis.
-- But fQ is Q's vis function. We fire Q's vis via sMixVis? No — (P□Q)=mix fP (P'□Q),
-- so the vis part is fP not fQ. We cannot directly fire Q's vis here.
-- Instead, τ-slide to (P'□Q), then recurse on (P'□Q) with same Q-vis step.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                        eqQ eq-j) bs)
  | mix fP P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bStep (sVis {f = fQ} {at = at} {a = a} {t′ = t′}
                                       eqQ eq-j) bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-vis {P = P} {Q = Q} eqP eqQ)) bs″
-- Phase 4 (mirror): bStep (sRet eqQ) — Q terminates; case-split on P .force.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sRet {x = r′} eqQ) bs)
  with P .force in eqP
-- P is sil P′: force (P □ Q) = sil (P' □ Q) by P-sil; peel P's sil and recurse.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bStep (sRet {x = r′} eqQ) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret r: inner case on r ≟ r′.
... | ret r with r ≟ r′
--   Same value: force (P □ Q) = ret r′; emit the sRet step directly.
...   | yes refl =
  _ , bStep (sRet (force-□-ret-ret-yes {P = P} {Q = Q} eqP eqQ))
            bs
--   Different values: force (P □ Q) = ndbr (br2 P Q) …
--   τ-step from (P □ Q) to Q (via br2 lift (fsuc fzero)), then Q takes the sRet step.
...   | no neq =
  _ , bTau (sNdbr {f = br2 P Q}
                  {wi = (Lift _ (Fin 2) , fin)} {wa = lift fzero}
                  {prf = any-just tt₀}
                  {i = (Lift _ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                  (force-□-ret-ret-no {P = P} {Q = Q} eqP eqQ neq)
                  refl)
           (bStep (sRet eqQ) bs)
-- P is vis fQ: force (P □ Q) = mix fP P; slide to P via sMixSlide, then take sRet.
-- (force-□-mix-vis-ret: P≡vis fP, Q≡ret r → (P□Q)=mix fP Q. sMixSlide to Q.)
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sRet {x = r′} eqQ) bs)
  | vis fP =
  _ , bTau (sMixSlide (force-□-mix-vis-ret {P = P} {Q = Q} eqP eqQ))
           (bStep (sRet eqQ) bs)
-- P is ndbr fP wi wa wp: force (P □ Q) = ndbr (mergeNdbr-vis-R fP Q) wi wa …
-- τ-step to (P_branch □ Q), recurse.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sRet {x = r′} eqQ) bs)
  | ndbr fP wi wa wp =
  let P_branch  = to-witness wp
      eq-branch = just-to-witness wp
      merged-eq = merged-branch-eq-vis-R fP eq-branch
      (T″ , bs″) = ExtChoice-trace-introR {P = P_branch} {Q = Q}
                     (T , bStep (sRet {x = r′} eqQ) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi} {wa = wa}
                        {prf = mergeNdbr-vis-R-witness fP Q wp}
                        {i = wi} {a = wa}
                        (force-□-ndbr-vis-R-ret {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
               bs″
-- P is mix fP P′: force (P □ Q) = mix fP (P′ □ Q); slide to (P′ □ Q), recurse.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sRet {x = r′} eqQ) bs)
  | mix fP P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bStep (sRet {x = r′} eqQ) bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-ret {P = P} {Q = Q} eqP eqQ)) bs″
-- Phase 5a (mirror): bStep (sMixVis …) — Q fires from mix-shaped state.
-- force Q ≡ mix fQ Q′, fQ at a ≡ just t′; case-split on P .force.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fQ} {Qt = Q′} {at = at} {a = a} {t′ = t′}
                                            eqQ eq-j) bs)
  with P .force in eqP
-- P is sil P′: force (P □ Q) = sil (P' □ Q); peel P's sil and recurse.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bStep (sMixVis {f = fQ} {Qt = Q′} {at = at} {a = a} {t′ = t′}
                                           eqQ eq-j) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret r: force (P □ Q) = mix fQ (P □ Q′) by force-□-mix-ret-mix; fire sMixVis.
... | ret r =
  _ , bStep (sMixVis {f = fQ} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-ret-mix {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- P is vis fP: force (P □ Q) = mix fQ (P □ Q′) by force-□-mix-vis-mix; fire sMixVis.
... | vis fP =
  _ , bStep (sMixVis {f = fQ} {at = at} {a = a} {t′ = t′}
                     (force-□-mix-vis-mix {P = P} {Q = Q} eqP eqQ) eq-j) bs
-- P is ndbr fP wi′ wa′ wp′: force (P □ Q) = ndbr (mergeNdbr-vis-R fP Q) wi′ wa′ …
-- τ-step to (P_branch □ Q) then recurse.
-- Fresh clause (necessary after the nested with-split above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fQ} {Qt = Q′} {at = at} {a = a} {t′ = t′}
                                            eqQ eq-j) bs)
  | ndbr fP wi′ wa′ wp′ =
  let P_branch  = to-witness wp′
      eq-branch = just-to-witness wp′
      merged-eq = merged-branch-eq-vis-R fP eq-branch
      (T″ , bs″) = ExtChoice-trace-introR {P = P_branch} {Q = Q}
                     (T , bStep (sMixVis {f = fQ} {Qt = Q′} {at = at} {a = a} {t′ = t′}
                                          eqQ eq-j) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-R-witness fP Q wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-R-mix {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- P is mix fP P′: force (P □ Q) = mix (λ Ae → mergeVis fP fQ Ae) (P′ □ Q′).
-- Q fires sMixVis; nested with on fP at a for the merged continuation.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bStep (sMixVis {f = fQ} {Qt = Q′} {at = at} {a = a} {t′ = t′}
                                            eqQ eq-j) bs)
  | mix fP P′ with fP at a in eq-fP-at
-- fP at a = nothing: merged continuation is just t′.
...              | nothing =
  _ , bStep (sMixVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                     {at = at} {a = a} {t′ = t′}
                     (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)
                     (merged-at-a-nothing-R {fP = fP} {fQ = fQ} eq-fP-at eq-j))
            bs
-- fP at a = just U: merged continuation is just (U ⊓ t′); lift bs via IntChoice-introR.
...              | just U =
  let (T″ , bs″) = IntChoice-trace-introR {P = U} {Q = t′} (T , bs)
   in T″ , bStep (sMixVis {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                           {at = at} {a = a} {t′ = U ⊓ t′}
                           (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)
                           (merged-at-a-just-R {fP = fP} {fQ = fQ} eq-fP-at eq-j))
              bs″
-- Phase 5b (mirror): bTau (sMixSlide …) — Q τ-slides to Q′ from mix-shaped state.
-- force Q ≡ mix fQ Q′; bs : Q′ ═⟨ s ⟩═► T. Case-split on P .force.
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fQ} {Qt = Q′} eqQ) bs)
  with P .force in eqP
-- P is sil P′: force (P □ Q) = sil (P' □ Q); peel P's sil and recurse.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                      (T , bTau (sMixSlide {f = fQ} {Qt = Q′} eqQ) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret r: force (P □ Q) = mix fQ (P □ Q′); slide to (P □ Q′), then recurse.
... | ret r =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-ret-mix {P = P} {Q = Q} eqP eqQ)) bs″
-- P is vis fP: force (P □ Q) = mix fQ (P □ Q′); slide to (P □ Q′), then recurse.
... | vis fP =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-vis-mix {P = P} {Q = Q} eqP eqQ)) bs″
-- P is ndbr fP wi′ wa′ wp′: force (P □ Q) = ndbr (mergeNdbr-vis-R fP Q) …
-- τ-step to (P_branch □ Q) then recurse keeping the same sMixSlide on Q.
-- Fresh clause (necessary after the nested with-split above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fQ} {Qt = Q′} eqQ) bs)
  | ndbr fP wi′ wa′ wp′ =
  let P_branch  = to-witness wp′
      eq-branch = just-to-witness wp′
      merged-eq = merged-branch-eq-vis-R fP eq-branch
      (T″ , bs″) = ExtChoice-trace-introR {P = P_branch} {Q = Q}
                     (T , bTau (sMixSlide {f = fQ} {Qt = Q′} eqQ) bs)
   in T″ , bTau (sNdbr {f = mergeNdbr-vis-R fP Q}
                        {wi = wi′} {wa = wa′}
                        {prf = mergeNdbr-vis-R-witness fP Q wp′}
                        {i = wi′} {a = wa′}
                        (force-□-ndbr-vis-R-mix {P = P} {Q = Q} eqP eqQ)
                        merged-eq)
                bs″
-- P is mix fP P′: force (P □ Q) = mix (λ Ae → mergeVis fP fQ Ae) (P′ □ Q′).
-- Slide to (P′ □ Q′), then recurse.
-- Fresh clause (same reason as ndbr above).
ExtChoice-trace-introR {P = P} {Q = Q}
                       (T , bTau (sMixSlide {f = fQ} {Qt = Q′} eqQ) bs)
  | mix fP P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q′} (T , bs)
   in T″ , bTau (sMixSlide (force-□-mix-mix-mix {P = P} {Q = Q} eqP eqQ)) bs″
-- Phase 1 (mirror): bTau (sSil eqQ) — Q takes a τ via sil; case-split on P .force.
ExtChoice-trace-introR {P = P} {Q = Q} (T , bTau (sSil {t = Q′} eqQ) bs)
  with P .force in eqP
-- P is sil P′: P-sil rule fires first; step to (P' □ Q), then recurse with Q's sSil.
... | sil P′ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P′} {Q = Q}
                                            (T , bTau (sSil eqQ) bs)
   in T″ , bTau (sSil (force-□-sil-L {P = P} {P′ = P′} {Q = Q} eqP)) bs″
-- P is ret: force (P □ Q) = sil (P □ Q′) by force-□-sil-R-ret; recurse on Q′.
... | ret _ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sSil (force-□-sil-R-ret {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- P is vis: force (P □ Q) = sil (P □ Q′) by force-□-sil-R-vis; recurse on Q′.
... | vis _ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sSil (force-□-sil-R-vis {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- P is ndbr: force (P □ Q) = sil (P □ Q′) by force-□-sil-R-ndbr; recurse on Q′.
... | ndbr _ _ _ _ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sSil (force-□-sil-R-ndbr {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″
-- P is mix: force (P □ Q) = sil (P □ Q′) by force-□-sil-R-mix; recurse on Q′.
... | mix _ _ =
  let (T″ , bs″) = ExtChoice-trace-introR {P = P} {Q = Q′} (T , bs)
   in T″ , bTau (sSil (force-□-sil-R-mix {P = P} {Q = Q} {Q′ = Q′} eqP eqQ)) bs″

------------------------------------------------------------------------
-- Refinement-order corollaries:  (P □ Q) ⊑ᵀ P  and  (P □ Q) ⊑ᵀ Q.
------------------------------------------------------------------------

⊑ᵀ-□-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           ⦃ _ : DecEq R ⦄
           {P Q : ITree E (ExtI I) R}
         → (P □ Q) ⊑ᵀ P
⊑ᵀ-□-L = ExtChoice-trace-introL

⊑ᵀ-□-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           ⦃ _ : DecEq R ⦄
           {P Q : ITree E (ExtI I) R}
         → (P □ Q) ⊑ᵀ Q
⊑ᵀ-□-R = ExtChoice-trace-introR

------------------------------------------------------------------------
-- Monotonicity of _□_ under _⊑ᵀ_.
--
-- Inherits the two postulates from ExtChoice-trace-introL/R (the
-- pair-indexed ndbr|ndbr sub-cases).  The mono lemma is true modulo
-- those postulates.
------------------------------------------------------------------------
□-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              ⦃ _ : DecEq R ⦄
              {P P′ Q Q′ : ITree E (ExtI I) R}
            → P ⊑ᵀ P′ → Q ⊑ᵀ Q′
            → (P □ Q) ⊑ᵀ (P′ □ Q′)
□-mono-⊑ᵀ {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} P⊑P′ Q⊑Q′ tr-rhs
  with ExternalChoice-trace P′ Q′ tr-rhs
... | inj₁ tr-P′ = ExtChoice-trace-introL (P⊑P′ tr-P′)
... | inj₂ tr-Q′ = ExtChoice-trace-introR (Q⊑Q′ tr-Q′)

-----------------------------------------------------------------------------------------
-- Bind >>=
-- traces [P >>= Q] =
-- traces [P ; Q] = {trp : traces [P] | ✓ ∉ trp • trp } ∪
--                  {trp : traces [P] ; trq : traces [Q] | ✓ ∉ trp ∧ trp ⌢ ⟨✓⟩ ∈ traces [P] • trp ⌢ trq }

data BindSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (k : R → ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  -- Case 1: P is still executing
  in-P : ∀ {P'} {s : List (Event E)}
       -- We lift plain events s into Event√ E S to match the bind's trace
       → traces P (map evl s)              
       → t-final ≡ (P' >>= k)
       → BindSplit P k t-final (map evl s)

  -- Case 2: P finished and we transitioned to k
  in-k : ∀ {s : List (Event√ E S)} 
       → (r : R) 
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from k (can include √ S)
       → (s ≡ map evl s1 ++ s2)            -- s1 is lifted to S-type to join s2
       → traces P (map evl s1 ++ [ √ r ])  -- s1 is lifted to R-type to match P
       → traces (k r) s2                  -- Already S-type
       → BindSplit P k t-final s


-- A helper to allow us induct on transition directly, instead of 
bind-trace-helper : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)} (t-f : ITree E (ExtI I) S)
   → (P >>= k) ═⟨ s ⟩═► t-f    -- The transition proof is now isolated!
   → Σ (ITree E (ExtI I) S) (λ t-f' → BindSplit P k t-f' s)

-- Base Case
bind-trace-helper P k t-f bNil = t-f , in-P (P , bNil) refl

-- 1. Handling Silent Steps (Tau via sSil)
bind-trace-helper P k t-f (bTau (sSil {t = next} eq-f) big-step) with P .force in p-eq | eq-f
... | sil c | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper c k t-f big-step of λ where
      (tend , in-P (P' , c-step) eq) → 
          tend , in-P (P' , bTau (sSil p-eq) c-step) eq
      (tend , in-k r s1 s2 eq-s (P' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P' , bTau (sSil p-eq) c-step) trk2

... | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sSil eq-f') big-step)

... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just P' | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper P' k t-f big-step of λ where
      
      (tend , in-P (P'' , c-step) eq) → 
          tend , in-P (P'' , bTau (sNdbr p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P'' , bTau (sNdbr p-eq fi-eq) c-step) trk2
          
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) 
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sNdbr eq-f' eq-j) big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | sil _ | ()
bind-trace-helper P k t-f (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ()

-- 3. Handling Visible Steps (e via sVis)
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just P' | refl =
    -- Recurse using the helper, passing t-f and big-step separately
    case bind-trace-helper P' k t-f big-step of λ where
      
      (tend , in-P {s = sP} (P'' , c-step) eq) → 
          tend , in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (P'' , bStep (sVis p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2 (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (P'' , bStep (sVis p-eq fi-eq) c-step) trk2
          
... | nothing | ()

-- The Hand-off case
bind-trace-helper P k t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) 
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sVis eq-f' eq-j) big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-- 4. Handling Termination (The hand-off to k via sRet)
bind-trace-helper P k t-f (bStep (sRet {x = r} eq-f) big-step) with P .force in p-eq | eq-f
... | ret r' | eq-f' = 
    -- Hand-off point: s1 is empty ([]). P's trace is done. 
    -- The rest of the transition (big-step) belongs to (k r').
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sRet eq-f') big-step)

-- Absurd cases (updated to the curried helper format)
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | vis _        | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
bind-trace-helper P k t-f (bStep (sRet eq-f) big-step) | mix _ _      | ()

-- 5. NEW: bTau via sMixSlide. force(P >>= k) ≡ mix _ Qt, with Qt = (Qt-orig >>= k).
bind-trace-helper P k t-f (bTau (sMixSlide eq-f) big-step) with P .force in p-eq | eq-f
... | mix _ Qt | refl =
    case bind-trace-helper Qt k t-f big-step of λ where
      (tend , in-P (Q' , c-step) eq) →
          tend , in-P (Q' , bTau (sMixSlide p-eq) c-step) eq
      (tend , in-k r s1 s2 eq-s (Q' , c-step) trk2) →
          tend , in-k r s1 s2 eq-s (Q' , bTau (sMixSlide p-eq) c-step) trk2
-- Hand-off: P at ret r' means force(P >>= k) = (k r').force; the τ-step belongs to k.
... | ret r' | eq-f' =
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sMixSlide eq-f') big-step)
-- Absurd cases: P.force is not mix, so eq-f : ≡ mix _ _ is impossible.
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 6. NEW: bStep via sMixVis. force(P >>= k) ≡ mix lifted-fP Qt; sub-case on fP at a.
bind-trace-helper P k t-f (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | mix fP _ | refl with fP at a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace-helper P' k t-f big-step of λ where
      (tend , in-P {s = sP} (P'' , c-step) eq) →
          tend , in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (P'' , bStep (sMixVis p-eq fi-eq) c-step) eq
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) →
          tend , in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2 (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (P'' , bStep (sMixVis p-eq fi-eq) c-step) trk2
... | nothing | ()
-- Hand-off: P at ret r' means the step belongs to k.
bind-trace-helper P k t-f (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
    | ret r' | eq-f' =
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sMixVis eq-f' eq-j) big-step)
-- Absurd cases.
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | sil _        | ()
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | vis _        | ()
bind-trace-helper P k t-f (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

bind-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)}
   → traces (P >>= k) s
   → Σ (ITree E (ExtI I) S) (λ t-f → BindSplit P k t-f s)
-- By moving the logic into the helpfer function, we can overcome the termination
-- checking error for the below version. 
bind-trace P k (t-f , tr) = bind-trace-helper P k t-f tr

------------------------------------------------------------------------
-- Introduction direction for `bind-trace`.
-- Given a BindSplit witness, build a trace of (P >>= k).
------------------------------------------------------------------------

-- Helper A: lift a bigstep of P (R-typed events) to a bigstep of (P >>= k) (S-typed events).
-- The trace lists are both `map evl s` for the same underlying s : List (Event E),
-- but have different return-type parameters (Event√ E R vs Event√ E S).
-- Termination: structural induction on the bigstep.
private
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

  lift-bind-bigstep
    : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
        (s : List (Event E)) {P' : ITree E (ExtI I) R}
      → P ═⟨ map evl s ⟩═► P'
      → Σ (ITree E (ExtI I) S) λ Q → (P >>= k) ═⟨ map evl s ⟩═► Q

  lift-bind-bigstep P k [] bNil = P >>= k , bNil

  -- τ via sSil: P steps silently, so does P >>= k
  lift-bind-bigstep P k s (bTau (sSil {t = c} eq-f) rest) =
      case lift-bind-bigstep c k s rest of λ where
        (Q , bs) → Q , bTau (sSil (bind-force-sil P k eq-f)) bs

  -- τ via sNdbr: P branches internally, so does P >>= k
  lift-bind-bigstep P k s (bTau (sNdbr {f = f} {wi = wi} {wa = wa} {prf = wp}
                                        {i = i} {a = a} {t′ = t′} eq-f eq-j) rest) =
      case lift-bind-bigstep t′ k s rest of λ where
        (Q , bs) → Q , bTau (sNdbr (bind-force-ndbr P k eq-f)
                                    (bind-cont-ndbr-just k f i a eq-j)) bs

  -- τ via sMixSlide: P slides from mix to fallback, so does P >>= k
  lift-bind-bigstep P k s (bTau (sMixSlide {Qt = Qt} eq-f) rest) =
      case lift-bind-bigstep Qt k s rest of λ where
        (Q , bs) → Q , bTau (sMixSlide (bind-force-mix P k eq-f)) bs

  -- visible step via sVis: trace head consumed, recurse on tail
  lift-bind-bigstep P k (_ ∷ s') (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
      case lift-bind-bigstep t′ k s' rest of λ where
        (Q , bs) → Q , bStep (sVis (bind-force-vis P k eq-f)
                                    (bind-cont-vis-just k f at a eq-j)) bs

  -- visible step via sMixVis: trace head consumed, recurse on tail
  lift-bind-bigstep P k (_ ∷ s') (bStep (sMixVis {f = f} {at = at} {a = a} {t′ = t′} eq-f eq-j) rest) =
      case lift-bind-bigstep t′ k s' rest of λ where
        (Q , bs) → Q , bStep (sMixVis (bind-force-mix P k eq-f)
                                       (bind-cont-mix-just k f at a eq-j)) bs

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

  -- Helper D: reattach a bigstep to a tree with the same force (first-step coercion).
  -- After the first step both trees are at the same successor, so `rest` is reused directly.
  bigstep-force-eq
    : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q : ITree E (ExtI I) R} {t : ITree E (ExtI I) R}
        {s : List (Event√ E R)}
      → ITree.force P ≡ ITree.force Q
      → Q ═⟨ s ⟩═► t
      → Σ (ITree E (ExtI I) R) λ t' → P ═⟨ s ⟩═► t'
  bigstep-force-eq _  bNil                         = _ , bNil
  bigstep-force-eq eq (bTau  (sSil       eq-f) rest) = _ , bTau  (sSil       (trans eq eq-f)) rest
  bigstep-force-eq eq (bTau  (sNdbr      eq-f eq-j) rest) = _ , bTau  (sNdbr (trans eq eq-f) eq-j) rest
  bigstep-force-eq eq (bTau  (sMixSlide  eq-f) rest) = _ , bTau  (sMixSlide  (trans eq eq-f)) rest
  bigstep-force-eq eq (bStep (sVis       eq-f eq-j) rest) = _ , bStep (sVis   (trans eq eq-f) eq-j) rest
  bigstep-force-eq eq (bStep (sRet       eq-f) rest) = _ , bStep (sRet        (trans eq eq-f)) rest
  bigstep-force-eq eq (bStep (sMixVis    eq-f eq-j) rest) = _ , bStep (sMixVis (trans eq eq-f) eq-j) rest

bind-trace-intro : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
    {s : List (Event√ E S)} {t-final : ITree E (ExtI I) S}
  → BindSplit P k t-final s
  → traces (P >>= k) s

-- Case 1: P is still executing.  Lift P's bigstep through >>= .
bind-trace-intro P k (in-P {s = s'} (_ , tr-P) _) =
  lift-bind-bigstep P k s' tr-P

-- Case 2: P finished with value r, then k r provides the rest.
bind-trace-intro P k (in-k r s1 s2 eq-s (_ , tr-P-tick) (t-k , tr-k)) =
  subst (traces (P >>= k)) (sym eq-s)
    (let (P-bind , bs-s1 , f-eq) = lift-bind-bigstep-tick P k s1 tr-P-tick
         (t-result , bs-s2)      = bigstep-force-eq f-eq tr-k
     in t-result , bigstep-concat bs-s1 bs-s2)

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
... | T-f , in-P {P' = P'} tr-P′ _
    = bind-trace-intro P k (in-P {P' = P'} (P⊑P′ tr-P′) refl)
... | T-f , in-k r s1 s2 eq-s tr-P′ tr-k′
    = bind-trace-intro P k
        (in-k {t-final = T-f} r s1 s2 eq-s (P⊑P′ tr-P′) (k⊑k′ r tr-k′))

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

{-
-- {-# NON_TERMINATING #-}
bind-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
   (P : ITree E (ExtI I) R) (k : R → ITree E (ExtI I) S)
   {s : List (Event√ E S)}
   → traces (P >>= k) s
   → Σ (ITree E (ExtI I) S) (λ t-f → BindSplit P k t-f s)

-- Base Case
bind-trace P k (t-f , bNil) = t-f , in-P (P , bNil) refl

-- ==========================================
-- 1. Handling Silent Steps (Tau via sSil)
-- ==========================================
bind-trace P k (t-f , bTau (sSil {t = next} eq-f) big-step) with P .force in p-eq | eq-f
... | sil c | refl =
-- ====================================================================
-- This causes the termination checking error because the termination checker
-- cannot see that big-step is smaller than bTau (sSil eq-f) big-step when
-- c is not syntactically a subterm of P. The recursive call bind-trace c k
-- (t-f , big-step) is fine on the trace argument, but Agda's termination
-- checker needs a lexicographic measure and loses track when with P .force.
--
-- The core issue is that with P .force in p-eq abstracts over P .force,
-- which hides the structural relationship between P and c from the termination
-- checker. It can no longer see that big-step is a strict subterm of the
-- original trace.
--
-- Solution:  Induct on the trace proof directly
-- ====================================================================
    -- 1. Recurse on 'c', because P stepped to c!
    case bind-trace c k (t-f , big-step) of λ where
      
      -- 2. Deconstruct the trace pair (P' , c-step)
      (tend , in-P (P' , c-step) eq) → 
          -- 3. Reconstruct the trace pair for P using P' and the new bTau
          tend , in-P (P' , bTau (sSil p-eq) c-step) eq
      
      -- Do the same for in-k. trP1 is a pair (P' , c-step)
      (tend , in-k r s1 s2 eq-s (P' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P' , bTau (sSil p-eq) c-step) trk2

... | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sSil eq-f') big-step)
... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- ==========================================
-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
-- ==========================================
-- Notice we explicitly bind `eq-j` here so it is in scope for the `with` block
bind-trace P k (t-f , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just P' | refl =
    case bind-trace P' k (t-f , big-step) of λ where
      
      -- 1. Destructure into (P'' , c-step)
      (tend , in-P (P'' , c-step) eq) → 
          tend , in-P (P'' , bTau (sNdbr p-eq fi-eq) c-step) eq
          
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          tend , in-k r s1 s2 eq-s (P'' , bTau (sNdbr p-eq fi-eq) c-step) trk2
          
-- The branch f i a returning 'nothing' contradicts eq-j : just t' ≡ nothing
... | nothing | ()
-- Absurd cases for sNdbr
bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step) | sil _ | ()
bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step)
    | ret r' | eq-f' = 
      t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bTau (sNdbr eq-f' eq-j) big-step)

bind-trace P k (t-f , bTau (sNdbr eq-f eq-j) big-step) | vis _ | ()

-- ==========================================
-- 3. Handling Visible Steps (e via sVis)
-- ==========================================
bind-trace P k (t-f , bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with P .force in p-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just P' | refl =
-- Make sure to recurse on P', as the process stepped to P'
    case bind-trace P' k (t-f , big-step) of λ where
      
      -- 1. Bind the implicit {s = sP} so we can use it, and destructure the pair
      (tend , in-P {s = sP} (P'' , c-step) eq) → 
          -- Prepend the visible event to sP, and rebuild the pair for P
          tend , in-P {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (P'' , bStep (sVis p-eq fi-eq) c-step) eq
          
      -- 2. Destructure the trace pair into (P'' , c-step)
      (tend , in-k r s1 s2 eq-s (P'' , c-step) trk2) → 
          -- Prepend to s1, KEEP the cong logic, and rebuild the pair for P
          tend , in-k r ((evLabel (proj₁ at) (proj₂ at) a) ∷ s1) s2 (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (P'' , bStep (sVis p-eq fi-eq) c-step) trk2
          
... | nothing | ()
-- Absurd cases for sVis
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step) | sil _ | ()
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step)
-- The hand-off: P returned, so this visible step actually belongs to k!
    | ret r' | eq-f' = 
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sVis eq-f' eq-j) big-step)
bind-trace P k (t-f , bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-- ==========================================
-- 4. Handling Termination (The hand-off to k via sRet)
-- ==========================================
bind-trace P k (t-f , bStep (sRet {x = r} eq-f) big-step) with P .force in p-eq | eq-f
... | ret r' | eq-f' = 
    -- Hand-off point: s1 is empty ([]). P's trace is done. 
    -- The rest of the transition (big-step) belongs to (k r').
    t-f , in-k r' [] _ refl (_ , bStep (sRet p-eq) bNil) (t-f , bStep (sRet eq-f') big-step)
-- Absurd cases for sRet
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | sil _        | ()
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | vis _        | ()
bind-trace P k (t-f , bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
-}

-----------------------------------------------------------------------------------------
-- Bind >>

data Bind₀Split {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E I R) (Q : ITree E I S) (t-final : ITree E I S)
  : List (Event√ E S) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  -- Case 1: P is still executing
  in-P₀ : ∀ {P'} {s : List (Event E)}
       -- We lift plain events s into Event√ E S to match the bind's trace
       → traces P (map evl s)              
       → t-final ≡ (_>>_ {R = R} P' Q)
       → Bind₀Split P Q t-final (map evl s)

  -- Case 2: P finished and we transitioned to k
  in-Q₀ : ∀ {s : List (Event√ E S)} 
       → (r : R) 
       → (s1 : List (Event E))            -- Plain events from P
       → (s2 : List (Event√ E S))         -- Full trace from k (can include √ S)
       → (s ≡ map evl s1 ++ s2)            -- s1 is lifted to S-type to join s2
       → traces P (map evl s1 ++ [ √ r ])  -- s1 is lifted to R-type to match P
       → traces Q s2                  -- Already S-type
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
      -- We explicitly name P' here to help unification
      help (in-P {P' = P'} sP trP) = 
        in-P₀ {P' = P'} sP trP
        
      help (in-k r s1 s2 eq trP trQ) = 
        in-Q₀ r s1 s2 eq trP trQ

-----------------------------------------------------------------------------------------
-- Kleisli composition >=> or ⨾

data KleisliSplit {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T) (x : R) (t-final : ITree E (ExtI I) T)
  : List (Event√ E T) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs ⊔ ℓt) where

  in-Pᵏ : ∀ {P'} {s : List (Event E)}
       → traces (P x) (map evl s)
       → t-final ≡ (P' >>= Q)
       → KleisliSplit P Q x t-final (map evl s)

  in-Qᵏ : ∀ {s : List (Event√ E T)} 
       → (r : S) (s1 : List (Event E)) (s2 : List (Event√ E T))
       → (s ≡ map evl s1 ++ s2)
       → traces (P x) (map evl s1 ++ [ √ r ])
       → traces (Q r) s2
       → KleisliSplit P Q x t-final s

kleisli-trace : ∀ {ℓi ℓr ℓs ℓt} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} {T : Set ℓt}
  {s : List (Event√ E T)} (x : R)
  (P : KTree E (ExtI I) R S) (Q : KTree E (ExtI I) S T)
  → traces ((P >=> Q) x) s
  → Σ (ITree E (ExtI I) T) (λ t-f → KleisliSplit P Q x t-f s)
kleisli-trace {S = S} {T = T} {s = s} x P Q tr = 
  -- We leverage the bind-trace lemma we already finished
  let (t-f , bsplit) = bind-trace (P x) Q tr 
  in t-f , help bsplit
  where
    -- Helper to solve the UnsolvedConstraints for S and T (the return types)
    help : ∀ {t-f} → BindSplit {R = S} {S = T} (P x) Q t-f s → KleisliSplit P Q x t-f s
    
    -- Case 1: P x is still running
    help (in-P {P' = P'} sP trP) = 
      in-Pᵏ sP trP
      
    -- Case 2: P x finished with result 'r', and Q r took over
    help (in-k r s1 s2 eq trP trQ) =
      in-Qᵏ r s1 s2 eq trP trQ

-----------------------------------------------------------------------------------------
-- Interleave  P ⦀ Q
-- traces [P ⦀ Q] = arbitrary interleaving of P's and Q's plain-event traces;
-- the combined process terminates with √(r,q) only when both P and Q reach
-- termination simultaneously.

import CSP.Definitions.Parallel {ℓ} {ℓe} {E} as CSPPar
open CSPPar E-≟

-- Pure-events merge predicate (no √).
data Interleave : List (Event E) → List (Event E) → List (Event E)
                → Set (lsuc ℓ ⊔ ℓe) where
  int-nil : Interleave [] [] []
  int-l   : ∀ {sP sQ s e} → Interleave sP sQ s → Interleave (e ∷ sP) sQ (e ∷ s)
  int-r   : ∀ {sP sQ s e} → Interleave sP sQ s → Interleave sP (e ∷ sQ) (e ∷ s)

-- Splitting witness: a trace of (P ⦀ Q) decomposes into either an
-- in-progress interleave (no √) or a fully terminated trace ending in √(r,q).
data InterleaveSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  : List (Event√ E (R × S)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where

  in-progress : ∀ {sP sQ s : List (Event E)}
              → Interleave sP sQ s
              → traces P (map evl sP)
              → traces Q (map evl sQ)
              → InterleaveSplit P Q (map evl s)

  done : ∀ {sP sQ s : List (Event E)} {r : R} {q : S}
       → Interleave sP sQ s
       → traces P (map evl sP ++ [ √ r ])
       → traces Q (map evl sQ ++ [ √ q ])
       → InterleaveSplit P Q (map evl s ++ [ √ (r , q) ])

Interleave-trace-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_⦀_ {I = I} {R = R} {S = S} P Q) ═⟨ s ⟩═► t′
  → InterleaveSplit P Q s

-- 1. Empty trace
Interleave-trace-aux P Q bNil =
  in-progress int-nil (_ , bNil) (_ , bNil)

-- 2. Tau via sSil — exactly one of P, Q has a sil head
Interleave-trace-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | sil P' | _ | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sSil p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sSil p-eq) trP') trQ
... | ret _ | sil Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | vis _ | sil Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | ndbr _ _ _ _ | sil Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
-- NEW: mix | sil Q' — Q takes the silent step. (User's _⦀_ rule: mix _ _ | sil _ = sil (P ⦀ Q'))
... | mix _ _ | sil Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
-- All other (P.force, Q.force) combinations do not reduce force(P ⦀ Q) to sil.
... | ret _ | ret _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sSil (force is mix or ndbr for these combinations, not sil)
... | ret _ | mix _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 3. Visible step via sVis — comes from a vis head in the merge
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- (a) vis | ret : P moves alone
... | vis fP | ret _ | refl with fP at a in fp-eq | eq-j
... | just P' | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | ()

-- (b) ret | vis : Q moves alone
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | nothing | ()

-- (c) vis | vis : four sub-cases, one of which is the internal-choice case
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts
... | just P' | nothing | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
-- only Q accepts
... | nothing | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
-- both accept: continuation is (P' ⦀ Q) ⊓ (P ⦀ Q'); inline InternalChoice-trace
-- so the structural decrease on the inner big-step is visible to the termination checker
... | just P' | just Q' | refl with big-step
-- inner trace empty: outer trace is just [at]; default to P'-side
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (int-l int-nil)
                (_ , bStep (sVis p-eq fp-eq) bNil)
                (_ , bNil)
-- internal-choice picks a branch via sNdbr
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P' Q inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P Q' inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
-- other internal-choice indices: br2 returns nothing → eq-int-j absurd
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
-- force ((P' ⦀ Q) ⊓ (P ⦀ Q')) is ndbr, so sSil/sVis/sRet first steps are impossible
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sSil ()) _
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bStep (sVis () _) _
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bStep (sRet ()) _
-- neither accepts: merge yields nothing → eq-j impossible
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | nothing | nothing | ()

-- (d) absurd head combinations for sVis
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sVis (force(P ⦀ Q) is mix or ndbr for these, not vis).
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 4. Termination via sRet — only when both P and Q are at ret simultaneously
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret rP | ret rQ | refl with big-step
...   | bNil =
        done int-nil
             (_ , bStep (sRet p-eq) bNil)
             (_ , bStep (sRet q-eq) bNil)
...   | bTau (sSil ()) _
...   | bTau (sNdbr () _) _
...   | bStep (sRet ()) _
...   | bStep (sVis refl ()) _
-- absurd head combinations for sRet
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | sil _ | _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sRet (force is mix or ndbr, not ret, when one side is mix).
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ret _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | vis _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 5. Tau via sNdbr — at least one of P, Q has an ndbr head
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- (a) ret | ndbr : Q moves alone (Q-distribution)
... | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (b) vis | ndbr : Q moves alone (Q-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (d) ndbr | vis : P moves alone (P-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (e) ndbr | ndbr : both ndbr; merge ranges over pair indices
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  with i | a
-- non-pair indices reject in mergeNdbr' → eq-j impossible
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
-- pair index: case-split on (fP _, fQ _)
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
-- only P accepts → continuation (P' ⦀ Q)
... | just P' | nothing | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
-- only Q accepts → continuation (P ⦀ Q')
... | nothing | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
-- both accept → continuation (P' ⦀ Q'); add τ on BOTH sides
... | just P' | just Q' | refl =
    case Interleave-trace-aux P' Q' big-step of λ where
      (in-progress merge (_ , trP') (_ , trQ')) →
        in-progress merge
                    (_ , bTau (sNdbr p-eq fp'-eq) trP')
                    (_ , bTau (sNdbr q-eq fq'-eq) trQ')
      (done merge (_ , trP') (_ , trQ')) →
        done merge
             (_ , bTau (sNdbr p-eq fp'-eq) trP')
             (_ , bTau (sNdbr q-eq fq'-eq) trQ')
... | nothing | nothing | ()

-- (f) absurd head combinations for sNdbr
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | vis _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ret _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | vis _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()

-- (g) NEW: mix | ndbr — Q does ndbr-distribution; the mix on the left's vis side is absent at this τ-step.
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (h) NEW: ndbr | mix — P does ndbr-distribution.
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (i) NEW: mix-shape absurds for sNdbr (force is mix, not ndbr, for these combinations).
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Interleave-trace-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | mix _ _ | ()

-- ----- 6. NEW: bTau via sMixSlide. force (P ⦀ Q) ≡ mix _ Qt; slide goes to Qt. -----
Interleave-trace-aux P Q (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix fQ Q': force = mix _ (P ⦀ Q'). Q slides.
... | ret _ | mix _ Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | mix: both slide simultaneously to (P' ⦀ Q').
... | mix _ P' | mix _ Q' | refl =
    case Interleave-trace-aux P' Q' big-step of λ where
      (in-progress merge (_ , trP') (_ , trQ')) →
        in-progress merge
                    (_ , bTau (sMixSlide p-eq) trP')
                    (_ , bTau (sMixSlide q-eq) trQ')
      (done merge (_ , trP') (_ , trQ')) →
        done merge
             (_ , bTau (sMixSlide p-eq) trP')
             (_ , bTau (sMixSlide q-eq) trQ')
-- Absurd: all non-mix shapes.
... | sil _ | _ | ()
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- ----- 7. NEW: bStep via sMixVis. force (P ⦀ Q) ≡ mix f Qt, f at a ≡ just t'. -----
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix fQ _: Q's vis-side fires.
... | ret _ | mix fQ _ | refl with fQ at a in fq-eq | eq-j
... | just _  | refl =
    case Interleave-trace-aux P _ big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | nothing | ()
-- vis | mix: merged vis-function of fP and fQ (same merge as vis|vis under _⦀_).
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P' ⦀ Q (Q stays as the original mix). P side fires a vis step.
... | just P' | nothing | refl =
    case Interleave-trace-aux P' Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
-- only Q accepts: t' = P ⦀ Q''. Q side fires an sMixVis step.
... | nothing | just Q'' | refl =
    case Interleave-trace-aux P Q'' big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
-- both accept: the merge yields an internal nondeterministic choice between
-- (P' ⦀ Q) and (P ⦀ Q''). The big-step's first instruction picks one branch.
... | just P' | just Q'' | refl with big-step
-- bNil: empty trace; pick the left branch arbitrarily (P fires).
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (int-l int-nil)
                (_ , bStep (sVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P' Q inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P Q'' inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
-- other inner-ndbr indices yield nothing, so eq-int-j is absurd
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
-- inner big-step starting with non-ndbr is impossible (force is the internal ndbr)
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sSil ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sMixSlide ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sRet ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sVis () _) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sMixVis () _) _
-- neither accepts: merged-f at a = nothing → eq-j impossible
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | nothing | nothing | ()
-- mix | ret: P's vis-side fires (mix's vis is just fP — no merge needed).
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with fP at a in fp-eq | eq-j
... | just _ | refl =
    case Interleave-trace-aux _ Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
-- mix | vis: symmetric to vis|mix — P fires via sMixVis, Q via sVis.
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P'' ⦀ Q. P side fires sMixVis.
... | just P'' | nothing | refl =
    case Interleave-trace-aux P'' Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
-- only Q accepts: t' = P ⦀ Q'. Q side fires sVis.
... | nothing | just Q' | refl =
    case Interleave-trace-aux P Q' big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
-- both accept: internal choice between (P'' ⦀ Q) and (P ⦀ Q').
... | just P'' | just Q' | refl with big-step
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (int-l int-nil)
                (_ , bStep (sMixVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P'' Q inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P Q' inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sSil ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sMixSlide ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sRet ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sVis () _) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sMixVis () _) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | nothing | nothing | ()
-- mix | mix: full merge of vis functions. Mirrors mix|vis: both sides fire via sMixVis;
-- both-accept case branches internally on an ndbr (fin fzero ↦ P-side, fin fsuc fzero ↦ Q-side).
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P'' ⦀ Q
... | just P'' | nothing | refl =
    case Interleave-trace-aux P'' Q big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
-- only Q accepts: t' = P ⦀ Q''
... | nothing | just Q'' | refl =
    case Interleave-trace-aux P Q'' big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
-- both accept: internal ndbr between (P'' ⦀ Q) and (P ⦀ Q'').
... | just P'' | just Q'' | refl with big-step
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (int-l int-nil)
                (_ , bStep (sMixVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P'' Q inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (int-l merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (int-l merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Interleave-trace-aux P Q'' inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (int-r merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (int-r merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
-- inner big-step starting with non-ndbr is impossible (force is internal ndbr)
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sSil ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sMixSlide ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sRet ()) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sVis () _) _
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sMixVis () _) _
-- neither accepts.
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | nothing | nothing | ()
-- Absurd: non-mix shapes.
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-trace-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()

Interleave-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  {s : List (Event√ E (R × S))}
  → traces (_⦀_ {I = I} {R = R} {S = S} P Q) s
  → InterleaveSplit P Q s
Interleave-trace P Q (_ , bs) = Interleave-trace-aux P Q bs

-----------------------------------------------------------------------------------------
-- Synchronised parallel  P ∥⇘ cs ¿ dec ⇙ Q
-- traces [P ∥cs⇙ Q] = a synchronised merge of P's and Q's plain-event traces:
--   • events in cs must be performed by both sides simultaneously (sync-both)
--   • events outside cs are interleaved (sync-l, sync-r)
-- After one side terminates with √, the other can only progress on events
-- outside cs (distributed termination, UCS p136).

-- Synchronised merge predicate.
data Sync (cs : AnyTypes E → Set) : List (Event E) → List (Event E) → List (Event E)
                                  → Set (lsuc ℓ ⊔ ℓe) where
  sync-nil  : Sync cs [] [] []
  sync-l    : ∀ {sP sQ s e}
            → ¬ cs (Event.A e , Event.e e)
            → Sync cs sP sQ s
            → Sync cs (e ∷ sP) sQ (e ∷ s)
  sync-r    : ∀ {sP sQ s e}
            → ¬ cs (Event.A e , Event.e e)
            → Sync cs sP sQ s
            → Sync cs sP (e ∷ sQ) (e ∷ s)
  sync-both : ∀ {sP sQ s e}
            → cs (Event.A e , Event.e e)
            → Sync cs sP sQ s
            → Sync cs (e ∷ sP) (e ∷ sQ) (e ∷ s)

-- Splitting witness for traces of (P ∥cs⇙ Q).
data SyncSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (cs : AnyTypes E → Set)
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  : List (Event√ E (R × S)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where

  in-progress : ∀ {sP sQ s : List (Event E)}
              → Sync cs sP sQ s
              → traces P (map evl sP)
              → traces Q (map evl sQ)
              → SyncSplit cs P Q (map evl s)

  done : ∀ {sP sQ s : List (Event E)} {r : R} {q : S}
       → Sync cs sP sQ s
       → traces P (map evl sP ++ [ √ r ])
       → traces Q (map evl sQ ++ [ √ q ])
       → SyncSplit cs P Q (map evl s ++ [ √ (r , q) ])

Parallel-trace-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (cs : AnyTypes E → Set)
  (dec : (at : AnyTypes E) → Dec (cs at))
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_∥⇘_¿_⇙_ {I = I} {R = R} {S = S} P cs dec Q) ═⟨ s ⟩═► t′
  → SyncSplit cs P Q s

-- 1. Empty trace
Parallel-trace-aux P Q cs dec bNil =
  in-progress sync-nil (_ , bNil) (_ , bNil)

-- 2. Tau via sSil — sil head from P or from Q
Parallel-trace-aux P Q cs dec (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | sil P' | _ | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sSil p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sSil p-eq) trP') trQ
... | ret _ | sil Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | vis _ | sil Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | ndbr _ _ _ _ | sil Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
-- NEW: mix | sil Q' — Q's silent step propagates (user's _∥⇘_¿_⇙_ rule).
... | mix _ _ | sil Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
-- impossible (force(P ∥cs⇙ Q) is not sil for these heads)
... | ret _ | ret _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sSil (force is mix or ndbr for these, not sil)
... | ret _ | mix _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 3. Visible step via sVis
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- (a) vis | ret : P moves alone — only when at ∉ cs
... | vis fP | ret _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fP at a in fp-eq | eq-j
... | just P' | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | ()

-- (b) ret | vis : Q moves alone — only when at ∉ cs
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | nothing | ()

-- (c) vis | vis : split on dec at
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl with dec at
-- (c.1) at ∈ cs : both must accept
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just Q' | refl =
    case Parallel-trace-aux P' Q' cs dec big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just _ | nothing | ()
... | nothing | just _ | ()
... | nothing | nothing | ()

-- (c.2) at ∉ cs : interleave
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just P' | just Q' | refl with big-step
-- inner trace empty: outer trace is just [at]; default to P'-side
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (sync-l ¬p sync-nil)
                (_ , bStep (sVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P' Q cs dec inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P Q' cs dec inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
-- other internal-choice indices: br2 returns nothing → eq-int-j absurd
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
-- force ((P' ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ Q')) is ndbr; sSil/sVis/sRet impossible
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sSil ()) _
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sRet ()) _
-- neither accepts: merge yields nothing → eq-j impossible
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | nothing | nothing | ()

-- (d) absurd head combinations for sVis
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sVis.
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | vis _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 4. Termination via sRet — only when both P and Q are at ret simultaneously
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret rP | ret rQ | refl with big-step
...   | bNil =
        done sync-nil
             (_ , bStep (sRet p-eq) bNil)
             (_ , bStep (sRet q-eq) bNil)
...   | bTau (sSil ()) _
...   | bTau (sNdbr () _) _
...   | bStep (sRet ()) _
...   | bStep (sVis refl ()) _
-- absurd head combinations for sRet
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | sil _ | _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ret _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ret _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | vis _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | vis _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | vis _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sRet.
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | mix _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | mix _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | mix _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ret _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | vis _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 5. Tau via sNdbr — at least one of P, Q has an ndbr head (cs is irrelevant for τ)
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- (a) ret | ndbr : Q moves alone (Q-distribution)
... | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (b) vis | ndbr : Q moves alone
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (d) ndbr | vis : P moves alone
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (e) ndbr | ndbr : both ndbr; merge on pair indices
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  with i | a
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
... | just P' | nothing | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
... | nothing | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
... | just P' | just Q' | refl =
    case Parallel-trace-aux P' Q' cs dec big-step of λ where
      (in-progress merge (_ , trP') (_ , trQ')) →
        in-progress merge
                    (_ , bTau (sNdbr p-eq fp'-eq) trP')
                    (_ , bTau (sNdbr q-eq fq'-eq) trQ')
      (done merge (_ , trP') (_ , trQ')) →
        done merge
             (_ , bTau (sNdbr p-eq fp'-eq) trP')
             (_ , bTau (sNdbr q-eq fq'-eq) trQ')
... | nothing | nothing | ()

-- (f) absurd head combinations for sNdbr
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | ret _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | vis _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()

-- (g) NEW: mix | ndbr — Q distributes through ndbr.
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (h) NEW: ndbr | mix — P distributes through ndbr.
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (i) NEW: mix-shape absurds for sNdbr.
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bTau (sNdbr eq-f eq-j) big-step) | vis _ | mix _ _ | ()

-- ----- 6. NEW: bTau via sMixSlide. force (P ∥cs⇙ Q) ≡ mix _ Qt. -----
Parallel-trace-aux P Q cs dec (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix: Q slides.
... | ret _ | mix _ Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | mix: both slide.
... | mix _ P' | mix _ Q' | refl =
    case Parallel-trace-aux P' Q' cs dec big-step of λ where
      (in-progress merge (_ , trP') (_ , trQ')) →
        in-progress merge
                    (_ , bTau (sMixSlide p-eq) trP')
                    (_ , bTau (sMixSlide q-eq) trQ')
      (done merge (_ , trP') (_ , trQ')) →
        done merge
             (_ , bTau (sMixSlide p-eq) trP')
             (_ , bTau (sMixSlide q-eq) trQ')
-- Absurd: all non-mix shapes.
... | sil _ | _ | ()
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- ----- 7. NEW: bStep via sMixVis. -----
-- ret | mix fQ _: mix's vis applies dec-filter then fQ. Q fires via sMixVis (only outside cs).
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret _ | mix fQ _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fQ at a in fq-eq | eq-j
... | just _ | refl =
    case Parallel-trace-aux P _ cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | nothing | ()

-- mix | ret: symmetric — P fires via sMixVis (only outside cs).
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fP at a in fp-eq | eq-j
... | just _ | refl =
    case Parallel-trace-aux _ Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | ()

-- vis | mix: mix's vis merges fP and fQ; dec-filter splits.  Mirrors vis|vis but Q fires sMixVis.
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just _ | refl =
    case Parallel-trace-aux P' _ cs dec big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just P' | just Q' | refl with big-step
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (sync-l ¬p sync-nil)
                (_ , bStep (sVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P' Q cs dec inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P Q' cs dec inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sSil ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sMixSlide ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sRet ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sMixVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | nothing | nothing | ()

-- mix | vis: symmetric to vis | mix.  P fires via sMixVis, Q via sVis.
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _  | just Q' | refl =
    case Parallel-trace-aux _ Q' cs dec big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just P' | just Q' | refl with big-step
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (sync-l ¬p sync-nil)
                (_ , bStep (sMixVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P' Q cs dec inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P Q' cs dec inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sSil ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sMixSlide ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sRet ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sMixVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | nothing | nothing | ()

-- mix | mix: both fire via sMixVis.  Mirrors vis|vis structure.
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _ | just _ | refl =
    case Parallel-trace-aux _ _ cs dec big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    case Parallel-trace-aux P' Q cs dec big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | just Q' | refl =
    case Parallel-trace-aux P Q' cs dec big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just P' | just Q' | refl with big-step
... | bNil =
    in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ []}
                (sync-l ¬p sync-nil)
                (_ , bStep (sMixVis p-eq fp-eq) bNil)
                (_ , bNil)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P' Q cs dec inner-bs of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l ¬p merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l ¬p merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    case Parallel-trace-aux P Q' cs dec inner-bs of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬p merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬p merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sSil ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sMixSlide ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sRet ()) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bStep (sMixVis () _) _
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | nothing | nothing | ()
-- Absurd: non-mix shapes (must use full function-name clauses, not `...`,
-- because the preceding deep-nested productive case escapes outer-with continuation).
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ret _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | vis _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()

Parallel-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (cs : AnyTypes E → Set)
  (dec : (at : AnyTypes E) → Dec (cs at))
  {s : List (Event√ E (R × S))}
  → traces (_∥⇘_¿_⇙_ {I = I} {R = R} {S = S} P cs dec Q) s
  → SyncSplit cs P Q s
Parallel-trace P Q cs dec (_ , bs) = Parallel-trace-aux P Q cs dec bs

-----------------------------------------------------------------------------------------
-- Sliding : P ▷ Q

sliding-trace-helper : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ dec : DecEq R ⦄
  {s : List (Event√ E R)}
   (P Q : ITree E (ExtI I) R) (t-f : ITree E (ExtI I) R)
   → (P ▷ Q) ═⟨ s ⟩═► t-f 
   → traces P s ⊎ traces Q s

-- Base Case
sliding-trace-helper P Q t-f bNil = inj₁ (P , bNil)

-- 1. Silent Step: sSil
-- Productive only when P.force = sil P' and Q.force ≠ ndbr (force(P ▷ Q) = sil (P' ▷ Q)).
-- All other 5×5−4 = 21 combinations are absurd.  Wildcards on Q.force can't reduce
-- past ▷'s with-abstraction; we must case explicitly on each Q.force shape.
sliding-trace-helper P Q t-f (bTau (sSil eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | sil P' | ret _ | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sSil eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | sil P' | sil _ | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sSil eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | sil P' | vis _ | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sSil eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | sil P' | mix _ _ | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sSil eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | sil _ | ndbr _ _ _ _ | ()  -- ▷-rule-1: force = ndbr
-- ret | * : force = ret (or ndbr when *=ndbr)
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | mix _ _ | ()
... | ret _ | ndbr _ _ _ _ | ()
-- vis | * : force = mix fP Q (or ndbr when *=ndbr)
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | mix _ _ | ()
... | vis _ | ndbr _ _ _ _ | ()
-- ndbr | * : force = ndbr (P-distr or Q-distr)
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- mix | * : force = mix (or ndbr when *=ndbr)
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | mix _ _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- 2. Silent Step: sNdbr
-- Productive when force(P ▷ Q) is ndbr:
--   (a) Q.force = ndbr fQ  → ndbr (mergeNdbr▷-R P fQ) ...     (Q distributes; any P)
--   (b) Q.force ≠ ndbr ∧ P.force = ndbr fP → ndbr (mergeNdbr▷-L fP Q) ... (P distributes)
-- (a) Q distributes — all 5 P-shapes × ndbr Q.
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case sliding-trace-helper P Q' t-f big-step of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (tend , trQ')) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | sil _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case sliding-trace-helper P Q' t-f big-step of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (tend , trQ')) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | vis _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case sliding-trace-helper P Q' t-f big-step of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (tend , trQ')) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr _ _ _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case sliding-trace-helper P Q' t-f big-step of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (tend , trQ')) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | mix _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case sliding-trace-helper P Q' t-f big-step of λ where
      (inj₁ trP)           → inj₁ trP
      (inj₂ (tend , trQ')) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
-- (b) P distributes — Q is not ndbr.  Sub-case on fP i a.
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP')
      (inj₂ trQ)           → inj₂ trQ
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | sil _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP')
      (inj₂ trQ)           → inj₂ trQ
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP')
      (inj₂ trQ)           → inj₂ trQ
... | nothing | ()
sliding-trace-helper P Q t-f (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP')
      (inj₂ trQ)           → inj₂ trQ
... | nothing | ()
-- Absurd cases — force is not ndbr.
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | ret _ | ret _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | ret _ | sil _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | ret _ | vis _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | ret _ | mix _ _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | sil _ | ret _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | sil _ | sil _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | sil _ | vis _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | sil _ | mix _ _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | vis _ | ret _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | vis _ | sil _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | vis _ | vis _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | vis _ | mix _ _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | mix _ _ | ret _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | mix _ _ | sil _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | mix _ _ | vis _ | ()
sliding-trace-helper P Q t-f (bTau (sNdbr eq eq-j) big-step) | mix _ _ | mix _ _ | ()

-- 3. Visible Step: sVis
-- Under new ▷, force(P ▷ Q) is never `vis _`: it's ret / sil / mix / ndbr.
-- All sVis cases are therefore absurd; wildcard Q is left unreduced past ▷'s
-- with-abstraction, so we must enumerate every Q.force shape per P.force shape.
sliding-trace-helper P Q t-f (bStep (sVis eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 4. Visible Step: sRet
sliding-trace-helper P Q t-f (bStep (sRet eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret r | ndbr _ _ _ _ | ()  -- new _▷_: ret|ndbr produces ndbr, not ret
... | ret r | ret _ | refl =
    inj₁ (t-f , bStep (sRet eq-P) big-step)
... | ret r | sil _ | refl =
    inj₁ (t-f , bStep (sRet eq-P) big-step)
... | ret r | vis _ | refl =
    inj₁ (t-f , bStep (sRet eq-P) big-step)
... | ret r | mix _ _ | refl =
    inj₁ (t-f , bStep (sRet eq-P) big-step)
-- sil | * : force = sil (P' ▷ Q) or ndbr
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
-- vis | * : force = mix fP Q (or ndbr if Q=ndbr)
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
-- ndbr | * : force = ndbr (always)
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
-- mix | * : force = mix (or ndbr if Q=ndbr)
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 5. NEW: Silent Step: sMixSlide
-- Under new ▷:
--   P=vis fP, Q≠ndbr → force = mix fP Q.  Slide goes to Q.  Result: Q-trace.
--   P=mix fP P', Q≠ndbr → force = mix fP (P' ▷ Q).  Slide goes to (P' ▷ Q); recurse.
sliding-trace-helper P Q t-f (bTau (sMixSlide eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = inj₂ (t-f , big-step)
... | vis _ | sil _   | refl = inj₂ (t-f , big-step)
... | vis _ | vis _   | refl = inj₂ (t-f , big-step)
... | vis _ | mix _ _ | refl = inj₂ (t-f , big-step)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ P' | ret _   | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sMixSlide eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | mix _ P' | sil _   | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sMixSlide eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | mix _ P' | vis _   | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sMixSlide eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | mix _ P' | mix _ _ | refl =
    case sliding-trace-helper P' Q t-f big-step of λ where
      (inj₁ (tend , trP')) → inj₁ (tend , bTau (sMixSlide eq-P) trP')
      (inj₂ trQ)           → inj₂ trQ
... | mix _ _  | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- 6. NEW: Visible Step: sMixVis
-- P=vis fP, Q≠ndbr → force = mix fP Q.  Visible fire of fP at a — P-side step.
-- P=mix fP P', Q≠ndbr → force = mix fP (P' ▷ Q).  Visible fire of fP at a — P-side step.
sliding-trace-helper P Q t-f (bStep (sMixVis {at = at} {a = a} eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = inj₁ (t-f , bStep (sVis eq-P eq-j) big-step)
... | vis _ | sil _   | refl = inj₁ (t-f , bStep (sVis eq-P eq-j) big-step)
... | vis _ | vis _   | refl = inj₁ (t-f , bStep (sVis eq-P eq-j) big-step)
... | vis _ | mix _ _ | refl = inj₁ (t-f , bStep (sVis eq-P eq-j) big-step)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _   | refl = inj₁ (t-f , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | sil _   | refl = inj₁ (t-f , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | vis _   | refl = inj₁ (t-f , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | mix _ _ | refl = inj₁ (t-f , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

Sliding-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ dec : DecEq R ⦄
  (P Q : ITree E (ExtI I) R) {s : List (Event√ E R)}
  → traces {I = ExtI I} {R = R} (_▷_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s
Sliding-trace P Q (t-f , tr) = sliding-trace-helper P Q t-f tr  

-----------------------------------------------------------------------------------------
-- iter-bind

-- Specifically for iter-bind, similar to bindSplit or iterSplit
data IterGBindSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
  (t-final : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Case 1: c is still executing
  in-c : ∀ {c'} {s : List (Event E)}
       → traces c (map evl s)
       → t-final ≡ iter-bind c' body
       → IterGBindSplit c body t-final (map evl s)

  -- Case 2: c finished with inj₁ a', handing control directly to the loop.
  in-loop' : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)            
       → traces c (map evl s1 ++ [ √ (inj₁ a') ]) 
       → traces (iter body a') s2
       → IterGBindSplit c body t-final s

  -- Case 3: c finished with inj₂ r, finalizing the result.
  in-done' : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)            
       → traces c (map evl s1 ++ [ √ (inj₂ r) ]) 
       → traces {I = ExtI I} (Ret r) s2     
       → IterGBindSplit c body t-final s

-- A helper to allow us to induct on the transition directly for iter-bind
iter-bind-trace-helper : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (c : ITree E (ExtI I) (A ⊎ R)) (body : A → ITree E (ExtI I) (A ⊎ R))
   {s : List (Event√ E R)} (t-f : ITree E (ExtI I) R)
   → iter-bind c body ═⟨ s ⟩═► t-f 
   → Σ (ITree E (ExtI I) R) (λ t-f' → IterGBindSplit c body t-f' s)

-- Base Case
iter-bind-trace-helper c body t-f bNil = t-f , in-c (c , bNil) refl

-- 1. Handling Silent Steps (Tau via sSil)
iter-bind-trace-helper c body t-f (bTau (sSil {t = next} eq-f) big-step) with c .force in c-eq | eq-f
... | sil c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c (c'' , c-step) eq) → 
          tend , in-c (c'' , bTau (sSil c-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' eq-s (c'' , bTau (sSil c-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' eq-s (c'' , bTau (sSil c-eq) c-step) trk2

... | ret (inj₁ a') | refl = 
    -- iter-bind c body evaluates to sil (iter body a'). 
    -- Matching refl proves `next` is exactly `iter body a'`, 
    -- meaning `big-step` is exactly the trace of `iter body a'`!
    t-f , in-loop' refl (_ , bStep (sRet c-eq) bNil) (t-f , big-step)

... | ret (inj₂ r) | () -- ret ≡ sil is absurd

... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 2. Handling Non-deterministic Steps (Tau via sNdbr)
iter-bind-trace-helper c body t-f (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | ndbr f wi wa wp | refl with f i a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c (c'' , c-step) eq) → 
          tend , in-c (c'' , bTau (sNdbr c-eq fi-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' eq-s (c'' , bTau (sNdbr c-eq fi-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' eq-s (c'' , bTau (sNdbr c-eq fi-eq) c-step) trk2
... | nothing | ()

-- Absurd cases for sNdbr
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | sil _   | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | vis _   | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body t-f (bTau (sNdbr eq-f eq-j) big-step) | ret (inj₂ _) | ()

-- 3. Handling Visible Steps (e via sVis)
iter-bind-trace-helper c body t-f (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | vis f | refl with f at a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c {s = sP} (c'' , c-step) eq) → 
          tend , in-c {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (c'' , bStep (sVis c-eq fi-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) → 
          tend , in-loop' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sVis c-eq fi-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) → 
          tend , in-done' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sVis c-eq fi-eq) c-step) trk2
... | nothing | ()

-- Absurd cases for sVis
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | sil _        | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body t-f (bStep (sVis eq-f eq-j) big-step) | ret (inj₂ _) | ()

-- 4. Handling Termination (sRet)
iter-bind-trace-helper c body t-f (bStep (sRet {x = res} eq-f) big-step) with c .force in c-eq | eq-f
... | ret (inj₂ r) | refl = 
    -- Hand-off point. iter-bind evaluated to `ret r`.
    t-f , in-done' {s1 = []} refl (_ , bStep (sRet c-eq) bNil) (t-f , bStep (sRet refl) big-step)

... | ret (inj₁ a') | () -- sil ≡ ret is absurd

-- Absurd cases for sRet
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | sil _        | ()
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | vis _        | ()
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ()
iter-bind-trace-helper c body t-f (bStep (sRet eq-f) big-step) | mix _ _      | ()

-- 5. NEW: bTau via sMixSlide. force(iter-bind c body) ≡ mix _ (iter-bind Qt body) when c.force = mix _ Qt.
iter-bind-trace-helper c body t-f (bTau (sMixSlide eq-f) big-step) with c .force in c-eq | eq-f
... | mix _ Qt | refl =
    case iter-bind-trace-helper Qt body t-f big-step of λ where
      (tend , in-c (c' , c-step) eq) →
          tend , in-c (c' , bTau (sMixSlide c-eq) c-step) eq
      (tend , in-loop' eq-s (c' , c-step) trk2) →
          tend , in-loop' eq-s (c' , bTau (sMixSlide c-eq) c-step) trk2
      (tend , in-done' eq-s (c' , c-step) trk2) →
          tend , in-done' eq-s (c' , bTau (sMixSlide c-eq) c-step) trk2
... | sil _        | ()
... | ret (inj₁ _) | ()
... | ret (inj₂ _) | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()

-- 6. NEW: bStep via sMixVis.
iter-bind-trace-helper c body t-f (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step) with c .force in c-eq | eq-f
... | mix f _ | refl with f at a in fi-eq | eq-j
... | just c' | refl =
    case iter-bind-trace-helper c' body t-f big-step of λ where
      (tend , in-c {s = sP} (c'' , c-step) eq) →
          tend , in-c {s = (evLabel (proj₁ at) (proj₂ at) a) ∷ sP} (c'' , bStep (sMixVis c-eq fi-eq) c-step) eq
      (tend , in-loop' eq-s (c'' , c-step) trk2) →
          tend , in-loop' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sMixVis c-eq fi-eq) c-step) trk2
      (tend , in-done' eq-s (c'' , c-step) trk2) →
          tend , in-done' (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a) ∷ xs) eq-s) (c'' , bStep (sMixVis c-eq fi-eq) c-step) trk2
... | nothing | ()
-- Absurd shape mismatches for sMixVis.
iter-bind-trace-helper c body t-f (bStep (sMixVis eq-f eq-j) big-step) | sil _        | ()
iter-bind-trace-helper c body t-f (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₁ _) | ()
iter-bind-trace-helper c body t-f (bStep (sMixVis eq-f eq-j) big-step) | ret (inj₂ _) | ()
iter-bind-trace-helper c body t-f (bStep (sMixVis eq-f eq-j) big-step) | vis _        | ()
iter-bind-trace-helper c body t-f (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ()

-----------------------------------------------------------------------------------------
-- iter

data IterSplit {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
  (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A) (t-final : ITree E (ExtI I) R) 
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Case 1: Actively executing `body a`. (Maps to BindSplit.in-P)
  in-body : ∀ {P'} {s : List (Event E)}
       → traces (body a) (map evl s)
       → t-final ≡ iter-bind P' body -- (P' >>= iterStep body)
       → IterSplit body a t-final (map evl s)

  -- Case 2: The body finished with `inj₁ a'`, handing control back to the loop.
  in-loop : ∀ {a' : A} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)
       → traces (body a) (map evl s1 ++ [ √ (inj₁ a') ])
       → traces (Tau (iter body a')) s2
       → IterSplit body a t-final s

  -- Case 3: The body finished with `inj₂ r`, returning the final result.
  in-done : ∀ {r : R} {s1 : List (Event E)} {s2 : List (Event√ E R)} {s}
       → (s ≡ map evl s1 ++ s2)
       → traces (body a) (map evl s1 ++ [ √ (inj₂ r) ])
       → traces {I = ExtI I} (Ret r) s2
       → IterSplit body a t-final s

iter-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {A : Set ℓ} {R : Set ℓr}
   (body : A → ITree E (ExtI I) (A ⊎ R)) (a : A)
   {s : List (Event√ E R)}
   → traces (iter body a) s
   → Σ (ITree E (ExtI I) R) (λ t-f → IterSplit body a t-f s)

iter-trace body a (t-f , bNil) = 
    t-f , in-body (body a , bNil) refl

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a') with eq-f
...                  | refl  =
    -- Because `body a` returned `inj₁ a'`, the body has completed 
    -- its step and handed control back to the loop. 
    -- This is always an `in-loop` case for `body a`.
    t-f , in-loop refl (_ , bStep (sRet b-eq) bNil) (_ , bTau (sSil refl) big-step)

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | ret (inj₂ r) = 
    -- iter body a .force = ret r in this branch, sSil is impossible
    t-f , in-done refl (_ , bStep (sRet b-eq) bNil) (_ , bTau (sSil eq-f) big-step)

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | sil c with eq-f
...        | refl = 
    -- iter body a .force = sil (c >>= iterStep body)
    case iter-bind-trace-helper c body t-f big-step of λ where
      (tend , in-c {c' = c'} (c_end , c-step) eq-P) → 
          tend , in-body (c_end , bTau (sSil b-eq) c-step) eq-P

      (tend , in-loop' eq-s (c_end , c-step) (k_end , k-step)) → 
          tend , in-loop eq-s 
              (c_end , bTau (sSil b-eq) c-step) 
              (k_end , bTau (sSil refl) k-step)
              
      (tend , in-done' eq-s (c_end , c-step) trK) → 
          tend , in-done eq-s 
              (c_end , bTau (sSil b-eq) c-step) 
              trK
              
iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | vis f = 
    -- iter body a .force = vis (...), sSil is impossible here
    case eq-f of λ ()

iter-trace body a (t-f , bTau (sSil {t = next} eq-f) big-step) 
  | ndbr f wi wa wp = 
    case eq-f of λ ()

iter-trace body a (t-f , bTau (sNdbr {i = i} {a = a'} eq-f eq-j) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp with eq-f
...   | refl with f i a' in fi-eq | eq-j
...     | just t' | refl =
        -- We pass t' and big-step! 
        case iter-bind-trace-helper t' body t-f big-step of λ where
          (tend , in-c (c' , c-step) eq-P) → 
              tend , in-body (c' , bTau (sNdbr b-eq fi-eq) c-step) eq-P
              
          (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) → 
              tend , in-loop eq-s 
                  (c' , bTau (sNdbr b-eq fi-eq) c-step) 
                  (k_end , bTau (sSil refl) k-step)
                  
          (tend , in-done' eq-s (c' , c-step) trK) → 
              tend , in-done eq-s 
                  (c' , bTau (sNdbr b-eq fi-eq) c-step) 
                  trK
...     | nothing | ()

iter-trace body a (t-f , bStep (sVis {at = at} {a = a'} eq-f eq-j) big-step) 
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   = case eq-f of λ ()
... | sil c          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()
... | vis f with eq-f
...   | refl with f at a' in fi-eq | eq-j
...     | just t' | refl =
        -- We pass t' and big-step!
        case iter-bind-trace-helper t' body t-f big-step of λ where
          (tend , in-c {s = sP} (c' , c-step) eq-P) → 
              tend , in-body (c' , bStep (sVis b-eq fi-eq) c-step) eq-P
              
          (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) → 
              tend , in-loop (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s) 
                  (c' , bStep (sVis b-eq fi-eq) c-step) 
                  (k_end , bTau (sSil refl) k-step)
                  
          (tend , in-done' eq-s (c' , c-step) trK) → 
              tend , in-done (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s) 
                  (c' , bStep (sVis b-eq fi-eq) c-step) 
                  trK

iter-trace body a (t-f , bStep (sRet {x = x} eq-f) big-step)
    with body a .force in b-eq
... | ret (inj₁ a'') = case eq-f of λ ()
... | ret (inj₂ r)   =
    -- iter body a .force = ret r, sRet step gives x = r
    t-f , in-done {s1 = []} refl
        (_ , bStep (sRet b-eq) bNil)
        (_ , bStep (sRet eq-f) big-step)
... | sil c          = case eq-f of λ ()
... | vis f          = case eq-f of λ ()
... | ndbr f wi wa wp = case eq-f of λ ()
... | mix _ _        = case eq-f of λ ()

-- NEW: sMixSlide for iter-trace. body a .force = mix _ Qt → recurse on Qt via iter-bind-trace-helper.
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step)
    with body a .force in b-eq
... | mix _ Qt with eq-f
...   | refl =
    case iter-bind-trace-helper Qt body t-f big-step of λ where
      (tend , in-c (c' , c-step) eq-P) →
          tend , in-body (c' , bTau (sMixSlide b-eq) c-step) eq-P
      (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) →
          tend , in-loop eq-s
              (c' , bTau (sMixSlide b-eq) c-step)
              (k_end , bTau (sSil refl) k-step)
      (tend , in-done' eq-s (c' , c-step) trK) →
          tend , in-done eq-s
              (c' , bTau (sMixSlide b-eq) c-step)
              trK
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step) | ret (inj₁ _) = case eq-f of λ ()
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step) | ret (inj₂ _) = case eq-f of λ ()
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step) | sil _        = case eq-f of λ ()
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step) | vis _        = case eq-f of λ ()
iter-trace body a (t-f , bTau (sMixSlide eq-f) big-step) | ndbr _ _ _ _ = case eq-f of λ ()

-- NEW: sMixVis for iter-trace. body a .force = mix f _ → fire visible event via merged f.
iter-trace body a (t-f , bStep (sMixVis {at = at} {a = a'} eq-f eq-j) big-step)
    with body a .force in b-eq
... | mix f _ with eq-f
...   | refl with f at a' in fi-eq | eq-j
...     | just t' | refl =
        case iter-bind-trace-helper t' body t-f big-step of λ where
          (tend , in-c {s = sP} (c' , c-step) eq-P) →
              tend , in-body (c' , bStep (sMixVis b-eq fi-eq) c-step) eq-P
          (tend , in-loop' eq-s (c' , c-step) (k_end , k-step)) →
              tend , in-loop (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (c' , bStep (sMixVis b-eq fi-eq) c-step)
                  (k_end , bTau (sSil refl) k-step)
          (tend , in-done' eq-s (c' , c-step) trK) →
              tend , in-done (cong (λ xs → evl (evLabel (proj₁ at) (proj₂ at) a') ∷ xs) eq-s)
                  (c' , bStep (sMixVis b-eq fi-eq) c-step)
                  trK
...     | nothing | ()
iter-trace body a (t-f , bStep (sMixVis eq-f eq-j) big-step) | ret (inj₁ _) = case eq-f of λ ()
iter-trace body a (t-f , bStep (sMixVis eq-f eq-j) big-step) | ret (inj₂ _) = case eq-f of λ ()
iter-trace body a (t-f , bStep (sMixVis eq-f eq-j) big-step) | sil _        = case eq-f of λ ()
iter-trace body a (t-f , bStep (sMixVis eq-f eq-j) big-step) | vis _        = case eq-f of λ ()
iter-trace body a (t-f , bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ = case eq-f of λ ()

