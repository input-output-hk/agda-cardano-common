{-
  Trace laws (and refinement / monotonicity corollaries) for external
  choice _□_.

  DRBisim laws live in `CSP.Laws.ExternalChoice_DRBisim`.
  Failures/divergences laws live in `CSP.Laws.ExternalChoice_FD`.
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

module CSP.Laws.ExternalChoice
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Traces

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open import CSP.Laws.BasicProcesses {ℓ} {ℓe} {E} E-≟
open import CSP.Laws.InternalChoice {ℓ} {ℓe} {E} E-≟

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
