{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; _++_; _∷_; []; [_]; map)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

module CSP.Laws.AlphaParallel
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Label
open Traces

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟
import CSP.Definitions.AlphaParallel {ℓ} {ℓe} {E} as CSPAPar
open CSPAPar E-≟

-------------------------------------------------------------------------------------
-- Synchronisation merge predicate (two alphabets, dual guards).
-- An event routes by alphabet membership:
--   sync-l    : event in A only      → P performs it solo
--   sync-r    : event in B only      → Q performs it solo
--   sync-both : event in both A and B → P and Q synchronise

data AlphaSync (A B : Alpha)
  : List (Event E) → List (Event E) → List (Event E) → Set (lsuc ℓ ⊔ ℓe) where
  sync-nil  : AlphaSync A B [] [] []
  sync-l    : ∀ {sP sQ s e}
            →   A (Event.A e , Event.e e) → ¬ B (Event.A e , Event.e e)
            → AlphaSync A B sP sQ s → AlphaSync A B (e ∷ sP) sQ (e ∷ s)
  sync-r    : ∀ {sP sQ s e}
            → ¬ A (Event.A e , Event.e e) →   B (Event.A e , Event.e e)
            → AlphaSync A B sP sQ s → AlphaSync A B sP (e ∷ sQ) (e ∷ s)
  sync-both : ∀ {sP sQ s e}
            →   A (Event.A e , Event.e e) →   B (Event.A e , Event.e e)
            → AlphaSync A B sP sQ s → AlphaSync A B (e ∷ sP) (e ∷ sQ) (e ∷ s)

-- Splitting witness for traces of the binary alphabetised parallel.
data AlphaSyncSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (A B : Alpha) (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  : List (Event√ E (R × S)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where
  in-progress : ∀ {sP sQ s : List (Event E)}
              → AlphaSync A B sP sQ s
              → traces P (map evl sP) → traces Q (map evl sQ)
              → AlphaSyncSplit A B P Q (map evl s)
  done : ∀ {sP sQ s : List (Event E)} {r : R} {q : S}
       → AlphaSync A B sP sQ s
       → traces P (map evl sP ++ [ √ r ]) → traces Q (map evl sQ ++ [ √ q ])
       → AlphaSyncSplit A B P Q (map evl s ++ [ √ (r , q) ])

-------------------------------------------------------------------------------------
-- Refusal-composition (IsStuck) for binary alphabetised parallel.
--
-- When both operands are `vis`-shaped and *every* event (at , a) is "blocked" — the
-- routing offer on the side(s) the alphabets require is `nothing` — the composite can
-- fire no event at all, hence `IsStuck`.  This is the key tool for deadlock proofs.

-- The routing fails for event (at , a): the composite cannot fire it.
Blocked : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    (A B : Alpha) (da : Dec-Alpha A) (db : Dec-Alpha B)
    (fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R)))
    (fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S)))
    (at : AnyTypes E) (a : proj₁ at) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
Blocked {ℓi = ℓi} {ℓr = ℓr} {ℓs = ℓs} A B da db fP fQ at a =
  case (da at , db at) of λ where
    -- both alphabets claim e: blocked iff either side refuses the offer
    (yes _ , yes _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
                          ((fP at a ≡ nothing) ⊎ (fQ at a ≡ nothing))
    -- only A claims e: blocked iff P refuses
    (yes _ , no  _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) (fP at a ≡ nothing)
    -- only B claims e: blocked iff Q refuses
    (no  _ , yes _) → Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) (fQ at a ≡ nothing)
    -- e in neither alphabet: always refused (vacuously blocked)
    (no  _ , no  _) → ⊤ {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs}

αpar-IsStuck : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
    {fP fQ}
  → P .force ≡ vis fP → Q .force ≡ vis fQ
  → (∀ (at : AnyTypes E) (a : proj₁ at) → Blocked A B da db fP fQ at a)
  → IsStuck (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
-- silent / ndbr / mix-slide steps: force is `vis`, contradicting the premise.
αpar-IsStuck eqP eqQ blocked (sRet eq)      rewrite eqP | eqQ = case eq of λ ()
αpar-IsStuck eqP eqQ blocked (sSil eq)      rewrite eqP | eqQ = case eq of λ ()
αpar-IsStuck eqP eqQ blocked (sNdbr eq _)   rewrite eqP | eqQ = case eq of λ ()
αpar-IsStuck eqP eqQ blocked (sMixSlide eq) rewrite eqP | eqQ = case eq of λ ()
αpar-IsStuck eqP eqQ blocked (sMixVis eq _) rewrite eqP | eqQ = case eq of λ ()
-- visible step: the merged offer at (at , a) is `nothing`, contradicting branch-eq.
αpar-IsStuck {da = da} {db = db} {fP = fP} {fQ = fQ} eqP eqQ blocked
             (sVis {at = at} {a = a} feq branch-eq)
  rewrite eqP | eqQ with feq
... | refl with da at      | db at      | blocked at a
...   | yes _    | yes _    | lift bl with fP at a | fQ at a | bl
...     | nothing  | _        | inj₁ refl = case branch-eq of λ ()
...     | just _   | nothing  | inj₂ refl = case branch-eq of λ ()
αpar-IsStuck {fP = fP} eqP eqQ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | yes _ | no _ | lift bl with fP at a | bl
...   | nothing | refl = case branch-eq of λ ()
αpar-IsStuck {fQ = fQ} eqP eqQ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | no _ | yes _ | lift bl with fQ at a | bl
...   | nothing | refl = case branch-eq of λ ()
αpar-IsStuck eqP eqQ blocked (sVis {at = at} {a = a} feq branch-eq)
  | refl | no _ | no _ | _ = case branch-eq of λ ()

-------------------------------------------------------------------------------------
-- Elimination law: every trace of (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) decomposes into
-- traces of P and Q merged by alphabet-driven synchronisation (AlphaSync).

AlphaParallel-trace-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (A : Alpha) (da : Dec-Alpha A) (B : Alpha) (db : Dec-Alpha B)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ═⟨ s ⟩═► t′
  → AlphaSyncSplit A B P Q s

-- 1. Empty trace
AlphaParallel-trace-aux P Q A da B db bNil =
  in-progress sync-nil (_ , bNil) (_ , bNil)

-- 2. Tau via sSil — sil head from P or from Q
AlphaParallel-trace-aux P Q A da B db (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | sil P' | _ | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sSil p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sSil p-eq) trP') trQ
... | ret _ | sil Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | vis _ | sil Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | ndbr _ _ _ _ | sil Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
... | mix _ _ | sil Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sSil q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sSil q-eq) trQ')
-- impossible (force(P ⟦…⟧ Q) is not sil for these heads)
... | ret _ | ret _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 4. Termination via sRet — only when both P and Q are at ret simultaneously
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step)
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
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | sil _ | _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ret _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ret _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | vis _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | vis _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | vis _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | mix _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | mix _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | mix _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ret _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | vis _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 5. Tau via sNdbr — at least one of P, Q has an ndbr head (alphabets irrelevant for τ)
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- (a) ret | ndbr : Q moves alone (Q-distribution)
... | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (b) vis | ndbr : Q moves alone
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (d) ndbr | vis : P moves alone
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (e) ndbr | ndbr : both ndbr; merge on pair indices
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  with i | a
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
... | just P' | nothing | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp'-eq) trP') trQ
... | nothing | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq'-eq) trQ')
... | just P' | just Q' | refl =
    case AlphaParallel-trace-aux P' Q' A da B db big-step of λ where
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
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | sil _ | _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | ret _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | ret _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | ret _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | vis _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | vis _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()

-- (g) mix | ndbr — Q distributes through ndbr.
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sNdbr q-eq fq-eq) trQ')
... | nothing | ()

-- (h) ndbr | mix — P distributes through ndbr.
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sNdbr p-eq fp-eq) trP') trQ
... | nothing | ()

-- (i) mix-shape absurds for sNdbr.
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | ret _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bTau (sNdbr eq-f eq-j) big-step) | vis _ | mix _ _ | ()

-- 3. Visible step via sVis — routing by (da at , db at)
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- (a) vis | ret : only A-solo (yes , no) can fire; other routings refuse.
... | vis fP | ret _ | refl with da at | db at
... | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | ret _ | refl | yes _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | ret _ | refl | no _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | ret _ | refl | no _ | no _ = case eq-j of λ ()

-- (b) ret | vis : only B-solo (no , yes) can fire; other routings refuse.
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with da at | db at
... | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl | yes _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl | yes _ | no _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl | no _ | no _ = case eq-j of λ ()

-- (c) vis | vis : split on (da at , db at)
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl with da at | db at
-- (c.1) both alphabets claim e: must synchronise
... | yes pA | yes pB with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just Q' | refl =
    case AlphaParallel-trace-aux P' Q' A da B db big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both pA pB merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both pA pB merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just _ | nothing | ()
... | nothing | just _ | ()
... | nothing | nothing | ()
-- (c.2) only A claims e: P steps alone
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
-- (c.3) only B claims e: Q steps alone
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | nothing | ()
-- (c.4) e in neither alphabet: refused — merged offer is nothing, eq-j absurd
AlphaParallel-trace-aux P Q A da B db (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no _ | no _ = case eq-j of λ ()

-- (d) absurd head combinations for sVis
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | sil _ | _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ret _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ret _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | vis _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | mix _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ret _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | vis _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 6. bTau via sMixSlide. force (P ⟦…⟧ Q) ≡ mix _ _.
AlphaParallel-trace-aux P Q A da B db (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix: Q slides.
... | ret _ | mix _ Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress merge trP (_ , trQ')) →
        in-progress merge trP (_ , bTau (sMixSlide q-eq) trQ')
      (done merge trP (_ , trQ')) →
        done merge trP (_ , bTau (sMixSlide q-eq) trQ')
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress merge (_ , trP') trQ) →
        in-progress merge (_ , bTau (sMixSlide p-eq) trP') trQ
      (done merge (_ , trP') trQ) →
        done merge (_ , bTau (sMixSlide p-eq) trP') trQ
-- mix | mix: both slide.
... | mix _ P' | mix _ Q' | refl =
    case AlphaParallel-trace-aux P' Q' A da B db big-step of λ where
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

-- 7. bStep via sMixVis — routing by (da at , db at).
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix: only B-solo (no , yes) can fire.
... | ret _ | mix fQ _ | refl with da at | db at
... | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux P _ A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | mix fQ _ | refl | yes _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | mix fQ _ | refl | yes _ | no _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | mix fQ _ | refl | no _ | no _ = case eq-j of λ ()

-- mix | ret: only A-solo (yes , no) can fire.
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with da at | db at
... | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux _ Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl | yes _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl | no _ | yes _ = case eq-j of λ ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl | no _ | no _ = case eq-j of λ ()

-- vis | mix: routing by (da at , db at).  P fires via sVis, Q via sMixVis.
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl with da at | db at
... | yes pA | yes pB with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just _ | refl =
    case AlphaParallel-trace-aux P' _ A da B db big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both pA pB merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both pA pB merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just P' | refl =
    case AlphaParallel-trace-aux P' Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux P _ A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no _ | no _ = case eq-j of λ ()

-- mix | vis: routing by (da at , db at).  P fires via sMixVis, Q via sVis.
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl with da at | db at
... | yes pA | yes pB with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _ | just Q' | refl =
    case AlphaParallel-trace-aux _ Q' A da B db big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both pA pB merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both pA pB merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux _ Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    case AlphaParallel-trace-aux P Q' A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sVis q-eq fq-eq) trQ')
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no _ | no _ = case eq-j of λ ()

-- mix | mix: routing by (da at , db at).  both fire via sMixVis.
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl with da at | db at
... | yes pA | yes pB with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _ | just _ | refl =
    case AlphaParallel-trace-aux _ _ A da B db big-step of λ where
      (in-progress {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-both pA pB merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sP = sPi} {sQ = sQi} merge (_ , trP') (_ , trQ')) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-both pA pB merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | yes pA | no ¬pB with fP at a in fp-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux _ Q A da B db big-step of λ where
      (in-progress {sP = sPi} merge (_ , trP') trQ) →
        in-progress {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
                    (sync-l pA ¬pB merge)
                    (_ , bStep (sMixVis p-eq fp-eq) trP')
                    trQ
      (done {sP = sPi} merge (_ , trP') trQ) →
        done {sP = evLabel (proj₁ at) (proj₂ at) a ∷ sPi}
             (sync-l pA ¬pB merge)
             (_ , bStep (sMixVis p-eq fp-eq) trP')
             trQ
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬pA | yes pB with fQ at a in fq-eq | eq-j
... | just _ | refl =
    case AlphaParallel-trace-aux P _ A da B db big-step of λ where
      (in-progress {sQ = sQi} merge trP (_ , trQ')) →
        in-progress {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
                    (sync-r ¬pA pB merge)
                    trP
                    (_ , bStep (sMixVis q-eq fq-eq) trQ')
      (done {sQ = sQi} merge trP (_ , trQ')) →
        done {sQ = evLabel (proj₁ at) (proj₂ at) a ∷ sQi}
             (sync-r ¬pA pB merge)
             trP
             (_ , bStep (sMixVis q-eq fq-eq) trQ')
... | nothing | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no _ | no _ = case eq-j of λ ()

-- Absurd: non-mix/non-vis shapes for sMixVis.
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | sil _ | _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ret _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ret _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | vis _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | vis _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
AlphaParallel-trace-aux P Q A da B db (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()

AlphaParallel-trace : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (A : Alpha) (da : Dec-Alpha A) (B : Alpha) (db : Dec-Alpha B)
  {s : List (Event√ E (R × S))}
  → traces (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) s
  → AlphaSyncSplit A B P Q s
AlphaParallel-trace P Q A da B db (_ , bs) = AlphaParallel-trace-aux P Q A da B db bs


-------------------------------------------------------------------------------------
-- STAGE 1: composite single-τ-step building blocks (introduction direction)
-------------------------------------------------------------------------------------

private
  -- ===== sil cases =====
  -- clause 1 (P sil): composite.force ≡ sil (P′⟦…⟧Q), for ANY Q.
  αpar-fsil-L :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
    → P .force ≡ sil P′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ sil (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-fsil-L eqP rewrite eqP = refl

  -- clause 2 (Q sil, P non-sil): composite.force ≡ sil (P⟦…⟧Q′).
  αpar-fsil-R :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    → (∀ {t} → P .force ≢ sil t)
    → Q .force ≡ sil Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ sil (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-fsil-R {P = P} ¬sP eqQ with P .force
  ... | ret _        rewrite eqQ = refl
  ... | vis _        rewrite eqQ = refl
  ... | ndbr _ _ _ _ rewrite eqQ = refl
  ... | mix _ _      rewrite eqQ = refl
  ... | sil _        = ⊥-elim (¬sP refl)

-- (1) P-sil advances unconditionally (operator clause 1).
αpar-sil-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
  → P .force ≡ sil P′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
αpar-sil-L eqP = sSil (αpar-fsil-L eqP)

-- (2) Q-sil advances only when P is not sil (operator clause 2).
αpar-sil-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
  → (∀ {t} → P .force ≢ sil t)
  → Q .force ≡ sil Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-sil-R ¬sP eqQ = sSil (αpar-fsil-R ¬sP eqQ)

private
  -- ===== P-ndbr distributes alone (Q ∈ {ret,vis,mix}) =====
  -- force helpers (one per Q-shape): composite.force ≡ ndbr f wi wa prf, f existential.
  αpar-fndbrL-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP wi wa wp} {s}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ ret s
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrL-ret eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-fndbrL-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP wi wa wp} {fQ}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrL-vis eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-fndbrL-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP wi wa wp} {fQ Qt}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ mix fQ Qt
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrL-mix eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  -- offer helpers: f i a ≡ just (P′⟦…⟧Q)  (P-distribution), one per Q-shape.
  αpar-offndbrL-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP wi wa wp i a} {s} {f prf}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ ret s → fP i a ≡ just P′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-offndbrL-ret eqP eqQ bP feq rewrite eqP | eqQ with feq
  ... | refl rewrite bP = refl

  αpar-offndbrL-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP wi wa wp i a} {fQ} {f prf}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ vis fQ → fP i a ≡ just P′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-offndbrL-vis eqP eqQ bP feq rewrite eqP | eqQ with feq
  ... | refl rewrite bP = refl

  αpar-offndbrL-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP wi wa wp i a} {fQ Qt} {f prf}
    → P .force ≡ ndbr fP wi wa wp → Q .force ≡ mix fQ Qt → fP i a ≡ just P′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-offndbrL-mix eqP eqQ bP feq rewrite eqP | eqQ with feq
  ... | refl rewrite bP = refl

-- (3) P-ndbr advances alone, when Q is ret / vis / mix (NOT sil, NOT ndbr).
αpar-ndbr-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
    {fP wi wa wp i a}
  → P .force ≡ ndbr fP wi wa wp → fP i a ≡ just P′
  → (∀ {t} → Q .force ≢ sil t)
  → (∀ {f wi′ wa′ wp′} → Q .force ≢ ndbr f wi′ wa′ wp′)
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
αpar-ndbr-L {Q = Q} eqP bP ¬sQ ¬nQ with Q .force in eqQ
... | ret _ with αpar-fndbrL-ret eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrL-ret eqP eqQ bP feq)
αpar-ndbr-L {Q = Q} eqP bP ¬sQ ¬nQ | vis _ with αpar-fndbrL-vis eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrL-vis eqP eqQ bP feq)
αpar-ndbr-L {Q = Q} eqP bP ¬sQ ¬nQ | mix _ _ with αpar-fndbrL-mix eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrL-mix eqP eqQ bP feq)
αpar-ndbr-L {Q = Q} eqP bP ¬sQ ¬nQ | sil _ = ⊥-elim (¬sQ refl)
αpar-ndbr-L {Q = Q} eqP bP ¬sQ ¬nQ | ndbr _ _ _ _ = ⊥-elim (¬nQ refl)

private
  -- ===== Q-ndbr distributes alone (P ∈ {ret,vis,mix}, P not sil/ndbr) =====
  αpar-fndbrR-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fQ wi wa wp} {r}
    → P .force ≡ ret r → Q .force ≡ ndbr fQ wi wa wp
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrR-ret eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-fndbrR-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fQ wi wa wp} {fP}
    → P .force ≡ vis fP → Q .force ≡ ndbr fQ wi wa wp
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrR-vis eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-fndbrR-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fQ wi wa wp} {fP Pt}
    → P .force ≡ mix fP Pt → Q .force ≡ ndbr fQ wi wa wp
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf)
  αpar-fndbrR-mix eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-offndbrR-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fQ wi wa wp i a} {r} {f prf}
    → P .force ≡ ret r → Q .force ≡ ndbr fQ wi wa wp → fQ i a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-offndbrR-ret eqP eqQ bQ feq rewrite eqP | eqQ with feq
  ... | refl rewrite bQ = refl

  αpar-offndbrR-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fQ wi wa wp i a} {fP} {f prf}
    → P .force ≡ vis fP → Q .force ≡ ndbr fQ wi wa wp → fQ i a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-offndbrR-vis eqP eqQ bQ feq rewrite eqP | eqQ with feq
  ... | refl rewrite bQ = refl

  αpar-offndbrR-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fQ wi wa wp i a} {fP Pt} {f prf}
    → P .force ≡ mix fP Pt → Q .force ≡ ndbr fQ wi wa wp → fQ i a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f wi wa prf
    → f i a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-offndbrR-mix eqP eqQ bQ feq rewrite eqP | eqQ with feq
  ... | refl rewrite bQ = refl

-- (4) Q-ndbr advances alone, when P is ret / vis / mix (NOT sil, NOT ndbr).
αpar-ndbr-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    {fQ wi wa wp i a}
  → Q .force ≡ ndbr fQ wi wa wp → fQ i a ≡ just Q′
  → (∀ {t} → P .force ≢ sil t)
  → (∀ {f wi′ wa′ wp′} → P .force ≢ ndbr f wi′ wa′ wp′)
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-ndbr-R {P = P} eqQ bQ ¬sP ¬nP with P .force in eqP
... | ret _ with αpar-fndbrR-ret eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrR-ret eqP eqQ bQ feq)
αpar-ndbr-R {P = P} eqQ bQ ¬sP ¬nP | vis _ with αpar-fndbrR-vis eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrR-vis eqP eqQ bQ feq)
αpar-ndbr-R {P = P} eqQ bQ ¬sP ¬nP | mix _ _ with αpar-fndbrR-mix eqP eqQ
...   | f , prf , feq = sNdbr feq (αpar-offndbrR-mix eqP eqQ bQ feq)
αpar-ndbr-R {P = P} eqQ bQ ¬sP ¬nP | sil _ = ⊥-elim (¬sP refl)
αpar-ndbr-R {P = P} eqQ bQ ¬sP ¬nP | ndbr _ _ _ _ = ⊥-elim (¬nP refl)

private
  -- ===== both ndbr: synchronous merge at a `pair` index =====
  αpar-fndbr-both :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP AP iP waP wpP} {fQ AQ iQ waQ wpQ}
    → P .force ≡ ndbr fP (AP , iP) waP wpP
    → Q .force ≡ ndbr fQ (AQ , iQ) waQ wpQ
    → Σ[ f ∈ _ ] Σ[ prf ∈ _ ]
        ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force
           ≡ ndbr f ((AP × AQ) , pair iP iQ) (waP , waQ) prf)
  αpar-fndbr-both eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  αpar-offndbr-both :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP AP iP waP wpP} {fQ AQ iQ waQ wpQ}
      {APx iPx aPx AQx iQx aQx} {f prf}
    → P .force ≡ ndbr fP (AP , iP) waP wpP
    → Q .force ≡ ndbr fQ (AQ , iQ) waQ wpQ
    → fP (APx , iPx) aPx ≡ just P′ → fQ (AQx , iQx) aQx ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ ndbr f ((AP × AQ) , pair iP iQ) (waP , waQ) prf
    → f ((APx × AQx) , pair iPx iQx) (aPx , aQx) ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-offndbr-both eqP eqQ bP bQ feq rewrite eqP | eqQ with feq
  ... | refl rewrite bP | bQ = refl

-- (5) both ndbr: synchronous pair merge (resolves BOTH choices in one τ-step).
αpar-ndbr-both :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    {fP AP iP waP wpP} {fQ AQ iQ waQ wpQ}
    {APx iPx aPx AQx iQx aQx}
  → P .force ≡ ndbr fP (AP , iP) waP wpP
  → Q .force ≡ ndbr fQ (AQ , iQ) waQ wpQ
  → fP (APx , iPx) aPx ≡ just P′ → fQ (AQx , iQx) aQx ≡ just Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-ndbr-both eqP eqQ bP bQ with αpar-fndbr-both eqP eqQ
... | f , prf , feq = sNdbr feq (αpar-offndbr-both eqP eqQ bP bQ feq)

-------------------------------------------------------------------------------------
-- STAGE 1b: mix single-τ-step building blocks (introduction direction)
-------------------------------------------------------------------------------------

private
  -- ===== P-mix slides alone (Q ∈ {ret,vis}) =====
  -- force helpers: composite.force ≡ mix f (P′⟦…⟧Q), f existential.
  αpar-fmixL-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP} {s}
    → P .force ≡ mix fP P′ → Q .force ≡ ret s
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q))
  αpar-fmixL-ret eqP eqQ rewrite eqP | eqQ = _ , refl

  αpar-fmixL-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP} {fQ}
    → P .force ≡ mix fP P′ → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q))
  αpar-fmixL-vis eqP eqQ rewrite eqP | eqQ = _ , refl

-- (6) P-mix slides alone, when Q is ret / vis (NOT sil, NOT ndbr, NOT mix).
αpar-mix-slide-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP}
  → P .force ≡ mix fP P′
  → (∀ {t} → Q .force ≢ sil t)
  → (∀ {f wi wa wp} → Q .force ≢ ndbr f wi wa wp)
  → (∀ {g Qt} → Q .force ≢ mix g Qt)
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
αpar-mix-slide-L {Q = Q} eqP ¬sQ ¬nQ ¬mQ with Q .force in eqQ
... | ret _ with αpar-fmixL-ret eqP eqQ
...   | f , feq = sMixSlide feq
αpar-mix-slide-L {Q = Q} eqP ¬sQ ¬nQ ¬mQ | vis _ with αpar-fmixL-vis eqP eqQ
...   | f , feq = sMixSlide feq
αpar-mix-slide-L {Q = Q} eqP ¬sQ ¬nQ ¬mQ | sil _        = ⊥-elim (¬sQ refl)
αpar-mix-slide-L {Q = Q} eqP ¬sQ ¬nQ ¬mQ | ndbr _ _ _ _ = ⊥-elim (¬nQ refl)
αpar-mix-slide-L {Q = Q} eqP ¬sQ ¬nQ ¬mQ | mix _ _      = ⊥-elim (¬mQ refl)

private
  -- ===== Q-mix slides alone (P ∈ {ret,vis}, P not sil/ndbr/mix) =====
  αpar-fmixR-ret :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S} {fQ} {r}
    → P .force ≡ ret r → Q .force ≡ mix fQ Q′
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′))
  αpar-fmixR-ret eqP eqQ rewrite eqP | eqQ = _ , refl

  αpar-fmixR-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S} {fQ} {fP}
    → P .force ≡ vis fP → Q .force ≡ mix fQ Q′
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′))
  αpar-fmixR-vis eqP eqQ rewrite eqP | eqQ = _ , refl

-- (7) Q-mix slides alone, when P is ret / vis (NOT sil, NOT ndbr, NOT mix).
αpar-mix-slide-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S} {fQ}
  → Q .force ≡ mix fQ Q′
  → (∀ {t} → P .force ≢ sil t)
  → (∀ {f wi wa wp} → P .force ≢ ndbr f wi wa wp)
  → (∀ {g Pt} → P .force ≢ mix g Pt)
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-mix-slide-R {P = P} eqQ ¬sP ¬nP ¬mP with P .force in eqP
... | ret _ with αpar-fmixR-ret eqP eqQ
...   | f , feq = sMixSlide feq
αpar-mix-slide-R {P = P} eqQ ¬sP ¬nP ¬mP | vis _ with αpar-fmixR-vis eqP eqQ
...   | f , feq = sMixSlide feq
αpar-mix-slide-R {P = P} eqQ ¬sP ¬nP ¬mP | sil _        = ⊥-elim (¬sP refl)
αpar-mix-slide-R {P = P} eqQ ¬sP ¬nP ¬mP | ndbr _ _ _ _ = ⊥-elim (¬nP refl)
αpar-mix-slide-R {P = P} eqQ ¬sP ¬nP ¬mP | mix _ _      = ⊥-elim (¬mP refl)

private
  -- ===== both mix: slide both jointly =====
  αpar-fmix-both :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S} {fP} {fQ}
    → P .force ≡ mix fP P′ → Q .force ≡ mix fQ Q′
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′))
  αpar-fmix-both eqP eqQ rewrite eqP | eqQ = _ , refl

-- (8) both mix: slide both jointly (one τ-step).
αpar-mix-both :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S} {fP} {fQ}
  → P .force ≡ mix fP P′ → Q .force ≡ mix fQ Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ─[ τ ]─► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-mix-both eqP eqQ with αpar-fmix-both eqP eqQ
... | f , feq = sMixSlide feq

-------------------------------------------------------------------------------------
-- STAGE 2: τ-flush — drive both operands through their leading τ's, in lock-step
-- respecting the operator's priority, to a pair of stable (vis-headed) residuals.
-------------------------------------------------------------------------------------

private
  -- A vis-headed tree admits no τ-step.
  no-τ-from-vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t t′ : ITree E (ExtI I) R} {f}
    → t .force ≡ vis f → t ─[ τ ]─► t′ → ⊥
  no-τ-from-vis eq (sSil s)      = case trans (sym eq) s of λ ()
  no-τ-from-vis eq (sNdbr s _)   = case trans (sym eq) s of λ ()
  no-τ-from-vis eq (sMixSlide s) = case trans (sym eq) s of λ ()

  -- A stable (vis-headed source) tree is end-of-bigstep: empty bigstep is bNil.
  stable-bigNil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t t′ : ITree E (ExtI I) R} {f}
    → t .force ≡ vis f → t ═⟨ [] ⟩═► t′ → t′ ≡ t
  stable-bigNil eq bNil = refl
  stable-bigNil eq (bTau τ-step rest) = ⊥-elim (no-τ-from-vis eq τ-step)

  -- isStable + non-vis head is absurd.
  stable-not-sil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t u : ITree E (ExtI I) R}
    → isStable t → t .force ≡ sil u → ⊥
  stable-not-sil {t = t} st eq with t .force
  ... | vis _ = case eq of λ ()

  stable-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {r}
    → isStable t → t .force ≡ ret r → ⊥
  stable-ret {t = t} st eq with t .force
  ... | vis _ = case eq of λ ()

  stable-ndbr :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f wi wa wp}
    → isStable t → t .force ≡ ndbr f wi wa wp → ⊥
  stable-ndbr {t = t} st eq with t .force
  ... | vis _ = case eq of λ ()

  stable-mix :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f Qt}
    → isStable t → t .force ≡ mix f Qt → ⊥
  stable-mix {t = t} st eq with t .force
  ... | vis _ = case eq of λ ()

  -- From a known head shape, refute the other head shapes.  These let the mix/ndbr
  -- step lemmas' "Q is not sil / not ndbr / not mix" hypotheses be discharged even
  -- when `Q .force` is abstracted by an outer `with … in` and only `q-eq` is known.
  ¬sil-of-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {r} → t .force ≡ ret r → ∀ {u} → t .force ≢ sil u
  ¬sil-of-ret eq e = case trans (sym eq) e of λ ()
  ¬sil-of-vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f} → t .force ≡ vis f → ∀ {u} → t .force ≢ sil u
  ¬sil-of-vis eq e = case trans (sym eq) e of λ ()
  ¬sil-of-mix :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {g Qt} → t .force ≡ mix g Qt → ∀ {u} → t .force ≢ sil u
  ¬sil-of-mix eq e = case trans (sym eq) e of λ ()
  ¬sil-of-ndbr :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {g wi wa wp} → t .force ≡ ndbr g wi wa wp
    → ∀ {u} → t .force ≢ sil u
  ¬sil-of-ndbr eq e = case trans (sym eq) e of λ ()
  ¬ndbr-of-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {r} → t .force ≡ ret r
    → ∀ {f wi wa wp} → t .force ≢ ndbr f wi wa wp
  ¬ndbr-of-ret eq e = case trans (sym eq) e of λ ()
  ¬ndbr-of-vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f} → t .force ≡ vis f
    → ∀ {g wi wa wp} → t .force ≢ ndbr g wi wa wp
  ¬ndbr-of-vis eq e = case trans (sym eq) e of λ ()
  ¬ndbr-of-mix :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {g Qt} → t .force ≡ mix g Qt
    → ∀ {h wi wa wp} → t .force ≢ ndbr h wi wa wp
  ¬ndbr-of-mix eq e = case trans (sym eq) e of λ ()
  ¬mix-of-ret :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {r} → t .force ≡ ret r → ∀ {g Qt} → t .force ≢ mix g Qt
  ¬mix-of-ret eq e = case trans (sym eq) e of λ ()
  ¬mix-of-vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f} → t .force ≡ vis f → ∀ {g Qt} → t .force ≢ mix g Qt
  ¬mix-of-vis eq e = case trans (sym eq) e of λ ()

-- The τ-flush proper.  Recursion is structural on the operand bigsteps: every
-- recursive call shrinks restP and/or restQ (sub-derivations of the input bTau's).
αpar-τ-flush : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
  → P ═⟨ [] ⟩═► P′ → Q ═⟨ [] ⟩═► Q′ → isStable P′ → isStable Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ═⟨ [] ⟩═► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ with P .force in p-eq | Q .force in q-eq

-- ===== P sil-headed: consume P's τ head (operator clause 1) =====
-- We drive the operator with the step's OWN force-eq `e` (not p-eq), so the residual
-- `restP` of the matched bTau is exactly the recursion argument — no subst, hence
-- structurally smaller and termination is accepted.
... | sil P0 | _ with bP
...   | bNil = ⊥-elim (stable-not-sil {t = P} stP p-eq)
...   | bTau (sSil e) restP =
        bTau (αpar-sil-L e) (αpar-τ-flush restP bQ stP stQ)
...   | bTau (sNdbr e _) _   = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()

-- ===== P non-sil, Q sil-headed: consume Q's τ head (operator clause 2) =====
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret _ | sil Q0 with bQ
...   | bNil = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | bTau (sSil e) restQ =
        bTau (αpar-sil-R (¬sil-of-ret {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | bTau (sNdbr e _) _   = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | vis _ | sil Q0 with bQ
...   | bNil = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | bTau (sSil e) restQ =
        bTau (αpar-sil-R (¬sil-of-vis {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | bTau (sNdbr e _) _   = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ndbr _ _ _ _ | sil Q0 with bQ
...   | bNil = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | bTau (sSil e) restQ =
        bTau (αpar-sil-R (¬sil-of-ndbr {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | bTau (sNdbr e _) _   = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | mix _ _ | sil Q0 with bQ
...   | bNil = ⊥-elim (stable-not-sil {t = Q} stQ q-eq)
...   | bTau (sSil e) restQ =
        bTau (αpar-sil-R (¬sil-of-mix {t = P} p-eq) e) (αpar-τ-flush bP restQ stP stQ)
...   | bTau (sNdbr e _) _   = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()

-- ===== both non-sil =====

-- both vis: both bigsteps are bNil (vis has no τ); residuals are P,Q themselves.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | vis _ | vis _ =
      subst (λ z → _ ═⟨ [] ⟩═► (z ⟦ _ ¿ _ ∥ _ ¿ _ ⟧ _))
            (sym (stable-bigNil p-eq bP))
            (subst (λ z → _ ═⟨ [] ⟩═► (_ ⟦ _ ¿ _ ∥ _ ¿ _ ⟧ z))
                   (sym (stable-bigNil q-eq bQ)) bNil)

-- both ndbr: joint τ-step (operator's synchronous ndbr|ndbr).
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ndbr _ _ _ _ | ndbr _ _ _ _ with bP | bQ
...   | bTau (sNdbr eqfP bp) restP | bTau (sNdbr eqfQ bq) restQ =
        bTau (αpar-ndbr-both eqfP eqfQ bp bq)
             (αpar-τ-flush restP restQ stP stQ)
...   | bNil | _ = ⊥-elim (stable-ndbr {t = P} stP p-eq)
...   | bTau (sSil e) _ | _ = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ | _ = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr _ _) _ | bNil = ⊥-elim (stable-ndbr {t = Q} stQ q-eq)
...   | bTau (sNdbr _ _) _ | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sNdbr _ _) _ | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()

-- P ndbr, Q ret/vis/mix: P distributes alone (operator's ndbr|{ret,vis,mix}).
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ndbr _ _ _ _ | ret _ with bP
...   | bTau (sNdbr eqfP bp) restP =
        bTau (αpar-ndbr-L eqfP bp (¬sil-of-ret {t = Q} q-eq) (¬ndbr-of-ret {t = Q} q-eq))
             (αpar-τ-flush restP bQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = P} stP p-eq)
...   | bTau (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ndbr _ _ _ _ | vis _ with bP
...   | bTau (sNdbr eqfP bp) restP =
        bTau (αpar-ndbr-L eqfP bp (¬sil-of-vis {t = Q} q-eq) (¬ndbr-of-vis {t = Q} q-eq))
             (αpar-τ-flush restP bQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = P} stP p-eq)
...   | bTau (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ndbr _ _ _ _ | mix _ _ with bP
...   | bTau (sNdbr eqfP bp) restP =
        bTau (αpar-ndbr-L eqfP bp (¬sil-of-mix {t = Q} q-eq) (¬ndbr-of-mix {t = Q} q-eq))
             (αpar-τ-flush restP bQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = P} stP p-eq)
...   | bTau (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()

-- Q ndbr, P ret/vis/mix (P non-ndbr): Q distributes alone.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret _ | ndbr _ _ _ _ with bQ
...   | bTau (sNdbr eqfQ bq) restQ =
        bTau (αpar-ndbr-R eqfQ bq (¬sil-of-ret {t = P} p-eq) (¬ndbr-of-ret {t = P} p-eq))
             (αpar-τ-flush bP restQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = Q} stQ q-eq)
...   | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | vis _ | ndbr _ _ _ _ with bQ
...   | bTau (sNdbr eqfQ bq) restQ =
        bTau (αpar-ndbr-R eqfQ bq (¬sil-of-vis {t = P} p-eq) (¬ndbr-of-vis {t = P} p-eq))
             (αpar-τ-flush bP restQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = Q} stQ q-eq)
...   | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | mix _ _ | ndbr _ _ _ _ with bQ
...   | bTau (sNdbr eqfQ bq) restQ =
        bTau (αpar-ndbr-R eqfQ bq (¬sil-of-mix {t = P} p-eq) (¬ndbr-of-mix {t = P} p-eq))
             (αpar-τ-flush bP restQ stP stQ)
...   | bNil = ⊥-elim (stable-ndbr {t = Q} stQ q-eq)
...   | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()

-- both mix: joint slide.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | mix _ _ | mix _ _ with bP | bQ
...   | bTau (sMixSlide eqP) restP | bTau (sMixSlide eqQ) restQ =
        bTau (αpar-mix-both eqP eqQ)
             (αpar-τ-flush restP restQ stP stQ)
...   | bNil | _ = ⊥-elim (stable-mix {t = P} stP p-eq)
...   | bTau (sSil e) _ | _ = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr e _) _ | _ = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide _) _ | bNil = ⊥-elim (stable-mix {t = Q} stQ q-eq)
...   | bTau (sMixSlide _) _ | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide _) _ | bTau (sNdbr e _) _ = case trans (sym q-eq) e of λ ()

-- P mix, Q ret/vis: P slides alone.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | mix _ _ | ret _ with bP
...   | bTau (sMixSlide eqP) restP =
        bTau (αpar-mix-slide-L eqP (¬sil-of-ret {t = Q} q-eq) (¬ndbr-of-ret {t = Q} q-eq) (¬mix-of-ret {t = Q} q-eq))
             (αpar-τ-flush restP bQ stP stQ)
...   | bNil = ⊥-elim (stable-mix {t = P} stP p-eq)
...   | bTau (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr e _) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | mix _ _ | vis _ with bP
...   | bTau (sMixSlide eqP) restP =
        bTau (αpar-mix-slide-L eqP (¬sil-of-vis {t = Q} q-eq) (¬ndbr-of-vis {t = Q} q-eq) (¬mix-of-vis {t = Q} q-eq))
             (αpar-τ-flush restP bQ stP stQ)
...   | bNil = ⊥-elim (stable-mix {t = P} stP p-eq)
...   | bTau (sSil e) _ = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr e _) _ = case trans (sym p-eq) e of λ ()

-- Q mix, P ret/vis: Q slides alone.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret _ | mix _ _ with bQ
...   | bTau (sMixSlide eqQ) restQ =
        bTau (αpar-mix-slide-R eqQ (¬sil-of-ret {t = P} p-eq) (¬ndbr-of-ret {t = P} p-eq) (¬mix-of-ret {t = P} p-eq))
             (αpar-τ-flush bP restQ stP stQ)
...   | bNil = ⊥-elim (stable-mix {t = Q} stQ q-eq)
...   | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sNdbr e _) _ = case trans (sym q-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | vis _ | mix _ _ with bQ
...   | bTau (sMixSlide eqQ) restQ =
        bTau (αpar-mix-slide-R eqQ (¬sil-of-vis {t = P} p-eq) (¬ndbr-of-vis {t = P} p-eq) (¬mix-of-vis {t = P} p-eq))
             (αpar-τ-flush bP restQ stP stQ)
...   | bNil = ⊥-elim (stable-mix {t = Q} stQ q-eq)
...   | bTau (sSil e) _ = case trans (sym q-eq) e of λ ()
...   | bTau (sNdbr e _) _ = case trans (sym q-eq) e of λ ()

-- remaining both-non-sil combinations where neither side moves nor needs to:
-- ret|ret, ret|vis, vis|ret.  These have NO τ (both bigsteps bNil), but the
-- residual must be stable (vis).  ret-headed stable is impossible.
-- A ret-headed operand has no τ, so its empty bigstep is bNil ⇒ residual = itself,
-- which is ret-headed, contradicting stability of the residual.
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret _ | ret _ with bP
...   | bNil = ⊥-elim (stable-ret {t = P} stP p-eq)
...   | bTau (sSil e) _      = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr e _) _   = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | ret _ | vis _ with bP
...   | bNil = ⊥-elim (stable-ret {t = P} stP p-eq)
...   | bTau (sSil e) _      = case trans (sym p-eq) e of λ ()
...   | bTau (sNdbr e _) _   = case trans (sym p-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym p-eq) e of λ ()
αpar-τ-flush {P = P} {Q = Q} bP bQ stP stQ | vis _ | ret _ with bQ
...   | bNil = ⊥-elim (stable-ret {t = Q} stQ q-eq)
...   | bTau (sSil e) _      = case trans (sym q-eq) e of λ ()
...   | bTau (sNdbr e _) _   = case trans (sym q-eq) e of λ ()
...   | bTau (sMixSlide e) _ = case trans (sym q-eq) e of λ ()

-------------------------------------------------------------------------------------
-- STAGE 3: general introduction law.
-------------------------------------------------------------------------------------

private
  -- A component bigstep with a leading visible event splits into: leading τ's to a
  -- stable-or-mix head X₁, the visible step, and the tail.
  split-head :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {X X″ : ITree E (ExtI I) R} {e rest}
    → X ═⟨ evl e ∷ rest ⟩═► X″
    → Σ[ X₁ ∈ ITree E (ExtI I) R ] Σ[ X₂ ∈ ITree E (ExtI I) R ]
        (X ═⟨ [] ⟩═► X₁
         × ((Σ[ f ∈ _ ] X₁ .force ≡ vis f)
            ⊎ (Σ[ f ∈ _ ] Σ[ Qt ∈ ITree E (ExtI I) R ] X₁ .force ≡ mix f Qt))
         × (X₁ ─[ ev (evl e) ]─► X₂)
         × (X₂ ═⟨ rest ⟩═► X″))
  split-head (bStep {t = X} step tail) with ev-ndbr step
  ... | inj₁ (f , (fe , _))      = _ , _ , bNil , inj₁ (f , fe) , step , tail
  ... | inj₂ (f , Qt , (fe , _)) = _ , _ , bNil , inj₂ (f , Qt , fe) , step , tail
  split-head (bTau τ-step rest) with split-head rest
  ... | X₁ , X₂ , flush , headshape , vstep , tail =
        X₁ , X₂ , bTau τ-step flush , headshape , vstep , tail

-------------------------------------------------------------------------------------
-- Generalised composite visible-step lemmas, allowing each operand to be either
-- `vis`-headed (fires via sVis) or `mix`-headed (fires via sMixVis).  These extend
-- αpar-sync-step / αpar-soloL-step / αpar-soloR-step to mix-headed operands.

private
  -- A head is "ready" (vis or mix) and offers `just t′` at the event.
  ReadyAt : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            → ITree E (ExtI I) R → (at : AnyTypes E) → proj₁ at
            → ITree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  ReadyAt {I = I} {R = R} P at a P′ =
      (Σ[ f ∈ _ ] (P .force ≡ vis f × f at a ≡ just P′))
    ⊎ (Σ[ f ∈ _ ] Σ[ Qt ∈ ITree E (ExtI I) R ] (P .force ≡ mix f Qt × f at a ≡ just P′))



  -- A head is "ready" (vis or mix) without a specific offer — used for the
  -- stationary operand of a solo step (only its head-shape matters).
  Headed : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → ITree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  Headed {I = I} {R = R} Q =
      (Σ[ f ∈ _ ] Q .force ≡ vis f)
    ⊎ (Σ[ f ∈ _ ] Σ[ Qt ∈ ITree E (ExtI I) R ] Q .force ≡ mix f Qt)

  -- Force-reduction helpers for the sync step (one per head-shape combo).
  fsync-vv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP fQ}
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f)
  fsync-vv eqP eqQ rewrite eqP | eqQ = _ , refl

  fsync-vm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP fQ Qt}
    → P .force ≡ vis fP → Q .force ≡ mix fQ Qt
    → Σ[ f ∈ _ ] Σ[ Rt ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt)
  fsync-vm eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  fsync-mv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP Pt fQ}
    → P .force ≡ mix fP Pt → Q .force ≡ vis fQ
    → Σ[ f ∈ _ ] Σ[ Rt ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt)
  fsync-mv eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  fsync-mm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S} {fP Pt fQ Qt}
    → P .force ≡ mix fP Pt → Q .force ≡ mix fQ Qt
    → Σ[ f ∈ _ ] Σ[ Rt ∈ _ ] ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt)
  fsync-mm eqP eqQ rewrite eqP | eqQ = _ , _ , refl

  -- Offer helpers for the sync step.  After rewriting both operand force eqs, the
  -- composite's merged offer at (at,a) under (yes,yes) routing is just(P′⟦…⟧Q′).
  osync-vv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP fQ} {at a} {f}
    → A at → B at → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osync-vv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA mB eqP bP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | yes _ rewrite bP | bQ = refl
  osync-vv mA mB eqP bP eqQ bQ fe | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  osync-vv mA mB eqP bP eqQ bQ fe | refl | no ¬A | _     = ⊥-elim (¬A mA)

  osync-vm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP fQ Qt} {at a} {f Rt}
    → A at → B at → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ mix fQ Qt → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osync-vm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA mB eqP bP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | yes _ rewrite bP | bQ = refl
  osync-vm mA mB eqP bP eqQ bQ fe | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  osync-vm mA mB eqP bP eqQ bQ fe | refl | no ¬A | _     = ⊥-elim (¬A mA)

  osync-mv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP Pt fQ} {at a} {f Rt}
    → A at → B at → P .force ≡ mix fP Pt → fP at a ≡ just P′
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osync-mv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA mB eqP bP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | yes _ rewrite bP | bQ = refl
  osync-mv mA mB eqP bP eqQ bQ fe | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  osync-mv mA mB eqP bP eqQ bQ fe | refl | no ¬A | _     = ⊥-elim (¬A mA)

  osync-mm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP Pt fQ Qt} {at a} {f Rt}
    → A at → B at → P .force ≡ mix fP Pt → fP at a ≡ just P′
    → Q .force ≡ mix fQ Qt → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osync-mm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA mB eqP bP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | yes _ rewrite bP | bQ = refl
  osync-mm mA mB eqP bP eqQ bQ fe | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  osync-mm mA mB eqP bP eqQ bQ fe | refl | no ¬A | _     = ⊥-elim (¬A mA)

  -- Generalised synchronisation step assembled from the helpers.
  αpar-sync-step' :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {at : AnyTypes E} {a : proj₁ at}
    → A at → B at
    → ReadyAt P at a P′ → ReadyAt Q at a Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
      (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-sync-step' mA mB (inj₁ (fP , eqP , bP)) (inj₁ (fQ , eqQ , bQ))
    with fsync-vv eqP eqQ
  ... | f , fe = sVis fe (osync-vv mA mB eqP bP eqQ bQ fe)
  αpar-sync-step' mA mB (inj₁ (fP , eqP , bP)) (inj₂ (fQ , Qt , eqQ , bQ))
    with fsync-vm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osync-vm mA mB eqP bP eqQ bQ fe)
  αpar-sync-step' mA mB (inj₂ (fP , Pt , eqP , bP)) (inj₁ (fQ , eqQ , bQ))
    with fsync-mv eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osync-mv mA mB eqP bP eqQ bQ fe)
  αpar-sync-step' mA mB (inj₂ (fP , Pt , eqP , bP)) (inj₂ (fQ , Qt , eqQ , bQ))
    with fsync-mm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osync-mm mA mB eqP bP eqQ bQ fe)

  ---------------------------------------------------------------------------------
  -- Solo-L offer helpers (moving = P, stationary = Q; event in A only).
  -- The operator's (yes,no) branch consults only fP, yielding just (P′⟦…⟧Q).
  osoloL-vv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP fQ} {at a} {f}
    → A at → ¬ (B at) → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  osoloL-vv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA ¬mB eqP bP eqQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | no _ rewrite bP = refl
  osoloL-vv mA ¬mB eqP bP eqQ fe | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  osoloL-vv mA ¬mB eqP bP eqQ fe | refl | no ¬A | _      = ⊥-elim (¬A mA)

  osoloL-vm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP fQ Qt} {at a} {f Rt}
    → A at → ¬ (B at) → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ mix fQ Qt
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  osoloL-vm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA ¬mB eqP bP eqQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | no _ rewrite bP = refl
  osoloL-vm mA ¬mB eqP bP eqQ fe | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  osoloL-vm mA ¬mB eqP bP eqQ fe | refl | no ¬A | _      = ⊥-elim (¬A mA)

  osoloL-mv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP Pt fQ} {at a} {f Rt}
    → A at → ¬ (B at) → P .force ≡ mix fP Pt → fP at a ≡ just P′
    → Q .force ≡ vis fQ
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  osoloL-mv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA ¬mB eqP bP eqQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | no _ rewrite bP = refl
  osoloL-mv mA ¬mB eqP bP eqQ fe | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  osoloL-mv mA ¬mB eqP bP eqQ fe | refl | no ¬A | _      = ⊥-elim (¬A mA)

  osoloL-mm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP Pt fQ Qt} {at a} {f Rt}
    → A at → ¬ (B at) → P .force ≡ mix fP Pt → fP at a ≡ just P′
    → Q .force ≡ mix fQ Qt
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  osoloL-mm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} mA ¬mB eqP bP eqQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | yes _ | no _ rewrite bP = refl
  osoloL-mm mA ¬mB eqP bP eqQ fe | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  osoloL-mm mA ¬mB eqP bP eqQ fe | refl | no ¬A | _      = ⊥-elim (¬A mA)

  ---------------------------------------------------------------------------------
  -- Solo-R offer helpers (moving = Q, stationary = P; event in B only).
  -- The operator's (no,yes) branch consults only fQ, yielding just (P⟦…⟧Q′).
  osoloR-vv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP fQ} {at a} {f}
    → ¬ (A at) → B at → P .force ≡ vis fP
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osoloR-vv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} ¬mA mB eqP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | no _ | yes _ rewrite bQ = refl
  osoloR-vv ¬mA mB eqP eqQ bQ fe | refl | yes mA | _     = ⊥-elim (¬mA mA)
  osoloR-vv ¬mA mB eqP eqQ bQ fe | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  osoloR-vm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP fQ Qt} {at a} {f Rt}
    → ¬ (A at) → B at → P .force ≡ vis fP
    → Q .force ≡ mix fQ Qt → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osoloR-vm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} ¬mA mB eqP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | no _ | yes _ rewrite bQ = refl
  osoloR-vm ¬mA mB eqP eqQ bQ fe | refl | yes mA | _     = ⊥-elim (¬mA mA)
  osoloR-vm ¬mA mB eqP eqQ bQ fe | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  osoloR-mv :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP Pt fQ} {at a} {f Rt}
    → ¬ (A at) → B at → P .force ≡ mix fP Pt
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osoloR-mv {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} ¬mA mB eqP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | no _ | yes _ rewrite bQ = refl
  osoloR-mv ¬mA mB eqP eqQ bQ fe | refl | yes mA | _     = ⊥-elim (¬mA mA)
  osoloR-mv ¬mA mB eqP eqQ bQ fe | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  osoloR-mm :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP Pt fQ Qt} {at a} {f Rt}
    → ¬ (A at) → B at → P .force ≡ mix fP Pt
    → Q .force ≡ mix fQ Qt → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ mix f Rt
    → f at a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  osoloR-mm {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a} ¬mA mB eqP eqQ bQ fe
    rewrite eqP | eqQ with fe
  ... | refl with da at | db at
  ...   | no _ | yes _ rewrite bQ = refl
  osoloR-mm ¬mA mB eqP eqQ bQ fe | refl | yes mA | _     = ⊥-elim (¬mA mA)
  osoloR-mm ¬mA mB eqP eqQ bQ fe | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  ---------------------------------------------------------------------------------
  -- Generalised solo step lemmas.
  αpar-soloL-step' :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {at : AnyTypes E} {a : proj₁ at}
    → A at → ¬ (B at)
    → ReadyAt P at a P′ → Headed Q
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
      (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-soloL-step' mA ¬mB (inj₁ (fP , eqP , bP)) (inj₁ (fQ , eqQ))
    with fsync-vv eqP eqQ
  ... | f , fe = sVis fe (osoloL-vv mA ¬mB eqP bP eqQ fe)
  αpar-soloL-step' mA ¬mB (inj₁ (fP , eqP , bP)) (inj₂ (fQ , Qt , eqQ))
    with fsync-vm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloL-vm mA ¬mB eqP bP eqQ fe)
  αpar-soloL-step' mA ¬mB (inj₂ (fP , Pt , eqP , bP)) (inj₁ (fQ , eqQ))
    with fsync-mv eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloL-mv mA ¬mB eqP bP eqQ fe)
  αpar-soloL-step' mA ¬mB (inj₂ (fP , Pt , eqP , bP)) (inj₂ (fQ , Qt , eqQ))
    with fsync-mm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloL-mm mA ¬mB eqP bP eqQ fe)

  αpar-soloR-step' :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {at : AnyTypes E} {a : proj₁ at}
    → ¬ (A at) → B at
    → Headed P → ReadyAt Q at a Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
      (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-soloR-step' ¬mA mB (inj₁ (fP , eqP)) (inj₁ (fQ , eqQ , bQ))
    with fsync-vv eqP eqQ
  ... | f , fe = sVis fe (osoloR-vv ¬mA mB eqP eqQ bQ fe)
  αpar-soloR-step' ¬mA mB (inj₁ (fP , eqP)) (inj₂ (fQ , Qt , eqQ , bQ))
    with fsync-vm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloR-vm ¬mA mB eqP eqQ bQ fe)
  αpar-soloR-step' ¬mA mB (inj₂ (fP , Pt , eqP)) (inj₁ (fQ , eqQ , bQ))
    with fsync-mv eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloR-mv ¬mA mB eqP eqQ bQ fe)
  αpar-soloR-step' ¬mA mB (inj₂ (fP , Pt , eqP)) (inj₂ (fQ , Qt , eqQ , bQ))
    with fsync-mm eqP eqQ
  ... | f , Rt , fe = sMixVis fe (osoloR-mm ¬mA mB eqP eqQ bQ fe)

-------------------------------------------------------------------------------------
-- STAGE 4: restricted introduction law (vis-headed visible events).
--
-- `VisDriven bs` asserts that every VISIBLE step in the bigstep `bs` is a `sVis`
-- (fired from a `vis` head).  τ-steps — including `sMixSlide` (mix-slides) — are
-- unconstrained.  This is exactly the restriction under which the binary
-- alphabetised parallel admits an introduction law: synchronisation events must be
-- offered from genuine `vis` heads, not from sliding `mix` heads.
-------------------------------------------------------------------------------------

data VisDriven {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  : {X X′ : ITree E (ExtI I) R} {s : List (Event√ E R)} → X ═⟨ s ⟩═► X′
  → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  vd-nil  : ∀ {X} → VisDriven (bNil {t = X})
  vd-tau  : ∀ {X X′ X″ s} {τstep : X ─[ τ ]─► X′} {rest : X′ ═⟨ s ⟩═► X″}
          → VisDriven rest → VisDriven (bTau τstep rest)
  vd-vis  : ∀ {X X′ X″ at a fX s} {rest : X′ ═⟨ s ⟩═► X″}
          → (fe : X .force ≡ vis fX) → (je : fX at a ≡ just X′)
          → VisDriven rest
          → VisDriven (bStep (sVis {p = X} {f = fX} {at = at} {a = a} {t′ = X′} fe je) rest)

private
  -- A stable tree is `vis`-headed; extract the offer function.
  isStable⇒vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R}
    → isStable t
    → Σ[ f ∈ _ ] t .force ≡ vis f
  isStable⇒vis {I = I} {R = R} {t = t} st = helper (t .force) refl st
    where
      helper : ∀ (n : NodeKind E (ExtI I) R) → t .force ≡ n
             → (isStable t)
             → Σ[ f ∈ _ ] t .force ≡ vis f
      helper (vis f) eq _ = f , eq
      helper (ret _) eq st = ⊥-elim (stable-ret {t = t} st eq)
      helper (sil _) eq st = ⊥-elim (stable-not-sil {t = t} st eq)
      helper (ndbr _ _ _ _) eq st = ⊥-elim (stable-ndbr {t = t} st eq)
      helper (mix _ _) eq st = ⊥-elim (stable-mix {t = t} st eq)

  -- A vis-headed tree is stable.
  vis⇒isStable :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {t : ITree E (ExtI I) R} {f}
    → t .force ≡ vis f → isStable t
  vis⇒isStable {t = t} eq with t .force
  ... | vis _ = tt₀

  -- Concatenate a τ-only front with an arbitrary bigstep.
  bigstep-++ :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {X Y Z : ITree E (ExtI I) R} {s : List (Event√ E R)}
    → X ═⟨ [] ⟩═► Y → Y ═⟨ s ⟩═► Z → X ═⟨ s ⟩═► Z
  bigstep-++ bNil               bs = bs
  bigstep-++ (bTau τstep front) bs = bTau τstep (bigstep-++ front bs)

-- Front split landing at a vis head: a vis-driven bigstep whose endpoint is stable
-- decomposes into leading τ's to a vis-headed X₁ followed by the same trace from X₁.
lead-split-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {X X′ : ITree E (ExtI I) R} {s : List (Event√ E R)} (bs : X ═⟨ s ⟩═► X′)
  → VisDriven bs → isStable X′
  → Σ[ X₁ ∈ ITree E (ExtI I) R ] Σ[ fX₁ ∈ _ ]
      (X ═⟨ [] ⟩═► X₁ × X₁ .force ≡ vis fX₁ × Σ[ bs₁ ∈ (X₁ ═⟨ s ⟩═► X′) ] VisDriven bs₁)
lead-split-vis {X = X} {X′ = X′} bNil vd-nil stX′ with isStable⇒vis {t = X′} stX′
... | f , eq = X′ , f , bNil {t = X′} , eq , bNil {t = X′} , vd-nil {X = X′}
lead-split-vis (bTau τstep rest) (vd-tau vd) stX′ with lead-split-vis rest vd stX′
... | X₁ , fX₁ , flush , eq , bs₁ , vd₁ =
      X₁ , fX₁ , bTau τstep flush , eq , bs₁ , vd₁
lead-split-vis (bStep (sVis fe je) rest) (vd-vis _ _ vd) _ =
  _ , _ , bNil , fe , bStep (sVis fe je) rest , vd-vis fe je vd

-------------------------------------------------------------------------------------
-- The restricted introduction law.
--
-- Given a synchronisation split `AlphaSync A B sP sQ s` and vis-driven component
-- bigsteps for P and Q ending at stable (vis-headed) residuals, the binary
-- alphabetised parallel performs the merged trace `map evl s`, ending at the
-- composite of the residuals.
-------------------------------------------------------------------------------------

αpar-trace-intro : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    {sP sQ s : List (Event E)}
  → AlphaSync A B sP sQ s
  → (bP : P ═⟨ map evl sP ⟩═► P′) → VisDriven bP
  → (bQ : Q ═⟨ map evl sQ ⟩═► Q′) → VisDriven bQ
  → isStable P′ → isStable Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) ═⟨ map evl s ⟩═► (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)

-- empty: both operands just τ-flush to their stable endpoints.
αpar-trace-intro sync-nil bP _ bQ _ stP stQ = αpar-τ-flush bP bQ stP stQ

-- synchronisation: P and Q both fire `e`.
αpar-trace-intro {da = da} {db = db} (sync-both {e = e} pA pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , fP₁ , flushP , eqP₁ , bP₁ , vdP₁
    | Q₁ , fQ₁ , flushQ , eqQ₁ , bQ₁ , vdQ₁
  with vdP₁
...   | vd-tau {τstep = τstep} _ = ⊥-elim (no-τ-from-vis eqP₁ τstep)
...   | vd-vis {at = atP} {a = aP} {fX = fXP} {rest = bP₂} feP jeP vdP₂
        with vdQ₁
...       | vd-tau {τstep = τstep} _ = ⊥-elim (no-τ-from-vis eqQ₁ τstep)
...       | vd-vis {at = atQ} {a = aQ} {fX = fXQ} {rest = bQ₂} feQ jeQ vdQ₂ =
            bigstep-++
              (αpar-τ-flush flushP flushQ (vis⇒isStable {t = P₁} eqP₁) (vis⇒isStable {t = Q₁} eqQ₁))
              (bStep
                (αpar-sync-step' {da = da} {db = db} {P = P₁} {Q = Q₁}
                  {at = atP} {a = aP} pA pB
                  (inj₁ (fXP , feP , jeP)) (inj₁ (fXQ , feQ , jeQ)))
                (αpar-trace-intro rest bP₂ vdP₂ bQ₂ vdQ₂ stP stQ))

-- solo-L: P fires `e` (in A only), Q stationary.
αpar-trace-intro {da = da} {db = db} (sync-l {e = e} pA ¬pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , fP₁ , flushP , eqP₁ , bP₁ , vdP₁
    | Q₁ , fQ₁ , flushQ , eqQ₁ , bQ₁ , vdQ₁
  with vdP₁
...   | vd-tau {τstep = τstep} _ = ⊥-elim (no-τ-from-vis eqP₁ τstep)
...   | vd-vis {at = atP} {a = aP} {fX = fXP} {rest = bP₂} feP jeP vdP₂ =
          bigstep-++
            (αpar-τ-flush flushP flushQ (vis⇒isStable {t = P₁} eqP₁) (vis⇒isStable {t = Q₁} eqQ₁))
            (bStep
              (αpar-soloL-step' {da = da} {db = db} pA ¬pB
                (inj₁ (fXP , feP , jeP)) (inj₁ (fQ₁ , eqQ₁)))
              (αpar-trace-intro rest bP₂ vdP₂ bQ₁ vdQ₁ stP stQ))

-- solo-R: Q fires `e` (in B only), P stationary.
αpar-trace-intro {da = da} {db = db} (sync-r {e = e} ¬pA pB rest)
                 bP vdP bQ vdQ stP stQ
  with lead-split-vis bP vdP stP | lead-split-vis bQ vdQ stQ
... | P₁ , fP₁ , flushP , eqP₁ , bP₁ , vdP₁
    | Q₁ , fQ₁ , flushQ , eqQ₁ , bQ₁ , vdQ₁
  with vdQ₁
...   | vd-tau {τstep = τstep} _ = ⊥-elim (no-τ-from-vis eqQ₁ τstep)
...   | vd-vis {at = atQ} {a = aQ} {fX = fXQ} {rest = bQ₂} feQ jeQ vdQ₂ =
          bigstep-++
            (αpar-τ-flush flushP flushQ (vis⇒isStable {t = P₁} eqP₁) (vis⇒isStable {t = Q₁} eqQ₁))
            (bStep
              (αpar-soloR-step' {da = da} {db = db} ¬pA pB
                (inj₁ (fP₁ , eqP₁)) (inj₁ (fXQ , feQ , jeQ)))
              (αpar-trace-intro rest bP₁ vdP₁ bQ₂ vdQ₂ stP stQ))

-------------------------------------------------------------------------------------
-- Sanity: the deadlock-composition path end-to-end.  A composite of two `Stop`s,
-- under ANY alphabets, is `IsStuck` (every event is blocked since `Stop` offers
-- nothing), hence `HasDeadlock`.  This is exactly what the dining-philosophers
-- deadlock proof relies on.

private
  module Sanity where
    open import ITree_Relations.Deadlock using (HasDeadlock; DeadlockFree; hasDeadlock⇒¬deadlockFree)

    stop∥stop-stuck :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      → IsStuck (Stop {E = E} {I = ExtI I} {R = R} ⟦ A ¿ da ∥ B ¿ db ⟧ Stop {E = E} {I = ExtI I} {R = S})
    stop∥stop-stuck {da = da} {db = db} =
      αpar-IsStuck refl refl blocked
      where
        blocked : ∀ at a → Blocked _ _ da db _ _ at a
        blocked at a with da at | db at
        ... | yes _ | yes _ = lift (inj₁ refl)
        ... | yes _ | no  _ = lift refl
        ... | no  _ | yes _ = lift refl
        ... | no  _ | no  _ = tt

    stop∥stop-hasDeadlock :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      → HasDeadlock (Stop {E = E} {I = ExtI I} {R = R} ⟦ A ¿ da ∥ B ¿ db ⟧ Stop {E = E} {I = ExtI I} {R = S})
    stop∥stop-hasDeadlock = [] , _ , bNil , stop∥stop-stuck
