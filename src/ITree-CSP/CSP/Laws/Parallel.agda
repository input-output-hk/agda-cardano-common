{-
  Parallel-composition laws for ITree-CSP: interleave (_⦀_) and synchronised
  parallel (_∥⇘_¿_⇙_).

  Contents:
    1. Trace lemmas
       - Interleave splitting (Interleave, InterleaveSplit, Interleave-trace)
       - Synchronised splitting (Sync, SyncSplit, Parallel-trace)
    2. DRBisim laws
       - ∥-⊓-distrib-L, ∥-⊓-distrib-R
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
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
open import Data.Nat using (ℕ; suc; zero)
import Data.List.Membership.Propositional as Relation
open Relation using (_∈_; _∉_)
open import Relation.Unary using (∅)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no; contradiction)
open import Relation.Binary using (Rel; IsEquivalence)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; inspect)

open import Class.DecEq using (DecEq; _≟_)
open import Prelude

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences using (Divergent; divergent-prefix)
open import ITree_Relations.DRWeakBisim

module CSP.Laws.Parallel
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Label
open Traces
open DRWSimF
open DRWbisim

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

import CSP.Definitions.Parallel {ℓ} {ℓe} {E} as CSPPar
open CSPPar E-≟

open import CSP.Laws.InternalChoice {ℓ} {ℓe} {E} E-≟
  using (⊓-comm; ⊓-idem; ⊓-cong)

-- Reusable equivalence-closure helpers for `≈ = DRWbisim _≡_`.
private
  open module EQ {ℓ' ℓe' ℓi' ℓr'} {E' : Set ℓ' → Set ℓe'}
                 {I' : Set ℓ' → Set ℓi'} {R' : Set ℓr'} =
        DRWbisimEquiv {E = E'} {I = I'} {R = R'} {RetRel = _≡_} ≡-equiv
        using (drwbisim-refl; drwbisim-sym; drwbisim-trans)

-----------------------------------------------------------------------------
-- Trace lemmas
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Interleave  P ⦀ Q
-- traces [P ⦀ Q] = arbitrary interleaving of P's and Q's plain-event traces;
-- the combined process terminates with √(r,q) only when both P and Q reach
-- termination simultaneously.


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

-- Shared reconstruction lemmas for Interleave-trace-aux (cf. the extend-* lemmas for
-- Interleave-reach-aux).  Same idea, but InterleaveSplit has two constructors and its
-- witnesses are `traces` Σ-pairs `(_ , …)`, so the step is prepended inside the pair.
private
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
           {s : List (Event√ E (R × S))} where

    t-extend-P-τ : ∀ {P′} → P ─[ τ ]─► P′ → InterleaveSplit P′ Q s → InterleaveSplit P Q s
    t-extend-P-τ st (in-progress merge (_ , trP) trQ) = in-progress merge (_ , bTau st trP) trQ
    t-extend-P-τ st (done merge (_ , trP) trQ)        = done merge (_ , bTau st trP) trQ

    t-extend-Q-τ : ∀ {Q′} → Q ─[ τ ]─► Q′ → InterleaveSplit P Q′ s → InterleaveSplit P Q s
    t-extend-Q-τ st (in-progress merge trP (_ , trQ)) = in-progress merge trP (_ , bTau st trQ)
    t-extend-Q-τ st (done merge trP (_ , trQ))        = done merge trP (_ , bTau st trQ)

    t-extend-both-τ : ∀ {P′ Q′} → P ─[ τ ]─► P′ → Q ─[ τ ]─► Q′
                    → InterleaveSplit P′ Q′ s → InterleaveSplit P Q s
    t-extend-both-τ stP stQ (in-progress merge (_ , trP) (_ , trQ)) = in-progress merge (_ , bTau stP trP) (_ , bTau stQ trQ)
    t-extend-both-τ stP stQ (done merge (_ , trP) (_ , trQ))        = done merge (_ , bTau stP trP) (_ , bTau stQ trQ)

    t-extend-P-vis : ∀ {P′ ev0} → P ─[ ev (evl ev0) ]─► P′
                   → InterleaveSplit P′ Q s → InterleaveSplit P Q (evl ev0 ∷ s)
    t-extend-P-vis st (in-progress merge (_ , trP) trQ) = in-progress (int-l merge) (_ , bStep st trP) trQ
    t-extend-P-vis st (done merge (_ , trP) trQ)        = done (int-l merge) (_ , bStep st trP) trQ

    t-extend-Q-vis : ∀ {Q′ ev0} → Q ─[ ev (evl ev0) ]─► Q′
                   → InterleaveSplit P Q′ s → InterleaveSplit P Q (evl ev0 ∷ s)
    t-extend-Q-vis st (in-progress merge trP (_ , trQ)) = in-progress (int-r merge) trP (_ , bStep st trQ)
    t-extend-Q-vis st (done merge trP (_ , trQ))        = done (int-r merge) trP (_ , bStep st trQ)

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
    t-extend-P-τ (sSil p-eq) (Interleave-trace-aux P' Q big-step)
... | ret _ | sil Q' | refl =
    t-extend-Q-τ (sSil q-eq) (Interleave-trace-aux P Q' big-step)
... | vis _ | sil Q' | refl =
    t-extend-Q-τ (sSil q-eq) (Interleave-trace-aux P Q' big-step)
... | ndbr _ _ _ _ | sil Q' | refl =
    t-extend-Q-τ (sSil q-eq) (Interleave-trace-aux P Q' big-step)
-- NEW: mix | sil Q' — Q takes the silent step. (User's _⦀_ rule: mix _ _ | sil _ = sil (P ⦀ Q'))
... | mix _ _ | sil Q' | refl =
    t-extend-Q-τ (sSil q-eq) (Interleave-trace-aux P Q' big-step)
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
    t-extend-P-vis (sVis p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
... | nothing | ()

-- (b) ret | vis : Q moves alone
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    t-extend-Q-vis (sVis q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
... | nothing | ()

-- (c) vis | vis : four sub-cases, one of which is the internal-choice case
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts
... | just P' | nothing | refl =
    t-extend-P-vis (sVis p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
-- only Q accepts
... | nothing | just Q' | refl =
    t-extend-Q-vis (sVis q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
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
    t-extend-P-vis (sVis p-eq fp-eq) (Interleave-trace-aux P' Q inner-bs)
Interleave-trace-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    t-extend-Q-vis (sVis q-eq fq-eq) (Interleave-trace-aux P Q' inner-bs)
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
    t-extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
... | nothing | ()

-- (b) vis | ndbr : Q moves alone (Q-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    t-extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    t-extend-P-τ (sNdbr p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
... | nothing | ()

-- (d) ndbr | vis : P moves alone (P-distribution)
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    t-extend-P-τ (sNdbr p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
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
    t-extend-P-τ (sNdbr p-eq fp'-eq) (Interleave-trace-aux P' Q big-step)
-- only Q accepts → continuation (P ⦀ Q')
... | nothing | just Q' | refl =
    t-extend-Q-τ (sNdbr q-eq fq'-eq) (Interleave-trace-aux P Q' big-step)
-- both accept → continuation (P' ⦀ Q'); add τ on BOTH sides
... | just P' | just Q' | refl =
    t-extend-both-τ (sNdbr p-eq fp'-eq) (sNdbr q-eq fq'-eq) (Interleave-trace-aux P' Q' big-step)
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
    t-extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
... | nothing | ()

-- (h) NEW: ndbr | mix — P does ndbr-distribution.
Interleave-trace-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    t-extend-P-τ (sNdbr p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
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
    t-extend-Q-τ (sMixSlide q-eq) (Interleave-trace-aux P Q' big-step)
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    t-extend-Q-τ (sMixSlide q-eq) (Interleave-trace-aux P Q' big-step)
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    t-extend-P-τ (sMixSlide p-eq) (Interleave-trace-aux P' Q big-step)
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    t-extend-P-τ (sMixSlide p-eq) (Interleave-trace-aux P' Q big-step)
-- mix | mix: both slide simultaneously to (P' ⦀ Q').
... | mix _ P' | mix _ Q' | refl =
    t-extend-both-τ (sMixSlide p-eq) (sMixSlide q-eq) (Interleave-trace-aux P' Q' big-step)
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
    t-extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-trace-aux P _ big-step)
... | nothing | ()
-- vis | mix: merged vis-function of fP and fQ (same merge as vis|vis under _⦀_).
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P' ⦀ Q (Q stays as the original mix). P side fires a vis step.
... | just P' | nothing | refl =
    t-extend-P-vis (sVis p-eq fp-eq) (Interleave-trace-aux P' Q big-step)
-- only Q accepts: t' = P ⦀ Q''. Q side fires an sMixVis step.
... | nothing | just Q'' | refl =
    t-extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-trace-aux P Q'' big-step)
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
    t-extend-P-vis (sVis p-eq fp-eq) (Interleave-trace-aux P' Q inner-bs)
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    t-extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-trace-aux P Q'' inner-bs)
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
    t-extend-P-vis (sMixVis p-eq fp-eq) (Interleave-trace-aux _ Q big-step)
... | nothing | ()
-- mix | vis: symmetric to vis|mix — P fires via sMixVis, Q via sVis.
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P'' ⦀ Q. P side fires sMixVis.
... | just P'' | nothing | refl =
    t-extend-P-vis (sMixVis p-eq fp-eq) (Interleave-trace-aux P'' Q big-step)
-- only Q accepts: t' = P ⦀ Q'. Q side fires sVis.
... | nothing | just Q' | refl =
    t-extend-Q-vis (sVis q-eq fq-eq) (Interleave-trace-aux P Q' big-step)
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
    t-extend-P-vis (sMixVis p-eq fp-eq) (Interleave-trace-aux P'' Q inner-bs)
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    t-extend-Q-vis (sVis q-eq fq-eq) (Interleave-trace-aux P Q' inner-bs)
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
    t-extend-P-vis (sMixVis p-eq fp-eq) (Interleave-trace-aux P'' Q big-step)
-- only Q accepts: t' = P ⦀ Q''
... | nothing | just Q'' | refl =
    t-extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-trace-aux P Q'' big-step)
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
    t-extend-P-vis (sMixVis p-eq fp-eq) (Interleave-trace-aux P'' Q inner-bs)
Interleave-trace-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    t-extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-trace-aux P Q'' inner-bs)
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
-- Interleave-reach: state-closure split for P ⦀ Q
-----------------------------------------------------------------------------------------
-- A trace `s` of (P ⦀ Q) reaching target `t′` decomposes into an interleaving merge
-- of P's and Q's component traces, recording the reached target state `t′`.  This is
-- the state-level analogue of `Interleave-trace`/`InterleaveSplit`.  Unlike the
-- full-sync parallel reach law, interleave has a genuine collision case: when BOTH P
-- and Q can fire the SAME visible event from their reached states, the operator emits
-- an internal-choice node `⦀-choice P′ Qc Pc Q′` between the two one-sided residuals.
data ParInterleaveSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  : ITree E (ExtI I) (R × S) → List (Event√ E (R × S)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where

  in-progress : ∀ {P′ Q′} {sP sQ s : List (Event E)}
              → Interleave sP sQ s
              → P ═⟨ map evl sP ⟩═► P′
              → Q ═⟨ map evl sQ ⟩═► Q′
              → ParInterleaveSplit P Q (P′ ⦀ Q′) (map evl s)

  -- collision: both components reach collision-time states Pc / Qc (after the prefix sP / sQ),
  -- then each fires the SAME event e (Pc → P′, Qc → Q′), so `_⦀_` emits the choice node
  -- `⦀-choice P′ Qc Pc Q′`.  ONE constructor covers all four force-head variants
  -- (vis/mix × vis/mix): the step relation `Pc ─[ ev (evl e) ]─► P′` is inhabited by `sVis`
  -- (vis-headed side) or `sMixVis` (mix-headed side), so the head shape is absorbed.
  collision : ∀ {Pc Qc P′ Q′} {sP sQ s : List (Event E)} {e : Event E}
            → Interleave sP sQ s
            → P ═⟨ map evl sP ⟩═► Pc
            → Q ═⟨ map evl sQ ⟩═► Qc
            → Pc ─[ ev (evl e) ]─► P′
            → Qc ─[ ev (evl e) ]─► Q′
            → ParInterleaveSplit P Q (⦀-choice P′ Qc Pc Q′) (map evl s ++ [ evl e ])

  done : ∀ {sP sQ s : List (Event E)} {r : R} {q : S}
       → Interleave sP sQ s
       → P ═⟨ map evl sP ++ [ √ r ] ⟩═► deadlock
       → Q ═⟨ map evl sQ ++ [ √ q ] ⟩═► deadlock
       → ParInterleaveSplit P Q deadlock (map evl s ++ [ √ (r , q) ])

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

-- Shared reconstruction lemmas for Parallel-trace-aux.  Like the InterleaveSplit
-- lemmas, but the merge is `Sync cs`: visible events outside `cs` interleave
-- (sync-l / sync-r, carrying the ¬cs proof), events inside `cs` synchronise
-- (sync-both, carrying the cs proof and firing the SAME event on both sides).
private
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           {cs : AnyTypes E → Set}
           {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
           {s : List (Event√ E (R × S))} where

    s-extend-P-τ : ∀ {P′} → P ─[ τ ]─► P′ → SyncSplit cs P′ Q s → SyncSplit cs P Q s
    s-extend-P-τ st (in-progress merge (_ , trP) trQ) = in-progress merge (_ , bTau st trP) trQ
    s-extend-P-τ st (done merge (_ , trP) trQ)        = done merge (_ , bTau st trP) trQ

    s-extend-Q-τ : ∀ {Q′} → Q ─[ τ ]─► Q′ → SyncSplit cs P Q′ s → SyncSplit cs P Q s
    s-extend-Q-τ st (in-progress merge trP (_ , trQ)) = in-progress merge trP (_ , bTau st trQ)
    s-extend-Q-τ st (done merge trP (_ , trQ))        = done merge trP (_ , bTau st trQ)

    s-extend-both-τ : ∀ {P′ Q′} → P ─[ τ ]─► P′ → Q ─[ τ ]─► Q′
                    → SyncSplit cs P′ Q′ s → SyncSplit cs P Q s
    s-extend-both-τ stP stQ (in-progress merge (_ , trP) (_ , trQ)) = in-progress merge (_ , bTau stP trP) (_ , bTau stQ trQ)
    s-extend-both-τ stP stQ (done merge (_ , trP) (_ , trQ))        = done merge (_ , bTau stP trP) (_ , bTau stQ trQ)

    s-extend-P-vis : ∀ {P′ ev0} → ¬ cs (Event.A ev0 , Event.e ev0) → P ─[ ev (evl ev0) ]─► P′
                   → SyncSplit cs P′ Q s → SyncSplit cs P Q (evl ev0 ∷ s)
    s-extend-P-vis ¬p st (in-progress merge (_ , trP) trQ) = in-progress (sync-l ¬p merge) (_ , bStep st trP) trQ
    s-extend-P-vis ¬p st (done merge (_ , trP) trQ)        = done (sync-l ¬p merge) (_ , bStep st trP) trQ

    s-extend-Q-vis : ∀ {Q′ ev0} → ¬ cs (Event.A ev0 , Event.e ev0) → Q ─[ ev (evl ev0) ]─► Q′
                   → SyncSplit cs P Q′ s → SyncSplit cs P Q (evl ev0 ∷ s)
    s-extend-Q-vis ¬p st (in-progress merge trP (_ , trQ)) = in-progress (sync-r ¬p merge) trP (_ , bStep st trQ)
    s-extend-Q-vis ¬p st (done merge trP (_ , trQ))        = done (sync-r ¬p merge) trP (_ , bStep st trQ)

    s-extend-both-vis : ∀ {P′ Q′ ev0} → cs (Event.A ev0 , Event.e ev0)
                      → P ─[ ev (evl ev0) ]─► P′ → Q ─[ ev (evl ev0) ]─► Q′
                      → SyncSplit cs P′ Q′ s → SyncSplit cs P Q (evl ev0 ∷ s)
    s-extend-both-vis p stP stQ (in-progress merge (_ , trP) (_ , trQ)) = in-progress (sync-both p merge) (_ , bStep stP trP) (_ , bStep stQ trQ)
    s-extend-both-vis p stP stQ (done merge (_ , trP) (_ , trQ))        = done (sync-both p merge) (_ , bStep stP trP) (_ , bStep stQ trQ)

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
    s-extend-P-τ (sSil p-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | ret _ | sil Q' | refl =
    s-extend-Q-τ (sSil q-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | vis _ | sil Q' | refl =
    s-extend-Q-τ (sSil q-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | ndbr _ _ _ _ | sil Q' | refl =
    s-extend-Q-τ (sSil q-eq) (Parallel-trace-aux P Q' cs dec big-step)
-- NEW: mix | sil Q' — Q's silent step propagates (user's _∥⇘_¿_⇙_ rule).
... | mix _ _ | sil Q' | refl =
    s-extend-Q-τ (sSil q-eq) (Parallel-trace-aux P Q' cs dec big-step)
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
    s-extend-P-vis ¬p (sVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | ()

-- (b) ret | vis : Q moves alone — only when at ∉ cs
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    s-extend-Q-vis ¬p (sVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | nothing | ()

-- (c) vis | vis : split on dec at
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl with dec at
-- (c.1) at ∈ cs : both must accept
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just Q' | refl =
    s-extend-both-vis p (sVis p-eq fp-eq) (sVis q-eq fq-eq) (Parallel-trace-aux P' Q' cs dec big-step)
... | just _ | nothing | ()
... | nothing | just _ | ()
... | nothing | nothing | ()

-- (c.2) at ∉ cs : interleave
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    s-extend-P-vis ¬p (sVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | just Q' | refl =
    s-extend-Q-vis ¬p (sVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
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
    s-extend-P-vis ¬p (sVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec inner-bs)
Parallel-trace-aux P Q cs dec (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    s-extend-Q-vis ¬p (sVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec inner-bs)
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
    s-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | nothing | ()

-- (b) vis | ndbr : Q moves alone
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    s-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    s-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | ()

-- (d) ndbr | vis : P moves alone
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    s-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
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
    s-extend-P-τ (sNdbr p-eq fp'-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | just Q' | refl =
    s-extend-Q-τ (sNdbr q-eq fq'-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | just P' | just Q' | refl =
    s-extend-both-τ (sNdbr p-eq fp'-eq) (sNdbr q-eq fq'-eq) (Parallel-trace-aux P' Q' cs dec big-step)
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
    s-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
... | nothing | ()

-- (h) NEW: ndbr | mix — P distributes through ndbr.
Parallel-trace-aux P Q cs dec (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    s-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
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
    s-extend-Q-τ (sMixSlide q-eq) (Parallel-trace-aux P Q' cs dec big-step)
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    s-extend-Q-τ (sMixSlide q-eq) (Parallel-trace-aux P Q' cs dec big-step)
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    s-extend-P-τ (sMixSlide p-eq) (Parallel-trace-aux P' Q cs dec big-step)
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    s-extend-P-τ (sMixSlide p-eq) (Parallel-trace-aux P' Q cs dec big-step)
-- mix | mix: both slide.
... | mix _ P' | mix _ Q' | refl =
    s-extend-both-τ (sMixSlide p-eq) (sMixSlide q-eq) (Parallel-trace-aux P' Q' cs dec big-step)
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
    s-extend-Q-vis ¬p (sMixVis q-eq fq-eq) (Parallel-trace-aux P _ cs dec big-step)
... | nothing | ()

-- mix | ret: symmetric — P fires via sMixVis (only outside cs).
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p with fP at a in fp-eq | eq-j
... | just _ | refl =
    s-extend-P-vis ¬p (sMixVis p-eq fp-eq) (Parallel-trace-aux _ Q cs dec big-step)
... | nothing | ()

-- vis | mix: mix's vis merges fP and fQ; dec-filter splits.  Mirrors vis|vis but Q fires sMixVis.
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just _ | refl =
    s-extend-both-vis p (sVis p-eq fp-eq) (sMixVis q-eq fq-eq) (Parallel-trace-aux P' _ cs dec big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    s-extend-P-vis ¬p (sVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | just Q' | refl =
    s-extend-Q-vis ¬p (sMixVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
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
    s-extend-P-vis ¬p (sVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec inner-bs)
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    s-extend-Q-vis ¬p (sMixVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec inner-bs)
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
    s-extend-both-vis p (sMixVis p-eq fp-eq) (sVis q-eq fq-eq) (Parallel-trace-aux _ Q' cs dec big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    s-extend-P-vis ¬p (sMixVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | just Q' | refl =
    s-extend-Q-vis ¬p (sVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
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
    s-extend-P-vis ¬p (sMixVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec inner-bs)
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    s-extend-Q-vis ¬p (sVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec inner-bs)
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
    s-extend-both-vis p (sMixVis p-eq fp-eq) (sMixVis q-eq fq-eq) (Parallel-trace-aux _ _ cs dec big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl
  | no ¬p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | nothing | refl =
    s-extend-P-vis ¬p (sMixVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec big-step)
... | nothing | just Q' | refl =
    s-extend-Q-vis ¬p (sMixVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec big-step)
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
    s-extend-P-vis ¬p (sMixVis p-eq fp-eq) (Parallel-trace-aux P' Q cs dec inner-bs)
Parallel-trace-aux P Q cs dec (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | no ¬p | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    s-extend-Q-vis ¬p (sMixVis q-eq fq-eq) (Parallel-trace-aux P Q' cs dec inner-bs)
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
-- State-closure split for synchronised parallel  P ∥⇘ cs ¿ dec ⇙ Q
-----------------------------------------------------------------------------------------

-- Reachable-state split: a trace `s` of (P ∥⇘ cs ¿ dec ⇙ Q) reaching target `t′`
-- decomposes into a synchronised merge plus the component traces, recording the
-- target state `t′` (not just the trace), so this lemma is a state-closure law.
-- This is the state-level analogue of `Parallel-trace`/`SyncSplit` (which keep only
-- the trace).  FULL-SYNC ONLY: the accompanying `Parallel-reach` takes `full : ∀ at →
-- cs at`, under which every interleave/solo (at∉cs) branch is unreachable — so the
-- trace twin's interleave-collision `⊓`-node case has no counterpart here, and the
-- target is always `P′ ∥⇘ cs ¿ dec ⇙ Q′` or `deadlock`.
data ParReachSplit {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (cs : AnyTypes E → Set) (dec : (at : AnyTypes E) → Dec (cs at))
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  : ITree E (ExtI I) (R × S) → List (Event√ E (R × S)) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs) where

  in-progress : ∀ {P′ Q′} {sP sQ s : List (Event E)}
              → Sync cs sP sQ s
              → P ═⟨ map evl sP ⟩═► P′
              → Q ═⟨ map evl sQ ⟩═► Q′
              → ParReachSplit cs dec P Q (P′ ∥⇘ cs ¿ dec ⇙ Q′) (map evl s)

  done : ∀ {sP sQ s : List (Event E)} {r : R} {q : S}
       → Sync cs sP sQ s
       → P ═⟨ map evl sP ++ [ √ r ] ⟩═► deadlock
       → Q ═⟨ map evl sQ ++ [ √ q ] ⟩═► deadlock
       → ParReachSplit cs dec P Q deadlock (map evl s ++ [ √ (r , q) ])

-----------------------------------------------------------------------------------------
-- Parallel-reach: state-closure split (full-sync precondition makes collision unreachable)
-----------------------------------------------------------------------------------------

-- Shared reconstruction lemmas for Parallel-reach-aux (ParReachSplit, big-step
-- witnesses, Sync merge).  The full-sync precondition makes single-sided visible
-- steps impossible, so only the τ lemmas and the synchronised both-vis lemma occur.
private
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           {cs : AnyTypes E → Set} {dec : (at : AnyTypes E) → Dec (cs at)}
           {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
           {t′ : ITree E (ExtI I) (R × S)} {s : List (Event√ E (R × S))} where

    pr-extend-P-τ : ∀ {P′} → P ─[ τ ]─► P′
                  → ParReachSplit cs dec P′ Q t′ s → ParReachSplit cs dec P Q t′ s
    pr-extend-P-τ st (in-progress merge trP trQ) = in-progress merge (bTau st trP) trQ
    pr-extend-P-τ st (done merge trP trQ)        = done merge (bTau st trP) trQ

    pr-extend-Q-τ : ∀ {Q′} → Q ─[ τ ]─► Q′
                  → ParReachSplit cs dec P Q′ t′ s → ParReachSplit cs dec P Q t′ s
    pr-extend-Q-τ st (in-progress merge trP trQ) = in-progress merge trP (bTau st trQ)
    pr-extend-Q-τ st (done merge trP trQ)        = done merge trP (bTau st trQ)

    pr-extend-both-τ : ∀ {P′ Q′} → P ─[ τ ]─► P′ → Q ─[ τ ]─► Q′
                     → ParReachSplit cs dec P′ Q′ t′ s → ParReachSplit cs dec P Q t′ s
    pr-extend-both-τ stP stQ (in-progress merge trP trQ) = in-progress merge (bTau stP trP) (bTau stQ trQ)
    pr-extend-both-τ stP stQ (done merge trP trQ)        = done merge (bTau stP trP) (bTau stQ trQ)

    pr-extend-both-vis : ∀ {P′ Q′ ev0} → cs (Event.A ev0 , Event.e ev0)
                       → P ─[ ev (evl ev0) ]─► P′ → Q ─[ ev (evl ev0) ]─► Q′
                       → ParReachSplit cs dec P′ Q′ t′ s → ParReachSplit cs dec P Q t′ (evl ev0 ∷ s)
    pr-extend-both-vis p stP stQ (in-progress merge trP trQ) = in-progress (sync-both p merge) (bStep stP trP) (bStep stQ trQ)
    pr-extend-both-vis p stP stQ (done merge trP trQ)        = done (sync-both p merge) (bStep stP trP) (bStep stQ trQ)

Parallel-reach-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (cs : AnyTypes E → Set)
  (dec : (at : AnyTypes E) → Dec (cs at))
  (full : (at : AnyTypes E) → cs at)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_∥⇘_¿_⇙_ {I = I} {R = R} {S = S} P cs dec Q) ═⟨ s ⟩═► t′
  → ParReachSplit cs dec P Q t′ s

-- 1. Empty trace
Parallel-reach-aux P Q cs dec full bNil =
  in-progress sync-nil bNil bNil

-- 2. Tau via sSil — sil head from P or from Q
Parallel-reach-aux P Q cs dec full (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | sil P' | _ | refl =
    pr-extend-P-τ (sSil p-eq) (Parallel-reach-aux P' Q cs dec full big-step)
... | ret _ | sil Q' | refl =
    pr-extend-Q-τ (sSil q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | vis _ | sil Q' | refl =
    pr-extend-Q-τ (sSil q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | ndbr _ _ _ _ | sil Q' | refl =
    pr-extend-Q-τ (sSil q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
-- NEW: mix | sil Q' — Q's silent step propagates (user's _∥⇘_¿_⇙_ rule).
... | mix _ _ | sil Q' | refl =
    pr-extend-Q-τ (sSil q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
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
Parallel-reach-aux P Q cs dec full (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- (a) vis | ret : would be P-solo (at∉cs) in the trace twin; under full-sync at∈cs,
--     so the at∈cs arm refuses (absurd eq-j) and the at∉cs arm is killed by ⊥-elim.
... | vis fP | ret _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p = ⊥-elim (¬p (full at))

-- (b) ret | vis : would be Q-solo (at∉cs); full-sync ⇒ at∈cs, so both arms vanish as in (a).
Parallel-reach-aux P Q cs dec full (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p = ⊥-elim (¬p (full at))

-- (c) vis | vis : split on dec at
Parallel-reach-aux P Q cs dec full (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl with dec at
-- (c.1) at ∈ cs : both must accept
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just Q' | refl =
    pr-extend-both-vis p (sVis p-eq fp-eq) (sVis q-eq fq-eq) (Parallel-reach-aux P' Q' cs dec full big-step)
... | just _ | nothing | ()
... | nothing | just _ | ()
... | nothing | nothing | ()
-- (c.2) at ∉ cs : full-sync ⇒ at ∈ cs, contradiction (collision unreachable).
Parallel-reach-aux P Q cs dec full (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  | no ¬p = ⊥-elim (¬p (full at))

-- (d) absurd head combinations for sVis
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sVis.
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | vis _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 4. Termination via sRet — only when both P and Q are at ret simultaneously
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret rP | ret rQ | refl with big-step
...   | bNil =
        done sync-nil
             (bStep (sRet p-eq) bNil)
             (bStep (sRet q-eq) bNil)
...   | bTau (sSil ()) _
...   | bTau (sNdbr () _) _
...   | bStep (sRet ()) _
...   | bStep (sVis refl ()) _
-- absurd head combinations for sRet
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | sil _ | _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ret _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ret _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | vis _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | vis _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | vis _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- NEW: mix-shape absurds for sRet.
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | mix _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | mix _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | mix _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ret _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | vis _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 5. Tau via sNdbr — at least one of P, Q has an ndbr head (cs is irrelevant for τ)
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- (a) ret | ndbr : Q moves alone (Q-distribution)
... | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    pr-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | nothing | ()

-- (b) vis | ndbr : Q moves alone
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    pr-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    pr-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-reach-aux P' Q cs dec full big-step)
... | nothing | ()

-- (d) ndbr | vis : P moves alone
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    pr-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-reach-aux P' Q cs dec full big-step)
... | nothing | ()

-- (e) ndbr | ndbr : both ndbr; merge on pair indices
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  with i | a
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
... | just P' | nothing | refl =
    pr-extend-P-τ (sNdbr p-eq fp'-eq) (Parallel-reach-aux P' Q cs dec full big-step)
... | nothing | just Q' | refl =
    pr-extend-Q-τ (sNdbr q-eq fq'-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | just P' | just Q' | refl =
    pr-extend-both-τ (sNdbr p-eq fp'-eq) (sNdbr q-eq fq'-eq) (Parallel-reach-aux P' Q' cs dec full big-step)
... | nothing | nothing | ()

-- (f) absurd head combinations for sNdbr
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | ret _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | vis _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()

-- (g) NEW: mix | ndbr — Q distributes through ndbr.
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    pr-extend-Q-τ (sNdbr q-eq fq-eq) (Parallel-reach-aux P Q' cs dec full big-step)
... | nothing | ()

-- (h) NEW: ndbr | mix — P distributes through ndbr.
Parallel-reach-aux P Q cs dec full (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    pr-extend-P-τ (sNdbr p-eq fp-eq) (Parallel-reach-aux P' Q cs dec full big-step)
... | nothing | ()

-- (i) NEW: mix-shape absurds for sNdbr.
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bTau (sNdbr eq-f eq-j) big-step) | vis _ | mix _ _ | ()

-- ----- 6. NEW: bTau via sMixSlide. force (P ∥cs⇙ Q) ≡ mix _ Qt. -----
Parallel-reach-aux P Q cs dec full (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix: Q slides.
... | ret _ | mix _ Q' | refl =
    pr-extend-Q-τ (sMixSlide q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    pr-extend-Q-τ (sMixSlide q-eq) (Parallel-reach-aux P Q' cs dec full big-step)
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    pr-extend-P-τ (sMixSlide p-eq) (Parallel-reach-aux P' Q cs dec full big-step)
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    pr-extend-P-τ (sMixSlide p-eq) (Parallel-reach-aux P' Q cs dec full big-step)
-- mix | mix: both slide.
... | mix _ P' | mix _ Q' | refl =
    pr-extend-both-τ (sMixSlide p-eq) (sMixSlide q-eq) (Parallel-reach-aux P' Q' cs dec full big-step)
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
-- ret | mix : would be Q-solo (at∉cs) via sMixVis in the trace twin; full-sync ⇒ at∈cs,
--     so the at∈cs arm refuses (absurd eq-j) and the at∉cs arm is killed by ⊥-elim.
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret _ | mix fQ _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p = ⊥-elim (¬p (full at))

-- mix | ret: would be P-solo (at∉cs) via sMixVis; full-sync ⇒ at∈cs, so both arms vanish.
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with dec at
... | yes _ = case eq-j of λ ()
... | no ¬p = ⊥-elim (¬p (full at))

-- vis | mix: mix's vis merges fP and fQ; dec-filter splits.  Mirrors vis|vis but Q fires sMixVis.
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just P' | just _ | refl =
    pr-extend-both-vis p (sVis p-eq fp-eq) (sMixVis q-eq fq-eq) (Parallel-reach-aux P' _ cs dec full big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  | no ¬p = ⊥-elim (¬p (full at))

-- mix | vis: symmetric to vis | mix.  P fires via sMixVis, Q via sVis.
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _  | just Q' | refl =
    pr-extend-both-vis p (sMixVis p-eq fp-eq) (sVis q-eq fq-eq) (Parallel-reach-aux _ Q' cs dec full big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  | no ¬p = ⊥-elim (¬p (full at))

-- mix | mix: both fire via sMixVis.  Mirrors vis|vis structure.
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl with dec at
... | yes p with fP at a in fp-eq | fQ at a in fq-eq | eq-j
... | just _ | just _ | refl =
    pr-extend-both-vis p (sMixVis p-eq fp-eq) (sMixVis q-eq fq-eq) (Parallel-reach-aux _ _ cs dec full big-step)
... | just _  | nothing | ()
... | nothing | just _  | ()
... | nothing | nothing | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl
  | no ¬p = ⊥-elim (¬p (full at))
-- Absurd: non-mix shapes (must use full function-name clauses, not `...`,
-- because the preceding deep-nested productive case escapes outer-with continuation).
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | sil _ | _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ret _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | vis _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Parallel-reach-aux P Q cs dec full (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()

-- State-closure law: the state-level analogue of `Parallel-trace`.  Given full
-- synchronisation (`full : ∀ at → cs at`), every reachable state of (P ∥⇘ cs ¿ dec ⇙ Q)
-- is `P′ ∥⇘ cs ¿ dec ⇙ Q′` (component residuals, `in-progress`) or `deadlock` (`done`).
Parallel-reach : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  (cs : AnyTypes E → Set) (dec : (at : AnyTypes E) → Dec (cs at))
  (full : (at : AnyTypes E) → cs at)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_∥⇘_¿_⇙_ {I = I} {R = R} {S = S} P cs dec Q) ═⟨ s ⟩═► t′
  → ParReachSplit cs dec P Q t′ s
Parallel-reach P Q cs dec full bs = Parallel-reach-aux P Q cs dec full bs

private
  -- Sanity: under full-sync, the empty trace decomposes to both components at their start.
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S) where
    private
      csTrue  : AnyTypes E → Set
      csTrue _ = ⊤ {lzero}
      decTrue : (at : AnyTypes E) → Dec (csTrue at)
      decTrue _ = yes tt
      fullTrue : (at : AnyTypes E) → csTrue at
      fullTrue _ = tt
    _ : ParReachSplit csTrue decTrue P Q (P ∥⇘ csTrue ¿ decTrue ⇙ Q) []
    _ = Parallel-reach P Q csTrue decTrue fullTrue bNil



-----------------------------------------------------------------------------
-- DRBisim lemmas
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- sil-τ-refl: standalone; if `force P ≡ sil P'`, then `P ≈ P'`.
-- Copied from `ExternalChoice_DRBisim` so this module is self-contained.
-----------------------------------------------------------------------------

sil-τ-refl :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {P P' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → DRWbisim _≡_ P P'
sil-τ-refl eqP .fwd .on-ret eq =
      case trans (sym eqP) eq of λ ()
sil-τ-refl eqP .fwd .on-vis (sVis force-eq _) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-vis (sMixVis force-eq _) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-tau (sSil force-eq)
  with sil-injective (trans (sym force-eq) eqP)
... | refl = _ , weak-τ τ*-zero , drwbisim-refl _
sil-τ-refl eqP .fwd .on-tau (sNdbr force-eq _) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-tau (sMixSlide force-eq) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-div d
  with d .Divergent.step
...  | sSil force-eq with sil-injective (trans (sym force-eq) eqP)
...  | refl = d .Divergent.diverge
sil-τ-refl eqP .fwd .on-div d | sNdbr force-eq _ =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-div d | sMixSlide force-eq =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl {P = P} {P' = P'} eqP .bwd .on-ret {r = r} eq =
      P' , r , weak-τ (τ*-step (sSil eqP) τ*-zero) , eq , refl
sil-τ-refl eqP .bwd .on-vis step =
      _ , weak-ev (τ*-step (sSil eqP) τ*-zero) step τ*-zero , drwbisim-refl _
sil-τ-refl eqP .bwd .on-tau step =
      _ , weak-τ (τ*-step (sSil eqP) (τ*-step step τ*-zero)) , drwbisim-refl _
sil-τ-refl eqP .bwd .on-div d =
      divergent-prefix (τ*-step (sSil eqP) τ*-zero) d

-----------------------------------------------------------------------------
-- Force-unfolding helpers for `P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')`.
-----------------------------------------------------------------------------

-- When `force P ≡ sil P'`, the parallel composition takes a τ to
-- `(P' ∥⇘ cs ¿ dec ⇙ T)` (rule A — sil-from-left).
force-∥-sil-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → {P P' : ITree E (ExtI I) R}
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (T : ITree E (ExtI I) S)
  → ITree.force P ≡ sil P'
  → ITree.force (P ∥⇘ cs ¿ dec ⇙ T) ≡ sil (P' ∥⇘ cs ¿ dec ⇙ T)
force-∥-sil-L {P = P} cs dec T eqP
  with ITree.force P | eqP
... | sil _ | refl = refl

-- The symmetric rule: P stable (i.e. not sil), force T ≡ sil T'.
-- Specialised to T = (Q ⊓ R'), `force T ≡ sil T'` is impossible because
-- `force (Q ⊓ R')` is by definition an `ndbr`.  Stated for symmetry.

-- Symmetric rule used by the L-distributivity proof: when the left
-- operand is an internal choice `(P ⊓ Q)` (whose force is `ndbr …`, never
-- `sil`), the operator's first clause does NOT fire, so a `sil` on the
-- *right* operand `R'` propagates: `force ((P⊓Q) ∥ R') ≡ sil ((P⊓Q) ∥ R'')`.
force-∥-sil-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → {R' R'' : ITree E (ExtI I) S}
  → ITree.force R' ≡ sil R''
  → ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡ sil ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R'')
force-∥-sil-R P Q cs dec {R' = R'} eqR
  with ITree.force R' | eqR
... | sil _ | refl = refl

-- Unfold `force (P ∥ (Q⊓R'))` when `force P ≡ ret r`.  The compound's
-- force is the *exact* `ndbr` produced by Parallel.agda's ret/ndbr rule,
-- here returned existentially together with the witness equations for
-- the two non-empty branches `lift fzero` (yielding `P ∥ Q`) and
-- `lift (fsuc fzero)` (yielding `P ∥ R'`).
force-∥R-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → {P : ITree E (ExtI I) R} {r : R}
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → ITree.force P ≡ ret r
  → Σ[ f' ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ pr ∈ Is-just (f' (Lift _ (Fin 2) , fin) (lift fzero)) ]
      ( ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡
          ndbr f' (Lift _ (Fin 2) , fin) (lift fzero) pr
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc n)) , fin) (lift fzero)
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ Q))
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc (suc n))) , fin) (lift (fsuc fzero))
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {A : Set ℓ} {ai : I A} {a : A}
           → f' (A , base ai) a ≡ nothing)
      × (∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ} {a : AP × AQ}
           → f' ((AP × AQ) , pair iP iQ) a ≡ nothing)
      × (∀ {n : ℕ} {i : Fin (suc n)} → f' (Lift _ (Fin (suc (suc (suc n)))) , fin)
                                           (lift (fsuc (fsuc i))) ≡ nothing) )
force-∥R-ret {P = P} cs dec Q R' eqP
  with ITree.force P | eqP
... | ret _ | refl = _ , _ , refl , refl , refl , refl , refl , refl



-- Unfold `force (P ∥ (Q⊓R'))` when `force P ≡ vis fP`.  Same shape as
-- the ret case; the `Q⊓R'` side dominates branching.
force-∥R-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → {P : ITree E (ExtI I) R}
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → ITree.force P ≡ vis fP
  → Σ[ f' ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ pr ∈ Is-just (f' (Lift _ (Fin 2) , fin) (lift fzero)) ]
      ( ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡
          ndbr f' (Lift _ (Fin 2) , fin) (lift fzero) pr
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc n)) , fin) (lift fzero)
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ Q))
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc (suc n))) , fin) (lift (fsuc fzero))
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {A : Set ℓ} {ai : I A} {a : A}
           → f' (A , base ai) a ≡ nothing)
      × (∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ} {a : AP × AQ}
           → f' ((AP × AQ) , pair iP iQ) a ≡ nothing)
      × (∀ {n : ℕ} {i : Fin (suc n)} → f' (Lift _ (Fin (suc (suc (suc n)))) , fin)
                                           (lift (fsuc (fsuc i))) ≡ nothing) )
force-∥R-vis {P = P} cs dec Q R' eqP
  with ITree.force P | eqP
... | vis _ | refl = _ , _ , refl , refl , refl , refl , refl , refl


-- Unfold for L-distributivity:  `force ((P⊓Q) ∥ R')` when `force R' ≡ ret s`.
-- Mirror of `force-∥R-ret`: the compound `(P⊓Q)` has force `ndbr (br2 P Q) …`
-- definitionally, so the `ndbr | ret` rule of `_∥⇘_¿_⇙_` fires, producing
-- the post-composed lambda `f'` with `f' (_,fin)(lift fzero) = just (P∥R')`
-- and `f' (_,fin)(lift (fsuc fzero)) = just (Q∥R')` (∀ {n}, since `br2`'s
-- `fin` clause ignores the arity).
force-∥L-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → {R' : ITree E (ExtI I) S} {s : S}
  → ITree.force R' ≡ ret s
  → Σ[ f' ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ pr ∈ Is-just (f' (Lift _ (Fin 2) , fin) (lift fzero)) ]
      ( ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡
          ndbr f' (Lift _ (Fin 2) , fin) (lift fzero) pr
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc n)) , fin) (lift fzero)
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc (suc n))) , fin) (lift (fsuc fzero))
                       ≡ just (Q ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {A : Set ℓ} {ai : I A} {a : A}
           → f' (A , base ai) a ≡ nothing)
      × (∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ} {a : AP × AQ}
           → f' ((AP × AQ) , pair iP iQ) a ≡ nothing)
      × (∀ {n : ℕ} {i : Fin (suc n)} → f' (Lift _ (Fin (suc (suc (suc n)))) , fin)
                                           (lift (fsuc (fsuc i))) ≡ nothing) )
force-∥L-ret P Q cs dec {R' = R'} eqR
  with ITree.force R' | eqR
... | ret _ | refl = _ , _ , refl , refl , refl , refl , refl , refl

-- Unfold for L-distributivity:  `force ((P⊓Q) ∥ R')` when `force R' ≡ vis fR`.
-- Mirror of `force-∥R-vis`; same shape as the ret case.
force-∥L-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → {R' : ITree E (ExtI I) S}
  → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
  → ITree.force R' ≡ vis fR
  → Σ[ f' ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ pr ∈ Is-just (f' (Lift _ (Fin 2) , fin) (lift fzero)) ]
      ( ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡
          ndbr f' (Lift _ (Fin 2) , fin) (lift fzero) pr
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc n)) , fin) (lift fzero)
                       ≡ just (P ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {n : ℕ} → f' (Lift _ (Fin (suc (suc n))) , fin) (lift (fsuc fzero))
                       ≡ just (Q ∥⇘ cs ¿ dec ⇙ R'))
      × (∀ {A : Set ℓ} {ai : I A} {a : A}
           → f' (A , base ai) a ≡ nothing)
      × (∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ} {a : AP × AQ}
           → f' ((AP × AQ) , pair iP iQ) a ≡ nothing)
      × (∀ {n : ℕ} {i : Fin (suc n)} → f' (Lift _ (Fin (suc (suc (suc n)))) , fin)
                                           (lift (fsuc (fsuc i))) ≡ nothing) )
force-∥L-vis P Q cs dec {R' = R'} eqR
  with ITree.force R' | eqR
... | vis _ | refl = _ , _ , refl , refl , refl , refl , refl , refl

-----------------------------------------------------------------------------
-- Forward declarations of the laws (so sub-lemmas can corecursively
-- invoke them through `⊓-cong`).
-----------------------------------------------------------------------------

∥-⊓-distrib-R :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≈ ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R'))

∥-⊓-distrib-L :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≈ ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R'))

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-R sub-lemmas (forward simulation).
--
-- The `fwd` direction must, for each one-step LTS transition out of
-- `P ∥ (Q⊓R')`, produce a weak matching transition out of
-- `(P∥Q) ⊓ (P∥R')` and a bisim witness on the successors.  The shape of
-- `force P` determines what kind of step the LHS can take.
--
-- Notation:  LHS = P ∥ (Q⊓R'),  RHS = (P∥Q) ⊓ (P∥R').
-----------------------------------------------------------------------------

-- Postulates for the residual sub-cases.  Declared up-front so the
-- main on-tau dispatcher can refer to them.  Proof plans:
--
-- distrib-R-fwd-on-tau-stable-ret:
--   force P = ret r ⇒ force LHS = ndbr f' (Lift _ Fin 2, fin) (lift fzero) pr
--   where f' is the post-composed lambda from `Parallel.agda` ret/ndbr rule.
--   The step sNdbr force-eq j-eq picks some index (i,a).  Productive
--   choices are (Lift _ Fin n, fin) with a ∈ {lift fzero, lift (fsuc fzero)},
--   yielding successors `P∥Q` and `P∥R'` resp.  Match the RHS sNdbr at
--   the same `br2` branch, bisim is `drwbisim-refl`.  Implementation
--   needs a small `subst` to convert j-eq from `Fin n` to `Fin 2`
--   because the unfolding lemma `force-∥R-ret` fixes the witness arity
--   at 2 while the step's `i` carries an unconstrained `n`.
--
-- distrib-R-fwd-on-tau-stable-vis:
--   Identical structure to -ret, replacing `force-∥R-ret` with
--   `force-∥R-vis`.
--
-- distrib-R-fwd-on-tau-ndbr-J:
--   J-rule paired-branching case.  force P = ndbr fP (AP, iP) waP wpP,
--   force (Q⊓R') = ndbr (br2 Q R') (Lift _ Fin 2, fin) (lift fzero) _.
--   force LHS = ndbr (mergeNdbr-style) ((AP × (Lift _ Fin 2)) , pair iP fin)
--                    ((waP, lift fzero)) ...
--   Mirrors the `mergeNdbr-pair-jj/-jn/-nj` lemma family from
--   ExternalChoice; cf. `comm-tau-ndbr-step` there.  Index juggling
--   for `pair (proj₂ wiP) (Lift Fin 2, fin)` plus the merge continuation
--   makes a clean direct proof tedious; left postulated per the spec
--   `2026-05-07-parallel-drbisim-distrib-design.md`.
-- distrib-R-fwd-on-tau-stable-ret: real proof.
--
-- When `force P ≡ ret r`, `force (P ∥ (Q⊓R'))` reduces (per the ret/ndbr
-- rule of `_∥⇘_¿_⇙_` and the ndbr-form of `_⊓_`) to a literal
-- `ndbr f' (Lift _ (Fin 2), fin) (lift fzero) (any-just tt₀)` where f' is
-- the post-composed lambda producing `P∥Q` and `P∥R'` respectively.
-- Pattern-matching on the τ step's index thus mirrors `⊓-comm` exactly.
distrib-R-fwd-on-tau-stable-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {r : R}
  → ITree.force P ≡ ret r
  → {t' : ITree E (ExtI I) (R × S)}
  → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-R-fwd-on-tau-stable-ret {R = R} {S = S} P cs dec Q R' {r = r} eqP step
  with force-∥R-ret cs dec Q R' eqP | τ-ndbr step
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₁ (u , sil-eq , _)
    = ⊥-elim (case trans (sym force-eq) sil-eq of λ ())
... | f' , pr , force-eq , _ , _ , _ , _ , _
    | inj₂ (inj₂ (g , Qt , mix-eq , _))
    = ⊥-elim (case trans (sym force-eq) mix-eq of λ ())
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₂ (inj₁ (g , wi , wa , prf , i , a , ndbr-eq , j-eq))
    with trans (sym ndbr-eq) force-eq
...   | refl = handle i a j-eq
  where
    maybe-itree : Maybe (ITree E (ExtI _) (R × S)) → ITree E (ExtI _) (R × S)
    maybe-itree (just x) = x
    maybe-itree nothing  = deadlock
    handle :
        (i : AnyTypes (ExtI _)) (a : proj₁ i)
        {t' : ITree E (ExtI _) (R × S)}
        → f' i a ≡ just t'
        → Σ[ u' ∈ ITree E (ExtI _) (R × S) ]
            ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
            × t' ≈ u' )
    handle (_ , base _) _ j-eq =
        ⊥-elim (case trans (sym eq-base) j-eq of λ ())
    handle (_ , pair _ _) _ j-eq =
        ⊥-elim (case trans (sym eq-pair) j-eq of λ ())
    handle (_ , fin {n = zero}) (lift ()) _
    handle (_ , fin {n = suc n}) (lift fzero) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ Q) ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ Q) (P ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ Q))
              (trans (sym (eq-fzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc zero}) (lift (fsuc ())) _
    handle (_ , fin {n = suc (suc n)}) (lift (fsuc fzero)) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ Q) (P ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fsucfzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc (suc (suc n))}) (lift (fsuc (fsuc i))) j-eq =
        ⊥-elim (case trans (sym (eq-fin-big {n = n} {i = i})) j-eq of λ ())

-- distrib-R-fwd-on-tau-stable-vis: identical structure to -ret (the
-- post-composed lambda for `vis fP | ndbr (br2 Q R')` is the same shape).
distrib-R-fwd-on-tau-stable-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → {t' : ITree E (ExtI I) (R × S)}
  → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-R-fwd-on-tau-stable-vis {R = R} {S = S} P cs dec Q R' eqP step
  with force-∥R-vis cs dec Q R' eqP | τ-ndbr step
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₁ (u , sil-eq , _)
    = ⊥-elim (case trans (sym force-eq) sil-eq of λ ())
... | f' , pr , force-eq , _ , _ , _ , _ , _
    | inj₂ (inj₂ (g , Qt , mix-eq , _))
    = ⊥-elim (case trans (sym force-eq) mix-eq of λ ())
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₂ (inj₁ (g , wi , wa , prf , i , a , ndbr-eq , j-eq))
    with trans (sym ndbr-eq) force-eq
...   | refl = handle i a j-eq
  where
    maybe-itree : Maybe (ITree E (ExtI _) (R × S)) → ITree E (ExtI _) (R × S)
    maybe-itree (just x) = x
    maybe-itree nothing  = deadlock
    handle :
        (i : AnyTypes (ExtI _)) (a : proj₁ i)
        {t' : ITree E (ExtI _) (R × S)}
        → f' i a ≡ just t'
        → Σ[ u' ∈ ITree E (ExtI _) (R × S) ]
            ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
            × t' ≈ u' )
    handle (_ , base _) _ j-eq =
        ⊥-elim (case trans (sym eq-base) j-eq of λ ())
    handle (_ , pair _ _) _ j-eq =
        ⊥-elim (case trans (sym eq-pair) j-eq of λ ())
    handle (_ , fin {n = zero}) (lift ()) _
    handle (_ , fin {n = suc n}) (lift fzero) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ Q) ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ Q) (P ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ Q))
              (trans (sym (eq-fzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc zero}) (lift (fsuc ())) _
    handle (_ , fin {n = suc (suc n)}) (lift (fsuc fzero)) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ Q) (P ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fsucfzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc (suc (suc n))}) (lift (fsuc (fsuc i))) j-eq =
        ⊥-elim (case trans (sym (eq-fin-big {n = n} {i = i})) j-eq of λ ())

postulate
  distrib-R-fwd-on-tau-ndbr-J :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
      {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
    → ITree.force P ≡ ndbr fP wiP waP wpP
    → {t' : ITree E (ExtI I) (R × S)}
    → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ─[ τ ]─► t'
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
        × t' ≈ u' )

  -- New: `mix` case for `force P`.  The `mix` shape produces a parallel
  -- compound whose force is itself `mix` (vis-side merged, slide-side
  -- becomes the parallel of slide-target with (Q⊓R')).  The simulation
  -- argument mirrors the ret/vis ones; left postulated for now.
  distrib-R-fwd-on-tau-stable-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
    → ITree.force P ≡ mix fP Qt
    → {t' : ITree E (ExtI I) (R × S)}
    → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ─[ τ ]─► t'
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
        × t' ≈ u' )

  distrib-R-bwd-on-tau-ndbr-J-zero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
      {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
    → ITree.force P ≡ ndbr fP wiP waP wpP
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ Q) ≈ u' )

  distrib-R-bwd-on-tau-ndbr-J-suc :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
      {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
    → ITree.force P ≡ ndbr fP wiP waP wpP
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

  -- `mix` cases for the backward direction (fzero / fsuc-fzero branches).
  -- These mirror the ndbr-J postulates; the simulation reasoning under
  -- the `mix` shape of `force P` needs the dec-filter merge, left
  -- postulated for now.
  distrib-R-bwd-on-tau-stable-mix-fzero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
    → ITree.force P ≡ mix fP Qt
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ Q) ≈ u' )

  distrib-R-bwd-on-tau-stable-mix-fsucfzero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (Q R' : ITree E (ExtI I) S)
    → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
    → ITree.force P ≡ mix fP Qt
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

-- The on-tau forward sub-lemma dispatches on `force P`:
--
--   * `force P = sil P'` — the LHS step is `sSil`, with successor
--     `P' ∥ (Q⊓R')`.  The RHS matches by doing zero τ-steps and
--     recovering bisim via the chain:
--       P' ∥ (Q⊓R')
--         ≈ (P'∥Q) ⊓ (P'∥R')   -- corecursive ∥-⊓-distrib-R on P'
--         ≈ (P∥Q) ⊓ (P∥R')     -- ⊓-cong (sym sil-τ-refl) twice
--     This branch is fully proved.
--
--   * `force P = ret r`  — the LHS step is an sNdbr through the
--     post-composed `f'`.  Productive branches: `(_, fin) (lift fzero)`
--     yielding `P∥Q`, and `(_, fin) (lift (fsuc fzero))` yielding `P∥R'`.
--     RHS matches by selecting the same `br2` branch.  The structural
--     pattern is identical to the proved `⊓-comm`/`⊓-idem` cases, but
--     the `Lift ℓ (Fin n)` arity in the step's index does not unify
--     with the unfolding's `Fin 2` without an explicit `subst` lemma.
--     Postulated below; proof plan in the same comment block as the
--     vis case.
--
--   * `force P = vis fP` — same structural shape as the ret case;
--     postulated for the same arity-unification reason.
--
--   * `force P = ndbr fP _ _ _` — the J-rule paired-branching case;
--     postulated per the spec.
--
-- Marked `NON_TERMINATING` because the sil case appeals corecursively
-- to `∥-⊓-distrib-R` through `⊓-cong`.
-- {-# NON_TERMINATING #-}
distrib-R-fwd-on-tau :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {t' : ITree E (ExtI I) (R × S)}
  → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-R-fwd-on-tau P cs dec Q R' step
  with ITree.force P | inspect ITree.force P
... | sil P' | Eq.[ eqP ] with step
...   | sSil force-eq
      with sil-injective (trans (sym force-eq) (force-∥-sil-L cs dec (Q ⊓ R') eqP))
...     | refl =
            ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ,
            weak-τ τ*-zero ,
            drwbisim-trans
              (∥-⊓-distrib-R P' cs dec Q R')
              (⊓-cong (drwbisim-sym (sil-τ-refl (force-∥-sil-L cs dec Q eqP)))
                      (drwbisim-sym (sil-τ-refl (force-∥-sil-L cs dec R' eqP))))
distrib-R-fwd-on-tau P cs dec Q R' _
  | sil _ | Eq.[ eqP ] | sNdbr force-ndbr _ =
      case trans (sym (force-∥-sil-L cs dec (Q ⊓ R') eqP)) force-ndbr of λ ()
-- sMixSlide case at force P ≡ sil P': absurd, since force LHS ≡ sil _, not mix.
distrib-R-fwd-on-tau P cs dec Q R' _
  | sil _ | Eq.[ eqP ] | sMixSlide force-mix =
      case trans (sym (force-∥-sil-L cs dec (Q ⊓ R') eqP)) force-mix of λ ()
-- ret/vis/ndbr cases postulated; see proof plans below.
distrib-R-fwd-on-tau P cs dec Q R' step
  | ret r | Eq.[ eqP ] = distrib-R-fwd-on-tau-stable-ret P cs dec Q R' eqP step
distrib-R-fwd-on-tau P cs dec Q R' step
  | vis fP | Eq.[ eqP ] = distrib-R-fwd-on-tau-stable-vis P cs dec Q R' eqP step
distrib-R-fwd-on-tau P cs dec Q R' step
  | ndbr fP wiP waP wpP | Eq.[ eqP ] = distrib-R-fwd-on-tau-ndbr-J P cs dec Q R' eqP step
-- mix case: postulated (mirrors the ret/vis/ndbr stable-helper pattern).
distrib-R-fwd-on-tau P cs dec Q R' step
  | mix fP Qt | Eq.[ eqP ] = distrib-R-fwd-on-tau-stable-mix P cs dec Q R' eqP step

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-R: assembly.  Aside from the J-rule postulate above,
-- everything is direct because LHS force is never `ret` or `vis` (always
-- `sil` or `ndbr`).
-----------------------------------------------------------------------------

-- bwd: each τ step out of `(P∥Q) ⊓ (P∥R')` is matched by LHS doing some
-- τ steps to a bisim-equivalent successor.
--
-- The step out of RHS picks `(P∥Q)` (lift fzero) or `(P∥R')` (lift (fsuc
-- fzero)).  Matching from LHS depends on `force P`:
--   * `force P = sil P'`: the sil chain may not terminate; the proof
--     requires the "lift τ* through P" technique (cf. `lift-via-bisim`)
--     mutually with this lemma.
--   * `force P = ret r`: LHS's force is the ndbr from `force-∥R-ret`;
--     pick the same `(_ , fin) (lift fzero)` / `(lift (fsuc fzero))`
--     index, get `P∥Q`/`P∥R'`, bisim-refl.
--   * `force P = vis fP`: same shape as ret.
--   * `force P = ndbr`: J-rule paired-branch case — postulated.
--
-- The bwd dispatcher: dispatch on `force P`.  ret/vis give direct
-- ndbr-step matching; sil recurses through `∥-⊓-distrib-R` corecursively;
-- ndbr-J postulated for the merge-rule case.

distrib-R-bwd-on-tau-stable-ret-fzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {r : R}
  → ITree.force P ≡ ret r
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ Q) ≈ u' )
distrib-R-bwd-on-tau-stable-ret-fzero P cs dec Q R' eqP
  with force-∥R-ret cs dec Q R' eqP
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ Q) ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         force-eq (eq-fzero {n = 1}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-R-bwd-on-tau-stable-ret-fsucfzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {r : R}
  → ITree.force P ≡ ret r
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-R-bwd-on-tau-stable-ret-fsucfzero P cs dec Q R' eqP
  with force-∥R-ret cs dec Q R' eqP
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         force-eq (eq-fsucfzero {n = 0}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-R-bwd-on-tau-stable-vis-fzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ Q) ≈ u' )
distrib-R-bwd-on-tau-stable-vis-fzero P cs dec Q R' eqP
  with force-∥R-vis cs dec Q R' eqP
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ Q) ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         force-eq (eq-fzero {n = 1}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-R-bwd-on-tau-stable-vis-fsucfzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-R-bwd-on-tau-stable-vis-fsucfzero P cs dec Q R' eqP
  with force-∥R-vis cs dec Q R' eqP
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         force-eq (eq-fsucfzero {n = 0}))
                  τ*-zero) ,
        drwbisim-refl _

{-# NON_TERMINATING #-}
distrib-R-bwd-on-tau :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {t' : ITree E (ExtI I) (R × S)}
  → ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-R-bwd-on-tau P cs dec Q R' (sSil ())
distrib-R-bwd-on-tau P cs dec Q R' (sNdbr {i = (_ , base _)}   refl ())
distrib-R-bwd-on-tau P cs dec Q R' (sNdbr {i = (_ , pair _ _)} refl ())
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  with ITree.force P | inspect ITree.force P
... | sil P' | Eq.[ eqP ]
    with distrib-R-bwd-on-tau P' cs dec Q R'
           (sNdbr {p = (P' ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P' ∥⇘ cs ¿ dec ⇙ R')}
                  {f = br2 (P' ∥⇘ cs ¿ dec ⇙ Q) (P' ∥⇘ cs ¿ dec ⇙ R')}
                  {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                  refl refl)
... | u'' , weak-τ chain , bisim =
        u'' ,
        weak-τ (τ*-step (sSil (force-∥-sil-L cs dec (Q ⊓ R') eqP)) chain) ,
        drwbisim-trans
          (sil-τ-refl (force-∥-sil-L cs dec Q eqP))
          bisim
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | ret r | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-ret-fzero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | vis _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-vis-fzero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | ndbr _ _ _ _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-ndbr-J-zero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | mix _ _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-mix-fzero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  with ITree.force P | inspect ITree.force P
... | sil P' | Eq.[ eqP ]
    with distrib-R-bwd-on-tau P' cs dec Q R'
           (sNdbr {p = (P' ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P' ∥⇘ cs ¿ dec ⇙ R')}
                  {f = br2 (P' ∥⇘ cs ¿ dec ⇙ Q) (P' ∥⇘ cs ¿ dec ⇙ R')}
                  {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                  refl refl)
... | u'' , weak-τ chain , bisim =
        u'' ,
        weak-τ (τ*-step (sSil (force-∥-sil-L cs dec (Q ⊓ R') eqP)) chain) ,
        drwbisim-trans
          (sil-τ-refl (force-∥-sil-L cs dec R' eqP))
          bisim
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | ret r | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-ret-fsucfzero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | vis _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-vis-fsucfzero P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | ndbr _ _ _ _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-ndbr-J-suc P cs dec Q R' eqP
distrib-R-bwd-on-tau P cs dec Q R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | mix _ _ | Eq.[ eqP ] =
      distrib-R-bwd-on-tau-stable-mix-fsucfzero P cs dec Q R' eqP

-----------------------------------------------------------------------------
-- Assembly of `∥-⊓-distrib-R`.
-----------------------------------------------------------------------------

-- on-ret/on-vis cases: LHS force is never ret or vis (always sil
-- or ndbr depending on `force P` × `force (Q⊓R')`).  The proof closes
-- by absurdity in each `force P` branch but typecheking the absurdity
-- through the reduced `force LHS` requires care.  Postulated; trivial
-- proof plan: dispatch on `force P`, derive `force LHS ≡ sil/ndbr ...`
-- from `force-∥-sil-L` / `force-∥R-{ret,vis}` plus the merge rule for
-- ndbr/ndbr; in each case `eq : force LHS ≡ ret _` (or `≡ vis _`) is
-- absurd.
-- The on-ret/on-vis cases close by absurdity: `force LHS` is never
-- `ret` or `vis` because `force (Q⊓R')` is `ndbr`, forcing the parallel
-- compound's force to be either `sil` (when `force P = sil`) or `ndbr`.

-- Head-unfolding lemmas (note `P` is EXPLICIT: an implicit `P` blocks the
-- `with ITree.force P` abstraction).  When `force P` is `ndbr`/`mix`, the
-- operator's ndbr/ndbr (resp. mix/ndbr) clause fires — `force (Q⊓R')` is
-- always `ndbr` — so `force (P ∥ (Q⊓R'))` is `ndbr`-headed.  Proved by `refl`.
force-∥R-ndbr-eq :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → Σ[ g ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ wi ∈ AnyTypes (ExtI I) ] Σ[ wa ∈ proj₁ wi ] Σ[ pr ∈ Is-just (g wi wa) ]
      ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡ ndbr g wi wa pr
force-∥R-ndbr-eq P cs dec Q R' eqP with ITree.force P | eqP
... | ndbr _ (_ , _) _ _ | refl = _ , _ , _ , _ , refl

force-∥R-mix-eq :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {Pt : ITree E (ExtI I) R}
  → ITree.force P ≡ mix fP Pt
  → Σ[ g ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ wi ∈ AnyTypes (ExtI I) ] Σ[ wa ∈ proj₁ wi ] Σ[ pr ∈ Is-just (g wi wa) ]
      ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡ ndbr g wi wa pr
force-∥R-mix-eq P cs dec Q R' eqP with ITree.force P | eqP
... | mix _ _ | refl = _ , _ , _ , _ , refl

-- `force (P ∥ (Q⊓R'))` is never `mix`-headed: case on `force P`
-- (sil ⇒ sil; ret/vis/ndbr/mix ⇒ ndbr — none is `mix`).
force-∥R-notmix :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
    {Qt : ITree E (ExtI I) (R × S)}
  → ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡ mix f Qt
  → ⊥
force-∥R-notmix P cs dec Q R' fe = aux (ITree.force P) refl
  where
    aux : (k : NodeKind E (ExtI _) _) → ITree.force P ≡ k → ⊥
    aux (sil _) eqP =
        case trans (sym (force-∥-sil-L cs dec (Q ⊓ R') eqP)) fe of λ ()
    aux (ret _) eqP with force-∥R-ret cs dec Q R' eqP
    ... | _ , _ , feq , _ = case trans (sym feq) fe of λ ()
    aux (vis _) eqP with force-∥R-vis cs dec Q R' eqP
    ... | _ , _ , feq , _ = case trans (sym feq) fe of λ ()
    aux (ndbr _ _ _ _) eqP with force-∥R-ndbr-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) fe of λ ()
    aux (mix _ _) eqP with force-∥R-mix-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) fe of λ ()

∥-⊓-distrib-R-fwd-on-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → ∀ {r : R × S}
  → ITree.force (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R')) ≡ ret r
  → Σ[ t₂' ∈ ITree E (ExtI I) (R × S) ]
    Σ[ r'  ∈ R × S ]
    ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► t₂'
    × ITree.force t₂' ≡ ret r'
    × r ≡ r' )
∥-⊓-distrib-R-fwd-on-ret {R = R} {S = S} P cs dec Q R' {r = r} eq =
    aux (ITree.force P) refl
  where
    Goal : Set _
    Goal = Σ[ t₂' ∈ ITree E (ExtI _) (R × S) ]
           Σ[ r'  ∈ R × S ]
           ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► t₂'
           × ITree.force t₂' ≡ ret r'
           × r ≡ r' )
    aux : (k : NodeKind E (ExtI _) R)
        → ITree.force P ≡ k
        → Goal
    aux (sil _) eqP =
        case trans (sym (force-∥-sil-L {P = P} cs dec (Q ⊓ R') eqP)) eq of λ ()
    aux (ret _) eqP with force-∥R-ret cs dec Q R' eqP
    ... | _ , _ , force-eq , _ , _ , _ , _ , _ =
        case trans (sym force-eq) eq of λ ()
    aux (vis _) eqP with force-∥R-vis cs dec Q R' eqP
    ... | _ , _ , force-eq , _ , _ , _ , _ , _ =
        case trans (sym force-eq) eq of λ ()
    aux (ndbr _ _ _ _) eqP with force-∥R-ndbr-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) eq of λ ()
    aux (mix _ _) eqP with force-∥R-mix-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) eq of λ ()

∥-⊓-distrib-R-fwd-on-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (Q R' : ITree E (ExtI I) S)
  → ∀ {at : AnyTypes E} {a : proj₁ at}
      {t₁' : ITree E (ExtI I) (R × S)}
  → (P ∥⇘ cs ¿ dec ⇙ (Q ⊓ R'))
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t₁'
  → Σ[ t₂' ∈ ITree E (ExtI I) (R × S) ]
    ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R'))
        ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₂'
    × t₁' ≈ t₂' )
∥-⊓-distrib-R-fwd-on-vis {R = R} {S = S} P cs dec Q R'
    {at = at} {a = a} {t₁' = t₁'} (sVis force-eq _) =
    aux (ITree.force P) refl
  where
    Goal : Set _
    Goal = Σ[ t₂' ∈ ITree E (ExtI _) (R × S) ]
           ( ((P ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ R'))
               ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₂'
           × t₁' ≈ t₂' )
    aux : (k : NodeKind E (ExtI _) R)
        → ITree.force P ≡ k
        → Goal
    aux (sil _) eqP =
        case trans (sym (force-∥-sil-L {P = P} cs dec (Q ⊓ R') eqP)) force-eq of λ ()
    aux (ret _) eqP with force-∥R-ret cs dec Q R' eqP
    ... | _ , _ , force-eq2 , _ , _ , _ , _ , _ =
        case trans (sym force-eq2) force-eq of λ ()
    aux (vis _) eqP with force-∥R-vis cs dec Q R' eqP
    ... | _ , _ , force-eq2 , _ , _ , _ , _ , _ =
        case trans (sym force-eq2) force-eq of λ ()
    aux (ndbr _ _ _ _) eqP with force-∥R-ndbr-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) force-eq of λ ()
    aux (mix _ _) eqP with force-∥R-mix-eq P cs dec Q R' eqP
    ... | _ , _ , _ , _ , feq = case trans (sym feq) force-eq of λ ()
-- sMixVis case: `force LHS ≡ mix …` is impossible — `force (Q⊓R')` is `ndbr`,
-- so the compound's force is `sil` or `ndbr`, never `mix`.
∥-⊓-distrib-R-fwd-on-vis P cs dec Q R' (sMixVis force-eq _) =
  ⊥-elim (force-∥R-notmix P cs dec Q R' force-eq)

∥-⊓-distrib-R P cs dec Q R' .fwd .on-ret eq =
      ∥-⊓-distrib-R-fwd-on-ret P cs dec Q R' eq
∥-⊓-distrib-R P cs dec Q R' .fwd .on-vis step =
      ∥-⊓-distrib-R-fwd-on-vis P cs dec Q R' step
∥-⊓-distrib-R P cs dec Q R' .fwd .on-tau step =
      distrib-R-fwd-on-tau P cs dec Q R' step
∥-⊓-distrib-R P cs dec Q R' .fwd .on-div d
  with ∥-⊓-distrib-R P cs dec Q R' .fwd .on-tau (d .Divergent.step)
... | _ , weak-τ chain , bisim =
      divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))
∥-⊓-distrib-R P cs dec Q R' .bwd .on-ret ()
∥-⊓-distrib-R P cs dec Q R' .bwd .on-vis (sVis () _)
∥-⊓-distrib-R P cs dec Q R' .bwd .on-tau step =
      distrib-R-bwd-on-tau P cs dec Q R' step
∥-⊓-distrib-R P cs dec Q R' .bwd .on-div d
  with ∥-⊓-distrib-R P cs dec Q R' .bwd .on-tau (d .Divergent.step)
... | _ , weak-τ chain , bisim =
      divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L: symmetric to R.  Same structure, with the ⊓ on the
-- left argument of `_∥_`.  This is the real, structured mirror of the R
-- proof.  Notation:  LHS = (P⊓Q) ∥ R',  RHS = (P∥R') ⊓ (Q∥R').
--
-- The proof case-splits the LHS step on `force R'` (the right / non-choice
-- factor) — the mirror of the R proof's split on `force P`.
-----------------------------------------------------------------------------

-- Right-sil absorption.  In the R proof, when the chosen factor is `sil`,
-- the silent step is on the *left* factor, which has reduction priority in
-- `_∥⇘_¿_⇙_` (clause 1), so it is discharged by `force-∥-sil-L` +
-- `sil-τ-refl`.  For L the silent step is on the *right* factor, which has
-- no reduction priority when the left factor `X` is itself `sil`.
--
-- Proof by cases on `force X`:
--   * `force X = sil X'`: the operator's clause 1 strips `X`'s sil first,
--     so `force (X ∥ R') ≡ sil (X' ∥ R')` and `force (X ∥ R'') ≡ sil (X' ∥ R'')`.
--     Bridge `(X∥R') ≈ (X'∥R') ≈ (X'∥R'') ≈ (X∥R'')`, the middle step by a
--     self-recursive appeal on the forced child `X'`.  This recursion walks
--     `X`'s τ-chain, which is unbounded for divergent `X` — hence the
--     `NON_TERMINATING` pragma (same flavour as `distrib-{R,L}-bwd-on-tau`).
--   * `force X ∈ {ret,vis,ndbr,mix}`: clause 1 does not fire, so the right
--     `sil` propagates: `force (X ∥ R') ≡ sil (X ∥ R'')`, closed directly by
--     `sil-τ-refl` with no recursion.
{-# NON_TERMINATING #-}
∥-sil-R-absorb :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (X : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → {R' R'' : ITree E (ExtI I) S}
  → ITree.force R' ≡ sil R''
  → (X ∥⇘ cs ¿ dec ⇙ R') ≈ (X ∥⇘ cs ¿ dec ⇙ R'')
∥-sil-R-absorb X cs dec {R' = R'} {R'' = R''} eqR
  with ITree.force X | inspect ITree.force X
... | sil X' | Eq.[ eqX ] =
      drwbisim-trans
        (sil-τ-refl (force-∥-sil-L cs dec R' eqX))
        (drwbisim-trans
          (∥-sil-R-absorb X' cs dec eqR)
          (drwbisim-sym (sil-τ-refl (force-∥-sil-L cs dec R'' eqX))))
... | ret r | Eq.[ eqX ] = sil-τ-refl (stable eqX eqR)
  where
    stable : ITree.force X ≡ ret r → ITree.force R' ≡ sil R''
           → ITree.force (X ∥⇘ cs ¿ dec ⇙ R') ≡ sil (X ∥⇘ cs ¿ dec ⇙ R'')
    stable e1 e2 with ITree.force X | ITree.force R' | e1 | e2
    ... | ret _ | sil _ | refl | refl = refl
... | vis fX | Eq.[ eqX ] = sil-τ-refl (stable eqX eqR)
  where
    stable : ITree.force X ≡ vis fX → ITree.force R' ≡ sil R''
           → ITree.force (X ∥⇘ cs ¿ dec ⇙ R') ≡ sil (X ∥⇘ cs ¿ dec ⇙ R'')
    stable e1 e2 with ITree.force X | ITree.force R' | e1 | e2
    ... | vis _ | sil _ | refl | refl = refl
... | ndbr fX wi wa wp | Eq.[ eqX ] = sil-τ-refl (stable eqX eqR)
  where
    stable : ITree.force X ≡ ndbr fX wi wa wp → ITree.force R' ≡ sil R''
           → ITree.force (X ∥⇘ cs ¿ dec ⇙ R') ≡ sil (X ∥⇘ cs ¿ dec ⇙ R'')
    stable e1 e2 with ITree.force X | ITree.force R' | e1 | e2
    ... | ndbr _ _ _ _ | sil _ | refl | refl = refl
... | mix fX Xt | Eq.[ eqX ] = sil-τ-refl (stable eqX eqR)
  where
    stable : ITree.force X ≡ mix fX Xt → ITree.force R' ≡ sil R''
           → ITree.force (X ∥⇘ cs ¿ dec ⇙ R') ≡ sil (X ∥⇘ cs ¿ dec ⇙ R'')
    stable e1 e2 with ITree.force X | ITree.force R' | e1 | e2
    ... | mix _ _ | sil _ | refl | refl = refl

-- Residual sub-cases, declared up-front so the on-tau dispatchers can
-- refer to them.  Each is the mirror of the correspondingly-named R
-- postulate (the J-rule paired-branching `ndbr` cases and the `mix`
-- cases), here splitting on `force R'`.
postulate
  -- mirror of `distrib-R-fwd-on-tau-ndbr-J` (force R' = ndbr)
  distrib-L-fwd-on-tau-ndbr-J :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) S))}
      {wiR : AnyTypes (ExtI I)} {waR : proj₁ wiR} {wpR : Is-just (fR wiR waR)}
    → ITree.force R' ≡ ndbr fR wiR waR wpR
    → {t' : ITree E (ExtI I) (R × S)}
    → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ─[ τ ]─► t'
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
        × t' ≈ u' )

  -- mirror of `distrib-R-fwd-on-tau-stable-mix` (force R' = mix)
  distrib-L-fwd-on-tau-stable-mix :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {Rt : ITree E (ExtI I) S}
    → ITree.force R' ≡ mix fR Rt
    → {t' : ITree E (ExtI I) (R × S)}
    → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ─[ τ ]─► t'
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
        × t' ≈ u' )

  -- mirror of `distrib-R-bwd-on-tau-ndbr-J-zero`
  distrib-L-bwd-on-tau-ndbr-J-zero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) S))}
      {wiR : AnyTypes (ExtI I)} {waR : proj₁ wiR} {wpR : Is-just (fR wiR waR)}
    → ITree.force R' ≡ ndbr fR wiR waR wpR
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

  -- mirror of `distrib-R-bwd-on-tau-ndbr-J-suc`
  distrib-L-bwd-on-tau-ndbr-J-suc :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) S))}
      {wiR : AnyTypes (ExtI I)} {waR : proj₁ wiR} {wpR : Is-just (fR wiR waR)}
    → ITree.force R' ≡ ndbr fR wiR waR wpR
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
        × (Q ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

  -- mirror of `distrib-R-bwd-on-tau-stable-mix-fzero`
  distrib-L-bwd-on-tau-stable-mix-fzero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {Rt : ITree E (ExtI I) S}
    → ITree.force R' ≡ mix fR Rt
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
        × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

  -- mirror of `distrib-R-bwd-on-tau-stable-mix-fsucfzero`
  distrib-L-bwd-on-tau-stable-mix-fsucfzero :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    → (P Q : ITree E (ExtI I) R)
    → (cs : AnyTypes E → Set)
    → (dec : (at : AnyTypes E) → Dec (cs at))
    → (R' : ITree E (ExtI I) S)
    → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {Rt : ITree E (ExtI I) S}
    → ITree.force R' ≡ mix fR Rt
    → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
        ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
        × (Q ∥⇘ cs ¿ dec ⇙ R') ≈ u' )

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L sub-lemmas (forward simulation), stable cases.
-- Mirror of `distrib-R-fwd-on-tau-stable-{ret,vis}`.
-----------------------------------------------------------------------------

distrib-L-fwd-on-tau-stable-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {s : S}
  → ITree.force R' ≡ ret s
  → {t' : ITree E (ExtI I) (R × S)}
  → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-L-fwd-on-tau-stable-ret {R = R} {S = S} P Q cs dec R' eqR step
  with force-∥L-ret P Q cs dec eqR | τ-ndbr step
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₁ (u , sil-eq , _)
    = ⊥-elim (case trans (sym force-eq) sil-eq of λ ())
... | f' , pr , force-eq , _ , _ , _ , _ , _
    | inj₂ (inj₂ (g , Qt , mix-eq , _))
    = ⊥-elim (case trans (sym force-eq) mix-eq of λ ())
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₂ (inj₁ (g , wi , wa , prf , i , a , ndbr-eq , j-eq))
    with trans (sym ndbr-eq) force-eq
...   | refl = handle i a j-eq
  where
    maybe-itree : Maybe (ITree E (ExtI _) (R × S)) → ITree E (ExtI _) (R × S)
    maybe-itree (just x) = x
    maybe-itree nothing  = deadlock
    handle :
        (i : AnyTypes (ExtI _)) (a : proj₁ i)
        {t' : ITree E (ExtI _) (R × S)}
        → f' i a ≡ just t'
        → Σ[ u' ∈ ITree E (ExtI _) (R × S) ]
            ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
            × t' ≈ u' )
    handle (_ , base _) _ j-eq =
        ⊥-elim (case trans (sym eq-base) j-eq of λ ())
    handle (_ , pair _ _) _ j-eq =
        ⊥-elim (case trans (sym eq-pair) j-eq of λ ())
    handle (_ , fin {n = zero}) (lift ()) _
    handle (_ , fin {n = suc n}) (lift fzero) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ R') (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc zero}) (lift (fsuc ())) _
    handle (_ , fin {n = suc (suc n)}) (lift (fsuc fzero)) j-eq =
        (Q ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ R') (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (Q ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fsucfzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc (suc (suc n))}) (lift (fsuc (fsuc i))) j-eq =
        ⊥-elim (case trans (sym (eq-fin-big {n = n} {i = i})) j-eq of λ ())

distrib-L-fwd-on-tau-stable-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
  → ITree.force R' ≡ vis fR
  → {t' : ITree E (ExtI I) (R × S)}
  → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-L-fwd-on-tau-stable-vis {R = R} {S = S} P Q cs dec R' eqR step
  with force-∥L-vis P Q cs dec eqR | τ-ndbr step
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₁ (u , sil-eq , _)
    = ⊥-elim (case trans (sym force-eq) sil-eq of λ ())
... | f' , pr , force-eq , _ , _ , _ , _ , _
    | inj₂ (inj₂ (g , Qt , mix-eq , _))
    = ⊥-elim (case trans (sym force-eq) mix-eq of λ ())
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , eq-base , eq-pair , eq-fin-big
    | inj₂ (inj₁ (g , wi , wa , prf , i , a , ndbr-eq , j-eq))
    with trans (sym ndbr-eq) force-eq
...   | refl = handle i a j-eq
  where
    maybe-itree : Maybe (ITree E (ExtI _) (R × S)) → ITree E (ExtI _) (R × S)
    maybe-itree (just x) = x
    maybe-itree nothing  = deadlock
    handle :
        (i : AnyTypes (ExtI _)) (a : proj₁ i)
        {t' : ITree E (ExtI _) (R × S)}
        → f' i a ≡ just t'
        → Σ[ u' ∈ ITree E (ExtI _) (R × S) ]
            ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
            × t' ≈ u' )
    handle (_ , base _) _ j-eq =
        ⊥-elim (case trans (sym eq-base) j-eq of λ ())
    handle (_ , pair _ _) _ j-eq =
        ⊥-elim (case trans (sym eq-pair) j-eq of λ ())
    handle (_ , fin {n = zero}) (lift ()) _
    handle (_ , fin {n = suc n}) (lift fzero) j-eq =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ R') (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (P ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc zero}) (lift (fsuc ())) _
    handle (_ , fin {n = suc (suc n)}) (lift (fsuc fzero)) j-eq =
        (Q ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {f = br2 (P ∥⇘ cs ¿ dec ⇙ R') (Q ∥⇘ cs ¿ dec ⇙ R')}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         refl refl)
                  τ*-zero) ,
        subst (λ x → maybe-itree x ≈ (Q ∥⇘ cs ¿ dec ⇙ R'))
              (trans (sym (eq-fsucfzero {n = n})) j-eq)
              (drwbisim-refl _)
    handle (_ , fin {n = suc (suc (suc n))}) (lift (fsuc (fsuc i))) j-eq =
        ⊥-elim (case trans (sym (eq-fin-big {n = n} {i = i})) j-eq of λ ())

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L: backward-direction stable helpers.
-- Mirror of `distrib-R-bwd-on-tau-stable-{ret,vis}-{fzero,fsucfzero}`.
-----------------------------------------------------------------------------

distrib-L-bwd-on-tau-stable-ret-fzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {s : S}
  → ITree.force R' ≡ ret s
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-L-bwd-on-tau-stable-ret-fzero P Q cs dec R' eqR
  with force-∥L-ret P Q cs dec eqR
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         force-eq (eq-fzero {n = 1}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-L-bwd-on-tau-stable-ret-fsucfzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {s : S}
  → ITree.force R' ≡ ret s
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
      × (Q ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-L-bwd-on-tau-stable-ret-fsucfzero P Q cs dec R' eqR
  with force-∥L-ret P Q cs dec eqR
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (Q ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         force-eq (eq-fsucfzero {n = 0}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-L-bwd-on-tau-stable-vis-fzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
  → ITree.force R' ≡ vis fR
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
      × (P ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-L-bwd-on-tau-stable-vis-fzero P Q cs dec R' eqR
  with force-∥L-vis P Q cs dec eqR
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (P ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                         force-eq (eq-fzero {n = 1}))
                  τ*-zero) ,
        drwbisim-refl _

distrib-L-bwd-on-tau-stable-vis-fsucfzero :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
  → ITree.force R' ≡ vis fR
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
      × (Q ∥⇘ cs ¿ dec ⇙ R') ≈ u' )
distrib-L-bwd-on-tau-stable-vis-fsucfzero P Q cs dec R' eqR
  with force-∥L-vis P Q cs dec eqR
... | f' , pr , force-eq , eq-fzero , eq-fsucfzero , _ , _ , _ =
        (Q ∥⇘ cs ¿ dec ⇙ R') ,
        weak-τ (τ*-step
                  (sNdbr {f = f'}
                         {wi = (Lift ℓ (Fin 2) , fin)} {wa = lift fzero} {prf = pr}
                         {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                         force-eq (eq-fsucfzero {n = 0}))
                  τ*-zero) ,
        drwbisim-refl _

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L: forward on-tau dispatcher.  Mirror of
-- `distrib-R-fwd-on-tau`, dispatching on `force R'`.  The sil case appeals
-- corecursively to `∥-⊓-distrib-L` (guarded), so no pragma is needed.
-----------------------------------------------------------------------------
distrib-L-fwd-on-tau :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {t' : ITree E (ExtI I) (R × S)}
  → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► u'
      × t' ≈ u' )
distrib-L-fwd-on-tau P Q cs dec R' step
  with ITree.force R' | inspect ITree.force R'
... | sil R'' | Eq.[ eqR ] with step
...   | sSil force-eq
      with sil-injective (trans (sym force-eq) (force-∥-sil-R P Q cs dec eqR))
...     | refl =
            ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ,
            weak-τ τ*-zero ,
            drwbisim-trans
              (∥-⊓-distrib-L P Q cs dec R'')
              (⊓-cong (drwbisim-sym (∥-sil-R-absorb P cs dec eqR))
                      (drwbisim-sym (∥-sil-R-absorb Q cs dec eqR)))
distrib-L-fwd-on-tau P Q cs dec R' _
  | sil _ | Eq.[ eqR ] | sNdbr force-ndbr _ =
      case trans (sym (force-∥-sil-R P Q cs dec eqR)) force-ndbr of λ ()
distrib-L-fwd-on-tau P Q cs dec R' _
  | sil _ | Eq.[ eqR ] | sMixSlide force-mix =
      case trans (sym (force-∥-sil-R P Q cs dec eqR)) force-mix of λ ()
distrib-L-fwd-on-tau P Q cs dec R' step
  | ret s | Eq.[ eqR ] = distrib-L-fwd-on-tau-stable-ret P Q cs dec R' eqR step
distrib-L-fwd-on-tau P Q cs dec R' step
  | vis fR | Eq.[ eqR ] = distrib-L-fwd-on-tau-stable-vis P Q cs dec R' eqR step
distrib-L-fwd-on-tau P Q cs dec R' step
  | ndbr fR wiR waR wpR | Eq.[ eqR ] = distrib-L-fwd-on-tau-ndbr-J P Q cs dec R' eqR step
distrib-L-fwd-on-tau P Q cs dec R' step
  | mix fR Rt | Eq.[ eqR ] = distrib-L-fwd-on-tau-stable-mix P Q cs dec R' eqR step

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L: backward on-tau dispatcher.  Mirror of
-- `distrib-R-bwd-on-tau`.  Marked `NON_TERMINATING` for the sil
-- self-recursion (mirror of R's pragma).
-----------------------------------------------------------------------------
{-# NON_TERMINATING #-}
distrib-L-bwd-on-tau :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {t' : ITree E (ExtI I) (R × S)}
  → ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ─[ τ ]─► t'
  → Σ[ u' ∈ ITree E (ExtI I) (R × S) ]
      ( ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ═[ τ ]═► u'
      × t' ≈ u' )
distrib-L-bwd-on-tau P Q cs dec R' (sSil ())
distrib-L-bwd-on-tau P Q cs dec R' (sNdbr {i = (_ , base _)}   refl ())
distrib-L-bwd-on-tau P Q cs dec R' (sNdbr {i = (_ , pair _ _)} refl ())
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  with ITree.force R' | inspect ITree.force R'
... | sil R'' | Eq.[ eqR ]
    with distrib-L-bwd-on-tau P Q cs dec R''
           (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R'') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R'')}
                  {f = br2 (P ∥⇘ cs ¿ dec ⇙ R'') (Q ∥⇘ cs ¿ dec ⇙ R'')}
                  {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                  refl refl)
... | u'' , weak-τ chain , bisim =
        u'' ,
        weak-τ (τ*-step (sSil (force-∥-sil-R P Q cs dec eqR)) chain) ,
        drwbisim-trans
          (∥-sil-R-absorb P cs dec eqR)
          bisim
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | ret s | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-ret-fzero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | vis _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-vis-fzero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | ndbr _ _ _ _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-ndbr-J-zero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl)
  | mix _ _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-mix-fzero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  with ITree.force R' | inspect ITree.force R'
... | sil R'' | Eq.[ eqR ]
    with distrib-L-bwd-on-tau P Q cs dec R''
           (sNdbr {p = (P ∥⇘ cs ¿ dec ⇙ R'') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R'')}
                  {f = br2 (P ∥⇘ cs ¿ dec ⇙ R'') (Q ∥⇘ cs ¿ dec ⇙ R'')}
                  {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                  refl refl)
... | u'' , weak-τ chain , bisim =
        u'' ,
        weak-τ (τ*-step (sSil (force-∥-sil-R P Q cs dec eqR)) chain) ,
        drwbisim-trans
          (∥-sil-R-absorb Q cs dec eqR)
          bisim
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | ret s | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-ret-fsucfzero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | vis _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-vis-fsucfzero P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | ndbr _ _ _ _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-ndbr-J-suc P Q cs dec R' eqR
distrib-L-bwd-on-tau P Q cs dec R'
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl)
  | mix _ _ | Eq.[ eqR ] =
      distrib-L-bwd-on-tau-stable-mix-fsucfzero P Q cs dec R' eqR

-----------------------------------------------------------------------------
-- ∥-⊓-distrib-L: on-ret / on-vis forward.  Mirror of
-- `∥-⊓-distrib-R-fwd-on-{ret,vis}`: `force LHS` is never `ret`/`vis`
-- (always `sil` when `force R' = sil`, or `ndbr` when `force R' = ret/vis`).
-----------------------------------------------------------------------------

-- Head-unfolding lemmas for L (mirror of `force-∥R-{ndbr,mix}-eq`).  When
-- `force R'` is `ndbr`/`mix`, the operator's ndbr/ndbr (resp. ndbr/mix)
-- clause fires — `force (P⊓Q)` is always `ndbr` — so `force ((P⊓Q) ∥ R')`
-- is `ndbr`-headed.  (`R'` is the matched operand; destructure its witness.)
force-∥L-ndbr-eq :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {fR : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) S))}
    {wiR : AnyTypes (ExtI I)} {waR : proj₁ wiR} {wpR : Is-just (fR wiR waR)}
  → ITree.force R' ≡ ndbr fR wiR waR wpR
  → Σ[ g ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ wi ∈ AnyTypes (ExtI I) ] Σ[ wa ∈ proj₁ wi ] Σ[ pr ∈ Is-just (g wi wa) ]
      ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡ ndbr g wi wa pr
force-∥L-ndbr-eq P Q cs dec R' eqR with ITree.force R' | eqR
... | ndbr _ (_ , _) _ _ | refl = _ , _ , _ , _ , refl

force-∥L-mix-eq :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
    {Rt : ITree E (ExtI I) S}
  → ITree.force R' ≡ mix fR Rt
  → Σ[ g ∈ ((i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))) ]
    Σ[ wi ∈ AnyTypes (ExtI I) ] Σ[ wa ∈ proj₁ wi ] Σ[ pr ∈ Is-just (g wi wa) ]
      ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡ ndbr g wi wa pr
force-∥L-mix-eq P Q cs dec R' eqR with ITree.force R' | eqR
... | mix _ _ | refl = _ , _ , _ , _ , refl

-- `force ((P⊓Q) ∥ R')` is never `mix`-headed: case on `force R'`.
force-∥L-notmix :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
    {Qt : ITree E (ExtI I) (R × S)}
  → ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡ mix f Qt
  → ⊥
force-∥L-notmix P Q cs dec R' fe = aux (ITree.force R') refl
  where
    aux : (k : NodeKind E (ExtI _) _) → ITree.force R' ≡ k → ⊥
    aux (sil _) eqR =
        case trans (sym (force-∥-sil-R P Q cs dec eqR)) fe of λ ()
    aux (ret _) eqR with force-∥L-ret P Q cs dec eqR
    ... | _ , _ , feq , _ = case trans (sym feq) fe of λ ()
    aux (vis _) eqR with force-∥L-vis P Q cs dec eqR
    ... | _ , _ , feq , _ = case trans (sym feq) fe of λ ()
    aux (ndbr _ _ _ _) eqR with force-∥L-ndbr-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) fe of λ ()
    aux (mix _ _) eqR with force-∥L-mix-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) fe of λ ()

∥-⊓-distrib-L-fwd-on-ret :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → ∀ {r : R × S}
  → ITree.force ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R') ≡ ret r
  → Σ[ t₂' ∈ ITree E (ExtI I) (R × S) ]
    Σ[ r'  ∈ R × S ]
    ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► t₂'
    × ITree.force t₂' ≡ ret r'
    × r ≡ r' )
∥-⊓-distrib-L-fwd-on-ret {R = R} {S = S} P Q cs dec R' {r = r} eq =
    aux (ITree.force R') refl
  where
    Goal : Set _
    Goal = Σ[ t₂' ∈ ITree E (ExtI _) (R × S) ]
           Σ[ r'  ∈ R × S ]
           ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R')) ═[ τ ]═► t₂'
           × ITree.force t₂' ≡ ret r'
           × r ≡ r' )
    aux : (k : NodeKind E (ExtI _) S)
        → ITree.force R' ≡ k
        → Goal
    aux (sil _) eqR =
        case trans (sym (force-∥-sil-R P Q cs dec eqR)) eq of λ ()
    aux (ret _) eqR with force-∥L-ret P Q cs dec eqR
    ... | _ , _ , force-eq , _ , _ , _ , _ , _ =
        case trans (sym force-eq) eq of λ ()
    aux (vis _) eqR with force-∥L-vis P Q cs dec eqR
    ... | _ , _ , force-eq , _ , _ , _ , _ , _ =
        case trans (sym force-eq) eq of λ ()
    aux (ndbr _ _ _ _) eqR with force-∥L-ndbr-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) eq of λ ()
    aux (mix _ _) eqR with force-∥L-mix-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) eq of λ ()

∥-⊓-distrib-L-fwd-on-vis :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → (P Q : ITree E (ExtI I) R)
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → (R' : ITree E (ExtI I) S)
  → ∀ {at : AnyTypes E} {a : proj₁ at}
      {t₁' : ITree E (ExtI I) (R × S)}
  → ((P ⊓ Q) ∥⇘ cs ¿ dec ⇙ R')
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t₁'
  → Σ[ t₂' ∈ ITree E (ExtI I) (R × S) ]
    ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R'))
        ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₂'
    × t₁' ≈ t₂' )
∥-⊓-distrib-L-fwd-on-vis {R = R} {S = S} P Q cs dec R'
    {at = at} {a = a} {t₁' = t₁'} (sVis force-eq _) =
    aux (ITree.force R') refl
  where
    Goal : Set _
    Goal = Σ[ t₂' ∈ ITree E (ExtI _) (R × S) ]
           ( ((P ∥⇘ cs ¿ dec ⇙ R') ⊓ (Q ∥⇘ cs ¿ dec ⇙ R'))
               ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₂'
           × t₁' ≈ t₂' )
    aux : (k : NodeKind E (ExtI _) S)
        → ITree.force R' ≡ k
        → Goal
    aux (sil _) eqR =
        case trans (sym (force-∥-sil-R P Q cs dec eqR)) force-eq of λ ()
    aux (ret _) eqR with force-∥L-ret P Q cs dec eqR
    ... | _ , _ , force-eq2 , _ , _ , _ , _ , _ =
        case trans (sym force-eq2) force-eq of λ ()
    aux (vis _) eqR with force-∥L-vis P Q cs dec eqR
    ... | _ , _ , force-eq2 , _ , _ , _ , _ , _ =
        case trans (sym force-eq2) force-eq of λ ()
    aux (ndbr _ _ _ _) eqR with force-∥L-ndbr-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) force-eq of λ ()
    aux (mix _ _) eqR with force-∥L-mix-eq P Q cs dec R' eqR
    ... | _ , _ , _ , _ , feq = case trans (sym feq) force-eq of λ ()
∥-⊓-distrib-L-fwd-on-vis P Q cs dec R' (sMixVis force-eq _) =
  ⊥-elim (force-∥L-notmix P Q cs dec R' force-eq)

-----------------------------------------------------------------------------
-- Assembly of `∥-⊓-distrib-L`.
-----------------------------------------------------------------------------
∥-⊓-distrib-L P Q cs dec R' .fwd .on-ret eq =
      ∥-⊓-distrib-L-fwd-on-ret P Q cs dec R' eq
∥-⊓-distrib-L P Q cs dec R' .fwd .on-vis step =
      ∥-⊓-distrib-L-fwd-on-vis P Q cs dec R' step
∥-⊓-distrib-L P Q cs dec R' .fwd .on-tau step =
      distrib-L-fwd-on-tau P Q cs dec R' step
∥-⊓-distrib-L P Q cs dec R' .fwd .on-div d
  with ∥-⊓-distrib-L P Q cs dec R' .fwd .on-tau (d .Divergent.step)
... | _ , weak-τ chain , bisim =
      divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))
∥-⊓-distrib-L P Q cs dec R' .bwd .on-ret ()
∥-⊓-distrib-L P Q cs dec R' .bwd .on-vis (sVis () _)
∥-⊓-distrib-L P Q cs dec R' .bwd .on-tau step =
      distrib-L-bwd-on-tau P Q cs dec R' step
∥-⊓-distrib-L P Q cs dec R' .bwd .on-div d
  with ∥-⊓-distrib-L P Q cs dec R' .bwd .on-tau (d .Divergent.step)
... | _ , weak-τ chain , bisim =
      divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-----------------------------------------------------------------------------------------
-- Interleave-reach-aux / Interleave-reach (state-closure law for P ⦀ Q)
-----------------------------------------------------------------------------------------

-- Shared reconstruction lemmas for Interleave-reach-aux.
--
-- Every recursive clause takes the split of a sub-component and prepends a single
-- LTS step to one (or both) side(s).  Pulling the per-constructor reconstruction out
-- into these lemmas means the (heavily-indexed) re-packing of `ParInterleaveSplit` is
-- elaborated once here rather than inlined at every clause.  The τ lemmas serve the
-- sSil / sNdbr / sMixSlide groups; the visible lemmas serve the sVis / sMixVis groups
-- (abstract over the single visible step, so one lemma covers both sVis and sMixVis).
private
  -- Common params: P, Q, t′, s.  The sub-component (P′ / Q′) and the visible event
  -- ev0 are quantified per-lemma so every implicit is constrained by that lemma's
  -- arguments (a shared P′/Q′ would be unconstrained in the one-sided lemmas).
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
           {t′ : ITree E (ExtI I) (R × S)} {s : List (Event√ E (R × S))} where

    extend-P-τ : ∀ {P′} → P ─[ τ ]─► P′ → ParInterleaveSplit P′ Q t′ s → ParInterleaveSplit P Q t′ s
    extend-P-τ st (in-progress merge trP trQ)           = in-progress merge (bTau st trP) trQ
    extend-P-τ st (collision intlv bsP bsQ stepP stepQ) = collision intlv (bTau st bsP) bsQ stepP stepQ
    extend-P-τ st (done merge trP trQ)                  = done merge (bTau st trP) trQ

    extend-Q-τ : ∀ {Q′} → Q ─[ τ ]─► Q′ → ParInterleaveSplit P Q′ t′ s → ParInterleaveSplit P Q t′ s
    extend-Q-τ st (in-progress merge trP trQ)           = in-progress merge trP (bTau st trQ)
    extend-Q-τ st (collision intlv bsP bsQ stepP stepQ) = collision intlv bsP (bTau st bsQ) stepP stepQ
    extend-Q-τ st (done merge trP trQ)                  = done merge trP (bTau st trQ)

    extend-both-τ : ∀ {P′ Q′} → P ─[ τ ]─► P′ → Q ─[ τ ]─► Q′
                  → ParInterleaveSplit P′ Q′ t′ s → ParInterleaveSplit P Q t′ s
    extend-both-τ stP stQ (in-progress merge trP trQ)           = in-progress merge (bTau stP trP) (bTau stQ trQ)
    extend-both-τ stP stQ (collision intlv bsP bsQ stepP stepQ) = collision intlv (bTau stP bsP) (bTau stQ bsQ) stepP stepQ
    extend-both-τ stP stQ (done merge trP trQ)                  = done merge (bTau stP trP) (bTau stQ trQ)

    extend-P-vis : ∀ {P′ ev0} → P ─[ ev (evl ev0) ]─► P′
                 → ParInterleaveSplit P′ Q t′ s → ParInterleaveSplit P Q t′ (evl ev0 ∷ s)
    extend-P-vis st (in-progress merge trP trQ)           = in-progress (int-l merge) (bStep st trP) trQ
    extend-P-vis st (collision intlv bsP bsQ stepP stepQ) = collision (int-l intlv) (bStep st bsP) bsQ stepP stepQ
    extend-P-vis st (done merge trP trQ)                  = done (int-l merge) (bStep st trP) trQ

    extend-Q-vis : ∀ {Q′ ev0} → Q ─[ ev (evl ev0) ]─► Q′
                 → ParInterleaveSplit P Q′ t′ s → ParInterleaveSplit P Q t′ (evl ev0 ∷ s)
    extend-Q-vis st (in-progress merge trP trQ)           = in-progress (int-r merge) trP (bStep st trQ)
    extend-Q-vis st (collision intlv bsP bsQ stepP stepQ) = collision (int-r intlv) bsP (bStep st bsQ) stepP stepQ
    extend-Q-vis st (done merge trP trQ)                  = done (int-r merge) trP (bStep st trQ)

Interleave-reach-aux : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_⦀_ {I = I} {R = R} {S = S} P Q) ═⟨ s ⟩═► t′
  → ParInterleaveSplit P Q t′ s

-- 1. Empty trace
Interleave-reach-aux P Q bNil =
  in-progress int-nil bNil bNil

-- 2. Tau via sSil — exactly one of P, Q has a sil head
Interleave-reach-aux P Q (bTau (sSil {t = next} eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | sil P' | _ | refl =
    extend-P-τ (sSil p-eq) (Interleave-reach-aux P' Q big-step)
... | ret _ | sil Q' | refl =
    extend-Q-τ (sSil q-eq) (Interleave-reach-aux P Q' big-step)
... | vis _ | sil Q' | refl =
    extend-Q-τ (sSil q-eq) (Interleave-reach-aux P Q' big-step)
... | ndbr _ _ _ _ | sil Q' | refl =
    extend-Q-τ (sSil q-eq) (Interleave-reach-aux P Q' big-step)
... | mix _ _ | sil Q' | refl =
    extend-Q-τ (sSil q-eq) (Interleave-reach-aux P Q' big-step)
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

-- 3. Visible step via sVis — comes from a vis head in the merge
Interleave-reach-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- (a) vis | ret : P moves alone
... | vis fP | ret _ | refl with fP at a in fp-eq | eq-j
... | just P' | refl =
    extend-P-vis (sVis p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
... | nothing | ()

-- (b) ret | vis : Q moves alone
Interleave-reach-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | ret _ | vis fQ | refl with fQ at a in fq-eq | eq-j
... | just Q' | refl =
    extend-Q-vis (sVis q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
... | nothing | ()

-- (c) vis | vis : four sub-cases, one of which is the internal-choice case
Interleave-reach-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts
... | just P' | nothing | refl =
    extend-P-vis (sVis p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
-- only Q accepts
... | nothing | just Q' | refl =
    extend-Q-vis (sVis q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
-- both accept: continuation is ⦀-choice P' Q P Q'; collision when the trace stops here
... | just P' | just Q' | refl with big-step
-- inner trace empty: outer trace is just [at]; this is the collision node
... | bNil =
    collision int-nil bNil bNil (sVis p-eq fp-eq) (sVis q-eq fq-eq)
-- internal-choice picks a branch via sNdbr
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    extend-P-vis (sVis p-eq fp-eq) (Interleave-reach-aux P' Q inner-bs)
Interleave-reach-aux P Q (bStep (sVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    extend-Q-vis (sVis q-eq fq-eq) (Interleave-reach-aux P Q' inner-bs)
-- other internal-choice indices: br2 returns nothing → eq-int-j absurd
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
-- force (⦀-choice …) is ndbr, so sSil/sVis/sRet first steps are impossible
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bTau (sSil ()) _
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bStep (sVis () _) _
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | just P' | just Q' | refl
  | bStep (sRet ()) _
-- neither accepts: merge yields nothing → eq-j impossible
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step)
  | vis fP | vis fQ | refl | nothing | nothing | ()

-- (d) absurd head combinations for sVis
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | vis _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 4. Termination via sRet — only when both P and Q are at ret simultaneously
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
... | ret rP | ret rQ | refl with big-step
...   | bNil =
        done int-nil (bStep (sRet p-eq) bNil) (bStep (sRet q-eq) bNil)
...   | bTau (sSil ()) _
...   | bTau (sNdbr () _) _
...   | bStep (sRet ()) _
...   | bStep (sVis refl ()) _
-- absurd head combinations for sRet
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | sil _ | _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ret _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ret _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | vis _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | vis _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | vis _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | mix _ _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ret _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | vis _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sRet eq-f) big-step) | ndbr _ _ _ _ | mix _ _ | ()

-- 5. Tau via sNdbr — at least one of P, Q has an ndbr head
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f

-- (a) ret | ndbr : Q moves alone (Q-distribution)
... | ret _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
... | nothing | ()

-- (b) vis | ndbr : Q moves alone (Q-distribution)
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | vis _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
... | nothing | ()

-- (c) ndbr | ret : P moves alone (P-distribution)
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    extend-P-τ (sNdbr p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
... | nothing | ()

-- (d) ndbr | vis : P moves alone (P-distribution)
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    extend-P-τ (sNdbr p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
... | nothing | ()

-- (e) ndbr | ndbr : both ndbr; merge ranges over pair indices
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ | refl
  with i | a
... | (_ , base _) | _ = case eq-j of λ ()
... | (_ , fin)    | _ = case eq-j of λ ()
... | (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ') | (aP' , aQ')
  with fP (AP' , iP') aP' in fp'-eq | fQ (AQ' , iQ') aQ' in fq'-eq | eq-j
-- only P accepts → continuation (P' ⦀ Q)
... | just P' | nothing | refl =
    extend-P-τ (sNdbr p-eq fp'-eq) (Interleave-reach-aux P' Q big-step)
-- only Q accepts → continuation (P ⦀ Q')
... | nothing | just Q' | refl =
    extend-Q-τ (sNdbr q-eq fq'-eq) (Interleave-reach-aux P Q' big-step)
-- both accept → continuation (P' ⦀ Q'); add τ on BOTH sides
... | just P' | just Q' | refl =
    extend-both-τ (sNdbr p-eq fp'-eq) (sNdbr q-eq fq'-eq) (Interleave-reach-aux P' Q' big-step)
... | nothing | nothing | ()

-- (f) absurd head combinations for sNdbr
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | vis _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | ret _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | vis _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()

-- (g) mix | ndbr — Q does ndbr-distribution
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | mix _ _ | ndbr fQ wi wa wp | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    extend-Q-τ (sNdbr q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
... | nothing | ()

-- (h) ndbr | mix — P does ndbr-distribution
Interleave-reach-aux P Q (bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  | ndbr fP wi wa wp | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    extend-P-τ (sNdbr p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
... | nothing | ()

-- (i) mix-shape absurds for sNdbr
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | ret _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | vis _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | mix _ _ | mix _ _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | ret _ | mix _ _ | ()
Interleave-reach-aux P Q (bTau (sNdbr eq-f eq-j) big-step) | vis _ | mix _ _ | ()

-- ----- 6. bTau via sMixSlide. force (P ⦀ Q) ≡ mix _ Qt; slide goes to Qt. -----
Interleave-reach-aux P Q (bTau (sMixSlide eq-f) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix fQ Q': Q slides.
... | ret _ | mix _ Q' | refl =
    extend-Q-τ (sMixSlide q-eq) (Interleave-reach-aux P Q' big-step)
-- vis | mix: Q slides.
... | vis _ | mix _ Q' | refl =
    extend-Q-τ (sMixSlide q-eq) (Interleave-reach-aux P Q' big-step)
-- mix | ret: P slides.
... | mix _ P' | ret _ | refl =
    extend-P-τ (sMixSlide p-eq) (Interleave-reach-aux P' Q big-step)
-- mix | vis: P slides.
... | mix _ P' | vis _ | refl =
    extend-P-τ (sMixSlide p-eq) (Interleave-reach-aux P' Q big-step)
-- mix | mix: both slide simultaneously to (P' ⦀ Q').
... | mix _ P' | mix _ Q' | refl =
    extend-both-τ (sMixSlide p-eq) (sMixSlide q-eq) (Interleave-reach-aux P' Q' big-step)
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

-- ----- 7. bStep via sMixVis. force (P ⦀ Q) ≡ mix f Qt, f at a ≡ just t'. -----
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  with P .force in p-eq | Q .force in q-eq | eq-f
-- ret | mix fQ _: Q's vis-side fires.
... | ret _ | mix fQ _ | refl with fQ at a in fq-eq | eq-j
... | just _  | refl =
    extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-reach-aux P _ big-step)
... | nothing | ()
-- vis | mix: merged vis-function of fP and fQ.
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P' ⦀ Q. P side fires a vis step.
... | just P' | nothing | refl =
    extend-P-vis (sVis p-eq fp-eq) (Interleave-reach-aux P' Q big-step)
-- only Q accepts: t' = P ⦀ Q''. Q side fires an sMixVis step.
... | nothing | just Q'' | refl =
    extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-reach-aux P Q'' big-step)
-- both accept: internal nondeterministic choice between (P' ⦀ Q) and (P ⦀ Q'').
... | just P' | just Q'' | refl with big-step
-- bNil: empty trace; residual is the inline mix-collision ndbr node.
... | bNil =
    collision int-nil bNil bNil (sVis p-eq fp-eq) (sMixVis q-eq fq-eq)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    extend-P-vis (sVis p-eq fp-eq) (Interleave-reach-aux P' Q inner-bs)
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-reach-aux P Q'' inner-bs)
-- other inner-ndbr indices yield nothing, so eq-int-j is absurd
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sSil ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bTau (sMixSlide ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sRet ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | just P' | just Q'' | refl
  | bStep (sMixVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | vis fP | mix fQ _ | refl | nothing | nothing | ()
-- mix | ret: P's vis-side fires.
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | ret _ | refl with fP at a in fp-eq | eq-j
... | just _ | refl =
    extend-P-vis (sMixVis p-eq fp-eq) (Interleave-reach-aux _ Q big-step)
... | nothing | ()
-- mix | vis: symmetric to vis|mix — P fires via sMixVis, Q via sVis.
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P'' ⦀ Q. P side fires sMixVis.
... | just P'' | nothing | refl =
    extend-P-vis (sMixVis p-eq fp-eq) (Interleave-reach-aux P'' Q big-step)
-- only Q accepts: t' = P ⦀ Q'. Q side fires sVis.
... | nothing | just Q' | refl =
    extend-Q-vis (sVis q-eq fq-eq) (Interleave-reach-aux P Q' big-step)
-- both accept: internal choice between (P'' ⦀ Q) and (P ⦀ Q').
... | just P'' | just Q' | refl with big-step
... | bNil =
    collision int-nil bNil bNil (sMixVis p-eq fp-eq) (sVis q-eq fq-eq)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    extend-P-vis (sMixVis p-eq fp-eq) (Interleave-reach-aux P'' Q inner-bs)
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    extend-Q-vis (sVis q-eq fq-eq) (Interleave-reach-aux P Q' inner-bs)
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sSil ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bTau (sMixSlide ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sRet ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | just P'' | just Q' | refl
  | bStep (sMixVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | vis fQ | refl | nothing | nothing | ()
-- mix | mix: full merge of vis functions.
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl
  with fP at a in fp-eq | fQ at a in fq-eq | eq-j
-- only P accepts: t' = P'' ⦀ Q
... | just P'' | nothing | refl =
    extend-P-vis (sMixVis p-eq fp-eq) (Interleave-reach-aux P'' Q big-step)
-- only Q accepts: t' = P ⦀ Q''
... | nothing | just Q'' | refl =
    extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-reach-aux P Q'' big-step)
-- both accept: internal ndbr between (P'' ⦀ Q) and (P ⦀ Q'').
... | just P'' | just Q'' | refl with big-step
... | bNil =
    collision int-nil bNil bNil (sMixVis p-eq fp-eq) (sMixVis q-eq fq-eq)
... | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
    with i-int | a-int | eq-int
... | (_ , fin) | lift fzero | refl with eq-int-j
... | refl =
    extend-P-vis (sMixVis p-eq fp-eq) (Interleave-reach-aux P'' Q inner-bs)
Interleave-reach-aux P Q (bStep (sMixVis {at = at} {a = a} eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr {i = i-int} {a = a-int} eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc fzero) | refl with eq-int-j
... | refl =
    extend-Q-vis (sMixVis q-eq fq-eq) (Interleave-reach-aux P Q'' inner-bs)
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , fin) | lift (fsuc (fsuc _)) | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , base _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sNdbr eq-int eq-int-j) inner-bs
  | (_ , pair _ _) | _ | refl = case eq-int-j of λ ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sSil ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bTau (sMixSlide ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sRet ()) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | just P'' | just Q'' | refl
  | bStep (sMixVis () _) _
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step)
  | mix fP _ | mix fQ _ | refl | nothing | nothing | ()
-- Absurd: non-mix shapes.
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | sil _ | _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ret _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | vis _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ret _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | vis _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | ndbr _ _ _ _ | mix _ _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | sil _ | ()
Interleave-reach-aux P Q (bStep (sMixVis eq-f eq-j) big-step) | mix _ _ | ndbr _ _ _ _ | ()

Interleave-reach : ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
  {s : List (Event√ E (R × S))} {t′ : ITree E (ExtI I) (R × S)}
  → (_⦀_ {I = I} {R = R} {S = S} P Q) ═⟨ s ⟩═► t′
  → ParInterleaveSplit P Q t′ s
Interleave-reach P Q bs = Interleave-reach-aux P Q bs

private
  -- Sanity (in-progress): the empty trace decomposes to both components at
  -- their start states, with the empty interleave merge.  Mirrors the sibling
  -- `Parallel-reach` bNil sanity check above.
  module _ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
           (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S) where
    _ : ParInterleaveSplit P Q (P ⦀ Q) []
    _ = Interleave-reach P Q bNil

  -- Non-vacuity of the `collision` constructor.
  --
  -- The `collision` case requires a CONCRETE event `e₀` that BOTH components
  -- offer from their reached states, e.g. `P0 = e₀ ⟶ k` and `Q0 = e₀ ⟶ k`
  -- with the single visible step `bStep (sVis refl refl) bNil` reaching the
  -- `⦀-choice P′ Qc Pc Q′` node.  This module is parametrised by an ABSTRACT
  -- event signature `E` (module parameter, line 49), so no concrete event /
  -- `Prefix` is constructible here — the local check cannot be written.
  --
  -- The non-vacuity was instead verified dynamically by the spec-reviewer over
  -- the concrete `E = IO` from `CSP/Examples/IO/IO.agda`:
  --
  --   Interleave-reach P0 Q0 (bStep (sVis refl refl) bNil)
  --     ≡ collision int-nil bNil bNil (sVis refl refl) (sVis refl refl)
  --
  -- typechecked (by `refl`), confirming the `collision` constructor is reachable
  -- and not dead code.  Step skipped here only because of the abstract `E`.
