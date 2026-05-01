{-
  Internal-choice laws for ITree-CSP under failures-divergences
  equivalence `_≃FD_` from `ITree_Relations.FailuresDivergencesEquiv`.

  Specifically:

      ⊓-assoc-FD :  ((P ⊓ Q) ⊓ R)  ≃FD  (P ⊓ (Q ⊓ R))

  This law fails under DRWbisim — see the commented-out statement in
  `CSP.Laws.InternalChoice_DRBisim` — but holds in the FD model because
  both processes have the same set of τ*-reachable derivatives `{P,Q,R}`,
  and the FD model only observes that set (via `failures⊥` and
  `divergences`).

  Strategy.  Prove that failures and divergences of `(P ⊓ Q)` decompose
  as `failures/divergences` of P  ⊎  `failures/divergences` of Q.
  Associativity then follows from associativity of `_⊎_` on these sets.
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; sym; trans; cong)

open import Class.DecEq using (DecEq; _≟_)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open import ITree_Relations.DRWeakBisim
open import ITree_Relations.FailuresDivergencesEquiv

module CSP.Laws.InternalChoice_FD
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open ITree
open Label
open Event√
open Failures
open IsDivergence

-----------------------------------------------------------------------------
-- Step lemmas: P ⊓ Q always τ-reaches its two operands directly.
-----------------------------------------------------------------------------

⊓-step-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (P Q : ITree E (ExtI I) R) → (P ⊓ Q) ─[ τ ]─► P
⊓-step-L P Q = sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl

⊓-step-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (P Q : ITree E (ExtI I) R) → (P ⊓ Q) ─[ τ ]─► Q
⊓-step-R P Q = sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl

-----------------------------------------------------------------------------
-- failures decomposes as a sum: failures (P ⊓ Q) = failures P ⊎ failures Q.
-----------------------------------------------------------------------------

-- Intro-L: prepend a τ-step from `P ⊓ Q` to `P` in front of any failure
-- of P; the visible-label list `s` is unchanged because the prepended
-- step is `bTau`.
⊓-failures-introL :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures P s B → failures (P ⊓ Q) s B
⊓-failures-introL {P = P} {Q = Q} (T , bigstep , refusal) =
  T , bTau (⊓-step-L P Q) bigstep , refusal

⊓-failures-introR :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures Q s B → failures (P ⊓ Q) s B
⊓-failures-introR {P = P} {Q = Q} (T , bigstep , refusal) =
  T , bTau (⊓-step-R P Q) bigstep , refusal

-- Elim: invert a failure of P ⊓ Q.  The trace must take a τ-step out of
-- P ⊓ Q first (force = ndbr admits no `bNil` witness for refusal and no
-- `bStep`/sVis/sRet step).  The τ-step picks a `br2`-branch leading to
-- P (lift fzero) or Q (lift (fsuc fzero)); other branches yield
-- `nothing` and are absurd.
⊓-failures-elim :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures (P ⊓ Q) s B
  → failures P s B ⊎ failures Q s B
⊓-failures-elim {P = P} {Q = Q} {B = B} (T , bigstep , refusal) =
    go bigstep refusal
  where
    go : ∀ {s} → (P ⊓ Q) ═⟨ s ⟩═► T → T ref B
       → failures P s B ⊎ failures Q s B
    -- bNil : T = P ⊓ Q.  Refusal of an ndbr-shaped tree is impossible:
    -- ref-stable needs `isStable (P ⊓ Q)` (= ⊥), ref-tick needs
    -- `force (P ⊓ Q) ≡ ret _` (it is `ndbr _`).
    go bNil (ref-stable () _)
    go bNil (ref-tick (sRet ()) _)
    -- bTau: τ from P ⊓ Q is sNdbr (force is ndbr, sSil absurd).
    go (bTau (sSil ()) _) _
    go (bTau (sNdbr {i = (_ , base _)}   refl ()) _) _
    go (bTau (sNdbr {i = (_ , pair _ _)} refl ()) _) _
    go (bTau (sNdbr {i = (_ , fin)} {a = lift fzero}        refl refl) rest) ref =
        inj₁ (T , rest , ref)
    go (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) rest) ref =
        inj₂ (T , rest , ref)
    go (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ()) _) _
    -- bStep: ev from P ⊓ Q is impossible (force is ndbr).
    go (bStep (sRet ())   _) _
    go (bStep (sVis () _) _) _

-----------------------------------------------------------------------------
-- divergences decomposes as a sum:
--   divergences (P ⊓ Q) = divergences P ⊎ divergences Q.
-----------------------------------------------------------------------------

⊓-divergences-introL :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences P s → divergences (P ⊓ Q) s
⊓-divergences-introL {P = P} {Q = Q} d = record
  { prefix  = d .prefix
  ; suffix  = d .suffix
  ; split   = d .split
  ; witness = d .witness
  ; reach   = bTau (⊓-step-L P Q) (d .reach)
  ; divwit  = d .divwit
  }

⊓-divergences-introR :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences Q s → divergences (P ⊓ Q) s
⊓-divergences-introR {P = P} {Q = Q} d = record
  { prefix  = d .prefix
  ; suffix  = d .suffix
  ; split   = d .split
  ; witness = d .witness
  ; reach   = bTau (⊓-step-R P Q) (d .reach)
  ; divwit  = d .divwit
  }

-- Elim for divergences.  The reach `(P ⊓ Q) ═⟨ pre ⟩═► witness` either
-- starts with a τ-step into P/Q (bTau) — re-anchor the trace at P or Q —
-- or is `bNil` with `witness = P ⊓ Q`, in which case the divergent
-- witness's first τ-step lands at P or Q and we re-anchor on that.
⊓-divergences-elim :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences (P ⊓ Q) s
  → divergences P s ⊎ divergences Q s
⊓-divergences-elim {I = I} {R = R} {P = P} {Q = Q} {s = s}
  record { prefix = pre ; suffix = suf ; split = sp
         ; witness = w  ; reach = r ; divwit = dw } =
    go suf sp r dw
  where
    -- Inner helper for the `bNil`-prefix case: in that branch the trace
    -- itself is empty, so the divergent witness's first τ-step is the
    -- only thing that picks a br2 branch.  Records produced here use
    -- `prefix = []` and `suffix = s` (forced by `reach = bNil`).
    -- Splitting out into `aux` lets the `refl` in `sNdbr … refl refl`
    -- unify `next` with `P`/`Q` — impossible if `next` were a record
    -- projection like `dpq .Divergent.next`.
    aux : (next : ITree E (ExtI I) R)
        → (P ⊓ Q) ─[ τ ]─► next
        → Divergent next
        → divergences P s ⊎ divergences Q s
    aux next (sSil ()) _
    aux next (sNdbr {i = (_ , base _)}   refl ()) _
    aux next (sNdbr {i = (_ , pair _ _)} refl ()) _
    aux next (sNdbr {i = (_ , fin)} {a = lift fzero}
                    refl refl) dnext =
        inj₁ (record
          { prefix = [] ; suffix = s ; split = refl
          ; witness = next ; reach = bNil ; divwit = dnext
          })
    aux next (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)}
                    refl refl) dnext =
        inj₂ (record
          { prefix = [] ; suffix = s ; split = refl
          ; witness = next ; reach = bNil ; divwit = dnext
          })
    aux next (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))}
                    refl ()) _

    -- Walk the trace `(P ⊓ Q) ═⟨ pre' ⟩═► w'`.  We thread `suf'`/`sp'`
    -- through but make `pre'` implicit so that the `bNil` pattern can
    -- refine it to `[]` automatically (otherwise `pre'` would be a
    -- pattern variable and Agda couldn't unify it with `[]`).
    go : (suf' : List (Event√ E R))
       → ∀ {pre'} → s ≡ pre' ++ suf'
       → ∀ {w'}
       → (P ⊓ Q) ═⟨ pre' ⟩═► w'
       → Divergent w'
       → divergences P s ⊎ divergences Q s
    -- bNil : pre' = [], w' = P ⊓ Q.  Delegate to `aux`.
    go suf' sp' bNil dpq =
      aux (dpq .Divergent.next) (dpq .Divergent.step)
          (dpq .Divergent.diverge)
    -- bTau : the τ-step is sNdbr (force = ndbr).  Re-anchor on P or Q.
    go _ _ (bTau (sSil ())                              _) _
    go _ _ (bTau (sNdbr {i = (_ , base _)}   refl ())   _) _
    go _ _ (bTau (sNdbr {i = (_ , pair _ _)} refl ())   _) _
    go suf' sp' (bTau (sNdbr {i = (_ , fin)} {a = lift fzero}
                              refl refl) rest) dw' =
        inj₁ (record
          { prefix = _ ; suffix = suf' ; split = sp'
          ; witness = _ ; reach = rest ; divwit = dw'
          })
    go suf' sp' (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)}
                              refl refl) rest) dw' =
        inj₂ (record
          { prefix = _ ; suffix = suf' ; split = sp'
          ; witness = _ ; reach = rest ; divwit = dw'
          })
    go _ _ (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))}
                        refl ()) _) _
    -- bStep: ev from P ⊓ Q impossible.
    go _ _ (bStep (sRet ())   _) _
    go _ _ (bStep (sVis () _) _) _

-----------------------------------------------------------------------------
-- failures⊥ inherits the sum decomposition via case-split on the
-- `failures ⊎ divergences` representation.
-----------------------------------------------------------------------------

⊓-failures⊥-introL :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ P s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥-introL (inj₁ f) = inj₁ (⊓-failures-introL f)
⊓-failures⊥-introL (inj₂ d) = inj₂ (⊓-divergences-introL d)

⊓-failures⊥-introR :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ Q s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥-introR (inj₁ f) = inj₁ (⊓-failures-introR f)
⊓-failures⊥-introR (inj₂ d) = inj₂ (⊓-divergences-introR d)

⊓-failures⊥-elim :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ (P ⊓ Q) s B
  → failures⊥ P s B ⊎ failures⊥ Q s B
⊓-failures⊥-elim (inj₁ f) with ⊓-failures-elim f
... | inj₁ fP = inj₁ (inj₁ fP)
... | inj₂ fQ = inj₂ (inj₁ fQ)
⊓-failures⊥-elim (inj₂ d) with ⊓-divergences-elim d
... | inj₁ dP = inj₁ (inj₂ dP)
... | inj₂ dQ = inj₂ (inj₂ dQ)

-----------------------------------------------------------------------------
-- Associativity of internal choice in the FD model.
--
-- Given the sum decomposition lemmas, the proof is just associativity
-- of `_⊎_`: a failure⊥ of `P ⊓ (Q ⊓ R)` decomposes as
--     failures⊥ P ⊎ (failures⊥ Q ⊎ failures⊥ R)
-- which by re-bracketing is
--     (failures⊥ P ⊎ failures⊥ Q) ⊎ failures⊥ R
-- and re-introduces as a failure⊥ of `(P ⊓ Q) ⊓ R`.  Same shape for
-- divergences.  The two refinements pair into `≃FD`.
-----------------------------------------------------------------------------

⊓-assoc-FD :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q R' : ITree E (ExtI I) R)
  → ((P ⊓ Q) ⊓ R') ≃FD (P ⊓ (Q ⊓ R'))
⊓-assoc-FD P Q R' = fwd , bwd
  where
    -- ((P ⊓ Q) ⊓ R')  ⊑FD  (P ⊓ (Q ⊓ R')):
    --   inputs are failures⊥/divergences of the right side; we
    --   produce failures⊥/divergences of the left side.
    fwd-F⊥ : ((P ⊓ Q) ⊓ R') ⊑F⊥ (P ⊓ (Q ⊓ R'))
    fwd-F⊥ f-RHS with ⊓-failures⊥-elim f-RHS
    ... | inj₁ f-P  = ⊓-failures⊥-introL (⊓-failures⊥-introL f-P)
    ... | inj₂ f-QR with ⊓-failures⊥-elim f-QR
    ... | inj₁ f-Q  = ⊓-failures⊥-introL (⊓-failures⊥-introR f-Q)
    ... | inj₂ f-R' = ⊓-failures⊥-introR f-R'

    fwd-D : ((P ⊓ Q) ⊓ R') ⊑D (P ⊓ (Q ⊓ R'))
    fwd-D d-RHS with ⊓-divergences-elim d-RHS
    ... | inj₁ d-P  = ⊓-divergences-introL (⊓-divergences-introL d-P)
    ... | inj₂ d-QR with ⊓-divergences-elim d-QR
    ... | inj₁ d-Q  = ⊓-divergences-introL (⊓-divergences-introR d-Q)
    ... | inj₂ d-R' = ⊓-divergences-introR d-R'

    fwd : ((P ⊓ Q) ⊓ R') ⊑FD (P ⊓ (Q ⊓ R'))
    fwd = fwd-F⊥ , fwd-D

    -- The reverse direction is the mirror image: re-bracket via the
    -- sum decompositions in the opposite associativity.
    bwd-F⊥ : (P ⊓ (Q ⊓ R')) ⊑F⊥ ((P ⊓ Q) ⊓ R')
    bwd-F⊥ f-LHS with ⊓-failures⊥-elim f-LHS
    ... | inj₂ f-R' = ⊓-failures⊥-introR (⊓-failures⊥-introR f-R')
    ... | inj₁ f-PQ with ⊓-failures⊥-elim f-PQ
    ... | inj₁ f-P  = ⊓-failures⊥-introL f-P
    ... | inj₂ f-Q  = ⊓-failures⊥-introR (⊓-failures⊥-introL f-Q)

    bwd-D : (P ⊓ (Q ⊓ R')) ⊑D ((P ⊓ Q) ⊓ R')
    bwd-D d-LHS with ⊓-divergences-elim d-LHS
    ... | inj₂ d-R' = ⊓-divergences-introR (⊓-divergences-introR d-R')
    ... | inj₁ d-PQ with ⊓-divergences-elim d-PQ
    ... | inj₁ d-P  = ⊓-divergences-introL d-P
    ... | inj₂ d-Q  = ⊓-divergences-introR (⊓-divergences-introL d-Q)

    bwd : (P ⊓ (Q ⊓ R')) ⊑FD ((P ⊓ Q) ⊓ R')
    bwd = bwd-F⊥ , bwd-D

-----------------------------------------------------------------------------
-- Laws lifted from DRWbisim via `≈⇒≃FD`.
--
-- `_⊓_` commutativity and idempotence already hold under DRWbisim
-- (see `CSP.Laws.InternalChoice_DRBisim`), so they lift to `_≃FD_`
-- for free via the preservation theorem
--   `≈⇒≃FD : ∀ {P Q} → P ≈ Q → P ≃FD Q`
-- defined in `ITree_Relations.FailuresDivergencesEquiv`.
-----------------------------------------------------------------------------

import CSP.Laws.InternalChoice_DRBisim {ℓ} {ℓe} {E} as ⊓-bisim-laws
open ⊓-bisim-laws E-≟ using () renaming (⊓-comm to ⊓-comm-≈; ⊓-idem to ⊓-idem-≈)

⊓-comm-FD :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P Q : ITree E (ExtI I) R)
  → (P ⊓ Q) ≃FD (Q ⊓ P)
⊓-comm-FD P Q = ≈⇒≃FD (⊓-comm-≈ P Q)

⊓-idem-FD :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P : ITree E (ExtI I) R)
  → (P ⊓ P) ≃FD P
⊓-idem-FD P = ≈⇒≃FD (⊓-idem-≈ P)
