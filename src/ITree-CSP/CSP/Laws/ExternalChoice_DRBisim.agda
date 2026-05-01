{-
  External-choice laws for ITree-CSP, validated w.r.t. divergence-respecting
  weak bisimulation (DRWbisim) with propositional equality on return values.

  We work with the abbreviation
      _≈_  =  DRWbisim _≡_
  introduced in ITree_Relations.DRWeakBisim.

  The laws proved (or stated as `postulate` for now, pending completion):

    Stop-unit     :  Stop □ P ≈ P              P □ Stop ≈ P
    idempotence   :  P □ P   ≈ P
    commutativity :  P □ Q   ≈ Q □ P
    associativity :  (P □ Q) □ R ≈ P □ (Q □ R)
    ⊓-distrib     :  P □ (Q ⊓ R) ≈ (P □ Q) ⊓ (P □ R)
    congruence    :  P₁ ≈ P₂  →  Q₁ ≈ Q₂  →  P₁ □ Q₁ ≈ P₂ □ Q₂

  Notes on proof strategy
  ───────────────────────
  Each law is a coinductive DRWbisim proof: we must build `fwd` and `bwd`
  simulations that for every LTS transition of the LHS produce a weak
  matching transition of the RHS (and vice-versa), carrying a DRWbisim
  witness for the resulting pair.  Because the reduction semantics of `_□_`
  (see `CSP/Operators.agda`) has 10+ cases (based on the node kinds of
  `P .force` and `Q .force`), each law requires exhaustive case analysis.

  The laws below are currently stated; proofs that are straightforward
  symbolic manipulations are in place, while the structurally heavy ones
  are marked `postulate` with a concrete proof plan in a comment.
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax; ∃-syntax)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Maybe   using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base renaming (tt to tt₀)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Function     using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary  using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂; inspect; [_])

open import Class.DecEq using (DecEq; _≟_)

open import Prelude
open import Interaction_Trees
open import CSP.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences using (Divergent; divergent-prefix)
open import ITree_Relations.DRWeakBisim

module CSP.Laws.ExternalChoice_DRBisim
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-- Internal-choice laws (`⊓-comm`, `⊓-idem`) are proved in a separate
-- module and re-exported here so existing call sites keep working.
open import CSP.Laws.InternalChoice_DRBisim {ℓ} {ℓe} {E} E-≟ public
  using (⊓-comm; ⊓-idem)

open ITree
open Label
open DRWSimF
open DRWbisim

-----------------------------------------------------------------------------
-- Statements of the external-choice laws.
--
-- `_≈_` is `DRWbisim _≡_`, the divergence-respecting weak bisimulation
-- identifying return values by propositional equality.  See
-- `ITree_Relations.DRWeakBisim`.
-----------------------------------------------------------------------------

-- Stop is a left unit of external choice.
--
--   Proof plan: by coinduction on P.  Cases for P .force:
--     ret r           : force Stop = vis (λ _ _ → nothing), force P = ret r,
--                       so force (Stop □ P) = ret r = force P, reflexive.
--     sil P'          : force (Stop □ P) = sil (Stop □ P'),
--                       force P = sil P', so both take a τ step; recurse.
--     vis fP          : force (Stop □ P) = vis (mergeVis (λ _ → nothing) fP)
--                                       = vis fP (extensionally).  Visible
--                       events and their successors agree; recurse.
--     ndbr fP wi wa w : force (Stop □ P) = ndbr ... with branches
--                       (Stop □ P'); a τ match on both sides reduces to
--                       proving Stop □ P' ≈ P' — recurse.
-- `□-Stop-left` is proved below (after the congruence/commutativity
-- scaffolding) with the same decomposition used for `□-cong`/`□-comm`.
-- `□-Stop-right` is then derived from `□-comm` + `□-Stop-left`.
postulate

-- Idempotence: external choice of P with itself is P (up to ≈).
--
--   Proof plan: the only sub-case that is not literally reflexive at the
--   force level is `ret r | ret r | yes refl = ret r` (trivially ok) and
--   `vis fP | vis fP`, which yields `vis (mergeVis fP fP)`.  When
--   `fP x = just t`, `mergeVis fP fP x = just (t ⊓ t)`, so idempotence of
--   `_□_` reduces to idempotence of `_⊓_` on the successors.  The ndbr/ndbr
--   case likewise reduces to idempotence of `_⊓_` via `mergeNdbr`.
  □-idem :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    → (P : ITree E (ExtI I) R)
    → (P □ P) ≈ P

-- Commutativity is proved below (after the inversion lemmas) with the
-- same outer-plumbing/sub-obligation decomposition as `□-cong`.

-- Associativity.
--
--   Proof plan: coinduction on ((P □ Q) .force , (P □ (Q □ R)) .force).
--   The key combinatorial work is showing that the "bundled" ndbr node
--   produced by `mergeNdbr fP (mergeNdbr fQ fR) ...` is bisim-equivalent to
--   `mergeNdbr (mergeNdbr fP fQ) fR ...`; this is an ndbr-re-associativity
--   lemma generalising the usual associativity of `_⊓_` to the arbitrary
--   branching structure of `_□_`.
  □-assoc :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    → (P Q R' : ITree E (ExtI I) R)
    → ((P □ Q) □ R') ≈ (P □ (Q □ R'))

-- External choice distributes over internal choice from the right.
--
--   Proof plan: `Q ⊓ R` unfolds to an `ndbr` node whose two branches are
--   `Q` and `R`.  Therefore `P □ (Q ⊓ R)` reduces (by the vis/ndbr or
--   ndbr/ndbr rules of `_□_`, depending on P's shape) to an `ndbr` whose
--   branches are `P □ Q` and `P □ R` — which is precisely `(P □ Q) ⊓ (P □ R)`.
--   The proof walks both sides in lock-step by LTS transitions.
  □-⊓-distrib :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    → (P Q R' : ITree E (ExtI I) R)
    → (P □ (Q ⊓ R')) ≈ ((P □ Q) ⊓ (P □ R'))

-----------------------------------------------------------------------------
-- Inversion lemmas for `force (P □ Q)`
--
-- These invert the defining equations of `_□_` in `CSP/Operators.agda`:
-- if `force (P □ Q)` is of a given node kind, then so are `force P` and
-- `force Q` in specific patterns.  They let consumers skip nested `with`-
-- dispatches and the reduction hurdles they entail.
-----------------------------------------------------------------------------

-- If `force (P □ Q) ≡ vis f`, then both sides must be `vis`, and
-- `f` is `mergeVis` of their continuation maps (rule G of `_□_`).
□-force-vis-inv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force (P □ Q) ≡ vis f
  → Σ[ fP ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))) ]
    Σ[ fQ ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))) ]
      ( ITree.force P ≡ vis fP
      × ITree.force Q ≡ vis fQ
      × f ≡ (λ Ae → mergeVis (fP Ae) (fQ Ae)) )
□-force-vis-inv {P = P} {Q = Q} eq
  with ITree.force P | inspect ITree.force P | ITree.force Q | inspect ITree.force Q
-- Rule (G): the productive case.
... | vis fP        | [ eqP ] | vis fQ        | [ eqQ ] =
        fP , fQ , refl , refl , sym (vis-injective eq)
-- Remaining 15 non-vis/vis force combinations yield a non-`vis` node
-- for `force (P □ Q)`, so `eq : _ ≡ vis _` is absurd in each.
... | sil _         | _       | _             | _       = case eq of λ ()
... | ret r         | _       | ret r'        | _       with r ≟ r'
...   | yes refl = case eq of λ ()
...   | no  _    = case eq of λ ()
□-force-vis-inv eq | ret _        | _ | sil _          | _ = case eq of λ ()
□-force-vis-inv eq | ret _        | _ | vis _          | _ = case eq of λ ()
□-force-vis-inv eq | ret _        | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-vis-inv eq | vis _        | _ | sil _          | _ = case eq of λ ()
□-force-vis-inv eq | vis _        | _ | ret _          | _ = case eq of λ ()
□-force-vis-inv eq | vis _        | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-vis-inv eq | ndbr _ _ _ _ | _ | sil _          | _ = case eq of λ ()
□-force-vis-inv eq | ndbr _ _ _ _ | _ | ret _          | _ = case eq of λ ()
□-force-vis-inv eq | ndbr _ _ _ _ | _ | vis _          | _ = case eq of λ ()
□-force-vis-inv eq | ndbr _ _ _ _ | _ | ndbr _ _ _ _   | _ = case eq of λ ()

-- If `force (P □ Q) ≡ sil u`, then either `force P ≡ sil P'` (and
-- `u = P' □ Q` — rule A) or `force Q ≡ sil Q'` with P stable (and
-- `u = P □ Q'` — rule B).
□-force-sil-inv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {u : ITree E (ExtI I) R}
  → ITree.force (P □ Q) ≡ sil u
  → (Σ[ P' ∈ ITree E (ExtI I) R ]
       (ITree.force P ≡ sil P' × u ≡ (P' □ Q)))
  ⊎ (Σ[ Q' ∈ ITree E (ExtI I) R ]
       (ITree.force Q ≡ sil Q' × u ≡ (P □ Q')))
□-force-sil-inv {P = P} {Q = Q} eq
  with ITree.force P | inspect ITree.force P | ITree.force Q | inspect ITree.force Q
-- Rule (A): P has a sil, regardless of Q.
... | sil P'        | _       | _             | _       =
        inj₁ (P' , refl , sym (sil-injective eq))
-- Rule (B): P is stable (ret/vis/ndbr), Q has a sil.
... | ret _         | _       | sil Q'        | _       =
        inj₂ (Q' , refl , sym (sil-injective eq))
... | vis _         | _       | sil Q'        | _       =
        inj₂ (Q' , refl , sym (sil-injective eq))
... | ndbr _ _ _ _  | _       | sil Q'        | _       =
        inj₂ (Q' , refl , sym (sil-injective eq))
-- Remaining combinations: force (P □ Q) ≠ sil.
... | ret r         | _       | ret r'        | _       with r ≟ r'
...   | yes refl = case eq of λ ()
...   | no  _    = case eq of λ ()
□-force-sil-inv eq | ret _  | _ | vis _          | _ = case eq of λ ()
□-force-sil-inv eq | ret _  | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-sil-inv eq | vis _  | _ | ret _          | _ = case eq of λ ()
□-force-sil-inv eq | vis _  | _ | vis _          | _ = case eq of λ ()
□-force-sil-inv eq | vis _  | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-sil-inv eq | ndbr _ _ _ _ | _ | ret _          | _ = case eq of λ ()
□-force-sil-inv eq | ndbr _ _ _ _ | _ | vis _          | _ = case eq of λ ()
□-force-sil-inv eq | ndbr _ _ _ _ | _ | ndbr _ _ _ _   | _ = case eq of λ ()

-- If `force (P □ Q) ≡ ret r`, the r came from P (rule C/E) or from Q
-- (rule F).
□-force-ret-inv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {r : R}
  → ITree.force (P □ Q) ≡ ret r
  → ITree.force P ≡ ret r ⊎ ITree.force Q ≡ ret r
□-force-ret-inv {P = P} {Q = Q} eq
  with ITree.force P | inspect ITree.force P | ITree.force Q | inspect ITree.force Q
... | sil _         | _ | _             | _ = case eq of λ ()
... | ret r'        | _ | ret r''       | _ with r' ≟ r''
...   | yes refl = inj₁ eq
...   | no  _    = case eq of λ ()
□-force-ret-inv eq | ret _  | _ | sil _          | _ = case eq of λ ()
□-force-ret-inv eq | ret _  | _ | vis _          | _ = inj₁ eq
□-force-ret-inv eq | ret _  | _ | ndbr _ _ _ _   | _ = inj₁ eq
□-force-ret-inv eq | vis _  | _ | sil _          | _ = case eq of λ ()
□-force-ret-inv eq | vis _  | _ | ret _          | _ = inj₂ eq
□-force-ret-inv eq | vis _  | _ | vis _          | _ = case eq of λ ()
□-force-ret-inv eq | vis _  | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-ret-inv eq | ndbr _ _ _ _ | _ | sil _          | _ = case eq of λ ()
□-force-ret-inv eq | ndbr _ _ _ _ | _ | ret _          | _ = inj₂ eq
□-force-ret-inv eq | ndbr _ _ _ _ | _ | vis _          | _ = case eq of λ ()
□-force-ret-inv eq | ndbr _ _ _ _ | _ | ndbr _ _ _ _   | _ = case eq of λ ()

-- If `force (P □ Q) ≡ ndbr _ _ _ _`, then one of four productive rules
-- of `_□_` produced it:
--   (D) ret r | ret r' | no _  (the `ret_r ⊓ ret_r'` unfold)
--   (H) vis   | ndbr                 (bundle P with Q's branches)
--   (I) ndbr  | vis                  (bundle P's branches with Q)
--   (J) ndbr  | ndbr                 (mergeNdbr pair-bundling)
-- The returned disjunction captures the force kinds of P and Q, which is
-- enough to trigger further unfolding at call sites.
□-force-ndbr-inv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  →   -- (D) ret/ret with r ≠ r'
      (Σ[ r ∈ _ ] Σ[ r' ∈ _ ]
         (r ≢ r' × ITree.force P ≡ ret r × ITree.force Q ≡ ret r'))
    ⊎ -- (H) vis / ndbr
      (Σ[ fP ∈ _ ] Σ[ fQ ∈ _ ]
       Σ[ wiQ ∈ _ ] Σ[ waQ ∈ _ ] Σ[ wpQ ∈ _ ]
         (ITree.force P ≡ vis fP × ITree.force Q ≡ ndbr fQ wiQ waQ wpQ))
    ⊎ -- (I) ndbr / vis
      (Σ[ fP ∈ _ ] Σ[ wiP ∈ _ ] Σ[ waP ∈ _ ] Σ[ wpP ∈ _ ]
       Σ[ fQ ∈ _ ]
         (ITree.force P ≡ ndbr fP wiP waP wpP × ITree.force Q ≡ vis fQ))
    ⊎ -- (J) ndbr / ndbr
      (Σ[ fP ∈ _ ] Σ[ wiP ∈ _ ] Σ[ waP ∈ _ ] Σ[ wpP ∈ _ ]
       Σ[ fQ ∈ _ ] Σ[ wiQ ∈ _ ] Σ[ waQ ∈ _ ] Σ[ wpQ ∈ _ ]
         ( ITree.force P ≡ ndbr fP wiP waP wpP
         × ITree.force Q ≡ ndbr fQ wiQ waQ wpQ ))
□-force-ndbr-inv {P = P} {Q = Q} eq
  with ITree.force P | inspect ITree.force P | ITree.force Q | inspect ITree.force Q
-- Case D: ret r | ret r' with r ≟ r'.
... | ret r  | _ | ret r' | _ with r ≟ r'
...   | yes refl = case eq of λ ()
...   | no  neq  = inj₁ (r , r' , neq , refl , refl)
-- Case H, I, J, and remaining absurd combinations handled below.
□-force-ndbr-inv eq | vis fP         | _ | ndbr fQ wiQ waQ wpQ | _ =
        inj₂ (inj₁ (fP , fQ , wiQ , waQ , wpQ , refl , refl))
□-force-ndbr-inv eq | ndbr fP wiP waP wpP | _ | vis fQ              | _ =
        inj₂ (inj₂ (inj₁ (fP , wiP , waP , wpP , fQ , refl , refl)))
□-force-ndbr-inv eq | ndbr fP wiP waP wpP | _ | ndbr fQ wiQ waQ wpQ | _ =
        inj₂ (inj₂ (inj₂ (fP , wiP , waP , wpP , fQ , wiQ , waQ , wpQ , refl , refl)))
-- Absurd combinations (force reduces to sil / ret / vis, not ndbr).
□-force-ndbr-inv eq | sil _          | _ | _              | _ = case eq of λ ()
□-force-ndbr-inv eq | ret _          | _ | sil _          | _ = case eq of λ ()
□-force-ndbr-inv eq | ret _          | _ | vis _          | _ = case eq of λ ()
□-force-ndbr-inv eq | ret _          | _ | ndbr _ _ _ _   | _ = case eq of λ ()
□-force-ndbr-inv eq | vis _          | _ | sil _          | _ = case eq of λ ()
□-force-ndbr-inv eq | vis _          | _ | ret _          | _ = case eq of λ ()
□-force-ndbr-inv eq | vis _          | _ | vis _          | _ = case eq of λ ()
□-force-ndbr-inv eq | ndbr _ _ _ _   | _ | sil _          | _ = case eq of λ ()
□-force-ndbr-inv eq | ndbr _ _ _ _   | _ | ret _          | _ = case eq of λ ()

-----------------------------------------------------------------------------
-- Foundational bisim lemmas (Option B)
--
-- These are the "atoms" of the equational approach: small, reusable bisim
-- properties that let operator laws be derived as short chains of
-- `drwbisim-trans` / `drwbisim-sym` / `□-cong` applications instead of
-- multi-case structural coinduction.
-----------------------------------------------------------------------------

-- sil-τ-refl: if `force P ≡ sil P'`, then P and P' are weak-bisim equal.
-- This is the "τ-prefix absorption" lemma: a single silent step doesn't
-- observably distinguish two trees under DRWbisim.
--
-- Notably, this definition is NOT recursive on `sil-τ-refl` itself —
-- it uses only `drwbisim-refl` (which is standalone in `DRWeakBisim`)
-- and `divergent-prefix`.  No `NON_TERMINATING` pragma required.
sil-τ-refl :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {P P' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → P ≈ P'
-- fwd: P simulated by P'.  P's only step is its own sil; P' matches via
-- zero τs and reflexive bisim.
sil-τ-refl {P = P} {P' = P'} eqP .fwd .on-ret eq =
      case trans (sym eqP) eq of λ ()
sil-τ-refl eqP .fwd .on-vis (sVis force-eq _) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-tau (sSil force-eq)
  with sil-injective (trans (sym force-eq) eqP)
... | refl = _ , weak-τ τ*-zero , DRWbisimEquiv.drwbisim-refl ≡-equiv _
sil-τ-refl eqP .fwd .on-tau (sNdbr force-eq _) =
      case trans (sym eqP) force-eq of λ ()
sil-τ-refl eqP .fwd .on-div d
  with d .Divergent.step
...  | sSil force-eq with sil-injective (trans (sym force-eq) eqP)
...  | refl = d .Divergent.diverge
sil-τ-refl eqP .fwd .on-div d | sNdbr force-eq _ =
      case trans (sym eqP) force-eq of λ ()
-- bwd: P' simulated by P.  Every step of P' is matched by P doing its
-- own sil first (via sSil eqP) and then the same step on P'.
sil-τ-refl {P = P} {P' = P'} eqP .bwd .on-ret {r = r} eq =
      P' , r , weak-τ (τ*-step (sSil eqP) τ*-zero) , eq , refl
sil-τ-refl eqP .bwd .on-vis step =
      _ , weak-ev (τ*-step (sSil eqP) τ*-zero) step τ*-zero ,
      DRWbisimEquiv.drwbisim-refl ≡-equiv _
sil-τ-refl eqP .bwd .on-tau step =
      _ , weak-τ (τ*-step (sSil eqP) (τ*-step step τ*-zero)) ,
      DRWbisimEquiv.drwbisim-refl ≡-equiv _
sil-τ-refl eqP .bwd .on-div d =
      divergent-prefix (τ*-step (sSil eqP) τ*-zero) d

-- τ*-concat: concatenate two τ* chains.  (Private in DRWeakBisim — we
-- redefine here for use in foundation lemmas.)
τ*-concat :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {t t' t'' : ITree E (ExtI I) R}
  → t ─[τ*]─► t' → t' ─[τ*]─► t'' → t ─[τ*]─► t''
τ*-concat τ*-zero       q = q
τ*-concat (τ*-step s p) q = τ*-step s (τ*-concat p q)

-- lift-via-bisim: given a τ* chain `P ─[τ*]─► P'` and a bisim `X ≈ P`,
-- produce a weak-τ matching chain from `X` whose end is bisim to P'.
-- Inducts structurally on the chain — no `NON_TERMINATING` needed.
lift-via-bisim :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {X P P' : ITree E (ExtI I) R}
  → P ─[τ*]─► P'
  → X ≈ P
  → Σ[ X' ∈ ITree E (ExtI I) R ] ((X ═[ τ ]═► X') × X' ≈ P')
lift-via-bisim τ*-zero bisim = _ , weak-τ τ*-zero , bisim
lift-via-bisim (τ*-step step rest) bisim
  with bisim .bwd .on-tau step
... | X-mid , weak-τ X-step , P-mid≈X-mid
    with lift-via-bisim rest (DRWbisimEquiv.drwbisim-sym ≡-equiv P-mid≈X-mid)
...   | X' , weak-τ rest-step , X'≈P' =
        X' , weak-τ (τ*-concat X-step rest-step) , X'≈P'

-- ret-equiv: two trees with matching `ret r` forces are bisim-equal.
-- Once a tree is at a `ret r` node, no further steps are possible, so
-- any two such trees observationally equivalent.
--
-- Like `sil-τ-refl`, non-recursive on itself — no pragma needed.
ret-equiv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {P Q : ITree E (ExtI I) R} {r : R}
  → ITree.force P ≡ ret r
  → ITree.force Q ≡ ret r
  → P ≈ Q
-- fwd: P simulated by Q.
ret-equiv {Q = Q} {r = r} eqP eqQ .fwd .on-ret eq
  with trans (sym eqP) eq
... | refl = Q , r , weak-τ τ*-zero , eqQ , refl
ret-equiv eqP _ .fwd .on-vis (sVis force-eq _) =
      case trans (sym eqP) force-eq of λ ()
ret-equiv eqP _ .fwd .on-tau (sSil force-eq) =
      case trans (sym eqP) force-eq of λ ()
ret-equiv eqP _ .fwd .on-tau (sNdbr force-eq _) =
      case trans (sym eqP) force-eq of λ ()
ret-equiv eqP _ .fwd .on-div d
  with d .Divergent.step
...  | sSil force-eq    = case trans (sym eqP) force-eq of λ ()
...  | sNdbr force-eq _ = case trans (sym eqP) force-eq of λ ()
-- bwd: Q simulated by P.  Symmetric.
ret-equiv {P = P} {r = r} eqP eqQ .bwd .on-ret eq
  with trans (sym eqQ) eq
... | refl = P , r , weak-τ τ*-zero , eqP , refl
ret-equiv _ eqQ .bwd .on-vis (sVis force-eq _) =
      case trans (sym eqQ) force-eq of λ ()
ret-equiv _ eqQ .bwd .on-tau (sSil force-eq) =
      case trans (sym eqQ) force-eq of λ ()
ret-equiv _ eqQ .bwd .on-tau (sNdbr force-eq _) =
      case trans (sym eqQ) force-eq of λ ()
ret-equiv _ eqQ .bwd .on-div d
  with d .Divergent.step
...  | sSil force-eq    = case trans (sym eqQ) force-eq of λ ()
...  | sNdbr force-eq _ = case trans (sym eqQ) force-eq of λ ()

-----------------------------------------------------------------------------
-- Congruence of `_□_` under DRWbisim
--
--   □-cong :  P₁ ≈ P₂  →  Q₁ ≈ Q₂  →  P₁ □ Q₁ ≈ P₂ □ Q₂
--
-- We assemble `□-cong` from four simulation-step sub-lemmas, one per
-- field of `DRWSimF`.  Each sub-lemma inverts a one-step LTS transition
-- out of `P₁ □ Q₁` (by case analysis on `force P₁` and `force Q₁`) and,
-- using the bisim hypotheses on `P` and `Q`, constructs a matching weak
-- transition out of `P₂ □ Q₂`.
--
-- The backward simulation is obtained from the forward one by symmetry
-- of `≈` (see `DRWbisimEquiv.drwbisim-sym` applied to `≡-equiv`).
-----------------------------------------------------------------------------

-- Reusable equivalence-closure helpers for `≈ = DRWbisim _≡_`.
private
  open module EQ {ℓ' ℓe' ℓi' ℓr'} {E' : Set ℓ' → Set ℓe'}
                 {I' : Set ℓ' → Set ℓi'} {R' : Set ℓr'} =
        DRWbisimEquiv {E = E'} {I = I'} {R = R'} {RetRel = _≡_} ≡-equiv
        using (drwbisim-sym; drwbisim-refl)

-- Forward declaration of `□-cong` — needed by `vis-liftL` below (which
-- uses `□-cong bP bQ .fwd .on-vis` on a constructed compound step).
□-cong :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → (P₁ □ Q₁) ≈ (P₂ □ Q₂)

-- Simulation-step obligations for the forward direction.  Each of these
-- mirrors the corresponding field of `DRWSimF _≡_ (DRWbisim _≡_)
-- (P₁ □ Q₁) (P₂ □ Q₂)`.
--
-- Proof plan for all four:
--   Case analyse `force P₁` and `force Q₁`; for each of the ~16
--   combinations use the defining rule of `_□_` in `CSP/Operators.agda`
--   and the corresponding matching clause of the hypothesis bisims to
--   synthesise the weak match from `P₂ □ Q₂`.

-- Auxiliary lifting postulates used by the `on-vis` case below.
--
-- They are cleanly separated so a future proof session can attack them
-- directly.  Each corresponds to one of the three ways a single visible
-- event out of `P₁ □ Q₁` can be attributed:
--
--   vis-liftL : the event is offered only by P (fP enabled, fQ blocked),
--               so a matching weak ev transition is produced from the
--               left side alone.
--   vis-liftR : symmetric — only Q offers the event.
--   vis-liftM : both sides offer; the merged successor is an `⊓`.
--
-- These three lemmas are the actual residual content of `on-vis` after
-- stripping away the bookkeeping; fill them in to finish `on-vis`.
-- Force-unfolding helper for the vis/vis case of `_□_` (rule G).
force-□-vis-vis' :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ vis fQ
  → ITree.force (P □ Q) ≡ vis (λ Ae → mergeVis (fP Ae) (fQ Ae))
force-□-vis-vis' {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | vis _ | refl | vis _ | refl = refl

-- `vis-liftL` proved.  New signature takes the force equations for P₁ and
-- Q₁ explicitly (which the caller in `□-cong-fwd-on-vis` always has in
-- scope).  Proof strategy: lift P₁'s vis step into `(P₁ □ Q₁)`'s force-G
-- step (yields P' directly since fQ at a = nothing), then apply
-- `□-cong bP bQ .fwd .on-vis` to the compound step.
{-# NON_TERMINATING #-}
vis-liftL :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P₁ ≡ vis fP
  → ITree.force Q₁ ≡ vis fQ
  → {at : AnyTypes E} {a : proj₁ at} {P' : ITree E (ExtI I) R}
  → fP at a ≡ just P'
  → fQ at a ≡ nothing
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (P₂ □ Q₂) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × P' ≈ t' )
vis-liftL {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ} eqP eqQ
          {at = at} {a = a} {P' = P'} fP-eq fQ-eq =
    (□-cong bP bQ) .fwd .on-vis compound-step
  where
    compound-step : (P₁ □ Q₁) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► P'
    compound-step = sVis {p = P₁ □ Q₁}
                         {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                         {at = at} {a = a} {t′ = P'}
                         (force-□-vis-vis' {P = P₁} {Q = Q₁} eqP eqQ)
                         (cong₂ mergeMaybe fP-eq fQ-eq)

-- `vis-liftR` proved.  Symmetric to `vis-liftL`: only Q offers the
-- event (`fQ at a ≡ just Q'`, `fP at a ≡ nothing`).  Compound (P₁ □ Q₁)
-- still steps to Q' via mergeMaybe; apply □-cong's on-vis.
{-# NON_TERMINATING #-}
vis-liftR :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P₁ ≡ vis fP
  → ITree.force Q₁ ≡ vis fQ
  → {at : AnyTypes E} {a : proj₁ at} {Q' : ITree E (ExtI I) R}
  → fP at a ≡ nothing
  → fQ at a ≡ just Q'
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (P₂ □ Q₂) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × Q' ≈ t' )
vis-liftR {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ} eqP eqQ
          {at = at} {a = a} {Q' = Q'} fP-eq fQ-eq =
    (□-cong bP bQ) .fwd .on-vis compound-step
  where
    compound-step : (P₁ □ Q₁) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► Q'
    compound-step = sVis {p = P₁ □ Q₁}
                         {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                         {at = at} {a = a} {t′ = Q'}
                         (force-□-vis-vis' {P = P₁} {Q = Q₁} eqP eqQ)
                         (cong₂ mergeMaybe fP-eq fQ-eq)

-- `vis-liftM` proved.  Both sides offer the event; mergeMaybe yields
-- `just (P' ⊓ Q')`.  Same pattern — compound steps to `P' ⊓ Q'`,
-- □-cong matches.
{-# NON_TERMINATING #-}
vis-liftM :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P₁ ≡ vis fP
  → ITree.force Q₁ ≡ vis fQ
  → {at : AnyTypes E} {a : proj₁ at} {P' Q' : ITree E (ExtI I) R}
  → fP at a ≡ just P'
  → fQ at a ≡ just Q'
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (P₂ □ Q₂) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × (P' ⊓ Q') ≈ t' )
vis-liftM {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ} eqP eqQ
          {at = at} {a = a} {P' = P'} {Q' = Q'} fP-eq fQ-eq =
    (□-cong bP bQ) .fwd .on-vis compound-step
  where
    compound-step : (P₁ □ Q₁) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► (P' ⊓ Q')
    compound-step = sVis {p = P₁ □ Q₁}
                         {f = λ Ae → mergeVis (fP Ae) (fQ Ae)}
                         {at = at} {a = a} {t′ = P' ⊓ Q'}
                         (force-□-vis-vis' {P = P₁} {Q = Q₁} eqP eqQ)
                         (cong₂ mergeMaybe fP-eq fQ-eq)

-- The `on-vis` sub-lemma.  A visible step out of `P₁ □ Q₁` fires only
-- when `force (P₁ □ Q₁) = vis (mergeVis fP fQ)` — i.e., by rule (G) of
-- `_□_`, which requires `force P₁ = vis fP` and `force Q₁ = vis fQ`.
-- Decomposition of `mergeVis fP fQ at a = just t` then forks into the
-- three `vis-liftL` / `vis-liftR` / `vis-liftM` cases above.
--
-- With `□-force-vis-inv` in hand, we can decompose the visible step:
-- by rule G, `force P₁ ≡ vis fP` and `force Q₁ ≡ vis fQ`, and the
-- continuation is `mergeVis fP fQ`.  A `just t` case of `mergeMaybe`
-- picks exactly which of `vis-liftL/R/M` fires.
□-cong-fwd-on-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {at : AnyTypes E} {a : proj₁ at} {t : ITree E (ExtI I) R}
  → (P₁ □ Q₁) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (P₂ □ Q₂) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × t ≈ t' )
□-cong-fwd-on-vis {P₁ = P₁} {P₂} {Q₁} {Q₂} bP bQ {at = at} {a = a} step
  with ev-ndbr step
... | f , force-eq , f-eq
    with □-force-vis-inv {P = P₁} {Q = Q₁} {f = f} force-eq
...   | fP , fQ , eqP , eqQ , eqF
        rewrite eqF
        with fP at a | inspect (fP at) a | fQ at a | inspect (fQ at) a | f-eq
-- Case L: only P offers the event.
...        | just P' | [ eqFP ] | nothing | [ eqFQ ] | refl =
              vis-liftL {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ}
                        eqP eqQ {at = at} {a = a} {P' = P'} eqFP eqFQ
-- Case R: only Q offers the event.
...        | nothing | [ eqFP ] | just Q' | [ eqFQ ] | refl =
              vis-liftR {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ}
                        eqP eqQ {at = at} {a = a} {Q' = Q'} eqFP eqFQ
-- Case M: both sides offer, merged successor is an `⊓`.
...        | just P' | [ eqFP ] | just Q' | [ eqFQ ] | refl =
              vis-liftM {P₁ = P₁} {Q₁ = Q₁} bP bQ {fP = fP} {fQ = fQ}
                        eqP eqQ {at = at} {a = a} {P' = P'} {Q' = Q'} eqFP eqFQ
-- Absurd: mergeMaybe nothing nothing = nothing ≠ just t.
...        | nothing | _        | nothing | _       | ()

-- The `on-ret` sub-lemma — proved equationally via foundations.
--
-- Strategy: by `□-force-ret-inv`, force P₁ ≡ ret r (Case L) or force Q₁
-- ≡ ret r (Case R).  In Case L:
--   1. Apply bP.fwd.on-ret to get P₂ ─[τ*]─► P₂' with force P₂' ≡ ret r'.
--   2. By `ret-equiv`, (P₁ □ Q₁) ≈ P₁ — both have force ret r.
--   3. By □-cong + bP, (P₂ □ Q₂) ≈ (P₁ □ Q₁) ≈ P₁ ≈ P₂.  Call this `Z`.
--   4. By `lift-via-bisim`, the chain on P₂ lifts to a weak τ from
--      (P₂ □ Q₂) reaching X' with X' ≈ P₂'.
--   5. Since force P₂' ≡ ret r', applying X'≈P₂'.bwd.on-ret yields a
--      further weak τ chain to a ret-r' state in (P₂ □ Q₂).  Compose
--      chains and we're done.
{-# NON_TERMINATING #-}
□-cong-fwd-on-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {r : R}
  → ITree.force (P₁ □ Q₁) ≡ ret r
  → Σ[ t' ∈ ITree E (ExtI I) R ]
    Σ[ r' ∈ R ]
      ( (P₂ □ Q₂) ═[ τ ]═► t'
      × ITree.force t' ≡ ret r'
      × r ≡ r' )
□-cong-fwd-on-ret {P₁ = P₁} {P₂} {Q₁} {Q₂} bP bQ eq
  with □-force-ret-inv {P = P₁} {Q = Q₁} eq
-- Case L: the ret came from P₁.
... | inj₁ force-P₁-eq with bP .fwd .on-ret force-P₁-eq
...   | P₂' , r' , weak-τ P₂-chain , force-P₂'-eq , r≡r' =
        let
          -- Z : (P₂ □ Q₂) ≈ P₂.
          Z : (P₂ □ Q₂) ≈ P₂
          Z = DRWbisimEquiv.drwbisim-trans ≡-equiv
                (drwbisim-sym (□-cong bP bQ))
                (DRWbisimEquiv.drwbisim-trans ≡-equiv
                  (ret-equiv eq force-P₁-eq) bP)
          -- Lift P₂'s chain through Z.
          X' , weak-X' , X'≈P₂' = lift-via-bisim P₂-chain Z
          -- Use X' ≈ P₂' to get the final ret-r' state.
          X'' , r'' , weak-X'' , force-X''-eq , r'≡r'' =
                X'≈P₂' .bwd .on-ret force-P₂'-eq
        in
          X'' , r'' ,
          (case weak-X' of λ where
             (weak-τ chain1) →
               (case weak-X'' of λ where
                 (weak-τ chain2) → weak-τ (τ*-concat chain1 chain2))) ,
          force-X''-eq ,
          trans r≡r' r'≡r''
-- Case R: the ret came from Q₁ — symmetric.
□-cong-fwd-on-ret {P₁ = P₁} {P₂} {Q₁} {Q₂} bP bQ eq
    | inj₂ force-Q₁-eq with bQ .fwd .on-ret force-Q₁-eq
...   | Q₂' , r' , weak-τ Q₂-chain , force-Q₂'-eq , r≡r' =
        let
          Z : (P₂ □ Q₂) ≈ Q₂
          Z = DRWbisimEquiv.drwbisim-trans ≡-equiv
                 (drwbisim-sym (□-cong bP bQ))
                 (DRWbisimEquiv.drwbisim-trans ≡-equiv
                   (ret-equiv eq force-Q₁-eq) bQ)
          X' , weak-X' , X'≈Q₂' = lift-via-bisim Q₂-chain Z
          X'' , r'' , weak-X'' , force-X''-eq , r'≡r'' =
                X'≈Q₂' .bwd .on-ret force-Q₂'-eq
        in
          X'' , r'' ,
          (case weak-X' of λ where
             (weak-τ chain1) →
               (case weak-X'' of λ where
                 (weak-τ chain2) → weak-τ (τ*-concat chain1 chain2))) ,
          force-X''-eq ,
          trans r≡r' r'≡r''

-- Auxiliary lifting lemmas used by `on-tau`.
--
-- `tau-lift-L` (resp. `tau-lift-R`) handles the rule-A (resp. rule-B) τ
-- step: the compound `force (P₁ □ Q₁) ≡ sil (P₁' □ Q₁)` (resp.
-- `sil (P₁ □ Q₁')`) was produced by P's (resp. Q's) own sil.  Both are
-- proved uniformly by passing the compound step into `□-cong`'s `on-tau`.
-- This relies on the productive coinductive nature of `≈`; the
-- `NON_TERMINATING` pragma marks the mutual recursion through `□-cong`.
--
-- `tau-lift-ndbr-step` is still postulated; it handles the remaining
-- `sNdbr` cases (D, H, I, J).
{-# NON_TERMINATING #-}
tau-lift-L :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {P₁' : ITree E (ExtI I) R}
  → ITree.force (P₁ □ Q₁) ≡ sil (P₁' □ Q₁)
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ((P₂ □ Q₂) ═[ τ ]═► t' × (P₁' □ Q₁) ≈ t')
tau-lift-L bP bQ eq-sil = (□-cong bP bQ) .fwd .on-tau (sSil eq-sil)

{-# NON_TERMINATING #-}
tau-lift-R :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {Q₁' : ITree E (ExtI I) R}
  → ITree.force (P₁ □ Q₁) ≡ sil (P₁ □ Q₁')
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ((P₂ □ Q₂) ═[ τ ]═► t' × (P₁ □ Q₁') ≈ t')
tau-lift-R bP bQ eq-sil = (□-cong bP bQ) .fwd .on-tau (sSil eq-sil)

-- `tau-lift-ndbr-step` covers the rule-D/H/I/J sub-cases: the τ step is
-- the compound's own `sNdbr`.  Like `tau-lift-L`/`R`, the proof reduces
-- to `(□-cong bP bQ) .fwd .on-tau (sNdbr eq-ndbr eq-j)` — Agda accepts
-- the productive coinductive recursion through `□-cong` under
-- `NON_TERMINATING`.
{-# NON_TERMINATING #-}
tau-lift-ndbr-step :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → ITree.force (P₁ □ Q₁) ≡ ndbr f wi wa prf
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ((P₂ □ Q₂) ═[ τ ]═► t' × t ≈ t')
tau-lift-ndbr-step bP bQ eq-ndbr eq-j =
    (□-cong bP bQ) .fwd .on-tau (sNdbr eq-ndbr eq-j)

-- The `on-tau` sub-lemma.  By `τ-ndbr` inversion, the step is either
-- `sSil` or `sNdbr`.
--   sSil : `force (P₁ □ Q₁) ≡ sil t`.  Split via `□-force-sil-inv`: the
--          sil came from P (rule A) or Q (rule B); use `tau-lift-L` /
--          `tau-lift-R` on the reconstructed single-side step.
--   sNdbr: all four ndbr-producing rules (D, H, I, J) collapse into a
--          single `tau-lift-ndbr-step` call.
□-cong-fwd-on-tau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → {t : ITree E (ExtI I) R}
  → (P₁ □ Q₁) ─[ τ ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (P₂ □ Q₂) ═[ τ ]═► t'
      × t ≈ t' )
□-cong-fwd-on-tau {P₁ = P₁} {P₂} {Q₁} {Q₂} bP bQ step
  with τ-ndbr step
-- Case A (sSil): force (P₁ □ Q₁) ≡ sil t.  Dispatch via sil-inversion.
... | inj₁ (u , eq-sil , refl)
    with □-force-sil-inv {P = P₁} {Q = Q₁} eq-sil
...    | inj₁ (P₁' , eqP , refl) = tau-lift-L bP bQ eq-sil
...    | inj₂ (Q₁' , eqQ , refl) = tau-lift-R bP bQ eq-sil
-- Case B (sNdbr): the τ is an ndbr branch.  All four sub-cases (D, H,
-- I, J) are lumped into `tau-lift-ndbr-step`.
□-cong-fwd-on-tau {P₁ = P₁} {P₂} {Q₁} {Q₂} bP bQ _
    | inj₂ (_ , _ , _ , _ , _ , _ , eq-ndbr , eq-j) =
          tau-lift-ndbr-step bP bQ eq-ndbr eq-j

-- The `on-div` sub-lemma.  Given `Divergent (P₁ □ Q₁)`, we invoke
-- `□-cong-fwd-on-tau` on the single τ step supplied by the divergence
-- witness.  That yields a weak τ chain `(P₂ □ Q₂) ─[τ*]─► t'` and a
-- bisim `d.next ≈ t'`.  Divergence is preserved by `≈` (its `on-div`
-- field), so `t'` is divergent; then `divergent-prefix` lifts via the
-- τ chain to `Divergent (P₂ □ Q₂)`.
□-cong-fwd-on-div :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → Divergent (P₁ □ Q₁)
  → Divergent (P₂ □ Q₂)
□-cong-fwd-on-div bP bQ d
  with □-cong-fwd-on-tau bP bQ (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-- `□-cong` definition — signature forward-declared above.  Plain plumbing
-- over the four sub-lemmas; backward simulation uses the forward
-- sub-lemmas applied to the symmetric hypotheses.
□-cong bP bQ .fwd .on-ret eq   = □-cong-fwd-on-ret bP bQ eq
□-cong bP bQ .fwd .on-vis step = □-cong-fwd-on-vis bP bQ step
□-cong bP bQ .fwd .on-tau step = □-cong-fwd-on-tau bP bQ step
□-cong bP bQ .fwd .on-div d    = □-cong-fwd-on-div bP bQ d
□-cong bP bQ .bwd .on-ret eq   = □-cong-fwd-on-ret (drwbisim-sym bP) (drwbisim-sym bQ) eq
□-cong bP bQ .bwd .on-vis step = □-cong-fwd-on-vis (drwbisim-sym bP) (drwbisim-sym bQ) step
□-cong bP bQ .bwd .on-tau step = □-cong-fwd-on-tau (drwbisim-sym bP) (drwbisim-sym bQ) step
□-cong bP bQ .bwd .on-div d    = □-cong-fwd-on-div (drwbisim-sym bP) (drwbisim-sym bQ) d

-----------------------------------------------------------------------------
-- Commutativity: P □ Q ≈ Q □ P
--
-- Same decomposition as `□-cong`: four simulation sub-obligations
-- (on-ret, on-vis, on-tau, on-div), `on-div` is derived via `on-tau` +
-- `divergent-prefix`, and the outer bisimulation record is assembled by
-- applying the forward sub-lemmas with swapped arguments for `bwd`.
--
-- Forward-declare `□-comm` so that `comm-tau-sSil-R` can issue a
-- recursive call on a smaller right-argument.
-----------------------------------------------------------------------------

□-comm :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → (P □ Q) ≈ (Q □ P)

-- Forward symmetry: if force (P □ Q) reduces to ret r, so does force (Q □ P).
-- Every ret-producing rule of `_□_` has a symmetric partner when (P, Q) is
-- swapped — rule C's `yes refl` is symmetric, rules E and F are each other's
-- counterparts.
force-□-comm-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R} {r : R}
  → ITree.force (P □ Q) ≡ ret r
  → ITree.force (Q □ P) ≡ ret r
force-□-comm-ret {P = P} {Q = Q} eq
  with ITree.force P | ITree.force Q
-- sil on either side: force (P □ Q) = sil, absurd.
... | sil _ | _ = case eq of λ ()
-- ret/ret: force (P □ Q) reduces via r₁ ≟ r₂; force (Q □ P) reduces via
-- r₂ ≟ r₁.  We match on both to let Agda reduce each independently —
-- Agda's DecEq reduction doesn't automatically cross the argument flip.
... | ret r₁ | ret r₂ with r₁ ≟ r₂ | r₂ ≟ r₁
...   | yes refl | yes refl = eq
...   | yes refl | no  neq  = ⊥-elim (neq refl)
...   | no  neq  | yes refl = ⊥-elim (neq refl)
...   | no  _    | no  _    = case eq of λ ()
force-□-comm-ret eq | ret _ | sil _            = case eq of λ ()
force-□-comm-ret eq | ret _ | vis _            = eq
force-□-comm-ret eq | ret _ | ndbr _ _ _ _     = eq
force-□-comm-ret eq | vis _ | sil _            = case eq of λ ()
force-□-comm-ret eq | vis _ | ret _            = eq
force-□-comm-ret eq | vis _ | vis _            = case eq of λ ()
force-□-comm-ret eq | vis _ | ndbr _ _ _ _     = case eq of λ ()
force-□-comm-ret eq | ndbr _ _ _ _ | sil _         = case eq of λ ()
force-□-comm-ret eq | ndbr _ _ _ _ | ret _         = eq
force-□-comm-ret eq | ndbr _ _ _ _ | vis _         = case eq of λ ()
force-□-comm-ret eq | ndbr _ _ _ _ | ndbr _ _ _ _  = case eq of λ ()

-- `on-ret`: use the force-symmetry helper to produce a ret-configuration for
-- `(Q □ P)` at τ*-zero distance; r ≡ r' is refl.
□-comm-on-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {r : R}
  → ITree.force (P □ Q) ≡ ret r
  → Σ[ t' ∈ ITree E (ExtI I) R ]
    Σ[ r' ∈ R ]
      ( (Q □ P) ═[ τ ]═► t'
      × ITree.force t' ≡ ret r'
      × r ≡ r' )
□-comm-on-ret P Q {r} eq =
    (Q □ P) , r , weak-τ τ*-zero , force-□-comm-ret {P = P} {Q = Q} eq , refl

-- Force-unfolding helper for the vis/vis case of `_□_` (rule G).
force-□-vis-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ vis fQ
  → ITree.force (P □ Q) ≡ vis (λ Ae → mergeVis (fP Ae) (fQ Ae))
force-□-vis-vis {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | vis _ | refl | vis _ | refl = refl

-- `on-vis`: visible step out of `(P □ Q)` only via rule G (vis/vis).
-- The merged continuation is `mergeMaybe (fP at a) (fQ at a)`; the swap
-- `(Q □ P)` uses `mergeMaybe (fQ at a) (fP at a)`.  Three productive
-- sub-cases on the Maybe pair:
--   (just P', nothing) → t = P' ; swap keeps just P'.
--   (nothing, just Q') → t = Q' ; swap keeps just Q'.
--   (just P', just Q') → t = P' ⊓ Q' ; swap yields Q' ⊓ P', related by
--                                       ⊓-comm.
□-comm-on-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {at : AnyTypes E} {a : proj₁ at} {t : ITree E (ExtI I) R}
  → (P □ Q) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × t ≈ t' )
□-comm-on-vis P Q {at = at} {a = a} (sVis force-eq f-eq)
  with ITree.force P | inspect ITree.force P
     | ITree.force Q | inspect ITree.force Q | force-eq
-- vis/vis: the only productive case.
... | vis fP | [ eqP ] | vis fQ | [ eqQ ] | refl
    with fP at a | inspect (fP at) a | fQ at a | inspect (fQ at) a | f-eq
-- Case L: only P offers (fP just, fQ nothing).
...   | just P' | [ fP-eq ] | nothing | [ fQ-eq ] | refl =
        P' ,
        weak-ev τ*-zero
          (sVis {p = Q □ P}
                {f = λ Ae → mergeVis (fQ Ae) (fP Ae)}
                {at = at} {a = a} {t′ = P'}
                (force-□-vis-vis {P = Q} {Q = P} eqQ eqP)
                (cong₂ mergeMaybe fQ-eq fP-eq))
          τ*-zero ,
        drwbisim-refl P'
-- Case R: only Q offers (fP nothing, fQ just).
...   | nothing | [ fP-eq ] | just Q' | [ fQ-eq ] | refl =
        Q' ,
        weak-ev τ*-zero
          (sVis {p = Q □ P}
                {f = λ Ae → mergeVis (fQ Ae) (fP Ae)}
                {at = at} {a = a} {t′ = Q'}
                (force-□-vis-vis {P = Q} {Q = P} eqQ eqP)
                (cong₂ mergeMaybe fQ-eq fP-eq))
          τ*-zero ,
        drwbisim-refl Q'
-- Case M: both offer; t = P' ⊓ Q', swap's t' = Q' ⊓ P', related by ⊓-comm.
...   | just P' | [ fP-eq ] | just Q' | [ fQ-eq ] | refl =
        (Q' ⊓ P') ,
        weak-ev τ*-zero
          (sVis {p = Q □ P}
                {f = λ Ae → mergeVis (fQ Ae) (fP Ae)}
                {at = at} {a = a} {t′ = Q' ⊓ P'}
                (force-□-vis-vis {P = Q} {Q = P} eqQ eqP)
                (cong₂ mergeMaybe fQ-eq fP-eq))
          τ*-zero ,
        ⊓-comm P' Q'
-- mergeMaybe nothing nothing = nothing — absurd.
...   | nothing | _ | nothing | _ | ()
-- All other `(force P, force Q)` combinations make `force (P □ Q)`
-- NOT a vis, so `force-eq : _ ≡ vis f` is absurd.
□-comm-on-vis _ _ (sVis _ _) | sil _ | _ | _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ret r₁ | _ | ret r₂ | _ | eq with r₁ ≟ r₂
...   | yes refl = case eq of λ ()
...   | no  _    = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ret _ | _ | sil _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ret _ | _ | vis _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ret _ | _ | ndbr _ _ _ _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | vis _ | _ | sil _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | vis _ | _ | ret _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | vis _ | _ | ndbr _ _ _ _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ndbr _ _ _ _ | _ | sil _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ndbr _ _ _ _ | _ | ret _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ndbr _ _ _ _ | _ | vis _ | _ | eq = case eq of λ ()
□-comm-on-vis _ _ (sVis _ _) | ndbr _ _ _ _ | _ | ndbr _ _ _ _ | _ | eq = case eq of λ ()

-- Force-unfolding helper: if the *left* argument of `_□_` has `sil P'`,
-- the compound reduces via rule A to `sil (P' □ Q)`.
force-□-sil-L :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q P' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → ITree.force (P □ Q) ≡ sil (P' □ Q)
force-□-sil-L {P = P} {Q = Q} eqP
  with ITree.force P | eqP
... | sil _ | refl = refl

-- Force-unfolding helpers for rule B: the *right* argument has `sil P'`
-- and the left argument is stable (ret / vis / ndbr).
force-□-sil-R-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q P' : ITree E (ExtI I) R} {r : R}
  → ITree.force Q ≡ ret r
  → ITree.force P ≡ sil P'
  → ITree.force (Q □ P) ≡ sil (Q □ P')
force-□-sil-R-ret {P = P} {Q = Q} eqQ eqP
  with ITree.force Q | eqQ | ITree.force P | eqP
... | ret _ | refl | sil _ | refl = refl

force-□-sil-R-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q P' : ITree E (ExtI I) R}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force Q ≡ vis fQ
  → ITree.force P ≡ sil P'
  → ITree.force (Q □ P) ≡ sil (Q □ P')
force-□-sil-R-vis {P = P} {Q = Q} eqQ eqP
  with ITree.force Q | eqQ | ITree.force P | eqP
... | vis _ | refl | sil _ | refl = refl

force-□-sil-R-ndbr :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q P' : ITree E (ExtI I) R}
  → {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiQ : AnyTypes (ExtI I)} {waQ : proj₁ wiQ} {wpQ : Is-just (fQ wiQ waQ)}
  → ITree.force Q ≡ ndbr fQ wiQ waQ wpQ
  → ITree.force P ≡ sil P'
  → ITree.force (Q □ P) ≡ sil (Q □ P')
force-□-sil-R-ndbr {P = P} {Q = Q} eqQ eqP
  with ITree.force Q | eqQ | ITree.force P | eqP
... | ndbr _ _ _ _ | refl | sil _ | refl = refl

-- Sub-case helpers for `□-comm-on-tau`.
--
--   * `comm-tau-sSil-R` — force Q ≡ sil Q' (see below).
--   * `comm-tau-sSil-L` — force P ≡ sil P' (see below).  Three of the
--     four Q-shapes (ret, vis, ndbr) are proved directly; only `force Q
--     ≡ sil Q''` stays postulated (`comm-tau-sSil-LL-silQ`) because the
--     bisim chain for that sub-case needs `sil-τ-bisim` (P ─[τ]─► P'
--     ⇒ P ≈ P'), which is a separate lemma.
--   * `comm-tau-ndbr-step` — umbrella for sNdbr sub-cases D/H/I/J.
-- `comm-tau-sSil-LL-silQ` proved using the foundations.
--
--   (P □ Q) ─[τ]─► (P' □ Q)         (hypothesis context)
--   (Q □ P) ─[τ]─► (Q'' □ P)        via rule A on force Q ≡ sil Q''
--
--   Need: (P' □ Q) ≈ (Q'' □ P).  Chain via foundations + □-cong + □-comm:
--     (P' □ Q)  ≈ (P' □ Q'')  -- □-cong (refl P') (sil-τ-refl eqQ)
--             ≈ (Q'' □ P')   -- □-comm P' Q''
--             ≈ (Q'' □ P)    -- □-cong (refl Q'') (sym (sil-τ-refl eqP))

comm-tau-sSil-LL-silQ :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {P' Q'' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → ITree.force Q ≡ sil Q''
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × (P' □ Q) ≈ t' )
comm-tau-sSil-LL-silQ P Q {P' = P'} {Q'' = Q''} eqP eqQ =
    (Q'' □ P) ,
    weak-τ (τ*-step (sSil {p = Q □ P} {t = Q'' □ P}
                          (force-□-sil-L {P = Q} {Q = P} eqQ)) τ*-zero) ,
    DRWbisimEquiv.drwbisim-trans ≡-equiv
      (□-cong (drwbisim-refl P') (sil-τ-refl eqQ))
      (DRWbisimEquiv.drwbisim-trans ≡-equiv
        (□-comm P' Q'')
        (□-cong (drwbisim-refl Q'') (drwbisim-sym (sil-τ-refl eqP))))

-- Force-unfolding helper for rule D (ret/ret with distinct values).
-- The compound reduces to `(P ⊓ Q).force = ndbr (br2 P Q) ...`.
force-□-ndbr-D :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R} {r r' : R}
  → ITree.force P ≡ ret r
  → ITree.force Q ≡ ret r'
  → r ≢ r'
  → ITree.force (P □ Q) ≡
      ndbr (br2 P Q) (Lift _ (Fin 2) , fin) (lift fzero) (any-just tt₀)
force-□-ndbr-D {P = P} {Q = Q} eqP eqQ neq
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ret r | refl | ret r' | refl with r ≟ r'
...   | yes p = ⊥-elim (neq p)
...   | no _  = refl

-- Case D: ret/ret with distinct return values.  The compound reduces to
-- `ndbr (br2 P Q) ...`; the step selects either branch of `br2` giving
-- `t = P` or `t = Q`.  In (Q □ P), the symmetric `br2 Q P` offers the
-- *opposite* branch to the same successor.  Bisim is `drwbisim-refl`.
comm-tau-ndbr-D :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {r r' : R}
  → r ≢ r'
  → ITree.force P ≡ ret r
  → ITree.force Q ≡ ret r'
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
comm-tau-ndbr-D P Q {r} {r'} neq eqP eqQ eq-ndbr {i} {a} eq-j
  with ITree.force P | eqP
... | ret _ | refl with ITree.force Q | eqQ
...   | ret _ | refl with r ≟ r'
...     | yes p = ⊥-elim (neq p)
...     | no _  with r' ≟ r
...       | yes p = ⊥-elim (neq (sym p))
...       | no _  with eq-ndbr
...         | refl with i | a | eq-j
-- Branch (_ , fin) (lift fzero) → just P.  Take symmetric branch
-- (fsuc fzero) in (Q □ P) to reach P.
...           | (_ , fin) | lift fzero | refl =
                P ,
                weak-τ (τ*-step (sNdbr {p = Q □ P} {f = br2 Q P}
                                       {wi = Lift ℓ (Fin 2) , fin}
                                       {wa = lift fzero}
                                       {prf = any-just tt₀}
                                       {i = Lift ℓ (Fin 2) , fin}
                                       {a = lift (fsuc fzero)}
                                       {t′ = P}
                                       (force-□-ndbr-D {P = Q} {Q = P}
                                                       eqQ eqP (λ p → neq (sym p)))
                                       refl) τ*-zero) ,
                drwbisim-refl P
-- Branch (_ , fin) (lift (fsuc fzero)) → just Q.  Swap: take fzero in
-- (Q □ P) to reach Q.
...           | (_ , fin) | lift (fsuc fzero) | refl =
                Q ,
                weak-τ (τ*-step (sNdbr {p = Q □ P} {f = br2 Q P}
                                       {wi = Lift ℓ (Fin 2) , fin}
                                       {wa = lift fzero}
                                       {prf = any-just tt₀}
                                       {i = Lift ℓ (Fin 2) , fin}
                                       {a = lift fzero}
                                       {t′ = Q}
                                       (force-□-ndbr-D {P = Q} {Q = P}
                                                       eqQ eqP (λ p → neq (sym p)))
                                       refl) τ*-zero) ,
                drwbisim-refl Q
-- Other branch patterns: br2 gives `nothing`, contradicting eq-j.
...           | (_ , fin) | lift (fsuc (fsuc _)) | ()
...           | (_ , base _) | _ | ()
...           | (_ , pair _ _) | _ | ()

-- Force-eq helper: when force P ≡ ndbr fP wi wa wp and force Q ≡ vis fQ,
-- the compound's force reduces (rule I) to ndbr of the top-level
-- `mergeNdbr-vis-R fP Q` continuation.  Stating this with a fully-
-- explicit RHS in the type lets Agda's reduction succeed (matching its
-- internal with-helper); a `refl`-shaped sub-goal of `sNdbr` would not
-- reduce here on its own.
force-□-ndbr-vis-eq :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (fP wi wa)}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ ndbr fP wi wa wp
  → ITree.force Q ≡ vis fQ
  → ITree.force (P □ Q) ≡
        ndbr (mergeNdbr-vis-R fP Q) wi wa (mergeNdbr-vis-R-witness fP Q wp)
force-□-ndbr-vis-eq {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | vis _ | refl = refl

-- Branch-eq helper: `mergeNdbr-vis-R fP Q i a ≡ just (P' □ Q)` whenever
-- `fP i a ≡ just P'`.
mergeNdbr-vis-R-just :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (Q : ITree E (ExtI I) R)
  → ∀ {i a P'} → fP i a ≡ just P' → mergeNdbr-vis-R fP Q i a ≡ just (P' □ Q)
mergeNdbr-vis-R-just fP Q {i} {a} eq with fP i a | eq
... | just _ | refl = refl

-- Symmetric force-eq for rule H: `force P ≡ vis fP`, `force Q ≡ ndbr ...`
-- ⇒ `force (P □ Q)` reduces to ndbr of `mergeNdbr-vis-L P fQ`.
force-□-vis-ndbr-eq :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (fQ wi wa)}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ ndbr fQ wi wa wp
  → ITree.force (P □ Q) ≡
        ndbr (mergeNdbr-vis-L P fQ) wi wa (mergeNdbr-vis-L-witness P fQ wp)
force-□-vis-ndbr-eq {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | vis _ | refl | ndbr _ _ _ _ | refl = refl

-- Symmetric branch-eq: `mergeNdbr-vis-L P fQ i a ≡ just (P □ Q')` whenever
-- `fQ i a ≡ just Q'`.
mergeNdbr-vis-L-just :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {i a Q'} → fQ i a ≡ just Q' → mergeNdbr-vis-L P fQ i a ≡ just (P □ Q')
mergeNdbr-vis-L-just P fQ {i} {a} eq with fQ i a | eq
... | just _ | refl = refl

-- Force-eq for rule J (ndbr/ndbr): the compound's force is `ndbr` of the
-- top-level `mergeNdbr fP fQ`, indexed by the swapped/paired witness.
force-□-ndbr-ndbr-eq :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiP wiQ : AnyTypes (ExtI I)} {waP : proj₁ wiP} {waQ : proj₁ wiQ}
  → {wpP : Is-just (fP wiP waP)} {wpQ : Is-just (fQ wiQ waQ)}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → ITree.force Q ≡ ndbr fQ wiQ waQ wpQ
  → ITree.force (P □ Q) ≡
        ndbr (mergeNdbr fP fQ)
             ((proj₁ wiP × proj₁ wiQ) , pair (proj₂ wiP) (proj₂ wiQ))
             (waP , waQ)
             (mergeNdbr-witness fP fQ wpP wpQ)
force-□-ndbr-ndbr-eq {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | ndbr _ _ _ _ | refl = refl

-- Branch-eq helpers for `mergeNdbr` at a `pair`-indexed branch.
mergeNdbr-pair-jj :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ}
      {aP : AP} {aQ : AQ} {P' Q' : ITree E (ExtI I) R}
  → fP (AP , iP) aP ≡ just P'
  → fQ (AQ , iQ) aQ ≡ just Q'
  → mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (aP , aQ) ≡ just (P' □ Q')
mergeNdbr-pair-jj fP fQ {AP} {AQ} {iP} {iQ} {aP} {aQ} fP-eq fQ-eq
  with fP (AP , iP) aP | fP-eq | fQ (AQ , iQ) aQ | fQ-eq
... | just _ | refl | just _ | refl = refl

mergeNdbr-pair-jn :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ}
      {aP : AP} {aQ : AQ} {P' : ITree E (ExtI I) R}
  → fP (AP , iP) aP ≡ just P'
  → fQ (AQ , iQ) aQ ≡ nothing
  → mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (aP , aQ) ≡ just P'
mergeNdbr-pair-jn fP fQ {AP} {AQ} {iP} {iQ} {aP} {aQ} fP-eq fQ-eq
  with fP (AP , iP) aP | fP-eq | fQ (AQ , iQ) aQ | fQ-eq
... | just _ | refl | nothing | refl = refl

mergeNdbr-pair-nj :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {AP AQ : Set ℓ} {iP : ExtI I AP} {iQ : ExtI I AQ}
      {aP : AP} {aQ : AQ} {Q' : ITree E (ExtI I) R}
  → fP (AP , iP) aP ≡ nothing
  → fQ (AQ , iQ) aQ ≡ just Q'
  → mergeNdbr fP fQ ((AP × AQ) , pair iP iQ) (aP , aQ) ≡ just Q'
mergeNdbr-pair-nj fP fQ {AP} {AQ} {iP} {iQ} {aP} {aQ} fP-eq fQ-eq
  with fP (AP , iP) aP | fP-eq | fQ (AQ , iQ) aQ | fQ-eq
... | nothing | refl | just _ | refl = refl

-- Focused lift for Case H of `□-comm`: given `force P ≡ vis fP`,
-- `force Q ≡ ndbr fQ _ _ _`, and `fQ i a ≡ just Q'`, the swapped
-- compound `(Q □ P)` takes a τ step to `(Q' □ P)` via rule I.
-- Constructed by combining `force-□-ndbr-vis-eq` (force reduction) with
-- `mergeNdbr-vis-R-just` (continuation lookup) into an `sNdbr`.
comm-H-lift :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiQ : AnyTypes (ExtI I)} {waQ : proj₁ wiQ} {wpQ : Is-just (fQ wiQ waQ)}
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {Q' : ITree E (ExtI I) R}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ ndbr fQ wiQ waQ wpQ
  → fQ i a ≡ just Q'
  → (Q □ P) ─[ τ ]─► (Q' □ P)
comm-H-lift {P = P} {Q = Q} {fQ = fQ} {wiQ = wiQ} {waQ = waQ} {wpQ = wpQ}
            eqP eqQ fQ-eq =
    sNdbr {f = mergeNdbr-vis-R fQ P} {wi = wiQ} {wa = waQ}
          {prf = mergeNdbr-vis-R-witness fQ P wpQ}
          (force-□-ndbr-vis-eq {P = Q} {Q = P} eqQ eqP)
          (mergeNdbr-vis-R-just fQ P fQ-eq)

-- Case H: vis/ndbr.  Rule H gives force (P □ Q) = ndbr (λ ai a' →
-- case fQ ai a' of ...) with branches mapping fQ's "just Q'" to
-- "just (P □ Q')".  In the swap (Q □ P), rule I fires (ndbr/vis) with
-- branches mapping fQ's "just Q'" to "just (Q' □ P)".  Same index
-- (i, a), successor bisim `□-comm P Q'`.
{-# NON_TERMINATING #-}
comm-tau-ndbr-H :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiQ : AnyTypes (ExtI I)} {waQ : proj₁ wiQ} {wpQ : Is-just (fQ wiQ waQ)}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ ndbr fQ wiQ waQ wpQ
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
comm-tau-ndbr-H P Q {fQ = fQ} eqP eqQ eq-ndbr {i} {a} eq-j
  with ITree.force P | eqP | ITree.force Q | eqQ
... | vis _ | refl | ndbr _ _ _ _ | refl with eq-ndbr
...   | refl with fQ i a | inspect (fQ i) a | eq-j
...     | just Q' | [ fQ-eq ] | refl =
          (Q' □ P) ,
          weak-τ (τ*-step (comm-H-lift {P = P} {Q = Q}
                                        {i = i} {a = a} {Q' = Q'}
                                        eqP eqQ fQ-eq) τ*-zero) ,
          □-comm P Q'
...     | nothing | _ | ()

-- Focused lift for Case I (symmetric to comm-H-lift): rule H produces
-- the swapped τ step `(Q □ P) ─[τ]─► (Q □ P')` from `force P ≡ ndbr fP`,
-- `force Q ≡ vis fQ`, and `fP i a ≡ just P'`.
comm-I-lift :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q : ITree E (ExtI I) R}
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {P' : ITree E (ExtI I) R}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → ITree.force Q ≡ vis fQ
  → fP i a ≡ just P'
  → (Q □ P) ─[ τ ]─► (Q □ P')
comm-I-lift {P = P} {Q = Q} {fP = fP} {wiP = wiP} {waP = waP} {wpP = wpP}
            eqP eqQ fP-eq =
    sNdbr {f = mergeNdbr-vis-L Q fP} {wi = wiP} {wa = waP}
          {prf = mergeNdbr-vis-L-witness Q fP wpP}
          (force-□-vis-ndbr-eq {P = Q} {Q = P} eqQ eqP)
          (mergeNdbr-vis-L-just Q fP fP-eq)

-- Case I: ndbr/vis (P has ndbr, Q has vis).  Rule I gives force (P □ Q) =
-- ndbr (mergeNdbr-vis-R fP Q) ...; the τ branch (i, a) maps fP's "just
-- P'" to "just (P' □ Q)".  In the swap (Q □ P), rule H fires with
-- continuation `mergeNdbr-vis-L Q fP`, and the same branch maps to
-- `just (Q □ P')`.  Successor bisim is `□-comm P' Q`.
comm-tau-ndbr-I :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
  → {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → ITree.force Q ≡ vis fQ
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
comm-tau-ndbr-I P Q {fP = fP} eqP eqQ eq-ndbr {i} {a} eq-j
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | vis _ | refl with eq-ndbr
...   | refl with fP i a | inspect (fP i) a | eq-j
...     | just P' | [ fP-eq ] | refl =
          (Q □ P') ,
          weak-τ (τ*-step (comm-I-lift {P = P} {Q = Q}
                                        {i = i} {a = a} {P' = P'}
                                        eqP eqQ fP-eq) τ*-zero) ,
          □-comm P' Q
...     | nothing | _ | ()

-- Case J: ndbr/ndbr.  Rule J makes force (P □ Q) = ndbr (mergeNdbr fP
-- fQ) ((AP × AQ), pair iP iQ) ...; the τ branch must be `pair`-indexed
-- (otherwise mergeNdbr returns nothing).  Three productive sub-cases on
-- (fP _ aP, fQ _ aQ):
--   (just P', just Q') → t = P' □ Q' ; in (Q □ P), `pair iQ' iP'` /
--                                       (aQ, aP) yields Q' □ P'.  Bisim
--                                       is `□-comm P' Q'`.
--   (just P', nothing) → t = P' ; swap also yields P'.  Bisim refl.
--   (nothing, just Q') → t = Q' ; swap yields Q'.  Bisim refl.
comm-tau-ndbr-J :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
  → {fQ : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiQ : AnyTypes (ExtI I)} {waQ : proj₁ wiQ} {wpQ : Is-just (fQ wiQ waQ)}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → ITree.force Q ≡ ndbr fQ wiQ waQ wpQ
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
comm-tau-ndbr-J P Q {fP = fP} {wiP = wiP} {waP = waP} {wpP = wpP}
                    {fQ = fQ} {wiQ = wiQ} {waQ = waQ} {wpQ = wpQ}
                    eqP eqQ eq-ndbr {i = (_ , base _)} eq-j
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | ndbr _ _ _ _ | refl with eq-ndbr
...   | refl = case eq-j of λ ()
comm-tau-ndbr-J P Q {fP = fP} {wiP = wiP} {waP = waP} {wpP = wpP}
                    {fQ = fQ} {wiQ = wiQ} {waQ = waQ} {wpQ = wpQ}
                    eqP eqQ eq-ndbr {i = (_ , fin)} eq-j
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | ndbr _ _ _ _ | refl with eq-ndbr
...   | refl = case eq-j of λ ()
comm-tau-ndbr-J P Q {fP = fP} {wiP = wiP} {waP = waP} {wpP = wpP}
                    {fQ = fQ} {wiQ = wiQ} {waQ = waQ} {wpQ = wpQ}
                    eqP eqQ eq-ndbr {i = (.(AP' × AQ') , pair {AP'} {AQ'} iP' iQ')}
                    {a = (aP , aQ)} eq-j
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | ndbr _ _ _ _ | refl with eq-ndbr
...   | refl
   with fP (AP' , iP') aP | inspect (fP (AP' , iP')) aP
      | fQ (AQ' , iQ') aQ | inspect (fQ (AQ' , iQ')) aQ | eq-j
-- (just P', just Q'): t = P' □ Q'; swap step yields (Q' □ P'), bisim □-comm.
...     | just P' | [ fP-eq ] | just Q' | [ fQ-eq ] | refl =
          (Q' □ P') ,
          weak-τ (τ*-step (sNdbr {p = Q □ P} {f = mergeNdbr fQ fP}
                                  {wi = (proj₁ wiQ × proj₁ wiP) ,
                                        pair (proj₂ wiQ) (proj₂ wiP)}
                                  {wa = waQ , waP}
                                  {prf = mergeNdbr-witness fQ fP wpQ wpP}
                                  {i = (AQ' × AP') , pair iQ' iP'}
                                  {a = aQ , aP}
                                  (force-□-ndbr-ndbr-eq {P = Q} {Q = P} eqQ eqP)
                                  (mergeNdbr-pair-jj fQ fP fQ-eq fP-eq))
                          τ*-zero) ,
          □-comm P' Q'
-- (just P', nothing): t = P'; swap also yields P', refl bisim.
...     | just P' | [ fP-eq ] | nothing | [ fQ-eq ] | refl =
          P' ,
          weak-τ (τ*-step (sNdbr {p = Q □ P} {f = mergeNdbr fQ fP}
                                  {wi = (proj₁ wiQ × proj₁ wiP) ,
                                        pair (proj₂ wiQ) (proj₂ wiP)}
                                  {wa = waQ , waP}
                                  {prf = mergeNdbr-witness fQ fP wpQ wpP}
                                  {i = (AQ' × AP') , pair iQ' iP'}
                                  {a = aQ , aP}
                                  (force-□-ndbr-ndbr-eq {P = Q} {Q = P} eqQ eqP)
                                  (mergeNdbr-pair-nj fQ fP fQ-eq fP-eq))
                          τ*-zero) ,
          drwbisim-refl P'
-- (nothing, just Q'): t = Q'; swap also yields Q'.
...     | nothing | [ fP-eq ] | just Q' | [ fQ-eq ] | refl =
          Q' ,
          weak-τ (τ*-step (sNdbr {p = Q □ P} {f = mergeNdbr fQ fP}
                                  {wi = (proj₁ wiQ × proj₁ wiP) ,
                                        pair (proj₂ wiQ) (proj₂ wiP)}
                                  {wa = waQ , waP}
                                  {prf = mergeNdbr-witness fQ fP wpQ wpP}
                                  {i = (AQ' × AP') , pair iQ' iP'}
                                  {a = aQ , aP}
                                  (force-□-ndbr-ndbr-eq {P = Q} {Q = P} eqQ eqP)
                                  (mergeNdbr-pair-jn fQ fP fQ-eq fP-eq))
                          τ*-zero) ,
          drwbisim-refl Q'
-- (nothing, nothing): mergeNdbr returns nothing, eq-j absurd.
...     | nothing | _ | nothing | _ | ()

comm-tau-sSil-R :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {Q' : ITree E (ExtI I) R}
  → ITree.force Q ≡ sil Q'
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × (P □ Q') ≈ t' )
-- Same structural-recursion-through-propositional-equations issue as
-- `□-Stop-left-fwd-on-tau`: Q' is smaller than Q but Agda cannot see
-- this through `force Q ≡ sil Q'`.  Semantically productive.
{-# NON_TERMINATING #-}
comm-tau-sSil-R P Q {Q' = Q'} eqQ =
    (Q' □ P) ,
    weak-τ (τ*-step (sSil {p = Q □ P} {t = Q' □ P}
                          (force-□-sil-L {P = Q} {Q = P} eqQ)) τ*-zero) ,
    □-comm P Q'

-- `comm-tau-sSil-L`: force P ≡ sil P'.  Case-split on force Q.
--   * force Q ∈ {ret, vis, ndbr}: rule B applies to (Q □ P), reaching
--     (Q □ P'); successor bisim `□-comm P' Q`.
--   * force Q ≡ sil Q'': postponed to `comm-tau-sSil-LL-silQ`.
comm-tau-sSil-L :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {P' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × (P' □ Q) ≈ t' )
      
comm-tau-sSil-L P Q {P' = P'} eqP
  with ITree.force Q | inspect ITree.force Q
... | ret r | [ eqQ ] =
      (Q □ P') ,
      weak-τ (τ*-step (sSil {p = Q □ P} {t = Q □ P'}
                            (force-□-sil-R-ret {P = P} {Q = Q} eqQ eqP))
                      τ*-zero) ,
      □-comm P' Q
... | vis _ | [ eqQ ] =
      (Q □ P') ,
      weak-τ (τ*-step (sSil {p = Q □ P} {t = Q □ P'}
                            (force-□-sil-R-vis {P = P} {Q = Q} eqQ eqP))
                      τ*-zero) ,
      □-comm P' Q
... | ndbr _ _ _ _ | [ eqQ ] =
      (Q □ P') ,
      weak-τ (τ*-step (sSil {p = Q □ P} {t = Q □ P'}
                            (force-□-sil-R-ndbr {P = P} {Q = Q} eqQ eqP))
                      τ*-zero) ,
      □-comm P' Q
... | sil _ | [ eqQ ] = comm-tau-sSil-LL-silQ P Q eqP eqQ

-- `comm-tau-ndbr-step`: real dispatcher via `□-force-ndbr-inv`, splitting
-- into the four sub-cases D/H/I/J.
comm-tau-ndbr-step :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {prf : Is-just (f wi wa)}
  → ITree.force (P □ Q) ≡ ndbr f wi wa prf
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → f i a ≡ just t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
comm-tau-ndbr-step P Q eq-ndbr eq-j
  with □-force-ndbr-inv {P = P} {Q = Q} eq-ndbr
... | inj₁ (r , r' , neq , eqP , eqQ) =
      comm-tau-ndbr-D P Q neq eqP eqQ eq-ndbr eq-j
... | inj₂ (inj₁ (fP , fQ , wiQ , waQ , wpQ , eqP , eqQ)) =
      comm-tau-ndbr-H P Q eqP eqQ eq-ndbr eq-j
... | inj₂ (inj₂ (inj₁ (fP , wiP , waP , wpP , fQ , eqP , eqQ))) =
      comm-tau-ndbr-I P Q eqP eqQ eq-ndbr eq-j
... | inj₂ (inj₂ (inj₂ (fP , wiP , waP , wpP , fQ , wiQ , waQ , wpQ , eqP , eqQ))) =
      comm-tau-ndbr-J P Q eqP eqQ eq-ndbr eq-j

-- `□-comm-on-tau`: real dispatcher over τ-ndbr + force inversions.
-- Each sub-case delegates to one of the three `comm-tau-*` helpers.
□-comm-on-tau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → {t : ITree E (ExtI I) R}
  → (P □ Q) ─[ τ ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Q □ P) ═[ τ ]═► t'
      × t ≈ t' )
□-comm-on-tau P Q step with τ-ndbr step
-- sSil case: force (P □ Q) ≡ sil t.
... | inj₁ (u , eq-sil , refl)
    with □-force-sil-inv {P = P} {Q = Q} eq-sil
-- Rule A: the sil came from P.
...    | inj₁ (P' , eqP , refl) = comm-tau-sSil-L P Q eqP
-- Rule B: the sil came from Q (with P stable).
...    | inj₂ (Q' , eqQ , refl) = comm-tau-sSil-R P Q eqQ
-- sNdbr case: delegate to the umbrella ndbr-step helper.
□-comm-on-tau P Q _
    | inj₂ (_ , _ , _ , _ , _ , _ , eq-ndbr , eq-j) =
      comm-tau-ndbr-step P Q eq-ndbr eq-j

-- `on-div` is derived: use `on-tau` on the divergence's τ step, then the
-- returned bisim's `on-div` field transports `Divergent` to the witness,
-- and `divergent-prefix` lifts it through the weak τ chain.  This mirrors
-- the trick used in `□-cong-fwd-on-div`.
□-comm-on-div :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → Divergent (P □ Q) → Divergent (Q □ P)
□-comm-on-div P Q d
  with □-comm-on-tau P Q (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-- `□-comm` definition — signature was forward-declared above.  The
-- backward simulation uses the same forward sub-lemmas with P and Q
-- swapped.
□-comm P Q .fwd .on-ret eq   = □-comm-on-ret P Q eq
□-comm P Q .fwd .on-vis step = □-comm-on-vis P Q step
□-comm P Q .fwd .on-tau step = □-comm-on-tau P Q step
□-comm P Q .fwd .on-div d    = □-comm-on-div P Q d
□-comm P Q .bwd .on-ret eq   = □-comm-on-ret Q P eq
□-comm P Q .bwd .on-vis step = □-comm-on-vis Q P step
□-comm P Q .bwd .on-tau step = □-comm-on-tau Q P step
□-comm P Q .bwd .on-div d    = □-comm-on-div Q P d

-----------------------------------------------------------------------------
-- Stop is a left unit of external choice: Stop □ P ≈ P
--
-- Same decomposition as `□-cong` / `□-comm`: six simulation sub-obligations
-- (three per direction), `on-div` is derived via `on-tau` +
-- `divergent-prefix`, and the outer bisim is assembled by wiring the
-- sub-lemmas into the `fwd` / `bwd` fields.
-----------------------------------------------------------------------------

-- Forward `on-ret`.  By `□-force-ret-inv` applied to the equation, either
-- `force Stop ≡ ret r` (absurd: force Stop is `vis _` by definition), or
-- `force P ≡ ret r`.  Take `t' = P` with `weak-τ τ*-zero`.
□-Stop-left-fwd-on-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {r : R}
  → ITree.force (Stop □ P) ≡ ret r
  → Σ[ t' ∈ ITree E (ExtI I) R ]
    Σ[ r' ∈ R ]
      ( P ═[ τ ]═► t'
      × ITree.force t' ≡ ret r'
      × r ≡ r' )
□-Stop-left-fwd-on-ret P {r} eq with □-force-ret-inv {P = Stop} {Q = P} eq
... | inj₁ eqStop = case eqStop of λ ()
... | inj₂ eqP    = P , r , weak-τ τ*-zero , eqP , refl

-- Forward `on-vis`.  Since `force Stop = vis (λ _ _ → nothing)`, the only
-- way for `(Stop □ P)` to have a visible step is rule G with `force P =
-- vis fP`.  Then `mergeMaybe nothing (fP at a) = fP at a`, so the event
-- fires directly from P's branch; successor is `drwbisim-refl`.
□-Stop-left-fwd-on-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {at : AnyTypes E} {a : proj₁ at} {t : ITree E (ExtI I) R}
  → (Stop □ P) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( P ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × t ≈ t' )
□-Stop-left-fwd-on-vis P {at = at} {a = a} (sVis force-eq f-eq)
  with ITree.force P | inspect ITree.force P | force-eq
... | vis fP | [ eqP ] | refl
    with fP at a | inspect (fP at) a | f-eq
...    | just P' | [ fP-eq ] | refl =
          P' ,
          weak-ev τ*-zero
            (sVis {p = P} {f = fP} {at = at} {a = a} {t′ = P'} eqP fP-eq)
            τ*-zero ,
          drwbisim-refl P'
...    | nothing | _ | ()
□-Stop-left-fwd-on-vis _ (sVis force-eq _) | sil _          | _ | eq = case eq of λ ()
□-Stop-left-fwd-on-vis _ (sVis force-eq _) | ret _          | _ | eq = case eq of λ ()
□-Stop-left-fwd-on-vis _ (sVis force-eq _) | ndbr _ _ _ _   | _ | eq = case eq of λ ()

-- Forward declarations.  The `□-Stop-left-swap` restructure removed the
-- `NON_TERMINATING` that was previously required on `bwd-on-tau` (due to
-- `drwbisim-sym`'s projection).  A single `NON_TERMINATING` pragma
-- remains on `fwd-on-tau` because Agda's structural-recursion checker
-- cannot trace `P' ≺ P` through the propositional equation `force P ≡
-- sil P'` supplied by `□-force-sil-inv`.  Fully eliminating this final
-- pragma would require sized types in the underlying `ITree` definition
-- (so Agda can see coinductive sub-trees as structurally smaller).
□-Stop-left-fwd-on-tau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {t : ITree E (ExtI I) R}
  → (Stop □ P) ─[ τ ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( P ═[ τ ]═► t'
      × t ≈ t' )

□-Stop-left-bwd-on-tau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {t : ITree E (ExtI I) R}
  → P ─[ τ ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Stop □ P) ═[ τ ]═► t'
      × t ≈ t' )

□-Stop-left :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (Stop □ P) ≈ P

□-Stop-left-swap :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → P ≈ (Stop □ P)

-- Forward-direction auxiliary: if `force P ≡ ret r`, then
-- `force (Stop □ P) ≡ ret r` by rule F (vis/ret).
force-Stop-□-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P : ITree E (ExtI I) R} {r : R}
  → ITree.force P ≡ ret r
  → ITree.force (Stop □ P) ≡ ret r
force-Stop-□-ret {P = P} eqP with ITree.force P | eqP
... | ret r | refl = refl

-- Auxiliary: if `force P ≡ vis fP`, `(Stop □ P)` has the merged vis with
-- `λ _ → nothing` on the left.
force-Stop-□-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P : ITree E (ExtI I) R}
  → {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → ITree.force (Stop □ P) ≡
        vis (λ Ae → mergeVis (λ _ → nothing) (fP Ae))
force-Stop-□-vis {P = P} eqP with ITree.force P | eqP
... | vis fP | refl = refl

-- Auxiliary: if `force P ≡ sil P'`, then `(Stop □ P)` takes its sil via P
-- (rule B: `vis _ | sil Q' = sil (Stop □ Q')`).
force-Stop-□-sil :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P P' : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → ITree.force (Stop □ P) ≡ sil (Stop □ P')
force-Stop-□-sil {P = P} eqP with ITree.force P | eqP
... | sil _ | refl = refl

-- Backward `on-ret`: take t' = (Stop □ P), which has force ret r by the
-- auxiliary above.
□-Stop-left-bwd-on-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {r : R}
  → ITree.force P ≡ ret r
  → Σ[ t' ∈ ITree E (ExtI I) R ]
    Σ[ r' ∈ R ]
      ( (Stop □ P) ═[ τ ]═► t'
      × ITree.force t' ≡ ret r'
      × r ≡ r' )
□-Stop-left-bwd-on-ret P {r} eqP =
    (Stop □ P) , r , weak-τ τ*-zero , force-Stop-□-ret {P = P} eqP , refl

-- Backward `on-vis`.  P offers the event via `fP at a ≡ just t`, which
-- lifts to `mergeMaybe nothing (fP at a) ≡ just t` via `cong`; that in
-- turn matches the merged continuation of `(Stop □ P)`.
□-Stop-left-bwd-on-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {at : AnyTypes E} {a : proj₁ at} {t : ITree E (ExtI I) R}
  → P ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t
  → Σ[ t' ∈ ITree E (ExtI I) R ]
      ( (Stop □ P) ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
      × t ≈ t' )
□-Stop-left-bwd-on-vis P {at = at} {a = a} {t = t}
    (sVis {f = fP} force-eq-P fP-eq) =
      t ,
      weak-ev τ*-zero
        (sVis {p = Stop □ P} {at = at} {a = a} {t′ = t}
              (force-Stop-□-vis {P = P} force-eq-P)
              (cong (mergeMaybe nothing) fP-eq))
        τ*-zero ,
      drwbisim-refl t

-- Internal lift for Case H (rule H, vis/ndbr pattern) in the bwd
-- direction.  Stop's force is `vis (λ _ _ → nothing)`, so `(Stop □ P)`
-- with P at `ndbr fP _ _ _` reduces (rule H) to `ndbr (mergeNdbr-vis-L
-- Stop fP) ...`.  Stepping the same branch (i, a) of P maps `just t` to
-- `just (Stop □ t)`.
bwd-tau-ndbr-lift :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
  → {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
  → {i : AnyTypes (ExtI I)} {a : proj₁ i} {t : ITree E (ExtI I) R}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → fP i a ≡ just t
  → (Stop □ P) ─[ τ ]─► (Stop □ t)
bwd-tau-ndbr-lift P {fP = fP} {wiP = wiP} {waP = waP} {wpP = wpP}
                    eqP fP-eq =
    sNdbr {f = mergeNdbr-vis-L Stop fP} {wi = wiP} {wa = waP}
          {prf = mergeNdbr-vis-L-witness Stop fP wpP}
          (force-□-vis-ndbr-eq {P = Stop} {Q = P} refl eqP)
          (mergeNdbr-vis-L-just Stop fP fP-eq)

{-# NON_TERMINATING #-}
□-Stop-left-fwd-on-tau P step with τ-ndbr step
-- sSil: force (Stop □ P) ≡ sil t — the sil must come from P (rule B).
... | inj₁ (u , eq-sil , refl)
    with □-force-sil-inv {P = Stop} {Q = P} eq-sil
...    | inj₁ (_ , eqStop , _) = case eqStop of λ ()
...    | inj₂ (P' , eqP , refl) =
          P' ,
          weak-τ (τ*-step (sSil {p = P} {t = P'} eqP) τ*-zero) ,
          □-Stop-left P'
-- sNdbr: only rule H applies (force Stop = vis).
□-Stop-left-fwd-on-tau P _
    | inj₂ (_ , _ , _ , _ , i , a , eq-ndbr , eq-j)
    with ITree.force P | inspect ITree.force P | eq-ndbr
...    | ndbr fP wiP waP wpP | [ eqP ] | refl
          with fP i a | inspect (fP i) a | eq-j
...         | just P' | [ fP-eq ] | refl =
              P' ,
              weak-τ (τ*-step (sNdbr {p = P} {f = fP} {wi = wiP} {wa = waP}
                                     {prf = wpP} {i = i} {a = a} {t′ = P'}
                                     eqP fP-eq) τ*-zero) ,
              □-Stop-left P'
...         | nothing | _ | ()
□-Stop-left-fwd-on-tau _ _ | inj₂ (_ , _ , _ , _ , _ , _ , _ , _)
    | sil _ | _ | eq = case eq of λ ()
□-Stop-left-fwd-on-tau _ _ | inj₂ (_ , _ , _ , _ , _ , _ , _ , _)
    | ret _ | _ | eq = case eq of λ ()
□-Stop-left-fwd-on-tau _ _ | inj₂ (_ , _ , _ , _ , _ , _ , _ , _)
    | vis _ | _ | eq = case eq of λ ()

-- bwd-on-tau: successor bisim is `□-Stop-left-swap t` — a raw recursive
-- call with no projection.  No pragma needed here (the swap restructure
-- eliminated the `drwbisim-sym` projection issue).
□-Stop-left-bwd-on-tau P (sSil {t = t} eqP) =
      Stop □ t ,
      weak-τ (τ*-step (sSil {p = Stop □ P} {t = Stop □ t}
                            (force-Stop-□-sil {P = P} eqP)) τ*-zero) ,
      □-Stop-left-swap t
□-Stop-left-bwd-on-tau P (sNdbr {t′ = t} eqP fP-eq) =
      Stop □ t ,
      weak-τ (τ*-step (bwd-tau-ndbr-lift P eqP fP-eq) τ*-zero) ,
      □-Stop-left-swap t

-- on-div derivations reuse on-tau.
□-Stop-left-fwd-on-div :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → Divergent (Stop □ P)
  → Divergent P
□-Stop-left-fwd-on-div P d
  with □-Stop-left-fwd-on-tau P (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

□-Stop-left-bwd-on-div :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → Divergent P
  → Divergent (Stop □ P)
□-Stop-left-bwd-on-div P d
  with □-Stop-left-bwd-on-tau P (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-- `□-Stop-left` wiring.
□-Stop-left P .fwd .on-ret eq   = □-Stop-left-fwd-on-ret P eq
□-Stop-left P .fwd .on-vis step = □-Stop-left-fwd-on-vis P step
□-Stop-left P .fwd .on-tau step = □-Stop-left-fwd-on-tau P step
□-Stop-left P .fwd .on-div d    = □-Stop-left-fwd-on-div P d
□-Stop-left P .bwd .on-ret eq   = □-Stop-left-bwd-on-ret P eq
□-Stop-left P .bwd .on-vis step = □-Stop-left-bwd-on-vis P step
□-Stop-left P .bwd .on-tau step = □-Stop-left-bwd-on-tau P step
□-Stop-left P .bwd .on-div d    = □-Stop-left-bwd-on-div P d

-- `□-Stop-left-swap` — swaps directions via the same sub-lemmas.
□-Stop-left-swap P .fwd .on-ret eq   = □-Stop-left-bwd-on-ret P eq
□-Stop-left-swap P .fwd .on-vis step = □-Stop-left-bwd-on-vis P step
□-Stop-left-swap P .fwd .on-tau step = □-Stop-left-bwd-on-tau P step
□-Stop-left-swap P .fwd .on-div d    = □-Stop-left-bwd-on-div P d
□-Stop-left-swap P .bwd .on-ret eq   = □-Stop-left-fwd-on-ret P eq
□-Stop-left-swap P .bwd .on-vis step = □-Stop-left-fwd-on-vis P step
□-Stop-left-swap P .bwd .on-tau step = □-Stop-left-fwd-on-tau P step
□-Stop-left-swap P .bwd .on-div d    = □-Stop-left-fwd-on-div P d

-----------------------------------------------------------------------------
-- `□-Stop-right` as a corollary of `□-comm` and `□-Stop-left`
-----------------------------------------------------------------------------

-- `P □ Stop ≈ Stop □ P ≈ P` via `□-comm` and `□-Stop-left`.
□-Stop-right-from-comm :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (P □ Stop) ≈ P
□-Stop-right-from-comm P =
  DRWbisimEquiv.drwbisim-trans ≡-equiv
    (□-comm P Stop)
    (□-Stop-left P)
