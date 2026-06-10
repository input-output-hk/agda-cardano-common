{-
  External-choice laws for ITree-CSP under failures-divergences
  equivalence `_≃FD_`.

  This file is being grown incrementally toward a full proof of

      □-idem-FD :  P □ P  ≃FD  P

  Session 1 (already landed) proved the **immediate-refusal iff** for
  the `P = Q` specialisation, in BOTH directions:

      P-ref→PP-ref  :  P ref B  →  (P □ P) ref B
      PP-ref→P-ref  :  (P □ P) ref B  →  P ref B
      □P-ref-iff    : combined as a `×`-pair.

  These are foundations — `P-ref→PP-ref` lifts a refusal of `P` to one
  of `P □ P` via the `vis/vis` and `ret/ret-equal` rules of `_□_`;
  `PP-ref→P-ref` projects back via `□-force-vis-inv`/`□-force-ret-inv`
  plus the `mergeMaybe x x ≡ nothing ⇒ x ≡ nothing` self-collapse.

  `□-idem-FD` itself remains a `postulate` for now.  The remaining work
  is the bigstep simulation that walks an arbitrary trace through the
  asymmetric `_□_` τ-tree (sessions 2–4 in the original plan).  See the
  comment at the postulate site for the structure.
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; inspect; [_])
open import Data.Maybe.Properties using (just-injective)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)

open import Class.DecEq using (DecEq; _≟_)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open import ITree_Relations.DRWeakBisim using (_≈_)
open import ITree_Relations.FailuresDivergencesEquiv

module CSP.Laws.ExternalChoice_FD
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open ITree
open Failures

-----------------------------------------------------------------------------
-- Laws lifted from DRWbisim via `≈⇒≃FD`.
--
-- Whatever holds under `≈` (e.g. `□-comm`) lifts immediately.  The
-- harder cases — `□-idem`, `□-assoc`, `□-⊓-distrib` — are NOT bisim
-- laws and need direct FD proofs.
-----------------------------------------------------------------------------

import CSP.Laws.ExternalChoice_DRBisim {ℓ} {ℓe} {E} as □-bisim-laws
open □-bisim-laws E-≟ using
  ( □-force-vis-inv
  ; □-force-ret-inv
  ; □-force-sil-inv
  ; □-force-ndbr-inv
  ; force-□-vis-vis
  ; force-□-ndbr-D
  ; force-□-vis-ndbr-eq
  ; force-□-ndbr-vis-eq
  ; force-□-ndbr-ndbr-eq
  ; force-□-mix-mix-mix
  ; force-□-ret-ndbr-eq
  ; force-□-ndbr-ret-eq
  ; force-□-mix-ndbr-eq
  ; force-□-ndbr-mix-eq
  ; mergeNdbr-vis-L-just
  ; mergeNdbr-vis-R-just
  ; mergeNdbr-pair-jj
  ; mergeNdbr-pair-jn
  ; mergeNdbr-pair-nj
  )
  renaming (□-comm to □-comm-≈)

import CSP.Laws.InternalChoice_FD {ℓ} {ℓe} {E} as ⊓-FD-laws
open ⊓-FD-laws E-≟ using (⊓-idem-FD; ⊓-step-L; ⊓-step-R; ⊓-failures-elim; ⊓-divergences-elim)

□-comm-FD :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q : ITree E (ExtI I) R)
  → _≃FD_ {ℓB = ℓB} (P □ Q) (Q □ P)
□-comm-FD P Q = ≈⇒≃FD (□-comm-≈ P Q)

-----------------------------------------------------------------------------
-- Session 1: empty-trace immediate-refusal iff for `P □ P`.
--
-- Specialisation of the `_□_` LTS rules to `P = Q`: the asymmetric
-- cases (`vis/ndbr`, `ndbr/vis`, `ret/ret-different`) are unreachable
-- because both operands have the same `force`.  Only four rule cases
-- need to be handled:
--   • `vis/vis`     : `force (P □ P) = vis (mergeVis fP fP)` (stable).
--   • `ret/ret-eq`  : `force (P □ P) = ret r`                (✓-step).
--   • `sil-left`    : `force (P □ P) = sil (P' □ P)`         (τ-only).
--   • `ndbr/ndbr`   : `force (P □ P) = ndbr (mergeNdbr fP fP) …`.
--
-- Sessions 2–4 will reuse these.
-----------------------------------------------------------------------------

-- mergeMaybe is "self-nothing": for any `x : Maybe _`,
--   `mergeMaybe x x ≡ nothing`  iff  `x ≡ nothing`.
-- (The `just`/`just` case yields `just (p ⊓ p)`, not `nothing`.)
mergeMaybe-self-nothing→nothing :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {x : Maybe (ITree E (ExtI I) R)}
  → mergeMaybe x x ≡ nothing → x ≡ nothing
mergeMaybe-self-nothing→nothing {x = nothing} _    = refl
mergeMaybe-self-nothing→nothing {x = just _}  ()

mergeMaybe-nothing→self-nothing :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {x : Maybe (ITree E (ExtI I) R)}
  → x ≡ nothing → mergeMaybe x x ≡ nothing
mergeMaybe-nothing→self-nothing refl = refl

-- Construction: if `force P ≡ ret r` then `force (P □ P) ≡ ret r`
-- (the `ret/ret-equal` rule of `_□_`, where `r ≟ r` always succeeds).
force-□-ret-ret-eq :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P : ITree E (ExtI I) R} {r : R}
  → ITree.force P ≡ ret r
  → ITree.force (P □ P) ≡ ret r
force-□-ret-ret-eq {P = P} eq with ITree.force P | eq
... | sil _        | ()
... | vis _        | ()
... | ndbr _ _ _ _ | ()
... | ret r        | refl with r ≟ r
...   | yes refl = refl
...   | no neq   = ⊥-elim (neq refl)

-- Force is `vis` ⇒ tree is stable (re-derived locally; `force-vis→isStable`
-- in `DRWeakBisim.Preservation` is a private/parametrised copy).
force-vis→stable :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t : ITree E (ExtI I) R} {f}
  → ITree.force t ≡ vis f
  → isStable t
force-vis→stable {t = t} eq with ITree.force t | eq
... | vis _        | _   = _   -- ⊤
... | ret _        | ()
... | sil _        | ()
... | ndbr _ _ _ _ | ()

-- Inverse: a stable tree's force is `vis _` (extracted with the
-- continuation map made explicit).  Used by `PP-ref→P-ref`.
stable→force-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t : ITree E (ExtI I) R}
  → isStable t
  → Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))) ]
    ITree.force t ≡ vis f
stable→force-vis {t = t} st with ITree.force t
... | vis f        = f , refl

-----------------------------------------------------------------------------
-- The iff itself.
--
-- Forward (P → P □ P): a refusal of P promotes to a refusal of P □ P.
--   • ref-stable: `mergeMaybe nothing nothing = nothing`, so `mergeVis fP fP`
--     refuses every event refused by `fP`.  P □ P is stable (vis-shaped).
--   • ref-tick: P does √r at `force P ≡ ret r`; force (P □ P) ≡ ret r by
--     `force-□-ret-ret-eq`, so P □ P does √r too.
--
-- Backward (P □ P → P): a refusal of P □ P descends to a refusal of P.
--   • ref-stable: by `□-force-vis-inv`, force P ≡ vis fP and the merged
--     map is `mergeVis fP fP`.  If `mergeVis fP fP at = nothing` for an
--     event refused by P □ P, then by `mergeMaybe-self-nothing→nothing`
--     we have `fP at = nothing`.
--   • ref-tick: by `□-force-ret-inv` for P=Q=P, force P ≡ ret r.  The
--     inversion returns `inj₁` or `inj₂` but both unify to the same
--     equation since both sides are P.
-----------------------------------------------------------------------------

-- A short helper that handles the productive-merge inversion: given
-- `mergeMaybe (fP at a) (fP at a) ≡ just T'` for some T', produce
-- the original `fP at a` value as a `just`.
refuse-vis-stable-inv :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {at : AnyTypes E} {a : proj₁ at} {T : ITree E (ExtI I) R}
  → mergeMaybe (fP at a) (fP at a) ≡ just T
  → Σ[ t ∈ ITree E (ExtI I) R ] (fP at a ≡ just t)
refuse-vis-stable-inv {fP = fP} {at = at} {a = a} m-eq
  with fP at a | m-eq
... | just t  | _ = t , refl
... | nothing | ()

P-ref→PP-ref :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {B : Event√ E R → Set ℓB}
  → P ref B
  → (P □ P) ref B
-- ref-tick path: P does √r, force P ≡ ret r ⇒ force (P □ P) ≡ ret r
-- by `force-□-ret-ret-eq`, so P □ P also does √r.
P-ref→PP-ref {P = P} (ref-tick {x = x} (sRet eq) ¬Bx) =
    ref-tick {P = P □ P} {x = x}
             (sRet {p = P □ P} (force-□-ret-ret-eq {P = P} eq))
             ¬Bx
-- ref-stable path: P stable + refuses B ⇒ P □ P stable + refuses B.
P-ref→PP-ref {I = I} {R = R} {P = P} (ref-stable {P = .P} {B = B} st refuses)
  with ITree.force P | inspect ITree.force P
... | ret _        | _      = case st of λ ()
... | sil _        | _      = case st of λ ()
... | ndbr _ _ _ _ | _      = case st of λ ()
... | vis fP       | [ eq ] =
    ref-stable {P = P □ P}
      (force-vis→stable {t = P □ P} eqPP)
      refuses-PP
  where
    eqPP : ITree.force (P □ P) ≡ vis (λ ae → mergeVis (fP ae) (fP ae))
    eqPP = force-□-vis-vis {P = P} {Q = P} {fP = fP} {fQ = fP} eq eq

    -- A visible step out of P □ P at event e is forced (by force-□-vis-vis)
    -- to come from `vis (mergeVis fP fP)` and to land at the productive
    -- value of `mergeMaybe (fP at a) (fP at a)`.  By
    -- `refuse-vis-stable-inv`, this productivity implies `fP at a = just _`,
    -- which we feed back to the original `refuses e Be (sVis eq …)` to
    -- derive ⊥.
    refuses-PP : ∀ e → B e → ∀ {Q : ITree E (ExtI I) R}
               → ¬ ((P □ P) ─[ ev e ]─► Q)
    refuses-PP e Be (sRet sR-eq) =
        case trans (sym eqPP) sR-eq of λ ()
    refuses-PP e Be (sVis {at = at} {a = a} sV-eq f-eq)
      with trans (sym eqPP) sV-eq
    ... | refl with refuse-vis-stable-inv {fP = fP} {at = at} {a = a} f-eq
    ...   | _ , fP-eq = refuses e Be (sVis {p = P} eq fP-eq)
    -- sMixVis: force(P □ P) ≡ mix _ _ contradicts the established vis-shape.
    refuses-PP e Be (sMixVis sM-eq _) =
        case trans (sym eqPP) sM-eq of λ ()

-- Backward direction (P □ P → P).
--
-- ref-tick: by `□-force-ret-inv` for `P=Q=P` (both `inj₁` and `inj₂`
-- give the same equation), force P ≡ ret r so P does √r.
--
-- ref-stable: from `isStable (P □ P)` get `force (P □ P) ≡ vis f-PP`
-- via `stable→force-vis`, then `□-force-vis-inv` gives
-- `force P ≡ vis fP`, `force P ≡ vis fQ`, and
-- `f-PP ≡ mergeVis fP fQ`.  Both equations come from the same `force P`,
-- so `vis-injective` collapses `fP ≡ fQ`.  A visible step on P at event
-- `(at, a)` with `fP at a ≡ just Q'` lifts to a visible step on P □ P at
-- the same event landing at `Q' ⊓ Q'` (since `mergeMaybe (just Q')
-- (just Q') = just (Q' ⊓ Q')`), which `refuses e Be` rules out.
PP-ref→P-ref :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {B : Event√ E R → Set ℓB}
  → (P □ P) ref B
  → P ref B
PP-ref→P-ref {P = P} (ref-tick {x = x} (sRet eq) ¬Bx)
  with □-force-ret-inv {P = P} {Q = P} eq
... | inj₁ eqP = ref-tick {P = P} {x = x} (sRet {p = P} eqP) ¬Bx
... | inj₂ eqP = ref-tick {P = P} {x = x} (sRet {p = P} eqP) ¬Bx
PP-ref→P-ref {I = I} {R = R} {P = P}
             (ref-stable {P = .(P □ P)} {B = B} st refuses)
  with stable→force-vis {t = P □ P} st
... | f-PP , eqPP-vis
  with □-force-vis-inv {P = P} {Q = P} {f = f-PP} eqPP-vis
... | fP , fQ , eqP , eqQ , merge-eq =
    ref-stable {P = P}
      (force-vis→stable {t = P} eqP)
      refuses-P
  where
    fP≡fQ : fP ≡ fQ
    fP≡fQ = vis-injective (trans (sym eqP) eqQ)

    refuses-P : ∀ e → B e → ∀ {Q : ITree E (ExtI I) R}
              → ¬ (P ─[ ev e ]─► Q)
    refuses-P e Be (sRet sR-eq) =
        case trans (sym eqP) sR-eq of λ ()
    refuses-P e Be {Q = Q'} (sVis {at = at} {a = a} sV-eq fP-eq)
      with trans (sym eqP) sV-eq
    ... | refl = refuses e Be (sVis {p = P □ P} eqPP-vis merged-just)
      where
        -- After merge-eq → sym fP≡fQ → fP-eq, the goal reduces to
        -- `mergeMaybe (just Q') (just Q') ≡ just (Q' ⊓ Q')`, which
        -- holds definitionally.
        merged-just : f-PP at a ≡ just (Q' ⊓ Q')
        merged-just rewrite merge-eq | sym fP≡fQ | fP-eq = refl
    -- sMixVis: force P ≡ mix _ _ contradicts established vis-shape of P.
    refuses-P e Be (sMixVis sM-eq _) =
        case trans (sym eqP) sM-eq of λ ()

-- The session-1 iff combinator: bundles both directions.
□P-ref-iff :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {B : Event√ E R → Set ℓB}
  → ((P □ P) ref B → P ref B) × (P ref B → (P □ P) ref B)
□P-ref-iff = PP-ref→P-ref , P-ref→PP-ref

-----------------------------------------------------------------------------
-- Session 2: visible-step continuation lemma for `P □ P`.
--
--    □P-step-cont :  (P □ P) ─[ev e]─► T
--                 →  ∃ t. P ─[ev e]─► t  ×  T ≃FD t
--
-- Cases:
--   • `sRet eq` (e = √r, T = deadlock):  by `□-force-ret-inv`,
--     `force P ≡ ret r`, so P also does √r.  `t = T = deadlock`,
--     `T ≃FD t` is reflexivity.
--
--   • `sVis sV-eq f-eq` (e = evl …, T = continuation):  by
--     `□-force-vis-inv`, `force P ≡ vis fP` (and `≡ vis fQ`, with
--     `fP ≡ fQ` by `vis-injective`).  The merged map at `(at, a)` is
--     `mergeMaybe (fP at a) (fQ at a)`, which under `f-eq : … ≡ just T`
--     forces `fP at a = just p` for some `p` (the `nothing` case
--     yields `mergeMaybe nothing nothing = nothing ≢ just T`).  Then
--     `T = mergeMaybe (just p) (just p) = just (p ⊓ p)`, so `T ≡ p ⊓ p`,
--     and `T ≃FD p` follows from `⊓-idem-FD`.
-----------------------------------------------------------------------------

□P-step-cont :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {e : Event√ E R} {T : ITree E (ExtI I) R}
  → (P □ P) ─[ ev e ]─► T
  → Σ[ t ∈ ITree E (ExtI I) R ]
      ((P ─[ ev e ]─► t) × (_≃FD_ {ℓB = ℓB} T t))
-- sRet case: force (P □ P) ≡ ret r.  By inversion, force P ≡ ret r,
-- so P also fires √r.  Both destinations are `deadlock`, so the FD
-- relation is reflexive.
□P-step-cont {P = P} (sRet eq)
  with □-force-ret-inv {P = P} {Q = P} eq
... | inj₁ eqP = deadlock , sRet {p = P} eqP , ≃FD-refl
... | inj₂ eqP = deadlock , sRet {p = P} eqP , ≃FD-refl

-- sVis case: force (P □ P) ≡ vis f.  By inversion, force P ≡ vis fP,
-- force P ≡ vis fQ, and `f ≡ mergeVis fP fQ`.  The two equations on
-- `force P` give `fP ≡ fQ` by `vis-injective`.  Case on `fP at a`:
-- nothing leads to `mergeMaybe nothing nothing = nothing` ≢ just T
-- (absurd); just p gives `T = p ⊓ p`, and `p ⊓ p ≃FD p` is `⊓-idem-FD`.
□P-step-cont {P = P} (sVis {f = f} {at = at} {a = a} sV-eq f-eq)
  with □-force-vis-inv {P = P} {Q = P} {f = f} sV-eq
... | fP , fQ , eqP , eqQ , merge-eq
  with fP at a | inspect (fP at) a
... | nothing | [ fP-noth ] = ⊥-elim (case f-noth-vs-just of λ ())
  where
    fP≡fQ : fP ≡ fQ
    fP≡fQ = vis-injective (trans (sym eqP) eqQ)
    fQ-noth : fQ at a ≡ nothing
    fQ-noth = subst (λ g → g at a ≡ nothing) fP≡fQ fP-noth
    -- f at a ≡ mergeMaybe (fP at a) (fQ at a) ≡ mergeMaybe nothing nothing
    --       = nothing
    f-at-noth : f at a ≡ nothing
    f-at-noth = trans (cong (λ g → g at a) merge-eq)
                      (cong₂ mergeMaybe fP-noth fQ-noth)
    f-noth-vs-just : nothing ≡ just _
    f-noth-vs-just = trans (sym f-at-noth) f-eq
... | just p | [ fP-eq ] =
        p , sVis {p = P} eqP fP-eq , T≃FD-p
  where
    fP≡fQ : fP ≡ fQ
    fP≡fQ = vis-injective (trans (sym eqP) eqQ)
    -- fQ at a = fP at a = just p
    fQ-eq : fQ at a ≡ just p
    fQ-eq = subst (λ g → g at a ≡ just p) fP≡fQ fP-eq
    -- After merge-eq, f at a = mergeMaybe (fP at a) (fQ at a)
    --                       = mergeMaybe (just p) (just p)
    --                       = just (p ⊓ p).
    -- Combined with f-eq : f at a ≡ just T:  just (p ⊓ p) ≡ just T,
    -- hence p ⊓ p ≡ T.
    merge-just : f at a ≡ just (p ⊓ p)
    merge-just = trans (cong (λ g → g at a) merge-eq)
                       (cong₂ mergeMaybe fP-eq fQ-eq)
    p⊓p≡T : p ⊓ p ≡ _
    p⊓p≡T = just-injective (trans (sym merge-just) f-eq)
    -- T ≃FD p:  rewrite T as p ⊓ p, then apply ⊓-idem-FD.
    T≃FD-p : _ ≃FD p
    T≃FD-p = subst (λ x → x ≃FD p) p⊓p≡T (⊓-idem-FD p)

-- sMixVis case: force (P □ P) ≡ mix _ _.  By the (5×5) reduction rules of
-- `_□_`, P □ P can be `mix` only when P itself is `mix` (the only
-- self-paired case among the 7 mix-producing rules is `mix | mix`).  But
-- under that scenario `force P ≡ mix _ _` too, and we can fire `sMixVis`
-- on P directly to get the same continuation.  The merged vis function
-- `mergeVis fP fP` at `a` reduces to `mergeMaybe (fP at a) (fP at a)`,
-- collapsing by `mergeMaybe-idem`-style argument to `just (p ⊓ p)` when
-- both equal `just p`.  ⊓-idem-FD then gives `T ≃FD p`.
□P-step-cont {P = P} (sMixVis {f = f} {at = at} {a = a} sM-eq f-eq)
  with ITree.force P | inspect ITree.force P | sM-eq
... | mix fP P' | [ eqP ] | refl with fP at a in fP-eq | f-eq
...    | nothing | ()
...    | just p  | refl =
         p , sMixVis {p = P} {f = fP} {Qt = P'} eqP fP-eq , T≃FD-p
  where
    -- For P=mix fP P' and Q=P, the rule "mix | mix" yields
    --   force(P □ P) = mix (λ Ae → mergeVis (fP Ae) (fP Ae)) (P' □ P')
    -- so f = λ Ae → mergeVis (fP Ae) (fP Ae); at `a` this is mergeMaybe
    -- (fP at a) (fP at a) = mergeMaybe (just p) (just p) = just (p ⊓ p).
    -- Combined with f-eq, the target is `p ⊓ p`, which is ≃FD p by ⊓-idem-FD.
    T≃FD-p : _ ≃FD p
    T≃FD-p = ⊓-idem-FD p
-- Other force shapes don't reduce force(P □ P) to mix.
□P-step-cont {P = P} (sMixVis sM-eq _) | sil _    | _ | ()
□P-step-cont {P = P} (sMixVis sM-eq _) | ret r    | _ | sM-eq' with r ≟ r
... | yes refl = case sM-eq' of λ ()
... | no  neq  = ⊥-elim (neq refl)
□P-step-cont {P = P} (sMixVis sM-eq _) | vis _    | _ | ()
□P-step-cont {P = P} (sMixVis sM-eq _) | ndbr _ _ _ _ | _ | ()

-----------------------------------------------------------------------------
-- Force-unfolding helpers for `_□_`'s sil rules.
--
--   • `sil-left`  always fires when force LEFT = sil.
--   • `sil-right` fires when force LEFT = ret/vis/ndbr AND force RIGHT = sil.
--
-- The four `force-□-sil-{left,right-{ret,vis,nbr}}` lemmas below are
-- the unfolding helpers for these LTS rules.  The three
-- `sync-sil-{ret,vis,ndbr}` lemmas combine them for the case where
-- `force P' ∈ {ret r, vis _, ndbr _ _ _ _}` after one `sil-left`,
-- giving a 2-step τ*-chain `(P □ P) ─[τ*]─► (P' □ P')`.
--
-- The general τ*-chain `(P □ P) ─[τ*]─► (Z □ Z)` for arbitrary chain
-- depth is realised by `walk-PP-asymm-LEFT` / `walk-PP-asymm-RIGHT`
-- further below, which terminate by structural recursion on the bigstep
-- / sSil*-chain (no `walk-left-to-stable`-style coinductive descent).
-----------------------------------------------------------------------------

-- sil-left rule unfolding.
force-□-sil-left :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P P' Q : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → ITree.force (P □ Q) ≡ sil (P' □ Q)
force-□-sil-left {P = P} {Q = Q} eq with ITree.force P | eq
... | sil _ | refl = refl

-- sil-right rule unfoldings, one per non-sil shape of LEFT.
force-□-sil-right-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q Q' : ITree E (ExtI I) R} {r : R}
  → ITree.force P ≡ ret r
  → ITree.force Q ≡ sil Q'
  → ITree.force (P □ Q) ≡ sil (P □ Q')
force-□-sil-right-ret {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ret _ | refl | sil _ | refl = refl

force-□-sil-right-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q Q' : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ vis fP
  → ITree.force Q ≡ sil Q'
  → ITree.force (P □ Q) ≡ sil (P □ Q')
force-□-sil-right-vis {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | vis _ | refl | sil _ | refl = refl

force-□-sil-right-ndbr :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q Q' : ITree E (ExtI I) R}
    {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (fP wi wa)}
  → ITree.force P ≡ ndbr fP wi wa wp
  → ITree.force Q ≡ sil Q'
  → ITree.force (P □ Q) ≡ sil (P □ Q')
force-□-sil-right-ndbr {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | ndbr _ _ _ _ | refl | sil _ | refl = refl

-- New under post-mix `_□_`: mix on the left, sil on the right.
force-□-sil-right-mix :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P Q Q' : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {Pt : ITree E (ExtI I) R}
  → ITree.force P ≡ mix fP Pt
  → ITree.force Q ≡ sil Q'
  → ITree.force (P □ Q) ≡ sil (P □ Q')
force-□-sil-right-mix {P = P} {Q = Q} eqP eqQ
  with ITree.force P | eqP | ITree.force Q | eqQ
... | mix _ _ | refl | sil _ | refl = refl

-- 2-step sync helpers: when `force P = sil P'` and `force P'` is non-sil,
-- the chain `(P □ P) ─[τ*]─► (P' □ P')` is `sil-left + sil-right`.
-- These are non-recursive and terminate trivially.
sync-sil-ret :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P P' : ITree E (ExtI I) R} {r : R}
  → ITree.force P ≡ sil P'
  → ITree.force P' ≡ ret r
  → (P □ P) ─[τ*]─► (P' □ P')
sync-sil-ret {P = P} {P' = P'} eqP eqP' =
    τ*-step (sSil {p = P □ P} (force-□-sil-left {P = P} {Q = P} eqP))
            (τ*-step (sSil {p = P' □ P}
                           (force-□-sil-right-ret {P = P'} {Q = P} eqP' eqP))
                     τ*-zero)

sync-sil-vis :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P P' : ITree E (ExtI I) R}
    {fP' : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ITree.force P ≡ sil P'
  → ITree.force P' ≡ vis fP'
  → (P □ P) ─[τ*]─► (P' □ P')
sync-sil-vis {P = P} {P' = P'} eqP eqP' =
    τ*-step (sSil {p = P □ P} (force-□-sil-left {P = P} {Q = P} eqP))
            (τ*-step (sSil {p = P' □ P}
                           (force-□-sil-right-vis {P = P'} {Q = P} eqP' eqP))
                     τ*-zero)

sync-sil-ndbr :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → {P P' : ITree E (ExtI I) R}
    {fP' : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (fP' wi wa)}
  → ITree.force P ≡ sil P'
  → ITree.force P' ≡ ndbr fP' wi wa wp
  → (P □ P) ─[τ*]─► (P' □ P')
sync-sil-ndbr {P = P} {P' = P'} eqP eqP' =
    τ*-step (sSil {p = P □ P} (force-□-sil-left {P = P} {Q = P} eqP))
            (τ*-step (sSil {p = P' □ P}
                           (force-□-sil-right-ndbr {P = P'} {Q = P} eqP' eqP))
                     τ*-zero)

-----------------------------------------------------------------------------
-- General sync helper for arbitrary depth of sil-chain.
-- Two phases:
--   Phase 1 (walk-left): take repeated `sil-left` τ-steps on the left
--       copy, advancing `(X □ Y) → (X' □ Y) → … → (X-stable □ Y)`.
--   Phase 2 (walk-right): from `(X-stable □ Y)` with `force X-stable`
--       non-sil, take repeated `sil-right` τ-steps on the right copy,
--       ending at `(X-stable □ X-stable)`.
--
-- The plain recursive form below would diverge for divergent `X`
-- (`div = sil div`), so it CANNOT typecheck as a total function in
-- vanilla Agda — it would require either:
--   (a) a `NON_TERMINATING` / `TERMINATING` pragma (currently disallowed
--       in this file), or
--   (b) a termination witness, e.g. add a parameter
--       `Stabilises X` (a finite proof that `X` reaches a non-sil
--       τ*-derivative) and structurally recurse on it, or
--   (c) `--sized-types`.
--
-- The actual proofs in this file use `walk-PP-asymm-LEFT` /
-- `walk-PP-asymm-RIGHT` instead, which structurally recurse on the
-- failure's bigstep (always finite) — so this helper is preserved here
-- for future reuse but kept commented.

{-
walk-left-to-stable :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (X Y : ITree E (ExtI I) R)
  → Σ[ X-stable ∈ ITree E (ExtI I) R ]
      ((X □ Y) ─[τ*]─► (X-stable □ Y))
      × (X ─[τ*]─► X-stable)
walk-left-to-stable X Y with ITree.force X | inspect ITree.force X
... | ret _        | _      = X , τ*-zero , τ*-zero
... | vis _        | _      = X , τ*-zero , τ*-zero
... | ndbr _ _ _ _ | _      = X , τ*-zero , τ*-zero
... | sil X'       | [ eq ]
    with walk-left-to-stable X' Y
... | X-stable , chain-XY , chain-X =
        X-stable ,
        τ*-step (sSil {p = X □ Y}
                      (force-□-sil-left {P = X} {P' = X'} {Q = Y} eq))
                chain-XY ,
        τ*-step (sSil {p = X} eq) chain-X
-}

-----------------------------------------------------------------------------
-- Idempotence of external choice (FD).
--
--     □-idem-FD :  P □ P  ≃FD  P
--
-- Proof plan (postulated for now — see TODO at bottom).
--
-- The key obstruction to a `≈`-proof is that for `force P = ndbr fP …`,
-- the operator `_□_` produces
--
--     force (P □ P) = ndbr (mergeNdbr fP fP) ((Aₚ × Aₚ) , pair iₚ iₚ) …
--
-- whose τ-successors range over the *Cartesian product* of P's branches:
--
--     mergeNdbr fP fP (pair iₚ iQ) (aₚ , aQ) = just (Pᵢ □ Pⱼ)
--
-- For `i ≠ j` this `Pᵢ □ Pⱼ` is not bisim to any single derivative of P,
-- so coinductive bisim closes only on the diagonal.
--
-- In `_≃FD_` the cross-products are absorbed because every τ-derivative
-- of `Pᵢ □ Pⱼ` is also a τ-derivative of P (just by picking either
-- side's derivative), so they have the same `failures⊥` and
-- `divergences` sets.  But to *prove* this we need:
--
-- 1. A general `□`-failures characterisation lemma:
--
--      failures (P □ Q) s B
--        ↔
--      • (s = []) ∧ refusal-of-(P □ Q) initially refuses B
--          (which decomposes into stable-cases on `force P` × `force Q`,
--           plus the `ret r | ret r' | r ≟ r'` subcase, plus all of the
--           `mergeMaybe`-stable visibles), or
--      • (s starts with `evl ev` AT a productive `mergeVis`-entry, and
--          the residual is a failure of `t ⊓ t'` for the merged
--          continuations), or
--      • (s starts with `√r`  AT a `force=ret r` side), or
--      • (s starts with τ-padding, dispatching on the four sil/ret/vis/ndbr
--          cases of `force P` and `force Q` in the `_□_` LTS).
--
--    This is the workhorse — ~150 to 300 lines.  It's the same lemma
--    needed by `□-Stop-left-FD`, `□-assoc-FD`, `□-⊓-distrib-FD`, etc.,
--    so once written it pays for itself across the algebra.
--
-- 2. A general `□`-divergences characterisation lemma (smaller, similar
--    shape).
--
-- 3. **`⊓-idem-FD`** (already available — we lift it from bisim in
--    `CSP.Laws.InternalChoice_FD`).  Used to discharge the
--    `vis fP | vis fP` post-event continuation `t ⊓ t ≃FD t`.
--
-- With those in hand, `□-idem-FD` is a one-line specialisation of the
-- characterisation to `Q = P`:
--
--   • Empty trace:   refusal-of-(P □ P)  ≃ refusal-of-P
--                    (mergeMaybe (fP x) (fP x) = nothing iff fP x = nothing).
--   • Visible-event continuation:  t ⊓ t ≃FD t   (⊓-idem-FD).
--   • τ-prefixes:  (P' □ P) and (P □ P') decompose recursively, with
--     the cross-branch case `P_i □ P_j` (i ≠ j) absorbed because both
--     `failures(P_i)` and `failures(P_j)` are subsets of `failures(P)`.
--
-- Recommended next step: build the `□`-failures characterisation in a
-- separate file (e.g. `CSP/Laws/ExternalChoice_FD_Characterisation.agda`),
-- discharge `□-idem-FD` here, then leverage the same lemma to discharge
-- the other postulates in `CSP.Laws.ExternalChoice_DRBisim` (which are
-- about `≈` but most lift to `≃FD`).
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- Session 3: assemble `□-idem-FD` from four sub-lemmas.
--
-- The four sub-lemmas are the pointwise inclusions for failures and
-- divergences in both directions.  We prove the simple cases (bNil for
-- failures, both directions) using sessions 1+2's helpers, and leave
-- the bigstep-recursion-heavy cases (bTau, plus full divergence
-- handling) as `postulate` blocks with detailed sub-comments.  Granular
-- postulates make subsequent sessions pickup-ready: each postulate has
-- a clear pre/post-condition and a documented strategy.
--
-- Helpers used:
--   • `P-ref→PP-ref`, `PP-ref→P-ref` (session 1) — refusal iff at force.
--   • `□P-step-cont`                  (session 2) — visible-step lift+cont.
--   • `⊓-idem-FD`                     (lifted from bisim) — t ⊓ t ≃FD t.
-----------------------------------------------------------------------------

-- Forward (lift):  failures P s B → failures (P □ P) s B.
-- The bNil + bStep cases are proved using session 1+2 helpers.
-- bTau (sNdbr) is proved via the diagonal `mergeNdbr` step.
-- bTau (sSil) is postulated — see comment at the postulate site.
-- The three are mutually defined since `failures-lift-PP-bTau-sNdbr`
-- recursively calls `failures-lift-PP` on the post-step subtree.

-- Forward declaration of `failures-lift-PP` to allow the
-- `failures-lift-PP-bTau-sNdbr` definition (which references it) to
-- come first.
failures-lift-PP :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures P s B → failures (P □ P) s B

-----------------------------------------------------------------------------
-- Synchronisation infrastructure for the asymmetric `_□_` cases.
--
-- Used to discharge the bTau / sSil case of `failures-lift-PP`.
--
-- Challenge: after `(P □ P) ─[sil-LEFT]─► (P' □ P)` (from
-- `force P ≡ sil P'`), the right copy lags.  Recovering the symmetric
-- `(Ys □ Ys)` requires walking both copies through their τ-chain — but
-- if `force P'` is itself `sil`, the next `sil-RIGHT` step is blocked,
-- and we must walk further to the first non-sil τ*-derivative.
--
-- All helpers below terminate by structural recursion (no pragma):
-- `walk-and-peel` recurses on the bigstep, `left-walk-□` /
-- `right-walk-□` on the chain.
-----------------------------------------------------------------------------

-- A τ*-chain restricted to `sSil` steps only.  An `sNdbr` step on the
-- right copy can't be replayed by `sil-RIGHT` when the left is e.g.
-- `ret`-shaped (the merger blocks), so we keep the chain sSil-only.
data _─[sSil*]─►_ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                : ITree E (ExtI I) R → ITree E (ExtI I) R
                → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  sSil*-zero : ∀ {t} → t ─[sSil*]─► t
  sSil*-step : ∀ {t t' t''}
             → ITree.force t ≡ sil t'
             → t' ─[sSil*]─► t''
             → t  ─[sSil*]─► t''

-- Concatenate two τ*-chains.
τ*-trans :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t t' t'' : ITree E (ExtI I) R}
  → t ─[τ*]─► t' → t' ─[τ*]─► t'' → t ─[τ*]─► t''
τ*-trans τ*-zero       q = q
τ*-trans (τ*-step s p) q = τ*-step s (τ*-trans p q)

-- Prepend a τ*-chain to a bigstep, materialising each τ-step as `bTau`.
τ*-prepend-bigstep :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t t' t'' : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → t ─[τ*]─► t' → t' ═⟨ s ⟩═► t'' → t ═⟨ s ⟩═► t''
τ*-prepend-bigstep τ*-zero       bs = bs
τ*-prepend-bigstep (τ*-step s p) bs = bTau s (τ*-prepend-bigstep p bs)

-- Shape witness for non-sil `ITree.force` — pattern-dispatched in
-- `right-walk-□`.
data NonSilForce {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               : ITree E (ExtI I) R
               → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  nsf-ret  : ∀ {t : ITree E (ExtI I) R} {r : R}
           → ITree.force t ≡ ret r
           → NonSilForce t
  nsf-vis  : ∀ {t : ITree E (ExtI I) R}
             {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
           → ITree.force t ≡ vis f
           → NonSilForce t
  nsf-ndbr : ∀ {t : ITree E (ExtI I) R}
             {f  : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
             {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f wi wa)}
           → ITree.force t ≡ ndbr f wi wa wp
           → NonSilForce t
  nsf-mix  : ∀ {t : ITree E (ExtI I) R}
             {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
             {Qt : ITree E (ExtI I) R}
           → ITree.force t ≡ mix f Qt
           → NonSilForce t

-- walk-and-peel: from a failure of `Y`, descend through the bigstep's
-- `bTau (sSil _)` prefix to the first non-sil τ*-derivative `Ys`.  The
-- returned failure has the same `T` and `ref` but a strictly shorter
-- bigstep (when the input started with `bTau (sSil _)`).
--
-- Termination: structural recursion on the bigstep — the `bTau (sSil _)`
-- case recurses on `rest'`, a strict subterm of the input bigstep.
walk-and-peel :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {Y : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures Y s B
  → Σ[ Ys ∈ ITree E (ExtI I) R ]
       (failures Ys s B) × (Y ─[sSil*]─► Ys) × NonSilForce Ys
-- bNil + ref-stable: T = Y; ref says Y stable ⇒ force Y = vis _.
walk-and-peel {Y = Y} (.Y , bNil , ref-stable st refuses)
  with stable→force-vis {t = Y} st
... | f , eq =
    Y , (Y , bNil , ref-stable st refuses) , sSil*-zero , nsf-vis eq
-- bNil + ref-tick: ref's √x step witnesses force Y = ret x.
walk-and-peel {Y = Y} (.Y , bNil , ref-tick step ¬B)
  with √-is-ret step
... | eq , _ =
    Y , (Y , bNil , ref-tick step ¬B) , sSil*-zero , nsf-ret eq
-- bTau (sSil eq) rest': peel one step, recurse.
walk-and-peel (T , bTau (sSil eq) rest' , ref)
  with walk-and-peel (T , rest' , ref)
... | Ys , fail-Ys , chain , shape =
    Ys , fail-Ys , sSil*-step eq chain , shape
-- bTau (sNdbr eq f-eq) rest': force Y = ndbr ⇒ Y already non-sil.
walk-and-peel {Y = Y} (T , bTau (sNdbr eq f-eq) rest' , ref) =
    Y , (T , bTau (sNdbr eq f-eq) rest' , ref) , sSil*-zero , nsf-ndbr eq
-- bStep (sRet eq) bNil: T = deadlock, force Y = ret x ⇒ non-sil.
walk-and-peel {Y = Y} (.deadlock , bStep (sRet eq) bNil , ref) =
    Y , (deadlock , bStep (sRet eq) bNil , ref) , sSil*-zero , nsf-ret eq
-- bStep (sRet _) (bTau step _): step is τ from deadlock — impossible.
walk-and-peel (T , bStep (sRet _) (bTau step _) , _) =
    case step of λ where
      (sSil ())
      (sNdbr () _)
-- bStep (sRet _) (bStep step _): step is ev from deadlock — impossible.
walk-and-peel (T , bStep (sRet _) (bStep step _) , _) =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep (sVis eq f-eq) rest': force Y = vis _ ⇒ non-sil.
walk-and-peel {Y = Y} (T , bStep (sVis eq f-eq) rest' , ref) =
    Y , (T , bStep (sVis eq f-eq) rest' , ref) , sSil*-zero , nsf-vis eq
-- bTau (sMixSlide eq) rest': force Y = mix _ _ ⇒ non-sil (slide isn't sil).
walk-and-peel {Y = Y} (T , bTau (sMixSlide eq) rest' , ref) =
    Y , (T , bTau (sMixSlide eq) rest' , ref) , sSil*-zero , nsf-mix eq
-- bStep (sMixVis eq f-eq) rest': force Y = mix _ _ ⇒ non-sil.
walk-and-peel {Y = Y} (T , bStep (sMixVis eq f-eq) bNil , ref) =
    Y , (T , bStep (sMixVis eq f-eq) bNil , ref) , sSil*-zero , nsf-mix eq
walk-and-peel {Y = Y} (T , bStep (sMixVis eq f-eq) (bTau s rest') , ref) =
    Y , (T , bStep (sMixVis eq f-eq) (bTau s rest') , ref) , sSil*-zero , nsf-mix eq
walk-and-peel {Y = Y} (T , bStep (sMixVis eq f-eq) (bStep s rest') , ref) =
    Y , (T , bStep (sMixVis eq f-eq) (bStep s rest') , ref) , sSil*-zero , nsf-mix eq

-- left-walk-□: drive the LEFT copy along a sSil-only chain.
-- Trivial structural recursion on the chain.
left-walk-□ :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {X Y Xs : ITree E (ExtI I) R}
  → X ─[sSil*]─► Xs
  → (X □ Y) ─[τ*]─► (Xs □ Y)
left-walk-□                         sSil*-zero            = τ*-zero
left-walk-□ {X = X} {Y = Y} (sSil*-step {t' = X'} eq rest) =
    τ*-step (sSil {p = X □ Y}
                  (force-□-sil-left {P = X} {P' = X'} {Q = Y} eq))
            (left-walk-□ {X = X'} rest)

-- right-walk-□: drive the RIGHT copy along a sSil-only chain when the
-- LEFT is fixed at a non-sil-shaped `Xs`.  Dispatched on Xs's shape via
-- `force-□-sil-right-{ret,vis,ndbr}`.
right-walk-□ :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {Y Xs : ITree E (ExtI I) R}
  → NonSilForce Xs
  → Y ─[sSil*]─► Xs
  → (Xs □ Y) ─[τ*]─► (Xs □ Xs)
right-walk-□                              _      sSil*-zero = τ*-zero
right-walk-□ {Y = Y} {Xs = Xs} (nsf-ret  eq-Xs)  (sSil*-step {t' = Y'} eq rest) =
    τ*-step (sSil {p = Xs □ Y}
                  (force-□-sil-right-ret {P = Xs} {Q = Y} {Q' = Y'} eq-Xs eq))
            (right-walk-□ (nsf-ret eq-Xs) rest)
right-walk-□ {Y = Y} {Xs = Xs} (nsf-vis  eq-Xs)  (sSil*-step {t' = Y'} eq rest) =
    τ*-step (sSil {p = Xs □ Y}
                  (force-□-sil-right-vis {P = Xs} {Q = Y} {Q' = Y'} eq-Xs eq))
            (right-walk-□ (nsf-vis eq-Xs) rest)
right-walk-□ {Y = Y} {Xs = Xs} (nsf-ndbr eq-Xs)  (sSil*-step {t' = Y'} eq rest) =
    τ*-step (sSil {p = Xs □ Y}
                  (force-□-sil-right-ndbr {P = Xs} {Q = Y} {Q' = Y'} eq-Xs eq))
            (right-walk-□ (nsf-ndbr eq-Xs) rest)
right-walk-□ {Y = Y} {Xs = Xs} (nsf-mix  eq-Xs)  (sSil*-step {t' = Y'} eq rest) =
    τ*-step (sSil {p = Xs □ Y}
                  (force-□-sil-right-mix {P = Xs} {Q = Y} {Q' = Y'} eq-Xs eq))
            (right-walk-□ (nsf-mix eq-Xs) rest)

-----------------------------------------------------------------------------
-- bTau / sSil case of `failures-lift-PP`.  Replaces what was a postulate.
--
-- Strategy:
--   1. `walk-and-peel` finds `Ys`, the first non-sil τ*-derivative of
--      `P'`, with a peeled failure and chain `P' ─[sSil*]─► Ys`.
--   2. Build `(P □ P) ─[τ*]─► (Ys □ Ys)`:
--        (a) one `sil-LEFT` τ-step `(P □ P) → (P' □ P)` from `eq`,
--        (b) `left-walk-□` along `P' → Ys`,
--        (c) `right-walk-□` along the extended chain `P → Ys` (i.e.
--            `eq` followed by `chain-P'-Ys`), exploiting `Ys`'s shape.
--   3. Recurse via `failures-lift-PP {P = Ys}` on the peeled failure.
--   4. Prepend the τ*-chain via `τ*-prepend-bigstep`.
-----------------------------------------------------------------------------

failures-lift-PP-bTau-sSil :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P P' : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ sil P'
  → failures P' s B
  → failures (P □ P) s B
failures-lift-PP-bTau-sSil {P = P} {P' = P'} eq fail-P'
  with walk-and-peel fail-P'
... | Ys , fail-Ys , chain-P'-Ys , shape-Ys
  with failures-lift-PP {P = Ys} fail-Ys
... | T'' , big-Ys-Ys , ref'' =
    T'' ,
    τ*-prepend-bigstep
      (τ*-step (sSil {p = P □ P}
                     (force-□-sil-left {P = P} {P' = P'} {Q = P} eq))
               (τ*-trans (left-walk-□ {Y = P} chain-P'-Ys)
                         (right-walk-□ shape-Ys (sSil*-step eq chain-P'-Ys))))
      big-Ys-Ys ,
    ref''

-- bTau sNdbr — proved.  A τ-step from P □ P at force P = ndbr can
-- pick the diagonal `mergeNdbr`-pair `(i, i)` with arg `(a, a)`,
-- which yields `just (t' □ t')` (since both `fP (Aᵢ, iᵢ-ext) aᵢ` are
-- the same `just t'`).  The lifted bigstep is then
--     bTau (sNdbr force-eq-PP merge-eq) (lifted-bigstep-on-t')
-- where `lifted-bigstep-on-t'` is `failures-lift-PP` recursively
-- applied to the input failure of `t'`.
{-# TERMINATING #-}
failures-lift-PP-bTau-sNdbr :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P : ITree E (ExtI I) R}
      {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
      {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
      {wp : Is-just (fP wi wa)}
      {i : AnyTypes (ExtI I)} {a : proj₁ i}
      {t' : ITree E (ExtI I) R}
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → ITree.force P ≡ ndbr fP wi wa wp
    → fP i a ≡ just t'
    → failures t' s B
    → failures (P □ P) s B
failures-lift-PP-bTau-sNdbr {P = P} {fP = fP}
    {wi = (AP-ext , iP-ext)} {wa = waP} {wp = wpP}
    {i  = (AI-ext , iI-ext)} {a  = aᵢ}   {t' = t'}
    eq f-eq fail-t'
  with failures-lift-PP {P = t'} fail-t'
... | T'' , bigstep-t'-□-t' , ref'' =
    T'' , bTau step-PP bigstep-t'-□-t' , ref''
  where
    -- `force (P □ P)` reduces (with both copies' forces being the
    -- same `ndbr fP wi wa wp`) to the merged ndbr.  We use `rewrite`
    -- to replace `force P` and let the with-clauses in `_□_` reduce.
    force-eq-PP :
      ITree.force (P □ P) ≡
        ndbr (mergeNdbr fP fP)
             ((AP-ext × AP-ext) , pair iP-ext iP-ext)
             (waP , waP)
             (mergeNdbr-witness fP fP wpP wpP)
    force-eq-PP rewrite eq = refl

    -- Diagonal `mergeNdbr` at pair-index `(iI-ext, iI-ext)` with arg
    -- `(aᵢ, aᵢ)`: both `fP …` calls are the same `just t'`, so the
    -- merge returns `just (t' □ t')`.
    merge-eq :
      mergeNdbr fP fP
        ((AI-ext × AI-ext) , pair iI-ext iI-ext)
        (aᵢ , aᵢ)
      ≡ just (t' □ t')
    merge-eq rewrite f-eq = refl

    step-PP : (P □ P) ─[ τ ]─► (t' □ t')
    step-PP =
      sNdbr {p = P □ P}
            {f = mergeNdbr fP fP}
            {wi = ((AP-ext × AP-ext) , pair iP-ext iP-ext)}
            {wa = (waP , waP)}
            {prf = mergeNdbr-witness fP fP wpP wpP}
            {i  = ((AI-ext × AI-ext) , pair iI-ext iI-ext)}
            {a  = (aᵢ , aᵢ)}
            {t′ = t' □ t'}
            force-eq-PP
            merge-eq

-- Forward direction (definition of the forward-declared signature
-- above).  Modulo the sSil sub-postulate, this is fully proved.
-- bNil: trace empty, T = P.  Refusal lifts via P-ref→PP-ref.
failures-lift-PP {P = P} (.P , bNil , ref) =
    P □ P , bNil , P-ref→PP-ref ref
-- bStep / sRet: a √r step from P (force P ≡ ret r) and `rest = bNil`
-- (deadlock has no transitions).  P □ P does √r at force = ret r too
-- (by `force-□-ret-ret-eq`).
failures-lift-PP {P = P} (.deadlock , bStep (sRet {x = x} eq) bNil , ref) =
    deadlock ,
    bStep {t = P □ P} {t′ = deadlock}
          (sRet {p = P □ P} {x = x} (force-□-ret-ret-eq {P = P} eq))
          bNil ,
    ref
-- bStep / sRet with non-bNil rest: deadlock has no transitions, so the
-- residual must be `bNil`.  Discharged via `case` on the residual step.
failures-lift-PP (T , bStep (sRet _) (bTau step _) , ref) =
    case step of λ where
      (sSil ())
      (sNdbr () _)
failures-lift-PP (T , bStep (sRet _) (bStep step _) , ref) =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep / sVis: the visible event lifts via `force-□-vis-vis`; the
-- merged continuation is `t' ⊓ t'`, from which a τ-step (`⊓-step-L`)
-- lands at `t'` and we splice the original `rest` from `t'`.
failures-lift-PP {P = P}
  (T , bStep (sVis {f = fP} {at = at} {a = a} {t′ = t'} sV-eq fP-eq) rest , ref) =
    T ,
    bStep {t = P □ P} {t′ = t' ⊓ t'}
          (sVis {p = P □ P} {f = λ Ae → mergeVis (fP Ae) (fP Ae)}
                {at = at} {a = a} {t′ = t' ⊓ t'}
                (force-□-vis-vis {P = P} {Q = P} {fP = fP} {fQ = fP} sV-eq sV-eq)
                merged-just)
          (bTau (⊓-step-L t' t') rest) ,
    ref
  where
    merged-just :
        (λ Ae → mergeVis (fP Ae) (fP Ae)) at a ≡ just (t' ⊓ t')
    merged-just rewrite fP-eq = refl
-- bTau / sSil: dispatched to the sub-postulate.
failures-lift-PP (T , bTau (sSil eq) rest , ref) =
    failures-lift-PP-bTau-sSil eq (T , rest , ref)
-- bTau / sNdbr: dispatched to the sub-postulate.
failures-lift-PP (T , bTau (sNdbr eq f-eq) rest , ref) =
    failures-lift-PP-bTau-sNdbr eq f-eq (T , rest , ref)
-- bTau / sMixSlide (post-mix): P slides via mix from P to Pt.  Under rule
-- "mix | mix", P □ P also slides via mix to (Pt □ Pt).  Recurse on the
-- residual failure of Pt to lift it to (Pt □ Pt), then prepend the slide.
failures-lift-PP {P = P}
  (T , bTau (sMixSlide {f = fP} {Qt = Pt} sM-eq) rest , ref)
  with failures-lift-PP {P = Pt} (T , rest , ref)
... | T' , big-Pt-Pt , ref' =
    T' ,
    bTau {t = P □ P} {t′ = Pt □ Pt}
         (sMixSlide {p = P □ P} {f = λ Ae → mergeVis (fP Ae) (fP Ae)}
                    {Qt = Pt □ Pt}
                    (force-□-mix-mix-mix {P = P} {Q = P} sM-eq sM-eq))
         big-Pt-Pt ,
    ref'
-- bStep / sMixVis (post-mix): P fires a visible event from a mix node.  The
-- compound P □ P fires via the merged vis function `mergeVis fP fP`, which
-- at `a` is `mergeMaybe (just t') (just t') = just (t' ⊓ t')`; then
-- `⊓-step-L` splices the original rest.  Mirrors the existing sVis case.
failures-lift-PP {P = P}
  (T , bStep (sMixVis {f = fP} {Qt = Pt} {at = at} {a = a} {t′ = t'} sM-eq fP-eq) rest , ref) =
    T ,
    bStep {t = P □ P} {t′ = t' ⊓ t'}
          (sMixVis {p = P □ P} {f = λ Ae → mergeVis (fP Ae) (fP Ae)}
                   {Qt = Pt □ Pt}
                   {at = at} {a = a} {t′ = t' ⊓ t'}
                   (force-□-mix-mix-mix {P = P} {Q = P} sM-eq sM-eq)
                   merged-just)
          (bTau (⊓-step-L t' t') rest) ,
    ref
  where
    merged-just :
        (λ Ae → mergeVis (fP Ae) (fP Ae)) at a ≡ just (t' ⊓ t')
    merged-just rewrite fP-eq = refl

-- Backward (project):  failures (P □ P) s B → failures P s B.
-- The bNil + bStep cases are proved using session 1+2 helpers.
-- The bTau case dispatches to one of two sub-functions, depending on
-- whether the τ-step out of (P □ P) is sSil or sNdbr.  The sSil case
-- is proved here; the sNdbr case remains a postulate for the moment.
--
-- sSil case: force (P □ P) ≡ sil U.  By `□-force-sil-inv` specialised to
--   P=Q=P:
--     inj₁: force P ≡ sil P', U ≡ P' □ P (LEFT post-τ, RIGHT pre-τ).
--     inj₂: force P ≡ sil P', U ≡ P □ P' (LEFT pre-τ, RIGHT post-τ).
--   In inj₁, the deterministic τ-walk from `(P' □ P)` may need many
--   steps before reaching the symmetric form `(Z □ Z)` (where Z is the
--   first non-sil τ*-derivative of P): we walk left until force becomes
--   non-sil, then walk right.
--   In inj₂, force P ≡ sil P' makes sil-LEFT always fire, so a single
--   τ-step takes `(P □ P') → (P' □ P')` — symmetric reached immediately.
--
-- sNdbr case: force (P □ P) ≡ ndbr g wi wa wp where g = mergeNdbr fP fP.
--   By `□-force-ndbr-inv` specialised to P=Q=P, only case J fires (others
--   require LEFT and RIGHT to differ in shape), so force P ≡ ndbr fP wiP
--   waP wpP and U ≡ tL □ tR for some pair-branch (iL,aL),(iR,aR) of fP.
--   Still postulated.

-- Forward declaration of failures-project-PP, since the sSil discharge
-- below recursively calls it on the symmetric `(Z □ Z)` form reached
-- after the asymmetric walk.
failures-project-PP :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures (P □ P) s B → failures P s B

-- Mix-shape projection / lift / divergence helpers (post-mix `_□_`).  All
-- proofs follow the same template as their sSil / sNdbr / sVis cousins;
-- deferred to postulate here because each requires re-replication of the
-- existing (extensive) machinery for the mix-mix-mix force-eq and merged-vis
-- collapse `mergeMaybe (just _) (just _) = just (_ ⊓ _)`.
postulate
  failures-project-PP-bTau-sMixSlide :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → ITree.force (P □ P) ≡ mix f Qt
    → failures Qt s B
    → failures P s B
  failures-project-PP-bStep-sMixVis :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → ITree.force (P □ P) ≡ mix f Qt
    → f at a ≡ just t'
    → failures t' s B
    → failures P (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) B
  -- Divergence lift through `_□_` when one or both sides are mix-shaped.
  -- Used by divergent-□-asymm-orig's mix sub-cases.
  divergent-□-mix-asymm :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {tL tR : ITree E (ExtI I) R}
    → Divergent tL → Divergent tR → Divergent (tL □ tR)
  -- Divergence lift through `_□_` for mix-prefixed bigsteps.
  divergences-lift-PP-bTau-sMixSlide :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {t : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {pre : List (Event√ E R)} {Q : ITree E (ExtI I) R}
    → ITree.force t ≡ mix f Qt
    → Qt ═⟨ pre ⟩═► Q → Divergent Q
    → Σ[ T' ∈ ITree E (ExtI I) R ]
        ((t □ t) ═⟨ pre ⟩═► T' × Divergent T')
  divergences-lift-PP-bStep-sMixVis-bNil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {t : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
    → ITree.force t ≡ mix f Qt
    → f at a ≡ just t'
    → Divergent t'
    → Σ[ T' ∈ ITree E (ExtI I) R ]
        ((t □ t) ═⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ [] ⟩═► T'
         × Divergent T')
  divergences-lift-PP-bStep-sMixVis-bTau :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {t t' t'' Q : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at}
      {pre : List (Event√ E R)}
    → ITree.force t ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ τ ]─► t''
    → t'' ═⟨ pre ⟩═► Q
    → Divergent Q
    → Σ[ T' ∈ ITree E (ExtI I) R ]
        ((t □ t) ═⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre ⟩═► T'
         × Divergent T')
  divergences-lift-PP-bStep-sMixVis-bStep :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {t t' t'' Q : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at}
      {el : Event√ E R} {pre : List (Event√ E R)}
    → ITree.force t ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ ev el ]─► t''
    → t'' ═⟨ pre ⟩═► Q
    → Divergent Q
    → Σ[ T' ∈ ITree E (ExtI I) R ]
        ((t □ t) ═⟨ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ el ∷ pre ⟩═► T'
         × Divergent T')
  -- Asymm-divergence-project: mix-vis case at (tL □ tR).
  -- A sMixVis step at (tL □ tR) requires force (tL □ tR) ≡ mix f Qt.  By
  -- the (5×5) reduction rules this happens iff both tL and tR are mix-
  -- shaped (force tL ≡ mix fmL Lt, force tR ≡ mix fmR Rt), in which case
  -- f ≡ mergeVis fmL fmR and Qt ≡ Lt □ Rt.  Need to project a divergence
  -- at the residual back to P, using chL : P →* tL and chR : P →* tR.
  -- Three sub-cases on the bigstep tail after sMixVis.
  asymm-divergence-project-sMixVis-bNil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → s ≡ pre ++ suf
    → pre ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ []
    → ITree.force (tL □ tR) ≡ mix f Qt
    → f at a ≡ just t'
    → Divergent t'
    → divergences P s
  asymm-divergence-project-sMixVis-bTau :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR U Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre ++ suf
    → ITree.force (tL □ tR) ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ τ ]─► U
    → U ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s
  asymm-divergence-project-sMixVis-bStep :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR U Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {el : Event√ E R}
      {pre suf s : List (Event√ E R)}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ el ∷ pre ++ suf
    → ITree.force (tL □ tR) ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ ev el ]─► U
    → U ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s
  -- Asymm-divergence-project-bTau: sMixSlide case at (tL □ tR).
  -- A sMixSlide step requires force (tL □ tR) ≡ mix f Qt with U ≡ Qt.
  -- By the (5×5) rules this happens iff both tL and tR are mix-shaped;
  -- project Divergent Qt back to P via chL/chR.
  asymm-divergence-project-bTau-sMixSlide :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → s ≡ pre ++ suf
    → ITree.force (tL □ tR) ≡ mix f Qt
    → Qt ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s
  -- Divergences-project-PP: sMixSlide / sMixVis cases at (P □ P).
  -- Same structure as the asymm versions but specialised to chL = chR = ε.
  divergences-project-PP-bTau-sMixSlide :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → s ≡ pre ++ suf
    → ITree.force (P □ P) ≡ mix f Qt
    → Qt ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s
  divergences-project-PP-sMixVis-bNil :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → s ≡ pre ++ suf
    → pre ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ []
    → ITree.force (P □ P) ≡ mix f Qt
    → f at a ≡ just t'
    → Divergent t'
    → divergences P s
  divergences-project-PP-sMixVis-bTau :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P U Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {pre suf s : List (Event√ E R)}
    → s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre ++ suf
    → ITree.force (P □ P) ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ τ ]─► U
    → U ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s
  divergences-project-PP-sMixVis-bStep :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P U Q' : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {el : Event√ E R}
      {pre suf s : List (Event√ E R)}
    → s ≡ evl (evLabel (proj₁ at) (proj₂ at) a) ∷ el ∷ pre ++ suf
    → ITree.force (P □ P) ≡ mix f Qt
    → f at a ≡ just t'
    → t' ─[ ev el ]─► U
    → U ═⟨ pre ⟩═► Q'
    → Divergent Q'
    → divergences P s

-----------------------------------------------------------------------------
-- Helpers for the sSil-case discharge.
-----------------------------------------------------------------------------

-- Conversion: sSil-only chain → τ*-chain.
sSil*→τ* :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t t' : ITree E (ExtI I) R}
  → t ─[sSil*]─► t' → t ─[τ*]─► t'
sSil*→τ* sSil*-zero          = τ*-zero
sSil*→τ* (sSil*-step eq rest) = τ*-step (sSil eq) (sSil*→τ* rest)

-- Append a sSil step at the end of a sSil*-chain.
sSil*-snoc :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t t' t'' : ITree E (ExtI I) R}
  → t ─[sSil*]─► t'
  → ITree.force t' ≡ sil t''
  → t ─[sSil*]─► t''
sSil*-snoc sSil*-zero          eq = sSil*-step eq sSil*-zero
sSil*-snoc (sSil*-step e rest) eq = sSil*-step e (sSil*-snoc rest eq)

-- A sil-shaped tree cannot be `isStable`.
sil-not-stable :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t t' : ITree E (ExtI I) R}
  → ITree.force t ≡ sil t' → isStable t → ⊥
sil-not-stable {t = t} eq st with stable→force-vis {t = t} st
... | _ , eqVis = vis≢sil (trans (sym eqVis) eq)

-- If RIGHT of `(X □ Y)` is sil-shaped, force `(X □ Y)` is sil too.
-- `aux` dispatches on `force X`; placing it inside a where keeps the
-- with-substitution local to aux's own body where it does the right
-- thing.
□-LR-force-sil :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (X : ITree E (ExtI I) R) {Y Y' : ITree E (ExtI I) R}
  → ITree.force Y ≡ sil Y'
  → Σ[ V ∈ ITree E (ExtI I) R ] ITree.force (X □ Y) ≡ sil V
□-LR-force-sil {I = I} {R = R} X {Y = Y} {Y' = Y'} forceY = aux (ITree.force X) refl
  where
    aux : (fX : NodeKind E (ExtI I) R)
        → ITree.force X ≡ fX
        → Σ[ V ∈ ITree E (ExtI I) R ] ITree.force (X □ Y) ≡ sil V
    aux (sil X') eqX =
        X' □ Y , force-□-sil-left {P = X} {P' = X'} {Q = Y} eqX
    aux (ret r) eqX =
        X □ Y' , force-□-sil-right-ret {P = X} {Q = Y} {Q' = Y'} eqX forceY
    aux (vis _) eqX =
        X □ Y' , force-□-sil-right-vis {P = X} {Q = Y} {Q' = Y'} eqX forceY
    aux (ndbr _ _ _ _) eqX =
        X □ Y' , force-□-sil-right-ndbr {P = X} {Q = Y} {Q' = Y'} eqX forceY
    aux (mix _ _) eqX =
        X □ Y' , force-□-sil-right-mix {P = X} {Q = Y} {Q' = Y'} eqX forceY

-----------------------------------------------------------------------------
-- Phase 2 walker (RIGHT-walk): once `Xs` is the τ*-stable form (non-sil),
-- drive the right copy of `(Xs □ Y)` along the chain `Y ─[sSil*]─► Xs`.
-- When the chain runs out (Y ≡ Xs), we're at the symmetric form and
-- apply `failures-project-PP {P = Xs}`.

walk-PP-asymm-RIGHT :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P-tau Y Xs : ITree E (ExtI I) R) {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → P-tau ─[sSil*]─► Y
  → Y ─[sSil*]─► Xs
  → NonSilForce Xs
  → failures (Xs □ Y) s B
  → failures P-tau s B
-- Base: chain Y → Xs is empty ⇒ Y ≡ Xs.  Apply failures-project-PP.
walk-PP-asymm-RIGHT P-tau .Xs Xs chain-Pt-Y sSil*-zero shape-Xs (T , bigstep , ref)
  with failures-project-PP (T , bigstep , ref)
... | T' , bigstep-Xs , ref-Xs =
    T' , τ*-prepend-bigstep (sSil*→τ* chain-Pt-Y) bigstep-Xs , ref-Xs
-- Chain-Y-Xs non-empty: force Y is sil, so force `(Xs □ Y)` is sil.
-- Bigstep must start with bTau-sSil and uses sil-RIGHT (Xs is non-sil).
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bNil , ref-stable st _)
    with □-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y
... | V , force-eq = ⊥-elim (sil-not-stable {t = Xs □ Y} {t' = V} force-eq st)
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bNil , ref-tick (sRet {x = x} eq-ret) _)
    with □-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y
... | V , force-eq = case trans (sym force-eq) eq-ret of λ ()
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) (nsf-ret eqXs)
                    (T , bTau (sSil {t = V} eq2) rest' , ref)
    with sil-injective (trans (sym eq2)
           (force-□-sil-right-ret {P = Xs} {Q = Y} {Q' = Y'} eqXs eq-Y))
... | refl =
    walk-PP-asymm-RIGHT P-tau Y' Xs (sSil*-snoc chain-Pt-Y eq-Y) rest-Y-Xs (nsf-ret eqXs)
         (T , rest' , ref)
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) (nsf-vis eqXs)
                    (T , bTau (sSil {t = V} eq2) rest' , ref)
    with sil-injective (trans (sym eq2)
           (force-□-sil-right-vis {P = Xs} {Q = Y} {Q' = Y'} eqXs eq-Y))
... | refl =
    walk-PP-asymm-RIGHT P-tau Y' Xs (sSil*-snoc chain-Pt-Y eq-Y) rest-Y-Xs (nsf-vis eqXs)
         (T , rest' , ref)
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) (nsf-ndbr eqXs)
                    (T , bTau (sSil {t = V} eq2) rest' , ref)
    with sil-injective (trans (sym eq2)
           (force-□-sil-right-ndbr {P = Xs} {Q = Y} {Q' = Y'} eqXs eq-Y))
... | refl =
    walk-PP-asymm-RIGHT P-tau Y' Xs (sSil*-snoc chain-Pt-Y eq-Y) rest-Y-Xs (nsf-ndbr eqXs)
         (T , rest' , ref)
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bTau (sNdbr eq2 _) _ , _) =
    case trans (sym (proj₂ (□-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y))) eq2 of λ ()
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bStep (sRet eq2) _ , _) =
    case trans (sym (proj₂ (□-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y))) eq2 of λ ()
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bStep (sVis eq2 _) _ , _) =
    case trans (sym (proj₂ (□-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y))) eq2 of λ ()
-- sMixSlide / sMixVis: force(Xs □ Y) is sil (Xs non-sil + Y sil); mix ≢ sil.
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bTau (sMixSlide eq2) _ , _) =
    case trans (sym (proj₂ (□-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y))) eq2 of λ ()
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) shape-Xs
                    (T , bStep (sMixVis eq2 _) _ , _) =
    case trans (sym (proj₂ (□-LR-force-sil Xs {Y = Y} {Y' = Y'} eq-Y))) eq2 of λ ()
-- nsf-mix productive case (mirrors nsf-ret/vis/ndbr) using force-□-sil-right-mix.
walk-PP-asymm-RIGHT P-tau Y Xs chain-Pt-Y (sSil*-step {t' = Y'} eq-Y rest-Y-Xs) (nsf-mix eqXs)
                    (T , bTau (sSil {t = V} eq2) rest' , ref)
    with sil-injective (trans (sym eq2)
           (force-□-sil-right-mix {P = Xs} {Q = Y} {Q' = Y'} eqXs eq-Y))
... | refl =
    walk-PP-asymm-RIGHT P-tau Y' Xs (sSil*-snoc chain-Pt-Y eq-Y) rest-Y-Xs (nsf-mix eqXs)
         (T , rest' , ref)

-----------------------------------------------------------------------------
-- Phase 1 walker (LEFT-walk): drive the left copy of `(X □ P-tau)` until
-- force X becomes non-sil; then transition to Phase 2 with `(X □ P)` and
-- the chain `P → X` (RIGHT-walk).
walk-PP-asymm-LEFT :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P-tau P X : ITree E (ExtI I) R) {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force P-tau ≡ sil P
  → P ─[sSil*]─► X
  → failures (X □ P-tau) s B
  → failures P-tau s B
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X (T , bNil , ref-stable st _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = ⊥-elim (sil-not-stable {t = X □ P-tau} {t' = V} force-eq st)
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X (T , bNil , ref-tick (sRet eq-ret) _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq-ret of λ ()
-- bTau (sSil eq2): dispatch on force X via aux; each branch unifies V via
-- `with refl` (no subst), preserving the structural relationship between
-- rest' and the input bigstep so Agda's termination checker accepts.
walk-PP-asymm-LEFT {I = I} {R = R} P-tau P X forceP-tau chain-P-X
                   (T , bTau (sSil {t = V} eq2) rest' , ref) =
    aux (ITree.force X) refl
  where
    aux : (fX : NodeKind E (ExtI I) R) → ITree.force X ≡ fX → failures P-tau _ _
    aux (sil X') eqX
        with sil-injective (trans (sym eq2)
               (force-□-sil-left {P = X} {P' = X'} {Q = P-tau} eqX))
    ... | refl =
        walk-PP-asymm-LEFT P-tau P X' forceP-tau (sSil*-snoc chain-P-X eqX)
             (T , rest' , ref)
    aux (ret r) eqX
        with sil-injective (trans (sym eq2)
               (force-□-sil-right-ret {P = X} {Q = P-tau} {Q' = P} eqX forceP-tau))
    ... | refl =
        walk-PP-asymm-RIGHT P-tau P X
             (sSil*-step forceP-tau sSil*-zero) chain-P-X (nsf-ret eqX)
             (T , rest' , ref)
    aux (vis _) eqX
        with sil-injective (trans (sym eq2)
               (force-□-sil-right-vis {P = X} {Q = P-tau} {Q' = P} eqX forceP-tau))
    ... | refl =
        walk-PP-asymm-RIGHT P-tau P X
             (sSil*-step forceP-tau sSil*-zero) chain-P-X (nsf-vis eqX)
             (T , rest' , ref)
    aux (ndbr _ _ _ _) eqX
        with sil-injective (trans (sym eq2)
               (force-□-sil-right-ndbr {P = X} {Q = P-tau} {Q' = P} eqX forceP-tau))
    ... | refl =
        walk-PP-asymm-RIGHT P-tau P X
             (sSil*-step forceP-tau sSil*-zero) chain-P-X (nsf-ndbr eqX)
             (T , rest' , ref)
    aux (mix _ _) eqX
        with sil-injective (trans (sym eq2)
               (force-□-sil-right-mix {P = X} {Q = P-tau} {Q' = P} eqX forceP-tau))
    ... | refl =
        walk-PP-asymm-RIGHT P-tau P X
             (sSil*-step forceP-tau sSil*-zero) chain-P-X (nsf-mix eqX)
             (T , rest' , ref)
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X
                   (T , bTau (sNdbr eq2 _) _ , _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq2 of λ ()
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X
                   (T , bStep (sRet eq2) _ , _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq2 of λ ()
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X
                   (T , bStep (sVis eq2 _) _ , _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq2 of λ ()
-- sMixSlide / sMixVis: force(X □ P-tau) is sil (X non-sil-mix and P-tau sil); mix ≢ sil.
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X
                   (T , bTau (sMixSlide eq2) _ , _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq2 of λ ()
walk-PP-asymm-LEFT P-tau P X forceP-tau chain-P-X
                   (T , bStep (sMixVis eq2 _) _ , _)
    with □-LR-force-sil X {Y = P-tau} {Y' = P} forceP-tau
... | V , force-eq = case trans (sym force-eq) eq2 of λ ()

-----------------------------------------------------------------------------
-- inj₂-handler: when U = P □ P' (RIGHT-advanced), force `(P □ P')` is
-- always `sil (P' □ P')` via sil-LEFT (since force P sil), so a single
-- bTau-sSil consume reaches the symmetric form.  Apply
-- `failures-project-PP {P = P'}` and prepend `bTau (sSil forceP)`.
--
-- TERMINATING-pragma justification: this function calls
-- `failures-project-PP` recursively, which in turn dispatches back to
-- `failures-project-PP-bTau-sSil → walk-PP-asymm-INJ2` if the recursive
-- call's bigstep starts with another bTau-sSil.  Each round-trip strictly
-- decreases the bigstep size (by ≥ 2), so the function terminates — but
-- Agda's size-change termination checker can't see this through the
-- multi-function dispatch chain.  Removing this pragma would require
-- inlining the relevant `failures-project-PP` cases (significant code
-- duplication) or using sized types / well-founded recursion.
-- {-# TERMINATING #-}
walk-PP-asymm-INJ2 :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P P' : ITree E (ExtI I) R) {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ sil P'
  → failures (P □ P') s B
  → failures P s B
walk-PP-asymm-INJ2 P P' forceP (T , bNil , ref-stable st _) =
    ⊥-elim (sil-not-stable {t = P □ P'} {t' = P' □ P'}
             (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP) st)
walk-PP-asymm-INJ2 P P' forceP (T , bNil , ref-tick (sRet eq-ret) _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq-ret
      of λ ()
walk-PP-asymm-INJ2 P P' forceP
                   (T , bTau (sSil {t = V} eq2) rest' , ref)
    with sil-injective (trans (sym eq2)
           (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP))
... | refl
    with failures-project-PP {P = P'} (T , rest' , ref)
... | T'' , big-P' , ref'' =
    T'' ,
    bTau {t = P} {t′ = P'} (sSil {p = P} forceP) big-P' ,
    ref''
walk-PP-asymm-INJ2 P P' forceP (T , bTau (sNdbr eq2 _) _ , _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq2
      of λ ()
walk-PP-asymm-INJ2 P P' forceP (T , bStep (sRet eq2) _ , _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq2
      of λ ()
walk-PP-asymm-INJ2 P P' forceP (T , bStep (sVis eq2 _) _ , _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq2
      of λ ()
-- sMixSlide / sMixVis: force(P □ P') is sil (P=sil and rule "sil | _ → sil"),
-- so mix ≢ sil — absurd via the same force-□-sil-left equation.
walk-PP-asymm-INJ2 P P' forceP (T , bTau (sMixSlide eq2) _ , _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq2
      of λ ()
walk-PP-asymm-INJ2 P P' forceP (T , bStep (sMixVis eq2 _) _ , _) =
    case trans (sym (force-□-sil-left {P = P} {P' = P'} {Q = P'} forceP)) eq2
      of λ ()

-----------------------------------------------------------------------------
-- The discharged sSil case.  Use □-force-sil-inv to get force P ≡ sil P';
-- inj₁ uses Phase 1 walker; inj₂ uses INJ2 helper.
failures-project-PP-bTau-sSil :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P U : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force (P □ P) ≡ sil U
  → failures U s B
  → failures P s B
failures-project-PP-bTau-sSil {P = P} eqStep fail-U
    with □-force-sil-inv {P = P} {Q = P} eqStep
... | inj₁ (P' , forceP , refl) =
    walk-PP-asymm-LEFT P P' P' forceP sSil*-zero fail-U
... | inj₂ (P' , forceP , refl) =
    walk-PP-asymm-INJ2 P P' forceP fail-U

-- Generalised asymmetric-`_□_` projection walker.
--
-- This unifies what were four separate pieces (refusal-tL-from-tLR,
-- failures-project-asymm-□-bStep-sVis, failures-project-asymm-□-bTau,
-- failures-project-PP-bTau-sNdbr-J-both): given that `P` τ*-reaches
-- both `tL` and `tR`, any failure of `(tL □ tR)` lifts to a failure of
-- `P`.  Structural recursion on the bigstep handles each case; the
-- bTau-sNdbr case (four sub-cases D/H/I/J of `□-force-ndbr-inv`) is
-- handed off to a focused postulate.
--
-- Cases discharged here:
--   • bNil + ref-stable: project (tL □ tR)-refusal to tL-refusal.
--   • bNil + ref-tick:   tL or tR has ret-shaped force.
--   • bStep sRet bNil:   tL or tR has ret-shaped force.
--   • bStep sVis rest:   four sub-cases on `mergeVis (fL at) (fR at) a`.
--   • bTau sSil rest:    extend chL or chR by one sSil step, recurse on
--                        the resulting smaller bigstep.
--   • bTau sNdbr rest:   handed off to `asymm-walk-□-bTau-sNdbr`.

-- bTau sMixSlide / bStep sMixVis at `(tL □ tR)`: force(tL □ tR) ≡ mix f Qt
-- comes from one of 7 mix-producing _□_ rules of post-mix `_□_`.  Each
-- sub-case requires `(force tL × force tR)` analysis and prepending a
-- single corresponding step on the matching chain (chL or chR).
--
-- Proof plan (deferred via postulate, mirroring `asymm-walk-□-bTau-sNdbr`):
--   • For ret/vis, vis/ret: prepend chR / chL with the single sVis fire.
--   • For ret/mix, vis/mix: prepend chR with sMixVis or sMixSlide of tR.
--   • For mix/ret, mix/vis: prepend chL with sMixVis or sMixSlide of tL.
--   • For mix/mix: both fire; merged-vis at a is `mergeMaybe (just _) (just _)`,
--     yielding `⊓` successor handled like the vis|vis case (⊓-failures-elim).
postulate
  asymm-walk-□-bTau-sMixSlide :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → ITree.force (tL □ tR) ≡ mix f Qt
    → failures Qt s B → failures P s B

  asymm-walk-□-bStep-sMixVis :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P tL tR : ITree E (ExtI I) R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {Qt : ITree E (ExtI I) R}
      {at : AnyTypes E} {a : proj₁ at} {t' : ITree E (ExtI I) R}
      {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
    → P ─[τ*]─► tL → P ─[τ*]─► tR
    → ITree.force (tL □ tR) ≡ mix f Qt
    → f at a ≡ just t'
    → failures t' s B
    → failures P (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) B

-- bTau sNdbr step at `(tL □ tR)`.  Splits into four cases of
-- `□-force-ndbr-inv` (D = ret/ret, H = vis/ndbr, I = ndbr/vis,
-- J = ndbr/ndbr); each requires unfolding the merge-form continuation.
-- Forward-declared here; body defined after `asymm-walk-□` below.
asymm-walk-□-bTau-sNdbr :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P tL tR : ITree E (ExtI I) R}
    {g : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (g wi wa)}
    {i : AnyTypes (ExtI I)} {a : proj₁ i}
    {V : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → P ─[τ*]─► tL → P ─[τ*]─► tR
  → ITree.force (tL □ tR) ≡ ndbr g wi wa wp
  → g i a ≡ just V
  → failures V s B
  → failures P s B

-- Helper: project a refusal of `(tL □ tR)` to a refusal of `tL`.  Used
-- inline in `asymm-walk-□`'s bNil+ref-stable clause.  The merged-vis
-- `mergeVis fL fR` blocks an event `e` only when both `fL` and `fR`
-- block; thus `tL` blocks every B-event that `(tL □ tR)` blocks.
refusal-tL-from-tLR :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {tL tR : ITree E (ExtI I) R}
    {fL fR : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {B : Event√ E R → Set ℓB}
  → ITree.force tL ≡ vis fL
  → ITree.force tR ≡ vis fR
  → (∀ e → B e → ∀ {Q : ITree E (ExtI I) R} → ¬ ((tL □ tR) ─[ ev e ]─► Q))
  → (∀ e → B e → ∀ {Q : ITree E (ExtI I) R} → ¬ (tL ─[ ev e ]─► Q))
refusal-tL-from-tLR {tL = tL} {tR = tR} {fL = fL} {fR = fR}
                    eqL eqR refuses-merged (√ x) Be (sRet eq-tL-ret) =
    case trans (sym eqL) eq-tL-ret of λ ()
refusal-tL-from-tLR {tL = tL} eqL eqR refuses-merged (evl evi) Be
                    (sMixVis sM-eq _) =
    case trans (sym eqL) sM-eq of λ ()
refusal-tL-from-tLR {tL = tL} {tR = tR} {fL = fL} {fR = fR}
                    eqL eqR refuses-merged (evl evi) Be {Q = Q}
                    (sVis {at = at} {a = a} sV-eq-tL fL-eq-arg)
    with vis-injective (trans (sym eqL) sV-eq-tL)
... | refl
    with fR at a | inspect (fR at) a
... | nothing | [ fR-noth ] =
    refuses-merged (evl evi) Be (sVis {p = tL □ tR}
                              {f = λ ae → mergeVis (fL ae) (fR ae)}
                              {at = at} {a = a} {t′ = Q}
                              (force-□-vis-vis {P = tL} {Q = tR} {fP = fL} {fQ = fR} eqL eqR)
                              merged-eq)
  where
    merged-eq : (λ ae → mergeVis (fL ae) (fR ae)) at a ≡ just Q
    merged-eq rewrite fL-eq-arg | fR-noth = refl
... | just tR' | [ fR-eq ] =
    refuses-merged (evl evi) Be (sVis {p = tL □ tR}
                              {f = λ ae → mergeVis (fL ae) (fR ae)}
                              {at = at} {a = a} {t′ = Q ⊓ tR'}
                              (force-□-vis-vis {P = tL} {Q = tR} {fP = fL} {fQ = fR} eqL eqR)
                              merged-eq)
  where
    merged-eq : (λ ae → mergeVis (fL ae) (fR ae)) at a ≡ just (Q ⊓ tR')
    merged-eq rewrite fL-eq-arg | fR-eq = refl

-- Generalised asymmetric walker.  P τ*-reaches both tL and tR ⇒ any
-- failure of (tL □ tR) is a failure of P.  Structural recursion on
-- the bigstep; the {-# TERMINATING #-} pragma is needed because the
-- sSil case rebases via `subst` before recursion.
{-# TERMINATING #-}
asymm-walk-□ :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P tL tR : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → P ─[τ*]─► tL → P ─[τ*]─► tR
  → failures (tL □ tR) s B → failures P s B
-- bNil + ref-stable: (tL □ tR) is vis-stable.  By □-force-vis-inv,
-- force tL = vis fL and force tR = vis fR.  Project to refusal-of-tL,
-- prepend chL.
asymm-walk-□ {tL = tL} {tR = tR}
             chL chR (.(tL □ tR) , bNil , ref-stable st refuses)
    with stable→force-vis {t = tL □ tR} st
... | f-merged , force-tLR-vis
    with □-force-vis-inv {P = tL} {Q = tR} {f = f-merged} force-tLR-vis
... | fL , fR , eqL-vis , eqR-vis , _ =
        tL ,
        τ*-prepend-bigstep chL bNil ,
        ref-stable {P = tL}
                   (force-vis→stable {t = tL} eqL-vis)
                   (refusal-tL-from-tLR {tL = tL} {tR = tR}
                                        eqL-vis eqR-vis refuses)
-- bNil + ref-tick: force (tL □ tR) ≡ ret x.  By □-force-ret-inv, force
-- tL ≡ ret x or force tR ≡ ret x; pick the side and prepend its chain.
asymm-walk-□ {tL = tL} {tR = tR}
             chL chR (.(tL □ tR) , bNil , ref-tick {x = x} (sRet eq-tick) ¬B)
    with □-force-ret-inv {P = tL} {Q = tR} eq-tick
... | inj₁ eqL-ret =
        tL ,
        τ*-prepend-bigstep chL bNil ,
        ref-tick {P = tL} {x = x}
                 (sRet {p = tL} {x = x} eqL-ret)
                 ¬B
... | inj₂ eqR-ret =
        tR ,
        τ*-prepend-bigstep chR bNil ,
        ref-tick {P = tR} {x = x}
                 (sRet {p = tR} {x = x} eqR-ret)
                 ¬B
-- bStep sRet bNil (T = deadlock): same shape analysis as ref-tick.
asymm-walk-□ {tL = tL} {tR = tR}
             chL chR (.deadlock , bStep (sRet {x = x} eq-ret) bNil , ref)
    with □-force-ret-inv {P = tL} {Q = tR} eq-ret
... | inj₁ eqL-ret =
        deadlock ,
        τ*-prepend-bigstep chL (bStep (sRet {p = tL} {x = x} eqL-ret) bNil) ,
        ref
... | inj₂ eqR-ret =
        deadlock ,
        τ*-prepend-bigstep chR (bStep (sRet {p = tR} {x = x} eqR-ret) bNil) ,
        ref
-- bStep sRet (bTau ...): deadlock has no τ-step.  Impossible.
asymm-walk-□ _ _ (T , bStep (sRet _) (bTau step _) , _) =
    case step of λ where
      (sSil ())
      (sNdbr () _)
-- bStep sRet (bStep ...): deadlock has no event-step.  Impossible.
asymm-walk-□ _ _ (T , bStep (sRet _) (bStep step _) , _) =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep sVis ... rest: four sub-cases on fL at a / fR at a.
asymm-walk-□ {tL = tL} {tR = tR} chL chR
    (T , bStep (sVis {f = f} {at = at} {a = a} {t′ = t-merged} sV-eq f-eq) rest , ref)
    with □-force-vis-inv {P = tL} {Q = tR} {f = f} sV-eq
... | fL , fR , eqL-vis , eqR-vis , merge-eq
    with fL at a | inspect (fL at) a | fR at a | inspect (fR at) a
-- nn: contradicts f-eq.
... | nothing | [ fL-noth ] | nothing | [ fR-noth ] =
        ⊥-elim (case (trans (sym (trans (cong (λ g → g at a) merge-eq)
                                         (cong₂ mergeMaybe fL-noth fR-noth)))
                            f-eq)
                     of λ ())
-- jn: t-merged ≡ tL', prepend chL then sVis tL → tL'.
... | just tL' | [ fL-eq ] | nothing | [ fR-noth ] =
        T ,
        τ*-prepend-bigstep chL
            (bStep {t = tL} {t′ = tL'}
                   (sVis {p = tL} {f = fL} {at = at} {a = a} {t′ = tL'}
                         eqL-vis fL-eq)
                   rest-tL') ,
        ref
  where
    f-just-tL' : f at a ≡ just tL'
    f-just-tL' = trans (cong (λ g → g at a) merge-eq)
                       (cong₂ mergeMaybe fL-eq fR-noth)
    tL'≡t-merged : tL' ≡ t-merged
    tL'≡t-merged = just-injective (trans (sym f-just-tL') f-eq)
    rest-tL' : tL' ═⟨ _ ⟩═► T
    rest-tL' = subst (λ x → x ═⟨ _ ⟩═► T) (sym tL'≡t-merged) rest
-- nj: symmetric.
... | nothing | [ fL-noth ] | just tR' | [ fR-eq ] =
        T ,
        τ*-prepend-bigstep chR
            (bStep {t = tR} {t′ = tR'}
                   (sVis {p = tR} {f = fR} {at = at} {a = a} {t′ = tR'}
                         eqR-vis fR-eq)
                   rest-tR') ,
        ref
  where
    f-just-tR' : f at a ≡ just tR'
    f-just-tR' = trans (cong (λ g → g at a) merge-eq)
                       (cong₂ mergeMaybe fL-noth fR-eq)
    tR'≡t-merged : tR' ≡ t-merged
    tR'≡t-merged = just-injective (trans (sym f-just-tR') f-eq)
    rest-tR' : tR' ═⟨ _ ⟩═► T
    rest-tR' = subst (λ x → x ═⟨ _ ⟩═► T) (sym tR'≡t-merged) rest
-- jj: t-merged ≡ tL' ⊓ tR'.  ⊓-failures-elim splits into one side.
... | just tL' | [ fL-eq ] | just tR' | [ fR-eq ]
    with ⊓-failures-elim {P = tL'} {Q = tR'} (T , rest-merge , ref)
  where
    f-just-merge : f at a ≡ just (tL' ⊓ tR')
    f-just-merge = trans (cong (λ g → g at a) merge-eq)
                         (cong₂ mergeMaybe fL-eq fR-eq)
    tL'⊓tR'≡t-merged : (tL' ⊓ tR') ≡ t-merged
    tL'⊓tR'≡t-merged = just-injective (trans (sym f-just-merge) f-eq)
    rest-merge : (tL' ⊓ tR') ═⟨ _ ⟩═► T
    rest-merge = subst (λ x → x ═⟨ _ ⟩═► T) (sym tL'⊓tR'≡t-merged) rest
... | inj₁ (T-L , L-bigstep , ref-L) =
        T-L ,
        τ*-prepend-bigstep chL
            (bStep {t = tL} {t′ = tL'}
                   (sVis {p = tL} {f = fL} {at = at} {a = a} {t′ = tL'}
                         eqL-vis fL-eq)
                   L-bigstep) ,
        ref-L
... | inj₂ (T-R , R-bigstep , ref-R) =
        T-R ,
        τ*-prepend-bigstep chR
            (bStep {t = tR} {t′ = tR'}
                   (sVis {p = tR} {f = fR} {at = at} {a = a} {t′ = tR'}
                         eqR-vis fR-eq)
                   R-bigstep) ,
        ref-R
-- bTau sSil eqStep rest: by □-force-sil-inv, force tL or force tR has
-- a sil step.  Extend the corresponding chain by one sSil step and
-- recurse on the smaller bigstep `rest` at the new asymm form.
asymm-walk-□ {tL = tL} {tR = tR} chL chR (T , bTau (sSil eqStep) rest , ref)
    with □-force-sil-inv {P = tL} {Q = tR} eqStep
... | inj₁ (tL' , eqL-sil , refl) =
        asymm-walk-□
            (τ*-trans chL (τ*-step (sSil eqL-sil) τ*-zero))
            chR
            (T , rest , ref)
... | inj₂ (tR' , eqR-sil , refl) =
        asymm-walk-□
            chL
            (τ*-trans chR (τ*-step (sSil eqR-sil) τ*-zero))
            (T , rest , ref)
-- bTau sNdbr eqStep f-eq rest: handed off to `asymm-walk-□-bTau-sNdbr`.
asymm-walk-□ chL chR (T , bTau (sNdbr eqStep f-eq) rest , ref) =
    asymm-walk-□-bTau-sNdbr chL chR eqStep f-eq (T , rest , ref)
-- bTau sMixSlide / bStep sMixVis: dispatched to the postulated mix-aware
-- sub-helpers (forward-declared above).
asymm-walk-□ chL chR (T , bTau (sMixSlide eqStep) rest , ref) =
    asymm-walk-□-bTau-sMixSlide chL chR eqStep (T , rest , ref)
asymm-walk-□ chL chR (T , bStep (sMixVis {f = f} {Qt = Qt} {at = at} {a = a} {t′ = t'}
                                  eqStep f-eq) rest , ref) =
    asymm-walk-□-bStep-sMixVis chL chR eqStep f-eq (T , rest , ref)

-- (Old `failures-project-asymm-□-bStep-sVis` and
-- `failures-project-PP-bTau-sNdbr-J-both` removed — superseded by
-- `asymm-walk-□` above.)

-- Body of `asymm-walk-□-bTau-sNdbr` (forward-declared above).  Splits
-- into the four cases of `□-force-ndbr-inv` and unfolds the merge-form
-- continuation in each.
--   • D (ret/ret): merged g ≡ br2 tL tR; τ-step lands at tL or tR.
--   • H (vis/ndbr): merged g ≡ mergeNdbr-vis-L tL fR'; τ-step lands at
--     (tL □ t') for some tR-branch t'.  Recurse via `asymm-walk-□`.
--   • I (ndbr/vis): symmetric to H.
--   • J (ndbr/ndbr): merged g ≡ mergeNdbr fL' fR'.  Pair-indexed
--     branches give four sub-cases (nn/jn/nj/jj); jj recurses into
--     `asymm-walk-□`.
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    with □-force-ndbr-inv {P = tL} {Q = tR} eqStep
-- ============ Case D: ret r / ret r' with r ≠ r' ============
... | inj₁ (r , r' , neq , eqL-ret , eqR-ret)
    with trans (sym eqStep) (force-□-ndbr-D {P = tL} {Q = tR} eqL-ret eqR-ret neq)
... | refl = dispatch-D i a f-eq fail-V
  where
    -- After unification, g ≡ br2 tL tR, wi ≡ (Lift _ (Fin 2) , fin),
    -- wa ≡ lift fzero, wp ≡ any-just tt₀.  Case on (i, a) via br2.
    dispatch-D : ∀ (i' : AnyTypes (ExtI _)) (a' : proj₁ i') {V'}
               → br2 tL tR i' a' ≡ just V'
               → failures V' s B
               → failures P s B
    dispatch-D (_ , fin) (lift fzero) refl (T , bs , ref) =
        T , τ*-prepend-bigstep chL bs , ref
    dispatch-D (_ , fin) (lift (fsuc fzero)) refl (T , bs , ref) =
        T , τ*-prepend-bigstep chR bs , ref
    dispatch-D (_ , fin) (lift (fsuc (fsuc _))) () _
    dispatch-D (_ , base _) _ () _
    dispatch-D (_ , pair _ _) _ () _
-- ============ Case H: vis fL / ndbr fR' ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₁ (fL , fR' , wiR , waR , wpR , eqL-vis , eqR-ndbr))
    with trans (sym eqStep) (force-□-vis-ndbr-eq {P = tL} {Q = tR} eqL-vis eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          fail-V
-- ============ Case I: ndbr fL' / vis fR ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , fR , eqL-ndbr , eqR-vis)))
    with trans (sym eqStep) (force-□-ndbr-vis-eq {P = tL} {Q = tR} eqL-ndbr eqR-vis)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          fail-V
-- ============ Case J: ndbr fL' / ndbr fR' ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , fR' , wiR , waR , wpR ,
                               eqL-ndbr , eqR-ndbr))))
    with trans (sym eqStep) (force-□-ndbr-ndbr-eq {P = tL} {Q = tR} eqL-ndbr eqR-ndbr)
... | refl = dispatch-J i a f-eq fail-V
  where
    -- Inner dispatcher for case J: case on (i, a) and the two fL'/fR'
    -- evaluations.  Productive only at pair-indexed branches; non-pair
    -- branches return `nothing` (mergeNdbr).
    dispatch-J : ∀ (i' : AnyTypes (ExtI _)) (a' : proj₁ i') {V'}
               → mergeNdbr fL' fR' i' a' ≡ just V'
               → failures V' s B
               → failures P s B
    dispatch-J (_ , base _) _ () _
    dispatch-J (_ , fin)    _ () _
    dispatch-J (.(AL × AR) , pair {AL} {AR} iL' iR') (aL' , aR') f-eq-pair fail-V'
        with fL' (AL , iL') aL' | inspect (fL' (AL , iL')) aL'
           | fR' (AR , iR') aR' | inspect (fR' (AR , iR')) aR'
           | f-eq-pair
    -- nn: mergeNdbr returns nothing.
    ... | nothing | _ | nothing | _ | ()
    -- jn: V' = tL''.  Prepend chL extended by sNdbr (tL → tL'').
    ... | just tL'' | [ fL'-eq ] | nothing | [ _ ] | refl =
        case fail-V' of λ where
          (T , bs , ref) →
            T ,
            τ*-prepend-bigstep
              (τ*-trans chL
                        (τ*-step (sNdbr {p = tL} {f = fL'}
                                        {wi = wiL} {wa = waL} {prf = wpL}
                                        {i = (AL , iL')} {a = aL'} {t′ = tL''}
                                        eqL-ndbr fL'-eq)
                                 τ*-zero))
              bs ,
            ref
    -- nj: symmetric.
    ... | nothing | [ _ ] | just tR'' | [ fR'-eq ] | refl =
        case fail-V' of λ where
          (T , bs , ref) →
            T ,
            τ*-prepend-bigstep
              (τ*-trans chR
                        (τ*-step (sNdbr {p = tR} {f = fR'}
                                        {wi = wiR} {wa = waR} {prf = wpR}
                                        {i = (AR , iR')} {a = aR'} {t′ = tR''}
                                        eqR-ndbr fR'-eq)
                                 τ*-zero))
              bs ,
            ref
    -- jj: V' = tL'' □ tR''.  Recurse with both chains extended.
    ... | just tL'' | [ fL'-eq ] | just tR'' | [ fR'-eq ] | refl =
        asymm-walk-□
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = (AL , iL')} {a = aL'} {t′ = tL''}
                                    eqL-ndbr fL'-eq)
                             τ*-zero))
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = (AR , iR')} {a = aR'} {t′ = tR''}
                                    eqR-ndbr fR'-eq)
                             τ*-zero))
          fail-V'
-- ============ Case K: ret r / ndbr fR' (new under post-mix _□_) ============
-- Force (tL □ tR) = ndbr (mergeNdbr-vis-L tL fR').  Same fR' fires; prepend
-- chR by sNdbr of tR.
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (r , fR' , wiR , waR , wpR , eqL-ret , eqR-ndbr)))))
    with trans (sym eqStep) (force-□-ret-ndbr-eq {P = tL} {Q = tR} eqL-ret eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          fail-V
-- ============ Case L: ndbr fL' / ret r (new under post-mix _□_) ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , r , eqL-ndbr , eqR-ret))))))
    with trans (sym eqStep) (force-□-ndbr-ret-eq {P = tL} {Q = tR} eqL-ndbr eqR-ret)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          fail-V
-- ============ Case M: mix _ _ / ndbr fR' (new under post-mix _□_) ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (fmL , Lt , fR' , wiR , waR , wpR , eqL-mix , eqR-ndbr)))))))
    with trans (sym eqStep) (force-□-mix-ndbr-eq {P = tL} {Q = tR} eqL-mix eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          fail-V
-- ============ Case N: ndbr fL' / mix _ _ (new under post-mix _□_) ============
asymm-walk-□-bTau-sNdbr {P = P} {tL = tL} {tR = tR}
                        {i = i} {a = a} {s = s} {B = B}
                        chL chR eqStep f-eq fail-V
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (fL' , wiL , waL , wpL , fmR , Rt , eqL-ndbr , eqR-mix)))))))
    with trans (sym eqStep) (force-□-ndbr-mix-eq {P = tL} {Q = tR} eqL-ndbr eqR-mix)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-walk-□
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          fail-V
-- Case-J body: after inverting force (P □ P) ≡ ndbr ... back to
-- force P ≡ ndbr fP wiP waP wpP and computing `force (P □ P)` to the
-- merged form, we case on `i` (must be `pair` to give `just U`) and on
-- `fP (·, iL) aL` / `fP (·, iR) aR`.
failures-project-PP-bTau-sNdbr-J :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R}
    {fP : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wiP : AnyTypes (ExtI I)} {waP : proj₁ wiP} {wpP : Is-just (fP wiP waP)}
    {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wi : AnyTypes (ExtI I)} {wa : proj₁ wi} {wp : Is-just (f wi wa)}
    {i : AnyTypes (ExtI I)} {a : proj₁ i}
    {U : ITree E (ExtI I) R}
    {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ ndbr fP wiP waP wpP
  → ITree.force (P □ P) ≡ ndbr f wi wa wp
  → f i a ≡ just U
  → failures U s B
  → failures P s B
failures-project-PP-bTau-sNdbr-J {I = I} {R = R}
                                  {P = P} {fP = fP} {wiP = (AP , iP-ext)} {waP = waP} {wpP = wpP}
                                  {i = i} {a = a}
                                  eqP eqStep f-eq fail-U
    rewrite eqP
    with eqStep
... | refl = dispatch-i i a f-eq fail-U
  where
    -- After `rewrite eqP` and `with refl` on eqStep:
    --   f  ≡ mergeNdbr fP fP
    --   wi ≡ (AP × AP , pair iP-ext iP-ext)
    --   wa ≡ (waP , waP)
    --   wp ≡ mergeNdbr-witness fP fP wpP wpP
    -- f-eq is now of type `mergeNdbr fP fP i a ≡ just U`.
    dispatch-i :
      ∀ (i : AnyTypes (ExtI I)) (a : proj₁ i)
      → mergeNdbr fP fP i a ≡ just _
      → failures _ _ _
      → failures P _ _
    -- base case: mergeNdbr returns nothing.
    dispatch-i (A , base _) a () _
    -- fin case: mergeNdbr returns nothing.
    dispatch-i (_ , fin) a () _
    -- pair case: dispatch on fP (AL,iL) aL and fP (AR,iR) aR.
    dispatch-i (.(AL × AR) , pair {AL} {AR} iL iR) (aL , aR) f-eq fail-U =
        dispatch-pair iL iR aL aR f-eq fail-U (fP (AL , iL) aL) refl
                                              (fP (AR , iR) aR) refl
      where
        -- Inner dispatch: case on the two fP-evaluations via inspect-style refl.
        dispatch-pair :
          ∀ (iL : ExtI I AL) (iR : ExtI I AR) (aL : AL) (aR : AR)
          → mergeNdbr fP fP ((AL × AR) , pair iL iR) (aL , aR) ≡ just _
          → failures _ _ _
          → ∀ (mL : Maybe (ITree E (ExtI I) R))
          → fP (AL , iL) aL ≡ mL
          → ∀ (mR : Maybe (ITree E (ExtI I) R))
          → fP (AR , iR) aR ≡ mR
          → failures P _ _
        -- both nothing: mergeNdbr returns nothing, contradicting just U.
        dispatch-pair iL iR aL aR f-eq _ nothing eqL nothing eqR
            rewrite eqL | eqR with f-eq
        ... | ()
        -- left just, right nothing: U = tL.  Easy prepend.
        dispatch-pair iL iR aL aR f-eq fail-U (just tL) eqL nothing eqR
            rewrite eqL | eqR with f-eq
        ... | refl with fail-U
        ... | T , bigstep , ref =
                 T ,
                 bTau {t = P} {t′ = tL}
                      (sNdbr {p = P} {f = fP} {wi = (AP , iP-ext)}
                             {wa = waP} {prf = wpP}
                             {i = (AL , iL)} {a = aL} {t′ = tL}
                             eqP eqL)
                      bigstep ,
                 ref
        -- left nothing, right just: U = tR.  Symmetric easy prepend.
        dispatch-pair iL iR aL aR f-eq fail-U nothing eqL (just tR) eqR
            rewrite eqL | eqR with f-eq
        ... | refl with fail-U
        ... | T , bigstep , ref =
                 T ,
                 bTau {t = P} {t′ = tR}
                      (sNdbr {p = P} {f = fP} {wi = (AP , iP-ext)}
                             {wa = waP} {prf = wpP}
                             {i = (AR , iR)} {a = aR} {t′ = tR}
                             eqP eqR)
                      bigstep ,
                 ref
        -- both just: U = tL □ tR.  Build single-step τ*-chains
        -- P → tL and P → tR from the sNdbr witnesses, then dispatch to
        -- the unified asymmetric walker.
        dispatch-pair iL iR aL aR f-eq fail-U (just tL) eqL (just tR) eqR
            rewrite eqL | eqR with f-eq
        ... | refl =
            asymm-walk-□
              (τ*-step (sNdbr {p = P} {f = fP} {wi = (AP , iP-ext)}
                              {wa = waP} {prf = wpP}
                              {i = (AL , iL)} {a = aL} {t′ = tL}
                              eqP eqL)
                       τ*-zero)
              (τ*-step (sNdbr {p = P} {f = fP} {wi = (AP , iP-ext)}
                              {wa = waP} {prf = wpP}
                              {i = (AR , iR)} {a = aR} {t′ = tR}
                              eqP eqR)
                       τ*-zero)
              fail-U

-- The bTau-sNdbr discharger.  Inverts the τ-step via `□-force-ndbr-inv`
-- specialised to P=Q=P, eliminates the absurd cases D/H/I (where same-P
-- forces conflict on shape), and dispatches to the case-J postulate.
failures-project-PP-bTau-sNdbr :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R}
    {f : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))}
    {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
    {wp : Is-just (f wi wa)}
    {i : AnyTypes (ExtI I)} {a : proj₁ i}
    {U : ITree E (ExtI I) R}
    {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → ITree.force (P □ P) ≡ ndbr f wi wa wp
  → f i a ≡ just U
  → failures U s B
  → failures P s B
failures-project-PP-bTau-sNdbr {P = P} eqStep f-eq fail-U
    with □-force-ndbr-inv {P = P} {Q = P} eqStep
-- Case D: force P = ret r AND force P = ret r' with r ≢ r'.  Same P
-- forces r ≡ r', contradicting neq.
... | inj₁ (r , r' , neq , eqP , eqP') =
        ⊥-elim (case trans (sym eqP) eqP' of λ where refl → neq refl)
-- Case H: force P = vis _ AND force P = ndbr _.  Contradiction.
... | inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-vis , eqP-ndbr)) =
        case trans (sym eqP-vis) eqP-ndbr of λ ()
-- Case I: force P = ndbr _ AND force P = vis _.  Contradiction.
... | inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ndbr , eqP-vis))) =
        case trans (sym eqP-ndbr) eqP-vis of λ ()
-- Case J: force P = ndbr fP wiP waP wpP (and same on RHS).  Dispatch.
... | inj₂ (inj₂ (inj₂ (inj₁ (fP , wiP , waP , wpP , _ , _ , _ , _ , eqP , _)))) =
        failures-project-PP-bTau-sNdbr-J eqP eqStep f-eq fail-U
-- Case K: force P = ret _ AND force P = ndbr _.  Contradiction.
... | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ret , eqP-ndbr))))) =
        case trans (sym eqP-ret) eqP-ndbr of λ ()
-- Case L: force P = ndbr _ AND force P = ret _.  Contradiction.
... | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ndbr , eqP-ret)))))) =
        case trans (sym eqP-ndbr) eqP-ret of λ ()
-- Case M: force P = mix _ _ AND force P = ndbr _.  Contradiction.
... | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , _ , eqP-mix , eqP-ndbr))))))) =
        case trans (sym eqP-mix) eqP-ndbr of λ ()
-- Case N: force P = ndbr _ AND force P = mix _ _.  Contradiction.
... | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (_ , _ , _ , _ , _ , _ , eqP-ndbr , eqP-mix))))))) =
        case trans (sym eqP-ndbr) eqP-mix of λ ()

-- The dispatcher: case on the τ-step's constructor.
failures-project-PP-bTau :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P U : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → (P □ P) ─[ τ ]─► U
  → failures U s B
  → failures P s B
failures-project-PP-bTau (sSil eqStep)      fail-U =
    failures-project-PP-bTau-sSil  eqStep       fail-U
failures-project-PP-bTau (sNdbr eqStep f-eq) fail-U =
    failures-project-PP-bTau-sNdbr eqStep f-eq  fail-U
-- sMixSlide / sMixVis cases: dispatched to top-level postulates declared
-- after the failures-project-PP block.
failures-project-PP-bTau {P = P} (sMixSlide eqStep) fail-U =
    failures-project-PP-bTau-sMixSlide eqStep fail-U

-- Backward direction body (forward-declared above).
-- bNil: T'' = P □ P.  Refusal projects via `PP-ref→P-ref`.
failures-project-PP {P = P} (.(P □ P) , bNil , ref) =
    P , bNil , PP-ref→P-ref ref
-- bStep / sRet at force (P □ P) ≡ ret r.  By `□-force-ret-inv` (both
-- `inj₁` and `inj₂` give the same equation for P=Q=P), force P ≡ ret r.
failures-project-PP {P = P} (.deadlock , bStep (sRet eq) bNil , ref)
  with □-force-ret-inv {P = P} {Q = P} eq
... | inj₁ eqP =
        deadlock ,
        bStep {t = P} {t′ = deadlock} (sRet {p = P} eqP) bNil ,
        ref
... | inj₂ eqP =
        deadlock ,
        bStep {t = P} {t′ = deadlock} (sRet {p = P} eqP) bNil ,
        ref
-- bStep / sRet with non-bNil residual: deadlock has no transitions,
-- so the residual must be bNil.
failures-project-PP (T , bStep (sRet _) (bTau step _) , _) =
    case step of λ where
      (sSil ())
      (sNdbr () _)
failures-project-PP (T , bStep (sRet _) (bStep step _) , _) =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep / sVis: visible step from P □ P.  By `□-force-vis-inv`,
-- `force P ≡ vis fP` and `force P ≡ vis fQ` with merged map
-- `mergeVis fP fQ`.  `vis-injective` collapses `fP ≡ fQ`.
-- For `fP at a = nothing` the merged value is `nothing`, contradicting
-- `f-eq : f at a ≡ just t-merged`.  For `fP at a = just p`, the merged
-- map gives `just (p ⊓ p)`, so `t-merged ≡ p ⊓ p`.  Then `rest` from
-- `t-merged` rebases to `p ⊓ p`, and `⊓-failures-elim` projects it to
-- a failure of `p`.  Prepend `bStep (sVis eqP fP-eq)` on P.
failures-project-PP {P = P}
  (T , bStep (sVis {f = f} {at = at} {a = a} {t′ = t-merged}
                    sV-eq f-eq) rest , ref)
  with □-force-vis-inv {P = P} {Q = P} {f = f} sV-eq
... | fP , fQ , eqP , eqQ , merge-eq
  with vis-injective (trans (sym eqP) eqQ)
... | refl  -- fQ unified with fP
  with fP at a | inspect (fP at) a
... | nothing | [ fP-noth ] =
        ⊥-elim (case (trans (sym (trans (cong (λ g → g at a) merge-eq)
                                         (cong₂ mergeMaybe fP-noth fP-noth)))
                            f-eq)
                     of λ ())
... | just p | [ fP-eq ]
    with ⊓-failures-elim {P = p} {Q = p} (T , rest-p⊓p , ref)
  where
    -- After the refl-unification, `merge-eq` collapses to
    --   f ≡ λ Ae → mergeVis (fP Ae) (fP Ae)
    -- so `f at a = mergeMaybe (fP at a) (fP at a)`.
    -- With `fP at a ≡ just p`, this evaluates to `just (p ⊓ p)`.
    f-just-pp : f at a ≡ just (p ⊓ p)
    f-just-pp = trans (cong (λ g → g at a) merge-eq)
                      (cong₂ mergeMaybe fP-eq fP-eq)
    -- t-merged ≡ p ⊓ p (extracted from `f-eq` and `f-just-pp`).
    p⊓p≡t-merged : p ⊓ p ≡ t-merged
    p⊓p≡t-merged = just-injective (trans (sym f-just-pp) f-eq)
    -- Rebase the residual from `t-merged` to `p ⊓ p`.
    rest-p⊓p : (p ⊓ p) ═⟨ _ ⟩═► T
    rest-p⊓p = subst (λ x → x ═⟨ _ ⟩═► T) (sym p⊓p≡t-merged) rest
... | inj₁ (T'-p , p-bigstep , ref-p) =
        T'-p ,
        bStep {t = P} {t′ = p}
              (sVis {p = P} {f = fP} {at = at} {a = a} {t′ = p}
                    eqP fP-eq)
              p-bigstep ,
        ref-p
... | inj₂ (T'-p , p-bigstep , ref-p) =
        T'-p ,
        bStep {t = P} {t′ = p}
              (sVis {p = P} {f = fP} {at = at} {a = a} {t′ = p}
                    eqP fP-eq)
              p-bigstep ,
        ref-p
-- bTau: dispatched to postulate.
failures-project-PP (T , bTau step rest , ref) =
    failures-project-PP-bTau step (T , rest , ref)
-- bStep / sMixVis: dispatched to the top-level postulate (no `where` to
-- avoid shadowing the infix `_ref_` by the local `ref` pattern variable).
failures-project-PP {P = P} (T , bStep (sMixVis eq f-eq) rest , ref) =
    failures-project-PP-bStep-sMixVis eq f-eq (T , rest , ref)

-- Asymmetric divergence lift.  KEY OBSERVATION: requiring `Divergent`
-- on BOTH sides closes the asymmetric problem — `Divergent t` rules out
-- `force t ≡ ret` (ret is stable, no τ-step), so the problematic
-- `force (X □ Y) = ret r` case (rule F) cannot arise.  Each step of
-- `(tL □ tR)` is constructed by:
--   • sSil-LEFT when `dtL`'s next step is sSil (force tL = sil),
--   • sSil-RIGHT when `dtL` is ndbr and `dtR`'s next step is sSil
--     (force tR = sil; tL stable from being ndbr-shaped),
--   • sNdbr at the diagonal pair when both `dtL` and `dtR` step via sNdbr.
-- Each branch produces a Divergent record (productively guarded), and
-- the recursive `divergent-□-asymm-orig` calls in the `diverge` field
-- are guarded by the surrounding constructor.
{-# TERMINATING #-}
divergent-□-asymm-orig :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {tL tR : ITree E (ExtI I) R}
  → Divergent tL → Divergent tR → Divergent (tL □ tR)
divergent-□-asymm-orig {tL = tL} {tR = tR} dtL dtR
    with dtL .Divergent.step | dtL .Divergent.diverge
... | sSil eqL-sil | dtL-next =
        record { next    = (dtL .Divergent.next) □ tR
               ; step    = sSil (force-□-sil-left {P = tL} {Q = tR} eqL-sil)
               ; diverge = divergent-□-asymm-orig dtL-next dtR }
... | sNdbr {f = fL} eqL-ndbr fL-eq | dtL-next
    with dtR .Divergent.step | dtR .Divergent.diverge
... | sSil eqR-sil | dtR-next =
        record { next    = tL □ (dtR .Divergent.next)
               ; step    = sSil (force-□-sil-right-ndbr
                                  {P = tL} {Q = tR}
                                  eqL-ndbr eqR-sil)
               ; diverge = divergent-□-asymm-orig dtL dtR-next }
... | sNdbr {f = fR} eqR-ndbr fR-eq | dtR-next =
        record { next    = (dtL .Divergent.next) □ (dtR .Divergent.next)
               ; step    = sNdbr
                            (force-□-ndbr-ndbr-eq {P = tL} {Q = tR}
                                                  eqL-ndbr eqR-ndbr)
                            (mergeNdbr-pair-jj fL fR fL-eq fR-eq)
               ; diverge = divergent-□-asymm-orig dtL-next dtR-next }
-- sMixSlide branch from tR while tL is ndbr.  Dispatched to top-level postulate.
... | sMixSlide eqR-mix | dtR-next =
        divergent-□-mix-asymm dtL dtR
-- sMixSlide branch from tL.  Same postulate (parameter order absorbs which side mixes).
divergent-□-asymm-orig {tL = tL} {tR = tR} dtL dtR
    | sMixSlide eqL-mix | dtL-next =
        divergent-□-mix-asymm dtL dtR

-- Symmetric divergence lift: `Divergent P → Divergent (P □ P)`.  Just
-- the asymm version with both sides being the same `dP`.
divergent-□-symm :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R}
  → Divergent P → Divergent (P □ P)
divergent-□-symm dP = divergent-□-asymm-orig dP dP

-- Mutually recursive forward declarations.  `divergences-lift-PP-bigstep`
-- handles all bigstep cases by dispatch; its bTau-sSil clause delegates
-- to `divergences-lift-PP-bTau-sSil`, which uses an inline walker
-- (structural recursion on the bigstep) and then calls back into
-- `divergences-lift-PP-bigstep` on the peeled bigstep.  Termination is
-- on the bigstep size; the {-# TERMINATING #-} pragma is needed because
-- Agda's termination checker doesn't see across the mutual recursion.
divergences-lift-PP-bigstep :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {t : ITree E (ExtI I) R}
    {pre : List (Event√ E R)} {Q : ITree E (ExtI I) R}
  → t ═⟨ pre ⟩═► Q → Divergent Q
  → Σ[ T' ∈ ITree E (ExtI I) R ]
      ((t □ t) ═⟨ pre ⟩═► T' × Divergent T')

divergences-lift-PP-bTau-sSil :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P P' : ITree E (ExtI I) R}
    {pre : List (Event√ E R)} {Q : ITree E (ExtI I) R}
  → ITree.force P ≡ sil P'
  → P' ═⟨ pre ⟩═► Q
  → Divergent Q
  → Σ[ T' ∈ ITree E (ExtI I) R ]
      ((P □ P) ═⟨ pre ⟩═► T' × Divergent T')

-- Body of `divergences-lift-PP-bigstep`.  Mirrors the case structure of
-- `failures-lift-PP` but operates on (bigstep + Divergent witness)
-- instead of (bigstep + refusal).
-- {-# TERMINATING #-}
-- bNil: witness transforms from t to (t □ t) via divergent-□-symm.
divergences-lift-PP-bigstep {t = t} bNil dw' =
    t □ t , bNil , divergent-□-symm dw'
-- bStep sRet bNil: T = deadlock; Divergent deadlock impossible.
divergences-lift-PP-bigstep {t = t} (bStep (sRet _) bNil) dw' =
    ⊥-elim (deadlock-not-div dw')
  where
    deadlock-not-div : Divergent deadlock → ⊥
    deadlock-not-div ddw with ddw .Divergent.step
    ... | sSil ()
    ... | sNdbr () _
-- bStep sRet (bTau ...): impossible (deadlock has no τ).
divergences-lift-PP-bigstep (bStep (sRet _) (bTau step _)) _ =
    case step of λ where
      (sSil ())
      (sNdbr () _)
-- bStep sRet (bStep ...): impossible (deadlock has no event step).
divergences-lift-PP-bigstep (bStep (sRet _) (bStep step _)) _ =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep sVis: lift via merged-vis + ⊓-step-L; splice rest unchanged.
divergences-lift-PP-bigstep {t = t} {Q = Q}
    (bStep (sVis {f = fP} {at = at} {a = a} {t′ = t'}
                  sV-eq fP-eq)
           rest) dw' =
    Q ,
    bStep {t = t □ t} {t′ = t' ⊓ t'}
          (sVis {p = t □ t} {f = λ Ae → mergeVis (fP Ae) (fP Ae)}
                {at = at} {a = a} {t′ = t' ⊓ t'}
                (force-□-vis-vis {P = t} {Q = t}
                                 {fP = fP} {fQ = fP} sV-eq sV-eq)
                merged-just)
          (bTau (⊓-step-L t' t') rest) ,
    dw'
  where
    merged-just :
        (λ Ae → mergeVis (fP Ae) (fP Ae)) at a ≡ just (t' ⊓ t')
    merged-just rewrite fP-eq = refl
-- bTau sSil: dispatch to walker-driven helper.
divergences-lift-PP-bigstep {t = t} (bTau (sSil eq) rest) dw' =
    divergences-lift-PP-bTau-sSil eq rest dw'
-- bTau sNdbr: lift via diagonal-pair sNdbr; recurse on rest at t'.
divergences-lift-PP-bigstep {t = t}
    (bTau (sNdbr {f = fP} {wi = (AP-ext , iP-ext)} {wa = waP} {prf = wpP}
                 {i = (AI-ext , iI-ext)} {a = aᵢ} {t′ = t'}
                 eq f-eq)
          rest) dw'
    with divergences-lift-PP-bigstep {t = t'} rest dw'
... | T'' , big-t'-□-t' , dw'' =
    T'' ,
    bTau {t = t □ t} {t′ = t' □ t'}
         (sNdbr {p = t □ t}
                {f = mergeNdbr fP fP}
                {wi = ((AP-ext × AP-ext) , pair iP-ext iP-ext)}
                {wa = (waP , waP)}
                {prf = mergeNdbr-witness fP fP wpP wpP}
                {i = ((AI-ext × AI-ext) , pair iI-ext iI-ext)}
                {a = (aᵢ , aᵢ)}
                {t′ = t' □ t'}
                force-eq-tt
                merge-eq-diag)
         big-t'-□-t' ,
    dw''
  where
    force-eq-tt :
      ITree.force (t □ t) ≡
        ndbr (mergeNdbr fP fP)
             ((AP-ext × AP-ext) , pair iP-ext iP-ext)
             (waP , waP)
             (mergeNdbr-witness fP fP wpP wpP)
    force-eq-tt rewrite eq = refl

    merge-eq-diag :
      mergeNdbr fP fP
        ((AI-ext × AI-ext) , pair iI-ext iI-ext)
        (aᵢ , aᵢ)
      ≡ just (t' □ t')
    merge-eq-diag rewrite f-eq = refl
-- bTau sMixSlide / bStep sMixVis (post-mix): dispatched to top-level
-- postulates (declared with the other mix-shape projection helpers).
divergences-lift-PP-bigstep (bTau (sMixSlide eq) rest) dw' =
    divergences-lift-PP-bTau-sMixSlide eq rest dw'
divergences-lift-PP-bigstep (bStep (sMixVis eq f-eq) bNil) dw' =
    divergences-lift-PP-bStep-sMixVis-bNil eq f-eq dw'
divergences-lift-PP-bigstep (bStep (sMixVis eq f-eq) (bTau s rest)) dw' =
    divergences-lift-PP-bStep-sMixVis-bTau eq f-eq s rest dw'
divergences-lift-PP-bigstep (bStep (sMixVis eq f-eq) (bStep s rest)) dw' =
    divergences-lift-PP-bStep-sMixVis-bStep eq f-eq s rest dw'

-- Body of `divergences-lift-PP-bTau-sSil`.  Walk the bigstep's sSil
-- prefix to a τ*-derivative `Ys` (with chain `P' →[sSil*]→ Ys`).
-- Then dispatch on the peeled bigstep:
--   • bNil at Ys = Q with `dw .step = sSil`: all-sil Q.  No NonSilForce
--     available; instead build `Divergent P` via `divergent-prefix` on
--     the chain `P →[τ*]→ Q` and use `bNil` at `(P □ P)`.
--   • bNil at Ys = Q with `dw .step = sNdbr`: `force Q ≡ ndbr` gives
--     NonSilForce Q.  Build chain `(P □ P) →[τ*]→ (Q □ Q)` and prepend
--     to `bNil` at `(Q □ Q)`.
--   • bTau (sNdbr eq _) ...: NonSilForce Ys via `nsf-ndbr eq`; recurse
--     via `divergences-lift-PP-bigstep` and prepend chain.
--   • bStep (sRet eq) ...: NonSilForce Ys via `nsf-ret eq`; recurse and
--     prepend (recursion discharges via `Divergent deadlock → ⊥`).
--   • bStep (sVis eq _) ...: NonSilForce Ys via `nsf-vis eq`; recurse
--     and prepend.
-- Body uses an inline walker (instead of `walk-and-peel-bigstep`)
-- since structural recursion on the bigstep gives all five head cases
-- including bTau-sSil (which recurses with extended chain).
divergences-lift-PP-bTau-sSil {I = I} {R = R} {P = P} {P' = P'} {pre = pre} {Q = Q}
                              eq rest dw =
    walker (sSil*-step eq sSil*-zero) rest
  where
    -- Build `(P □ P) →[τ*]→ (Y □ Y)` given chain `P →[sSil*]→ Y` and
    -- `NonSilForce Y`.  LEFT side: left-walk-□.  RIGHT side: right-walk-□.
    build-PP-to-YY :
        ∀ {Y : ITree E (ExtI I) R}
      → P ─[sSil*]─► Y → NonSilForce Y
      → (P □ P) ─[τ*]─► (Y □ Y)
    build-PP-to-YY chain nsf-Y =
        τ*-trans (left-walk-□ {Y = P} chain)
                 (right-walk-□ {Y = P} nsf-Y chain)

    walker :
        ∀ {Y : ITree E (ExtI I) R}
      → P ─[sSil*]─► Y → Y ═⟨ pre ⟩═► Q
      → Σ[ T' ∈ ITree E (ExtI I) R ]
          ((P □ P) ═⟨ pre ⟩═► T' × Divergent T')
    -- bTau sSil: peel and recurse with extended chain.
    walker chain (bTau (sSil eq') rest') =
        walker (sSil*-snoc chain eq') rest'
    -- bNil (Y = Q, pre = []): dispatch on dw's first step.
    walker chain bNil with dw .Divergent.step
    -- All-sil Q: derive `Divergent P` from chain + dw via divergent-prefix.
    ... | sSil _ =
        P □ P , bNil ,
        divergent-□-symm
          (divergent-prefix (sSil*→τ* chain) dw)
    -- ndbr Q: NonSilForce-ndbr from divwit; output is (Q □ Q, bNil, …).
    ... | sNdbr eq-Q-ndbr _ =
        Q □ Q ,
        τ*-prepend-bigstep
          (build-PP-to-YY chain (nsf-ndbr eq-Q-ndbr))
          bNil ,
        divergent-□-symm dw
    -- sMixSlide Q: NonSilForce-mix; output is (Q □ Q, bNil, …).
    ... | sMixSlide eq-Q-mix =
        Q □ Q ,
        τ*-prepend-bigstep
          (build-PP-to-YY chain (nsf-mix eq-Q-mix))
          bNil ,
        divergent-□-symm dw
    -- bTau sNdbr at Y: NonSilForce-ndbr; recurse via *-bigstep then prepend.
    walker {Y = Y} chain (bTau (sNdbr eq-Y-ndbr f-eq) rest')
        with divergences-lift-PP-bigstep {t = Y}
                (bTau (sNdbr eq-Y-ndbr f-eq) rest') dw
    ... | T' , big-Y-Y , dw' =
            T' ,
            τ*-prepend-bigstep
              (build-PP-to-YY chain (nsf-ndbr eq-Y-ndbr))
              big-Y-Y ,
            dw'
    -- bStep sRet at Y: NonSilForce-ret.  *-bigstep discharges via
    -- `Divergent deadlock → ⊥`.
    walker {Y = Y} chain (bStep (sRet eq-Y-ret) rest')
        with divergences-lift-PP-bigstep {t = Y}
                (bStep (sRet eq-Y-ret) rest') dw
    ... | T' , big-Y-Y , dw' =
            T' ,
            τ*-prepend-bigstep
              (build-PP-to-YY chain (nsf-ret eq-Y-ret))
              big-Y-Y ,
            dw'
    -- bStep sVis at Y: NonSilForce-vis.
    walker {Y = Y} chain (bStep (sVis eq-Y-vis f-eq) rest')
        with divergences-lift-PP-bigstep {t = Y}
                (bStep (sVis eq-Y-vis f-eq) rest') dw
    ... | T' , big-Y-Y , dw' =
            T' ,
            τ*-prepend-bigstep
              (build-PP-to-YY chain (nsf-vis eq-Y-vis))
              big-Y-Y ,
            dw'
    -- bTau sMixSlide / bStep sMixVis at Y: Y is mix-shaped (NonSilForce-mix).
    walker {Y = Y} chain (bTau (sMixSlide eq-Y-mix) rest')
        with divergences-lift-PP-bigstep {t = Y}
                (bTau (sMixSlide eq-Y-mix) rest') dw
    ... | T' , big-Y-Y , dw' =
            T' ,
            τ*-prepend-bigstep
              (build-PP-to-YY chain (nsf-mix eq-Y-mix))
              big-Y-Y ,
            dw'
    walker {Y = Y} chain (bStep (sMixVis eq-Y-mix f-eq) rest')
        with divergences-lift-PP-bigstep {t = Y}
                (bStep (sMixVis eq-Y-mix f-eq) rest') dw
    ... | T' , big-Y-Y , dw' =
            T' ,
            τ*-prepend-bigstep
              (build-PP-to-YY chain (nsf-mix eq-Y-mix))
              big-Y-Y ,
            dw'

-- Forward (lift) for divergences:  divergences P s → divergences (P □ P) s.
-- Just dispatches to `divergences-lift-PP-bigstep` on the bigstep portion.
divergences-lift-PP :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences P s → divergences (P □ P) s
divergences-lift-PP {P = P}
    record { prefix = pre; suffix = suf; split = sp
           ; witness = Q; reach = bs; divwit = dw } =
    let (T' , bs' , dw') = divergences-lift-PP-bigstep {t = P} bs dw
    in record { prefix  = pre
              ; suffix  = suf
              ; split   = sp
              ; witness = T'
              ; reach   = bs'
              ; divwit  = dw' }

-- Asymmetric divergence extraction.  `Divergent (tL □ tR) → Divergent tL
-- ⊎ Divergent tR`.  This is the **König step** in the CSP-FD divergence
-- projection: an infinite τ-chain in `(tL □ tR)` must have an infinite
-- suffix that consistently advances LEFT (yielding `Divergent tL`) or
-- RIGHT (`Divergent tR`).  Each step of the chain is a LEFT-walk
-- (sil-LEFT / sNdbr-L / J-jn / D-fzero), a RIGHT-walk (sil-RIGHT /
-- sNdbr-R / J-nj / D-fsuc), or a BOTH-walk (J-jj).  At least one side
-- must be advanced infinitely often, but **deciding which is fundamentally
-- non-constructive over an infinite chain**.
--
-- Standard CSP textbooks (e.g. Roscoe TPC) prove the corresponding
-- divergence-projection law `divergences (P □ Q) ⊆ divergences P ∪
-- divergences Q` using classical logic at this point.  Coq/Agda
-- formalizations either: add LEM as an axiom; reformulate divergence
-- to be more constructive (e.g. as `(n : ℕ) → ITree` giving the n-th
-- chain element so case analysis can decide LEFT vs RIGHT eagerly); or
-- accept this lemma as a postulate.  We do the latter — it is precisely
-- the König step, well-isolated and well-named.  Constructive
-- alternatives discussed:
--   1. "Follow LEFT, fall back to RIGHT" — fails if chain is all-RIGHT.
--   2. "Decide on first step" — a single LEFT step doesn't ensure
--      infinitely many.
--   3. `{-# TERMINATING #-}` + LEFT-walking — accepted by Agda
--      syntactically but unsound (the function would loop on
--      RIGHT-dominated chains).
--   4. Coinductive Sum — Sum is inductive, so no natural lazy form.
postulate
  divergent-□-asymm-project-LR :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {tL tR : ITree E (ExtI I) R}
    → Divergent (tL □ tR) → Divergent tL ⊎ Divergent tR

-- Symmetric specialisation: `Divergent (P □ P) → Divergent P`.  Trivial
-- via the LR extraction (both branches give Divergent P).
divergent-□-symm-project :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R}
  → Divergent (P □ P) → Divergent P
divergent-□-symm-project d with divergent-□-asymm-project-LR d
... | inj₁ d-P = d-P
... | inj₂ d-P = d-P

-- Forward declaration of `asymm-divergence-project` so
-- `asymm-divergence-project-bTau` (defined first) can call it
-- mutually-recursively.
asymm-divergence-project :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P tL tR : ITree E (ExtI I) R}
    {s : List (Event√ E R)}
  → P ─[τ*]─► tL → P ─[τ*]─► tR
  → divergences (tL □ tR) s
  → divergences P s

-- bTau cases of `asymm-divergence-project`.  Mirrors `asymm-walk-□`'s
-- bTau-sSil (chain extension + recursion) and `asymm-walk-□-bTau-sNdbr`'s
-- four sub-cases (D = ret/ret, H = vis/ndbr, I = ndbr/vis, J = ndbr/ndbr)
-- of `□-force-ndbr-inv`, but driven by `divwit`.  Termination across
-- `asymm-divergence-project` mutual recursion needs `{-# TERMINATING #-}`
-- (Agda can't see the bigstep decreases through the τ*-chain rebases).
{-# TERMINATING #-}
asymm-divergence-project-bTau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P tL tR U : ITree E (ExtI I) R}
    {pre : List (Event√ E R)} {Q' : ITree E (ExtI I) R}
    {suf : List (Event√ E R)} {s : List (Event√ E R)}
  → P ─[τ*]─► tL → P ─[τ*]─► tR
  → s ≡ pre ++ suf
  → (tL □ tR) ─[ τ ]─► U
  → U ═⟨ pre ⟩═► Q'
  → Divergent Q'
  → divergences P s
-- sSil: force (tL □ tR) ≡ sil U.  By □-force-sil-inv: either force tL ≡
-- sil tL' (extend chL) or force tR ≡ sil tR' (extend chR).  Recurse on
-- the resulting smaller asymm form.
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp (sSil eqStep) rest dw
    with □-force-sil-inv {P = tL} {Q = tR} eqStep
... | inj₁ (tL' , eqL-sil , refl) =
        asymm-divergence-project
          (τ*-trans chL (τ*-step (sSil eqL-sil) τ*-zero))
          chR
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
... | inj₂ (tR' , eqR-sil , refl) =
        asymm-divergence-project
          chL
          (τ*-trans chR (τ*-step (sSil eqR-sil) τ*-zero))
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- sNdbr: force (tL □ tR) ≡ ndbr g, g i a ≡ just U.  Dispatch via
-- □-force-ndbr-inv into the four cases D/H/I/J.
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    with □-force-ndbr-inv {P = tL} {Q = tR} eqStep
-- ============ Case D: ret r / ret r' with r ≠ r' ============
... | inj₁ (r , r' , neq , eqL-ret , eqR-ret)
    with trans (sym eqStep) (force-□-ndbr-D {P = tL} {Q = tR} eqL-ret eqR-ret neq)
... | refl = dispatch-D i a f-eq rest dw
  where
    -- After unification, g ≡ br2 tL tR.  Case on (i, a) via br2.
    dispatch-D : ∀ (i' : AnyTypes (ExtI _)) (a' : proj₁ i') {U' : ITree _ _ _}
               → br2 tL tR i' a' ≡ just U'
               → U' ═⟨ pre ⟩═► Q' → Divergent Q'
               → divergences P _
    dispatch-D (_ , fin) (lift fzero) refl rest' dw' =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep chL rest'
               ; divwit  = dw' }
    dispatch-D (_ , fin) (lift (fsuc fzero)) refl rest' dw' =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep chR rest'
               ; divwit  = dw' }
    dispatch-D (_ , fin) (lift (fsuc (fsuc _))) () _ _
    dispatch-D (_ , base _) _ () _ _
    dispatch-D (_ , pair _ _) _ () _ _
-- ============ Case H: vis fL / ndbr fR' ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₁ (fL , fR' , wiR , waR , wpR , eqL-vis , eqR-ndbr))
    with trans (sym eqStep) (force-□-vis-ndbr-eq {P = tL} {Q = tR} eqL-vis eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- ============ Case I: ndbr fL' / vis fR ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , fR , eqL-ndbr , eqR-vis)))
    with trans (sym eqStep) (force-□-ndbr-vis-eq {P = tL} {Q = tR} eqL-ndbr eqR-vis)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- ============ Case J: ndbr fL' / ndbr fR' ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , fR' , wiR , waR , wpR ,
                               eqL-ndbr , eqR-ndbr))))
    with trans (sym eqStep) (force-□-ndbr-ndbr-eq {P = tL} {Q = tR} eqL-ndbr eqR-ndbr)
... | refl = dispatch-J i a f-eq rest dw
  where
    dispatch-J : ∀ (i' : AnyTypes (ExtI _)) (a' : proj₁ i') {U' : ITree _ _ _}
               → mergeNdbr fL' fR' i' a' ≡ just U'
               → U' ═⟨ pre ⟩═► Q' → Divergent Q'
               → divergences P _
    dispatch-J (_ , base _) _ () _ _
    dispatch-J (_ , fin)    _ () _ _
    dispatch-J (.(AL × AR) , pair {AL} {AR} iL' iR') (aL' , aR')
               f-eq-pair rest' dw'
        with fL' (AL , iL') aL' | inspect (fL' (AL , iL')) aL'
           | fR' (AR , iR') aR' | inspect (fR' (AR , iR')) aR'
           | f-eq-pair
    -- nn: mergeNdbr returns nothing.
    ... | nothing | _ | nothing | _ | ()
    -- jn: U' = tL'-branch.  Direct prepend via chL extended by sNdbr.
    ... | just tL'-br | [ fL'-eq ] | nothing | [ _ ] | refl =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep
                            (τ*-trans chL
                                      (τ*-step (sNdbr {p = tL} {f = fL'}
                                                      {wi = wiL} {wa = waL} {prf = wpL}
                                                      {i = (AL , iL')} {a = aL'} {t′ = tL'-br}
                                                      eqL-ndbr fL'-eq)
                                               τ*-zero))
                            rest'
               ; divwit  = dw' }
    -- nj: U' = tR'-branch.  Direct prepend via chR extended by sNdbr.
    ... | nothing | [ _ ] | just tR'-br | [ fR'-eq ] | refl =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep
                            (τ*-trans chR
                                      (τ*-step (sNdbr {p = tR} {f = fR'}
                                                      {wi = wiR} {wa = waR} {prf = wpR}
                                                      {i = (AR , iR')} {a = aR'} {t′ = tR'-br}
                                                      eqR-ndbr fR'-eq)
                                               τ*-zero))
                            rest'
               ; divwit  = dw' }
    -- jj: U' = tL'-br □ tR'-br.  Asymm-recurse with both chains extended.
    ... | just tL'-br | [ fL'-eq ] | just tR'-br | [ fR'-eq ] | refl =
        asymm-divergence-project
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = (AL , iL')} {a = aL'} {t′ = tL'-br}
                                    eqL-ndbr fL'-eq)
                             τ*-zero))
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = (AR , iR')} {a = aR'} {t′ = tR'-br}
                                    eqR-ndbr fR'-eq)
                             τ*-zero))
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest'
                  ; divwit  = dw' })
-- ============ Case K: ret r / ndbr fR' ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (r , fR' , wiR , waR , wpR , eqL-ret , eqR-ndbr)))))
    with trans (sym eqStep) (force-□-ret-ndbr-eq {P = tL} {Q = tR} eqL-ret eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- ============ Case L: ndbr fL' / ret r ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (fL' , wiL , waL , wpL , r , eqL-ndbr , eqR-ret))))))
    with trans (sym eqStep) (force-□-ndbr-ret-eq {P = tL} {Q = tR} eqL-ndbr eqR-ret)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- ============ Case M: mix _ _ / ndbr fR' ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (fmL , Lt , fR' , wiR , waR , wpR , eqL-mix , eqR-ndbr)))))))
    with trans (sym eqStep) (force-□-mix-ndbr-eq {P = tL} {Q = tR} eqL-mix eqR-ndbr)
... | refl
    with fR' i a | inspect (fR' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          chL
          (τ*-trans chR
                    (τ*-step (sNdbr {p = tR} {f = fR'}
                                    {wi = wiR} {wa = waR} {prf = wpR}
                                    {i = i} {a = a} {t′ = t'}
                                    eqR-ndbr jeq)
                             τ*-zero))
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- ============ Case N: ndbr fL' / mix _ _ ============
asymm-divergence-project-bTau {P = P} {tL = tL} {tR = tR}
                              {pre = pre} {Q' = Q'} {suf = suf}
                              chL chR sp
                              (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                     {i = i} {a = a} {t′ = U}
                                     eqStep f-eq) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (fL' , wiL , waL , wpL , fmR , Rt , eqL-ndbr , eqR-mix)))))))
    with trans (sym eqStep) (force-□-ndbr-mix-eq {P = tL} {Q = tR} eqL-ndbr eqR-mix)
... | refl
    with fL' i a | inspect (fL' i) a | f-eq
... | nothing | _ | ()
... | just t' | [ jeq ] | refl =
        asymm-divergence-project
          (τ*-trans chL
                    (τ*-step (sNdbr {p = tL} {f = fL'}
                                    {wi = wiL} {wa = waL} {prf = wpL}
                                    {i = i} {a = a} {t′ = t'}
                                    eqL-ndbr jeq)
                             τ*-zero))
          chR
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- sMixSlide: force (tL □ tR) ≡ mix f Qt; U ≡ Qt; project via postulate.
asymm-divergence-project-bTau chL chR sp
                              (sMixSlide {f = f} {Qt = Qt} sM-eq) rest dw =
    asymm-divergence-project-bTau-sMixSlide
      chL chR sp sM-eq rest dw

-- Body of `asymm-divergence-project` (forward-declared above).  Cases:
--   • bNil: divwit `Divergent (tL □ tR)`.  Project to `Divergent tL` or
--     `Divergent tR` via `divergent-□-asymm-project-LR`; use chL/chR
--     with `divergent-prefix` to lift to `Divergent P`.
--   • bStep sRet bNil: T = deadlock; `Divergent deadlock` impossible.
--   • bStep sVis ... rest: `□-force-vis-inv` extracts `force tL ≡ vis fL`
--     and `force tR ≡ vis fR`, with `f ≡ mergeVis fL fR`.  Case on
--     `fL at a` / `fR at a`: nn absurd; jn/nj direct prepend; jj uses
--     `⊓-divergences-elim` to pick a side.
--   • bTau ...: dispatched to `asymm-divergence-project-bTau`.
-- bNil: divwit Divergent (tL □ tR).  pre = []; trace = suf.
asymm-divergence-project {P = P} {tL = tL} {tR = tR} chL chR
    record { prefix = .[]; suffix = suf; split = sp
           ; witness = .(tL □ tR); reach = bNil; divwit = dw }
    with divergent-□-asymm-project-LR dw
... | inj₁ d-tL =
        record { prefix  = []
               ; suffix  = suf
               ; split   = sp
               ; witness = P
               ; reach   = bNil
               ; divwit  = divergent-prefix chL d-tL }
... | inj₂ d-tR =
        record { prefix  = []
               ; suffix  = suf
               ; split   = sp
               ; witness = P
               ; reach   = bNil
               ; divwit  = divergent-prefix chR d-tR }
-- bStep sRet bNil: T = deadlock; Divergent deadlock impossible.
asymm-divergence-project _ _
    record { reach = bStep (sRet _) bNil; divwit = dw } =
    ⊥-elim (deadlock-not-div dw)
  where
    deadlock-not-div : Divergent deadlock → ⊥
    deadlock-not-div ddw with ddw .Divergent.step
    ... | sSil ()
    ... | sNdbr () _
-- bStep sRet (bTau ...): impossible (deadlock has no τ).
asymm-divergence-project _ _
    record { reach = bStep (sRet _) (bTau step _) } =
    case step of λ where
      (sSil ())
      (sNdbr () _)
-- bStep sRet (bStep ...): impossible (deadlock has no event step).
asymm-divergence-project _ _
    record { reach = bStep (sRet _) (bStep step _) } =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep sVis ... rest: project visible step via □-force-vis-inv +
-- merge-vis case analysis.  Four sub-cases on `(fL at a, fR at a)`.
asymm-divergence-project {P = P} {tL = tL} {tR = tR} chL chR
    record { prefix = .(_ ∷ _); suffix = suf; split = sp
           ; witness = Q'
           ; reach = bStep (sVis {f = f} {at = at} {a = a} {t′ = t-merged}
                                  sV-eq f-eq) rest
           ; divwit = dw }
    with □-force-vis-inv {P = tL} {Q = tR} {f = f} sV-eq
... | fL , fR , eqL-vis , eqR-vis , merge-eq
    with fL at a | inspect (fL at) a | fR at a | inspect (fR at) a
-- nn: contradicts f-eq.
... | nothing | [ fL-noth ] | nothing | [ fR-noth ] =
        ⊥-elim (case (trans (sym (trans (cong (λ g → g at a) merge-eq)
                                         (cong₂ mergeMaybe fL-noth fR-noth)))
                            f-eq)
                     of λ ())
-- jn: t-merged ≡ tL'.  Build P → tL' via chL + bStep (sVis at tL).
... | just tL' | [ fL-eq ] | nothing | [ fR-noth ] =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ _
               ; suffix  = suf
               ; split   = trans sp refl
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep chL
                            (bStep {t = tL} {t′ = tL'}
                                   (sVis {p = tL} {f = fL}
                                         {at = at} {a = a} {t′ = tL'}
                                         eqL-vis fL-eq)
                                   rest-tL')
               ; divwit  = dw }
  where
    f-just-tL' : f at a ≡ just tL'
    f-just-tL' = trans (cong (λ g → g at a) merge-eq)
                       (cong₂ mergeMaybe fL-eq fR-noth)
    tL'≡t-merged : tL' ≡ t-merged
    tL'≡t-merged = just-injective (trans (sym f-just-tL') f-eq)
    rest-tL' : tL' ═⟨ _ ⟩═► Q'
    rest-tL' = subst (λ x → x ═⟨ _ ⟩═► Q') (sym tL'≡t-merged) rest
-- nj: symmetric.
... | nothing | [ fL-noth ] | just tR' | [ fR-eq ] =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ _
               ; suffix  = suf
               ; split   = trans sp refl
               ; witness = Q'
               ; reach   = τ*-prepend-bigstep chR
                            (bStep {t = tR} {t′ = tR'}
                                   (sVis {p = tR} {f = fR}
                                         {at = at} {a = a} {t′ = tR'}
                                         eqR-vis fR-eq)
                                   rest-tR')
               ; divwit  = dw }
  where
    f-just-tR' : f at a ≡ just tR'
    f-just-tR' = trans (cong (λ g → g at a) merge-eq)
                       (cong₂ mergeMaybe fL-noth fR-eq)
    tR'≡t-merged : tR' ≡ t-merged
    tR'≡t-merged = just-injective (trans (sym f-just-tR') f-eq)
    rest-tR' : tR' ═⟨ _ ⟩═► Q'
    rest-tR' = subst (λ x → x ═⟨ _ ⟩═► Q') (sym tR'≡t-merged) rest
-- jj: t-merged ≡ tL' ⊓ tR'.  ⊓-divergences-elim to pick a side.
... | just tL' | [ fL-eq ] | just tR' | [ fR-eq ]
    with ⊓-divergences-elim {P = tL'} {Q = tR'}
            (record { prefix  = _
                    ; suffix  = suf
                    ; split   = refl
                    ; witness = Q'
                    ; reach   = rest-merge
                    ; divwit  = dw })
  where
    f-just-merge : f at a ≡ just (tL' ⊓ tR')
    f-just-merge = trans (cong (λ g → g at a) merge-eq)
                         (cong₂ mergeMaybe fL-eq fR-eq)
    tL'⊓tR'≡t-merged : (tL' ⊓ tR') ≡ t-merged
    tL'⊓tR'≡t-merged = just-injective (trans (sym f-just-merge) f-eq)
    rest-merge : (tL' ⊓ tR') ═⟨ _ ⟩═► Q'
    rest-merge = subst (λ x → x ═⟨ _ ⟩═► Q') (sym tL'⊓tR'≡t-merged) rest
... | inj₁ d-tL' = combine-L d-tL'
  where
    combine-L : divergences tL' _ → divergences P _
    combine-L record { prefix = pre-L; suffix = suf-L; split = sp-L
                     ; witness = w-L; reach = reach-L; divwit = dw-L } =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre-L
               ; suffix  = suf-L
               ; split   = trans sp (cong (evl (evLabel (proj₁ at) (proj₂ at) a) ∷_)
                                          sp-L)
               ; witness = w-L
               ; reach   = τ*-prepend-bigstep chL
                            (bStep {t = tL} {t′ = tL'}
                                   (sVis {p = tL} {f = fL}
                                         {at = at} {a = a} {t′ = tL'}
                                         eqL-vis fL-eq)
                                   reach-L)
               ; divwit  = dw-L }
... | inj₂ d-tR' = combine-R d-tR'
  where
    combine-R : divergences tR' _ → divergences P _
    combine-R record { prefix = pre-R; suffix = suf-R; split = sp-R
                     ; witness = w-R; reach = reach-R; divwit = dw-R } =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre-R
               ; suffix  = suf-R
               ; split   = trans sp (cong (evl (evLabel (proj₁ at) (proj₂ at) a) ∷_)
                                          sp-R)
               ; witness = w-R
               ; reach   = τ*-prepend-bigstep chR
                            (bStep {t = tR} {t′ = tR'}
                                   (sVis {p = tR} {f = fR}
                                         {at = at} {a = a} {t′ = tR'}
                                         eqR-vis fR-eq)
                                   reach-R)
               ; divwit  = dw-R }
-- bStep sMixVis bNil: tL □ tR is mix-shaped; project residual via postulate.
asymm-divergence-project chL chR
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq) bNil
           ; divwit = dw } =
    asymm-divergence-project-sMixVis-bNil
      {at = at} {a = a} chL chR sp refl sM-eq f-eq dw
-- bStep sMixVis (bTau ...): dispatch to postulate.
asymm-divergence-project chL chR
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq)
                          (bTau step rest)
           ; divwit = dw } =
    asymm-divergence-project-sMixVis-bTau
      {at = at} {a = a} chL chR sp sM-eq f-eq step rest dw
-- bStep sMixVis (bStep ...): dispatch to postulate.
asymm-divergence-project chL chR
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq)
                          (bStep step rest)
           ; divwit = dw } =
    asymm-divergence-project-sMixVis-bStep
      {at = at} {a = a} chL chR sp sM-eq f-eq step rest dw
-- bTau ...: dispatched to focused postulate.
asymm-divergence-project chL chR
    record { prefix = pre; suffix = suf; split = sp
           ; witness = Q'; reach = bTau step rest; divwit = dw } =
    asymm-divergence-project-bTau chL chR sp step rest dw

-- bTau-step projection for divergences.  Dispatches via
-- `□-force-sil-inv` / `□-force-ndbr-inv` to extract the structure of the
-- τ-step out of `(P □ P)`:
--   • sSil: force P = sil P'; U = P' □ P.  Build divergence at (P' □ P)
--     and apply `asymm-divergence-project` with chL = sSil-step, chR = ε.
--   • sNdbr (case J only — others rule out by same-P force shape):
--     force P = ndbr fP; U = mergeNdbr fP fP at branch.  Pair-branch
--     sub-cases:
--       - jn (left-just, right-nothing): U = tL; build P → tL via sNdbr
--         and prepend rest directly.  No asymm needed.
--       - nj (right-just, left-nothing): symmetric.
--       - jj (both-just): U = tL □ tR.  Apply `asymm-divergence-project`
--         with chL/chR extending by sNdbr.
--       - nn / non-pair: mergeNdbr returns nothing, contradicting f-eq.
divergences-project-PP-bTau :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P U : ITree E (ExtI I) R}
    {pre : List (Event√ E R)} {Q' : ITree E (ExtI I) R}
    {suf : List (Event√ E R)} {s : List (Event√ E R)}
  → s ≡ pre ++ suf
  → (P □ P) ─[ τ ]─► U
  → U ═⟨ pre ⟩═► Q'
  → Divergent Q'
  → divergences P s
-- sSil case: force P = sil P'.  Build (P' □ P) divergence + asymm project.
divergences-project-PP-bTau {P = P} {pre = pre} {Q' = Q'} {suf = suf}
                            sp (sSil eqStep) rest dw
    with □-force-sil-inv {P = P} {Q = P} eqStep
... | inj₁ (P' , eqP-sil , refl) =
        asymm-divergence-project
          (τ*-step (sSil eqP-sil) τ*-zero)
          τ*-zero
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
... | inj₂ (P' , eqP-sil , refl) =
        asymm-divergence-project
          τ*-zero
          (τ*-step (sSil eqP-sil) τ*-zero)
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest
                  ; divwit  = dw })
-- sNdbr case: force P = ndbr fP (only case J of □-force-ndbr-inv fires
-- for symm P=P).  Dispatch on the pair-branch sub-case.
divergences-project-PP-bTau {P = P} {pre = pre} {Q' = Q'} {suf = suf}
                            sp (sNdbr {f = g} {wi = wi} {wa = wa} {prf = wp}
                                       {i = i} {a = a} {t′ = U}
                                       eqStep f-eq) rest dw
    with □-force-ndbr-inv {P = P} {Q = P} eqStep
-- Case D (ret/ret with r ≠ r'): same-P forces r = r', contradicting neq.
... | inj₁ (r , r' , neq , eqP-ret , eqP-ret') =
        ⊥-elim (case trans (sym eqP-ret) eqP-ret' of λ where refl → neq refl)
-- Case H (vis / ndbr): same-P forces both shapes equal → contradiction.
... | inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-vis , eqP-ndbr)) =
        case trans (sym eqP-vis) eqP-ndbr of λ ()
-- Case I (ndbr / vis): symmetric contradiction.
... | inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ndbr , eqP-vis))) =
        case trans (sym eqP-ndbr) eqP-vis of λ ()
-- Case J (ndbr / ndbr): force P = ndbr fP wiP waP wpP.  After
-- unification, g ≡ mergeNdbr fP fP.  Dispatch on i (must be `pair`) and
-- on the four fP/fP combinations.
... | inj₂ (inj₂ (inj₂ (inj₁ (fP , wiP , waP , wpP , fQ , wiQ , waQ , wpQ ,
                                eqP-ndbr , _))))
    with trans (sym eqStep)
               (force-□-ndbr-ndbr-eq {P = P} {Q = P} eqP-ndbr eqP-ndbr)
... | refl = dispatch-J i a f-eq rest dw
  where
    dispatch-J :
      ∀ (i' : AnyTypes (ExtI _)) (a' : proj₁ i') {U : ITree _ _ _}
      → mergeNdbr fP fP i' a' ≡ just U
      → U ═⟨ pre ⟩═► Q' → Divergent Q'
      → divergences P _  -- inferred from outer s
    -- Non-pair branches (base / fin): mergeNdbr returns nothing.
    dispatch-J (_ , base _) _ () _ _
    dispatch-J (_ , fin)    _ () _ _
    -- Pair branch: case on the four fP/fP combinations.
    dispatch-J (.(AL × AR) , pair {AL} {AR} iL' iR') (aL' , aR')
               f-eq-pair rest' dw'
        with fP (AL , iL') aL' | inspect (fP (AL , iL')) aL'
           | fP (AR , iR') aR' | inspect (fP (AR , iR')) aR'
           | f-eq-pair
    -- nn: mergeNdbr returns nothing.
    ... | nothing | _ | nothing | _ | ()
    -- jn: U = tL.  Direct: prepend P → tL via sNdbr.
    ... | just tL | [ fP-eqL ] | nothing | [ _ ] | refl =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = bTau {t = P} {t′ = tL}
                                (sNdbr {p = P} {f = fP}
                                       {wi = wiP} {wa = waP} {prf = wpP}
                                       {i = (AL , iL')} {a = aL'} {t′ = tL}
                                       eqP-ndbr fP-eqL)
                                rest'
               ; divwit  = dw' }
    -- nj: U = tR.  Symmetric.
    ... | nothing | [ _ ] | just tR | [ fP-eqR ] | refl =
        record { prefix  = pre
               ; suffix  = suf
               ; split   = sp
               ; witness = Q'
               ; reach   = bTau {t = P} {t′ = tR}
                                (sNdbr {p = P} {f = fP}
                                       {wi = wiP} {wa = waP} {prf = wpP}
                                       {i = (AR , iR')} {a = aR'} {t′ = tR}
                                       eqP-ndbr fP-eqR)
                                rest'
               ; divwit  = dw' }
    -- jj: U = tL □ tR.  Asymm project with both chains extended by sNdbr.
    ... | just tL | [ fP-eqL ] | just tR | [ fP-eqR ] | refl =
        asymm-divergence-project
          (τ*-step (sNdbr {p = P} {f = fP}
                          {wi = wiP} {wa = waP} {prf = wpP}
                          {i = (AL , iL')} {a = aL'} {t′ = tL}
                          eqP-ndbr fP-eqL)
                   τ*-zero)
          (τ*-step (sNdbr {p = P} {f = fP}
                          {wi = wiP} {wa = waP} {prf = wpP}
                          {i = (AR , iR')} {a = aR'} {t′ = tR}
                          eqP-ndbr fP-eqR)
                   τ*-zero)
          (record { prefix  = pre
                  ; suffix  = suf
                  ; split   = sp
                  ; witness = Q'
                  ; reach   = rest'
                  ; divwit  = dw' })
-- Case K (ret / ndbr): same-P forces both shapes equal → contradiction.
divergences-project-PP-bTau {P = P}
    sp (sNdbr eqStep _) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ret , eqP-ndbr))))) =
        case trans (sym eqP-ret) eqP-ndbr of λ ()
-- Case L (ndbr / ret): symmetric contradiction.
divergences-project-PP-bTau {P = P}
    sp (sNdbr eqStep _) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , eqP-ndbr , eqP-ret)))))) =
        case trans (sym eqP-ndbr) eqP-ret of λ ()
-- Case M (mix / ndbr): same-P forces both shapes equal → contradiction.
divergences-project-PP-bTau {P = P}
    sp (sNdbr eqStep _) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (_ , _ , _ , _ , _ , _ , eqP-mix , eqP-ndbr))))))) =
        case trans (sym eqP-mix) eqP-ndbr of λ ()
-- Case N (ndbr / mix): symmetric contradiction.
divergences-project-PP-bTau {P = P}
    sp (sNdbr eqStep _) rest dw
    | inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (_ , _ , _ , _ , _ , _ , eqP-ndbr , eqP-mix))))))) =
        case trans (sym eqP-ndbr) eqP-mix of λ ()
-- sMixSlide: force (P □ P) ≡ mix f Qt; dispatch to postulate.
divergences-project-PP-bTau sp (sMixSlide sM-eq) rest dw =
    divergences-project-PP-bTau-sMixSlide sp sM-eq rest dw

-- Forward (project) for divergences:  divergences (P □ P) s → divergences P s.
-- Cases handled here:
--   • bNil: witness `Q' = P □ P`.  Project divwit via `divergent-□-symm-project`.
--   • bStep sRet bNil: T = deadlock.  `Divergent deadlock` impossible.
--   • bStep sVis ... rest: project visible step to P via `□-force-vis-inv`
--     (which forces `force P ≡ vis fP`).  After `vis-injective`, the
--     merged-vis continuation collapses to `(p ⊓ p)` for `fP at a = just p`
--     (or contradicts for `nothing`).  Apply `⊓-divergences-elim` to
--     project the residual `(p ⊓ p)`-divergence to a `p`-divergence,
--     then prepend the P-side `bStep (sVis ...)`.
--   • bTau ...: dispatched to `divergences-project-PP-bTau` postulate.
divergences-project-PP :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences (P □ P) s → divergences P s
-- bNil: witness = (P □ P), pre = [].  Project divwit via postulate.
divergences-project-PP {P = P}
    record { prefix = .[]; suffix = suf; split = sp
           ; witness = .(P □ P); reach = bNil; divwit = dw } =
    record { prefix  = []
           ; suffix  = suf
           ; split   = sp
           ; witness = P
           ; reach   = bNil
           ; divwit  = divergent-□-symm-project dw }
-- bStep sRet bNil: T = deadlock; Divergent deadlock impossible.
divergences-project-PP {P = P}
    record { reach = bStep (sRet _) bNil; divwit = dw } =
    ⊥-elim (deadlock-not-div dw)
  where
    deadlock-not-div : Divergent deadlock → ⊥
    deadlock-not-div ddw with ddw .Divergent.step
    ... | sSil ()
    ... | sNdbr () _
-- bStep sRet (bTau ...): impossible (deadlock has no τ-step).
divergences-project-PP
    record { reach = bStep (sRet _) (bTau step _) } =
    case step of λ where
      (sSil ())
      (sNdbr () _)
-- bStep sRet (bStep ...): impossible (deadlock has no event-step).
divergences-project-PP
    record { reach = bStep (sRet _) (bStep step _) } =
    case step of λ where
      (sRet ())
      (sVis refl ())
-- bStep sVis ... rest: project visible step via □-force-vis-inv +
-- vis-injective + ⊓-divergences-elim.
divergences-project-PP {P = P}
    record { prefix = .(_ ∷ _); suffix = suf; split = sp
           ; witness = Q'
           ; reach = bStep (sVis {f = f} {at = at} {a = a} {t′ = t-merged}
                                  sV-eq f-eq) rest
           ; divwit = dw }
    with □-force-vis-inv {P = P} {Q = P} {f = f} sV-eq
... | fP , fQ , eqP , eqQ , merge-eq
    with vis-injective (trans (sym eqP) eqQ)
... | refl  -- fQ unified with fP
    with fP at a | inspect (fP at) a
... | nothing | [ fP-noth ] =
        ⊥-elim (case (trans (sym (trans (cong (λ g → g at a) merge-eq)
                                         (cong₂ mergeMaybe fP-noth fP-noth)))
                            f-eq)
                     of λ ())
... | just p | [ fP-eq ]
    with ⊓-divergences-elim {P = p} {Q = p}
            (record { prefix  = _
                    ; suffix  = suf
                    ; split   = refl
                    ; witness = Q'
                    ; reach   = rest-p⊓p
                    ; divwit  = dw })
  where
    f-just-pp : f at a ≡ just (p ⊓ p)
    f-just-pp = trans (cong (λ g → g at a) merge-eq)
                      (cong₂ mergeMaybe fP-eq fP-eq)
    p⊓p≡t-merged : p ⊓ p ≡ t-merged
    p⊓p≡t-merged = just-injective (trans (sym f-just-pp) f-eq)
    rest-p⊓p : (p ⊓ p) ═⟨ _ ⟩═► Q'
    rest-p⊓p = subst (λ x → x ═⟨ _ ⟩═► Q') (sym p⊓p≡t-merged) rest
... | inj₁ d-p = combine d-p
  where
    -- Prepend P's sVis (force P ≡ vis fP, fP at a ≡ just p) to d-p's reach.
    combine : divergences p _ → divergences P _
    combine record { prefix = pre-p; suffix = suf-p; split = sp-p
                   ; witness = w-p; reach = reach-p; divwit = dw-p } =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre-p
               ; suffix  = suf-p
               ; split   = trans sp (cong (evl (evLabel (proj₁ at) (proj₂ at) a) ∷_)
                                          sp-p)
               ; witness = w-p
               ; reach   = bStep {t = P} {t′ = p}
                                 (sVis {p = P} {f = fP} {at = at} {a = a} {t′ = p}
                                       eqP fP-eq)
                                 reach-p
               ; divwit  = dw-p }
... | inj₂ d-p = combine d-p
  where
    -- Symmetric (same as inj₁ since both branches give p).
    combine : divergences p _ → divergences P _
    combine record { prefix = pre-p; suffix = suf-p; split = sp-p
                   ; witness = w-p; reach = reach-p; divwit = dw-p } =
        record { prefix  = evl (evLabel (proj₁ at) (proj₂ at) a) ∷ pre-p
               ; suffix  = suf-p
               ; split   = trans sp (cong (evl (evLabel (proj₁ at) (proj₂ at) a) ∷_)
                                          sp-p)
               ; witness = w-p
               ; reach   = bStep {t = P} {t′ = p}
                                 (sVis {p = P} {f = fP} {at = at} {a = a} {t′ = p}
                                       eqP fP-eq)
                                 reach-p
               ; divwit  = dw-p }
-- bStep sMixVis bNil: P □ P is mix-shaped; project residual via postulate.
divergences-project-PP
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq) bNil
           ; divwit = dw } =
    divergences-project-PP-sMixVis-bNil
      {at = at} {a = a} sp refl sM-eq f-eq dw
divergences-project-PP
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq)
                          (bTau step rest)
           ; divwit = dw } =
    divergences-project-PP-sMixVis-bTau
      {at = at} {a = a} sp sM-eq f-eq step rest dw
divergences-project-PP
    record { suffix = suf
           ; split = sp
           ; witness = Q'
           ; reach = bStep (sMixVis {f = f} {Qt = Qt}
                                     {at = at} {a = a} {t′ = t'}
                                     sM-eq f-eq)
                          (bStep step rest)
           ; divwit = dw } =
    divergences-project-PP-sMixVis-bStep
      {at = at} {a = a} sp sM-eq f-eq step rest dw
-- bTau: dispatched to focused postulate.
divergences-project-PP
    record { prefix = pre; suffix = suf; split = sp
           ; witness = Q'; reach = bTau step rest; divwit = dw } =
    divergences-project-PP-bTau sp step rest dw

-- Lift to failures⊥ (= failures ⊎ divergences) by case analysis on the
-- inj₁/inj₂ tag.  The four directions chain through the corresponding
-- failures or divergences sub-lemma.
failures⊥-lift-PP :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ P s B → failures⊥ (P □ P) s B
failures⊥-lift-PP (inj₁ f) = inj₁ (failures-lift-PP f)
failures⊥-lift-PP (inj₂ d) = inj₂ (divergences-lift-PP d)

failures⊥-project-PP :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ (P □ P) s B → failures⊥ P s B
failures⊥-project-PP (inj₁ f) = inj₁ (failures-project-PP f)
failures⊥-project-PP (inj₂ d) = inj₂ (divergences-project-PP d)

-- Idempotence of external choice in the FD model — assembled from
-- the four pointwise inclusions above.
□-idem-FD :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → _≃FD_ {ℓB = ℓB} (P □ P) P
□-idem-FD P = (PP⊑P-F⊥ , PP⊑P-D) , (P⊑PP-F⊥ , P⊑PP-D)
  where
    -- (P □ P) ⊑F⊥ P  means  failures⊥ P → failures⊥ (P □ P).
    PP⊑P-F⊥ : (P □ P) ⊑F⊥ P
    PP⊑P-F⊥ = failures⊥-lift-PP

    -- (P □ P) ⊑D P  means  divergences P → divergences (P □ P).
    PP⊑P-D : (P □ P) ⊑D P
    PP⊑P-D = divergences-lift-PP

    -- P ⊑F⊥ (P □ P)  means  failures⊥ (P □ P) → failures⊥ P.
    P⊑PP-F⊥ : P ⊑F⊥ (P □ P)
    P⊑PP-F⊥ = failures⊥-project-PP

    -- P ⊑D (P □ P)  means  divergences (P □ P) → divergences P.
    P⊑PP-D : P ⊑D (P □ P)
    P⊑PP-D = divergences-project-PP

------------------------------------------------------------------------
-- §X. Canonical lesson: external choice refines internal choice in FD.
--
--   ⊓⊑D□  : (P ⊓ Q) ⊑D  (P □ Q)
--   ⊓⊑F⊥□ : (P ⊓ Q) ⊑F⊥ (P □ Q)
--   ⊓⊑FD□ : (P ⊓ Q) ⊑FD (P □ Q)
--
-- Equivalent reading: every failure / divergence of P □ Q lifts to a
-- failure / divergence of P ⊓ Q.  Generalised from
-- `VendingMachine.lagda.md`'s `□-to-⊓-failure`.
--
-- Proof strategy: P ⊓ Q ─[τ]─► P  (via ⊓-step-L) and
--                 P ⊓ Q ─[τ]─► Q  (via ⊓-step-R), so
-- `asymm-walk-□` / `asymm-divergence-project` with these τ*-chains
-- directly transport failures / divergences of (P □ Q) to (P ⊓ Q).
------------------------------------------------------------------------

⊓⊑D□ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         ⦃ _ : DecEq R ⦄
         {P Q : ITree E (ExtI I) R}
       → (P ⊓ Q) ⊑D (P □ Q)
⊓⊑D□ {P = P} {Q = Q} d =
  asymm-divergence-project
    (τ*-step (⊓-step-L P Q) τ*-zero)
    (τ*-step (⊓-step-R P Q) τ*-zero)
    d

⊓⊑F⊥□ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          ⦃ _ : DecEq R ⦄
          {P Q : ITree E (ExtI I) R}
        → _⊑F⊥_ {ℓB = ℓB} (P ⊓ Q) (P □ Q)
⊓⊑F⊥□ {P = P} {Q = Q} (inj₁ f) =
  inj₁ (asymm-walk-□
          (τ*-step (⊓-step-L P Q) τ*-zero)
          (τ*-step (⊓-step-R P Q) τ*-zero)
          f)
⊓⊑F⊥□ {P = P} {Q = Q} (inj₂ d) =
  inj₂ (asymm-divergence-project
          (τ*-step (⊓-step-L P Q) τ*-zero)
          (τ*-step (⊓-step-R P Q) τ*-zero)
          d)

⊓⊑FD□ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          ⦃ _ : DecEq R ⦄
          {P Q : ITree E (ExtI I) R}
        → _⊑FD_ {ℓB = ℓB} (P ⊓ Q) (P □ Q)
⊓⊑FD□ = ⊓⊑F⊥□ , ⊓⊑D□

------------------------------------------------------------------------
-- §Y. Monotonicity of external choice in the FD model.
--
--   □-mono-⊑F⊥ : P ⊑F⊥ P′ → Q ⊑F⊥ Q′ → (P □ Q) ⊑F⊥ (P′ □ Q′)
--   □-mono-⊑D  : P ⊑D  P′ → Q ⊑D  Q′ → (P □ Q) ⊑D  (P′ □ Q′)
--   □-mono-⊑FD : P ⊑FD P′ → Q ⊑FD Q′ → (P □ Q) ⊑FD (P′ □ Q′)
--
-- Both □-mono-⊑F⊥ and □-mono-⊑D are postulated pending construction
-- of the asymmetric injection direction
--
--   failures-inject-□L : failures P s B → failures (P □ Q) s B
--   failures-inject-□R : failures Q s B → failures (P □ Q) s B
--
-- (and the corresponding divergence variants).  These injection lemmas
-- require a full failures-characterisation for `_□_` (the ↔ lemma
-- sketched in the §Session-3 comment above, ~150–300 lines), which has
-- not yet been built.  Once those lemmas exist the postulates below can
-- be discharged as follows:
--
--   □-mono-⊑F⊥ P⊑P′ Q⊑Q′ f
--       with asymm-walk-□ τ*-zero τ*-zero (inj-failure f)
--   ...  — walk failure of (P′ □ Q′) to a failure of P′ or Q′,
--          apply P⊑P′ or Q⊑Q′, re-inject via failures-inject-□L/R.
--
--   □-mono-⊑D is analogous using asymm-divergence-project.
------------------------------------------------------------------------

-- TODO: □-mono-⊑F⊥ requires the inverse of asymm-walk-□ (the
-- injection direction failures P s B → failures (P □ Q) s B), which
-- is not yet in the library.  Postulated pending construction of the
-- full □-failures characterisation (see Session-3 §1 above).
postulate
  □-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 ⦃ _ : DecEq R ⦄
                 {P P′ Q Q′ : ITree E (ExtI I) R}
               → _⊑F⊥_ {ℓB = ℓB} P P′ → _⊑F⊥_ {ℓB = ℓB} Q Q′
               → _⊑F⊥_ {ℓB = ℓB} (P □ Q) (P′ □ Q′)

-- TODO: □-mono-⊑D requires the divergence injection direction
-- divergences P s → divergences (P □ Q) s, similarly pending the
-- full □-divergences characterisation.
postulate
  □-mono-⊑D : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                ⦃ _ : DecEq R ⦄
                {P P′ Q Q′ : ITree E (ExtI I) R}
              → P ⊑D P′ → Q ⊑D Q′
              → (P □ Q) ⊑D (P′ □ Q′)

□-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               ⦃ _ : DecEq R ⦄
               {P P′ Q Q′ : ITree E (ExtI I) R}
             → _⊑FD_ {ℓB = ℓB} P P′ → _⊑FD_ {ℓB = ℓB} Q Q′
             → _⊑FD_ {ℓB = ℓB} (P □ Q) (P′ □ Q′)
□-mono-⊑FD (pF , pD) (qF , qD) = □-mono-⊑F⊥ pF qF , □-mono-⊑D pD qD
