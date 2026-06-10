{-# OPTIONS --guardedness #-}

open import Level using (_⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; Is-just; nothing)
open import Data.Maybe.Relation.Unary.Any using () renaming (just to any-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base renaming (⊤ to ⊤₀; tt to tt₀)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable.Core using (_⊎-dec_)

open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS

module CSP.Definitions.AlphaParallel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open ITree

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-- An alphabet is a decidable predicate on visible events.
Alpha : Set (lsuc ℓ ⊔ ℓe)
Alpha = AnyTypes E → Set

Dec-Alpha : Alpha → Set (lsuc ℓ ⊔ ℓe)
Dec-Alpha A = (at : AnyTypes E) → Dec (A at)

-------------------------------------------------------------------------------------
-- Binary alphabetised parallel composition

infixr 5 _⟦_¿_∥_¿_⟧_

-- Unlike the interface parallel in Parallel.agda, there is no Fin 2 "who moves"
-- interleave branch here: alphabet membership routes every event determinately
-- (synchronise / P-solo / Q-solo / refuse), so no nondeterministic choice arises.
_⟦_¿_∥_¿_⟧_ :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
  → ITree E (ExtI I) R
  → (A : Alpha) → (da : Dec-Alpha A)
  → (B : Alpha) → (db : Dec-Alpha B)
  → ITree E (ExtI I) S
  → ITree E (ExtI I) (R × S)

force (_⟦_¿_∥_¿_⟧_ {ℓi = ℓi} {ℓr = ℓr} {ℓs = ℓs} {I = I} {R = R} {S = S} P A da B db Q)
  with P .force | Q .force
... | sil P' | _ = sil (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
... | _ | sil Q' = sil (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
... | ret r | ret s = ret (r , s)
... | ret r | vis fQ = vis (λ at x →
      case (da at , db at) of λ where
        (no _ , yes _) → case fQ at x of λ where
                            nothing   → nothing
                            (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
        _              → nothing)
... | vis fP | ret s = vis (λ at x →
      case (da at , db at) of λ where
        (yes _ , no _) → case fP at x of λ where
                            nothing   → nothing
                            (just P') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        _              → nothing)
... | vis fP | vis fQ = vis (λ at x →
      case (da at , db at) of λ where
        (yes _ , yes _) → -- both alphabets claim e: must synchronise
                          case (fP at x , fQ at x) of λ where
                            (just P' , just Q') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
                            _                   → nothing
        (yes _ , no _)  → -- only A claims e: P steps alone
                          case fP at x of λ where
                            (just P') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
                            nothing   → nothing
        (no _ , yes _)  → -- only B claims e: Q steps alone
                          case fQ at x of λ where
                            (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
                            nothing   → nothing
        (no _ , no _)   → nothing)   -- e in neither alphabet: refused

... | ret r | ndbr fQ wi wa wp = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fQ i a of λ where
        nothing   → nothing
        (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
    go : Is-just (fQ wi wa) → Is-just (f' wi wa)
    go p with fQ wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()

... | vis fP | ndbr fQ wi wa wp = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fQ i a of λ where
        nothing   → nothing
        (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
    go : Is-just (fQ wi wa) → Is-just (f' wi wa)
    go p with fQ wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()

... | ndbr fP wi wa wp | ret s = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fP i a of λ where
        nothing   → nothing
        (just P') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
    go : Is-just (fP wi wa) → Is-just (f' wi wa)
    go p with fP wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()

... | ndbr fP wi wa wp | vis fQ = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fP i a of λ where
        nothing   → nothing
        (just P') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
    go : Is-just (fP wi wa) → Is-just (f' wi wa)
    go p with fP wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()

... | ndbr fP (AP , iP) waP wpP | ndbr fQ (AQ , iQ) waQ wpQ = ndbr mergeNdbr'
         ((AP × AQ) , pair iP iQ) (waP , waQ) (go wpP wpQ)
  where
    mergeNdbr' : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))
    mergeNdbr' (.(AP × AQ) , pair {AP} {AQ} iP iQ) (aP , aQ) =
      case fP (AP , iP) aP , fQ (AQ , iQ) aQ of λ where
        (just P' , just Q') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
        (just P' , nothing) → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        (nothing , just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
        (nothing , nothing) → nothing
    mergeNdbr' (A , base i) a = nothing
    mergeNdbr' (_ , fin) a = nothing

    go : Is-just (fP (AP , iP) waP)
       → Is-just (fQ (AQ , iQ) waQ)
       → Is-just (mergeNdbr' ((AP × AQ) , pair iP iQ) (waP , waQ))
    go pP pQ with fP (AP , iP) waP | pP | fQ (AQ , iQ) waQ | pQ
    ... | just P' | _ | just Q' | _ = any-just tt₀
    ... | just P' | _ | nothing | ()
    ... | nothing | () | _      | _

-- ----- mix cases (sliding-as-mix) ---------------------------------------------------

... | mix fP P' | ret s = mix (λ at x →
      case (da at , db at) of λ where
        (yes _ , no _) → case fP at x of λ where
                            nothing    → nothing
                            (just P'') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
        _              → nothing)
      (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
... | ret r | mix fQ Q' = mix (λ at x →
      case (da at , db at) of λ where
        (no _ , yes _) → case fQ at x of λ where
                            nothing    → nothing
                            (just Q'') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q'')
        _              → nothing)
      (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
... | mix fP P' | vis fQ = mix (λ at x →
      case (da at , db at) of λ where
        (yes _ , yes _) → case (fP at x , fQ at x) of λ where
                            (just P'' , just Q') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
                            _                    → nothing
        (yes _ , no _)  → case fP at x of λ where
                            (just P'') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
                            nothing    → nothing
        (no _ , yes _)  → case fQ at x of λ where
                            (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
                            nothing   → nothing
        (no _ , no _)   → nothing)
      (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
... | vis fP | mix fQ Q' = mix (λ at x →
      case (da at , db at) of λ where
        (yes _ , yes _) → case (fP at x , fQ at x) of λ where
                            (just P' , just Q'') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q'')
                            _                    → nothing
        (yes _ , no _)  → case fP at x of λ where
                            (just P') → just (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
                            nothing   → nothing
        (no _ , yes _)  → case fQ at x of λ where
                            (just Q'') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q'')
                            nothing    → nothing
        (no _ , no _)   → nothing)
      (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
... | mix fP P' | mix fQ Q' = mix (λ at x →
      case (da at , db at) of λ where
        (yes _ , yes _) → case (fP at x , fQ at x) of λ where
                            (just P'' , just Q'') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q'')
                            _                     → nothing
        (yes _ , no _)  → case fP at x of λ where
                            (just P'') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
                            nothing    → nothing
        (no _ , yes _)  → case fQ at x of λ where
                            (just Q'') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q'')
                            nothing    → nothing
        (no _ , no _)   → nothing)
      (P' ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
... | mix fP P' | ndbr fQ wi wa wp = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fQ i a of λ where
        nothing   → nothing
        (just Q') → just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q')
    go : Is-just (fQ wi wa) → Is-just (f' wi wa)
    go p with fQ wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()
... | ndbr fP wi wa wp | mix fQ Q' = ndbr (λ ai a → f' ai a) wi wa (go wp)
  where
    f' : (i : AnyTypes (ExtI I)) → (a : proj₁ i) → Maybe (ITree E (ExtI I) (R × S))
    f' i a = case fP i a of λ where
        nothing    → nothing
        (just P'') → just (P'' ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
    go : Is-just (fP wi wa) → Is-just (f' wi wa)
    go p with fP wi wa | p
    ... | just x  | _ = any-just tt₀
    ... | nothing | ()

-------------------------------------------------------------------------------------
-- LTS step lemmas (vis-shaped operands)

-- Scaffolding helpers used only within this module.
private
  -- Force-reduction lemma (à la the `Sanity.composite-is-vis`): when both operands
  -- are vis-shaped the composite's force is a `vis` node.  We return the offer
  -- function existentially (Agda infers it from the reduced force).
  αpar-force-vis-vis :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → Σ-syntax ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S))))
        (λ f → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f)
  αpar-force-vis-vis eqP eqQ rewrite eqP | eqQ = _ , refl

  -- Offer lemma: given the force equality (and hence the merged offer function `f`)
  -- the offer at the event is `just (P′ ⟦…⟧ Q′)`.  `rewrite`-ing both operand force
  -- equalities reduces `(P ⟦…⟧ Q) .force` in the *hypothesis* `feq` to `vis <merged>`,
  -- so matching `feq` as `refl` unifies `f` with the operator's own merged offer,
  -- after which we split the merged `case_of_`.
  αpar-sync-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
    → A at → B at
    → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-sync-offer-at {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a}
                     mA mB eqP bP eqQ bQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with da at | db at
  ...   | yes _ | yes _ with fP at a | fQ at a | bP | bQ
  ...     | just _ | just _ | refl | refl = refl
  αpar-sync-offer-at mA mB eqP bP eqQ bQ feq | refl | yes _ | no ¬B = ⊥-elim (¬B mB)
  αpar-sync-offer-at mA mB eqP bP eqQ bQ feq | refl | no ¬A | _     = ⊥-elim (¬A mA)

  -- Offer lemma for the P-solo case (event in A only).
  αpar-soloL-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
    → A at → ¬ (B at)
    → P .force ≡ vis fP → fP at a ≡ just P′
    → Q .force ≡ vis fQ
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
  αpar-soloL-offer-at {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a}
                      mA ¬mB eqP bP eqQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with da at | db at
  ...   | yes _ | no _ with fP at a | bP
  ...     | just _ | refl = refl
  αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq | refl | yes _ | yes mB = ⊥-elim (¬mB mB)
  αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq | refl | no ¬A | _      = ⊥-elim (¬A mA)

  -- Offer lemma for the Q-solo case (event in B only).
  αpar-soloR-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
      {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
    → ¬ (A at) → B at
    → P .force ≡ vis fP
    → Q .force ≡ vis fQ → fQ at a ≡ just Q′
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → f at a ≡ just (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
  αpar-soloR-offer-at {da = da} {db = db} {fP = fP} {fQ = fQ} {at = at} {a = a}
                      ¬mA mB eqP eqQ bQ feq
    rewrite eqP | eqQ
    with feq
  ... | refl with da at | db at
  ...   | no _ | yes _ with fQ at a | bQ
  ...     | just _ | refl = refl
  αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq | refl | yes mA | _     = ⊥-elim (¬mA mA)
  αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq | refl | no _   | no ¬B = ⊥-elim (¬B mB)

  -- Helper: when both operands are vis-shaped and the event is in neither alphabet,
  -- the merged offer function `f` returns `nothing`, so it cannot equal `just T`.
  αpar-refuse-offer-at :
    ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
      {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
      {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
      {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
      {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      {at : AnyTypes E} {a : proj₁ at}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))}
      {T : ITree E (ExtI I) (R × S)}
    → ¬ (A at) → ¬ (B at)
    → P .force ≡ vis fP → Q .force ≡ vis fQ
    → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q) .force ≡ vis f
    → ¬ (f at a ≡ just T)
  αpar-refuse-offer-at {da = da} {db = db} {at = at} {a = a}
                       ¬mA ¬mB eqP eqQ feq branch-eq
    rewrite eqP | eqQ with feq
  ... | refl with da at | db at
  ...   | no _   | no _  = case branch-eq of λ ()
  ...   | yes mA | _     = ⊥-elim (¬mA mA)
  ...   | no _   | yes mB = ⊥-elim (¬mB mB)

-- Public LTS step / refusal lemmas.

αpar-sync-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    {fP fQ} {at : AnyTypes E} {a : proj₁ at}
  → A at → B at
  → P .force ≡ vis fP → fP at a ≡ just P′
  → Q .force ≡ vis fQ → fQ at a ≡ just Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-sync-step mA mB eqP bP eqQ bQ
  with αpar-force-vis-vis eqP eqQ
... | f , feq = sVis feq (αpar-sync-offer-at mA mB eqP bP eqQ bQ feq)

αpar-soloL-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
    {fP fQ} {at : AnyTypes E} {a : proj₁ at}
  → A at → ¬ (B at)
  → P .force ≡ vis fP → fP at a ≡ just P′
  → Q .force ≡ vis fQ
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P′ ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
αpar-soloL-step mA ¬mB eqP bP eqQ
  with αpar-force-vis-vis eqP eqQ
... | f , feq = sVis feq (αpar-soloL-offer-at mA ¬mB eqP bP eqQ feq)

αpar-soloR-step :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
    {fP fQ} {at : AnyTypes E} {a : proj₁ at}
  → ¬ (A at) → B at
  → P .force ≡ vis fP
  → Q .force ≡ vis fQ → fQ at a ≡ just Q′
  → (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
      ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
    (P ⟦ A ¿ da ∥ B ¿ db ⟧ Q′)
αpar-soloR-step ¬mA mB eqP eqQ bQ
  with αpar-force-vis-vis eqP eqQ
... | f , feq = sVis feq (αpar-soloR-offer-at ¬mA mB eqP eqQ bQ feq)

-- Out-of-alphabet refusal: an event in neither alphabet is refused.
αpar-refuse-out :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
    {A : Alpha} {da : Dec-Alpha A} {B : Alpha} {db : Dec-Alpha B}
    {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
    {fP fQ} {at : AnyTypes E} {a : proj₁ at}
    {T : ITree E (ExtI I) (R × S)}
  → ¬ (A at) → ¬ (B at)
  → P .force ≡ vis fP → Q .force ≡ vis fQ
  → ¬ ((P ⟦ A ¿ da ∥ B ¿ db ⟧ Q)
         ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► T)
αpar-refuse-out ¬mA ¬mB eqP eqQ (sVis feq branch-eq) =
  αpar-refuse-offer-at ¬mA ¬mB eqP eqQ feq branch-eq
αpar-refuse-out ¬mA ¬mB eqP eqQ (sMixVis eq-mix _)
  rewrite eqP | eqQ = case eq-mix of λ ()

-------------------------------------------------------------------------------------
-- Replicated (list-folded) alphabetised parallel
--
-- A finite collection of homogeneous components, each carrying its own alphabet,
-- composed by a right fold of the binary operator.  The per-layer interface is the
-- head alphabet intersected (implicitly, by the binary operator) with the union of
-- the tail's alphabets, expressed as a `⊎`-disjunction (a hand-rolled `Any`; see the
-- note on `unionα` below).

record Comp {ℓi ℓr} (I : Set ℓ → Set ℓi) (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr) where
  constructor comp
  field
    alpha : Alpha
    adec  : Dec-Alpha alpha
    proc  : ITree E (ExtI I) R

-- Nested-product return type: one R per component, terminating in ⊤.
RetOf : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → List (Comp I R) → Set ℓr
RetOf {ℓr = ℓr} {R = R} []       = ⊤ {ℓr}
RetOf {R = R}        (_ ∷ xs)    = R × RetOf xs

-- Union alphabet of a list of components: an event is in the union when it is in
-- some component's alphabet.
--
-- NOTE on universe levels.  `Alpha`'s codomain is `Set₀` (every existing alphabet —
-- `All∈ _ = ⊤ {lzero}`, `None∈ _ = Lift lzero ⊥` — and the membership obligations of
-- the binary operator all live in `Set₀`).  The std-lib `Any P` over `List A` lands
-- at level `a ⊔ p` where `a` is the level of the element type `A`; here `A = Comp I R`
-- is large (`lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ lsuc ℓr`), so `Any (…) xs` cannot inhabit `Set₀`.
-- We therefore phrase the union by direct recursion over the list as the disjunction
-- (`_⊎_`) of the per-component memberships, which stays in `Set₀`.  This is exactly
-- `Any (λ c → Comp.alpha c at) xs` semantically (a witness selects one component),
-- and `unionDec` mirrors `LAny.any?`'s `⊎-dec` recursion to decide it.
unionα : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} → List (Comp I R) → Alpha
unionα []       at = Lift lzero ⊥
unionα (c ∷ xs) at = Comp.alpha c at ⊎ unionα xs at

unionDec : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (xs : List (Comp I R)) → Dec-Alpha (unionα xs)
unionDec []       at = no (λ { (lift ()) })
unionDec (c ∷ xs) at = Comp.adec c at ⊎-dec unionDec xs at

-- The fold: each head is composed (binary) against the union of the tail.
∥list : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → (xs : List (Comp I R)) → ITree E (ExtI I) (RetOf xs)
∥list []       = Skip
∥list (c ∷ xs) =
  Comp.proc c ⟦ Comp.alpha c ¿ Comp.adec c
              ∥ unionα xs ¿ unionDec xs
              ⟧ (∥list xs)

-- Head-layer unfolding: the cons clause is definitionally the binary composition
-- of the head against the folded tail.
∥list-unfold :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (c : Comp I R) (xs : List (Comp I R))
  → ∥list (c ∷ xs)
      ≡ (Comp.proc c ⟦ Comp.alpha c ¿ Comp.adec c
                     ∥ unionα xs ¿ unionDec xs
                     ⟧ (∥list xs))
∥list-unfold c xs = refl

-------------------------------------------------------------------------------------
-- Sanity instance

private
  module Sanity where
    All∈ : Alpha
    All∈ _ = ⊤ {lzero}
    All-dec : Dec-Alpha All∈
    All-dec _ = yes tt
    None∈ : Alpha
    None∈ _ = Lift lzero ⊥
    None-dec : Dec-Alpha None∈
    None-dec _ = no (λ ())

    composite-is-vis :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        (P : ITree E (ExtI I) R) (Q : ITree E (ExtI I) S)
        {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
        {fQ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) S))}
      → P .force ≡ vis fP
      → Q .force ≡ vis fQ
      → Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) (R × S)))) ]
          ((P ⟦ All∈ ¿ All-dec ∥ None∈ ¿ None-dec ⟧ Q) .force ≡ vis f)
    composite-is-vis P Q eqP eqQ rewrite eqP | eqQ = _ , refl

    -- A = B = everything  ⇒  events synchronise.
    sanity-sync :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {P P′ : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
        {fP fQ} {at : AnyTypes E} {a : proj₁ at}
      → P .force ≡ vis fP → fP at a ≡ just P′
      → Q .force ≡ vis fQ → fQ at a ≡ just Q′
      → (P ⟦ All∈ ¿ All-dec ∥ All∈ ¿ All-dec ⟧ Q)
          ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
        (P′ ⟦ All∈ ¿ All-dec ∥ All∈ ¿ All-dec ⟧ Q′)
    sanity-sync eqP bP eqQ bQ = αpar-sync-step tt tt eqP bP eqQ bQ

    -- A = everything, B = nothing  ⇒  P steps alone.
    sanity-soloL :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {P P′ : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
        {fP fQ} {at : AnyTypes E} {a : proj₁ at}
      → P .force ≡ vis fP → fP at a ≡ just P′
      → Q .force ≡ vis fQ
      → (P ⟦ All∈ ¿ All-dec ∥ None∈ ¿ None-dec ⟧ Q)
          ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
        (P′ ⟦ All∈ ¿ All-dec ∥ None∈ ¿ None-dec ⟧ Q)
    sanity-soloL eqP bP eqQ = αpar-soloL-step tt (λ { (lift ()) }) eqP bP eqQ

    -- A = nothing, B = everything  ⇒  Q steps alone.
    sanity-soloR :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {P : ITree E (ExtI I) R} {Q Q′ : ITree E (ExtI I) S}
        {fP fQ} {at : AnyTypes E} {a : proj₁ at}
      → P .force ≡ vis fP
      → Q .force ≡ vis fQ → fQ at a ≡ just Q′
      → (P ⟦ None∈ ¿ None-dec ∥ All∈ ¿ All-dec ⟧ Q)
          ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─►
        (P ⟦ None∈ ¿ None-dec ∥ All∈ ¿ All-dec ⟧ Q′)
    sanity-soloR eqP eqQ bQ = αpar-soloR-step (λ { (lift ()) }) tt eqP eqQ bQ

    -- A = B = nothing  ⇒  event refused.
    sanity-refuse :
      ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs}
        {P : ITree E (ExtI I) R} {Q : ITree E (ExtI I) S}
        {fP fQ} {at : AnyTypes E} {a : proj₁ at}
        {T : ITree E (ExtI I) (R × S)}
      → P .force ≡ vis fP → Q .force ≡ vis fQ
      → ¬ ((P ⟦ None∈ ¿ None-dec ∥ None∈ ¿ None-dec ⟧ Q)
             ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► T)
    sanity-refuse eqP eqQ = αpar-refuse-out (λ { (lift ()) }) (λ { (lift ()) }) eqP eqQ
