{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Adequacy of the CHANNEL-level priority operator `Priᶜ` (Phase 2 — see
-- `docs/specs/priority-implementation-plan.md`).
--
-- `Priᶜ O t fb` is tied to the ground-truth relational spec
-- `Semantics.PriLTS._─[_]─►ᵖ_` over the CHANNEL-LIFTED order `liftC O`
-- (`e₁ <ᵖ e₂ = chan e₁ <ᶜ chan e₂`), as a CROSS-SIMULATION up to strong bisim,
-- mirroring `CSP.Priority.Adequacy` for the value-level `Pri`.
--
-- The certificate that makes this work is `ExactSupp`: it says every channel in
-- `FinBr.chan-supp` is ACTUALLY offered (has a firing value).  Exactness is what
-- turns the channel-level Bool test `dominatedᶜ?` into the relational premise —
-- "a dominating channel is in chan-supp" becomes "a dominating EVENT is offered"
-- (so `Priᶜ` never prunes a visible event unless a real dominator is on offer).
--
-- STATUS: `--safe`, 0 postulates, nothing from `Classical`/`dne`.
--   * FWD adequacy: UNCONDITIONAL (needs only `ExactSupp` for the residual).
--   * BWD adequacy: UNCONDITIONAL.  Needs `ExactSupp` (the pLo/pMax-from-stable
--     crux) and, in the ONE corner `pMax` fired from an UNSTABLE node, the order's
--     `PriOrderC.above-inhabited` field (every dominating CHANNEL is inhabited).
--     That well-formedness is unavoidable: the spec's `Maximal (liftC O)`
--     quantifies over EVENTS, so an empty-carrier dominating channel makes an
--     event ≤-maximal yet leaves `isMaxᶜ? = false` (channel-max ⊋ event-max).  It
--     is now FOLDED INTO the order (no extra argument to `priᶜ-adequacy-bwd`).
------------------------------------------------------------------------

open import Level using (Level; _⊔_; lower) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.DecPropositional using ()
open import Data.Maybe using (Maybe; just; nothing; Is-just; is-just)
open import Data.Maybe.Properties using (just-injective)
import Data.Maybe.Relation.Unary.Any as MAny
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Priority.ChannelAdequacy {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import Semantics.PriOrder  {ℓ} {ℓe} {E}
open import Semantics.PriOrderC {ℓ} {ℓe} {E}
open import Semantics.LTS       {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim     {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals  {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Priority.Base        {ℓ} {ℓe} {E}
open import CSP.Priority.Channel E-≟
open import CSP.Priority.Adequacy {ℓ} {ℓe} {E}
  using (offers→just; just→offers; no-steps-∼; deadlock-stuck)
open import Data.List.Membership.DecPropositional E-≟ using (_∈?_)
import Semantics.PriLTS

------------------------------------------------------------------------
-- Order-independent helper lemmas.
------------------------------------------------------------------------

-- boolean `∨` inversions
∨-false-l : ∀ {x y} → x ∨ y ≡ false → x ≡ false
∨-false-l {false} _ = refl
∨-false-l {true}  ()

∨-false-r : ∀ {x y} → x ∨ y ≡ false → y ≡ false
∨-false-r {false} eq = eq
∨-false-r {true}  ()

-- `⌊ d ⌋ ≡ false` refutes the decided proposition; `≡ true` proves it
⌊⌋-false→¬ : ∀ {p} {P : Set p} (d : Dec P) → ⌊ d ⌋ ≡ false → ¬ P
⌊⌋-false→¬ (yes _)  () _
⌊⌋-false→¬ (no ¬p)  _  p = ¬p p

⌊⌋-true→ : ∀ {p} {P : Set p} (d : Dec P) → ⌊ d ⌋ ≡ true → P
⌊⌋-true→ (yes p) _  = p
⌊⌋-true→ (no _)  ()

-- `null xs ≡ true ⇒ xs ≡ []`
null-true→[] : ∀ {a′} {A : Set a′} {xs : List A} → null xs ≡ true → xs ≡ []
null-true→[] {xs = []}    _ = refl
null-true→[] {xs = _ ∷ _} ()

-- convert between `≡ just` and `Is-just`
≡just→Is-just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} {x} → m ≡ just x → Is-just m
≡just→Is-just refl = MAny.just _

Is-just→≡just : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} → Is-just m → Σ[ x ∈ X ] m ≡ just x
Is-just→≡just {m = just x} _ = x , refl

-- `any p` over a channel list: `false` ⇒ pointwise false; `true` ⇒ a witness
anyMem-false : (p : AnyTypes E → Bool) (cs : List (AnyTypes E))
             → any p cs ≡ false → ∀ c → c ∈ cs → p c ≡ false
anyMem-false p (c0 ∷ cs) eq c (here refl) = ∨-false-l eq
anyMem-false p (c0 ∷ cs) eq c (there mem) = anyMem-false p cs (∨-false-r eq) c mem

anyMem-true : (p : AnyTypes E → Bool) (cs : List (AnyTypes E))
            → any p cs ≡ true → Σ[ c ∈ AnyTypes E ] (c ∈ cs) × (p c ≡ true)
anyMem-true p (c0 ∷ cs) eq with p c0 in pc0
... | true  = c0 , here refl , pc0
... | false = let (c , mem , pc) = anyMem-true p cs eq
              in  c , there mem , pc

------------------------------------------------------------------------
-- `ExactSupp` — hereditary exactness of a `FinBr`'s channel support.
--
-- Every channel `c ∈ FinBr.chan-supp fb` is genuinely offered by the node: some
-- value of its carrier fires it (`Is-just (v c a)`).  Propagated along every
-- transition via `next`, so it is coinductively usable in the adequacy residual.
------------------------------------------------------------------------

record ExactSupp {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R} (fb : FinBr t)
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  coinductive
  field
    -- every listed channel is actually offered (a firing value exists)
    exact : ∀ {v τc} → PTree.force t ≡ react v τc
          → ∀ {c} → c ∈ FinBr.chan-supp fb → Σ[ a ∈ proj₁ c ] Is-just (v c a)
    -- exactness propagates along every transition
    next  : ∀ {l t′} (st : t ─[ l ]─► t′) → ExactSupp (FinBr.next fb st)

-- `deadlock` offers nothing, so its (empty) support is vacuously exact.
exactSupp-deadlock : ∀ {ℓr} {R : Set ℓr} → ExactSupp (finBr-deadlock {R = R})
ExactSupp.exact exactSupp-deadlock refl ()
ExactSupp.next  exactSupp-deadlock (sRet ())
ExactSupp.next  exactSupp-deadlock (sSil ())
ExactSupp.next  exactSupp-deadlock (sVis refl ())
ExactSupp.next  exactSupp-deadlock (sTau refl ())

------------------------------------------------------------------------
-- The channel→event order lift.
------------------------------------------------------------------------

-- `liftC O`: an event order that compares only channels — `e₁ <ᵖ e₂ = chan e₁ <ᶜ chan e₂`
liftC : ∀ {ℓo} → PriOrderC ℓo → PriOrderProp ℓo
liftC O = record
  { _<ᵖ_      = λ x y → PriOrderC._<ᶜ_ O (Ev.at x) (Ev.at y)
  ; <ᵖ-irrefl = PriOrderC.<ᶜ-irrefl O
  ; <ᵖ-trans  = PriOrderC.<ᶜ-trans O
  }

------------------------------------------------------------------------
-- Adequacy proper (order-dependent).
------------------------------------------------------------------------

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo) where
  private
    module Spec = Semantics.PriLTS
                    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {ℓo} {E} {ExtI E} (liftC O)
  open PriOrderC O using (aboveᶜ; aboveᶜ-sound; aboveᶜ-complete; above-inhabited)
  open PriOrderProp (liftC O) using (_<ᵖ_)

  ----------------------------------------------------------------------
  -- CRUX bridges linking the Bool test `dominatedᶜ?` to the spec premise.
  ----------------------------------------------------------------------

  -- COMPLETENESS side (uses `FinBr.chan-compl` only, no `ExactSupp`):
  -- `dominatedᶜ? = false` ⇒ the node offers no strictly-dominating event.
  domᶜ-false→premise : {t : PTree E (ExtI E) R} {fb : FinBr t}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at}
    → PTree.force t ≡ react v τc → dominatedᶜ? O fb at ≡ false
    → ∀ b → (at ∙ a) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b))
  domᶜ-false→premise {fb = fb} {v = v} {at = at} eqf domf ((B , eb) ∙ ab) lt offer
    with offers→just eqf offer
  ... | t′ , vjust =
        ⌊⌋-false→¬ ((B , eb) ∈? FinBr.chan-supp fb)
          (anyMem-false (λ c → ⌊ c ∈? FinBr.chan-supp fb ⌋) (aboveᶜ at) domf
                        (B , eb) (aboveᶜ-complete lt))
          (FinBr.chan-compl fb eqf (B , eb) ab (≡just→Is-just vjust))

  -- EXACTNESS side (uses `ExactSupp.exact`): `dominatedᶜ? = true` ⇒ some
  -- strictly-dominating EVENT is actually offered (this stops over-pruning).
  domᶜ-true→dominator : {t : PTree E (ExtI E) R} {fb : FinBr t}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at}
    → ExactSupp fb → PTree.force t ≡ react v τc → dominatedᶜ? O fb at ≡ true
    → Σ[ b ∈ Ev ] ((at ∙ a) <ᵖ b) × Offers t (evl (Spec.evOfEv b))
  domᶜ-true→dominator {fb = fb} {v = v} {at = at} es eqf domt
    with anyMem-true (λ c → ⌊ c ∈? FinBr.chan-supp fb ⌋) (aboveᶜ at) domt
  ... | c , c∈above , ⌊c⌋ with ExactSupp.exact es eqf (⌊⌋-true→ (c ∈? FinBr.chan-supp fb) ⌊c⌋)
  ...   | a′ , isj with Is-just→≡just isj
  ...     | x , vjust = (c ∙ a′) , aboveᶜ-sound c∈above
                      , just→offers eqf vjust

  -- `false` from the spec premise (via the exactness bridge, by contradiction).
  premise→domᶜ-false : {t : PTree E (ExtI E) R} {fb : FinBr t}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at}
    → ExactSupp fb → PTree.force t ≡ react v τc
    → (∀ b → (at ∙ a) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b)))
    → dominatedᶜ? O fb at ≡ false
  premise→domᶜ-false {fb = fb} {at = at} {a = a} es eqf prem with dominatedᶜ? O fb at in domeq
  ... | false = refl
  ... | true  = let (b , lt , off) = domᶜ-true→dominator {a = a} es eqf domeq
                in  ⊥-elim (prem b lt off)

  -- channel-maximality bridges (`isMaxᶜ?` ⟷ event-maximality of the lift).
  isMaxᶜ→Maximal : {at : AnyTypes E} {a : proj₁ at}
                 → isMaxᶜ? O at ≡ true → Maximal (liftC O) (at ∙ a)
  isMaxᶜ→Maximal {at = at} mxeq b lt =
    case subst (Ev.at b ∈_) (null-true→[] mxeq) (aboveᶜ-complete lt) of λ ()

  -- the ONE direction needing well-formedness: event-max ⇒ channel-max, using
  -- the order's `above-inhabited` (else an empty-carrier dominator makes an event
  -- ≤-maximal yet `isMaxᶜ? = false`); `above-inhabited` supplies the inhabitant.
  Maximal→isMaxᶜ : {at : AnyTypes E} {a : proj₁ at}
                 → Maximal (liftC O) (at ∙ a) → isMaxᶜ? O at ≡ true
  Maximal→isMaxᶜ {at = at} mx with aboveᶜ at in aeq
  ... | []       = refl
  ... | c0 ∷ cs  =
        let c0∈ : c0 ∈ aboveᶜ at
            c0∈ = subst (c0 ∈_) (sym aeq) (here refl)
        in  ⊥-elim (mx (c0 ∙ above-inhabited c0∈) (aboveᶜ-sound c0∈))

  -- a ≤-maximal event vacuously satisfies the "no dominator offered" premise
  Maximal→prem : {t : PTree E (ExtI E) R} {at : AnyTypes E} {a : proj₁ at}
               → Maximal (liftC O) (at ∙ a)
               → ∀ b → (at ∙ a) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b))
  Maximal→prem mx b lt _ = mx b lt

  ----------------------------------------------------------------------
  -- `priForceᶜ` head reductions + fired-offer inversions (mirror
  -- `CSP.Priority.Adequacy`, at the `ᶜ` helpers).
  ----------------------------------------------------------------------

  priForceᶜ-ret-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                     (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP)
                     (dec : Dec (isStable t)) {r : R}
                   → nP ≡ ret r → priForceᶜ O nP eqf fb dec ≡ ret r
  priForceᶜ-ret-eq (ret r) eqf dec refl = refl

  priForceᶜ-sil-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                     (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP)
                     (dec : Dec (isStable t)) {c : PTree E (ExtI E) R}
                   → nP ≡ sil c
                   → Σ[ eqf′ ∈ PTree.force t ≡ sil c ]
                       priForceᶜ O nP eqf fb dec ≡ sil (Priᶜ O c (FinBr.next fb (sSil eqf′)))
  priForceᶜ-sil-eq (sil c) eqf dec refl = eqf , refl

  priForceᶜ-yes-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                     (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP) {st : isStable t}
                     {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                     {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   → nP ≡ react v τc
                   → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                       priForceᶜ O nP eqf fb (yes st) ≡ react (priVisᶜ O v eqf′ fb) (λ _ _ → nothing)
  priForceᶜ-yes-eq (react v τc) eqf refl = eqf , refl

  priForceᶜ-no-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP) {¬st : ¬ isStable t}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  → nP ≡ react v τc
                  → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                      priForceᶜ O nP eqf fb (no ¬st) ≡ react (priMaxᶜ O v eqf′ fb) (priTauᶜ O τc eqf′ fb)
  priForceᶜ-no-eq (react v τc) eqf refl = eqf , refl

  fPriᶜ-ret : {t : PTree E (ExtI E) R} {fb : FinBr t} {r : R}
            → PTree.force t ≡ ret r → PTree.force (Priᶜ O t fb) ≡ ret r
  fPriᶜ-ret {t = t} {fb = fb} eqft = priForceᶜ-ret-eq (PTree.force t) refl (stab? t fb) eqft

  fPriᶜ-sil : {t : PTree E (ExtI E) R} {fb : FinBr t} {c : PTree E (ExtI E) R}
            → PTree.force t ≡ sil c
            → Σ[ eqf ∈ PTree.force t ≡ sil c ]
                PTree.force (Priᶜ O t fb) ≡ sil (Priᶜ O c (FinBr.next fb (sSil eqf)))
  fPriᶜ-sil {t = t} {fb = fb} eqft = priForceᶜ-sil-eq (PTree.force t) refl (stab? t fb) eqft

  fPriᶜ-react : {t : PTree E (ExtI E) R} {fb : FinBr t}
                {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → PTree.force t ≡ react v τc
              → (Σ[ st ∈ isStable t ] Σ[ eqf ∈ PTree.force t ≡ react v τc ]
                   PTree.force (Priᶜ O t fb) ≡ react (priVisᶜ O v eqf fb) (λ _ _ → nothing))
              ⊎ (Σ[ ¬st ∈ (¬ isStable t) ] Σ[ eqf ∈ PTree.force t ≡ react v τc ]
                   PTree.force (Priᶜ O t fb) ≡ react (priMaxᶜ O v eqf fb) (priTauᶜ O τc eqf fb))
  fPriᶜ-react {t = t} {fb = fb} eqft with stab? t fb
  ... | yes st = let (eqf , peq) = priForceᶜ-yes-eq (PTree.force t) refl {st = st} eqft
                 in  inj₁ (st , eqf , peq)
  ... | no ¬st = let (eqf , peq) = priForceᶜ-no-eq (PTree.force t) refl {¬st = ¬st} eqft
                 in  inj₂ (¬st , eqf , peq)

  priVisAtᶜ-just : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                   (dm : Bool) (dmeq : dominatedᶜ? O fb at ≡ dm)
                   (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → priVisAtᶜ O v eqf fb at a dm dmeq m meq ≡ just u
                 → Σ[ t′ ∈ PTree E (ExtI E) R ] (dm ≡ false) × Σ[ eva ∈ v at a ≡ just t′ ]
                     (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)) ≡ u)
  priVisAtᶜ-just eqf dm    dmeq nothing   meq ()
  priVisAtᶜ-just eqf true  dmeq (just t′) meq ()
  priVisAtᶜ-just eqf false dmeq (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  priMaxAtᶜ-just : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                   (mx : Bool) (mxeq : isMaxᶜ? O at ≡ mx)
                   (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → priMaxAtᶜ O v eqf fb at a mx mxeq m meq ≡ just u
                 → Σ[ t′ ∈ PTree E (ExtI E) R ] (mx ≡ true) × Σ[ eva ∈ v at a ≡ just t′ ]
                     (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)) ≡ u)
  priMaxAtᶜ-just eqf mx    mxeq nothing   meq ()
  priMaxAtᶜ-just eqf false mxeq (just t′) meq ()
  priMaxAtᶜ-just eqf true  mxeq (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  priTauAtᶜ-just : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {i : AnyTypes (ExtI E)} {a : proj₁ i} {u : PTree E (ExtI E) R}
                   (m : Maybe (PTree E (ExtI E) R)) (meq : τc i a ≡ m)
                 → priTauAtᶜ O τc eqf fb i a m meq ≡ just u
                 → Σ[ t′ ∈ PTree E (ExtI E) R ] Σ[ eia ∈ τc i a ≡ just t′ ]
                     (Priᶜ O t′ (FinBr.next fb (sTau eqf eia)) ≡ u)
  priTauAtᶜ-just eqf nothing   meq ()
  priTauAtᶜ-just eqf (just t′) meq eqj = t′ , meq , just-injective eqj

  priVisAtᶜ-fires : {t : PTree E (ExtI E) R}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                    {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                    (dm : Bool) (dmeq : dominatedᶜ? O fb at ≡ dm)
                    (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                  → dm ≡ false → m ≡ just t′
                  → Σ[ eva ∈ v at a ≡ just t′ ]
                      priVisAtᶜ O v eqf fb at a dm dmeq m meq ≡ just (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)))
  priVisAtᶜ-fires eqf true  dmeq m         meq () mj
  priVisAtᶜ-fires eqf false dmeq nothing   meq _  ()
  priVisAtᶜ-fires eqf false dmeq (just t′) meq _  refl = meq , refl

  priMaxAtᶜ-fires : {t : PTree E (ExtI E) R}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                    {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                    (mx : Bool) (mxeq : isMaxᶜ? O at ≡ mx)
                    (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                  → mx ≡ true → m ≡ just t′
                  → Σ[ eva ∈ v at a ≡ just t′ ]
                      priMaxAtᶜ O v eqf fb at a mx mxeq m meq ≡ just (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)))
  priMaxAtᶜ-fires eqf false mxeq m         meq () mj
  priMaxAtᶜ-fires eqf true  mxeq nothing   meq _  ()
  priMaxAtᶜ-fires eqf true  mxeq (just t′) meq _  refl = meq , refl

  priTauAtᶜ-fires : {t : PTree E (ExtI E) R}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                    (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                    {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) R}
                    (m : Maybe (PTree E (ExtI E) R)) (meq : τc i a ≡ m)
                  → m ≡ just t′
                  → Σ[ eia ∈ τc i a ≡ just t′ ]
                      priTauAtᶜ O τc eqf fb i a m meq ≡ just (Priᶜ O t′ (FinBr.next fb (sTau eqf eia)))
  priTauAtᶜ-fires eqf nothing   meq ()
  priTauAtᶜ-fires eqf (just t′) meq refl = meq , refl

  -- react-node stability in ∀-form
  isStable-react : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                 → PTree.force t ≡ react v τc → isStable t → ∀ i a → τc i a ≡ nothing
  isStable-react {t = t} eqft st i a with PTree.force t | eqft
  ... | react v′ τc′ | refl = st i a

  -- `Priᶜ O deadlock finBr-deadlock` is also stuck, hence ≈ deadlock
  Priᶜ-deadlock-stuck : ∀ {l} {t′ : PTree E (ExtI E) R}
                      → ¬ (Priᶜ O deadlock finBr-deadlock ─[ l ]─► t′)
  Priᶜ-deadlock-stuck (sRet ())
  Priᶜ-deadlock-stuck (sSil ())
  Priᶜ-deadlock-stuck (sTau refl ())
  Priᶜ-deadlock-stuck (sVis {at = at} {a = a} refl br) = case br of λ ()

  deadlock∼Priᶜ-deadlock : deadlock ∼ Priᶜ O deadlock (finBr-deadlock {R = R})
  deadlock∼Priᶜ-deadlock = no-steps-∼ (λ st → deadlock-stuck st) (λ st → Priᶜ-deadlock-stuck st)

  ----------------------------------------------------------------------
  -- FWD adequacy: every `Priᶜ`-step is matched by a `─►ᵖ`-step (residual
  -- re-prioritised, up to ∼).  UNCONDITIONAL (only `ExactSupp` for the residual).
  ----------------------------------------------------------------------

  priᶜ-adequacy-fwd : {t : PTree E (ExtI E) R} {fb : FinBr t}
                      {l : Label R} {u : PTree E (ExtI E) R}
                    → ExactSupp fb → Priᶜ O t fb ─[ l ]─► u
                    → Σ[ u′ ∈ PTree E (ExtI E) R ] Σ[ fb′ ∈ FinBr u′ ] Σ[ es′ ∈ ExactSupp fb′ ]
                        ((t Spec.─[ l ]─►ᵖ u′) × (u ∼ Priᶜ O u′ fb′))
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step with PTree.force t in eqft
  ... | ret r with step
  ...   | sRet eq   = deadlock , finBr-deadlock , exactSupp-deadlock
                    , Spec.p√ (sRet (trans eqft (trans (sym (fPriᶜ-ret eqft)) eq)))
                    , deadlock∼Priᶜ-deadlock
  ...   | sSil eq   = case trans (sym (fPriᶜ-ret eqft)) eq of λ ()
  ...   | sVis eq _ = case trans (sym (fPriᶜ-ret eqft)) eq of λ ()
  ...   | sTau eq _ = case trans (sym (fPriᶜ-ret eqft)) eq of λ ()
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | sil c with fPriᶜ-sil {fb = fb} eqft | step
  ...   | eqf , peq | sSil eq   =
            c , FinBr.next fb (sSil eqf) , ExactSupp.next es (sSil eqf) , Spec.pτ (sSil eqf)
              , subst (_∼ Priᶜ O c (FinBr.next fb (sSil eqf)))
                      (sil-injective (trans (sym peq) eq)) (sbisim-refl _)
  ...   | eqf , peq | sRet eq   = case trans (sym peq) eq of λ ()
  ...   | eqf , peq | sVis eq _ = case trans (sym peq) eq of λ ()
  ...   | eqf , peq | sTau eq _ = case trans (sym peq) eq of λ ()
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | react v τc with fPriᶜ-react {fb = fb} eqft | step
  ...   | inj₁ (st , eqf , peq) | sRet eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (st , eqf , peq) | sSil eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (st , eqf , peq) | sTau {i = i} {a = a} eq br =
            case subst (λ w → w i a ≡ just _)
                       (sym (proj₂ (react-injective (trans (sym peq) eq)))) br of λ ()
  ...   | inj₁ (st , eqf , peq) | sVis {at = at} {a = a} eq br
            with priVisAtᶜ-just eqf (dominatedᶜ? O fb at) refl (v at a) refl
                   (subst (λ w → w at a ≡ just _)
                          (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , dmfalse , eva , P≡u =
              t′ , FinBr.next fb (sVis eqf eva) , ExactSupp.next es (sVis eqf eva)
                 , Spec.pLo (sVis eqf eva) st (domᶜ-false→premise {fb = fb} {at = at} {a = a} eqf dmfalse)
                 , subst (_∼ Priᶜ O t′ (FinBr.next fb (sVis eqf eva))) P≡u (sbisim-refl _)
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | react v τc | inj₂ (¬st , eqf , peq) | sRet eq =
            case trans (sym peq) eq of λ ()
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | react v τc | inj₂ (¬st , eqf , peq) | sSil eq =
            case trans (sym peq) eq of λ ()
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | react v τc | inj₂ (¬st , eqf , peq)
        | sVis {at = at} {a = a} eq br
            with priMaxAtᶜ-just eqf (isMaxᶜ? O at) refl (v at a) refl
                   (subst (λ w → w at a ≡ just _)
                          (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , mxtrue , eva , P≡u =
              t′ , FinBr.next fb (sVis eqf eva) , ExactSupp.next es (sVis eqf eva)
                 , Spec.pMax (isMaxᶜ→Maximal {at = at} {a = a} mxtrue) (sVis eqf eva)
                 , subst (_∼ Priᶜ O t′ (FinBr.next fb (sVis eqf eva))) P≡u (sbisim-refl _)
  priᶜ-adequacy-fwd {t = t} {fb = fb} es step | react v τc | inj₂ (¬st , eqf , peq)
        | sTau {i = i} {a = a} eq br
            with priTauAtᶜ-just eqf (τc i a) refl
                   (subst (λ w → w i a ≡ just _)
                          (sym (proj₂ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , eia , P≡u =
              t′ , FinBr.next fb (sTau eqf eia) , ExactSupp.next es (sTau eqf eia)
                 , Spec.pτ (sTau eqf eia)
                 , subst (_∼ Priᶜ O t′ (FinBr.next fb (sTau eqf eia))) P≡u (sbisim-refl _)

  ----------------------------------------------------------------------
  -- BWD adequacy: every `─►ᵖ`-step is matched by a `Priᶜ`-step.  Needs
  -- `ExactSupp` (pLo / pMax-from-stable) and, for `pMax` from an UNSTABLE node,
  -- `inh` (dominating channels inhabited) — see the module header.
  ----------------------------------------------------------------------

  priᶜ-adequacy-bwd : {t : PTree E (ExtI E) R} {fb : FinBr t}
                      {l : Label R} {u′ : PTree E (ExtI E) R}
                    → ExactSupp fb → t Spec.─[ l ]─►ᵖ u′
                    → Σ[ u ∈ PTree E (ExtI E) R ] Σ[ fb′ ∈ FinBr u′ ] Σ[ es′ ∈ ExactSupp fb′ ]
                        ((Priᶜ O t fb ─[ l ]─► u) × (u ∼ Priᶜ O u′ fb′))
  -- √: ret fires unconditionally (to deadlock)
  priᶜ-adequacy-bwd es (Spec.p√ (sRet eqft)) =
      deadlock , finBr-deadlock , exactSupp-deadlock
    , sRet (fPriᶜ-ret eqft) , deadlock∼Priᶜ-deadlock
  -- τ from a sil node ⇒ Priᶜ sil-steps
  priᶜ-adequacy-bwd {fb = fb} es (Spec.pτ (sSil eqft)) =
      let (eqf , peq) = fPriᶜ-sil {fb = fb} eqft
      in  Priᶜ O _ (FinBr.next fb (sSil eqf)) , FinBr.next fb (sSil eqf)
            , ExactSupp.next es (sSil eqf) , sSil peq , sbisim-refl _
  -- τ from a react τ-branch ⇒ node UNSTABLE ⇒ priTauᶜ fires
  priᶜ-adequacy-bwd {fb = fb} es (Spec.pτ (sTau {τc = τc} {i = i} {a = a} eqft br))
        with fPriᶜ-react {fb = fb} eqft
  ... | inj₂ (¬st , eqf , peq) =
        let (eia , tfire) = priTauAtᶜ-fires eqf (τc i a) refl br
        in  Priᶜ O _ (FinBr.next fb (sTau eqf eia)) , FinBr.next fb (sTau eqf eia)
              , ExactSupp.next es (sTau eqf eia) , sTau peq tfire , sbisim-refl _
  priᶜ-adequacy-bwd {t = t} {fb = fb} es (Spec.pτ (sTau {τc = τc} {i = i} {a = a} eqft br))
        | inj₁ (st , eqf , peq) with trans (sym (isStable-react {t = t} eqft st i a)) br
  ... | ()
  -- ≤-maximal visible event: fires from STABLE (priVisᶜ) or UNSTABLE (priMaxᶜ) node
  priᶜ-adequacy-bwd {t = t} {fb = fb} es (Spec.pMax mx (sVis {v = v} {at = at} {a = a} eqft br))
        with fPriᶜ-react {fb = fb} eqft
  ... | inj₁ (st , eqf , peq) =
        let (eva , vfire) = priVisAtᶜ-fires eqf (dominatedᶜ? O fb at) refl (v at a) refl
                              (premise→domᶜ-false {t = t} {fb = fb} {at = at} {a = a} es eqf
                                 (Maximal→prem {t = t} {at = at} {a = a} mx)) br
        in  Priᶜ O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , ExactSupp.next es (sVis eqf eva) , sVis peq vfire , sbisim-refl _
  ... | inj₂ (¬st , eqf , peq) =
        let (eva , mfire) = priMaxAtᶜ-fires eqf (isMaxᶜ? O at) refl (v at a) refl
                              (Maximal→isMaxᶜ {at = at} {a = a} mx) br
        in  Priᶜ O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , ExactSupp.next es (sVis eqf eva) , sVis peq mfire , sbisim-refl _
  -- non-maximal visible event: fires only from a STABLE state offering no dominator
  priᶜ-adequacy-bwd {fb = fb} es (Spec.pLo (sVis {v = v} {at = at} {a = a} eqft br) isst prem)
        with fPriᶜ-react {fb = fb} eqft
  ... | inj₁ (st , eqf , peq) =
        let (eva , vfire) = priVisAtᶜ-fires eqf (dominatedᶜ? O fb at) refl (v at a) refl
                              (premise→domᶜ-false {fb = fb} {at = at} {a = a} es eqf prem) br
        in  Priᶜ O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , ExactSupp.next es (sVis eqf eva) , sVis peq vfire , sbisim-refl _
  ... | inj₂ (¬st , eqf , peq) = ⊥-elim (¬st isst)
