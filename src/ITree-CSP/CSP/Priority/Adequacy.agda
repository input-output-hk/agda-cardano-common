{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Adequacy of the executable priority operator `Pri` (Layer 2), PROVEN.
--
-- `Pri O t fb` and the ground-truth relational spec `Semantics.PriLTS._─[_]─►ᵖ_`
-- (over `PriOrder.prop O`) agree, as a CROSS-SIMULATION up to strong bisim `_∼_`:
-- every `Pri`-step is matched by a `─►ᵖ`-step whose residual, once RE-prioritised,
-- is bisimilar to the `Pri`-successor — and conversely.  (The earlier
-- `u ∼ u′` statement was provably false: a `Pri`-step lands in an already-
-- prioritised residual `Pri O u′ fb′`, not the plain `u′`.)
--
-- Both directions are SINGLE-STEP case analyses (not coinductive): the `∼`
-- closes by `sbisim-refl` because the `Pri`-successor IS `Pri O u′ fb′`
-- definitionally (only the ret/√ case needs the tiny `no-steps-∼` lemma).
--
-- `--safe`, 0 postulates, nothing from `Classical`/`dne`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_; lower) renaming (suc to lsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_; foldr; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Priority.Adequacy {ℓ ℓe} {E : Set ℓ → Set ℓe} where

open PTree
open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Refusals {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} using (Offers)
open import CSP.Priority.Base       {ℓ} {ℓe} {E}
import Semantics.PriLTS

------------------------------------------------------------------------
-- Order-independent helper lemmas.
------------------------------------------------------------------------

-- boolean `∨`
∨-false-l : ∀ {x y} → x ∨ y ≡ false → x ≡ false
∨-false-l {false} _ = refl
∨-false-l {true}  ()

∨-false-r : ∀ {x y} → x ∨ y ≡ false → y ≡ false
∨-false-r {false} eq = eq
∨-false-r {true}  ()

is-just-false→nothing : ∀ {ℓ'} {X : Set ℓ'} {m : Maybe X} → is-just m ≡ false → m ≡ nothing
is-just-false→nothing {m = nothing} _ = refl
is-just-false→nothing {m = just _}  ()

-- `foldr (λ b → is-just (v …) ∨_) false` over a channel-value list = the
-- `dominated?` scan; relate its being `false` to pointwise `nothing`.
module _ {ℓr} {R : Set ℓr}
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) where

  domScan : List Ev → Bool
  domScan = foldr (λ b acc → is-just (v (Ev.at b) (Ev.val b)) ∨ acc) false

  domScan-false→∅ : (bs : List Ev) → domScan bs ≡ false
                  → ∀ b → b ∈ bs → v (Ev.at b) (Ev.val b) ≡ nothing
  domScan-false→∅ (b0 ∷ bs) eq b (here refl) = is-just-false→nothing (∨-false-l eq)
  domScan-false→∅ (b0 ∷ bs) eq b (there mem) = domScan-false→∅ bs (∨-false-r eq) b mem

  domScan-∅→false : (bs : List Ev)
                  → (∀ b → b ∈ bs → v (Ev.at b) (Ev.val b) ≡ nothing) → domScan bs ≡ false
  domScan-∅→false []        _ = refl
  domScan-∅→false (b0 ∷ bs) h rewrite h b0 (here refl) = domScan-∅→false bs (λ b m → h b (there m))

-- `Offers` at a react node ⟺ the visible map is `just` there.
offers→just : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {B : Set ℓ} {eb : E B} {ab : B}
            → PTree.force t ≡ react v τc
            → Offers t (evl (evLabel B eb ab))
            → Σ[ t′ ∈ PTree E (ExtI E) R ] v (B , eb) ab ≡ just t′
offers→just eqf (t′ , sVis eqf′ br) =
  t′ , subst (λ w → w _ _ ≡ just t′) (sym (proj₁ (react-injective (trans (sym eqf) eqf′)))) br

just→offers : ∀ {ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {B : Set ℓ} {eb : E B} {ab : B} {t′}
            → PTree.force t ≡ react v τc → v (B , eb) ab ≡ just t′
            → Offers t (evl (evLabel B eb ab))
just→offers eqf br = _ , sVis eqf br

-- two step-less trees are bisimilar (vacuous simulation, not corecursive).
no-steps-∼ : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E (ExtI E) R}
           → (∀ {l t′} → ¬ (t₁ ─[ l ]─► t′))
           → (∀ {l t′} → ¬ (t₂ ─[ l ]─► t′))
           → t₁ ∼ t₂
no-steps-∼ n₁ n₂ .Sbisim.fwd .SSimF.on-ev  step = ⊥-elim (n₁ step)
no-steps-∼ n₁ n₂ .Sbisim.fwd .SSimF.on-tau step = ⊥-elim (n₁ step)
no-steps-∼ n₁ n₂ .Sbisim.bwd .SSimF.on-ev  step = ⊥-elim (n₂ step)
no-steps-∼ n₁ n₂ .Sbisim.bwd .SSimF.on-tau step = ⊥-elim (n₂ step)

-- `deadlock` has no transition of any kind.
deadlock-stuck : ∀ {ℓr} {R : Set ℓr} {l} {t′ : PTree E (ExtI E) R}
               → ¬ (deadlock ─[ l ]─► t′)
deadlock-stuck (sRet ())
deadlock-stuck (sSil ())
deadlock-stuck (sVis refl ())
deadlock-stuck (sTau refl ())

------------------------------------------------------------------------
-- Adequacy proper (order-dependent).
------------------------------------------------------------------------

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) where
  private
    module Spec = Semantics.PriLTS
                    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {ℓo} {E} {ExtI E} (PriOrder.prop O)
  open PriOrder O using (_<ᵖ_; above; above-sound; above-complete)

  -- `dominated? = false` ⟺ the node offers no strict dominator (pLo's premise).
  dom-false→premise : {t : PTree E (ExtI E) R}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at}
    → PTree.force t ≡ react v τc → dominated? O v (at ∙ a) ≡ false
    → ∀ b → (at ∙ a) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b))
  dom-false→premise {v = v} {at = at} {a = a} eqf domf ((B , eb) ∙ ab) lt offer
    with offers→just eqf offer
  ... | t′ , vjust =
        case trans (sym vjust)
                   (domScan-false→∅ v (above (at ∙ a)) domf ((B , eb) ∙ ab) (above-complete lt))
          of λ ()

  premise→dom-false : {t : PTree E (ExtI E) R}
      {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
      {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
      {at : AnyTypes E} {a : proj₁ at}
    → PTree.force t ≡ react v τc
    → (∀ b → (at ∙ a) <ᵖ b → ¬ Offers t (evl (Spec.evOfEv b)))
    → dominated? O v (at ∙ a) ≡ false
  premise→dom-false {v = v} {at = at} {a = a} eqf prem =
    domScan-∅→false v (above (at ∙ a)) helper
    where
      helper : ∀ b → b ∈ above (at ∙ a) → v (Ev.at b) (Ev.val b) ≡ nothing
      helper ((B , eb) ∙ ab) mem with v (B , eb) ab in veq
      ... | nothing = refl
      ... | just t′ = ⊥-elim (prem ((B , eb) ∙ ab) (above-sound mem) (just→offers eqf veq))

  -- Maximality ⟺ empty `above`, hence `isMax? = true` and `dominated? = false`.
  Max→above-[] : {e : Ev} → Maximal (PriOrder.prop O) e → above e ≡ []
  Max→above-[] {e} mx with above e in aeq
  ... | []      = refl
  ... | b0 ∷ bs = ⊥-elim (mx b0 (above-sound (subst (b0 ∈_) (sym aeq) (here refl))))

  Max→dom-false : {e : Ev}
      {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
    → Maximal (PriOrder.prop O) e → dominated? O v e ≡ false
  Max→dom-false {e} mx rewrite Max→above-[] mx = refl

  Max→isMax? : {e : Ev} → Maximal (PriOrder.prop O) e → isMax? O e ≡ true
  Max→isMax? {e} mx rewrite Max→above-[] mx = refl

  null-true→[] : ∀ {a′} {A : Set a′} {xs : List A} → null xs ≡ true → xs ≡ []
  null-true→[] {xs = []}    _ = refl
  null-true→[] {xs = _ ∷ _} ()

  isMax?→Max : {e : Ev} → isMax? O e ≡ true → Maximal (PriOrder.prop O) e
  isMax?→Max eq b lt = case subst (b ∈_) (null-true→[] eq) (above-complete lt) of λ ()

  -- `Pri O deadlock finBr-deadlock` also has no transition, so ≈ deadlock.
  Pri-deadlock-stuck : ∀ {l} {t′ : PTree E (ExtI E) R}
                     → ¬ (Pri O deadlock finBr-deadlock ─[ l ]─► t′)
  Pri-deadlock-stuck (sRet ())
  Pri-deadlock-stuck (sSil ())
  Pri-deadlock-stuck (sTau refl ())
  -- deadlock's visible map is `λ _ _ → nothing`, so `priVisAt … nothing …` = nothing
  Pri-deadlock-stuck (sVis {at = at} {a = a} refl br) = case br of λ ()

  deadlock∼Pri-deadlock : deadlock ∼ Pri O deadlock (finBr-deadlock {R = R})
  deadlock∼Pri-deadlock = no-steps-∼ (λ st → deadlock-stuck st) (λ st → Pri-deadlock-stuck st)

  -- Head reduction of `priForce`, obtained by casing the NODE `nP` (a fresh
  -- argument — NOT `force t`, whose casing is ill-typed while `force (Pri …)` is
  -- in scope).  Returns an EXISTENTIAL force-eq shared by the residual and the
  -- reconstructed spec-step.  Applied at `nP = force t` the result is STUCK but a
  -- VALID term; adequacy projects it via Σ-eta, so both sides use the same eqf.
  priForce-ret-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP)
                    (dec : Dec (isStable t)) {r : R}
                  → nP ≡ ret r → priForce O nP eqf fb dec ≡ ret r
  priForce-ret-eq (ret r) eqf dec refl = refl

  priForce-sil-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP)
                    (dec : Dec (isStable t)) {c : PTree E (ExtI E) R}
                  → nP ≡ sil c
                  → Σ[ eqf′ ∈ PTree.force t ≡ sil c ]
                      priForce O nP eqf fb dec ≡ sil (Pri O c (FinBr.next fb (sSil eqf′)))
  priForce-sil-eq (sil c) eqf dec refl = eqf , refl

  priForce-yes-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                    (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP) {st : isStable t}
                    {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  → nP ≡ react v τc
                  → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                      priForce O nP eqf fb (yes st) ≡ react (priVis O v eqf′ fb) (λ _ _ → nothing)
  priForce-yes-eq (react v τc) eqf refl = eqf , refl

  priForce-no-eq : {t : PTree E (ExtI E) R} {fb : FinBr t}
                   (nP : NodeKind E (ExtI E) R) (eqf : PTree.force t ≡ nP) {¬st : ¬ isStable t}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                 → nP ≡ react v τc
                 → Σ[ eqf′ ∈ PTree.force t ≡ react v τc ]
                     priForce O nP eqf fb (no ¬st) ≡ react (priMax O v eqf′ fb) (priTau O τc eqf′ fb)
  priForce-no-eq (react v τc) eqf refl = eqf , refl

  -- wrappers: `force (Pri O t fb) = priForce O (force t) refl fb (stab? t fb)`
  fPri-ret : {t : PTree E (ExtI E) R} {fb : FinBr t} {r : R}
           → PTree.force t ≡ ret r → PTree.force (Pri O t fb) ≡ ret r
  fPri-ret {t = t} {fb = fb} eqft = priForce-ret-eq (PTree.force t) refl (stab? t fb) eqft

  fPri-sil : {t : PTree E (ExtI E) R} {fb : FinBr t} {c : PTree E (ExtI E) R}
           → PTree.force t ≡ sil c
           → Σ[ eqf ∈ PTree.force t ≡ sil c ]
               PTree.force (Pri O t fb) ≡ sil (Pri O c (FinBr.next fb (sSil eqf)))
  fPri-sil {t = t} {fb = fb} eqft = priForce-sil-eq (PTree.force t) refl (stab? t fb) eqft

  -- react head: DECIDE stability internally (casing `stab? t fb`, a plain `Dec`,
  -- is clean even with `force (Pri O t fb)` in the goal), returning the stable
  -- (priVis) or unstable (priMax/priTau) reduction of `force (Pri O t fb)`.
  fPri-react : {t : PTree E (ExtI E) R} {fb : FinBr t}
               {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
             → PTree.force t ≡ react v τc
             → (Σ[ st ∈ isStable t ] Σ[ eqf ∈ PTree.force t ≡ react v τc ]
                  PTree.force (Pri O t fb) ≡ react (priVis O v eqf fb) (λ _ _ → nothing))
             ⊎ (Σ[ ¬st ∈ (¬ isStable t) ] Σ[ eqf ∈ PTree.force t ≡ react v τc ]
                  PTree.force (Pri O t fb) ≡ react (priMax O v eqf fb) (priTau O τc eqf fb))
  fPri-react {t = t} {fb = fb} eqft with stab? t fb
  ... | yes st  = let (eqf , peq) = priForce-yes-eq (PTree.force t) refl {st = st} eqft
                  in  inj₁ (st , eqf , peq)
  ... | no ¬st  = let (eqf , peq) = priForce-no-eq (PTree.force t) refl {¬st = ¬st} eqft
                  in  inj₂ (¬st , eqf , peq)

  -- Invert a FIRED offer/τ: `priVisAt/priMaxAt/priTauAt … ≡ just u` yields the
  -- surviving-offer conditions + the offer/τ value + the residual (= u).  Cased
  -- on the fresh dominance/value args (NOT the baked `in eva`), so invertible.
  priVisAt-just : {t : PTree E (ExtI E) R}
                  {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                  {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                  (dm : Bool) (dmeq : dominated? O v (at ∙ a) ≡ dm)
                  (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                → priVisAt O v eqf fb at a dm dmeq m meq ≡ just u
                → Σ[ t′ ∈ PTree E (ExtI E) R ] (dm ≡ false) × Σ[ eva ∈ v at a ≡ just t′ ]
                    (Pri O t′ (FinBr.next fb (sVis eqf eva)) ≡ u)
  priVisAt-just eqf dm    dmeq nothing   meq ()
  priVisAt-just eqf true  dmeq (just t′) meq ()
  priVisAt-just eqf false dmeq (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  priMaxAt-just : {t : PTree E (ExtI E) R}
                  {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                  {at : AnyTypes E} {a : proj₁ at} {u : PTree E (ExtI E) R}
                  (mx : Bool) (mxeq : isMax? O (at ∙ a) ≡ mx)
                  (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                → priMaxAt O v eqf fb at a mx mxeq m meq ≡ just u
                → Σ[ t′ ∈ PTree E (ExtI E) R ] (mx ≡ true) × Σ[ eva ∈ v at a ≡ just t′ ]
                    (Pri O t′ (FinBr.next fb (sVis eqf eva)) ≡ u)
  priMaxAt-just eqf mx    mxeq nothing   meq ()
  priMaxAt-just eqf false mxeq (just t′) meq ()
  priMaxAt-just eqf true  mxeq (just t′) meq eqj = t′ , refl , meq , just-injective eqj

  priTauAt-just : {t : PTree E (ExtI E) R}
                  {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                  {i : AnyTypes (ExtI E)} {a : proj₁ i} {u : PTree E (ExtI E) R}
                  (m : Maybe (PTree E (ExtI E) R)) (meq : τc i a ≡ m)
                → priTauAt O τc eqf fb i a m meq ≡ just u
                → Σ[ t′ ∈ PTree E (ExtI E) R ] Σ[ eia ∈ τc i a ≡ just t′ ]
                    (Pri O t′ (FinBr.next fb (sTau eqf eia)) ≡ u)
  priTauAt-just eqf nothing   meq ()
  priTauAt-just eqf (just t′) meq eqj = t′ , meq , just-injective eqj

  -- constructive duals: a surviving offer/τ FIRES to its prioritised residual.
  priVisAt-fires : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                   (dm : Bool) (dmeq : dominated? O v (at ∙ a) ≡ dm)
                   (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → dm ≡ false → m ≡ just t′
                 → Σ[ eva ∈ v at a ≡ just t′ ]
                     priVisAt O v eqf fb at a dm dmeq m meq ≡ just (Pri O t′ (FinBr.next fb (sVis eqf eva)))
  priVisAt-fires eqf true  dmeq m         meq () mj
  priVisAt-fires eqf false dmeq nothing   meq _  ()
  priVisAt-fires eqf false dmeq (just t′) meq _  refl = meq , refl

  priMaxAt-fires : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E (ExtI E) R}
                   (mx : Bool) (mxeq : isMax? O (at ∙ a) ≡ mx)
                   (m : Maybe (PTree E (ExtI E) R)) (meq : v at a ≡ m)
                 → mx ≡ true → m ≡ just t′
                 → Σ[ eva ∈ v at a ≡ just t′ ]
                     priMaxAt O v eqf fb at a mx mxeq m meq ≡ just (Pri O t′ (FinBr.next fb (sVis eqf eva)))
  priMaxAt-fires eqf false mxeq m         meq () mj
  priMaxAt-fires eqf true  mxeq nothing   meq _  ()
  priMaxAt-fires eqf true  mxeq (just t′) meq _  refl = meq , refl

  priTauAt-fires : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                   (eqf : PTree.force t ≡ react v τc) {fb : FinBr t}
                   {i : AnyTypes (ExtI E)} {a : proj₁ i} {t′ : PTree E (ExtI E) R}
                   (m : Maybe (PTree E (ExtI E) R)) (meq : τc i a ≡ m)
                 → m ≡ just t′
                 → Σ[ eia ∈ τc i a ≡ just t′ ]
                     priTauAt O τc eqf fb i a m meq ≡ just (Pri O t′ (FinBr.next fb (sTau eqf eia)))
  priTauAt-fires eqf nothing   meq ()
  priTauAt-fires eqf (just t′) meq refl = meq , refl

  -- extract the ∀-form of stability from a react node (`isStable` unfolds via `force t`).
  isStable-react : {t : PTree E (ExtI E) R}
                   {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                 → PTree.force t ≡ react v τc → isStable t
                 → ∀ i a → τc i a ≡ nothing
  isStable-react {t = t} eqft st i a with PTree.force t | eqft
  ... | react v′ τc′ | refl = st i a

  -- every `Pri`-step is matched by a `─►ᵖ`-step (residual re-prioritised, up to ∼).
  pri-adequacy-fwd : {t : PTree E (ExtI E) R} {fb : FinBr t}
                     {l : Label R} {u : PTree E (ExtI E) R}
                   → Pri O t fb ─[ l ]─► u
                   → Σ[ u′ ∈ PTree E (ExtI E) R ] Σ[ fb′ ∈ FinBr u′ ]
                       ((t Spec.─[ l ]─►ᵖ u′) × (u ∼ Pri O u′ fb′))
  -- Case `force t` FIRST via `in eqft` (`step`'s type is the tree
  -- `Pri O t fb ─[l]─► u`, so no `force t` is abstracted — clean); then `with
  -- step` and reduce `force (Pri O t fb)` through the `fPri-*` lemmas, sharing
  -- their existential `eqf` between the residual and the reconstructed spec-step.
  pri-adequacy-fwd {t = t} {fb = fb} step with PTree.force t in eqft
  -- ret r ⇒ force(Pri) = ret r ⇒ only a √-step to deadlock (spec p√)
  ... | ret r with step
  ...   | sRet eq   = deadlock , finBr-deadlock
                    , Spec.p√ (sRet (trans eqft (trans (sym (fPri-ret eqft)) eq)))
                    , deadlock∼Pri-deadlock
  ...   | sSil eq   = case trans (sym (fPri-ret eqft)) eq of λ ()
  ...   | sVis eq _ = case trans (sym (fPri-ret eqft)) eq of λ ()
  ...   | sTau eq _ = case trans (sym (fPri-ret eqft)) eq of λ ()
  pri-adequacy-fwd {t = t} {fb = fb} step | sil c with fPri-sil {fb = fb} eqft | step
  -- sil c ⇒ force(Pri) = sil (Pri O c …) ⇒ a τ-step (spec pτ)
  ...   | eqf , peq | sSil eq   =
            c , FinBr.next fb (sSil eqf) , Spec.pτ (sSil eqf)
              , subst (_∼ Pri O c (FinBr.next fb (sSil eqf)))
                      (sil-injective (trans (sym peq) eq)) (sbisim-refl _)
  ...   | eqf , peq | sRet eq   = case trans (sym peq) eq of λ ()
  ...   | eqf , peq | sVis eq _ = case trans (sym peq) eq of λ ()
  ...   | eqf , peq | sTau eq _ = case trans (sym peq) eq of λ ()
  pri-adequacy-fwd {t = t} {fb = fb} step | react v τc with fPri-react {fb = fb} eqft | step
  -- react, STABLE ⇒ priVis ⇒ pLo (visible); a τ is impossible (τc ≡ λ _ _ → nothing)
  ...   | inj₁ (st , eqf , peq) | sRet eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (st , eqf , peq) | sSil eq = case trans (sym peq) eq of λ ()
  ...   | inj₁ (st , eqf , peq) | sTau {i = i} {a = a} eq br =
            case subst (λ w → w i a ≡ just _)
                       (sym (proj₂ (react-injective (trans (sym peq) eq)))) br of λ ()
  ...   | inj₁ (st , eqf , peq) | sVis {at = at} {a = a} eq br
            with priVisAt-just eqf (dominated? O v (at ∙ a)) refl (v at a) refl
                   (subst (λ w → w at a ≡ just _)
                          (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , dmfalse , eva , P≡u =
              t′ , FinBr.next fb (sVis eqf eva)
                 , Spec.pLo (sVis eqf eva) st (dom-false→premise eqf dmfalse)
                 , subst (_∼ Pri O t′ (FinBr.next fb (sVis eqf eva))) P≡u (sbisim-refl _)
  -- react, UNSTABLE ⇒ priMax (visible ⇒ pMax) / priTau (τ ⇒ pτ)
  pri-adequacy-fwd {t = t} {fb = fb} step | react v τc | inj₂ (¬st , eqf , peq) | sRet eq =
            case trans (sym peq) eq of λ ()
  pri-adequacy-fwd {t = t} {fb = fb} step | react v τc | inj₂ (¬st , eqf , peq) | sSil eq =
            case trans (sym peq) eq of λ ()
  pri-adequacy-fwd {t = t} {fb = fb} step | react v τc | inj₂ (¬st , eqf , peq)
        | sVis {at = at} {a = a} eq br
            with priMaxAt-just eqf (isMax? O (at ∙ a)) refl (v at a) refl
                   (subst (λ w → w at a ≡ just _)
                          (sym (proj₁ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , mxtrue , eva , P≡u =
              t′ , FinBr.next fb (sVis eqf eva)
                 , Spec.pMax (isMax?→Max mxtrue) (sVis eqf eva)
                 , subst (_∼ Pri O t′ (FinBr.next fb (sVis eqf eva))) P≡u (sbisim-refl _)
  pri-adequacy-fwd {t = t} {fb = fb} step | react v τc | inj₂ (¬st , eqf , peq)
        | sTau {i = i} {a = a} eq br
            with priTauAt-just eqf (τc i a) refl
                   (subst (λ w → w i a ≡ just _)
                          (sym (proj₂ (react-injective (trans (sym peq) eq)))) br)
  ...     | t′ , eia , P≡u =
              t′ , FinBr.next fb (sTau eqf eia)
                 , Spec.pτ (sTau eqf eia)
                 , subst (_∼ Pri O t′ (FinBr.next fb (sTau eqf eia))) P≡u (sbisim-refl _)

  -- every `─►ᵖ`-step is matched by a `Pri`-step (residual re-prioritised, up to ∼).
  pri-adequacy-bwd : {t : PTree E (ExtI E) R} {fb : FinBr t}
                     {l : Label R} {u′ : PTree E (ExtI E) R}
                   → t Spec.─[ l ]─►ᵖ u′
                   → Σ[ u ∈ PTree E (ExtI E) R ] Σ[ fb′ ∈ FinBr u′ ]
                       ((Pri O t fb ─[ l ]─► u) × (u ∼ Pri O u′ fb′))
  -- √: ret fires unconditionally (to deadlock)
  pri-adequacy-bwd (Spec.p√ (sRet eqft)) =
      deadlock , finBr-deadlock , sRet (fPri-ret eqft) , deadlock∼Pri-deadlock
  -- τ from a sil node ⇒ Pri sil-steps
  pri-adequacy-bwd {fb = fb} (Spec.pτ (sSil eqft)) =
      let (eqf , peq) = fPri-sil {fb = fb} eqft
      in  Pri O _ (FinBr.next fb (sSil eqf)) , FinBr.next fb (sSil eqf) , sSil peq , sbisim-refl _
  -- τ from a react τ-branch ⇒ node is UNSTABLE ⇒ priTau fires
  pri-adequacy-bwd {fb = fb} (Spec.pτ (sTau {τc = τc} {i = i} {a = a} eqft br)) with fPri-react {fb = fb} eqft
  ... | inj₂ (¬st , eqf , peq) =
        let (eia , tfire) = priTauAt-fires eqf (τc i a) refl br
        in  Pri O _ (FinBr.next fb (sTau eqf eia)) , FinBr.next fb (sTau eqf eia)
              , sTau peq tfire , sbisim-refl _
  pri-adequacy-bwd {t = t} {fb = fb} (Spec.pτ (sTau {τc = τc} {i = i} {a = a} eqft br)) | inj₁ (st , eqf , peq)
        with trans (sym (isStable-react {t = t} eqft st i a)) br
  ... | ()
  -- ≤-maximal visible event: fires whether STABLE (priVis, dominated?=false) or UNSTABLE (priMax, isMax?=true)
  pri-adequacy-bwd {fb = fb} (Spec.pMax mx (sVis {v = v} {at = at} {a = a} eqft br)) with fPri-react {fb = fb} eqft
  ... | inj₁ (st , eqf , peq) =
        let (eva , vfire) = priVisAt-fires eqf (dominated? O v (at ∙ a)) refl (v at a) refl
                                           (Max→dom-false mx) br
        in  Pri O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , sVis peq vfire , sbisim-refl _
  ... | inj₂ (¬st , eqf , peq) =
        let (eva , mfire) = priMaxAt-fires eqf (isMax? O (at ∙ a)) refl (v at a) refl
                                           (Max→isMax? mx) br
        in  Pri O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , sVis peq mfire , sbisim-refl _
  -- non-maximal visible event: fires only from a STABLE state offering no dominator ⇒ priVis
  pri-adequacy-bwd {fb = fb} (Spec.pLo (sVis {v = v} {at = at} {a = a} eqft br) isst prem)
        with fPri-react {fb = fb} eqft
  ... | inj₁ (st , eqf , peq) =
        let (eva , vfire) = priVisAt-fires eqf (dominated? O v (at ∙ a)) refl (v at a) refl
                                           (premise→dom-false eqf prem) br
        in  Pri O _ (FinBr.next fb (sVis eqf eva)) , FinBr.next fb (sVis eqf eva)
              , sVis peq vfire , sbisim-refl _
  ... | inj₂ (¬st , eqf , peq) = ⊥-elim (¬st isst)
