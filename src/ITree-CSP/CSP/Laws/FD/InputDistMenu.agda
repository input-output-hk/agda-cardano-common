{-# OPTIONS --guardedness #-}

-- input-dist, MENU version (TPC 1.11 / UCS 2.11):  ?x:A → (P x ⊓ Q x) = (?x:A→P) ⊓ (?x:A→Q),
-- where A is an arbitrary SET of events (the prefix-CHOICE menu `pchoice`), possibly
-- spanning many channels — unlike the single-channel `Prefix e P` of CSP.Laws.FD.InputDist.
--
-- The menu is `pchoice (menuOf dom K)` where `dom at a : Bool` decides membership of the
-- event `(at,a)` in A and `K at a` is the continuation; offers/refusals depend only on
-- `dom` (not K), which is what makes the decomposition continuation-independent.
--
-- FD-direct (the two sides differ in initial stability — left offers the menu immediately,
-- right first resolves the ⊓), exactly mirroring CSP.Laws.FD.InputDist: a menu
-- failures/divergence decomposition composed with the ⊓ decomposition.

open import Level using (Level)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.InputDistMenu {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Offers; Refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_; ≈FD-refl; ≈FD-trans)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (stable-no-τ)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)
open import CSP.Laws.FD.FDLawsIChoiceRep E-≟ using (⊓-cong-FD≈)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-- the menu  ?x:A → K(x)  with A decided by `dom` and continuation `K`.
menuOf : (dom : (at : AnyTypes E) → proj₁ at → Bool)
         (K   : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
       → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
menuOf dom K at a = if dom at a then just (K at a) else nothing

-- the menu offers exactly the events with `dom ≡ true`, with continuation `K`.
menuOf-just : (dom : (at : AnyTypes E) → proj₁ at → Bool)
              (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
              (at : AnyTypes E) (a : proj₁ at)
            → dom at a ≡ true → menuOf dom K at a ≡ just (K at a)
menuOf-just dom K at a dt rewrite dt = refl

menu-ev : (dom : (at : AnyTypes E) → proj₁ at → Bool)
          (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
          {B : Set ℓ} {e′ : E B} {a : B}
        → dom (B , e′) a ≡ true
        → (pchoice (menuOf dom K)) ─[ ev (evl (evLabel B e′ a)) ]─► (K (B , e′) a)
menu-ev dom K {B} {e′} {a} dt = sVis {at = B , e′} {a = a} refl (menuOf-just dom K (B , e′) a dt)

menu-stable : (dom : (at : AnyTypes E) → proj₁ at → Bool)
              (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
            → isStable (pchoice (menuOf dom K))
menu-stable dom K _ _ = refl

-- every big-step out of a menu is empty or peels one offered event (cont = K).
menu-⟹-inv : (dom : (at : AnyTypes E) → proj₁ at → Bool)
              (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
              {s : List (Event√ R)} {W : PTree E (ExtI E) R}
            → (pchoice (menuOf dom K)) ⟹⟨ s ⟩ W
            → (W ≡ pchoice (menuOf dom K) × s ≡ [])
            ⊎ (Σ[ B ∈ Set ℓ ] Σ[ e′ ∈ E B ] Σ[ a ∈ B ] Σ[ t ∈ List (Event√ R) ]
                 (dom (B , e′) a ≡ true × s ≡ evl (evLabel B e′ a) ∷ t × (K (B , e′) a) ⟹⟨ t ⟩ W))
menu-⟹-inv dom K ⟹-refl              = inj₁ (refl , refl)
menu-⟹-inv dom K (⟹-τ (sSil ()) _)
menu-⟹-inv dom K (⟹-τ (sTau refl ()) _)
menu-⟹-inv dom K (⟹-ev (sRet ()) _)
menu-⟹-inv dom K (⟹-ev (sVis {at = at} {a = a} refl br) rest) with dom at a in eqd
... | false = case br of λ ()
... | true with br
...           | refl = inj₂ (proj₁ at , proj₂ at , a , _ , eqd , refl , rest)

-- offers / refusals are continuation-INDEPENDENT (depend only on `dom`).
menu-offers : (dom : (at : AnyTypes E) → proj₁ at → Bool)
              (K K′ : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) {l : Event√ R}
            → Offers (pchoice (menuOf dom K)) l → Offers (pchoice (menuOf dom K′)) l
menu-offers dom K K′ (_ , sRet ())
menu-offers dom K K′ (_ , sVis {at = at} {a = a} refl br) with dom at a in eqd
... | false = case br of λ ()
... | true  = K′ at a , sVis {at = at} {a = a} refl (menuOf-just dom K′ at a eqd)

menu-refuses : (dom : (at : AnyTypes E) → proj₁ at → Bool)
               (K K′ : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) {Z : Event√ R → Set ℓx}
             → Refuses (pchoice (menuOf dom K)) Z → Refuses (pchoice (menuOf dom K′)) Z
menu-refuses dom K K′ (_ , noOff) =
  menu-stable dom K′ , λ l Zl off → noOff l Zl (menu-offers dom K′ K off)

-- failures of a menu: {([], refusing)} ∪ {x∷t : x offered, failure of K x}.
menu-failures→ : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                 (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
                 {s : List (Event√ R)} {Z : Event√ R → Set ℓx}
               → failures (pchoice (menuOf dom K)) s Z
               → ((s ≡ []) × Refuses (pchoice (menuOf dom K)) Z)
               ⊎ (Σ[ B ∈ Set ℓ ] Σ[ e′ ∈ E B ] Σ[ a ∈ B ] Σ[ t ∈ List (Event√ R) ]
                    (dom (B , e′) a ≡ true × s ≡ evl (evLabel B e′ a) ∷ t × failures (K (B , e′) a) t Z))
menu-failures→ dom K (W , pw , ref) with menu-⟹-inv dom K pw
... | inj₁ (refl , refl)                       = inj₁ (refl , ref)
... | inj₂ (B , e′ , a , t , dt , refl , reach) = inj₂ (B , e′ , a , t , dt , refl , (W , reach , ref))

menu-failures-nil : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                    (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) {Z : Event√ R → Set ℓx}
                  → Refuses (pchoice (menuOf dom K)) Z → failures (pchoice (menuOf dom K)) [] Z
menu-failures-nil dom K ref = pchoice (menuOf dom K) , ⟹-refl , ref

menu-failures-cons : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                     (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
                     {B : Set ℓ} {e′ : E B} {a : B} (dt : dom (B , e′) a ≡ true)
                     {t : List (Event√ R)} {Z : Event√ R → Set ℓx}
                   → failures (K (B , e′) a) t Z
                   → failures (pchoice (menuOf dom K)) (evl (evLabel B e′ a) ∷ t) Z
menu-failures-cons dom K dt (W , reach , ref) = W , ⟹-ev (menu-ev dom K dt) reach , ref

-- divergences of a menu: {x∷t : x offered, divergence of K x}.
menu-div→ : (dom : (at : AnyTypes E) → proj₁ at → Bool)
            (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) {s : List (Event√ R)}
          → divergences (pchoice (menuOf dom K)) s
          → Σ[ B ∈ Set ℓ ] Σ[ e′ ∈ E B ] Σ[ a ∈ B ] Σ[ t ∈ List (Event√ R) ]
              (dom (B , e′) a ≡ true × s ≡ evl (evLabel B e′ a) ∷ t × divergences (K (B , e′) a) t)
menu-div→ dom K d with menu-⟹-inv dom K (d .IsDivergence.reach)
... | inj₁ (eqW , _) =
        ⊥-elim (stable-no-τ (menu-stable dom K)
                  (subst Diverges eqW (d .IsDivergence.divwit) .Diverges.step))
... | inj₂ (B , e′ , a , t , dt , eqPrefix , reach) =
        B , e′ , a , t ++ d .IsDivergence.suffix , dt
          , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) eqPrefix)
          , record { prefix  = t                   ; suffix = d .IsDivergence.suffix
                   ; split   = refl                 ; witness = d .IsDivergence.witness
                   ; reach   = reach                ; divwit = d .IsDivergence.divwit }

menu-div-cons : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
                {B : Set ℓ} {e′ : E B} {a : B} (dt : dom (B , e′) a ≡ true) {t : List (Event√ R)}
              → divergences (K (B , e′) a) t
              → divergences (pchoice (menuOf dom K)) (evl (evLabel B e′ a) ∷ t)
menu-div-cons dom K {B} {e′} {a} dt d = record
  { prefix  = evl (evLabel B e′ a) ∷ d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix
  ; split   = cong (evl (evLabel B e′ a) ∷_) (d .IsDivergence.split)
  ; witness = d .IsDivergence.witness
  ; reach   = ⟹-ev (menu-ev dom K dt) (d .IsDivergence.reach)
  ; divwit  = d .IsDivergence.divwit }

-- lift to failures⊥.
menu-failures⊥→ : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                  (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
                  {s : List (Event√ R)} {Z : Event√ R → Set ℓr}
                → failures⊥ (pchoice (menuOf dom K)) s Z
                → ((s ≡ []) × Refuses (pchoice (menuOf dom K)) Z)
                ⊎ (Σ[ B ∈ Set ℓ ] Σ[ e′ ∈ E B ] Σ[ a ∈ B ] Σ[ t ∈ List (Event√ R) ]
                     (dom (B , e′) a ≡ true × s ≡ evl (evLabel B e′ a) ∷ t × failures⊥ (K (B , e′) a) t Z))
menu-failures⊥→ dom K (inj₁ f) with menu-failures→ dom K f
... | inj₁ (eqs , ref)                       = inj₁ (eqs , ref)
... | inj₂ (B , e′ , a , t , dt , eqs , fC)  = inj₂ (B , e′ , a , t , dt , eqs , inj₁ fC)
menu-failures⊥→ dom K (inj₂ d) with menu-div→ dom K d
... | (B , e′ , a , t , dt , eqs , dC)       = inj₂ (B , e′ , a , t , dt , eqs , inj₂ dC)

menu-failures⊥-nil : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                     (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) {Z : Event√ R → Set ℓr}
                   → Refuses (pchoice (menuOf dom K)) Z → failures⊥ (pchoice (menuOf dom K)) [] Z
menu-failures⊥-nil dom K ref = inj₁ (menu-failures-nil dom K ref)

menu-failures⊥-cons : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                      (K : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R)
                      {B : Set ℓ} {e′ : E B} {a : B} (dt : dom (B , e′) a ≡ true)
                      {t : List (Event√ R)} {Z : Event√ R → Set ℓr}
                    → failures⊥ (K (B , e′) a) t Z
                    → failures⊥ (pchoice (menuOf dom K)) (evl (evLabel B e′ a) ∷ t) Z
menu-failures⊥-cons dom K dt (inj₁ fC) = inj₁ (menu-failures-cons dom K dt fC)
menu-failures⊥-cons dom K dt (inj₂ dC) = inj₂ (menu-div-cons dom K dt dC)

-------------------------------------------------------------------------------------
-- the law (assembled exactly as InputDist, over the general menu).
-------------------------------------------------------------------------------------
module _ {ℓr} {R : Set ℓr} (dom : (at : AnyTypes E) → proj₁ at → Bool)
         (P Q : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R) where

  private
    PQ : (at : AnyTypes E) → proj₁ at → PTree E (ExtI E) R
    PQ at a = P at a ⊓ Q at a

    MP MQ : PTree E (ExtI E) R
    MP = pchoice (menuOf dom P)
    MQ = pchoice (menuOf dom Q)

  dist-F⊥→ : ∀ {s} {Z : Event√ R → Set ℓr}
           → failures⊥ (pchoice (menuOf dom PQ)) s Z → failures⊥ (MP ⊓ MQ) s Z
  dist-F⊥→ f with menu-failures⊥→ dom PQ f
  ... | inj₁ (refl , ref) =
          ⊓-failures⊥←l MP MQ (menu-failures⊥-nil dom P (menu-refuses dom PQ P ref))
  ... | inj₂ (B , e′ , a , t , dt , refl , fbot) with ⊓-failures⊥→ (P (B , e′) a) (Q (B , e′) a) fbot
  ...   | inj₁ fP = ⊓-failures⊥←l MP MQ (menu-failures⊥-cons dom P dt fP)
  ...   | inj₂ fQ = ⊓-failures⊥←r MP MQ (menu-failures⊥-cons dom Q dt fQ)

  dist-F⊥← : ∀ {s} {Z : Event√ R → Set ℓr}
           → failures⊥ (MP ⊓ MQ) s Z → failures⊥ (pchoice (menuOf dom PQ)) s Z
  dist-F⊥← f with ⊓-failures⊥→ MP MQ f
  ... | inj₁ fP with menu-failures⊥→ dom P fP
  ...   | inj₁ (refl , ref)                  = menu-failures⊥-nil dom PQ (menu-refuses dom P PQ ref)
  ...   | inj₂ (B , e′ , a , t , dt , refl , fb) =
            menu-failures⊥-cons dom PQ dt (⊓-failures⊥←l (P (B , e′) a) (Q (B , e′) a) fb)
  dist-F⊥← f | inj₂ fQ with menu-failures⊥→ dom Q fQ
  ...   | inj₁ (refl , ref)                  = menu-failures⊥-nil dom PQ (menu-refuses dom Q PQ ref)
  ...   | inj₂ (B , e′ , a , t , dt , refl , fb) =
            menu-failures⊥-cons dom PQ dt (⊓-failures⊥←r (P (B , e′) a) (Q (B , e′) a) fb)

  dist-D→ : ∀ {s} → divergences (pchoice (menuOf dom PQ)) s → divergences (MP ⊓ MQ) s
  dist-D→ d with menu-div→ dom PQ d
  ... | (B , e′ , a , t , dt , refl , db) with ⊓-div→ (P (B , e′) a) (Q (B , e′) a) db
  ...   | inj₁ dP = ⊓-div←l MP MQ (menu-div-cons dom P dt dP)
  ...   | inj₂ dQ = ⊓-div←r MP MQ (menu-div-cons dom Q dt dQ)

  dist-D← : ∀ {s} → divergences (MP ⊓ MQ) s → divergences (pchoice (menuOf dom PQ)) s
  dist-D← d with ⊓-div→ MP MQ d
  ... | inj₁ dP with menu-div→ dom P dP
  ...   | (B , e′ , a , t , dt , refl , db) = menu-div-cons dom PQ dt (⊓-div←l (P (B , e′) a) (Q (B , e′) a) db)
  dist-D← d | inj₂ dQ with menu-div→ dom Q dQ
  ...   | (B , e′ , a , t , dt , refl , db) = menu-div-cons dom PQ dt (⊓-div←r (P (B , e′) a) (Q (B , e′) a) db)

  -- ?x:A → (P x ⊓ Q x)  ≈FD  (?x:A→P) ⊓ (?x:A→Q)
  input-dist-menu : (pchoice (menuOf dom (λ at a → P at a ⊓ Q at a))) ≈FD (MP ⊓ MQ)
  input-dist-menu = (dist-F⊥← , dist-D←) , (dist-F⊥→ , dist-D→)

-------------------------------------------------------------------------------------
-- input-Dist, MENU version (TPC 1.12 / UCS 2.12):  ?x:A → ⨅ S = ⨅ { ?x:A → Q | Q ∈ S }.
-- Const-continuation menu `menuC dom K = ?x:A → K`; one-line induction over the list
-- (binary input-dist-menu + ⊓-cong-FD≈ + IH), exactly as PrefixDistRep.
-------------------------------------------------------------------------------------

-- the const-continuation menu  ?x:A → K
menuC : (dom : (at : AnyTypes E) → proj₁ at → Bool) → PTree E (ExtI E) R → PTree E (ExtI E) R
menuC dom K = pchoice (menuOf dom (λ _ _ → K))

input-Dist-menu : (dom : (at : AnyTypes E) → proj₁ at → Bool)
                  (P : PTree E (ExtI E) R) (qs : List (PTree E (ExtI E) R))
                → (menuC dom (⨅⁺ P qs)) ≈FD ⨅⁺ (menuC dom P) (map (menuC dom) qs)
input-Dist-menu dom P []       = ≈FD-refl (menuC dom P)
input-Dist-menu dom P (X ∷ xs) =
  ≈FD-trans (input-dist-menu dom (λ _ _ → P) (λ _ _ → ⨅⁺ X xs))
            (⊓-cong-FD≈ (≈FD-refl (menuC dom P)) (input-Dist-menu dom X xs))
