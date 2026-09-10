{-# OPTIONS --guardedness #-}

-- ;-dist-r (T6.2):  P ; (Q ⊓ R) = (P ; Q) ⊓ (P ; R)   at ≈FD.
--
-- Unlike ;-dist-l (a strong bisim — the ⊓ is the OUTERMOST node), here the ⊓ sits INSIDE
-- the continuation, so the ⊓-resolution τ fires at time 0 on the RHS but only after P
-- terminates on the LHS.  That timing is observable under (even weak) bisimulation; only
-- failures/divergences identify the two.  So this is a genuinely FD-DIRECT law and needs
-- a decomposition of failures(P>>X) / divergences(P>>X).
--
-- This module builds that bind FD-theory (specialised to the constant continuation `>>`,
-- which is all dist-r needs) and assembles the law.  The crux is the √-SPLICE: at a ret,
-- force(P>>X) = force X, so bind silently continues into X with no τ and no √.  A
-- behaviour of P>>X is therefore either a √-free P-phase behaviour, or P reaches a ret
-- (√-free) and then an X-phase behaviour.
--
-- The finite reach-inversion (`>>-reach-inv`) and the whole FAILURES side are
-- constructive.  The DIVERGENCES side needs to decide whether an infinite τ-path of P>>X
-- stays in P or exits into X — constructively undecidable — so it uses one targeted
-- classical postulate `>>-Diverges→` (the bind König step), in the exact style of the
-- existing `□-Diverges→` / `△-Diverges→`.  CERTIFIED from the single `dne` axiom in
-- ClassicalFromLEM (Derivation 4, `>>-no-inf`), so the "all FD postulates derive from
-- one dne" invariant holds.

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Process_Trees

module CSP.Laws.FD.SeqDistR {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_>>=_; _>>_; _⊓_; bindV; bindT; viewT)
open import Semantics.LTS       {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Refusals  {E = E} {I = ExtI E} using (Refuses; Offers)
open import Semantics.Failures  {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; IsDivergence; div-extension-closed; empty-div; _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import Semantics.DRBisim   {E = E} {I = ExtI E} using (Diverges)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures→; ⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r)
open import CSP.Laws.FD.SeqLaws      E-≟ using (retarget)
open import CSP.Laws.FD.ParallelRefusals E-≟ using (stable→react; stable-not-ret; mk-stable)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E} using (stable-not-sil)
open import CSP.Laws.Bisim.IterCong  E-≟ using (sil-no-ev; sil-τ-inv; react-τ-inv)
open import CSP.Laws.Bisim.LoopCong  E-≟
  using (fBind-ret; fBind-sil; fBind-react; bindV-elim; bindT-elim; bindV-eq; bindT-eq; bind-τ; bind-ev)

private
  variable
    ℓr ℓs : Level
    R : Set ℓr
    S : Set ℓs

-------------------------------------------------------------------------------------
-- √-free weak reach: a τ-abstracting visible run whose visible events are all `evl`
-- (no √).  Indexed by List Event (continuation-type-independent), so it lifts through
-- `>>` for ANY continuation and embeds into the ordinary ⟹ over Event√ via `map evl`.
-------------------------------------------------------------------------------------

infix 4 _⟹ₚ⟨_⟩_
data _⟹ₚ⟨_⟩_ {ℓr} {R : Set ℓr}
    : PTree E (ExtI E) R → List Event → PTree E (ExtI E) R → Set (Level.suc ℓ Level.⊔ ℓe Level.⊔ ℓr) where
  ⟹ₚ-refl : ∀ {p} → p ⟹ₚ⟨ [] ⟩ p
  ⟹ₚ-τ    : ∀ {p q r s}            → p ─[ τ ]─► q          → q ⟹ₚ⟨ s ⟩ r → p ⟹ₚ⟨ s ⟩ r
  ⟹ₚ-ev   : ∀ {p q r s} {e : Event} → p ─[ ev (evl e) ]─► q → q ⟹ₚ⟨ s ⟩ r → p ⟹ₚ⟨ e ∷ s ⟩ r

-- embed a √-free reach into the ordinary Event√ reach
⟹ₚ→⟹ : {p q : PTree E (ExtI E) R} {s : List Event}
       → p ⟹ₚ⟨ s ⟩ q → p ⟹⟨ map evl s ⟩ q
⟹ₚ→⟹ ⟹ₚ-refl       = ⟹-refl
⟹ₚ→⟹ (⟹ₚ-τ st rest) = ⟹-τ st (⟹ₚ→⟹ rest)
⟹ₚ→⟹ (⟹ₚ-ev st rest) = ⟹-ev st (⟹ₚ→⟹ rest)

-- a √-free reach lifts through `>> X` (bind preserves evl-ness of the P-phase)
>>-liftₚ : {p q : PTree E (ExtI E) R} {s : List Event} (X : PTree E (ExtI E) S)
         → p ⟹ₚ⟨ s ⟩ q → (p >> X) ⟹ₚ⟨ s ⟩ (q >> X)
>>-liftₚ X ⟹ₚ-refl       = ⟹ₚ-refl
>>-liftₚ X (⟹ₚ-τ st rest) = ⟹ₚ-τ (bind-τ (λ _ → X) _ st) (>>-liftₚ X rest)
>>-liftₚ X (⟹ₚ-ev st rest) = ⟹ₚ-ev (bind-ev (λ _ → X) _ st) (>>-liftₚ X rest)

⟹ₚ-trans : {p q r : PTree E (ExtI E) R} {s t : List Event}
         → p ⟹ₚ⟨ s ⟩ q → q ⟹ₚ⟨ t ⟩ r → p ⟹ₚ⟨ s ++ t ⟩ r
⟹ₚ-trans ⟹ₚ-refl       qr = qr
⟹ₚ-trans (⟹ₚ-τ st rest) qr = ⟹ₚ-τ st (⟹ₚ-trans rest qr)
⟹ₚ-trans (⟹ₚ-ev st rest) qr = ⟹ₚ-ev st (⟹ₚ-trans rest qr)

⟹-trans : {p q r : PTree E (ExtI E) R} {s t : List (Event√ R)}
        → p ⟹⟨ s ⟩ q → q ⟹⟨ t ⟩ r → p ⟹⟨ s ++ t ⟩ r
⟹-trans ⟹-refl       qr = qr
⟹-trans (⟹-τ st rest) qr = ⟹-τ st (⟹-trans rest qr)
⟹-trans (⟹-ev st rest) qr = ⟹-ev st (⟹-trans rest qr)

-- transfer a reach across a force-equation (endpoint preserved, or force-equal at refl)
⟹-force-transfer : {a b W : PTree E (ExtI E) R} {s : List (Event√ R)}
                  → PTree.force a ≡ PTree.force b → b ⟹⟨ s ⟩ W
                  → Σ[ W′ ∈ PTree E (ExtI E) R ] (a ⟹⟨ s ⟩ W′) × (PTree.force W′ ≡ PTree.force W)
⟹-force-transfer eq ⟹-refl       = _ , ⟹-refl , eq
⟹-force-transfer eq (⟹-τ st rest) = _ , ⟹-τ (retarget eq st) rest , refl
⟹-force-transfer eq (⟹-ev st rest) = _ , ⟹-ev (retarget eq st) rest , refl

-- divergence is preserved across force-equality (only the first τ-step sees force)
Diverges-force-eq : {a b : PTree E (ExtI E) R} → PTree.force a ≡ PTree.force b → Diverges b → Diverges a
Diverges-force-eq eq d .Diverges.next = d .Diverges.next
Diverges-force-eq eq d .Diverges.step = retarget eq (d .Diverges.step)
Diverges-force-eq eq d .Diverges.rest = d .Diverges.rest

-- divergence lifts through `>> X` (every τ of P′ lifts via bind-τ)
bind-Diverges : {P′ : PTree E (ExtI E) R} (X : PTree E (ExtI E) S) → Diverges P′ → Diverges (P′ >> X)
bind-Diverges X d .Diverges.next = d .Diverges.next >> X
bind-Diverges X d .Diverges.step = bind-τ (λ _ → X) _ (d .Diverges.step)
bind-Diverges X d .Diverges.rest = bind-Diverges X (d .Diverges.rest)

-------------------------------------------------------------------------------------
-- The finite reach-inversion: a weak run of P>>X is either a √-free P-phase run (still
-- inside P, endpoint P′>>X), or P reaches a ret (√-free) and the rest is an X-run.
-------------------------------------------------------------------------------------

>>-reach-inv : {P : PTree E (ExtI E) R} {X : PTree E (ExtI E) S}
               {s : List (Event√ S)} {W : PTree E (ExtI E) S}
             → (P >> X) ⟹⟨ s ⟩ W
             → (Σ[ sp ∈ List Event ] Σ[ P′ ∈ PTree E (ExtI E) R ]
                  (s ≡ map evl sp) × (P ⟹ₚ⟨ sp ⟩ P′) × (W ≡ P′ >> X))
             ⊎ (Σ[ sp ∈ List Event ] Σ[ sx ∈ List (Event√ S) ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
                  (s ≡ map evl sp ++ sx) × (P ⟹ₚ⟨ sp ⟩ P′) × (PTree.force P′ ≡ ret r) × (X ⟹⟨ sx ⟩ W))
>>-reach-inv ⟹-refl = inj₁ ([] , _ , refl , ⟹ₚ-refl , refl)
>>-reach-inv {P = P} {X = X} (⟹-τ st rest) with PTree.force P in eqP
... | ret r = inj₂ ([] , _ , P , r , refl , ⟹ₚ-refl , eqP
                   , ⟹-τ (retarget (sym (fBind-ret (λ _ → X) P eqP)) st) rest)
... | sil c with sil-τ-inv (fBind-sil (λ _ → X) P eqP) st
...   | refl with >>-reach-inv {P = c} {X = X} rest
...     | inj₁ (sp , c′ , seq , reachc , weq) =
          inj₁ (sp , c′ , seq , ⟹ₚ-τ (sSil eqP) reachc , weq)
...     | inj₂ (sp , sx , c′ , r , seq , reachc , fc′ , xr) =
          inj₂ (sp , sx , c′ , r , seq , ⟹ₚ-τ (sSil eqP) reachc , fc′ , xr)
>>-reach-inv {P = P} {X = X} (⟹-τ st rest) | react v τc
  with react-τ-inv (fBind-react (λ _ → X) P eqP) st
... | i , a , br with bindT-elim (λ _ → X) (react v τc) br
...   | c , vt , refl with >>-reach-inv {P = c} {X = X} rest
...     | inj₁ (sp , c′ , seq , reachc , weq) =
          inj₁ (sp , c′ , seq , ⟹ₚ-τ (sTau eqP vt) reachc , weq)
...     | inj₂ (sp , sx , c′ , r , seq , reachc , fc′ , xr) =
          inj₂ (sp , sx , c′ , r , seq , ⟹ₚ-τ (sTau eqP vt) reachc , fc′ , xr)
>>-reach-inv {P = P} {X = X} (⟹-ev st rest) with PTree.force P in eqP
... | ret r = inj₂ ([] , _ , P , r , refl , ⟹ₚ-refl , eqP
                   , ⟹-ev (retarget (sym (fBind-ret (λ _ → X) P eqP)) st) rest)
... | sil c = ⊥-elim (sil-no-ev (fBind-sil (λ _ → X) P eqP) st)
>>-reach-inv {P = P} {X = X} (⟹-ev st rest) | react v τc with st
... | sRet eqf = ⊥-elim (case trans (sym (fBind-react (λ _ → X) P eqP)) eqf of λ ())
... | sVis {at = at} {a = a} eqf br
      with bindV-elim (λ _ → X) (react v τc)
             (subst (λ g → g at a ≡ just _)
                    (sym (proj₁ (react-injective (trans (sym (fBind-react (λ _ → X) P eqP)) eqf)))) br)
...   | c , vv , refl with >>-reach-inv {P = c} {X = X} rest
...     | inj₁ (sp , c′ , seq , reachc , weq) =
          inj₁ (_ ∷ sp , c′ , cong (_ ∷_) seq , ⟹ₚ-ev (sVis eqP vv) reachc , weq)
...     | inj₂ (sp , sx , c′ , r , seq , reachc , fc′ , xr) =
          inj₂ (_ ∷ sp , sx , c′ , r , cong (_ ∷_) seq , ⟹ₚ-ev (sVis eqP vv) reachc , fc′ , xr)

-------------------------------------------------------------------------------------
-- Failures side (constructive): refusal/stability transported across `>>`.
-------------------------------------------------------------------------------------

-- bindT of an empty / nothing τ-branch is nothing
bindT-none : (κ : R → PTree E (ExtI E) S) (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
             (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
             {i : AnyTypes (ExtI E)} {a : proj₁ i}
           → τc i a ≡ nothing → bindT κ (react v τc) i a ≡ nothing
bindT-none κ v τc {i = i} {a = a} eq with τc i a
... | nothing = refl

bindT-nothing-inv : (κ : R → PTree E (ExtI E) S) (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                    (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
                    {i : AnyTypes (ExtI E)} {a : proj₁ i}
                  → bindT κ (react v τc) i a ≡ nothing → τc i a ≡ nothing
bindT-nothing-inv κ v τc {i = i} {a = a} eq with τc i a
... | nothing = refl
... | just _  = case eq of λ ()

-- refusal transported across a force-equation (stability + offers are force-determined)
Refuses-force-eq : (a b : PTree E (ExtI E) R) {ℓx : Level} {B : Event√ R → Set ℓx}
                 → PTree.force a ≡ PTree.force b → Refuses b B → Refuses a B
Refuses-force-eq a b eq (stb , noff) with stable→react {t = b} stb
... | v , τc , eqb , empt =
      mk-stable {t = a} (trans eq eqb) empt
    , λ e be (t , st) → noff e be (t , retarget (sym eq) st)

-- offers of P′>>_ are continuation-independent when P′ forces to an react
>>-offer-react : (P′ : PTree E (ExtI E) R) (X Y : PTree E (ExtI E) S)
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {e : Event√ S}
              → PTree.force P′ ≡ react v τc → Offers (P′ >> Y) e → Offers (P′ >> X) e
>>-offer-react P′ X Y {v} {τc} eqP′ (t , sRet eqf) =
  ⊥-elim (case trans (sym (fBind-react (λ _ → Y) P′ eqP′)) eqf of λ ())
>>-offer-react P′ X Y {v} {τc} eqP′ (t , sVis {at = at} {a = a} eqf br)
  with bindV-elim (λ _ → Y) (react v τc)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react (λ _ → Y) P′ eqP′)) eqf)))) br)
... | c , vv , refl = (c >> X) , sVis (fBind-react (λ _ → X) P′ eqP′) (bindV-eq (λ _ → X) (react v τc) vv)

-- stability of P′>>_ is continuation-independent (forward and the react-inversion)
>>-stable : (P′ : PTree E (ExtI E) R) (Y : PTree E (ExtI E) S) → isStable P′ → isStable (P′ >> Y)
>>-stable P′ Y st with stable→react {t = P′} st
... | v , τc , eqP′ , empt = mk-stable {t = P′ >> Y} (fBind-react (λ _ → Y) P′ eqP′)
                                       (λ i a → bindT-none (λ _ → Y) v τc (empt i a))

>>-stable-inv : (P′ : PTree E (ExtI E) R) (X : PTree E (ExtI E) S)
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → PTree.force P′ ≡ react v τc → isStable (P′ >> X) → isStable P′
>>-stable-inv P′ X {v} {τc} eqP′ st with stable→react {t = P′ >> X} st
... | v′ , τc′ , eqPX , empt′ =
      mk-stable {t = P′} eqP′ (λ i a → bindT-nothing-inv (λ _ → X) v τc
        (trans (cong (λ f → f i a)
                     (proj₂ (react-injective (trans (sym (fBind-react (λ _ → X) P′ eqP′)) eqPX))))
               (empt′ i a)))

-- refusal of P′>>_ is continuation-independent for stable P′
>>-Refuses-transfer : (P′ : PTree E (ExtI E) R) (X Y : PTree E (ExtI E) S) {ℓx : Level} {B : Event√ S → Set ℓx}
                    → isStable P′ → Refuses (P′ >> X) B → Refuses (P′ >> Y) B
>>-Refuses-transfer P′ X Y st (_ , noff) with stable→react {t = P′} st
... | v , τc , eqP′ , empt =
      >>-stable P′ Y st , λ e be off → noff e be (>>-offer-react P′ X Y eqP′ off)

-------------------------------------------------------------------------------------
-- failures(P>>X) decomposition + intros
-------------------------------------------------------------------------------------

-- P-phase intro: P stays inside, reaching a stable react refusing B (cont-independent)
>>-fail←P : (P : PTree E (ExtI E) R) (X : PTree E (ExtI E) S) (P′ : PTree E (ExtI E) R)
            {sp : List Event} {ℓx : Level} {B : Event√ S → Set ℓx}
          → (P ⟹ₚ⟨ sp ⟩ P′) → Refuses (P′ >> X) B → failures (P >> X) (map evl sp) B
>>-fail←P P X P′ reachp ref = (P′ >> X) , ⟹ₚ→⟹ (>>-liftₚ X reachp) , ref

-- X-phase intro: P terminates (√-free) then X has the failure
>>-fail←X : (P : PTree E (ExtI E) R) (X : PTree E (ExtI E) S) (P′ : PTree E (ExtI E) R)
            {sp : List Event} {sx : List (Event√ S)} {r : R} {ℓx : Level} {B : Event√ S → Set ℓx}
          → (P ⟹ₚ⟨ sp ⟩ P′) → (PTree.force P′ ≡ ret r) → failures X sx B
          → failures (P >> X) (map evl sp ++ sx) B
>>-fail←X P X P′ reachp fret (W , xr , ref)
  with ⟹-force-transfer (fBind-ret (λ _ → X) P′ fret) xr
... | W′ , reachW′ , fW′ =
      W′ , ⟹-trans (⟹ₚ→⟹ (>>-liftₚ X reachp)) reachW′ , Refuses-force-eq W′ W fW′ ref

-- a force-view (index is the tree, NOT its force) — pattern matching it exposes the
-- force-equation cleanly, avoiding the `with force _ in _` goal-double-refinement quirk.
data ForceView {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R) : Set (Level.suc ℓ Level.⊔ ℓe Level.⊔ ℓr) where
  fv-ret  : (r : R) → PTree.force t ≡ ret r → ForceView t
  fv-sil  : (c : PTree E (ExtI E) R) → PTree.force t ≡ sil c → ForceView t
  fv-react : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
            (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
          → PTree.force t ≡ react v τc → ForceView t

force-view : (t : PTree E (ExtI E) R) → ForceView t
force-view t with PTree.force t in eq
... | ret r     = fv-ret r eq
... | sil c     = fv-sil c eq
... | react v τc = fv-react v τc eq

-- classify a refusing P′>>X by the force of P′ (terminated ⇒ X refuses; stable react ⇒
-- cont-independent refusal).
bind-Refuses-class : (P′ : PTree E (ExtI E) R) (X : PTree E (ExtI E) S)
                     {ℓx : Level} {B : Event√ S → Set ℓx}
                   → Refuses (P′ >> X) B
                   → (Σ[ r ∈ R ] (PTree.force P′ ≡ ret r) × Refuses X B)
                   ⊎ (isStable P′ × ((Y : PTree E (ExtI E) S) → Refuses (P′ >> Y) B))
bind-Refuses-class P′ X ref with force-view P′
... | fv-ret r eqP′  = inj₁ (r , eqP′ , Refuses-force-eq X (P′ >> X) (sym (fBind-ret (λ _ → X) P′ eqP′)) ref)
... | fv-sil c eqP′  = ⊥-elim (stable-not-sil {t = P′ >> X} (proj₁ ref) (fBind-sil (λ _ → X) P′ eqP′))
... | fv-react v τc eqP′ = inj₂ (>>-stable-inv P′ X eqP′ (proj₁ ref)
                               , λ Y → >>-Refuses-transfer P′ X Y (>>-stable-inv P′ X eqP′ (proj₁ ref)) ref)

-- the inversion
>>-fail→ : (P : PTree E (ExtI E) R) (X : PTree E (ExtI E) S)
           {s : List (Event√ S)} {ℓx : Level} {B : Event√ S → Set ℓx}
         → failures (P >> X) s B
         → (Σ[ sp ∈ List Event ] Σ[ P′ ∈ PTree E (ExtI E) R ]
              (s ≡ map evl sp) × (P ⟹ₚ⟨ sp ⟩ P′) × isStable P′
              × ((Y : PTree E (ExtI E) S) → Refuses (P′ >> Y) B))
         ⊎ (Σ[ sp ∈ List Event ] Σ[ sx ∈ List (Event√ S) ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
              (s ≡ map evl sp ++ sx) × (P ⟹ₚ⟨ sp ⟩ P′) × (PTree.force P′ ≡ ret r) × failures X sx B)
>>-fail→ P X (W , reach , ref) with >>-reach-inv reach
... | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , xr) =
      inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , (W , xr , ref))
... | inj₁ (sp , P′ , seq , reachp , refl) with bind-Refuses-class P′ X ref
...   | inj₁ (r , fret , refX) =
        inj₂ (sp , [] , P′ , r , trans seq (sym (++-identityʳ _)) , reachp , fret , (X , ⟹-refl , refX))
...   | inj₂ (stP′ , allY) = inj₁ (sp , P′ , seq , reachp , stP′ , allY)

-------------------------------------------------------------------------------------
-- Divergences side.  X-phase intro is constructive; the inversion needs the bind König
-- step `>>-Diverges→` (decide whether an infinite τ-path stays in P or exits to X) —
-- the one targeted classical postulate (cf □-Diverges→ / △-Diverges→).
-------------------------------------------------------------------------------------

-- X-phase intro: P terminates (√-free) then X diverges
>>-div-introX : (P : PTree E (ExtI E) R) (X : PTree E (ExtI E) S) (P′ : PTree E (ExtI E) R)
                {sp : List Event} {sx : List (Event√ S)} {r : R}
              → (P ⟹ₚ⟨ sp ⟩ P′) → (PTree.force P′ ≡ ret r) → divergences X sx
              → divergences (P >> X) (map evl sp ++ sx)
>>-div-introX P X P′ {sp = sp} reachp fret d
  with ⟹-force-transfer (fBind-ret (λ _ → X) P′ fret) (d .IsDivergence.reach)
... | W′ , reachW′ , fW′ = record
      { prefix  = map evl sp ++ d .IsDivergence.prefix
      ; suffix  = d .IsDivergence.suffix
      ; split   = trans (cong (map evl sp ++_) (d .IsDivergence.split))
                        (sym (++-assoc (map evl sp) (d .IsDivergence.prefix) (d .IsDivergence.suffix)))
      ; witness = W′
      ; reach   = ⟹-trans (⟹ₚ→⟹ (>>-liftₚ X reachp)) reachW′
      ; divwit  = Diverges-force-eq fW′ (d .IsDivergence.divwit)
      }

-- the bind König step (classical; CERTIFIED from the single `dne` in ClassicalFromLEM
-- via `>>-no-inf` — a well-founded recursion on DAcc P′, mirroring `□-no-inf`)
postulate
  >>-Diverges→ : {P′ : PTree E (ExtI E) R} {X : PTree E (ExtI E) S}
               → Diverges (P′ >> X)
               → Diverges P′
               ⊎ (Σ[ P″ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
                    (P′ ⟹ₚ⟨ [] ⟩ P″) × (PTree.force P″ ≡ ret r) × Diverges X)

-- divergence inversion: P-phase (continuation-independent, same trace s) or X-phase.
>>-div→ : (P : PTree E (ExtI E) R) (X : PTree E (ExtI E) S) {s : List (Event√ S)}
        → divergences (P >> X) s
        → ((Y : PTree E (ExtI E) S) → divergences (P >> Y) s)
        ⊎ (Σ[ sp ∈ List Event ] Σ[ sx ∈ List (Event√ S) ] Σ[ P′ ∈ PTree E (ExtI E) R ] Σ[ r ∈ R ]
             (s ≡ map evl sp ++ sx) × (P ⟹ₚ⟨ sp ⟩ P′) × (PTree.force P′ ≡ ret r) × divergences X sx)
>>-div→ P X d with >>-reach-inv (d .IsDivergence.reach)
... | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , xr) =
      inj₂ (sp , sx ++ d .IsDivergence.suffix , P′ , r
           , trans (d .IsDivergence.split)
                   (trans (cong (_++ d .IsDivergence.suffix) seq)
                          (++-assoc (map evl sp) sx (d .IsDivergence.suffix)))
           , reachp , fP′
           , record { prefix = sx ; suffix = d .IsDivergence.suffix ; split = refl
                    ; witness = d .IsDivergence.witness ; reach = xr ; divwit = d .IsDivergence.divwit })
... | inj₁ (sp , P′ , seq , reachp , refl) with >>-Diverges→ (d .IsDivergence.divwit)
...   | inj₁ dP′ =
        inj₁ (λ Y → record
          { prefix = map evl sp ; suffix = d .IsDivergence.suffix
          ; split = trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) seq)
          ; witness = P′ >> Y ; reach = ⟹ₚ→⟹ (>>-liftₚ Y reachp) ; divwit = bind-Diverges Y dP′ })
...   | inj₂ (P″ , r , p′reach , fP″ , dX) =
        inj₂ (sp , d .IsDivergence.suffix , P″ , r
             , trans (d .IsDivergence.split) (cong (_++ d .IsDivergence.suffix) seq)
             , subst (λ z → P ⟹ₚ⟨ z ⟩ P″) (++-identityʳ sp) (⟹ₚ-trans reachp p′reach) , fP″
             , div-extension-closed (empty-div dX))

-------------------------------------------------------------------------------------
-- ;-dist-r assembled at ≈FD.
-------------------------------------------------------------------------------------

module _ (P Q R₀ : PTree E (ExtI E) S) where
  private
    LHS = P >> (Q ⊓ R₀)
    RHS = (P >> Q) ⊓ (P >> R₀)

  -- failures⊥ RHS → failures⊥ LHS
  dist-F⊥₁ : LHS ⊇F⊥ RHS
  dist-F⊥₁ (inj₁ f) with ⊓-failures→ (P >> Q) (P >> R₀) f
  ... | inj₁ fPQ with >>-fail→ P Q fPQ
  ...   | inj₁ (sp , P′ , seq , reachp , stP′ , allY) =
          inj₁ (subst (λ z → failures LHS z _) (sym seq) (>>-fail←P P (Q ⊓ R₀) P′ reachp (allY (Q ⊓ R₀))))
  ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , fQ) =
          inj₁ (subst (λ z → failures LHS z _) (sym seq) (>>-fail←X P (Q ⊓ R₀) P′ reachp fP′ (⊓-failures←l Q R₀ fQ)))
  dist-F⊥₁ (inj₁ f) | inj₂ fPR with >>-fail→ P R₀ fPR
  ...   | inj₁ (sp , P′ , seq , reachp , stP′ , allY) =
          inj₁ (subst (λ z → failures LHS z _) (sym seq) (>>-fail←P P (Q ⊓ R₀) P′ reachp (allY (Q ⊓ R₀))))
  ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , fR) =
          inj₁ (subst (λ z → failures LHS z _) (sym seq) (>>-fail←X P (Q ⊓ R₀) P′ reachp fP′ (⊓-failures←r Q R₀ fR)))
  dist-F⊥₁ (inj₂ d) = inj₂ (dist-D₁ d)
    where
      dist-D₁ : divergences RHS _ → divergences LHS _
      dist-D₁ dv with ⊓-div→ (P >> Q) (P >> R₀) dv
      ... | inj₁ dPQ with >>-div→ P Q dPQ
      ...   | inj₁ allY = allY (Q ⊓ R₀)
      ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dQ) =
              subst (divergences LHS) (sym seq) (>>-div-introX P (Q ⊓ R₀) P′ reachp fP′ (⊓-div←l Q R₀ dQ))
      dist-D₁ dv | inj₂ dPR with >>-div→ P R₀ dPR
      ...   | inj₁ allY = allY (Q ⊓ R₀)
      ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dR) =
              subst (divergences LHS) (sym seq) (>>-div-introX P (Q ⊓ R₀) P′ reachp fP′ (⊓-div←r Q R₀ dR))

  -- divergences RHS → divergences LHS
  dist-D₁ : LHS ⊇D RHS
  dist-D₁ dv with ⊓-div→ (P >> Q) (P >> R₀) dv
  ... | inj₁ dPQ with >>-div→ P Q dPQ
  ...   | inj₁ allY = allY (Q ⊓ R₀)
  ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dQ) =
          subst (divergences LHS) (sym seq) (>>-div-introX P (Q ⊓ R₀) P′ reachp fP′ (⊓-div←l Q R₀ dQ))
  dist-D₁ dv | inj₂ dPR with >>-div→ P R₀ dPR
  ...   | inj₁ allY = allY (Q ⊓ R₀)
  ...   | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dR) =
          subst (divergences LHS) (sym seq) (>>-div-introX P (Q ⊓ R₀) P′ reachp fP′ (⊓-div←r Q R₀ dR))

  -- failures⊥ LHS → failures⊥ RHS
  dist-F⊥₂ : RHS ⊇F⊥ LHS
  dist-F⊥₂ (inj₁ f) with >>-fail→ P (Q ⊓ R₀) f
  ... | inj₁ (sp , P′ , seq , reachp , stP′ , allY) =
        inj₁ (⊓-failures←l (P >> Q) (P >> R₀)
               (subst (λ z → failures (P >> Q) z _) (sym seq) (>>-fail←P P Q P′ reachp (allY Q))))
  ... | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , fQR) with ⊓-failures→ Q R₀ fQR
  ...   | inj₁ fQ = inj₁ (⊓-failures←l (P >> Q) (P >> R₀)
                          (subst (λ z → failures (P >> Q) z _) (sym seq) (>>-fail←X P Q P′ reachp fP′ fQ)))
  ...   | inj₂ fR = inj₁ (⊓-failures←r (P >> Q) (P >> R₀)
                          (subst (λ z → failures (P >> R₀) z _) (sym seq) (>>-fail←X P R₀ P′ reachp fP′ fR)))
  dist-F⊥₂ (inj₂ d) = inj₂ (dist-D₂ d)
    where
      dist-D₂ : divergences LHS _ → divergences RHS _
      dist-D₂ dv with >>-div→ P (Q ⊓ R₀) dv
      ... | inj₁ allY = ⊓-div←l (P >> Q) (P >> R₀) (allY Q)
      ... | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dQR) with ⊓-div→ Q R₀ dQR
      ...   | inj₁ dQ = ⊓-div←l (P >> Q) (P >> R₀)
                         (subst (divergences (P >> Q)) (sym seq) (>>-div-introX P Q P′ reachp fP′ dQ))
      ...   | inj₂ dR = ⊓-div←r (P >> Q) (P >> R₀)
                         (subst (divergences (P >> R₀)) (sym seq) (>>-div-introX P R₀ P′ reachp fP′ dR))

  -- divergences LHS → divergences RHS
  dist-D₂ : RHS ⊇D LHS
  dist-D₂ dv with >>-div→ P (Q ⊓ R₀) dv
  ... | inj₁ allY = ⊓-div←l (P >> Q) (P >> R₀) (allY Q)
  ... | inj₂ (sp , sx , P′ , r , seq , reachp , fP′ , dQR) with ⊓-div→ Q R₀ dQR
  ...   | inj₁ dQ = ⊓-div←l (P >> Q) (P >> R₀)
                     (subst (divergences (P >> Q)) (sym seq) (>>-div-introX P Q P′ reachp fP′ dQ))
  ...   | inj₂ dR = ⊓-div←r (P >> Q) (P >> R₀)
                     (subst (divergences (P >> R₀)) (sym seq) (>>-div-introX P R₀ P′ reachp fP′ dR))

  -- ;-dist-r (T6.2):  P ; (Q ⊓ R) ≈FD (P ; Q) ⊓ (P ; R)
  seq-dist-r-FD : LHS ≈FD RHS
  seq-dist-r-FD = (dist-F⊥₁ , dist-D₁) , (dist-F⊥₂ , dist-D₂)
