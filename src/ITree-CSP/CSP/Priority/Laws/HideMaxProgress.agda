{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority Law: Pri ∘ Hide maximal progress (PROVED).
--
-- `Pri_≤ (P ∖ A) ∼ (Pri_≤↑A P) ∖ A`, where `≤↑A` extends the priority order `≤`
-- so that every hidden event `a ∈ A` strictly dominates every NON-maximal event.
-- Intuition: hiding turns A-offers into τ; under `Pri` (maximal progress) an
-- enabled hidden event makes every non-maximal VISIBLE offer redundant — which is
-- exactly what `≤↑A` bakes into the order, letting the prioritisation be done
-- BEFORE hiding.
--
-- This file gives the ORDER EXTENSION (`≤↑A`, a `PriOrder`) AND the commutation
-- bisimulation `pri-hide-maxprog`, discharged by a coinductive STRONG-bisim
-- relation `HR` (mirroring `CSP.Priority.Laws.Cong`'s guarded pattern).
-- `--safe`, 0 postulates, no dne / NON_TERMINATING / sized-types.
--
-- ── SIDE CONDITIONS (settled here) ────────────────────────────────────────────
--  (max) every A-event is ≤-MAXIMAL in the base order.  [⇒ A-events are ≤↑A-
--        maximal AND pairwise incomparable; needed for `<↑A`-irrefl/-trans.]
--  (fin) A is FINITELY ENUMERABLE AS EVENTS: a finite `A-evs : List Ev` listing
--        exactly A's events (sound + complete).  This is the MINIMAL finiteness
--        condition and is STRONGER than "finitely many A-channels": the `PriOrder`
--        interface uses a finite `above : Ev → List Ev` and `dominated?` scans it
--        for VALUE-specific offered dominators, so `above↑A e` must list every
--        A-event that could be offered — hence finite carriers too (a chanSet over
--        an infinite carrier does NOT qualify).  [MATERIAL FINDING — see report.]
------------------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List using (List; []; _∷_; _++_; foldr; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing; is-just)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ; Σ-syntax)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong; cong₂)
open import Function using (case_of_)

open import Process_Trees

module CSP.Priority.Laws.HideMaxProgress {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree

open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base       {ℓ} {ℓe} {E}
open import CSP.Operators      E-≟
open import CSP.Priority.Closure E-≟
open import CSP.Priority.Adequacy {ℓ} {ℓe} {E}
  using ( fPri-ret; fPri-sil; fPri-react
        ; priVisAt-just; priMaxAt-just; priTauAt-just
        ; priVisAt-fires; priMaxAt-fires; priTauAt-fires
        ; isStable-react
        ; no-steps-∼; deadlock-stuck )
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using ( fHide-react; fHide-ret; fHide-sil; fHide-ret-inv
        ; hide-hVis-elim; hide-hTau-elim; hide-emit-elim
        ; hide-hVis-keep-eq; hide-hTau-tag0-eq; hide-hTau-tag1-eq
        ; Hide-τ; Hide-keep; Hide-hidden
        ; HideτR; hτP; hτH; Hide-τ-elim
        ; HideevR; heV; he√; Hide-ev-elim )

------------------------------------------------------------------------
-- The order extension  ≤↑A  (fully proven as a PriOrder).
------------------------------------------------------------------------

module _ {ℓo} (O : PriOrder ℓo) (A : EventSet)
         (A-evs      : List Ev)
         (A-sound    : ∀ {b : Ev} → b ∈ A-evs → A .EventSet.mem (Ev.at b) (Ev.val b))
         (A-complete : ∀ {b : Ev} → A .EventSet.mem (Ev.at b) (Ev.val b) → b ∈ A-evs)
         (A-max      : ∀ {b : Ev} → A .EventSet.mem (Ev.at b) (Ev.val b)
                     → Maximal (PriOrder.prop O) b)
         where

  open PriOrder O using (_<ᵖ_; <ᵖ-irrefl; <ᵖ-trans; above; above-sound; above-complete)

  -- `b` is a hidden (A-)event
  InA : Ev → Set
  InA b = A .EventSet.mem (Ev.at b) (Ev.val b)

  -- extended strict order: base order, OR "f is a hidden event and e is non-maximal"
  _<↑A_ : Ev → Ev → Set (lsuc ℓ ⊔ ℓe ⊔ ℓo)
  e <↑A f = (e <ᵖ f) ⊎ (InA f × (above e ≢ []))

  -- a ≤-maximal event has an empty `above`
  Max→[] : ∀ {e} → Maximal (PriOrder.prop O) e → above e ≡ []
  Max→[] {e} mx with above e in aeq
  ... | []      = refl
  ... | b ∷ bs  = ⊥-elim (mx b (above-sound (subst (b ∈_) (sym aeq) (here refl))))

  -- a dominated event has a non-empty `above`
  <ᵖ→ne : ∀ {e f} → e <ᵖ f → above e ≢ []
  <ᵖ→ne {e} {f} p ae≡[] = case subst (f ∈_) ae≡[] (above-complete p) of λ ()

  <↑A-irrefl : ∀ {e} → ¬ (e <↑A e)
  <↑A-irrefl (inj₁ p)            = <ᵖ-irrefl p
  <↑A-irrefl (inj₂ (ina , ne))   = ne (Max→[] (A-max ina))

  <↑A-trans : ∀ {e f g} → e <↑A f → f <↑A g → e <↑A g
  <↑A-trans (inj₁ p)          (inj₁ q)          = inj₁ (<ᵖ-trans p q)
  <↑A-trans (inj₁ p)          (inj₂ (inaG , _)) = inj₂ (inaG , <ᵖ→ne p)
  <↑A-trans (inj₂ (inaF , _)) (inj₁ q)          = ⊥-elim (A-max inaF _ q)
  <↑A-trans (inj₂ (inaF , _)) (inj₂ (_ , neF))  = ⊥-elim (neF (Max→[] (A-max inaF)))

  -- the A-events added iff `e` is non-maximal (i.e. `above e` non-empty)
  extraA : List Ev → List Ev
  extraA []      = []
  extraA (_ ∷ _) = A-evs

  -- extended dominator enumeration: base dominators ++ (if e non-maximal) the
  -- A-events.  FINITE because `A-evs` is finite (the (fin) side condition).
  above↑A : Ev → List Ev
  above↑A e = above e ++ extraA (above e)

  above↑A-sound : ∀ {e b} → b ∈ above↑A e → e <↑A b
  above↑A-sound {e} {b} b∈ with ∈-++⁻ (above e) b∈
  ... | inj₁ b∈base = inj₁ (above-sound b∈base)
  ... | inj₂ b∈extra with above e
  ...   | []     = case b∈extra of λ ()
  ...   | x ∷ xs = inj₂ (A-sound b∈extra , λ ())

  above↑A-complete : ∀ {e b} → e <↑A b → b ∈ above↑A e
  above↑A-complete {e} {b} (inj₁ p)            = ∈-++⁺ˡ (above-complete p)
  above↑A-complete {e} {b} (inj₂ (inaB , ne)) with above e
  ... | []     = ⊥-elim (ne refl)
  ... | x ∷ xs = ∈-++⁺ʳ (x ∷ xs) (A-complete inaB)

  -- the extended finitary priority order
  ≤↑A : PriOrder (lsuc ℓ ⊔ ℓe ⊔ ℓo)
  ≤↑A = record
    { prop = record { _<ᵖ_ = _<↑A_ ; <ᵖ-irrefl = <↑A-irrefl ; <ᵖ-trans = <↑A-trans }
    ; above = above↑A
    ; above-sound = above↑A-sound
    ; above-complete = above↑A-complete
    }

  ------------------------------------------------------------------------
  -- Pri ∘ Hide commutation:  Pri O (P′ ∖ A) ∼ (Pri ≤↑A P′) ∖ A
  ------------------------------------------------------------------------

  private
    O′ : PriOrder (lsuc ℓ ⊔ ℓe ⊔ ℓo)
    O′ = ≤↑A

  -- a ≤-maximal event has empty ≤↑A-dominators
  above↑A-[] : ∀ {e} → above e ≡ [] → above↑A e ≡ []
  above↑A-[] {e} aeq rewrite aeq = refl

  -- pure boolean/maybe helpers
  null-[] : ∀ {xs : List Ev} → null xs ≡ true → xs ≡ []
  null-[] {[]}    _ = refl
  null-[] {_ ∷ _} ()

  ij-false→∅ : ∀ {ℓr} {R : Set ℓr} {m : Maybe (PTree E (ExtI E) R)}
             → is-just m ≡ false → m ≡ nothing
  ij-false→∅ {m = nothing} _ = refl
  ij-false→∅ {m = just _}  ()

  nothing≢just : ∀ {ℓ'} {X : Set ℓ'} {x : X} → nothing ≡ just x → ⊥
  nothing≢just ()

  -- a boolean that is not `false` is `true`
  notfalse→true : (b : Bool) → (b ≡ false → ⊥) → b ≡ true
  notfalse→true true  _ = refl
  notfalse→true false h = ⊥-elim (h refl)

  -- the domination scan (unfolds `dominated?`: dominated? O v e = domScan v (above e),
  -- dominated? O′ v e = domScan v (above↑A e), both definitionally)
  domScan : ∀ {ℓr} {R : Set ℓr}
              (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → List Ev → Bool
  domScan v = foldr (λ b acc → is-just (v (b .at) (b .val)) ∨ acc) false

  -- scan is a congruence under pointwise is-just equality
  domScan-ij-cong : ∀ {ℓr} {R : Set ℓr}
                      {v w : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  → (∀ b → is-just (v (b .at) (b .val)) ≡ is-just (w (b .at) (b .val)))
                  → (bs : List Ev) → domScan v bs ≡ domScan w bs
  domScan-ij-cong h []       = refl
  domScan-ij-cong h (b ∷ bs) = cong₂ _∨_ (h b) (domScan-ij-cong h bs)

  -- a list of unoffered events scans to false
  domScan-∅ : ∀ {ℓr} {R : Set ℓr}
                {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              (ys : List Ev) → (∀ b → b ∈ ys → is-just (v (b .at) (b .val)) ≡ false)
            → domScan v ys ≡ false
  domScan-∅ []       h = refl
  domScan-∅ (y ∷ ys) h rewrite h y (here refl) = domScan-∅ ys (λ b m → h b (there m))

  -- appending an all-unoffered suffix does not change the scan
  domScan-drop : ∀ {ℓr} {R : Set ℓr}
                   {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                 (xs ys : List Ev) → (∀ b → b ∈ ys → is-just (v (b .at) (b .val)) ≡ false)
               → domScan v (xs ++ ys) ≡ domScan v xs
  domScan-drop         []       ys h = domScan-∅ ys h
  domScan-drop {v = v} (x ∷ xs) ys h =
    cong (is-just (v (x .at) (x .val)) ∨_) (domScan-drop xs ys h)

  -- a single offered member forces the scan to true
  domScan-mem : ∀ {ℓr} {R : Set ℓr}
                  {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                (bs : List Ev) (b : Ev) → b ∈ bs → is-just (v (b .at) (b .val)) ≡ true
              → domScan v bs ≡ true
  domScan-mem {v = v} (b0 ∷ bs) b (here refl) ij = cong (_∨ domScan v bs) ij
  domScan-mem {v = v} (b0 ∷ bs) b (there m)   ij =
    trans (cong (is-just (v (b0 .at) (b0 .val)) ∨_) (domScan-mem bs b m ij)) (∨-zeroʳ _)

  ------------------------------------------------------------------------
  -- Order bridges (all constructive).
  ------------------------------------------------------------------------

  -- (B2) ≤-maximal ⇒ ≤↑A-maximal
  max→max′ : ∀ {e} → isMax? O e ≡ true → isMax? O′ e ≡ true
  max→max′ mx = cong null (above↑A-[] (null-[] mx))

  -- ≤↑A-maximal ⇒ ≤-maximal (always, since above e is a prefix of above↑A e)
  ++-[]ˡ : {xs ys : List Ev} → xs ++ ys ≡ [] → xs ≡ []
  ++-[]ˡ {[]}    _ = refl
  ++-[]ˡ {_ ∷ _} ()

  max′→max : ∀ {e} → isMax? O′ e ≡ true → isMax? O e ≡ true
  max′→max mx′ = cong null (++-[]ˡ (null-[] mx′))

  -- (B3) ≤-maximal ⇒ ≤↑A-undominated
  max→dom′false : ∀ {ℓr} {R : Set ℓr}
                    {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))} {e}
                → isMax? O e ≡ true → dominated? O′ vP e ≡ false
  max→dom′false {vP = vP} mx = cong (domScan vP) (above↑A-[] (null-[] mx))

  -- (B4) a hidden A-event is ≤↑A-maximal and ≤↑A-undominated
  InA→[] : ∀ {b} → InA b → above↑A b ≡ []
  InA→[] ina = above↑A-[] (Max→[] (A-max ina))

  InA→dom′false : ∀ {ℓr} {R : Set ℓr}
                    {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))} {b}
                → InA b → dominated? O′ vP b ≡ false
  InA→dom′false {vP = vP} ina = cong (domScan vP) (InA→[] ina)

  InA→max′ : ∀ {b} → InA b → isMax? O′ b ≡ true
  InA→max′ ina = cong null (InA→[] ina)

  ------------------------------------------------------------------------
  -- Refusal / stability plumbing.  `RefV vP` = "the react node offers no
  -- A-event".  (fin): decidable WITH a witness by scanning A-evs.
  ------------------------------------------------------------------------

  RefV : ∀ {ℓr} {R : Set ℓr}
       → ((at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr)
  RefV vP = ∀ (at : AnyTypes E) (a : proj₁ at) → A .EventSet.mem at a → vP at a ≡ nothing

  -- (B1 pointwise) is-just of the hidden visible map = is-just of vP (given RefV)
  hv-ij : ∀ {ℓr} {R : Set ℓr}
            {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
            {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
        → RefV vP → (b : Ev)
        → is-just (hide-hVis A (react vP τcP) (b .at) (b .val)) ≡ is-just (vP (b .at) (b .val))
  hv-ij {vP = vP} {τcP} refv b with A .EventSet.dec (b .at) (b .val)
  ... | yes p rewrite refv (b .at) (b .val) p = refl
  ... | no ¬p with viewV (react vP τcP) (b .at) (b .val)
  ...   | just P'' = refl
  ...   | nothing  = refl

  -- (B1) the ≤-scan over the hidden map equals the ≤↑A-scan over vP (given RefV)
  dom-hv≡dom′ : ∀ {ℓr} {R : Set ℓr}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → RefV vP → ∀ e
              → dominated? O (hide-hVis A (react vP τcP)) e ≡ dominated? O′ vP e
  dom-hv≡dom′ {vP = vP} refv e =
    trans (domScan-ij-cong (hv-ij refv) (above e))
          (sym (domScan-drop (above e) (extraA (above e)) extra∅))
    where
      extra∅ : ∀ b → b ∈ extraA (above e) → is-just (vP (b .at) (b .val)) ≡ false
      extra∅ b b∈ with above e
      ... | _ ∷ _ = cong is-just (refv (b .at) (b .val) (A-sound b∈))

  -- a non-null list is a cons
  null-false→∷ : ∀ {xs : List Ev} → null xs ≡ false → Σ[ y ∈ Ev ] Σ[ ys ∈ List Ev ] xs ≡ y ∷ ys
  null-false→∷ {[]}     ()
  null-false→∷ {y ∷ ys} _ = y , ys , refl

  -- (fin crux) an offered A-event ≤↑A-dominates every non-maximal event
  notmax→dom′true : ∀ {ℓr} {R : Set ℓr}
                      {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    (b : Ev) → b ∈ A-evs → is-just (vP (b .at) (b .val)) ≡ true
                  → ∀ {e} → isMax? O e ≡ false → dominated? O′ vP e ≡ true
  notmax→dom′true {vP = vP} b b∈ ij {e} nmx with null-false→∷ nmx
  ... | x , xs , aeq = domScan-mem (above↑A e) b b∈above ij
      where b∈above : b ∈ above↑A e
            b∈above rewrite aeq = ∈-++⁺ʳ (x ∷ xs) b∈

  -- P′∖A stable  ⇒  P′ refuses A / P′ stable
  ht∅→RefV : ∀ {ℓr} {R : Set ℓr}
               {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → (∀ i a → hide-hTau A (react vP τcP) i a ≡ nothing) → RefV vP
  ht∅→RefV {vP = vP} {τcP} ht∅ (B , e) a mem with vP (B , e) a in veq
  ... | nothing  = refl
  ... | just P'' = ⊥-elim (nothing≢just
        (trans (sym (ht∅ ((Lift ℓ (Fin 2) × B) , pair fin (base e)) (lift (fsuc fzero) , a)))
               (hide-hTau-tag1-eq A (react vP τcP) mem veq)))

  ht∅→stP : ∀ {ℓr} {R : Set ℓr}
              {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → (∀ i a → hide-hTau A (react vP τcP) i a ≡ nothing)
          → ∀ (j : AnyTypes (ExtI E)) (a : proj₁ j) → τcP j a ≡ nothing
  ht∅→stP {vP = vP} {τcP} ht∅ j a with τcP j a in veq
  ... | nothing  = refl
  ... | just P'' = ⊥-elim (nothing≢just
        (trans (sym (ht∅ ((Lift ℓ (Fin 2) × proj₁ j) , pair fin (proj₂ j)) (lift fzero , a)))
               (hide-hTau-tag0-eq A (react vP τcP) veq)))

  -- the tag1 emitter is empty when P′ refuses A
  hide-emit-∅ : ∀ {ℓr} {R : Set ℓr}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
              → RefV vP → ∀ {B} (i′ : ExtI E B) (a : B) → hide-emit A (react vP τcP) i′ a ≡ nothing
  hide-emit-∅ {vP = vP} {τcP} refv (base e) a with A .EventSet.dec (_ , e) a
  ... | no _  = refl
  ... | yes p with viewV (react vP τcP) (_ , e) a in veq
  ...   | nothing  = refl
  ...   | just P'' = ⊥-elim (nothing≢just (trans (sym (refv (_ , e) a p)) veq))
  hide-emit-∅ refv (pair _ _) a = refl
  hide-emit-∅ refv fin       a = refl

  -- P′ stable + refuses A  ⇒  the hidden τ-map is empty (P′∖A stable)
  hide-stable′ : ∀ {ℓr} {R : Set ℓr}
                   {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
               → (∀ j a → τcP j a ≡ nothing) → RefV vP
               → ∀ i a → hide-hTau A (react vP τcP) i a ≡ nothing
  hide-stable′ {vP = vP} {τcP} hst refv (_ , pair fin i′) (lift fzero , a)
    with viewT (react vP τcP) (_ , i′) a in veq
  ... | nothing  = refl
  ... | just P'' = ⊥-elim (nothing≢just (trans (sym (hst (_ , i′) a)) veq))
  hide-stable′ hst refv (_ , pair fin i′) (lift (fsuc fzero) , a)    = hide-emit-∅ refv i′ a
  hide-stable′ hst refv (_ , pair fin i′) (lift (fsuc (fsuc _)) , a) = refl
  hide-stable′ hst refv (_ , base _)      _ = refl
  hide-stable′ hst refv (_ , fin)         _ = refl
  hide-stable′ hst refv (_ , pair (base _)   _) _ = refl
  hide-stable′ hst refv (_ , pair (pair _ _) _) _ = refl

  -- (fin) decide whether the react node offers an A-event, with a witness
  scanList : ∀ {ℓr} {R : Set ℓr}
               (vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
             (bs : List Ev)
           → (∀ b → b ∈ bs → is-just (vP (b .at) (b .val)) ≡ false)
           ⊎ (Σ[ b ∈ Ev ] (b ∈ bs) × is-just (vP (b .at) (b .val)) ≡ true)
  scanList vP []         = inj₁ (λ b ())
  scanList vP (b0 ∷ bs) with is-just (vP (b0 .at) (b0 .val)) in eqb
  ... | true  = inj₂ (b0 , here refl , eqb)
  ... | false with scanList vP bs
  ...   | inj₁ h            = inj₁ (λ { b (here refl) → eqb ; b (there m) → h b m })
  ...   | inj₂ (b , m , tj) = inj₂ (b , there m , tj)

  allfalse→RefV : ∀ {ℓr} {R : Set ℓr}
                    {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                → (∀ b → b ∈ A-evs → is-just (vP (b .at) (b .val)) ≡ false) → RefV vP
  allfalse→RefV {vP = vP} h (B , e) a mem = ij-false→∅ (h ((B , e) ∙ a) (A-complete mem))

  -- rebuild `isStable` at a react node from the everywhere-nothing τ-branch
  mkStable : ∀ {ℓr} {R : Set ℓr} {P₀ : PTree E (ExtI E) R}
               {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
           → PTree.force P₀ ≡ react vP τcP → (∀ j a → τcP j a ≡ nothing) → isStable P₀
  mkStable {P₀ = P₀} eqf h with PTree.force P₀ | eqf
  ... | react vP τcP | refl = h

  ------------------------------------------------------------------------
  -- RHS-firing helpers (fire an event of P′ through Pri O′, then hide).
  -- Kept separate so the simulation bodies stay shallow (no with-backtracking).
  ------------------------------------------------------------------------

  -- fire P′'s own τ through the (unstable) Pri O′ P′, propagated by hide (tag0)
  fireOwnTauR : ∀ {ℓr} {R : Set ℓr} {P′ : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {j : AnyTypes (ExtI E)} {a' : proj₁ j} {P'' : PTree E (ExtI E) R}
                (fbR : FinBr P′) → PTree.force P′ ≡ react vP τcP → τcP j a' ≡ just P''
              → Σ[ fbR′ ∈ FinBr P'' ] (((Pri O′ P′ fbR) ∖ A) ─[ τ ]─► ((Pri O′ P'' fbR′) ∖ A))
  fireOwnTauR {P′ = P′} {j = j} {a' = a'} {P'' = P''} fbR eqP veqT with fPri-react O′ {t = P′} {fb = fbR} eqP
  ... | inj₁ (stP′ , _ , _) = ⊥-elim (nothing≢just (trans (sym (isStable-react O′ {t = P′} eqP stP′ j a')) veqT))
  ... | inj₂ (¬stP′ , eqfO′ , peqO′) =
        let (eiaO , tfireO) = priTauAt-fires O′ eqfO′ {fb = fbR} {i = j} {a = a'} {t′ = P''} (_) refl veqT
        in FinBr.next fbR (sTau eqfO′ eiaO) , Hide-τ A (Pri O′ P′ fbR) (sTau peqO′ tfireO)

  -- fire an offered A-event through Pri O′ (it is ≤↑A-maximal), hidden as a τ (tag1)
  fireHiddenR : ∀ {ℓr} {R : Set ℓr} {P′ : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {at : AnyTypes E} {a' : proj₁ at} {P'' : PTree E (ExtI E) R}
                (fbR : FinBr P′) → PTree.force P′ ≡ react vP τcP
              → A .EventSet.mem at a' → vP at a' ≡ just P''
              → Σ[ fbR′ ∈ FinBr P'' ] (((Pri O′ P′ fbR) ∖ A) ─[ τ ]─► ((Pri O′ P'' fbR′) ∖ A))
  fireHiddenR {P′ = P′} {vP = vP} {at = at} {a' = a'} {P'' = P''} fbR eqP mem veqV with fPri-react O′ {t = P′} {fb = fbR} eqP
  ... | inj₁ (stP′ , eqfO′ , peqO′) =
        let (eva′ , vfire) = priVisAt-fires O′ eqfO′ {fb = fbR} {at = at} {a = a'} {t′ = P''}
               (dominated? O′ vP (at ∙ a')) refl (vP at a') refl (InA→dom′false mem) veqV
        in FinBr.next fbR (sVis eqfO′ eva′) , Hide-hidden A (Pri O′ P′ fbR) mem (sVis peqO′ vfire)
  ... | inj₂ (¬stP′ , eqfO′ , peqO′) =
        let (eva′ , mfire) = priMaxAt-fires O′ eqfO′ {fb = fbR} {at = at} {a = a'} {t′ = P''}
               (isMax? O′ (at ∙ a')) refl (vP at a') refl (InA→max′ mem) veqV
        in FinBr.next fbR (sVis eqfO′ eva′) , Hide-hidden A (Pri O′ P′ fbR) mem (sVis peqO′ mfire)

  ------------------------------------------------------------------------
  -- LHS-firing helpers (fire an event on `Pri O (P′∖A)`).
  ------------------------------------------------------------------------

  -- (fin crux) LHS unstable but RHS stable: the ≤↑A-undominated non-A offer `e`
  -- (dominated? O′ vP e ≡ false) must be ≤-MAXIMAL — else an offered A-event (found
  -- by scanning A-evs) would ≤↑A-dominate it; and if none is offered, P′∖A would be
  -- stable, contradicting LHS instability.
  crux-max : ∀ {ℓr} {R : Set ℓr}
               {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
               {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))} {e}
             → (∀ j a → τcP j a ≡ nothing)
             → ((∀ i a → hide-hTau A (react vP τcP) i a ≡ nothing) → ⊥)
             → dominated? O′ vP e ≡ false → isMax? O e ≡ true
  crux-max {vP = vP} {e = e} stτ ¬st∖' dom′false with scanList vP A-evs
  ... | inj₁ allfalse = ⊥-elim (¬st∖' (hide-stable′ stτ (allfalse→RefV allfalse)))
  ... | inj₂ (b , b∈ , ijb) =
        notfalse→true (isMax? O e)
          (λ mxf → case trans (sym dom′false) (notmax→dom′true b b∈ ijb mxf) of λ ())

  -- fire a surviving non-A offer on the LHS (priVis O if stable, priMax O if not)
  fireKeepL : ∀ {ℓr} {R : Set ℓr} {P′ : PTree E (ExtI E) R}
                {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                {at : AnyTypes E} {a' : proj₁ at} {P'' : PTree E (ExtI E) R}
              (fbL : FinBr (P′ ∖ A)) → PTree.force P′ ≡ react vP τcP
            → ¬ A .EventSet.mem at a' → vP at a' ≡ just P''
            → (isStable (P′ ∖ A) → dominated? O (hide-hVis A (react vP τcP)) (at ∙ a') ≡ false)
            → (¬ isStable (P′ ∖ A) → isMax? O (at ∙ a') ≡ true)
            → Σ[ fbL′ ∈ FinBr (P'' ∖ A) ]
                ((Pri O (P′ ∖ A) fbL) ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a')) ]─► (Pri O (P'' ∖ A) fbL′))
  fireKeepL {P′ = P′} {vP = vP} {τcP} {at = at} {a' = a'} {P'' = P''} fbL eqP ¬c veqV domf maxf
    with fPri-react O {t = P′ ∖ A} {fb = fbL} (fHide-react A P′ eqP)
  ... | inj₁ (st∖ , eqf1 , peq1) =
        let (eva∖ , vfireL) = priVisAt-fires O eqf1 {fb = fbL} {at = at} {a = a'} {t′ = P'' ∖ A}
              (dominated? O (hide-hVis A (react vP τcP)) (at ∙ a')) refl
              (hide-hVis A (react vP τcP) at a') refl (domf st∖)
              (hide-hVis-keep-eq A (react vP τcP) ¬c veqV)
        in FinBr.next fbL (sVis eqf1 eva∖) , sVis peq1 vfireL
  ... | inj₂ (¬st∖ , eqf1 , peq1) =
        let (eva∖ , mfireL) = priMaxAt-fires O eqf1 {fb = fbL} {at = at} {a = a'} {t′ = P'' ∖ A}
              (isMax? O (at ∙ a')) refl (hide-hVis A (react vP τcP) at a') refl (maxf ¬st∖)
              (hide-hVis-keep-eq A (react vP τcP) ¬c veqV)
        in FinBr.next fbL (sVis eqf1 eva∖) , sVis peq1 mfireL

  -- fire P′'s own τ on the LHS (tag0) — requires P′∖A unstable
  fireOwnTauL : ∀ {ℓr} {R : Set ℓr} {P′ : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {j : AnyTypes (ExtI E)} {a' : proj₁ j} {P'' : PTree E (ExtI E) R}
                (fbL : FinBr (P′ ∖ A)) → PTree.force P′ ≡ react vP τcP → τcP j a' ≡ just P''
              → Σ[ fbL′ ∈ FinBr (P'' ∖ A) ] ((Pri O (P′ ∖ A) fbL) ─[ τ ]─► (Pri O (P'' ∖ A) fbL′))
  fireOwnTauL {P′ = P′} {vP = vP} {τcP} {j = j} {a' = a'} {P'' = P''} fbL eqP veqT
    with fPri-react O {t = P′ ∖ A} {fb = fbL} (fHide-react A P′ eqP)
  ... | inj₁ (st∖ , eqf1 , _) =
        ⊥-elim (nothing≢just (trans (sym (ht∅→stP (isStable-react O {t = P′ ∖ A} eqf1 st∖) j a')) veqT))
  ... | inj₂ (¬st∖ , eqf1 , peq1) =
        let (eiaL , tfireL) = priTauAt-fires O eqf1 {fb = fbL}
              {i = (Lift ℓ (Fin 2) × proj₁ j) , pair fin (proj₂ j)} {a = lift fzero , a'} {t′ = P'' ∖ A}
              (hide-hTau A (react vP τcP) ((Lift ℓ (Fin 2) × proj₁ j) , pair fin (proj₂ j)) (lift fzero , a')) refl
              (hide-hTau-tag0-eq A (react vP τcP) veqT)
        in FinBr.next fbL (sTau eqf1 eiaL) , sTau peq1 tfireL

  -- fire a hidden A-offer on the LHS (tag1) — requires P′∖A unstable
  fireHiddenL : ∀ {ℓr} {R : Set ℓr} {P′ : PTree E (ExtI E) R}
                  {vP : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                  {τcP : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
                  {B : Set ℓ} {e' : E B} {a' : B} {P'' : PTree E (ExtI E) R}
                (fbL : FinBr (P′ ∖ A)) → PTree.force P′ ≡ react vP τcP
              → A .EventSet.mem (B , e') a' → vP (B , e') a' ≡ just P''
              → Σ[ fbL′ ∈ FinBr (P'' ∖ A) ] ((Pri O (P′ ∖ A) fbL) ─[ τ ]─► (Pri O (P'' ∖ A) fbL′))
  fireHiddenL {P′ = P′} {vP = vP} {τcP} {B = B} {e' = e'} {a' = a'} {P'' = P''} fbL eqP mem veqV
    with fPri-react O {t = P′ ∖ A} {fb = fbL} (fHide-react A P′ eqP)
  ... | inj₁ (st∖ , eqf1 , _) =
        ⊥-elim (nothing≢just (trans (sym (ht∅→RefV (isStable-react O {t = P′ ∖ A} eqf1 st∖) (B , e') a' mem)) veqV))
  ... | inj₂ (¬st∖ , eqf1 , peq1) =
        let (eiaL , tfireL) = priTauAt-fires O eqf1 {fb = fbL}
              {i = (Lift ℓ (Fin 2) × B) , pair fin (base e')} {a = lift (fsuc fzero) , a'} {t′ = P'' ∖ A}
              (hide-hTau A (react vP τcP) ((Lift ℓ (Fin 2) × B) , pair fin (base e')) (lift (fsuc fzero) , a')) refl
              (hide-hTau-tag1-eq A (react vP τcP) mem veqV)
        in FinBr.next fbL (sTau eqf1 eiaL) , sTau peq1 tfireL

  ------------------------------------------------------------------------
  -- The strong bisimulation.  `hr` carries P′ + two INDEPENDENT stability
  -- certificates + an equation `L ≡ P′∖A` (so residual targets, which are only
  -- PROPOSITIONALLY of the form _∖A, plug in without `subst` on the corecursion).
  ------------------------------------------------------------------------

  data HR {ℓr} {R : Set ℓr} : PTree E (ExtI E) R → PTree E (ExtI E) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    hr : (P′ : PTree E (ExtI E) R) {L : PTree E (ExtI E) R}
         (eqL : L ≡ P′ ∖ A) (fbL : FinBr L) (fbR : FinBr P′)
       → HR (Pri O L fbL) ((Pri O′ P′ fbR) ∖ A)

  -- forward declarations (corecursion lives in the SSimF bodies, cf. PriCong)
  hr-∼  : ∀ {ℓr} {R : Set ℓr} {X Y : PTree E (ExtI E) R} → HR X Y → X ∼ Y
  hr-∼ˢ : ∀ {ℓr} {R : Set ℓr} {X Y : PTree E (ExtI E) R} → HR X Y → Y ∼ X
  hfwd  : ∀ {ℓr} {R : Set ℓr} (P′ : PTree E (ExtI E) R)
            (fbL : FinBr (P′ ∖ A)) (fbR : FinBr P′)
        → SSimF (Sbisim R) (Pri O (P′ ∖ A) fbL) ((Pri O′ P′ fbR) ∖ A)
  hbwd  : ∀ {ℓr} {R : Set ℓr} (P′ : PTree E (ExtI E) R)
            (fbL : FinBr (P′ ∖ A)) (fbR : FinBr P′)
        → SSimF (Sbisim R) ((Pri O′ P′ fbR) ∖ A) (Pri O (P′ ∖ A) fbL)

  hr-∼  (hr P′ refl fbL fbR) .Sbisim.fwd = hfwd P′ fbL fbR
  hr-∼  (hr P′ refl fbL fbR) .Sbisim.bwd = hbwd P′ fbL fbR
  hr-∼ˢ (hr P′ refl fbL fbR) .Sbisim.fwd = hbwd P′ fbL fbR
  hr-∼ˢ (hr P′ refl fbL fbR) .Sbisim.bwd = hfwd P′ fbL fbR

  ------------------------------------------------------------------------
  -- Forward simulation: LHS `Pri O (P′∖A)` is simulated by RHS `(Pri O′ P′)∖A`.
  ------------------------------------------------------------------------

  -- visible / √
  hfwd P′ fbL fbR .SSimF.on-ev step with PTree.force P′ in eqP
  ... | ret r with step
  ...   | sVis eq _ = case trans (sym (fPri-ret O (fHide-ret A P′ eqP))) eq of λ ()
  ...   | sRet eq0 with trans (sym eq0) (fPri-ret O (fHide-ret A P′ eqP))
  ...     | refl = deadlock , sRet (fHide-ret A (Pri O′ P′ fbR) (fPri-ret O′ eqP)) , sbisim-refl deadlock
  hfwd P′ fbL fbR .SSimF.on-ev step | sil c with step
  ...   | sRet eq   = case trans (sym (proj₂ (fPri-sil O {t = P′ ∖ A} {fb = fbL} (fHide-sil A P′ eqP)))) eq of λ ()
  ...   | sVis eq _ = case trans (sym (proj₂ (fPri-sil O {t = P′ ∖ A} {fb = fbL} (fHide-sil A P′ eqP)))) eq of λ ()
  hfwd P′ fbL fbR .SSimF.on-ev step | react vP τcP
        with fPri-react O {t = P′ ∖ A} {fb = fbL} (fHide-react A P′ eqP)
  -- LHS stable ⇒ P′ stable ∧ refuses A ⇒ RHS stable, priVis matches priVis
  ... | inj₁ (st∖ , eqf1 , peq1) with step
  ...   | sRet eq = case trans (sym peq1) eq of λ ()
  ...   | sVis {at = at} {a = a} eq br
          with priVisAt-just O eqf1 {fb = fbL} (dominated? O (hide-hVis A (react vP τcP)) (at ∙ a)) refl
                 (hide-hVis A (react vP τcP) at a) refl
                 (subst (λ w → w at a ≡ just _) (sym (proj₁ (react-injective (trans (sym peq1) eq)))) br)
  ...     | t′ , dmfalse , eva∖ , refl with hide-hVis-elim A (react vP τcP) eva∖
  ...       | ¬c , P'' , veq , M≡ with fPri-react O′ {t = P′} {fb = fbR} eqP
  ...         | inj₂ (¬stP′ , _ , _) =
                ⊥-elim (¬stP′ (mkStable {P₀ = P′} eqP (ht∅→stP (isStable-react O {t = P′ ∖ A} eqf1 st∖))))
  ...         | inj₁ (stP′ , eqfO′ , peqO′) =
                let (eva′ , vfire) = priVisAt-fires O′ eqfO′ {fb = fbR} {at = at} {a = a} {t′ = P''}
                       (dominated? O′ vP (at ∙ a)) refl (vP at a) refl
                       (trans (sym (dom-hv≡dom′ (ht∅→RefV (isStable-react O {t = P′ ∖ A} eqf1 st∖)) (at ∙ a))) dmfalse)
                       veq
                in (Pri O′ P'' (FinBr.next fbR (sVis eqfO′ eva′)) ∖ A)
                     , Hide-keep A (Pri O′ P′ fbR) ¬c (sVis peqO′ vfire)
                     , hr-∼ (hr P'' M≡ (FinBr.next fbL (sVis eqf1 eva∖)) (FinBr.next fbR (sVis eqfO′ eva′)))
  -- LHS unstable ⇒ priMax; RHS may be stable (case ii) or unstable (case iii)
  hfwd P′ fbL fbR .SSimF.on-ev step | react vP τcP | inj₂ (¬st∖ , eqf1 , peq1) with step
  ...   | sRet eq = case trans (sym peq1) eq of λ ()
  ...   | sVis {at = at} {a = a} eq br
          with priMaxAt-just O eqf1 {fb = fbL} (isMax? O (at ∙ a)) refl
                 (hide-hVis A (react vP τcP) at a) refl
                 (subst (λ w → w at a ≡ just _) (sym (proj₁ (react-injective (trans (sym peq1) eq)))) br)
  ...     | t′ , mxtrue , eva∖ , refl with hide-hVis-elim A (react vP τcP) eva∖
  ...       | ¬c , P'' , veq , M≡ with fPri-react O′ {t = P′} {fb = fbR} eqP
  ...         | inj₁ (stP′ , eqfO′ , peqO′) =
                let (eva′ , vfire) = priVisAt-fires O′ eqfO′ {fb = fbR} {at = at} {a = a} {t′ = P''}
                       (dominated? O′ vP (at ∙ a)) refl (vP at a) refl (max→dom′false mxtrue) veq
                in (Pri O′ P'' (FinBr.next fbR (sVis eqfO′ eva′)) ∖ A)
                     , Hide-keep A (Pri O′ P′ fbR) ¬c (sVis peqO′ vfire)
                     , hr-∼ (hr P'' M≡ (FinBr.next fbL (sVis eqf1 eva∖)) (FinBr.next fbR (sVis eqfO′ eva′)))
  ...         | inj₂ (¬stP′ , eqfO′ , peqO′) =
                let (eva′ , mfire) = priMaxAt-fires O′ eqfO′ {fb = fbR} {at = at} {a = a} {t′ = P''}
                       (isMax? O′ (at ∙ a)) refl (vP at a) refl (max→max′ mxtrue) veq
                in (Pri O′ P'' (FinBr.next fbR (sVis eqfO′ eva′)) ∖ A)
                     , Hide-keep A (Pri O′ P′ fbR) ¬c (sVis peqO′ mfire)
                     , hr-∼ (hr P'' M≡ (FinBr.next fbL (sVis eqf1 eva∖)) (FinBr.next fbR (sVis eqfO′ eva′)))

  -- τ
  hfwd P′ fbL fbR .SSimF.on-tau step with PTree.force P′ in eqP
  ... | ret r with step
  ...   | sSil eq   = case trans (sym (fPri-ret O (fHide-ret A P′ eqP))) eq of λ ()
  ...   | sTau eq _ = case trans (sym (fPri-ret O (fHide-ret A P′ eqP))) eq of λ ()
  hfwd P′ fbL fbR .SSimF.on-tau step | sil c
        with fPri-sil O {t = P′ ∖ A} {fb = fbL} (fHide-sil A P′ eqP)
           | fPri-sil O′ {t = P′} {fb = fbR} eqP | step
  ...   | eqf , peqL | eqfO , peqO | sTau eq _ = case trans (sym peqL) eq of λ ()
  ...   | eqf , peqL | eqfO , peqO | sSil eq with sil-injective (trans (sym peqL) eq)
  ...     | refl =
            ((Pri O′ c (FinBr.next fbR (sSil eqfO))) ∖ A)
              , sSil (fHide-sil A (Pri O′ P′ fbR) peqO)
              , hr-∼ (hr c refl (FinBr.next fbL (sSil eqf)) (FinBr.next fbR (sSil eqfO)))
  hfwd P′ fbL fbR .SSimF.on-tau step | react vP τcP
        with fPri-react O {t = P′ ∖ A} {fb = fbL} (fHide-react A P′ eqP)
  -- LHS stable ⇒ no τ
  ... | inj₁ (st∖ , eqf1 , peq1) with step
  ...   | sSil eq = case trans (sym peq1) eq of λ ()
  ...   | sTau {i = i} {a = a} eq br =
          case subst (λ w → w i a ≡ just _) (sym (proj₂ (react-injective (trans (sym peq1) eq)))) br of λ ()
  -- LHS unstable ⇒ priTau; τ is P′'s own τ (tag0) or a hidden A-event (tag1)
  hfwd P′ fbL fbR .SSimF.on-tau step | react vP τcP | inj₂ (¬st∖ , eqf1 , peq1) with step
  ...   | sSil eq = case trans (sym peq1) eq of λ ()
  ...   | sTau {i = i} {a = a} eq br
          with priTauAt-just O eqf1 {fb = fbL} {i = i} {a = a}
                 (hide-hTau A (react vP τcP) i a) refl
                 (subst (λ w → w i a ≡ just _) (sym (proj₂ (react-injective (trans (sym peq1) eq)))) br)
  ...     | t′ , eia∖ , refl with hide-hTau-elim A (react vP τcP) {i = i} {a = a} eia∖
  ...       | inj₁ (j , a' , P'' , veqT , M≡) =
              let r = fireOwnTauR fbR eqP veqT
              in (Pri O′ P'' (proj₁ r) ∖ A) , proj₂ r
                   , hr-∼ (hr P'' M≡ (FinBr.next fbL (sTau eqf1 eia∖)) (proj₁ r))
  ...       | inj₂ (at , a' , P'' , mem , veqV , M≡) =
              let r = fireHiddenR fbR eqP mem veqV
              in (Pri O′ P'' (proj₁ r) ∖ A) , proj₂ r
                   , hr-∼ (hr P'' M≡ (FinBr.next fbL (sTau eqf1 eia∖)) (proj₁ r))

  ------------------------------------------------------------------------
  -- Backward simulation: RHS `(Pri O′ P′)∖A` is simulated by LHS.
  ------------------------------------------------------------------------

  -- visible / √
  hbwd P′ fbL fbR .SSimF.on-ev step with PTree.force P′ in eqP
  ... | ret r with step
  ...   | sVis eq _ = case trans (sym (fHide-ret A (Pri O′ P′ fbR) (fPri-ret O′ eqP))) eq of λ ()
  ...   | sRet eq0 with trans (sym eq0) (fHide-ret A (Pri O′ P′ fbR) (fPri-ret O′ eqP))
  ...     | refl = deadlock , sRet (fPri-ret O (fHide-ret A P′ eqP)) , sbisim-refl deadlock
  hbwd P′ fbL fbR .SSimF.on-ev step | sil c with step
  ...   | sRet eq   = case trans (sym (fHide-sil A (Pri O′ P′ fbR) (proj₂ (fPri-sil O′ {t = P′} {fb = fbR} eqP)))) eq of λ ()
  ...   | sVis eq _ = case trans (sym (fHide-sil A (Pri O′ P′ fbR) (proj₂ (fPri-sil O′ {t = P′} {fb = fbR} eqP)))) eq of λ ()
  hbwd P′ fbL fbR .SSimF.on-ev step | react vP τcP with Hide-ev-elim A (Pri O′ P′ fbR) step
  ... | he√ eqRet with fPri-react O′ {t = P′} {fb = fbR} eqP
  ...   | inj₁ (_ , _ , peqO′) = case trans (sym peqO′) eqRet of λ ()
  ...   | inj₂ (_ , _ , peqO′) = case trans (sym peqO′) eqRet of λ ()
  hbwd P′ fbL fbR .SSimF.on-ev step | react vP τcP | heV {B = B} {e = e'} {a = a'} P₂ ¬c Pev
        with ev-inv Pev | fPri-react O′ {t = P′} {fb = fbR} eqP
  ...   | V' , T' , eqfp , brp | inj₁ (stP′ , eqfO′ , peqO′)
          with priVisAt-just O′ eqfO′ {fb = fbR} {at = B , e'} {a = a'}
                 (dominated? O′ vP ((B , e') ∙ a')) refl (vP (B , e') a') refl
                 (subst (λ w → w (B , e') a' ≡ just _) (sym (proj₁ (react-injective (trans (sym peqO′) eqfp)))) brp)
  ...     | P'' , dom′false , eva' , refl =
            let (fbL′ , lstep) = fireKeepL fbL eqP ¬c eva'
                  (λ st∖ → trans (dom-hv≡dom′ (ht∅→RefV (isStable-react O {t = P′ ∖ A} (fHide-react A P′ eqP) st∖)) ((B , e') ∙ a')) dom′false)
                  (λ ¬st∖ → crux-max (isStable-react O′ {t = P′} eqP stP′)
                              (λ h → ¬st∖ (mkStable {P₀ = P′ ∖ A} (fHide-react A P′ eqP) h)) dom′false)
            in (Pri O (P'' ∖ A) fbL′) , lstep
                 , hr-∼ˢ (hr P'' refl fbL′ (FinBr.next fbR (sVis eqfO′ eva')))
  hbwd P′ fbL fbR .SSimF.on-ev step | react vP τcP | heV {B = B} {e = e'} {a = a'} P₂ ¬c Pev
        | V' , T' , eqfp , brp | inj₂ (¬stP′ , eqfO′ , peqO′)
        with priMaxAt-just O′ eqfO′ {fb = fbR} {at = B , e'} {a = a'}
               (isMax? O′ ((B , e') ∙ a')) refl (vP (B , e') a') refl
               (subst (λ w → w (B , e') a' ≡ just _) (sym (proj₁ (react-injective (trans (sym peqO′) eqfp)))) brp)
  ... | P'' , mxtrue′ , eva' , refl =
        let (fbL′ , lstep) = fireKeepL fbL eqP ¬c eva'
              (λ st∖ → ⊥-elim (¬stP′ (mkStable {P₀ = P′} eqP (ht∅→stP (isStable-react O {t = P′ ∖ A} (fHide-react A P′ eqP) st∖)))))
              (λ ¬st∖ → max′→max mxtrue′)
        in (Pri O (P'' ∖ A) fbL′) , lstep
             , hr-∼ˢ (hr P'' refl fbL′ (FinBr.next fbR (sVis eqfO′ eva')))

  -- τ
  hbwd P′ fbL fbR .SSimF.on-tau step with PTree.force P′ in eqP
  ... | ret r with step
  ...   | sSil eq   = case trans (sym (fHide-ret A (Pri O′ P′ fbR) (fPri-ret O′ eqP))) eq of λ ()
  ...   | sTau eq _ = case trans (sym (fHide-ret A (Pri O′ P′ fbR) (fPri-ret O′ eqP))) eq of λ ()
  hbwd P′ fbL fbR .SSimF.on-tau step | sil c
        with fPri-sil O′ {t = P′} {fb = fbR} eqP | fPri-sil O {t = P′ ∖ A} {fb = fbL} (fHide-sil A P′ eqP) | step
  ...   | eqfO , peqO | eqf , peqL | sTau eq _ = case trans (sym (fHide-sil A (Pri O′ P′ fbR) peqO)) eq of λ ()
  ...   | eqfO , peqO | eqf , peqL | sSil eq with sil-injective (trans (sym (fHide-sil A (Pri O′ P′ fbR) peqO)) eq)
  ...     | refl =
            (Pri O (c ∖ A) (FinBr.next fbL (sSil eqf))) , sSil peqL
              , hr-∼ˢ (hr c refl (FinBr.next fbL (sSil eqf)) (FinBr.next fbR (sSil eqfO)))
  hbwd P′ fbL fbR .SSimF.on-tau step | react vP τcP with Hide-τ-elim A (Pri O′ P′ fbR) step
  ... | hτP P₂ Pτ refl with τ-inv Pτ | fPri-react O′ {t = P′} {fb = fbR} eqP
  ...   | inj₁ sileq | inj₁ (_ , _ , peqO′) = case trans (sym peqO′) sileq of λ ()
  ...   | inj₁ sileq | inj₂ (_ , _ , peqO′) = case trans (sym peqO′) sileq of λ ()
  ...   | inj₂ (V' , T' , i' , a' , feq , teq) | inj₁ (stP′ , eqfO′ , peqO′) =
          case subst (λ w → w i' a' ≡ just _) (proj₂ (react-injective (trans (sym feq) peqO′))) teq of λ ()
  ...   | inj₂ (V' , T' , i' , a' , feq , teq) | inj₂ (¬stP′ , eqfO′ , peqO′)
          with priTauAt-just O′ eqfO′ {fb = fbR} {i = i'} {a = a'} (τcP i' a') refl
                 (subst (λ w → w i' a' ≡ just _) (proj₂ (react-injective (trans (sym feq) peqO′))) teq)
  ...     | P'' , eia' , refl =
            let (fbL′ , lstep) = fireOwnTauL fbL eqP eia'
            in (Pri O (P'' ∖ A) fbL′) , lstep
                 , hr-∼ˢ (hr P'' refl fbL′ (FinBr.next fbR (sTau eqfO′ eia')))
  hbwd P′ fbL fbR .SSimF.on-tau step | react vP τcP | hτH {B = B} {e = e'} {a = a'} P₂ mem Pev refl
        with ev-inv Pev | fPri-react O′ {t = P′} {fb = fbR} eqP
  ...   | V' , T' , eqfp , brp | inj₁ (stP′ , eqfO′ , peqO′)
          with priVisAt-just O′ eqfO′ {fb = fbR} {at = B , e'} {a = a'}
                 (dominated? O′ vP ((B , e') ∙ a')) refl (vP (B , e') a') refl
                 (subst (λ w → w (B , e') a' ≡ just _) (sym (proj₁ (react-injective (trans (sym peqO′) eqfp)))) brp)
  ...     | P'' , _ , eva' , refl =
            let (fbL′ , lstep) = fireHiddenL fbL eqP mem eva'
            in (Pri O (P'' ∖ A) fbL′) , lstep
                 , hr-∼ˢ (hr P'' refl fbL′ (FinBr.next fbR (sVis eqfO′ eva')))
  hbwd P′ fbL fbR .SSimF.on-tau step | react vP τcP | hτH {B = B} {e = e'} {a = a'} P₂ mem Pev refl
        | V' , T' , eqfp , brp | inj₂ (¬stP′ , eqfO′ , peqO′)
        with priMaxAt-just O′ eqfO′ {fb = fbR} {at = B , e'} {a = a'}
               (isMax? O′ ((B , e') ∙ a')) refl (vP (B , e') a') refl
               (subst (λ w → w (B , e') a' ≡ just _) (sym (proj₁ (react-injective (trans (sym peqO′) eqfp)))) brp)
  ... | P'' , _ , eva' , refl =
        let (fbL′ , lstep) = fireHiddenL fbL eqP mem eva'
        in (Pri O (P'' ∖ A) fbL′) , lstep
             , hr-∼ˢ (hr P'' refl fbL′ (FinBr.next fbR (sVis eqfO′ eva')))

  ------------------------------------------------------------------------
  -- The general commutation, and its instance = the theorem below.
  ------------------------------------------------------------------------
  pri-hide-maxprog-gen : ∀ {ℓr} {R : Set ℓr} (P′ : PTree E (ExtI E) R)
                           (fbL : FinBr (P′ ∖ A)) (fbR : FinBr P′)
                       → Pri O (P′ ∖ A) fbL ∼ ((Pri ≤↑A P′ fbR) ∖ A)
  pri-hide-maxprog-gen P′ fbL fbR = hr-∼ (hr P′ refl fbL fbR)

-- SANITY (concrete): `≤↑A` constructs for a concrete order + hidden set (the
-- empty hidden set over the trivial order).  The intended "a<b, A hides the
-- ≤-maximal channel b" case is covered by the GENERAL proofs above: with
-- A = {b}, b ≤-maximal, `A-evs = [b∙_]` finite, all three side conditions hold,
-- and `≤↑A` adds exactly "b dominates every non-maximal event".
sanity-≤↑A : PriOrder (lsuc ℓ ⊔ ℓe)
sanity-≤↑A = ≤↑A emptyPO ∅ES [] (λ ()) (λ ()) (λ ())

------------------------------------------------------------------------
-- The commutation law.  STRONG bisim `_∼_` (Semantics.Bisim): hiding +
-- prioritisation on both sides yield the SAME τ-branches (P's τs + all offered
-- A-events-as-τ) and the SAME surviving visible offers (the ≤-maximal non-A
-- offers), so strong (not merely weak) bisimilarity holds.  PROVED (0 postulates,
-- no dne / NON_TERMINATING) via the coinductive `HR` bisimulation above, using
-- (max) for A-events surviving `Pri ≤↑A` and (fin) for the decidable A-offer
-- witness in the backward direction.
------------------------------------------------------------------------

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) (A : EventSet)
         (A-evs      : List Ev)
         (A-sound    : ∀ {b : Ev} → b ∈ A-evs → A .EventSet.mem (Ev.at b) (Ev.val b))
         (A-complete : ∀ {b : Ev} → A .EventSet.mem (Ev.at b) (Ev.val b) → b ∈ A-evs)
         (A-max      : ∀ {b : Ev} → A .EventSet.mem (Ev.at b) (Ev.val b)
                     → Maximal (PriOrder.prop O) b)
         (P : PTree E (ExtI E) R) (ar : ARefusal A P) (fbP : FinBr P)
         where

  -- LHS uses the caller's `ARefusal` (= StabDec (P ∖ A)) via `finBr-∖`; RHS uses
  -- the SAME `fbP : FinBr P` under the extended order `≤↑A`, then hides `A`.
  pri-hide-maxprog :
    Pri O (P ∖ A) (finBr-∖ ar fbP)
      ∼ ((Pri (≤↑A O A A-evs A-sound A-complete A-max) P fbP) ∖ A)
  pri-hide-maxprog =
    pri-hide-maxprog-gen O A A-evs A-sound A-complete A-max P (finBr-∖ ar fbP) fbP
