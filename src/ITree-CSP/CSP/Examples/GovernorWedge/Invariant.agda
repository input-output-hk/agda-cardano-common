{-# OPTIONS --guardedness #-}

-- Reachable-state invariant of the own-mux modes (spec v2 §5). Under fix #2
-- (CarryMux) every awaited mux is terminal, so no reachable state is wedged and
-- `promote` is always reachable within two steps. Under CarryMuxId the identity check
-- additionally keeps every active incarnation's entry (no orphaning step). `GoodO`
-- and `goodO-step` are generic over every mode with `enqP ≡ own` (FullFix reuses them).
-- The v1 claim N1 is false on the v2 model; its refutation is `FieldPath.notN1`.
module CSP.Examples.GovernorWedge.Invariant where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; _≤_; _<_; _≟_)
open import Data.Nat.Properties using (≤-refl; <-≤-trans; <-irrefl; <⇒≢; m<n⇒m<1+n; n<1+n; n≤1+n)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupAny)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AP
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import Process_Trees
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import CSP.Examples.GovernorWedge.Wedged using (stopped-conn)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; traces)

-- F2: under fix #2 every awaited mux is terminal
F2-safe : ∀ {c g} → Reach CarryMux c g → ∀ r → gphase g ≡ await r → r ∈ ran c
-- F2: from every reachable state promote, or stopped r then promote, is a trace
F2-live : ∀ {c g} → Reach CarryMux c g
        → (Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps CarryMux c g (GV promote ∷ []) c′ g′)
        ⊎ (Σ[ r ∈ ℕ ] Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps CarryMux c g (ST r ∷ GV promote ∷ []) c′ g′)
-- F2 at process level
F2-live-sys : ∀ {s W} → Sys CarryMux ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
-- F2id: the same two claims under CarryMuxId
F2id-safe : ∀ {c g} → Reach CarryMuxId c g → ∀ r → gphase g ≡ await r → r ∈ ran c
-- F2id liveness at process level
F2id-live-sys : ∀ {s W} → Sys CarryMuxId ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
-- F2id: no reachable orphaning step
F2id-no-orphan : ∀ {c g} → Reach CarryMuxId c g → ∀ at a → ¬ OrphanStep CarryMuxId c g at a

------------------------------------------------------------------------
-- The invariant

-- a queue item's invariant: NewConnection ids are below next, awaited refs terminal, no payload-free item
QOK : CState → Item → Set
QOK c (nc k) = k < next c
QOK c (mf v) = v ∈ ran c
QOK c mfK    = ⊥

-- live incarnation ids are pairwise distinct (movePh/freeIt/closeIt stop at the first id match)
Uniq : List Inc → Set
Uniq = AllPairs (λ i j → iid i ≢ iid j)

-- a live incarnation whose mux can still run
Runs : Inc → Set
Runs i = iph i ≡ hsd ⊎ iph i ≡ running

-- a live incarnation whose mux is not terminal: it can still run, or the IG released it (same shape as LiveMux)
MuxAlive : Inc → Set
MuxAlive i = iph i ≡ hsd ⊎ iph i ≡ running ⊎ iph i ≡ released

-- the Conn half of the invariant (run-out: a released mux is not yet terminal either; failed-in: a failedT mux is terminal too)
record CInv (c : CState) : Set where
  field
    failed-in : All (λ i → iph i ≡ failed ⊎ iph i ≡ failedT → iid i ∈ ran c) (live c)
    run-out   : All (λ i → MuxAlive i → iid i ∉ ran c) (live c)
    fresh     : All (λ i → iid i < next c) (live c)
    ran-fresh : All (_< next c) (ran c)
    uniq      : Uniq (live c)
open CInv public

-- invariant of the own-mux modes (fix #2 and its refinements)
record GoodO (c : CState) (g : GState) : Set where
  field
    cinv     : CInv c
    queue-ok : All (QOK c) (queue g)
    await-ok : ∀ r → gphase g ≡ await r → r ∈ ran c
open GoodO public

-- the initial state satisfies the invariant
goodO₀ : GoodO c₀ g₀
goodO₀ = record { cinv = record { failed-in = [] ; run-out = [] ; fresh = [] ; ran-fresh = [] ; uniq = [] }
                ; queue-ok = [] ; await-ok = λ _ () }

------------------------------------------------------------------------
-- Live-list lemmas

-- a phase move keeps All Q when Q survives the move of the moved incarnation
movePh-all : ∀ {Q : Inc → Set} {r p p′ is is′} → movePh r p p′ is ≡ just is′ → All Q is
           → (∀ f → Q (mkInc r p f) → Q (mkInc r p′ f)) → All Q is′
movePh-all {is = []} () _ _
movePh-all {r = r} {p} {p′} {mkInc x ph f ∷ xs} eq (qx ∷ qs) tr with r ≟ x | ph ≟ᴾ p | eq
... | yes refl | yes refl | refl = tr f qx ∷ qs
... | yes _ | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
...   | _ , eq₁ , refl = qx ∷ movePh-all eq₁ qs tr
movePh-all {r = r} {p} {p′} {mkInc x ph f ∷ xs} eq (qx ∷ qs) tr | no _ | _ | eq′
  with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
... | _ , eq₁ , refl = qx ∷ movePh-all eq₁ qs tr

-- a trace's move (failed or failedT → closing) keeps All Q when Q survives the traced incarnation becoming closing
trace-all : ∀ {Q : Inc → Set} {r is is′} → (movePh r failed closing is <∣> movePh r failedT closing is) ≡ just is′ → All Q is
          → (∀ {p} f → Q (mkInc r p f) → Q (mkInc r closing f)) → All Q is′
trace-all {r = r} {is} eq qs tr with alt-split {x = movePh r failed closing is} eq
... | inj₁ eq₁ = movePh-all eq₁ qs tr
... | inj₂ eq₁ = movePh-all eq₁ qs tr

-- a successful phase move found r live in phase p
movePh-any : ∀ {r p p′ is is′} → movePh r p p′ is ≡ just is′ → Any (λ i → iid i ≡ r × iph i ≡ p) is
movePh-any {is = []} ()
movePh-any {r} {p} {p′} {mkInc x ph f ∷ xs} eq with r ≟ x | ph ≟ᴾ p | eq
... | yes refl | yes refl | _ = here (refl , refl)
... | yes _ | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
...   | _ , eq₁ , _ = there (movePh-any eq₁)
movePh-any {r} {p} {p′} {mkInc x ph f ∷ xs} eq | no _ | _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
... | _ , eq₁ , _ = there (movePh-any eq₁)

-- a phase move keeps the ids distinct
movePh-uniq : ∀ {r p p′ is is′} → movePh r p p′ is ≡ just is′ → Uniq is → Uniq is′
movePh-uniq {is = []} ()
movePh-uniq {r} {p} {p′} {mkInc x ph f ∷ xs} eq (px ∷ u) with r ≟ x | ph ≟ᴾ p | eq
... | yes _ | yes _ | refl = px ∷ u
... | yes _ | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
...   | _ , eq₁ , refl = movePh-all eq₁ px (λ _ q → q) ∷ movePh-uniq eq₁ u
movePh-uniq {r} {p} {p′} {mkInc x ph f ∷ xs} eq (px ∷ u) | no _ | _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
... | _ , eq₁ , refl = movePh-all eq₁ px (λ _ q → q) ∷ movePh-uniq eq₁ u

-- with distinct ids, after a phase move only the moved incarnation (now in p′) has id r
movePh-others : ∀ {r p p′ is is′} → movePh r p p′ is ≡ just is′ → Uniq is → All (λ i → iph i ≢ p′ → iid i ≢ r) is′
movePh-others {is = []} ()
movePh-others {r} {p} {p′} {mkInc x ph f ∷ xs} eq (px ∷ u) with r ≟ x | ph ≟ᴾ p | eq
... | yes refl | yes refl | refl = (λ ne → ⊥-elim (ne refl)) ∷ All.map (λ x≢j _ j≡x → x≢j (sym j≡x)) px
... | yes refl | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
...   | _ , eq₁ , refl = ⊥-elim (let (ne , e , _) = lookupAny px (movePh-any eq₁) in ne (sym e))
movePh-others {r} {p} {p′} {mkInc x ph f ∷ xs} eq (px ∷ u) | no r≢x | _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = movePh r p p′ xs} eq′
... | _ , eq₁ , refl = (λ _ x≡r → r≢x (sym x≡r)) ∷ movePh-others eq₁ u

-- a peer reset keeps All Q when Q survives setting the freed flag
freeIt-all : ∀ {Q : Inc → Set} {r is is′} → freeIt r is ≡ just is′ → All Q is
           → (∀ {x ph} → Q (mkInc x ph false) → Q (mkInc x ph true)) → All Q is′
freeIt-all {is = []} () _ _
freeIt-all {r = r} {mkInc x ph f ∷ xs} eq (qx ∷ qs) tr with r ≟ x | eq
... | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = freeIt r xs} eq′
...   | _ , eq₁ , refl = qx ∷ freeIt-all eq₁ qs tr
freeIt-all {r = r} {mkInc x ph f ∷ xs} eq (qx ∷ qs) tr | yes _ | eq′ with ph | f | eq′
... | hsd     | false | refl = tr qx ∷ qs
... | running | false | refl = tr qx ∷ qs
... | released | false | refl = tr qx ∷ qs
... | hsd     | true  | ()
... | running | true  | ()
... | released | true | ()
... | failed  | _     | ()
... | closing | _     | ()
... | failedT | _     | ()

-- a peer reset keeps the ids distinct
freeIt-uniq : ∀ {r is is′} → freeIt r is ≡ just is′ → Uniq is → Uniq is′
freeIt-uniq {is = []} ()
freeIt-uniq {r} {mkInc x ph f ∷ xs} eq (px ∷ u) with r ≟ x | eq
... | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = freeIt r xs} eq′
...   | _ , eq₁ , refl = freeIt-all eq₁ px (λ q → q) ∷ freeIt-uniq eq₁ u
freeIt-uniq {r} {mkInc x ph f ∷ xs} eq (px ∷ u) | yes _ | eq′ with ph | f | eq′
... | hsd     | false | refl = px ∷ u
... | running | false | refl = px ∷ u
... | released | false | refl = px ∷ u
... | hsd     | true  | ()
... | running | true  | ()
... | released | true | ()
... | failed  | _     | ()
... | closing | _     | ()
... | failedT | _     | ()

-- closing removes one incarnation, so it keeps All Q
closeIt-all : ∀ {Q : Inc → Set} {r is is′} → closeIt r is ≡ just is′ → All Q is → All Q is′
closeIt-all {is = []} ()
closeIt-all {r = r} {mkInc x ph f ∷ xs} eq (qx ∷ qs) with r ≟ x | ph ≟ᴾ closing | eq
... | yes _ | yes _ | refl = qs
... | yes _ | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = closeIt r xs} eq′
...   | _ , eq₁ , refl = qx ∷ closeIt-all eq₁ qs
closeIt-all {r = r} {mkInc x ph f ∷ xs} eq (qx ∷ qs) | no _ | _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = closeIt r xs} eq′
... | _ , eq₁ , refl = qx ∷ closeIt-all eq₁ qs

-- closing keeps the ids distinct
closeIt-uniq : ∀ {r is is′} → closeIt r is ≡ just is′ → Uniq is → Uniq is′
closeIt-uniq {is = []} ()
closeIt-uniq {r} {mkInc x ph f ∷ xs} eq (px ∷ u) with r ≟ x | ph ≟ᴾ closing | eq
... | yes _ | yes _ | refl = u
... | yes _ | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = closeIt r xs} eq′
...   | _ , eq₁ , refl = closeIt-all eq₁ px ∷ closeIt-uniq eq₁ u
closeIt-uniq {r} {mkInc x ph f ∷ xs} eq (px ∷ u) | no _ | _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = closeIt r xs} eq′
... | _ , eq₁ , refl = closeIt-all eq₁ px ∷ closeIt-uniq eq₁ u

------------------------------------------------------------------------
-- Conn-side preservation

-- what a Conn move gives the IG half: next and ran only grow
CMono : CState → CState → Set
CMono c c′ = next c ≤ next c′ × (∀ {x} → x ∈ ran c → x ∈ ran c′)

-- an alive phase is neither failed nor failedT
runs≢dead : ∀ {p q} → p ≡ hsd ⊎ p ≡ running ⊎ p ≡ released → q ≡ failed ⊎ q ≡ failedT → p ≢ q
runs≢dead (inj₁ refl)        (inj₁ refl) ()
runs≢dead (inj₁ refl)        (inj₂ refl) ()
runs≢dead (inj₂ (inj₁ refl)) (inj₁ refl) ()
runs≢dead (inj₂ (inj₁ refl)) (inj₂ refl) ()
runs≢dead (inj₂ (inj₂ refl)) (inj₁ refl) ()
runs≢dead (inj₂ (inj₂ refl)) (inj₂ refl) ()

-- a phase move keeps CInv if the target is failed or failedT / alive only when the source was
mv-inv : ∀ {k p p′ n is is′ ts} → (p′ ≡ failed ⊎ p′ ≡ failedT → p ≡ failed ⊎ p ≡ failedT)
       → (p′ ≡ hsd ⊎ p′ ≡ running ⊎ p′ ≡ released → p ≡ hsd ⊎ p ≡ running ⊎ p ≡ released)
       → movePh k p p′ is ≡ just is′ → CInv (cst n is ts) → CInv (cst n is′ ts)
mv-inv h₁ h₂ eq ci = record
  { failed-in = movePh-all eq (failed-in ci) (λ _ q e → q (h₁ e))
  ; run-out   = movePh-all eq (run-out ci) (λ _ q e → q (h₂ e))
  ; fresh     = movePh-all eq (fresh ci) (λ _ q → q)
  ; ran-fresh = ran-fresh ci
  ; uniq      = movePh-uniq eq (uniq ci) }

-- a fail move from phase p (running or released) to a terminal phase p′ (failed or failedT) keeps CInv, with k now in ran
fail-inv : ∀ {k p p′ n is is′ ts} → p′ ≡ failed ⊎ p′ ≡ failedT → movePh k p p′ is ≡ just is′ → CInv (cst n is ts) → CInv (cst n is′ (k ∷ ts))
fail-inv {n = n} d eq₁ ci = record
  { failed-in = movePh-all eq₁ (All.map (λ q e → there (q e)) (failed-in ci)) (λ _ _ _ → here refl)
  ; run-out   = All.zipWith (λ (q , o) h → λ { (here e) → o (runs≢dead h d) e ; (there p) → q h p })
                  ( movePh-all eq₁ (run-out ci) (λ _ _ h → ⊥-elim (runs≢dead h d refl))
                  , movePh-others eq₁ (uniq ci) )
  ; fresh     = movePh-all eq₁ (fresh ci) (λ _ q → q)
  ; ran-fresh = (let (lt , e , _) = lookupAny (fresh ci) (movePh-any eq₁) in subst (_< n) e lt) ∷ ran-fresh ci
  ; uniq      = movePh-uniq eq₁ (uniq ci) }

-- every Conn move keeps CInv and is monotone, under any CM policy
conn-good : ∀ {at a c c′ pol} → cstep at a pol c ≡ just c′ → CInv c → CInv c′ × CMono c c′
conn-good {_ , gov} ()
conn-good {_ , stopped} {t} {cst _ _ ts} eq ci with t ∈? ts | eq
... | yes _ | refl = ci , ≤-refl , λ p → p
... | no _  | ()
conn-good {_ , hs} {r} {cst n is ts} {pol = pol} eq ci with r ≟ n | admitOK pol is | eq
... | yes refl | true | refl =
      record { failed-in = ∷ʳ⁺ (failed-in ci) (λ { (inj₁ ()) ; (inj₂ ()) })
             ; run-out   = ∷ʳ⁺ (run-out ci) (λ _ r∈ → <-irrefl refl (All.lookup (ran-fresh ci) r∈))
             ; fresh     = ∷ʳ⁺ (All.map m<n⇒m<1+n (fresh ci)) (n<1+n r)
             ; ran-fresh = All.map m<n⇒m<1+n (ran-fresh ci)
             ; uniq      = AP.++⁺ (uniq ci) ([] ∷ []) (All.map (λ lt → <⇒≢ lt ∷ []) (fresh ci)) }
    , n≤1+n r , λ p → p
... | yes _ | false | ()
... | no _  | _     | ()
conn-good {_ , conn} {run k} {cst n is ts} eq ci with map-split {f = λ is′ → cst n is′ ts} {x = movePh k hsd running is} eq
... | _ , eq₁ , refl = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ _ → inj₁ refl) eq₁ ci , ≤-refl , λ p → p
conn-good {_ , conn} {abort k} {cst n is ts} eq ci with map-split {f = λ is′ → cst n is′ ts} {x = movePh k hsd closing is} eq
... | _ , eq₁ , refl = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) eq₁ ci , ≤-refl , λ p → p
conn-good {_ , conn} {reset k} {cst n is ts} eq ci with map-split {f = λ is′ → cst n is′ ts} {x = freeIt k is} eq
... | _ , eq₁ , refl =
      record { failed-in = freeIt-all eq₁ (failed-in ci) (λ q → q)
             ; run-out   = freeIt-all eq₁ (run-out ci) (λ q → q)
             ; fresh     = freeIt-all eq₁ (fresh ci) (λ q → q)
             ; ran-fresh = ran-fresh ci
             ; uniq      = freeIt-uniq eq₁ (uniq ci) }
    , ≤-refl , λ p → p
conn-good {_ , conn} {close k} {cst n is ts} eq ci with map-split {f = λ is′ → cst n is′ ts} {x = closeIt k is} eq
... | _ , eq₁ , refl =
      record { failed-in = closeIt-all eq₁ (failed-in ci)
             ; run-out   = closeIt-all eq₁ (run-out ci)
             ; fresh     = closeIt-all eq₁ (fresh ci)
             ; ran-fresh = ran-fresh ci
             ; uniq      = closeIt-uniq eq₁ (uniq ci) }
    , ≤-refl , λ p → p
conn-good {_ , conn} {fail k} {cst n is ts} eq ci
  with map-split {f = λ is′ → cst n is′ (k ∷ ts)} {x = movePh k running failed is <∣> movePh k released failedT is} eq
... | _ , eq₁ , refl with alt-split {x = movePh k running failed is} eq₁
...   | inj₁ eq₂ = fail-inv (inj₁ refl) eq₂ ci , ≤-refl , there
...   | inj₂ eq₂ = fail-inv (inj₂ refl) eq₂ ci , ≤-refl , there
conn-good {_ , trace} {k , _} {cst n is ts} eq ci
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh k failed closing is <∣> movePh k failedT closing is} eq
... | _ , eq₁ , refl with alt-split {x = movePh k failed closing is} eq₁
...   | inj₁ eq₂ = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) eq₂ ci , ≤-refl , λ p → p
...   | inj₂ eq₂ = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) eq₂ ci , ≤-refl , λ p → p
conn-good {_ , rel} {_ , b} {cst n is ts} eq ci with map-split {f = λ is′ → cst n is′ ts} {x = relLive b (newest is) is} eq
... | _ , eq₁ , refl with rel-split {b} {newest is} eq₁
...   | inj₁ (_ , eq₂)               = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ _ → inj₁ refl) eq₂ ci , ≤-refl , λ p → p
...   | inj₂ (inj₁ (_ , eq₂))        = mv-inv (λ { (inj₁ ()) ; (inj₂ ()) }) (λ _ → inj₂ (inj₁ refl)) eq₂ ci , ≤-refl , λ p → p
...   | inj₂ (inj₂ (inj₁ (_ , eq₂))) = mv-inv (λ _ → inj₁ refl) (λ { (inj₁ ()) ; (inj₂ (inj₁ ())) ; (inj₂ (inj₂ ())) }) eq₂ ci , ≤-refl , λ p → p
...   | inj₂ (inj₂ (inj₂ refl))      = ci , ≤-refl , λ p → p

-- a trace comes from a failed or failedT incarnation, whose mux is terminal, under any CM policy
trace-in : ∀ {r v c c′ pol} → cstep ((ℕ × Maybe ℕ) , trace) (r , v) pol c ≡ just c′ → CInv c → r ∈ ran c
trace-in {r} {c = cst n is ts} eq ci
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh r failed closing is <∣> movePh r failedT closing is} eq
... | _ , eq₁ , _ with alt-split {x = movePh r failed closing is} eq₁
...   | inj₁ eq₂ = let (fi , e , ph) = lookupAny (failed-in ci) (movePh-any eq₂) in subst (_∈ ts) e (fi (inj₁ ph))
...   | inj₂ eq₂ = let (fi , e , ph) = lookupAny (failed-in ci) (movePh-any eq₂) in subst (_∈ ts) e (fi (inj₂ ph))

-- a handshake's id is below the new next, under any CM policy
hs-lt : ∀ {a c c′ pol} → cstep (ℕ , hs) a pol c ≡ just c′ → a < next c′
hs-lt {a} {cst n is _} {pol = pol} eq with a ≟ n | admitOK pol is | eq
... | yes refl | true  | refl = n<1+n a
... | yes _    | false | ()
... | no _     | _     | ()

-- a queue item stays OK across a monotone Conn move
qok-mono : ∀ {c c′} → CMono c c′ → ∀ {i} → QOK c i → QOK c′ i
qok-mono (le , _) {nc _} lt = <-≤-trans lt le
qok-mono (_ , sub) {mf _} p = sub p
qok-mono _ {mfK} ()

-- GoodO survives a Conn move with the IG unchanged
goodO-conn : ∀ {c c′ g} → CInv c′ × CMono c c′ → GoodO c g → GoodO c′ g
goodO-conn (ci , mono) G = record { cinv = ci ; queue-ok = All.map (qok-mono mono) (queue-ok G)
                                  ; await-ok = λ r p → proj₂ mono (await-ok G r p) }

-- enqueueing an OK item keeps GoodO
goodO-push : ∀ {c e q ph i} → GoodO c (gst e q ph) → QOK c i → GoodO c (gst e (q ∷ʳ i) ph)
goodO-push G ok = record { cinv = cinv G ; queue-ok = ∷ʳ⁺ (queue-ok G) ok ; await-ok = await-ok G }

------------------------------------------------------------------------
-- Gov-side preservation and the step lemma

-- taking the queue head keeps GoodO under either NewConnection policy
take-good : ∀ {c} p e i q → CInv c → All (QOK c) (i ∷ q) → GoodO c (takeG p e i q)
take-good _       nothing  (nc _) _ ci (_ ∷ qs)  = record { cinv = ci ; queue-ok = qs ; await-ok = λ _ () }
take-good keep    (just _) (nc _) _ ci (_ ∷ qs)  = record { cinv = ci ; queue-ok = qs ; await-ok = λ _ () }
take-good replace (just _) (nc _) _ ci (_ ∷ qs)  = record { cinv = ci ; queue-ok = qs ; await-ok = λ _ () }
take-good _       nothing  (mf _) _ ci (ok ∷ qs) = record { cinv = ci ; queue-ok = qs ; await-ok = λ { _ refl → ok } }
take-good keep    (just _) (mf _) _ ci (ok ∷ qs) = record { cinv = ci ; queue-ok = qs ; await-ok = λ { _ refl → ok } }
take-good replace (just _) (mf _) _ ci (ok ∷ qs) = record { cinv = ci ; queue-ok = qs ; await-ok = λ { _ refl → ok } }
take-good _       _        mfK    _ _  (() ∷ _)

-- every IG-only move keeps GoodO, whatever the mode's switches
goodO-gov : ∀ {m c g g₁} a → GoodO c g → gstep (GovAct , gov) a m g ≡ just g₁ → GoodO c g₁
goodO-gov {g = gst _ _ idle}            promote G refl = G
goodO-gov {g = gst _ _ (await _)}       promote G ()
goodO-gov {g = gst _ [] _}              take    G ()
goodO-gov {g = gst _ (_ ∷ _) (await _)} take    G ()
goodO-gov {m} {g = gst e (i ∷ q) idle}  take    G refl = take-good (newP m) e i q (cinv G) (queue-ok G)
goodO-gov {g = gst _ _ idle}            tmo     G ()
goodO-gov {m} {g = gst _ _ (await _)}   tmo     G eq with timer m | eq
... | true  | refl = record { cinv = cinv G ; queue-ok = queue-ok G ; await-ok = λ _ () }
... | false | ()

-- every composite step of an own-mux mode keeps GoodO (generic in newP, unregP, timer)
goodO-step : ∀ {m c g c′ g′} {at : AnyTypes Ev} {a : proj₁ at}
           → enqP m ≡ own → GoodO c g → sstep at a m c g ≡ just (c′ , g′) → GoodO c′ g′
goodO-step {m} {c = c} {g} {at = _ , conn} {a} _ G eq with map-split {f = λ c′ → c′ , g} {x = cstep (ConnAct , conn) a (cmP m) c} eq
... | _ , eqc , refl = goodO-conn (conn-good {_ , conn} {a} {c} {pol = cmP m} eqc (cinv G)) G
goodO-step {m} {c} {g} {at = _ , gov} {a} _ G eq with map-split {f = λ g′ → c , g′} {x = gstep (GovAct , gov) a m g} eq
... | _ , eqg , refl = goodO-gov a G eqg
goodO-step {m} {c = c} {gst e q ph} {at = _ , hs} {a} _ G eq with zip-split eq
... | eqc , refl = goodO-push (goodO-conn (conn-good {_ , hs} {a} {c} {pol = cmP m} eqc (cinv G)) G) (hs-lt {a} {c} {pol = cmP m} eqc)
goodO-step {m} {c} {gst e q ph} {at = _ , trace} {r , v} o G eq with zip-split eq
... | eqc , eqg with ≡-dec _≟_ v e | eqg
...   | no _  | ()
...   | yes _ | refl rewrite o = goodO-push (goodO-conn cg G) (proj₂ (proj₂ cg) (trace-in {r} {v} {c} {pol = cmP m} eqc (cinv G)))
  where
    -- the Conn half of the trace step
    cg = conn-good {_ , trace} {r , v} {c} {pol = cmP m} eqc (cinv G)
goodO-step {g = gst _ _ idle} {at = _ , stopped} _ G eq with zip-split eq
... | _ , ()
goodO-step {m} {c = c} {gst e q (await r)} {at = _ , stopped} {t} _ G eq with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _  | ()
...   | yes _ | refl = record { cinv = cinv G₁ ; queue-ok = queue-ok G₁ ; await-ok = λ _ () }
  where
    -- the state after the Conn half of the `stopped` step
    G₁ = goodO-conn (conn-good {_ , stopped} {t} {c} {pol = cmP m} eqc (cinv G)) G

goodO-step {m} {c = c} {gst e q idle} {at = _ , rel} {x , b} _ G eq with zip-split eq
... | eqc , eqg with relP m | ≡-dec _≟_ e (just x) | eqg
...   | true  | yes _ | refl = record { cinv = cinv G₁ ; queue-ok = queue-ok G₁ ; await-ok = λ _ () }
  where
    -- the state after the Conn half of the release (on the newest incarnation, either outcome; the entry is relEntry b e)
    G₁ = goodO-conn (conn-good {_ , rel} {x , b} {c} {pol = cmP m} eqc (cinv G)) G
...   | true  | no _  | ()
...   | false | _     | ()
goodO-step {g = gst _ _ (await _)} {at = _ , rel} _ G eq with zip-split eq
... | _ , ()

-- GoodO holds along every run of an own-mux mode
goodO-run : ∀ {m c g s c′ g′} → enqP m ≡ own → GoodO c g → Steps m c g s c′ g′ → GoodO c′ g′
goodO-run _ G done              = G
goodO-run o G (step at a eq ss) = goodO-run o (goodO-step {at = at} {a} o G eq) ss

-- every reachable state of an own-mux mode satisfies GoodO
own-reach : ∀ {m c g} → enqP m ≡ own → Reach m c g → GoodO c g
own-reach o (_ , ss) = goodO-run o goodO₀ ss

------------------------------------------------------------------------
-- Safety and liveness for every own-mux mode

-- every awaited mux is terminal
own-safe : ∀ {m c g} → enqP m ≡ own → Reach m c g → ∀ r → gphase g ≡ await r → r ∈ ran c
own-safe o R = await-ok (own-reach o R)

-- Conn answers `stopped t` for every terminal t, leaving its state unchanged, under any CM policy
stopped-ok : ∀ {t c pol} → t ∈ ran c → cstep (ℕ , stopped) t pol c ≡ just c
stopped-ok {t} {cst _ _ ts} p with t ∈? ts
... | yes _ = refl
... | no ¬p = ⊥-elim (¬p p)

-- a Gov blocked on r answers `stopped r` and returns to idle
stopped-gov-ok : ∀ {r m e q} → gstep (ℕ , stopped) r m (gst e q (await r)) ≡ just (gst (unreg (unregP m) r e) q idle)
stopped-gov-ok {r} with r ≟ r
... | yes _ = refl
... | no n  = ⊥-elim (n refl)

-- promote now from an idle IG, or after the awaited terminal mux's `stopped`
live-at : ∀ {m c} g → GoodO c g
        → (Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps m c g (GV promote ∷ []) c′ g′)
        ⊎ (Σ[ r ∈ ℕ ] Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps m c g (ST r ∷ GV promote ∷ []) c′ g′)
live-at (gst _ _ idle) _ = inj₁ (_ , _ , step (GovAct , gov) promote refl done)
live-at {m} {c} (gst e q (await r)) G = inj₂ (r , _ , _ , step (ℕ , stopped) r st (step (GovAct , gov) promote refl done))
  where
    -- the synchronised `stopped r` move
    st : sstep (ℕ , stopped) r m c (gst e q (await r)) ≡ just (c , gst (unreg (unregP m) r e) q idle)
    st rewrite stopped-ok {r} {c} {pol = cmP m} (await-ok G r refl) | stopped-gov-ok {r} {m} {e} {q} = refl

-- process-level liveness for every own-mux mode
own-live-sys : ∀ {m s W} → enqP m ≡ own → Sys m ⟹⟨ s ⟩ W
             → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
own-live-sys {m} o st with run-inv st
... | _ , g′ , refl , ss with live-at {m} g′ (goodO-run o goodO₀ ss)
...   | inj₁ (_ , _ , ss′)     = inj₁ (_ , run-intro ss′)
...   | inj₂ (r , _ , _ , ss′) = inj₂ (r , _ , run-intro ss′)

F2-safe = own-safe refl

F2-live {g = g} R = live-at g (own-reach refl R)

F2-live-sys = own-live-sys refl

F2id-safe = own-safe refl

F2id-live-sys = own-live-sys refl

------------------------------------------------------------------------
-- CarryMuxId: no orphaning step

-- an active incarnation's mux is not terminal
active-out : ∀ {c x} → CInv c → Active c x → x ∉ ran c
active-out ci act = let (o , e , h , _) = lookupAny (run-out ci) act in subst (_∉ _) e (o (map₂ inj₁ h))

-- under CarryMuxId no step drops the entry of an active incarnation
keeps-entry : ∀ {c e q ph x c′ g′} → GoodO c (gst e q ph) → ∀ at a
            → sstep at a CarryMuxId c (gst e q ph) ≡ just (c′ , g′) → e ≡ just x → Active c x → entry g′ ≡ just x
keeps-entry {c} {e} {q} {ph} _ (_ , conn) a eq ex _ with map-split {f = λ c′ → c′ , gst e q ph} {x = cstep (ConnAct , conn) a (cmP CarryMuxId) c} eq
... | _ , _ , refl = ex
keeps-entry _ (_ , hs) _ eq ex _ with zip-split eq
... | _ , refl = ex
keeps-entry {e = e} _ (_ , trace) (_ , v) eq ex _ with zip-split eq
... | _ , eqg with ≡-dec _≟_ v e | eqg
...   | yes _ | refl = ex
...   | no _  | ()
keeps-entry {ph = idle} _ (_ , stopped) _ eq _ _ with zip-split eq
... | _ , ()
keeps-entry {ph = await r} {x} G (_ , stopped) t eq refl act with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _    | ()
...   | yes refl | refl with x ≟ t
...     | yes refl = ⊥-elim (active-out (cinv G) act (stopped-conn {pol = cmP CarryMuxId} eqc))
...     | no _     = refl
keeps-entry {ph = idle}                 _ (_ , gov) promote refl ex _ = ex
keeps-entry {ph = await _}              _ (_ , gov) promote () _ _
keeps-entry {q = []}                    _ (_ , gov) take () _ _
keeps-entry {q = _ ∷ _} {ph = await _}  _ (_ , gov) take () _ _
keeps-entry {q = nc _ ∷ _} {ph = idle}  _ (_ , gov) take refl refl _ = refl
keeps-entry {q = mf _ ∷ _} {ph = idle}  _ (_ , gov) take refl refl _ = refl
keeps-entry {q = mfK ∷ _} {ph = idle}   _ (_ , gov) take refl refl _ = refl
keeps-entry {ph = idle} _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
keeps-entry {ph = await _} _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
keeps-entry {ph = idle}                 _ (_ , gov) tmo () _ _
keeps-entry {ph = await _}              _ (_ , gov) tmo () _ _

F2id-no-orphan {g = gst _ _ _} R at a (_ , _ , _ , eq , ex , ne , act) = ne (keeps-entry (own-reach refl R) at a eq ex act)
