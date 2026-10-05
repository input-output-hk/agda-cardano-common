{-# OPTIONS --guardedness #-}

-- The wedge is conditional on the field path (P1f: it lasts while D lives) and
-- unconditional on the never-run path (W0: the awaited mux can never become terminal).
module CSP.Examples.GovernorWedge.Wedged where

open import Data.Empty using (⊥-elim)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (<-irrefl; m<n⇒m<1+n)
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.Maybe using (Maybe; just; nothing; map; _<∣>_)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import Process_Trees
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import CSP.Examples.GovernorWedge.Witness using (cW0; gW0)
open import CSP.Examples.GovernorWedge.FieldPath using (cF; gF)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_)

-- the IG is blocked on r, r's mux is not terminal, and there is no timer
record Blocked (m : Mode) (c : CState) (g : GState) (r : ℕ) : Set where
  field
    blocked  : gphase g ≡ await r
    not-ran  : r ∉ ran c
    no-timer : timer m ≡ false
open Blocked public

-- Blocked survives every step except r's own fail
blocked-step : ∀ {m c g r c′ g′} {at : AnyTypes Ev} {a : proj₁ at}
             → Blocked m c g r → sstep at a m c g ≡ just (c′ , g′) → lbl at a ≢ CN (fail r) → Blocked m c′ g′ r

-- a blocked IG does not offer promote
blocked-no-promote : ∀ {m c g r} → Blocked m c g r → sstep (GovAct , gov) promote m c g ≡ nothing

-- no promote in any continuation that does not contain r's fail
blocked-until : ∀ {m c g r s c′ g′} → Blocked m c g r → Steps m c g s c′ g′
              → All (_≢ CN (fail r)) s → All (_≢ GV promote) s

-- r's mux can never become terminal: r is below next and not live
Dead : CState → ℕ → Set
Dead c r = r < next c × All (λ i → iid i ≢ r) (live c)

-- Dead survives every step
dead-step : ∀ {m c g r c′ g′} {at : AnyTypes Ev} {a : proj₁ at} → Dead c r → sstep at a m c g ≡ just (c′ , g′) → Dead c′ r

-- a dead incarnation never fails, under any CM policy
dead-no-fail : ∀ {c r pol} → Dead c r → cstep (ConnAct , conn) (fail r) pol c ≡ nothing

-- P1f: after the field path, the pinned IG never promotes while D (2) does not fail
P1f : ∀ {s W′} → SysAt AsBuilt cF gF ⟹⟨ s ⟩ W′ → All (_≢ CN (fail 2)) s → All (_≢ GV promote) s
-- P1f for origin/main
P1fmain : ∀ {s W′} → SysAt Main cF gF ⟹⟨ s ⟩ W′ → All (_≢ CN (fail 2)) s → All (_≢ GV promote) s
-- W0: after the never-run path the pinned IG never promotes again, in any continuation
W0-permanent : ∀ {s W′} → SysAt AsBuilt cW0 gW0 ⟹⟨ s ⟩ W′ → All (_≢ GV promote) s
-- W0 for origin/main
W0main-permanent : ∀ {s W′} → SysAt Main cW0 gW0 ⟹⟨ s ⟩ W′ → All (_≢ GV promote) s

-- an onLive update never changes the terminal muxes
onLive-ran : ∀ {f c c′} → onLive f c ≡ just c′ → ran c′ ≡ ran c
onLive-ran {f} {cst _ is _} eq with f is | eq
... | just _ | refl = refl

-- a Conn move other than r's fail keeps r outside `ran`, under any CM policy
conn-keeps : ∀ {at a c c′ r pol} → cstep at a pol c ≡ just c′ → lbl at a ≢ CN (fail r) → r ∉ ran c → r ∉ ran c′
conn-keeps {_ , gov} ()
conn-keeps {_ , stopped} {t} {cst _ _ ts} eq _ nr with t ∈? ts | eq
... | yes _ | refl = nr
... | no _  | ()
conn-keeps {_ , hs} {r′} {cst n is _} {pol = pol} eq _ nr with r′ ≟ n | admitOK pol is | eq
... | yes _ | true  | refl = nr
... | yes _ | false | ()
... | no _  | _     | ()
conn-keeps {_ , conn} {run k}   {c} eq _ nr rewrite onLive-ran {movePh k hsd running} {c} eq = nr
conn-keeps {_ , conn} {abort k} {c} eq _ nr rewrite onLive-ran {movePh k hsd closing} {c} eq = nr
conn-keeps {_ , conn} {reset k} {c} eq _ nr rewrite onLive-ran {freeIt k} {c} eq = nr
conn-keeps {_ , conn} {close k} {c} eq _ nr rewrite onLive-ran {closeIt k} {c} eq = nr
conn-keeps {_ , conn} {fail k} {cst n is ts} eq ne nr with movePh k running failed is <∣> movePh k released failedT is | eq
... | just _ | refl = λ { (here r≡k) → ne (cong (λ x → CN (fail x)) (sym r≡k)) ; (there p) → nr p }
conn-keeps {_ , trace} {k , _} {c} eq _ nr rewrite onLive-ran {λ is → movePh k failed closing is <∣> movePh k failedT closing is} {c} eq = nr
conn-keeps {_ , rel} {_ , b} {c} eq _ nr rewrite onLive-ran {λ is → relLive b (newest is) is} {c} eq = nr

-- Conn answers `stopped t` only for a terminal mux t, under any CM policy
stopped-conn : ∀ {t c c₁ pol} → cstep (ℕ , stopped) t pol c ≡ just c₁ → t ∈ ran c
stopped-conn {t} {cst _ _ ts} eq with t ∈? ts | eq
... | yes p | _  = p
... | no _  | ()

-- a Gov blocked on r answers `stopped t` only for t ≡ r
stopped-gov : ∀ {t m g g₁ r} → gphase g ≡ await r → gstep (ℕ , stopped) t m g ≡ just g₁ → t ≡ r
stopped-gov {t} {g = gst _ _ _} {r = r} refl eq with t ≟ r | eq
... | yes p | _  = p
... | no _  | ()

-- a trace enqueue leaves the IG loop phase unchanged
trace-phase : ∀ {a m g g₁} → gstep ((ℕ × Maybe ℕ) , trace) a m g ≡ just g₁ → gphase g₁ ≡ gphase g
trace-phase {_ , v} {g = gst e _ _} eq with ≡-dec _≟_ v e | eq
... | yes _ | refl = refl
... | no _  | ()

-- a handshake enqueue leaves the IG loop phase unchanged
hs-phase : ∀ {a m g g₁} → gstep (ℕ , hs) a m g ≡ just g₁ → gphase g₁ ≡ gphase g
hs-phase {g = gst _ _ _} refl = refl

-- a blocked Gov refuses the release, under any mode
rel-await : ∀ a {m g r} → gphase g ≡ await r → gstep ((ℕ × Bool) , rel) a m g ≡ nothing
rel-await _ {g = gst _ _ _} refl = refl

-- a blocked Gov without a timer refuses every gov action
gov-await : ∀ a {m g r} → gphase g ≡ await r → timer m ≡ false → gstep (GovAct , gov) a m g ≡ nothing
gov-await promote {g = gst _ _ _} refl _ = refl
gov-await take {g = gst _ [] _} refl _ = refl
gov-await take {g = gst _ (_ ∷ _) _} refl _ = refl
gov-await tmo {m} {gst _ _ _} refl nt rewrite nt = refl

blocked-step {m} {c = c} {g} {at = _ , conn} {a} b eq ne with map-split {f = λ c′ → c′ , g} {x = cstep (ConnAct , conn) a (cmP m) c} eq
... | _ , eqc , refl = record { blocked = blocked b ; not-ran = conn-keeps {_ , conn} {a} {c} {pol = cmP m} eqc ne (not-ran b)
                              ; no-timer = no-timer b }
blocked-step {m} {c} {g} {at = _ , gov} {a} b eq _ with map-split {f = λ g′ → c , g′} {x = gstep (GovAct , gov) a m g} eq
... | _ , eqg , refl with trans (sym eqg) (gov-await a {m} {g} (blocked b) (no-timer b))
...   | ()
blocked-step {m} {c} {at = _ , hs} {a} b eq ne with zip-split eq
... | eqc , eqg = record { blocked = trans (hs-phase {a} {m} eqg) (blocked b) ; not-ran = conn-keeps {_ , hs} {a} {c} {pol = cmP m} eqc ne (not-ran b)
                         ; no-timer = no-timer b }
blocked-step {m} {c} {at = _ , trace} {a} b eq ne with zip-split eq
... | eqc , eqg = record { blocked = trans (trace-phase eqg) (blocked b) ; not-ran = conn-keeps {_ , trace} {a} {c} {pol = cmP m} eqc ne (not-ran b)
                         ; no-timer = no-timer b }
blocked-step {m} {at = _ , stopped} b eq _ with zip-split eq
... | eqc , eqg = ⊥-elim (not-ran b (subst (_∈ _) (stopped-gov (blocked b) eqg) (stopped-conn {pol = cmP m} eqc)))
blocked-step {m} {g = g} {at = _ , rel} {a} b eq _ with zip-split eq
... | _ , eqg with trans (sym eqg) (rel-await a {m} {g} (blocked b))
...   | ()

blocked-no-promote {c = c} b = cong (map (λ g′ → c , g′)) (gov-await promote (blocked b) (no-timer b))

-- a blocked state never takes a promote step
no-promote-step : ∀ {m c g r c₁ g₁} → Blocked m c g r → ∀ at a → sstep at a m c g ≡ just (c₁ , g₁) → lbl at a ≢ GV promote
no-promote-step b (_ , _) _ eq refl with trans (sym eq) (blocked-no-promote b)
... | ()

blocked-until b done [] = []
blocked-until b (step at a eq ss) (nf ∷ nfs) = no-promote-step b at a eq ∷ blocked-until (blocked-step {at = at} {a} b eq nf) ss nfs

-- moving a phase keeps every live id
movePh-ids : ∀ {k p p′ r is is′} → movePh k p p′ is ≡ just is′ → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′
movePh-ids {k} {p} {p′} {is = mkInc x ph fr ∷ xs} eq (px ∷ ps) with k ≟ x | ph ≟ᴾ p | eq
... | yes _ | yes _ | refl = px ∷ ps
... | yes _ | no _  | eq′ with map-split {f = mkInc x ph fr ∷_} {x = movePh k p p′ xs} eq′
...   | _ , eq₁ , refl = px ∷ movePh-ids {k} {p} {p′} eq₁ ps
movePh-ids {k} {p} {p′} {is = mkInc x ph fr ∷ xs} eq (px ∷ ps) | no _ | _ | eq′ with map-split {f = mkInc x ph fr ∷_} {x = movePh k p p′ xs} eq′
...   | _ , eq₁ , refl = px ∷ movePh-ids {k} {p} {p′} eq₁ ps

-- a peer reset keeps every live id
freeIt-ids : ∀ {k r is is′} → freeIt k is ≡ just is′ → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′
freeIt-ids {k} {is = mkInc x ph f ∷ xs} eq (px ∷ ps) with k ≟ x | eq
... | no _ | eq′ with map-split {f = mkInc x ph f ∷_} {x = freeIt k xs} eq′
...   | _ , eq₁ , refl = px ∷ freeIt-ids {k} eq₁ ps
freeIt-ids {k} {is = mkInc x ph f ∷ _} eq (px ∷ ps) | yes _ | eq′ with ph | f | eq′
... | hsd     | false | refl = px ∷ ps
... | running | false | refl = px ∷ ps
... | released | false | refl = px ∷ ps
... | hsd     | true  | ()
... | running | true  | ()
... | released | true | ()
... | failed  | _     | ()
... | closing | _     | ()
... | failedT | _     | ()

-- closing a socket only removes a live entry
closeIt-ids : ∀ {k r is is′} → closeIt k is ≡ just is′ → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′
closeIt-ids {k} {is = mkInc x ph fr ∷ xs} eq (px ∷ ps) with k ≟ x | ph ≟ᴾ closing | eq
... | yes _ | yes _ | refl = ps
... | yes _ | no _  | eq′ with map-split {f = mkInc x ph fr ∷_} {x = closeIt k xs} eq′
...   | _ , eq₁ , refl = px ∷ closeIt-ids {k} eq₁ ps
closeIt-ids {k} {is = mkInc x ph fr ∷ xs} eq (px ∷ ps) | no _ | _ | eq′ with map-split {f = mkInc x ph fr ∷_} {x = closeIt k xs} eq′
...   | _ , eq₁ , refl = px ∷ closeIt-ids {k} eq₁ ps

-- a trace's move (from failed or failedT) keeps every live id
trace-ids : ∀ {k r is is′} → (movePh k failed closing is <∣> movePh k failedT closing is) ≡ just is′
          → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′
trace-ids {k} {is = is} eq ps with alt-split {x = movePh k failed closing is} eq
... | inj₁ eq₁ = movePh-ids {k} {failed} {closing} eq₁ ps
... | inj₂ eq₁ = movePh-ids {k} {failedT} {closing} eq₁ ps

-- a release's CM half keeps every live id
rel-ids : ∀ {b y r is is′} → relLive b y is ≡ just is′ → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′
rel-ids {b} {y} eq ps with rel-split {b} {y} eq
... | inj₁ (k , eq₁)               = movePh-ids {k} {hsd} {released} eq₁ ps
... | inj₂ (inj₁ (k , eq₁))        = movePh-ids {k} {running} {released} eq₁ ps
... | inj₂ (inj₂ (inj₁ (k , eq₁))) = movePh-ids {k} {failed} {failedT} eq₁ ps
... | inj₂ (inj₂ (inj₂ refl))      = ps

-- an id-preserving onLive update keeps Dead
onLive-dead : ∀ {f c c′ r} → (∀ {is is′} → f is ≡ just is′ → All (λ i → iid i ≢ r) is → All (λ i → iid i ≢ r) is′)
            → onLive f c ≡ just c′ → Dead c r → Dead c′ r
onLive-dead {f} {cst _ is _} pres eq (lt , ps) with f is | eq | pres {is}
... | just _ | refl | k = lt , k refl ps

-- every Conn move keeps Dead, under any CM policy
conn-dead : ∀ {at a c c′ r pol} → cstep at a pol c ≡ just c′ → Dead c r → Dead c′ r
conn-dead {_ , gov} ()
conn-dead {_ , stopped} {t} {cst _ _ ts} eq d with t ∈? ts | eq
... | yes _ | refl = d
... | no _  | ()
conn-dead {_ , hs} {r′} {cst n is _} {pol = pol} eq (lt , ps) with r′ ≟ n | admitOK pol is | eq
... | yes _ | true  | refl = m<n⇒m<1+n lt , ∷ʳ⁺ ps (λ n≡r → <-irrefl (sym n≡r) lt)
... | yes _ | false | ()
... | no _  | _     | ()
conn-dead {_ , conn} {run k}   eq d = onLive-dead (movePh-ids {k} {hsd} {running}) eq d
conn-dead {_ , conn} {abort k} eq d = onLive-dead (movePh-ids {k} {hsd} {closing}) eq d
conn-dead {_ , conn} {reset k} eq d = onLive-dead (freeIt-ids {k}) eq d
conn-dead {_ , conn} {close k} eq d = onLive-dead (closeIt-ids {k}) eq d
conn-dead {_ , conn} {fail k} {cst n is ts} eq (lt , ps)
  with map-split {f = λ is′ → cst n is′ (k ∷ ts)} {x = movePh k running failed is <∣> movePh k released failedT is} eq
... | _ , eq₁ , refl with alt-split {x = movePh k running failed is} eq₁
...   | inj₁ eq₂ = lt , movePh-ids {k} {running} {failed} eq₂ ps
...   | inj₂ eq₂ = lt , movePh-ids {k} {released} {failedT} eq₂ ps
conn-dead {_ , trace} {k , _} eq d = onLive-dead (trace-ids {k}) eq d
conn-dead {_ , rel} {_ , b} eq d = onLive-dead (λ {is} → rel-ids {b} {newest is}) eq d

dead-step {m} {c = c} {g} {at = _ , conn} {a} d eq with map-split {f = λ c′ → c′ , g} {x = cstep (ConnAct , conn) a (cmP m) c} eq
... | _ , eqc , refl = conn-dead {_ , conn} {a} {pol = cmP m} eqc d
dead-step {m} {c} {g} {at = _ , gov} {a} d eq with map-split {f = λ g′ → c , g′} {x = gstep (GovAct , gov) a m g} eq
... | _ , _ , refl = d
dead-step {m} {at = _ , hs} {a} d eq with zip-split eq
... | eqc , _ = conn-dead {_ , hs} {a} {pol = cmP m} eqc d
dead-step {m} {at = _ , trace} {a} d eq with zip-split eq
... | eqc , _ = conn-dead {_ , trace} {a} {pol = cmP m} eqc d
dead-step {m} {at = _ , stopped} {a} d eq with zip-split eq
... | eqc , _ = conn-dead {_ , stopped} {a} {pol = cmP m} eqc d
dead-step {m} {at = _ , rel} {a} d eq with zip-split eq
... | eqc , _ = conn-dead {_ , rel} {a} {pol = cmP m} eqc d

-- a phase move of an id that is not live is refused
movePh-none : ∀ {r p p′ is} → All (λ i → iid i ≢ r) is → movePh r p p′ is ≡ nothing
movePh-none [] = refl
movePh-none {r} {p} {p′} {mkInc x ph _ ∷ _} (px ∷ ps) with r ≟ x | ph ≟ᴾ p
... | yes r≡x | _ = ⊥-elim (px (sym r≡x))
... | no _    | _ rewrite movePh-none {r} {p} {p′} ps = refl

dead-no-fail {cst _ _ _} {r} (_ , ps) rewrite movePh-none {r} {running} {failed} ps | movePh-none {r} {released} {failedT} ps = refl

-- a Dead state never takes r's fail step
dead-step-nf : ∀ {m c g r c₁ g₁} → Dead c r → ∀ at a → sstep at a m c g ≡ just (c₁ , g₁) → lbl at a ≢ CN (fail r)
dead-step-nf {m} {g = g} d (_ , _) _ eq refl with trans (sym eq) (cong (map (λ c′ → c′ , g)) (dead-no-fail {pol = cmP m} d))
... | ()

-- no continuation of a Dead state contains r's fail
dead-steps : ∀ {m c g r s c′ g′} → Dead c r → Steps m c g s c′ g′ → All (_≢ CN (fail r)) s
dead-steps d done = []
dead-steps d (step at a eq ss) = dead-step-nf d at a eq ∷ dead-steps (dead-step {at = at} {a} d eq) ss

-- the field state is blocked on D under any mode without a timer
bF : ∀ {m} → timer m ≡ false → Blocked m cF gF 2
bF nt = record { blocked = refl ; not-ran = λ { (here ()) ; (there (here ())) ; (there (there ())) } ; no-timer = nt }

-- the never-run state is blocked on 0 under any mode without a timer
bW0 : ∀ {m} → timer m ≡ false → Blocked m cW0 gW0 0
bW0 nt = record { blocked = refl ; not-ran = λ { (here ()) ; (there ()) } ; no-timer = nt }

-- incarnation 0 is dead in the never-run state
dW0 : Dead cW0 0
dW0 = s≤s z≤n , (λ ()) ∷ []

P1f st with run-inv st
... | _ , _ , _ , ss = blocked-until (bF refl) ss

P1fmain st with run-inv st
... | _ , _ , _ , ss = blocked-until (bF refl) ss

W0-permanent st with run-inv st
... | _ , _ , _ , ss = blocked-until (bW0 refl) ss (dead-steps dW0 ss)

W0main-permanent st with run-inv st
... | _ , _ , _ , ss = blocked-until (bW0 refl) ss (dead-steps dW0 ss)
