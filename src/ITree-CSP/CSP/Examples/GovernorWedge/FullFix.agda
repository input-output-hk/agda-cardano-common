{-# OPTIONS --guardedness #-}

-- FullFix (own mux + replace + identity check): no wedge, no orphan, tracked.
-- Safety and liveness are the generic own-mux theorems of `Invariant`. No-orphan and
-- tracking need the FullFix invariant `FixI`: a queued `nc k` means every live
-- incarnation below k is freed (the hs guard, and freed never reverts); the queued
-- `nc` ids increase and exceed the entry; every active incarnation is the entry or
-- has its `nc` queued. So `take (nc k)` never displaces an active entry, and the
-- identity-checked unregister clears only a terminal (hence inactive) mux.
module CSP.Examples.GovernorWedge.FullFix where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc; _<_; _≟_)
open import Data.Nat.Properties using (<-≤-trans; <-irrefl; <-asym; m<n⇒m<1+n)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupAny)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.AllPairs.Properties as APP
open import Data.Maybe using (Maybe; just; nothing; _<∣>_)
open import Data.Maybe.Properties using (≡-dec)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst)

open import Process_Trees
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import CSP.Examples.GovernorWedge.Wedged using (stopped-conn)
open import CSP.Examples.GovernorWedge.Invariant
  using (GoodO; cinv; queue-ok; goodO₀; goodO-step; goodO-run; run-out; Runs; MuxAlive; QOK;
         conn-good; movePh-all; trace-all; freeIt-all; closeIt-all; active-out; own-safe; own-live-sys)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; traces)

-- FIX: every awaited mux is terminal
FIX-safe : ∀ {c g} → Reach FullFix c g → ∀ r → gphase g ≡ await r → r ∈ ran c
-- FIX: promote, or stopped r then promote, is always a trace
FIX-live-sys : ∀ {s W} → Sys FullFix ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
-- FIX: no reachable orphaning step
FIX-no-orphan : ∀ {c g} → Reach FullFix c g → ∀ at a → ¬ OrphanStep FullFix c g at a
-- FIX: whenever the IG is idle with an empty queue, the active incarnation (if any) is the entry
FIX-tracked : ∀ {c g} → Reach FullFix c g → gphase g ≡ idle → queue g ≡ [] → Tracked c g

FIX-safe = own-safe refl

FIX-live-sys = own-live-sys refl

------------------------------------------------------------------------
-- The FullFix invariant

-- a queued NewConnection k: every live incarnation below k is freed
NcFreed : List Inc → Item → Set
NcFreed is (nc k) = All (λ i → iid i < k → freed i ≡ true) is
NcFreed _  (mf _) = ⊤
NcFreed _  mfK    = ⊤

-- order of two queue items: NewConnection ids strictly increase, other items are unconstrained
NcLt : Item → Item → Set
NcLt (nc a) (nc b) = a < b
NcLt (nc _) (mf _) = ⊤
NcLt (nc _) mfK    = ⊤
NcLt (mf _) _      = ⊤
NcLt mfK    _      = ⊤

-- an active incarnation is the entry or has its NewConnection queued
TrackI : GState → Inc → Set
TrackI g i = Runs i → freed i ≡ false → entry g ≡ just (iid i) ⊎ nc (iid i) ∈ queue g

-- FullFix invariant (on top of GoodO)
record FixI (c : CState) (g : GState) : Set where
  field
    nc-freed : All (NcFreed (live c)) (queue g)
    sorted   : AllPairs NcLt (queue g)
    entry-ok : ∀ x → entry g ≡ just x → x < next c × All (NcLt (nc x)) (queue g)
    track    : All (TrackI g) (live c)
open FixI

-- the initial state satisfies FixI
fixI₀ : FixI c₀ g₀
fixI₀ = record { nc-freed = [] ; sorted = [] ; entry-ok = λ _ () ; track = [] }

------------------------------------------------------------------------
-- Small lemmas

-- a Bool cannot be both
bool-clash : ∀ {b} → b ≡ true → b ≡ false → ⊥
bool-clash refl ()

-- NewConnection is injective
nc-inj : ∀ {a b} → nc a ≡ nc b → a ≡ b
nc-inj refl = refl

-- every item may follow any item in the order when it is a MuxFinished
ncLt-mf : ∀ i {r} → NcLt i (mf r)
ncLt-mf (nc _) = tt
ncLt-mf (mf _) = tt
ncLt-mf mfK    = tt

-- allFreed as an All
allFreed-all : ∀ {is} → allFreed is ≡ true → All (λ i → freed i ≡ true) is
allFreed-all {[]} _ = []
allFreed-all {mkInc _ _ true ∷ is} eq = refl ∷ allFreed-all eq
allFreed-all {mkInc _ _ false ∷ is} ()

-- the identity check keeps an entry that is not the awaited mux
unreg-keeps : ∀ {r e x} → e ≡ just x → x ≢ r → unreg idChecked r e ≡ just x
unreg-keeps {r} {x = x} refl ne with x ≟ r
... | yes p = ⊥-elim (ne p)
... | no _  = refl

-- a non-empty entry after the identity check was already the entry
unreg-just : ∀ {r e x} → unreg idChecked r e ≡ just x → e ≡ just x
unreg-just {e = nothing} ()
unreg-just {r} {just y} eq with y ≟ r | eq
... | yes _ | ()
... | no _  | refl = refl

-- the hs guard, inverted, under any CM policy (allFreed follows admitOK via admitOK-freed)
hs-inv : ∀ {a n is ts c′ pol} → cstep (ℕ , hs) a pol (cst n is ts) ≡ just c′
       → a ≡ n × allFreed is ≡ true × c′ ≡ cst (suc n) (is ∷ʳ mkInc n hsd false) ts
hs-inv {a} {n} {is} {pol = pol} eq with a ≟ n | admitOK pol is in af | eq
... | yes refl | true  | refl = refl , admitOK-freed pol is af , refl
... | yes _    | false | ()
... | no _     | _     | ()

-- a Conn-only move keeps All Q when Q survives each phase move (fail: running → failed, released → failedT) and the reset
conn-all : ∀ {Q : Inc → Set} {a c c′ pol}
         → (∀ {x f} → Q (mkInc x hsd f) → Q (mkInc x running f))
         → (∀ {x f} → Q (mkInc x hsd f) → Q (mkInc x closing f))
         → (∀ {x f} → Q (mkInc x running f) → Q (mkInc x failed f))
         → (∀ {x f} → Q (mkInc x released f) → Q (mkInc x failedT f))
         → (∀ {x ph} → Q (mkInc x ph false) → Q (mkInc x ph true))
         → cstep (ConnAct , conn) a pol c ≡ just c′ → All Q (live c) → All Q (live c′)
conn-all {a = run k} {cst n is ts} h₁ _ _ _ _ eq qs with map-split {f = λ is′ → cst n is′ ts} {x = movePh k hsd running is} eq
... | _ , eq₁ , refl = movePh-all eq₁ qs (λ _ → h₁)
conn-all {a = abort k} {cst n is ts} _ h₂ _ _ _ eq qs with map-split {f = λ is′ → cst n is′ ts} {x = movePh k hsd closing is} eq
... | _ , eq₁ , refl = movePh-all eq₁ qs (λ _ → h₂)
conn-all {a = fail k} {cst n is ts} _ _ h₃ h₃′ _ eq qs
  with map-split {f = λ is′ → cst n is′ (k ∷ ts)} {x = movePh k running failed is <∣> movePh k released failedT is} eq
... | _ , eq₁ , refl with alt-split {x = movePh k running failed is} eq₁
...   | inj₁ eq₂ = movePh-all eq₂ qs (λ _ → h₃)
...   | inj₂ eq₂ = movePh-all eq₂ qs (λ _ → h₃′)
conn-all {a = reset k} {cst n is ts} _ _ _ _ h₄ eq qs with map-split {f = λ is′ → cst n is′ ts} {x = freeIt k is} eq
... | _ , eq₁ , refl = freeIt-all eq₁ qs h₄
conn-all {a = close k} {cst n is ts} _ _ _ _ _ eq qs with map-split {f = λ is′ → cst n is′ ts} {x = closeIt k is} eq
... | _ , eq₁ , refl = closeIt-all eq₁ qs

-- a closing or failed incarnation does not run
no-runs : ∀ {p} → (p ≡ closing ⊎ p ≡ failed) → ¬ (p ≡ hsd ⊎ p ≡ running)
no-runs (inj₁ refl) (inj₁ ())
no-runs (inj₁ refl) (inj₂ ())
no-runs (inj₂ refl) (inj₁ ())
no-runs (inj₂ refl) (inj₂ ())

-- extending the queue keeps TrackI
track-push : ∀ {e q ph j i} → TrackI (gst e q ph) i → TrackI (gst e (q ∷ʳ j) ph) i
track-push t rn fe with t rn fe
... | inj₁ ex = inj₁ ex
... | inj₂ p  = inj₂ (∈-++⁺ˡ p)

------------------------------------------------------------------------
-- Preservation

-- a Conn-only move keeps a queue item's NcFreed, under any CM policy
nf-conn : ∀ {a c c′ pol} → cstep (ConnAct , conn) a pol c ≡ just c′ → ∀ {i} → NcFreed (live c) i → NcFreed (live c′) i
nf-conn {a} {c} {pol = pol} eq {nc _} p = conn-all {a = a} {c} {pol = pol} (λ q → q) (λ q → q) (λ q → q) (λ q → q) (λ _ _ → refl) eq p
nf-conn eq {mf _} _ = tt
nf-conn eq {mfK}  _ = tt

-- a handshake keeps FixI, under any CM policy
fix-hs : ∀ {a c c′ e q ph pol} → cstep (ℕ , hs) a pol c ≡ just c′ → GoodO c (gst e q ph) → FixI c (gst e q ph)
       → FixI c′ (gst e (q ∷ʳ nc a) ph)
fix-hs {a} {cst n is ts} {e = e} {q} {ph} {pol = pol} eq G F with hs-inv {a} {n} {is} {ts} {pol = pol} eq
... | refl , af , refl = record
  { nc-freed = ∷ʳ⁺ (All.zipWith nf (queue-ok G , nc-freed F)) new-freed
  ; sorted   = APP.++⁺ (sorted F) ([] ∷ []) (All.map lt-new (queue-ok G))
  ; entry-ok = λ x ex → let (lt , ab) = entry-ok F x ex in m<n⇒m<1+n lt , ∷ʳ⁺ ab lt
  ; track    = ∷ʳ⁺ (All.map (track-push {e} {q} {ph} {nc a}) (track F)) (λ _ _ → inj₂ (∈-++⁺ʳ q (here refl))) }
  where
    -- an older NewConnection k < a is unaffected by the new incarnation a
    nf : ∀ {i} → QOK (cst a is ts) i × NcFreed is i → NcFreed (is ∷ʳ mkInc a hsd false) i
    nf {nc k} (k<a , p) = ∷ʳ⁺ p (λ a<k → ⊥-elim (<-asym k<a a<k))
    nf {mf _} _ = tt
    nf {mfK}  _ = tt
    -- the new NewConnection a: the hs guard freed every older incarnation
    new-freed : All (λ i → iid i < a → freed i ≡ true) (is ∷ʳ mkInc a hsd false)
    new-freed = ∷ʳ⁺ (All.map (λ f _ → f) (allFreed-all af)) (λ a<a → ⊥-elim (<-irrefl refl a<a))
    -- every queued NewConnection is below a
    lt-new : ∀ {i} → QOK (cst a is ts) i → All (NcLt i) (nc a ∷ [])
    lt-new {nc _} lt = lt ∷ []
    lt-new {mf _} _  = tt ∷ []
    lt-new {mfK}  _  = tt ∷ []

-- a callback trace (from failed or failedT) keeps FixI, under any CM policy
fix-trace : ∀ {r v c c′ e q ph pol} → cstep ((ℕ × Maybe ℕ) , trace) (r , v) pol c ≡ just c′ → FixI c (gst e q ph)
          → FixI c′ (gst e (q ∷ʳ mf r) ph)
fix-trace {r} {c = cst n is ts} {e = e} {q} {ph} eq F
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh r failed closing is <∣> movePh r failedT closing is} eq
... | is′ , eq₁ , refl = record
  { nc-freed = ∷ʳ⁺ (All.map nf (nc-freed F)) tt
  ; sorted   = APP.++⁺ (sorted F) ([] ∷ []) (All.tabulate (λ {i} _ → ncLt-mf i ∷ []))
  ; entry-ok = λ x ex → let (lt , ab) = entry-ok F x ex in lt , ∷ʳ⁺ ab tt
  ; track    = All.map (track-push {e} {q} {ph} {mf r}) (trace-all eq₁ (track F) (λ _ _ rn → ⊥-elim (no-runs (inj₁ refl) rn))) }
  where
    -- the phase move keeps every NcFreed
    nf : ∀ {i} → NcFreed is i → NcFreed is′ i
    nf {nc _} p = trace-all eq₁ p (λ _ q → q)
    nf {mf _} _ = tt
    nf {mfK}  _ = tt

-- taking a NewConnection keeps FixI: an active entry would contradict the queued item's freedom
take-nc : ∀ {c e k q} → GoodO c (gst e (nc k ∷ q) idle) → FixI c (gst e (nc k ∷ q) idle) → FixI c (gst (just k) q idle)
take-nc {c} {e} {k} {q} G F = record
  { nc-freed = All.tail (nc-freed F)
  ; sorted   = AP.tail (sorted F)
  ; entry-ok = λ { _ refl → All.head (queue-ok G) , AP.head (sorted F) }
  ; track    = All.zipWith tr (track F , All.head (nc-freed F)) }
  where
    -- the item k itself becomes the entry; a still-active old entry is impossible
    tr : ∀ {i} → TrackI (gst e (nc k ∷ q) idle) i × (iid i < k → freed i ≡ true) → TrackI (gst (just k) q idle) i
    tr {i} (t , fr) rn fe with t rn fe
    ... | inj₂ (here eq) = inj₁ (cong just (sym (nc-inj eq)))
    ... | inj₂ (there p) = inj₂ p
    ... | inj₁ ex        = ⊥-elim (bool-clash (fr (All.head (proj₂ (entry-ok F (iid i) ex)))) fe)

-- taking a MuxFinished keeps FixI
take-mf : ∀ {c e r q} → FixI c (gst e (mf r ∷ q) idle) → FixI c (gst e q (await r))
take-mf {e = e} {r} {q} F = record
  { nc-freed = All.tail (nc-freed F)
  ; sorted   = AP.tail (sorted F)
  ; entry-ok = λ x ex → let (lt , ab) = entry-ok F x ex in lt , All.tail ab
  ; track    = All.map tr (track F) }
  where
    -- the removed head was not a NewConnection
    tr : ∀ {i} → TrackI (gst e (mf r ∷ q) idle) i → TrackI (gst e q (await r)) i
    tr t rn fe with t rn fe
    ... | inj₁ ex        = inj₁ ex
    ... | inj₂ (here ())
    ... | inj₂ (there p) = inj₂ p

-- every IG-only move keeps FixI
fix-gov : ∀ {c g g₁} a → GoodO c g → FixI c g → gstep (GovAct , gov) a FullFix g ≡ just g₁ → FixI c g₁
fix-gov {g = gst _ _ idle}                  promote _ F refl = F
fix-gov {g = gst _ _ (await _)}             promote _ _ ()
fix-gov {g = gst _ [] _}                    take _ _ ()
fix-gov {g = gst _ (_ ∷ _) (await _)}       take _ _ ()
fix-gov {g = gst nothing (nc _ ∷ _) idle}   take G F refl = take-nc G F
fix-gov {g = gst (just _) (nc _ ∷ _) idle}  take G F refl = take-nc G F
fix-gov {g = gst nothing (mf _ ∷ _) idle}   take _ F refl = take-mf F
fix-gov {g = gst (just _) (mf _ ∷ _) idle}  take _ F refl = take-mf F
fix-gov {g = gst _ (mfK ∷ _) idle}          take G _ refl = ⊥-elim (All.head (queue-ok G))
fix-gov {g = gst _ _ idle}                  tmo _ _ ()
fix-gov {g = gst _ _ (await _)}             tmo _ _ ()

-- the identity-checked unregister keeps FixI: it only clears a terminal mux, under any CM policy
fix-stopped : ∀ {t c c₁ e q pol} → cstep (ℕ , stopped) t pol c ≡ just c₁ → GoodO c (gst e q (await t))
            → FixI c (gst e q (await t)) → FixI c₁ (gst (unreg idChecked t e) q idle)
fix-stopped {t} {cst n is ts} {e = e} {q} eq G F with t ∈? ts | eq
... | no _   | ()
... | yes t∈ | refl = record
  { nc-freed = nc-freed F
  ; sorted   = sorted F
  ; entry-ok = λ x ex → entry-ok F x (unreg-just ex)
  ; track    = All.zipWith tr (track F , run-out (cinv G)) }
  where
    -- an active entry is not the terminal awaited mux, so it stays
    tr : ∀ {i} → TrackI (gst e q (await t)) i × (MuxAlive i → iid i ∉ ts) → TrackI (gst (unreg idChecked t e) q idle) i
    tr (tk , ro) rn fe with tk rn fe
    ... | inj₂ p  = inj₂ p
    ... | inj₁ ex = inj₁ (unreg-keeps ex (λ i≡t → ro (map₂ inj₁ rn) (subst (_∈ ts) (sym i≡t) t∈)))

-- every FullFix step keeps FixI
fixI-step : ∀ {c g c′ g′} {at : AnyTypes Ev} {a : proj₁ at}
          → GoodO c g → FixI c g → sstep at a FullFix c g ≡ just (c′ , g′) → FixI c′ g′
fixI-step {c} {g} {at = _ , conn} {a} G F eq with map-split {f = λ c′ → c′ , g} {x = cstep (ConnAct , conn) a (cmP FullFix) c} eq
... | _ , eqc , refl = record
  { nc-freed = All.map (nf-conn {a} {c} eqc) (nc-freed F)
  ; sorted   = sorted F
  ; entry-ok = λ x ex → let (lt , ab) = entry-ok F x ex
                        in <-≤-trans lt (proj₁ (proj₂ (conn-good {_ , conn} {a} {c} eqc (cinv G)))) , ab
  ; track    = conn-all {Q = TrackI g} {a} {c} (λ t _ fe → t (inj₁ refl) fe)
                        (λ _ rn → ⊥-elim (no-runs (inj₁ refl) rn))
                        (λ _ rn → ⊥-elim (no-runs (inj₂ refl) rn))
                        (λ _ → λ { (inj₁ ()) ; (inj₂ ()) })
                        (λ _ _ ()) eqc (track F) }
fixI-step {c} {g} {at = _ , gov} {a} G F eq with map-split {f = λ g′ → c , g′} {x = gstep (GovAct , gov) a FullFix g} eq
... | _ , eqg , refl = fix-gov a G F eqg
fixI-step {c} {gst e q ph} {at = _ , hs} {a} G F eq with zip-split eq
... | eqc , refl = fix-hs {a} {c} {pol = cmP FullFix} eqc G F
fixI-step {c} {gst e q ph} {at = _ , trace} {r , v} G F eq with zip-split eq
... | eqc , eqg with ≡-dec _≟_ v e | eqg
...   | no _  | ()
...   | yes _ | refl = fix-trace {r} {v} {c} {pol = cmP FullFix} eqc F
fixI-step {g = gst _ _ idle} {at = _ , stopped} _ _ eq with zip-split eq
... | _ , ()
fixI-step {c} {gst e q (await r)} {at = _ , stopped} {t} G F eq with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _     | ()
...   | yes refl | refl = fix-stopped {pol = cmP FullFix} eqc G F

fixI-step {g = gst _ _ idle} {at = _ , rel} _ _ eq with zip-split eq
... | _ , ()
fixI-step {g = gst _ _ (await _)} {at = _ , rel} _ _ eq with zip-split eq
... | _ , ()

-- GoodO and FixI hold along every FullFix run
fix-run : ∀ {c g s c′ g′} → GoodO c g → FixI c g → Steps FullFix c g s c′ g′ → FixI c′ g′
fix-run _ F done              = F
fix-run G F (step at a eq ss) = fix-run (goodO-step {at = at} {a} refl G eq) (fixI-step {at = at} {a} G F eq) ss

-- every reachable FullFix state satisfies GoodO and FixI
fix-reach : ∀ {c g} → Reach FullFix c g → GoodO c g × FixI c g
fix-reach (_ , ss) = goodO-run refl goodO₀ ss , fix-run goodO₀ fixI₀ ss

------------------------------------------------------------------------
-- No orphan, tracked

-- an active entry with a NewConnection at the queue head is impossible
-- relies on hs being atomic with the NewConnection enqueue (v2 spec §3, "S5"): if enqueues reorder, replace can orphan the active incarnation and keep cannot
take-nc-absurd : ∀ {c x k q} → FixI c (gst (just x) (nc k ∷ q) idle) → Active c x → ⊥
take-nc-absurd {x = x} F act with lookupAny (All.head (nc-freed F)) act
... | fr , e , _ , fe = bool-clash (fr (subst (_< _) (sym e) (All.head (proj₂ (entry-ok F x refl))))) fe

-- under FullFix no step drops the entry of an active incarnation
fix-keeps : ∀ {c e q ph x c′ g′} → GoodO c (gst e q ph) → FixI c (gst e q ph) → ∀ at a
          → sstep at a FullFix c (gst e q ph) ≡ just (c′ , g′) → e ≡ just x → Active c x → entry g′ ≡ just x
fix-keeps {c} {e} {q} {ph} _ _ (_ , conn) a eq ex _ with map-split {f = λ c′ → c′ , gst e q ph} {x = cstep (ConnAct , conn) a (cmP FullFix) c} eq
... | _ , _ , refl = ex
fix-keeps _ _ (_ , hs) _ eq ex _ with zip-split eq
... | _ , refl = ex
fix-keeps {e = e} _ _ (_ , trace) (_ , v) eq ex _ with zip-split eq
... | _ , eqg with ≡-dec _≟_ v e | eqg
...   | yes _ | refl = ex
...   | no _  | ()
fix-keeps {ph = idle} _ _ (_ , stopped) _ eq _ _ with zip-split eq
... | _ , ()
fix-keeps {ph = await r} {x} G _ (_ , stopped) t eq refl act with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _     | ()
...   | yes refl | refl with x ≟ t
...     | yes refl = ⊥-elim (active-out (cinv G) act (stopped-conn {pol = cmP FullFix} eqc))
...     | no _     = refl
fix-keeps {ph = idle}                 _ _ (_ , gov) promote refl ex _ = ex
fix-keeps {ph = await _}              _ _ (_ , gov) promote () _ _
fix-keeps {q = []}                    _ _ (_ , gov) take () _ _
fix-keeps {q = _ ∷ _} {ph = await _}  _ _ (_ , gov) take () _ _
fix-keeps {q = nc _ ∷ _} {ph = idle}  _ F (_ , gov) take refl refl act = ⊥-elim (take-nc-absurd F act)
fix-keeps {q = mf _ ∷ _} {ph = idle}  _ _ (_ , gov) take refl refl _ = refl
fix-keeps {q = mfK ∷ _} {ph = idle}   _ _ (_ , gov) take refl refl _ = refl
fix-keeps {ph = idle} _ _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
fix-keeps {ph = await _} _ _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
fix-keeps {ph = idle}                 _ _ (_ , gov) tmo () _ _
fix-keeps {ph = await _}              _ _ (_ , gov) tmo () _ _

FIX-no-orphan {g = gst _ _ _} R at a (_ , _ , _ , eq , ex , ne , act) =
  ne (fix-keeps (proj₁ (fix-reach R)) (proj₂ (fix-reach R)) at a eq ex act)

-- with an empty queue every active incarnation is the entry
tracked-at : ∀ {c g r} → FixI c g → queue g ≡ [] → Active c r → entry g ≡ just r
tracked-at {g = gst en _ _} F refl act with lookupAny (track F) act
... | tk , e , rn , fe with tk rn fe
...   | inj₁ ex = subst (λ y → en ≡ just y) e ex
...   | inj₂ ()

FIX-tracked R ph q≡ = ph , q≡ , λ _ act → tracked-at (proj₂ (fix-reach R)) q≡ act
