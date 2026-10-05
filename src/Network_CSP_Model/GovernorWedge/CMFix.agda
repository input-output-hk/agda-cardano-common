{-# OPTIONS --guardedness #-}

-- CF1/CF3/CF5: under the CM fix (1ccd17298) the field path's
-- duplicate handshake is refused (CF1), yet the never-run interleaving w0 — whose
-- only handshakes fire on an EMPTY live list — still wedges every CM-fixed mode,
-- including the real main (CF3, CF5). `steps-det` packages that `sstep` is a
-- function so a shared prefix forces a shared intermediate state.
-- CF2/CF2main: under the CM fix the awaited mux is never LiveRun. The
-- invariant `CMI` gives: at most one live incarnation is not closing, so a trace leaves
-- nothing runnable, and a FIFO order on the IG's items covers the lookup at handle time.
-- CF4: CM fix plus fix #2 — no wedge, and no orphan with the byKey unregister
-- (no identity check): the FIFO order puts every NewConnection before any MuxFinished
-- out of the running, so while the IG awaits, its entry cannot be an active incarnation.
module CSP.Examples.GovernorWedge.CMFix where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _<_; _≟_)
open import Data.Nat.Properties using (<-≤-trans; <-irrefl; m<n⇒m<1+n)
open import Data.Maybe using (Maybe; just; nothing; zip; _<∣>_)
open import Data.Maybe.Properties using (just-injective; ≡-dec)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Membership.DecPropositional _≟_ using (_∈?_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookupAny)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (∷ʳ⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs as AP
import Data.List.Relation.Unary.AllPairs.Properties as APP
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Process_Trees
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import CSP.Examples.GovernorWedge.Witness using (w0; cW0; gW0; clean)
open import CSP.Examples.GovernorWedge.FieldPath using (wF)
open import CSP.Examples.GovernorWedge.Wedged using (blocked-until; dead-steps; bW0; dW0)
open import CSP.Examples.GovernorWedge.Invariant
  using (CInv; uniq; ran-fresh; Runs; conn-good; trace-in; hs-lt; movePh-all; trace-all; movePh-any; movePh-others; own-safe; own-live-sys)
open import CSP.Examples.GovernorWedge.FullFix using (conn-all; no-runs; hs-inv)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; traces)

-- the field prefix: B handshakes, is registered, runs, and is reset by the peer
cf-prefix : List (Event√ U)
cf-prefix = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ []

-- Conn after the prefix (identical under both CM policies)
cF4 : CState
cF4 = cst 1 (mkInc 0 running true ∷ []) []

-- IG after the prefix (identical under both CM policies)
gF4 : GState
gF4 = gst (just 0) [] idle

-- an hs move reduces via any CM policy equal to the mode's own (generalises FieldPath's sstep-hs-pin)
sstep-hs-eq : ∀ {m} {a : ℕ} {c g pol} → cmP m ≡ pol
            → sstep (ℕ , hs) a m c g ≡ zip (cstep (ℕ , hs) a pol c) (gstep (ℕ , hs) a m g)
sstep-hs-eq {m} {a} {c} {g} eq = cong (λ pol′ → zip (cstep (ℕ , hs) a pol′ c) (gstep (ℕ , hs) a m g)) eq

-- CF1: under any mode with the CM fix, the prefix is reachable and C's handshake is then refused
CF1 : ∀ m → cmP m ≡ cmFix → Steps m c₀ g₀ cf-prefix cF4 gF4 × sstep (ℕ , hs) 1 m cF4 gF4 ≡ nothing
CF1 m p =
  step (ℕ , hs) 0 (trans (sstep-hs-eq {m} {0} {c₀} {g₀} p) refl)
  (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl done)))
  , trans (sstep-hs-eq {m} {1} {cF4} {gF4} p) refl

-- Steps is deterministic: sstep is a function, so a shared trace forces a shared final state
steps-det : ∀ {m c g s c₁ g₁ c₂ g₂} → Steps m c g s c₁ g₁ → Steps m c g s c₂ g₂ → c₁ ≡ c₂ × g₁ ≡ g₂
steps-det done done = refl , refl
steps-det (step at a eq ss) (step .at .a eq₁ ss₁) with just-injective (trans (sym eq) eq₁)
... | refl = steps-det ss ss₁

-- CF1 at process level: the field interleaving is not a trace of any CM-fixed system
CF1-trace : ∀ m → cmP m ≡ cmFix → ¬ traces (Sys m) wF
CF1-trace m p (_ , tr) with run-inv tr
... | _ , _ , _ , step (ℕ , hs) 0 eq0
                     (step (GovAct , gov) take eq1
                     (step (ConnAct , conn) (run 0) eq2
                     (step (ConnAct , conn) (reset 0) eq3
                     (step (ℕ , hs) 1 eq4 _))))
  with steps-det (step (ℕ , hs) 0 eq0
                   (step (GovAct , gov) take eq1
                   (step (ConnAct , conn) (run 0) eq2
                   (step (ConnAct , conn) (reset 0) eq3 done))))
                 (proj₁ (CF1 m p))
... | refl , refl with trans (sym eq4) (proj₂ (CF1 m p))
...   | ()

-- CF3: the never-run interleaving still reaches the wedge under the leios fix
CF3-reach : Steps AsBuiltCM c₀ g₀ w0 cW0 gW0
CF3-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl done)))))))))

-- CF3: the never-run interleaving still reaches the wedge on the real main
CF3main-reach : Steps MainReal c₀ g₀ w0 cW0 gW0
CF3main-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl done)))))))))

-- CF3: the wedge is permanent under the leios fix, exactly as for the pinned CM
CF3-permanent : ∀ {s W′} → SysAt AsBuiltCM cW0 gW0 ⟹⟨ s ⟩ W′ → All (_≢ GV promote) s
CF3-permanent st with run-inv st
... | _ , _ , _ , ss = blocked-until (bW0 refl) ss (dead-steps dW0 ss)

-- CF3: the wedge is permanent on the real main
CF3main-permanent : ∀ {s W′} → SysAt MainReal cW0 gW0 ⟹⟨ s ⟩ W′ → All (_≢ GV promote) s
CF3main-permanent st with run-inv st
... | _ , _ , _ , ss = blocked-until (bW0 refl) ss (dead-steps dW0 ss)

-- CF5: the real main refuses the observed path yet keeps the never-run wedge
CF5 : ¬ traces (Sys MainReal) wF × traces (Sys MainReal) w0
CF5 = CF1-trace MainReal refl , (_ , run-intro CF3main-reach)

------------------------------------------------------------------------
-- CF2: under the CM fix the IG never waits on a live mux

-- CF2: Ramsay's SysFix invariant in the form that holds — under the CM fix the awaited mux is never a live, runnable incarnation (CF3 is its non-vacuity control: the wedge survives, on a dead mux)
CF2 : ∀ {c g r} → Reach AsBuiltCM c g → gphase g ≡ await r → ¬ LiveRun c r
-- CF2 on the real main (lookup at handle time plus the CM fix)
CF2main : ∀ {c g r} → Reach MainReal c g → gphase g ≡ await r → ¬ LiveRun c r

-- the CM-fixed modes with the pinned IG's other switches, for any enqueue policy (release not modelled)
CMMode : EnqPolicy → Mode
CMMode ep = mode ep keep byKey false cmFix false

-- no live incarnation with id k can still run, and k is not a future id
NR : CState → ℕ → Set
NR c k = k < next c × All (λ i → iid i ≡ k → ¬ Runs i) (live c)

-- the IG's items in order: the entry (as a NewConnection) in front of the queue
view : GState → List Item
view (gst nothing  q _) = q
view (gst (just x) q _) = nc x ∷ q

-- a queued item's invariant: NewConnection ids are not future ids, awaited refs cannot run
QI : CState → Item → Set
QI c (nc k) = k < next c
QI c (mf v) = NR c v
QI c mfK    = ⊤

-- a NewConnection cannot run (used for items queued before a MuxFinished)
NcNR : CState → Item → Set
NcNR c (nc k) = NR c k
NcNR c (mf _) = ⊤
NcNR c mfK    = ⊤

-- FIFO order: every NewConnection before a MuxFinished (with or without payload) cannot run
KR : CState → Item → Item → Set
KR c i (nc _) = ⊤
KR c i (mf _) = NcNR c i
KR c i mfK    = NcNR c i

-- the IG half of CMI
record GI (c : CState) (g : GState) : Set where
  field
    itemsG : All (QI c) (view g)
    orderG : AllPairs (KR c) (view g)
    awaitG : ∀ r → gphase g ≡ await r → NR c r
    awaitE : ∀ r x → gphase g ≡ await r → entry g ≡ just x → NR c x
open GI

-- the phases only the release reaches: released and failedT
RelPh : IPhase → Set
RelPh released = ⊤
RelPh failedT  = ⊤
RelPh _        = ⊥

-- the CM-fix invariant: at most one live incarnation (id opn) is not closing, none is released or failedT (relP false), plus the IG half
record CMI (c : CState) (g : GState) : Set where
  field
    cinvM : CInv c
    opn   : ℕ
    open1 : All (λ i → iph i ≡ closing ⊎ iid i ≡ opn) (live c)
    norel : All (λ i → ¬ RelPh (iph i)) (live c)
    gi    : GI c g
open CMI

-- the initial state satisfies CMI
cmi₀ : CMI c₀ g₀
cmi₀ = record { cinvM = record { failed-in = [] ; run-out = [] ; fresh = [] ; ran-fresh = [] ; uniq = [] }
              ; opn = 0 ; open1 = [] ; norel = [] ; gi = record { itemsG = [] ; orderG = [] ; awaitG = λ _ () ; awaitE = λ _ _ () } }

------------------------------------------------------------------------
-- Conn-side lemmas

-- allClosing as an All, when no incarnation is released or failedT
allClosing-all : ∀ {is} → All (λ i → ¬ RelPh (iph i)) is → allClosing is ≡ true → All (λ i → iph i ≡ closing) is
allClosing-all {[]} _ _ = []
allClosing-all {mkInc _ closing _ ∷ is} (_ ∷ nr) eq = refl ∷ allClosing-all nr eq
allClosing-all {mkInc _ released _ ∷ _} (n ∷ _) _ = ⊥-elim (n tt)
allClosing-all {mkInc _ failedT _ ∷ _} (n ∷ _) _ = ⊥-elim (n tt)
allClosing-all {mkInc _ hsd _ ∷ _} _ ()
allClosing-all {mkInc _ running _ ∷ _} _ ()
allClosing-all {mkInc _ failed _ ∷ _} _ ()

-- admitOK under the fix entails allClosing
admitOK-closing : ∀ is → admitOK cmFix is ≡ true → allClosing is ≡ true
admitOK-closing is eq with allFreed is | eq
... | true  | e = e
... | false | ()

-- the CM-fixed handshake's guard: every live incarnation was closing
hs-closing : ∀ {a n is ts c′} → cstep (ℕ , hs) a cmFix (cst n is ts) ≡ just c′ → allClosing is ≡ true
hs-closing {a} {n} {is} eq with a ≟ n | admitOK cmFix is in ok | eq
... | yes refl | true  | refl = admitOK-closing is ok
... | yes _    | false | ()
... | no _     | _     | ()

-- after a CM-fixed handshake the new incarnation is the only one not closing (no incarnation was released or failedT)
hs-open : ∀ {a c c′} → All (λ i → ¬ RelPh (iph i)) (live c) → cstep (ℕ , hs) a cmFix c ≡ just c′
        → All (λ i → iph i ≡ closing ⊎ iid i ≡ a) (live c′)
hs-open {a} {cst n is ts} nr eq with hs-closing {a} {n} {is} {ts} eq | hs-inv {a} {n} {is} {ts} {pol = cmFix} eq
... | ac | refl , _ , refl = ∷ʳ⁺ (All.map inj₁ (allClosing-all nr ac)) (inj₂ refl)


-- a Conn move keeps NR: next only grows and phases only move away from running (hs adds the fresh id; rel to released/failedT)
nr-mono : ∀ {at a pol c c′ k} → cstep at a pol c ≡ just c′ → CInv c → NR c k → NR c′ k
nr-mono {_ , gov} ()
nr-mono {_ , stopped} {t} {c = cst _ _ ts} eq _ nr with t ∈? ts | eq
... | yes _ | refl = nr
... | no _  | ()
nr-mono {_ , hs} {a} {pol} {cst n is ts} eq _ (lt , nr) with hs-inv {a} {n} {is} {ts} {pol = pol} eq
... | refl , _ , refl = m<n⇒m<1+n lt , ∷ʳ⁺ nr (λ e _ → <-irrefl (sym e) lt)
nr-mono {_ , conn} {a} {pol} {c} {k = k} eq ci (lt , nr) =
  <-≤-trans lt (proj₁ (proj₂ (conn-good {_ , conn} {a} {c} {pol = pol} eq ci)))
  , conn-all {Q = λ i → iid i ≡ k → ¬ Runs i} {a} {c} {pol = pol}
             (λ q e _ → q e (inj₁ refl)) (λ _ _ → no-runs (inj₁ refl)) (λ _ _ → no-runs (inj₂ refl)) (λ _ _ → λ { (inj₁ ()) ; (inj₂ ()) })
             (λ q → q) eq nr
nr-mono {_ , trace} {r , _} {c = cst n is ts} eq _ (lt , nr)
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh r failed closing is <∣> movePh r failedT closing is} eq
... | _ , eq₁ , refl = lt , trace-all eq₁ nr (λ _ _ _ → no-runs (inj₁ refl))
nr-mono {_ , rel} {_ , b} {c = cst n is ts} eq _ (lt , nr) with map-split {f = λ is′ → cst n is′ ts} {x = relLive b (newest is) is} eq
... | _ , eq₁ , refl with rel-split {b} {newest is} eq₁
...   | inj₁ (_ , eq₂)               = lt , movePh-all eq₂ nr (λ _ _ _ → λ { (inj₁ ()) ; (inj₂ ()) })
...   | inj₂ (inj₁ (_ , eq₂))        = lt , movePh-all eq₂ nr (λ _ _ _ → λ { (inj₁ ()) ; (inj₂ ()) })
...   | inj₂ (inj₂ (inj₁ (_ , eq₂))) = lt , movePh-all eq₂ nr (λ _ _ _ → λ { (inj₁ ()) ; (inj₂ ()) })
...   | inj₂ (inj₂ (inj₂ refl))      = lt , nr

-- the quiet argument for a trace's move of r from a non-closing phase p (failed or failedT) to closing
quiet-mv : ∀ {r p n is is′ ts o} → p ≢ closing → movePh r p closing is ≡ just is′ → CInv (cst n is ts)
         → All (λ i → iph i ≡ closing ⊎ iid i ≡ o) is
         → All (λ i → iph i ≡ closing ⊎ iid i ≡ o) is′ × All (λ i → ¬ Runs i) is′
quiet-mv {r} {p} {is′ = is′} {o = o} p≢cl eq₁ ci op = op′ , All.zipWith (λ {i} → quiet {i}) (op′ , movePh-others eq₁ (uniq ci))
  where
    -- the open-incarnation invariant after the p → closing move
    op′ : All (λ i → iph i ≡ closing ⊎ iid i ≡ o) is′
    op′ = movePh-all eq₁ op (λ _ _ → inj₁ refl)
    -- the tracer was in p, hence not closing, hence the open one
    r≡o : r ≡ o
    r≡o with lookupAny op (movePh-any eq₁)
    ... | inj₁ cl , _ , fl = ⊥-elim (p≢cl (trans (sym fl) cl))
    ... | inj₂ e  , e′ , _ = trans (sym e′) e
    -- every incarnation is closing, or carries the tracer's id and is then the (now closing) tracer
    quiet : ∀ {i} → (iph i ≡ closing ⊎ iid i ≡ o) × (iph i ≢ closing → iid i ≢ r) → ¬ Runs i
    quiet (inj₁ cl , _) = no-runs (inj₁ cl)
    quiet {i} (inj₂ e , ot) with iph i ≟ᴾ closing
    ... | yes cl = no-runs (inj₁ cl)
    ... | no ncl = ⊥-elim (ot ncl (trans e (sym r≡o)))

-- a CM-fixed trace: the tracer was the open incarnation, so afterwards no live incarnation can run
trace-quiet : ∀ {r v c c′ o} → cstep ((ℕ × Maybe ℕ) , trace) (r , v) cmFix c ≡ just c′ → CInv c
            → All (λ i → iph i ≡ closing ⊎ iid i ≡ o) (live c)
            → All (λ i → iph i ≡ closing ⊎ iid i ≡ o) (live c′) × All (λ i → ¬ Runs i) (live c′)
trace-quiet {r} {c = cst n is ts} eq ci op
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh r failed closing is <∣> movePh r failedT closing is} eq
... | _ , eq₁ , refl with alt-split {x = movePh r failed closing is} eq₁
...   | inj₁ eq₂ = quiet-mv (λ ()) eq₂ ci op
...   | inj₂ eq₂ = quiet-mv (λ ()) eq₂ ci op

-- Conn under stopped does not move
stopped-same : ∀ {t pol c c′} → cstep (ℕ , stopped) t pol c ≡ just c′ → c′ ≡ c
stopped-same {t} {c = cst _ _ ts} eq with t ∈? ts | eq
... | yes _ | refl = refl
... | no _  | ()

-- no Conn move other than the release makes an incarnation released or failedT (fail reaches failedT only from released)
norel-mono : ∀ {at a pol c c′} → cstep at a pol c ≡ just c′ → at ≢ ((ℕ × Bool) , rel)
           → All (λ i → ¬ RelPh (iph i)) (live c) → All (λ i → ¬ RelPh (iph i)) (live c′)
norel-mono {_ , gov} ()
norel-mono {_ , stopped} {pol = pol} {c} eq _ nr with stopped-same {pol = pol} {c = c} eq
... | refl = nr
norel-mono {_ , hs} {a} {pol} {cst n is ts} eq _ nr with hs-inv {a} {n} {is} {ts} {pol = pol} eq
... | refl , _ , refl = ∷ʳ⁺ nr (λ ())
norel-mono {_ , conn} {a} {pol} {c} eq _ nr =
  conn-all {Q = λ i → ¬ RelPh (iph i)} {a} {c} {pol = pol} (λ _ ()) (λ _ ()) (λ _ ()) (λ q → q) (λ q → q) eq nr
norel-mono {_ , trace} {r , _} {c = cst n is ts} eq _ nr
  with map-split {f = λ is′ → cst n is′ ts} {x = movePh r failed closing is <∣> movePh r failedT closing is} eq
... | _ , eq₁ , refl = trace-all eq₁ nr (λ _ _ ())
norel-mono {_ , rel} _ ne _ = ⊥-elim (ne refl)

------------------------------------------------------------------------
-- IG-side lemmas

-- a queued item's invariant survives a Conn move
qi-mono : ∀ {at a pol c c′} → cstep at a pol c ≡ just c′ → CInv c → ∀ {i} → QI c i → QI c′ i
qi-mono {at} {a} {pol} {c} eq ci {nc _} lt = <-≤-trans lt (proj₁ (proj₂ (conn-good {at} {a} {c} {pol = pol} eq ci)))
qi-mono {at} eq ci {mf _} nr = nr-mono {at} eq ci nr
qi-mono _ _ {mfK} _ = tt

-- the FIFO order survives a Conn move
kr-mono : ∀ {at a pol c c′} → cstep at a pol c ≡ just c′ → CInv c → ∀ {i j} → KR c i j → KR c′ i j
kr-mono _  _  {j = nc _}        _  = tt
kr-mono {at} eq ci {nc _} {mf _} nr = nr-mono {at} eq ci nr
kr-mono _  _  {mf _}  {mf _}    _  = tt
kr-mono _  _  {mfK}   {mf _}    _  = tt
kr-mono {at} eq ci {nc _} {mfK} nr = nr-mono {at} eq ci nr
kr-mono _  _  {mf _}  {mfK}     _  = tt
kr-mono _  _  {mfK}   {mfK}     _  = tt

-- the IG half survives a Conn move
gi-mono : ∀ {at a pol c c′ g} → cstep at a pol c ≡ just c′ → CInv c → GI c g → GI c′ g
gi-mono {at} {a} {pol} {c} {c′} eq ci G =
  record { itemsG = All.map (λ {i} → qi-mono {at} {a} {pol} {c} {c′} eq ci {i}) (itemsG G)
         ; orderG = AP.map (λ {i} {j} → kr-mono {at} {a} {pol} {c} {c′} eq ci {i} {j}) (orderG G)
         ; awaitG = λ r p → nr-mono {at} {a} {pol} {c} {c′} eq ci (awaitG G r p)
         ; awaitE = λ r x p e → nr-mono {at} {a} {pol} {c} {c′} eq ci (awaitE G r x p e) }

-- enqueueing extends the view at the end
view-push : ∀ e q ph i → view (gst e (q ∷ʳ i) ph) ≡ view (gst e q ph) ∷ʳ i
view-push nothing  _ _ _ = refl
view-push (just _) _ _ _ = refl

-- enqueueing an OK item, ordered after every earlier item, keeps the IG half
gi-push : ∀ {c e q ph i} → GI c (gst e q ph) → QI c i → All (λ j → KR c j i) (view (gst e q ph)) → GI c (gst e (q ∷ʳ i) ph)
gi-push {c} {e} {q} {ph} {i} G qi kr = record { itemsG = its ; orderG = ord ; awaitG = awaitG G ; awaitE = awaitE G }
  where
    -- the items, transported along view-push
    its : All (QI c) (view (gst e (q ∷ʳ i) ph))
    its rewrite view-push e q ph i = ∷ʳ⁺ (itemsG G) qi
    -- the order, transported along view-push
    ord : AllPairs (KR c) (view (gst e (q ∷ʳ i) ph))
    ord rewrite view-push e q ph i = APP.++⁺ (orderG G) ([] ∷ []) (All.map (_∷ []) kr)

-- with nothing runnable, every OK item's NewConnection cannot run
ncnr : ∀ {c} → All (λ i → ¬ Runs i) (live c) → ∀ {i} → QI c i → NcNR c i
ncnr nr {nc _} lt = lt , All.map (λ n _ → n) nr
ncnr _  {mf _} _  = tt
ncnr _  {mfK}  _  = tt

-- a callback trace's enqueue keeps the IG half, once nothing live can run
gi-trace : ∀ ep {c r e q ph} → All (λ i → ¬ Runs i) (live c) → r < next c → GI c (gst e q ph) → GI c (gst e (enq ep r e q) ph)
gi-trace atTrace {e = nothing} _  _  G = G
gi-trace atTrace {c} {e = just _} nr _  G = gi-push G (All.head (itemsG G) , All.map (λ n _ → n) nr) (All.map (λ {i} → ncnr {c} nr {i}) (itemsG G))
gi-trace atHandle {c}            nr _  G = gi-push G tt (All.map (λ {i} → ncnr {c} nr {i}) (itemsG G))
gi-trace own      {c}            nr lt G = gi-push G (lt , All.map (λ n _ → n) nr) (All.map (λ {i} → ncnr {c} nr {i}) (itemsG G))

-- the unregister clears the entry and returns to idle
gi-clear : ∀ {c e q ph} → GI c (gst e q ph) → GI c (gst nothing q idle)
gi-clear {e = nothing} G = record { itemsG = itemsG G ; orderG = orderG G ; awaitG = λ _ () ; awaitE = λ _ _ () }
gi-clear {e = just _}  G = record { itemsG = All.tail (itemsG G) ; orderG = AP.tail (orderG G) ; awaitG = λ _ () ; awaitE = λ _ _ () }

-- drop the second item of an All
all-drop₂ : ∀ {P : Item → Set} {x y q} → All P (x ∷ y ∷ q) → All P (x ∷ q)
all-drop₂ (px ∷ _ ∷ ps) = px ∷ ps

-- drop the second item of an AllPairs
ap-drop₂ : ∀ {R : Item → Item → Set} {x y q} → AllPairs R (x ∷ y ∷ q) → AllPairs R (x ∷ q)
ap-drop₂ ((_ ∷ px) ∷ (_ ∷ r)) = px ∷ r

-- every IG-only move keeps the IG half; take mfK reads the entry's safety off the FIFO order
gi-gov : ∀ {ep c g g₁} a → GI c g → gstep (GovAct , gov) a (CMMode ep) g ≡ just g₁ → GI c g₁
gi-gov {g = gst _ _ idle}                  promote G refl = G
gi-gov {g = gst _ _ (await _)}             promote _ ()
gi-gov {g = gst _ [] _}                    take _ ()
gi-gov {g = gst _ (_ ∷ _) (await _)}       take _ ()
gi-gov {g = gst nothing (nc _ ∷ _) idle}   take G refl = record { itemsG = itemsG G ; orderG = orderG G ; awaitG = λ _ () ; awaitE = λ _ _ () }
gi-gov {g = gst (just _) (nc _ ∷ _) idle}  take G refl = record { itemsG = all-drop₂ (itemsG G) ; orderG = ap-drop₂ (orderG G) ; awaitG = λ _ () ; awaitE = λ _ _ () }
gi-gov {g = gst nothing (mf _ ∷ _) idle}   take G refl = record { itemsG = All.tail (itemsG G) ; orderG = AP.tail (orderG G)
                                                                ; awaitG = λ { _ refl → All.head (itemsG G) } ; awaitE = λ _ _ _ () }
gi-gov {g = gst (just _) (mf _ ∷ _) idle}  take G refl = record { itemsG = all-drop₂ (itemsG G) ; orderG = ap-drop₂ (orderG G)
                                                                ; awaitG = λ { _ refl → All.head (All.tail (itemsG G)) }
                                                                ; awaitE = λ { _ _ refl refl → All.head (AP.head (orderG G)) } }
gi-gov {g = gst (just _) (mfK ∷ _) idle}   take G refl = record { itemsG = all-drop₂ (itemsG G) ; orderG = ap-drop₂ (orderG G)
                                                                ; awaitG = λ { _ refl → All.head (AP.head (orderG G)) }
                                                                ; awaitE = λ { _ _ refl refl → All.head (AP.head (orderG G)) } }
gi-gov {g = gst nothing (mfK ∷ _) idle}    take G refl = record { itemsG = All.tail (itemsG G) ; orderG = AP.tail (orderG G) ; awaitG = λ _ () ; awaitE = λ _ _ () }
gi-gov {g = gst _ _ idle}                  tmo _ ()
gi-gov {g = gst _ _ (await _)}             tmo _ ()

------------------------------------------------------------------------
-- Preservation and CF2

-- every composite step of a CM-fixed mode keeps CMI
cmi-step : ∀ {ep c g c′ g′} {at : AnyTypes Ev} {a : proj₁ at} → CMI c g → sstep at a (CMMode ep) c g ≡ just (c′ , g′) → CMI c′ g′
cmi-step {c = c} {g} {at = _ , conn} {a} I eq with map-split {f = λ c′ → c′ , g} {x = cstep (ConnAct , conn) a cmFix c} eq
... | _ , eqc , refl = record
  { cinvM = proj₁ (conn-good {_ , conn} {a} {c} {pol = cmFix} eqc (cinvM I))
  ; opn   = opn I
  ; open1 = conn-all {Q = λ i → iph i ≡ closing ⊎ iid i ≡ opn I} {a} {c} {pol = cmFix}
                     (λ { (inj₁ ()) ; (inj₂ e) → inj₂ e }) (λ _ → inj₁ refl) (λ { (inj₁ ()) ; (inj₂ e) → inj₂ e })
                     (λ { (inj₁ ()) ; (inj₂ e) → inj₂ e }) (λ q → q) eqc (open1 I)
  ; norel = norel-mono {_ , conn} {a} {cmFix} {c} eqc (λ ()) (norel I)
  ; gi    = gi-mono {_ , conn} {a} {cmFix} {c} eqc (cinvM I) (gi I) }
cmi-step {ep} {c} {g} {at = _ , gov} {a} I eq with map-split {f = λ g′ → c , g′} {x = gstep (GovAct , gov) a (CMMode ep) g} eq
... | _ , eqg , refl = record { cinvM = cinvM I ; opn = opn I ; open1 = open1 I ; norel = norel I ; gi = gi-gov {ep} a (gi I) eqg }
cmi-step {c = c} {gst e q ph} {at = _ , hs} {a} I eq with zip-split eq
... | eqc , refl = record
  { cinvM = proj₁ (conn-good {_ , hs} {a} {c} {pol = cmFix} eqc (cinvM I))
  ; opn   = a
  ; open1 = hs-open {a} {c} (norel I) eqc
  ; norel = norel-mono {_ , hs} {a} {cmFix} {c} eqc (λ ()) (norel I)
  ; gi    = gi-push (gi-mono {_ , hs} {a} {cmFix} {c} eqc (cinvM I) (gi I)) (hs-lt {a} {c} {pol = cmFix} eqc) (All.tabulate λ _ → tt) }
cmi-step {ep} {c} {gst e q ph} {at = _ , trace} {r , v} I eq with zip-split eq
... | eqc , eqg with ≡-dec _≟_ v e | eqg
...   | no _    | ()
...   | yes refl | refl = record
  { cinvM = proj₁ cg
  ; opn   = opn I
  ; open1 = proj₁ tq
  ; norel = norel-mono {_ , trace} {r , v} {cmFix} {c} eqc (λ ()) (norel I)
  ; gi    = gi-trace ep (proj₂ tq) lt (gi-mono {_ , trace} {r , v} {cmFix} {c} eqc (cinvM I) (gi I)) }
  where
    -- the Conn half of the trace step
    cg = conn-good {_ , trace} {r , v} {c} {pol = cmFix} eqc (cinvM I)
    -- after the trace nothing live can run
    tq = trace-quiet {r} {v} {c} eqc (cinvM I) (open1 I)
    -- the tracer's id is not a future id
    lt = <-≤-trans (All.lookup (ran-fresh (cinvM I)) (trace-in {r} {v} {c} {pol = cmFix} eqc (cinvM I))) (proj₁ (proj₂ cg))
cmi-step {g = gst _ _ idle} {at = _ , stopped} _ eq with zip-split eq
... | _ , ()
cmi-step {c = c} {gst e q (await r)} {at = _ , stopped} {t} I eq with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _  | ()
...   | yes _ | refl with stopped-same {pol = cmFix} {c = c} eqc
...     | refl = record { cinvM = cinvM I ; opn = opn I ; open1 = open1 I ; norel = norel I ; gi = gi-clear (gi I) }
cmi-step {g = gst _ _ idle} {at = _ , rel} _ eq with zip-split eq
... | _ , ()
cmi-step {g = gst _ _ (await _)} {at = _ , rel} _ eq with zip-split eq
... | _ , ()

-- CMI holds along every run of a CM-fixed mode
cmi-run : ∀ {ep c g s c′ g′} → CMI c g → Steps (CMMode ep) c g s c′ g′ → CMI c′ g′
cmi-run I done              = I
cmi-run {ep} I (step at a eq ss) = cmi-run {ep} (cmi-step {ep} {at = at} {a} I eq) ss

-- the awaited mux of a CMI state is not a live runnable incarnation
cf2-at : ∀ {c g r} → CMI c g → gphase g ≡ await r → ¬ LiveRun c r
cf2-at I ph lr with awaitG (gi I) _ ph
... | _ , nr = let (f , e , rn) = lookupAny nr lr in f e rn

CF2 (_ , ss) = cf2-at (cmi-run {atTrace} cmi₀ ss)

CF2main (_ , ss) = cf2-at (cmi-run {atHandle} cmi₀ ss)

------------------------------------------------------------------------
-- CF4: the CM fix plus fix #2 (own mux id): no wedge, no orphan

-- CF4: every awaited mux is terminal
CF4-safe : ∀ {c g} → Reach CarryMuxCM c g → ∀ r → gphase g ≡ await r → r ∈ ran c
-- CF4: promote, or stopped r then promote, is always a trace
CF4-live-sys : ∀ {s W} → Sys CarryMuxCM ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
-- CF4: no reachable orphaning step; the mode's unregister is byKey, so no identity check is used
CF4-no-orphan : ∀ {c g} → Reach CarryMuxCM c g → ∀ at a → ¬ OrphanStep CarryMuxCM c g at a

CF4-safe = own-safe refl

CF4-live-sys = own-live-sys refl

-- an incarnation that cannot run is not active
nr-inactive : ∀ {c x} → NR c x → ¬ Active c x
nr-inactive (_ , nr) act = let (f , e , rn , _) = lookupAny nr act in f e rn

-- under a CM-fixed keep/byKey mode no step drops an active entry: only stopped clears it, and then the entry cannot run
cm-keeps : ∀ {ep c e q ph x c′ g′} → CMI c (gst e q ph) → ∀ at a
         → sstep at a (CMMode ep) c (gst e q ph) ≡ just (c′ , g′) → e ≡ just x → Active c x → entry g′ ≡ just x
cm-keeps {ep} {c} {e} {q} {ph} _ (_ , conn) a eq ex _ with map-split {f = λ c′ → c′ , gst e q ph} {x = cstep (ConnAct , conn) a cmFix c} eq
... | _ , _ , refl = ex
cm-keeps _ (_ , hs) _ eq ex _ with zip-split eq
... | _ , refl = ex
cm-keeps {e = e} _ (_ , trace) (_ , v) eq ex _ with zip-split eq
... | _ , eqg with ≡-dec _≟_ v e | eqg
...   | yes _ | refl = ex
...   | no _  | ()
cm-keeps {ph = idle} _ (_ , stopped) _ eq _ _ with zip-split eq
... | _ , ()
cm-keeps {c = c} {ph = await r} {x} I (_ , stopped) t eq refl act with zip-split eq
... | _ , eqg with t ≟ r | eqg
...   | no _  | ()
...   | yes _ | refl = ⊥-elim (nr-inactive {c} {x} (awaitE (gi I) r x refl refl) act)
cm-keeps {ph = idle}                 _ (_ , gov) promote refl ex _ = ex
cm-keeps {ph = await _}              _ (_ , gov) promote () _ _
cm-keeps {q = []}                    _ (_ , gov) take () _ _
cm-keeps {q = _ ∷ _} {ph = await _}  _ (_ , gov) take () _ _
cm-keeps {q = nc _ ∷ _} {ph = idle}  _ (_ , gov) take refl refl _ = refl
cm-keeps {q = mf _ ∷ _} {ph = idle}  _ (_ , gov) take refl refl _ = refl
cm-keeps {q = mfK ∷ _} {ph = idle}   _ (_ , gov) take refl refl _ = refl
cm-keeps {ph = idle} _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
cm-keeps {ph = await _} _ (_ , rel) _ eq _ _ with zip-split eq
... | _ , ()
cm-keeps {ph = idle}                 _ (_ , gov) tmo () _ _
cm-keeps {ph = await _}              _ (_ , gov) tmo () _ _

CF4-no-orphan {g = gst _ _ _} (_ , ss) at a (_ , _ , _ , eq , ex , ne , act) = ne (cm-keeps {own} (cmi-run {own} cmi₀ ss) at a eq ex act)

-- CF4 control: under CarryMuxCM the clean episode awaits terminal mux 0 (own item mf 0)
clean-CarryMuxCM : Steps CarryMuxCM c₀ g₀ clean (cst 1 (mkInc 0 closing false ∷ []) (0 ∷ [])) (gst (just 0) [] (await 0))
clean-CarryMuxCM =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (fail 0) refl (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl
  (step (GovAct , gov) take refl done)))))
