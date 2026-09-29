{-# OPTIONS --guardedness #-}

-- RL0/RL1/RL3 (v4 spec §5): the release interleaving. B is released by the IG while
-- running (rel), then reset by the peer (its four-tuple frees while its mux stays
-- alive per LiveMux); the fixed CM now admits a redial as C since the released,
-- freed B counts as closing. C runs and is tracked; B's late lookup then makes the
-- IG await live C (RL1, on both the as-built lookup policy and the real main). Under
-- the CM fix plus fix #2 (own mux id), C's own enqueued item instead makes the IG
-- await B's already-terminal mux 0 while C is the entry, and B's `stopped` orphans
-- active C exactly as fix #2 alone did in the field path (RL3, `FieldPath.O2`).
-- RL2: the release wedge lasts while C lives. RL3-safe/RL3-live-sys: fix #2 alone still has
-- no wedge. RL4: adding the identity check restores safety, liveness and no-orphan (the
-- release itself, the IG's deliberate teardown, excluded; `rel-orphans` shows it must be).
-- v4.1a: the release is the general atomic one (Model `relLive`: by ConnectionId on the newest
-- incarnation, CommitTr or UnsupportedState, failed → failedT); the runs here use CommitTr (`REL 0 true`).
module CSP.Examples.GovernorWedge.Release where

open import Data.Empty using (⊥-elim)
open import Data.Nat using (ℕ; _≟_)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (≡-dec)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import Process_Trees
open PTree
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import CSP.Examples.GovernorWedge.Wedged using (Blocked; blocked-until; stopped-conn)
open import CSP.Examples.GovernorWedge.Invariant using (GoodO; cinv; own-reach; own-safe; own-live-sys; active-out)
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; traces)

-- the release interleaving: B released by the IG (CommitTr), reset by the peer, redialled as C; C tracked; B dies late
wRel : List (Event√ U)
wRel = HS 0 ∷ GV take ∷ CN (run 0) ∷ REL 0 true ∷ CN (reset 0) ∷ HS 1 ∷ GV take ∷ CN (run 1)
     ∷ CN (fail 0) ∷ TR 0 (just 1) ∷ GV take ∷ []

-- Conn after wRel: B closing (freed), C running and active; mux 0 terminal
cR1 : CState
cR1 = cst 2 (mkInc 0 closing true ∷ mkInc 1 running false ∷ []) (0 ∷ [])

-- IG after wRel under atTrace/atHandle: tracks C and awaits C
gR1 : GState
gR1 = gst (just 1) [] (await 1)

-- RL0: the release fires on the prefix, and the fixed CM then admits C
RL0 : Steps AsBuiltCMR c₀ g₀ (HS 0 ∷ GV take ∷ CN (run 0) ∷ REL 0 true ∷ CN (reset 0) ∷ HS 1 ∷ [])
        (cst 2 (mkInc 0 released true ∷ mkInc 1 hsd false ∷ []) []) (gst nothing (nc 1 ∷ []) idle)
RL0 =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , true) refl (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl done)))))

-- RL1: with the release, the CM-fixed pinned IG waits on a live mux
RL1 : Steps AsBuiltCMR c₀ g₀ wRel cR1 gR1 × gphase gR1 ≡ await 1 × 1 ∉ ran cR1 × LiveRun cR1 1
RL1 =
  (step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , true) refl (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl
  (step (GovAct , gov) take refl (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 1) refl (step (GovAct , gov) take refl done)))))))))))
  , refl
  , (λ { (here ()) ; (there ()) })
  , there (here (refl , inj₂ refl))

-- RL1 for the real main with the release
RL1main : Steps MainRealR c₀ g₀ wRel cR1 gR1 × gphase gR1 ≡ await 1 × 1 ∉ ran cR1 × LiveRun cR1 1
RL1main =
  (step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , true) refl (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl
  (step (GovAct , gov) take refl (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 1) refl (step (GovAct , gov) take refl done)))))))))))
  , refl
  , (λ { (here ()) ; (there ()) })
  , there (here (refl , inj₂ refl))

-- RL1 as a trace
RL1-trace : traces (Sys AsBuiltCMR) wRel
RL1-trace = _ , run-intro (proj₁ RL1)

-- IG after wRel under fix #2: B's own item makes it await 0
gR3 : GState
gR3 = gst (just 1) [] (await 0)

-- RL3: with the release, CM fix + fix #2 (byKey) orphans active C
RL3 : Steps CarryMuxCMR c₀ g₀ wRel cR1 gR3 × OrphanStepR CarryMuxCMR cR1 gR3 (ℕ , stopped) 0
RL3 =
  (step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , true) refl (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl
  (step (GovAct , gov) take refl (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 1) refl (step (GovAct , gov) take refl done)))))))))))
  , (1 , cR1 , gst nothing [] idle , refl , refl , (λ ()) , there (here (refl , inj₂ refl , refl)))
  , (λ ())

------------------------------------------------------------------------
-- RL2: the release wedge lasts while C lives

-- RL2: after the release interleaving the as-built lookup IG never promotes while C (1) does not fail
RL2 : ∀ {s W′} → SysAt AsBuiltCMR cR1 gR1 ⟹⟨ s ⟩ W′ → All (_≢ CN (fail 1)) s → All (_≢ GV promote) s
-- RL2 for the real main with the release
RL2main : ∀ {s W′} → SysAt MainRealR cR1 gR1 ⟹⟨ s ⟩ W′ → All (_≢ CN (fail 1)) s → All (_≢ GV promote) s

------------------------------------------------------------------------
-- RL3-safe / RL3-live-sys: fix #2 alone (CM fix, no identity check) keeps no-wedge under the release

-- fix #2 alone (CM fix, no identity check) still never awaits a live mux with the release
RL3-safe : ∀ {c g} → Reach CarryMuxCMR c g → ∀ r → gphase g ≡ await r → r ∈ ran c
RL3-safe = own-safe refl

-- … and promote stays within two steps
RL3-live-sys : ∀ {s W} → Sys CarryMuxCMR ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
RL3-live-sys = own-live-sys refl

------------------------------------------------------------------------
-- RL4: CM fix + fix #2 + identity check survives the release

-- RL4: every awaited mux is terminal
RL4-safe : ∀ {c g} → Reach CarryMuxIdCMR c g → ∀ r → gphase g ≡ await r → r ∈ ran c
-- RL4: from every reachable process promote, or stopped r then promote, is a trace
RL4-live-sys : ∀ {s W} → Sys CarryMuxIdCMR ⟹⟨ s ⟩ W → traces W (GV promote ∷ []) ⊎ Σ[ r ∈ ℕ ] traces W (ST r ∷ GV promote ∷ [])
-- RL4: no reachable orphaning step; the release step itself is excluded by OrphanStepR, as the IG's deliberate teardown
RL4-no-orphan : ∀ {c g} → Reach CarryMuxIdCMR c g → ∀ at a → ¬ OrphanStepR CarryMuxIdCMR c g at a
-- RL4 control: on the release interleaving B's `stopped 0` keeps C's entry, and C is active (fix #2 alone's RL3 orphaning step is gone)
RL4-ctrl : Steps CarryMuxIdCMR c₀ g₀ (wRel ∷ʳ ST 0) cR1 (gst (just 1) [] idle) × Active cR1 1

-- the post-release state is blocked on C under any mode without a timer
bR1 : ∀ {m} → timer m ≡ false → Blocked m cR1 gR1 1
bR1 nt = record { blocked = refl ; not-ran = λ { (here ()) ; (there ()) } ; no-timer = nt }

RL2 st with run-inv st
... | _ , _ , _ , ss = blocked-until (bR1 refl) ss

RL2main st with run-inv st
... | _ , _ , _ , ss = blocked-until (bR1 refl) ss

RL4-safe = own-safe refl

RL4-live-sys = own-live-sys refl

-- keeps-entryR at a mode whose switches are spelled out: keep, idChecked, no timer
keeps-entry′ : ∀ {ep cp rp c e q ph x c′ g′} → GoodO c (gst e q ph) → ∀ at a → at ≢ ((ℕ × Bool) , rel)
             → sstep at a (mode ep keep idChecked false cp rp) c (gst e q ph) ≡ just (c′ , g′)
             → e ≡ just x → Active c x → entry g′ ≡ just x
keeps-entry′ {cp = cp} {c = c} {e = e} {q = q} {ph = ph} _ (_ , conn) a _ eq ex _
  with map-split {f = λ c′ → c′ , gst e q ph} {x = cstep (ConnAct , conn) a cp c} eq
... | _ , _ , refl = ex
keeps-entry′ _ (_ , hs) _ _ eq ex _ with zip-split eq
... | _ , refl = ex
keeps-entry′ {e = e} _ (_ , trace) (_ , v) _ eq ex _ with zip-split eq
... | _ , eqg with ≡-dec _≟_ v e | eqg
...   | yes _ | refl = ex
...   | no _  | ()
keeps-entry′ {ph = idle} _ (_ , stopped) _ _ eq _ _ with zip-split eq
... | _ , ()
keeps-entry′ {cp = cp} {ph = await r} {x = x} G (_ , stopped) t _ eq refl act with zip-split eq
... | eqc , eqg with t ≟ r | eqg
...   | no _     | ()
...   | yes refl | refl with x ≟ t
...     | yes refl = ⊥-elim (active-out (cinv G) act (stopped-conn {pol = cp} eqc))
...     | no _     = refl
keeps-entry′ _ (_ , rel) _ nr _ _ _ = ⊥-elim (nr refl)
keeps-entry′ {ph = idle}                  _ (_ , gov) promote _ refl ex _ = ex
keeps-entry′ {ph = await _}               _ (_ , gov) promote _ () _ _
keeps-entry′ {q = []}                     _ (_ , gov) take _ () _ _
keeps-entry′ {q = _ ∷ _} {ph = await _}   _ (_ , gov) take _ () _ _
keeps-entry′ {q = nc _ ∷ _} {ph = idle}   _ (_ , gov) take _ refl refl _ = refl
keeps-entry′ {q = mf _ ∷ _} {ph = idle}   _ (_ , gov) take _ refl refl _ = refl
keeps-entry′ {q = mfK ∷ _} {ph = idle}    _ (_ , gov) take _ refl refl _ = refl
keeps-entry′ {ph = idle}                  _ (_ , gov) tmo _ () _ _
keeps-entry′ {ph = await _}               _ (_ , gov) tmo _ () _ _

-- mode-generic Invariant.keeps-entry: under keep, idChecked and no timer, no step but the release drops an active entry (CM policy unused)
keeps-entryR : ∀ {m c e q ph x c′ g′} → newP m ≡ keep → unregP m ≡ idChecked → timer m ≡ false
             → GoodO c (gst e q ph) → ∀ at a → at ≢ ((ℕ × Bool) , rel)
             → sstep at a m c (gst e q ph) ≡ just (c′ , g′) → e ≡ just x → Active c x → entry g′ ≡ just x
keeps-entryR {mode _ _ _ _ _ _} refl refl refl = keeps-entry′

RL4-no-orphan {g = gst _ _ _} R at a ((_ , _ , _ , eq , ex , ne , act) , nr) =
  ne (keeps-entryR refl refl refl (own-reach refl R) at a nr eq ex act)

RL4-ctrl =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , true) refl (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl
  (step (GovAct , gov) take refl (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 1) refl (step (GovAct , gov) take refl
  (step (ℕ , stopped) 0 refl done))))))))))) , there (here (refl , inj₂ refl , refl))

-- control: the release step itself (CommitTr) drops an active entry, so OrphanStepR's exclusion is load-bearing
rel-orphans : OrphanStep CarryMuxIdCMR (cst 1 (mkInc 0 running false ∷ []) []) (gst (just 0) [] idle) ((ℕ × Bool) , rel) (0 , true)
rel-orphans = 0 , _ , _ , refl , refl , (λ ()) , here (refl , inj₂ refl , refl)

------------------------------------------------------------------------
-- RLc1-RLc3: controls for the general release (v4.1a spec §4)

-- events: B fails, is released as UnsupportedState (kept) while C is admitted and takes over, then B's
-- stale entry is released (CommitTr), clearing the IG and cancelling C, the newest incarnation
wRc1 : List (Event√ U)
wRc1 = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ CN (fail 0) ∷ REL 0 false
     ∷ HS 1 ∷ GV take ∷ CN (run 1) ∷ REL 0 true ∷ []

-- RLc1: B failed and marked Terminating with its entry kept; C admitted over it and ignored; the IG then
-- releases its stale entry B while the CM cancels the newest incarnation, C. Its first release hits the CM's
-- InboundState, which the code treats as unexpected (assertion, CM:1241, CM:1289); RLc1′ reaches the effect without it
RLc1 : Steps CarryMuxIdCMR c₀ g₀ wRc1 (cst 2 (mkInc 0 failedT true ∷ mkInc 1 released false ∷ []) (0 ∷ [])) (gst nothing [] idle)
RLc1 =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Bool) , rel) (0 , false) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step ((ℕ × Bool) , rel) (0 , true) refl done)))))))))

-- events: B fails and is traced (closing), C is admitted and runs, then the IG releases its stale entry B (CommitTr only)
wRc1′ : List (Event√ U)
wRc1′ = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ CN (fail 0) ∷ TR 0 (just 0) ∷ HS 1 ∷ CN (run 1) ∷ REL 0 true ∷ []

-- RLc1′: the same side effect with CommitTr only: B traced and closing, C admitted and running, the IG
-- (whose CommitRemote precedes its queued messages, IG:258-266) releases stale entry B and the CM cancels C
RLc1′ : Steps CarryMuxIdCMR c₀ g₀ wRc1′ (cst 2 (mkInc 0 closing true ∷ mkInc 1 released false ∷ []) (0 ∷ [])) (gst nothing (mf 0 ∷ nc 1 ∷ []) idle)
RLc1′ =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (ℕ , hs) 1 refl
  (step (ConnAct , conn) (run 1) refl (step ((ℕ × Bool) , rel) (0 , true) refl done))))))))

-- RLc2: UnsupportedState marks B Terminating but the IG keeps its entry
RLc2 : Steps CarryMuxIdCMR c₀ g₀ (HS 0 ∷ GV take ∷ CN (run 0) ∷ REL 0 false ∷ [])
         (cst 1 (mkInc 0 released false ∷ []) []) (gst (just 0) [] idle)
RLc2 =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step ((ℕ × Bool) , rel) (0 , false) refl done)))

-- RLc3: the fixed CM admits C over a failed-then-released B
RLc3 : Steps CarryMuxIdCMR c₀ g₀ (HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ CN (fail 0) ∷ REL 0 false ∷ HS 1 ∷ [])
         (cst 2 (mkInc 0 failedT true ∷ mkInc 1 hsd false ∷ []) (0 ∷ [])) (gst (just 0) (nc 1 ∷ []) idle)
RLc3 =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Bool) , rel) (0 , false) refl (step (ℕ , hs) 1 refl done))))))
