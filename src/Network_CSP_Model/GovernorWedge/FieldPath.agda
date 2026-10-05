{-# OPTIONS --guardedness #-}

-- The field interleaving (spec §5) and its controls: incarnation B resets and is
-- redialled as C, C is ignored by the keep policy (IG:378) and B dies, C is itself
-- reset and redialled as D, D registers and C's late lookup finds live D. All proved
-- by computation on `Steps`/`sstep`, as in `Witness`. Log lines L<n> are line numbers
-- of govstall-a1-20260927-full.log (the IG:n code key is in Model.agda): L210290,
-- L210651, L211817, L211852, L212107, L212127, L707729;
-- B = incarnation 0, C = incarnation 1, D = incarnation 2.
module GovernorWedge.FieldPath where

open import Data.Nat using (ℕ)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing; zip)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∉_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_; cong; trans)

open import Process_Trees
open PTree
open import GovernorWedge.Model
open import GovernorWedge.Steps
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (traces)

-- the field interleaving (spec §5): B reset and redialled as C; C ignored (IG:378);
-- B dies and is unregistered; C reset and redialled as D; D registered; C dies and
-- its lookup finds live D
wF : List (Event√ U)
wF = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ HS 1 ∷ GV take ∷ CN (run 1)
   ∷ CN (fail 0) ∷ TR 0 (just 0) ∷ GV take ∷ ST 0 ∷ CN (reset 1) ∷ HS 2 ∷ GV take
   ∷ CN (run 2) ∷ CN (fail 1) ∷ TR 1 (just 2) ∷ GV take ∷ []

-- Conn after wF: B and C closing and freed, D running and active; muxes 1 and 0 terminal
cF : CState
cF = cst 3 (mkInc 0 closing true ∷ mkInc 1 closing true ∷ mkInc 2 running false ∷ []) (1 ∷ 0 ∷ [])

-- IG after wF: tracks D and is blocked on D
gF : GState
gF = gst (just 2) [] (await 2)

-- W1f: the pinned IG reaches the field wedge
W1f-reach : Steps AsBuilt c₀ g₀ wF cF gF
W1f-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (GovAct , gov) take refl
  (step (ℕ , stopped) 0 refl (step (ConnAct , conn) (reset 1) refl
  (step (ℕ , hs) 2 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 2) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 2) refl (step (GovAct , gov) take refl done)))))))))))))))))

-- W1f as a trace of the pinned system
W1f-trace : traces (Sys AsBuilt) wF
W1f-trace = _ , run-intro W1f-reach

-- W1f for origin/main 2e83f1a3
W1fmain-reach : Steps Main c₀ g₀ wF cF gF
W1fmain-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (GovAct , gov) take refl
  (step (ℕ , stopped) 0 refl (step (ConnAct , conn) (reset 1) refl
  (step (ℕ , hs) 2 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 2) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 2) refl (step (GovAct , gov) take refl done)))))))))))))))))

-- W1f for fix #1 (Timeout): wF has no `tmo`, so the same run reaches the field wedge
W1fT-reach : Steps Timeout c₀ g₀ wF cF gF
W1fT-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
  (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (GovAct , gov) take refl
  (step (ℕ , stopped) 0 refl (step (ConnAct , conn) (reset 1) refl
  (step (ℕ , hs) 2 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 2) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 2) refl (step (GovAct , gov) take refl done)))))))))))))))))

-- H1f: if D terminates, the IG resumes (self-heal)
H1f : Steps AsBuilt c₀ g₀ (wF ++ CN (fail 2) ∷ ST 2 ∷ GV promote ∷ [])
        (cst 3 (mkInc 0 closing true ∷ mkInc 1 closing true ∷ mkInc 2 failed false ∷ []) (2 ∷ 1 ∷ 0 ∷ []))
        (gst nothing [] idle)
H1f =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (
  step (ConnAct , conn) (run 0) refl (step (ConnAct , conn) (reset 0) refl (
  step (ℕ , hs) 1 refl (step (GovAct , gov) take refl (
  step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl (
  step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (GovAct , gov) take refl (
  step (ℕ , stopped) 0 refl (step (ConnAct , conn) (reset 1) refl (
  step (ℕ , hs) 2 refl (step (GovAct , gov) take refl (
  step (ConnAct , conn) (run 2) refl (step (ConnAct , conn) (fail 1) refl (
  step ((ℕ × Maybe ℕ) , trace) (1 , just 2) refl (step (GovAct , gov) take refl (
  step (ConnAct , conn) (fail 2) refl (step (ℕ , stopped) 2 refl (
  step (GovAct , gov) promote refl done))))))))))))))))))))

-- ¬N1: a reachable state waits on a live mux
notN1 : Σ[ s ∈ List (Event√ U) ] Steps AsBuilt c₀ g₀ s cF gF × gphase gF ≡ await 2 × 2 ∉ ran cF × LiveRun cF 2
notN1 = wF , W1f-reach , refl , (λ { (here ()) ; (there (here ())) ; (there (there ())) })
      , there (there (here (refl , inj₂ refl)))

-- IG after wF under fix #2: C's own item makes it await 1
gFC : GState
gFC = gst (just 2) [] (await 1)

-- O2: under fix #2 the field path reaches an orphaning step (stopped 1 deletes D's entry while D is active)
O2 : Steps CarryMux c₀ g₀ wF cF gFC × OrphanStep CarryMux cF gFC (ℕ , stopped) 1
O2 = (step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (
     step (ConnAct , conn) (run 0) refl (step (ConnAct , conn) (reset 0) refl (
     step (ℕ , hs) 1 refl (step (GovAct , gov) take refl (
     step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl (
     step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl (step (GovAct , gov) take refl (
     step (ℕ , stopped) 0 refl (step (ConnAct , conn) (reset 1) refl (
     step (ℕ , hs) 2 refl (step (GovAct , gov) take refl (
     step (ConnAct , conn) (run 2) refl (step (ConnAct , conn) (fail 1) refl (
     step ((ℕ × Maybe ℕ) , trace) (1 , just 2) refl (step (GovAct , gov) take refl done))))))))))))))))))
   , 2 , cF , gst nothing [] idle , refl , refl , (λ ()) , there (there (here (refl , inj₂ refl , refl)))

-- R1: with replace, C becomes the entry, then B's late lookup finds C and the IG waits on live C
wR : List (Event√ U)
wR = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ HS 1 ∷ GV take ∷ CN (run 1)
   ∷ CN (fail 0) ∷ TR 0 (just 1) ∷ GV take ∷ []

-- Conn after wR: B closing and freed, C running and active; mux 0 terminal
cR : CState
cR = cst 2 (mkInc 0 closing true ∷ mkInc 1 running false ∷ []) (0 ∷ [])

-- IG after wR: tracks C and is blocked on C
gR : GState
gR = gst (just 1) [] (await 1)

-- R1: under ReplaceEntry the field path reaches an await on the entry it just installed
R1 : Steps ReplaceEntry c₀ g₀ wR cR gR × 1 ∉ ran cR × Active cR 1
R1 = (step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
     (step (ConnAct , conn) (reset 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
     (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 0) refl
     (step ((ℕ × Maybe ℕ) , trace) (0 , just 1) refl (step (GovAct , gov) take refl done))))))))))
   , (λ { (here ()) ; (there ()) })
   , there (here (refl , inj₂ refl , refl))

-- O1: prefix after which C is hand-shaken (not yet run) while every keep-policy mode still tracks stale B
oF : List (Event√ U)
oF = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (reset 0) ∷ HS 1 ∷ GV take ∷ []

-- Conn after oF: B running and freed, C handshaking (not yet run)
cO : CState
cO = cst 2 (mkInc 0 running true ∷ mkInc 1 hsd false ∷ []) []

-- IG after oF: still tracking B, idle
gO : GState
gO = gst (just 0) [] idle

-- with the CM pinned, an hs move needs only the kernel rule to reduce, whatever the mode's other switches
sstep-hs-pin : ∀ {m a c g} → cmP m ≡ cmPin → sstep (ℕ , hs) a m c g ≡ zip (cstep (ℕ , hs) a cmPin c) (gstep (ℕ , hs) a m g)
sstep-hs-pin {m} {a} {c} {g} cp = cong (λ pol → zip (cstep (ℕ , hs) a pol c) (gstep (ℕ , hs) a m g)) cp

-- O1: under every keep-policy, pinned-CM mode, a reachable idle state where active C is not the entry
-- (cmP m ≡ cmPin is a genuinely new hypothesis: under cmFix this exact run is refused at incarnation 1's
-- handshake, since 0 is still live though freed, so the theorem as stated for "every keep-policy mode"
-- would be false once cmFix-policy modes exist — narrowing to the pinned CM restores it, unweakened
-- for every mode this file's other lemmas are about)
O1 : ∀ m → newP m ≡ keep → cmP m ≡ cmPin → Steps m c₀ g₀ oF cO gO × Active cO 1 × entry gO ≢ just 1
O1 m p cp =
  (step {c₁ = c1} {g₁ = g1} (ℕ , hs) 0 (trans (sstep-hs-pin {m = m} {a = 0} {c = c₀} {g = g₀} cp) refl)
  (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (reset 0) refl
  (step {c₁ = c5F} {g₁ = g5F} (ℕ , hs) 1 (trans (sstep-hs-pin {m = m} {a = 1} {c = c4} {g = g4} cp) refl)
       (step (GovAct , gov) take take-eq done))))))
  , there (here (refl , inj₁ refl , refl))
  , λ ()
  where
  -- Conn just after HS 0 (the pin's kernel rule fires the same regardless of m's other switches)
  c1 : CState
  c1 = cst 1 (mkInc 0 hsd false ∷ []) []
  -- IG just after HS 0
  g1 : GState
  g1 = gst nothing (nc 0 ∷ []) idle
  -- Conn just before HS 1: B running and freed (after take, run 0, reset 0)
  c4 : CState
  c4 = cst 1 (mkInc 0 running true ∷ []) []
  -- IG just before HS 1: tracking B, idle
  g4 : GState
  g4 = gst (just 0) [] idle
  -- Conn just before oF's mode-dependent take: B running (freed), C handshaken
  c5F : CState
  c5F = cst 2 (mkInc 0 running true ∷ mkInc 1 hsd false ∷ []) []
  -- IG just before oF's mode-dependent take: tracking B, C's item queued
  g5F : GState
  g5F = gst (just 0) (nc 1 ∷ []) idle
  -- the take of C's item reduces through takeG (newP m), forced to keep by p (IG:378)
  take-eq : sstep (GovAct , gov) take m c5F g5F ≡ just (cO , gO)
  take-eq rewrite p = refl
