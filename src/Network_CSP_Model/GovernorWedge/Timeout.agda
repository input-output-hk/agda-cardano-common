{-# OPTIONS --guardedness #-}

-- Fix #1 (Timeout mode): a visible `tmo` on the await always returns the IG loop to
-- idle, so `promote` is reachable within at most one extra step from any model
-- state. The stall is always escapable, by construction of the Timeout mode (F1;
-- the model is untimed, so nothing here bounds its duration); after the timeout on
-- the never-run wedge W0 the next incarnation is tracked (F1-heal). On the field path
-- the timeout fires while the IG awaits live, active D and deletes D's entry by key
-- (IG:406), so fix #1 alone orphans D (F1-orphan).
module CSP.Examples.GovernorWedge.Timeout where

open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees
open PTree
open import CSP.Examples.GovernorWedge.Model
open import CSP.Examples.GovernorWedge.Steps
open import CSP.Examples.GovernorWedge.Witness using (w0; W0T-reach)
open import CSP.Examples.GovernorWedge.FieldPath using (wF; cF; gF; W1fT-reach)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; traces)

-- holds for every model state, reachable or not: the timeout makes the await always
-- escapable, by construction of `gstep` (no reachability is used); it does not fix O1
F1-live : ∀ c g
        → (Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps Timeout c g (GV promote ∷ []) c′ g′)
        ⊎ (Σ[ c′ ∈ CState ] Σ[ g′ ∈ GState ] Steps Timeout c g (GV tmo ∷ GV promote ∷ []) c′ g′)

-- F1 at process level: every state the fix #1 system reaches can still promote,
-- either now or right after one `tmo`
F1-live-sys : ∀ {s W} → Sys Timeout ⟹⟨ s ⟩ W
            → traces W (GV promote ∷ []) ⊎ traces W (GV tmo ∷ GV promote ∷ [])

-- two Steps runs compose
Steps-++ : ∀ {m c g s c₁ g₁ s′ c′ g′} → Steps m c g s c₁ g₁ → Steps m c₁ g₁ s′ c′ g′
         → Steps m c g (s ++ s′) c′ g′

-- F1 control: from the never-run wedge (Witness.W0T-reach), one `tmo` then `promote`
-- is a trace of the fix #1 system, i.e. the stall it escapes is the real one
F1-ctrl : traces (Sys Timeout) (w0 ∷ʳ GV tmo ∷ʳ GV promote)

-- F1 heal: after the timeout deletes the stale entry 0, incarnation 1 closes and the
-- next incarnation's NewConnection is tracked (entry = just 2)
F1-heal : Steps Timeout c₀ g₀ (w0 ++ GV tmo ∷ CN (close 1) ∷ HS 2 ∷ GV take ∷ [])
                (cst 3 (mkInc 2 hsd false ∷ []) (1 ∷ [])) (gst (just 2) [] idle)

-- F1 orphan: fix #1 reaches the field wedge, and there `tmo` drops active D's entry
F1-orphan : Steps Timeout c₀ g₀ wF cF gF × OrphanStep Timeout cF gF (GovAct , gov) tmo

F1-live c (gst e q idle)      = inj₁ (_ , _ , step (GovAct , gov) promote refl done)
F1-live c (gst e q (await r)) = inj₂ (_ , _ , step (GovAct , gov) tmo refl (step (GovAct , gov) promote refl done))

F1-live-sys st with run-inv st
... | c′ , g′ , refl , ss with F1-live c′ g′
...   | inj₁ (_ , _ , ss′) = inj₁ (_ , run-intro ss′)
...   | inj₂ (_ , _ , ss′) = inj₂ (_ , run-intro ss′)

Steps-++ done ss′ = ss′
Steps-++ (step at a eq ss) ss′ = step at a eq (Steps-++ ss ss′)

F1-ctrl = _ , run-intro (Steps-++ W0T-reach
  (step (GovAct , gov) tmo refl (step (GovAct , gov) promote refl done)))

F1-heal = Steps-++ W0T-reach
  (step (GovAct , gov) tmo refl (step (ConnAct , conn) (close 1) refl
  (step (ℕ , hs) 2 refl (step (GovAct , gov) take refl done))))

F1-orphan = W1fT-reach
          , 2 , cF , gst nothing [] idle , refl , refl , (λ ()) , there (there (here (refl , inj₂ refl , refl)))
