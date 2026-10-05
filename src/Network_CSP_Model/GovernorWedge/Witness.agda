{-# OPTIONS --guardedness #-}

-- The never-run interleaving (v2 spec §5 W0; reachable in the model, not observed in
-- the log) and the non-vacuity controls, all proved by computation on `Steps`/`sstep`:
-- no simulation reasoning, just `refl` per letter.
-- IG:n = line n of ouroboros-network's InboundGovernor.hs at the pin (key: Model.agda).
module GovernorWedge.Witness where

open import Data.Nat using (ℕ)
open import Data.Bool using (false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees
open PTree
open import GovernorWedge.Model
open import GovernorWedge.Steps
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (traces)

-- the never-run interleaving (v1 W1, now W0): incarnation 0 aborts before Mx.run; 1 is ignored and finds stale 0
w0 : List (Event√ U)
w0 = HS 0 ∷ GV take ∷ CN (abort 0) ∷ CN (close 0) ∷ HS 1 ∷ GV take
   ∷ CN (run 1) ∷ CN (fail 1) ∷ TR 1 (just 0) ∷ GV take ∷ []

-- Conn after w0: incarnation 1 closing (not yet closed), mux 1 terminal
cW0 : CState
cW0 = cst 2 (mkInc 1 closing false ∷ []) (1 ∷ [])

-- IG after w0: blocked on mux 0, which never ran
gW0 : GState
gW0 = gst (just 0) [] (await 0)

-- W0 (reachability half): the as-built IG reaches the wedge
W0-reach : Steps AsBuilt c₀ g₀ w0 cW0 gW0
W0-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl done)))))))))

-- W0-main (reachability half): origin/main 2e83f1a3 reaches the same state
W0main-reach : Steps Main c₀ g₀ w0 cW0 gW0
W0main-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl done)))))))))

-- F1 control: the Timeout variant reaches the same await (the stall exists)
W0T-reach : Steps Timeout c₀ g₀ w0 cW0 gW0
W0T-reach =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl done)))))))))

-- a clean episode: the IG awaits a terminal mux (control for the ∈-ran case of F2-safe)
clean : List (Event√ U)
clean = HS 0 ∷ GV take ∷ CN (run 0) ∷ CN (fail 0) ∷ TR 0 (just 0) ∷ GV take ∷ []

-- N1 control: the as-built IG awaits a terminal mux on the clean episode
N1-ctrl-ran : Steps AsBuilt c₀ g₀ clean (cst 1 (mkInc 0 closing false ∷ []) (0 ∷ [])) (gst (just 0) [] (await 0))
N1-ctrl-ran =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (fail 0) refl (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl
  (step (GovAct , gov) take refl done)))))

-- F2id control: under CarryMuxId the clean episode awaits terminal mux 0 (own item mf 0)
clean-CarryMuxId : Steps CarryMuxId c₀ g₀ clean (cst 1 (mkInc 0 closing false ∷ []) (0 ∷ [])) (gst (just 0) [] (await 0))
clean-CarryMuxId =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (fail 0) refl (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl
  (step (GovAct , gov) take refl done)))))

-- FIX control: under FullFix the clean episode awaits terminal mux 0 (own item mf 0)
clean-FullFix : Steps FullFix c₀ g₀ clean (cst 1 (mkInc 0 closing false ∷ []) (0 ∷ [])) (gst (just 0) [] (await 0))
clean-FullFix =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (run 0) refl
  (step (ConnAct , conn) (fail 0) refl (step ((ℕ × Maybe ℕ) , trace) (0 , just 0) refl
  (step (GovAct , gov) take refl done)))))

-- F2 control: under CarryMux the W0 interleaving awaits mux 1, which stops, and promote follows
F2-ctrl : Steps CarryMux c₀ g₀ (w0 ∷ʳ ST 1 ∷ʳ GV promote) cW0 (gst nothing [] idle)
F2-ctrl =
  step (ℕ , hs) 0 refl (step (GovAct , gov) take refl (step (ConnAct , conn) (abort 0) refl
  (step (ConnAct , conn) (close 0) refl (step (ℕ , hs) 1 refl (step (GovAct , gov) take refl
  (step (ConnAct , conn) (run 1) refl (step (ConnAct , conn) (fail 1) refl
  (step ((ℕ × Maybe ℕ) , trace) (1 , just 0) refl (step (GovAct , gov) take refl
  (step (ℕ , stopped) 1 refl (step (GovAct , gov) promote refl done)))))))))))

-- control: promote is offered initially (so W0's refusal is not trivial)
promote₀ : ∀ m → Steps m c₀ g₀ (GV promote ∷ []) c₀ g₀
promote₀ m = step (GovAct , gov) promote refl done

-- W0 as a trace of the as-built system
W0-trace : traces (Sys AsBuilt) w0
W0-trace = _ , run-intro W0-reach
