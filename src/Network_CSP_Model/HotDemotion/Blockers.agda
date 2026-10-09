{-# OPTIONS --guardedness #-}

-- D3 (DESIGN.md §5) and D4: after ouroboros-consensus PR 2344 the demotion still cannot end Warm if the
-- remote never sends a blocking MsgRequestTxIds (TxSubmission2) or no Praos block arrives (ChainSync); with
-- the timer on, each such run is deadlock free, bounded, and ends tmo then cold.  D4 is the before/after
-- contrast in one environment.  Vacuity guards show that in each case every other hot protocol (LeiosNotify
-- included) can still return in the model, so within the model the blocker is that protocol.  (Not modelled:
-- BlockFetch's registry bracket waits for the same peer's ChainSync, RESEARCH.md §3, so without blocks
-- BlockFetch would in practice not return either; see README §2.)
module HotDemotion.Blockers where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-trans; m≤m+n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)

open import Process_Trees
open import HotDemotion.Model
open import HotDemotion.PrePR
  using (J; J-no-ready; J-notFin; stepIf-inv; if-just; pre-neverWarm; Pre
        ; TC; endsCold; timer-deadlockFree; steps⇒traceBound)
open import HotDemotion.PostPR using (Post; WarmFired; post-warmLTL; steps-len)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_)
open import Semantics.Deadlock {E = Ev} {I = ExtI Ev} using (DeadlockFree)
-- only definitions are used from Traces_Based; its two postulates (⟦G⟧⇒⟦G⟧⁺, ¬G⇒F¬) are not
open import Semantics.LTL.Traces_Based {E = Ev} {I = ExtI Ev} using (Trace; ◇ᵗ; atom)

-- with the timer on, every post-PR Steps run from st₀ has at most 13 moves (PostPR's rank of st₀)
steps-13 : ∀ {b t w s} → Steps (Post b t true) st₀ w s → length w ≤ 13
steps-13 ss = ≤-trans (m≤m+n _ _) (steps-len ss)

-- the D3 run form for a mode: deadlock free, every trace ≤ 14 events (13 moves plus √), and every
-- √-ended trace is  t₁ ++ GV tmo ∷ t₂  with cold in t₂
RunCold : Mode → Set₁
RunCold m = DeadlockFree (Sys m)
          × (∀ {tr W} → Sys m ⟹⟨ tr ⟩ W → length tr ≤ 14)
          × (∀ {tr r W} → Sys m ⟹⟨ tr ++ √ r ∷ [] ⟩ W → TC tr)

-- ===================== tx: no txReq means tx never returns =====================

-- the tx invariant: tx is still running / waiting, and the peer is not Warm
Inv-tx : St → Set
Inv-tx s = J (ps s tx) × (gph s ≢ warmD)

-- if the tx phase is not fin, allFin is false
allFin-tx : ∀ s → isFin (ps s tx) ≡ false → allFin s ≡ false
allFin-tx s e rewrite e = trans (cong (isFin (ps s cs) ∧_) (z (isFin (ps s bf)))) (z (isFin (ps s cs)))
  where
  -- x ∧ false is false
  z : ∀ x → (x ∧ false) ≡ false
  z true  = refl
  z false = refl

-- the warm move is impossible while the tx invariant holds
warm-tx : ∀ {v c s s′} → Inv-tx s → sstep (GAct , gov) warm (Post v false c) s ≡ just s′ → ⊥
warm-tx {s = mkSt hot f}      _ ()
warm-tx {s = mkSt warmD f}    _ ()
warm-tx {s = mkSt timedOut f} _ ()
warm-tx {s = mkSt coldD f}    _ ()
warm-tx {s = mkSt awaiting f} (j , _) h with allFin (mkSt awaiting f) | allFin-tx (mkSt awaiting f) (J-notFin j) | h
... | true  | () | _
... | false | _  | ()

-- every sstep move preserves the tx invariant
step-tx : ∀ {v c} s {s′} at a → Inv-tx s → sstep at a (Post v false c) s ≡ just s′ → Inv-tx s′
step-tx (mkSt hot f)      (_ , gov) demote i refl = inj₂ refl , λ ()
step-tx (mkSt hot f)      (_ , gov) warm   i ()
step-tx (mkSt hot f)      (_ , gov) tmo    i ()
step-tx (mkSt hot f)      (_ , gov) cold   i ()
step-tx (mkSt hot f)      (_ , rtn) p      i ()
step-tx (mkSt hot f)      (_ , env) e      i ()
step-tx (mkSt hot f)      (_ , int) a      i ()
step-tx (mkSt awaiting f) (_ , gov) demote i ()
step-tx {v} {c} (mkSt awaiting f) (_ , gov) warm   i h = ⊥-elim (warm-tx {v} {c} i h)
step-tx {c = c} (mkSt awaiting f) (_ , gov) tmo    (j , _) h with if-just c h
... | refl = j , λ ()
step-tx (mkSt awaiting f) (_ , gov) cold   i ()
step-tx (mkSt awaiting f) (_ , rtn) cs     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , rtn) bf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , rtn) tx     (j , _) h = ⊥-elim (J-no-ready j (proj₁ (stepIf-inv h)))
step-tx (mkSt awaiting f) (_ , rtn) lf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , rtn) ln     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx {v} (mkSt awaiting f) (_ , env) block (j , _) h with stepIf-inv (if-just v h)
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , env) txReq i ()
step-tx (mkSt awaiting f) (_ , env) lnReply i ()
step-tx (mkSt awaiting f) (_ , int) bfDrain    (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , int) lnQuit     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt awaiting f) (_ , int) lnQuitDone (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-tx (mkSt warmD f)    (_ , gov) demote i ()
step-tx (mkSt warmD f)    (_ , gov) warm   i ()
step-tx (mkSt warmD f)    (_ , gov) tmo    i ()
step-tx (mkSt warmD f)    (_ , gov) cold   i ()
step-tx (mkSt warmD f)    (_ , rtn) p      i ()
step-tx (mkSt warmD f)    (_ , env) e      i ()
step-tx (mkSt warmD f)    (_ , int) a      i ()
step-tx (mkSt timedOut f) (_ , gov) demote i ()
step-tx (mkSt timedOut f) (_ , gov) warm   i ()
step-tx (mkSt timedOut f) (_ , gov) tmo    i ()
step-tx (mkSt timedOut f) (_ , gov) cold   (j , _) refl = j , λ ()
step-tx (mkSt timedOut f) (_ , rtn) p      i ()
step-tx (mkSt timedOut f) (_ , env) e      i ()
step-tx (mkSt timedOut f) (_ , int) a      i ()
step-tx (mkSt coldD f)    (_ , gov) demote i ()
step-tx (mkSt coldD f)    (_ , gov) warm   i ()
step-tx (mkSt coldD f)    (_ , gov) tmo    i ()
step-tx (mkSt coldD f)    (_ , gov) cold   i ()
step-tx (mkSt coldD f)    (_ , rtn) p      i ()
step-tx (mkSt coldD f)    (_ , env) e      i ()
step-tx (mkSt coldD f)    (_ , int) a      i ()

-- the tx invariant holds along every Steps run
steps-tx : ∀ {v c s w s′} → Steps (Post v false c) s w s′ → Inv-tx s → Inv-tx s′
steps-tx done i = i
steps-tx {s = s} (more {at = at} {a = a} eq ss) i = steps-tx ss (step-tx s at a i eq)

-- D3: post-PR, a remote that never sends a blocking request makes Warm unreachable
post-noTxReq-noWarm : ∀ {v c w s} → Steps (Post v false c) st₀ w s → gph s ≢ warmD
post-noTxReq-noWarm ss = proj₂ (steps-tx ss (inj₁ refl , λ ()))

-- D3 run form: post-PR with the timer on and no blocking txReq, every maximal run ends tmo then cold
-- (deadlock free, bounded, no τ so no divergence; √-ended traces contain tmo then cold)
post-noTxReq-endsCold : ∀ {v} → RunCold (Post v false true)
post-noTxReq-endsCold = timer-deadlockFree refl , steps⇒traceBound steps-13 , endsCold step-tx proj₂ (inj₁ refl , λ ())

-- vacuity guard (PLAN.md review focus 1): the post-PR system reaches awaiting with every protocol but tx returned
post-noTxReq-nearlyWarm : Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s ∈ St ]
                 (Steps (Post true false true) st₀ w s × gph s ≡ awaiting
                  × ps s cs ≡ fin × ps s bf ≡ fin × ps s lf ≡ fin × ps s ln ≡ fin)
post-noTxReq-nearlyWarm =
  ( ((GAct , gov) , demote) ∷ ((IntAct , int) , bfDrain) ∷ ((EnvAct , env) , block) ∷ ((IntAct , int) , lnQuit) ∷ ((IntAct , int) , lnQuitDone) ∷ ((Proto , rtn) , cs) ∷ ((Proto , rtn) , bf) ∷ ((Proto , rtn) , lf) ∷ ((Proto , rtn) , ln) ∷ [] )
  , _
  , more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl done))))))))
  , refl , refl , refl , refl , refl

-- ===================== cs: no block means cs never returns =====================

-- the cs invariant: cs is still running / waiting, and the peer is not Warm
Inv-cs : St → Set
Inv-cs s = J (ps s cs) × (gph s ≢ warmD)

-- if the cs phase is not fin, allFin is false
allFin-cs : ∀ s → isFin (ps s cs) ≡ false → allFin s ≡ false
allFin-cs s e rewrite e = refl

-- the warm move is impossible while the cs invariant holds
warm-cs : ∀ {v c s s′} → Inv-cs s → sstep (GAct , gov) warm (Post false v c) s ≡ just s′ → ⊥
warm-cs {s = mkSt hot f}      _ ()
warm-cs {s = mkSt warmD f}    _ ()
warm-cs {s = mkSt timedOut f} _ ()
warm-cs {s = mkSt coldD f}    _ ()
warm-cs {s = mkSt awaiting f} (j , _) h with allFin (mkSt awaiting f) | allFin-cs (mkSt awaiting f) (J-notFin j) | h
... | true  | () | _
... | false | _  | ()

-- every sstep move preserves the cs invariant
step-cs : ∀ {v c} s {s′} at a → Inv-cs s → sstep at a (Post false v c) s ≡ just s′ → Inv-cs s′
step-cs (mkSt hot f)      (_ , gov) demote i refl = inj₂ refl , λ ()
step-cs (mkSt hot f)      (_ , gov) warm   i ()
step-cs (mkSt hot f)      (_ , gov) tmo    i ()
step-cs (mkSt hot f)      (_ , gov) cold   i ()
step-cs (mkSt hot f)      (_ , rtn) p      i ()
step-cs (mkSt hot f)      (_ , env) e      i ()
step-cs (mkSt hot f)      (_ , int) a      i ()
step-cs (mkSt awaiting f) (_ , gov) demote i ()
step-cs {v} {c} (mkSt awaiting f) (_ , gov) warm   i h = ⊥-elim (warm-cs {v} {c} i h)
step-cs {c = c} (mkSt awaiting f) (_ , gov) tmo    (j , _) h with if-just c h
... | refl = j , λ ()
step-cs (mkSt awaiting f) (_ , gov) cold   i ()
step-cs (mkSt awaiting f) (_ , rtn) cs     (j , _) h = ⊥-elim (J-no-ready j (proj₁ (stepIf-inv h)))
step-cs (mkSt awaiting f) (_ , rtn) bf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , rtn) tx     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , rtn) lf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , rtn) ln     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs {v} (mkSt awaiting f) (_ , env) txReq (j , _) h with stepIf-inv (if-just v h)
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , env) block i ()
step-cs (mkSt awaiting f) (_ , env) lnReply i ()
step-cs (mkSt awaiting f) (_ , int) bfDrain    (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , int) lnQuit     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt awaiting f) (_ , int) lnQuitDone (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-cs (mkSt warmD f)    (_ , gov) demote i ()
step-cs (mkSt warmD f)    (_ , gov) warm   i ()
step-cs (mkSt warmD f)    (_ , gov) tmo    i ()
step-cs (mkSt warmD f)    (_ , gov) cold   i ()
step-cs (mkSt warmD f)    (_ , rtn) p      i ()
step-cs (mkSt warmD f)    (_ , env) e      i ()
step-cs (mkSt warmD f)    (_ , int) a      i ()
step-cs (mkSt timedOut f) (_ , gov) demote i ()
step-cs (mkSt timedOut f) (_ , gov) warm   i ()
step-cs (mkSt timedOut f) (_ , gov) tmo    i ()
step-cs (mkSt timedOut f) (_ , gov) cold   (j , _) refl = j , λ ()
step-cs (mkSt timedOut f) (_ , rtn) p      i ()
step-cs (mkSt timedOut f) (_ , env) e      i ()
step-cs (mkSt timedOut f) (_ , int) a      i ()
step-cs (mkSt coldD f)    (_ , gov) demote i ()
step-cs (mkSt coldD f)    (_ , gov) warm   i ()
step-cs (mkSt coldD f)    (_ , gov) tmo    i ()
step-cs (mkSt coldD f)    (_ , gov) cold   i ()
step-cs (mkSt coldD f)    (_ , rtn) p      i ()
step-cs (mkSt coldD f)    (_ , env) e      i ()
step-cs (mkSt coldD f)    (_ , int) a      i ()

-- the cs invariant holds along every Steps run
steps-cs : ∀ {v c s w s′} → Steps (Post false v c) s w s′ → Inv-cs s → Inv-cs s′
steps-cs done i = i
steps-cs {s = s} (more {at = at} {a = a} eq ss) i = steps-cs ss (step-cs s at a i eq)

-- D3: post-PR, no Praos block during the wait makes Warm unreachable
post-noBlock-noWarm : ∀ {v c w s} → Steps (Post false v c) st₀ w s → gph s ≢ warmD
post-noBlock-noWarm ss = proj₂ (steps-cs ss (inj₁ refl , λ ()))

-- D3 run form: post-PR with the timer on and no Praos block, every maximal run ends tmo then cold
-- (deadlock free, bounded, no τ so no divergence; √-ended traces contain tmo then cold)
post-noBlock-endsCold : ∀ {v} → RunCold (Post false v true)
post-noBlock-endsCold = timer-deadlockFree refl , steps⇒traceBound steps-13 , endsCold step-cs proj₂ (inj₁ refl , λ ())

-- vacuity guard (PLAN.md review focus 1): the post-PR system reaches awaiting with every protocol but cs
-- returned.  In the model only; the real BlockFetch registry bracket waits for the same peer's ChainSync
-- (RESEARCH.md §3, BFReg:160-163), so `bf ≡ fin` with cs not returned is not a realistic state.
post-noBlock-nearlyWarm : Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s ∈ St ]
                 (Steps (Post false true true) st₀ w s × gph s ≡ awaiting
                  × ps s tx ≡ fin × ps s bf ≡ fin × ps s lf ≡ fin × ps s ln ≡ fin)
post-noBlock-nearlyWarm =
  ( ((GAct , gov) , demote) ∷ ((IntAct , int) , bfDrain) ∷ ((EnvAct , env) , txReq) ∷ ((IntAct , int) , lnQuit) ∷ ((IntAct , int) , lnQuitDone) ∷ ((Proto , rtn) , tx) ∷ ((Proto , rtn) , bf) ∷ ((Proto , rtn) , lf) ∷ ((Proto , rtn) , ln) ∷ [] )
  , _
  , more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl done))))))))
  , refl , refl , refl , refl , refl

-- D4: two modes that differ only in the LeiosNotify variant (blocks and txReqs on, no Leios load, no
-- timeout): before the PR no run reaches Warm, after it every maximal run does.  The post-PR half holds
-- under README §2's LeiosNotify assumptions (MsgQuit sent on Terminate even with a full pipeline; both
-- ends run PR 2344).
contrast : (∀ {w s} → Steps (Pre true true false) st₀ w s → gph s ≢ warmD)
         × ((tr : Trace U (Sys (Post true true false))) → ◇ᵗ (atom WarmFired) tr)
contrast = pre-neverWarm , post-warmLTL
