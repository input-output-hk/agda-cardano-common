{-# OPTIONS --guardedness #-}

-- D3 (DESIGN.md §5) and D4: after ouroboros-consensus PR 2344 the demotion still cannot end Warm if the
-- remote never sends a blocking MsgRequestTxIds (TxSubmission2) or no Praos block arrives (ChainSync),
-- and the before/after contrast under the same environment.  Vacuity guards show that in each case every
-- other hot protocol (LeiosNotify included) can still return, so the blocker is exactly that protocol.
module HotDemotion.Blockers where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong)

open import Process_Trees
open import HotDemotion.Model
open import HotDemotion.PrePR using (J; J-no-ready; J-notFin; stepIf-inv; if-just; pre-neverWarm; Pre)
open import HotDemotion.PostPR using (Post; WarmFired; post-warmLTL)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.LTL.Traces_Based {E = Ev} {I = ExtI Ev} using (Trace; ◇ᵗ; atom)

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

-- vacuity guard (Review Focus 1): the post-PR system reaches awaiting with every protocol but tx returned
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

-- vacuity guard (Review Focus 1): the post-PR system reaches awaiting with every protocol but cs returned
post-noBlock-nearlyWarm : Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s ∈ St ]
                 (Steps (Post false true true) st₀ w s × gph s ≡ awaiting
                  × ps s tx ≡ fin × ps s bf ≡ fin × ps s lf ≡ fin × ps s ln ≡ fin)
post-noBlock-nearlyWarm =
  ( ((GAct , gov) , demote) ∷ ((IntAct , int) , bfDrain) ∷ ((EnvAct , env) , txReq) ∷ ((IntAct , int) , lnQuit) ∷ ((IntAct , int) , lnQuitDone) ∷ ((Proto , rtn) , tx) ∷ ((Proto , rtn) , bf) ∷ ((Proto , rtn) , lf) ∷ ((Proto , rtn) , ln) ∷ [] )
  , _
  , more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl done))))))))
  , refl , refl , refl , refl , refl

-- D4: same environment (blocks and txReqs on, no Leios load): before the PR no run reaches Warm,
-- after it every maximal run does
contrast : (∀ {w s} → Steps (Pre true true) st₀ w s → gph s ≢ warmD)
         × ((tr : Trace U (Sys (Post true true false))) → ◇ᵗ (atom WarmFired) tr)
contrast = pre-neverWarm , post-warmLTL
