{-# OPTIONS --guardedness #-}

-- D1 (DESIGN.md §5): before ouroboros-consensus PR 2344, with no Leios load, the demotion
-- can never end Warm.  Adaptations to the brief: traces are arbitrary `t : List (Event√ U)`
-- (√-ended ones handled via `Sys-anyTrace`), `GV-event warm` is the letter `GV warm`, and
-- Steps entries are `((X , ch) , a)` pairs.
module HotDemotion.PrePR where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Process_Trees
open import HotDemotion.Model
open import HotDemotion.Lift
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_)

-- the pre-PR mode: env flags for blocks / txReqs, no Leios load, timer on
Pre : Bool → Bool → Mode
Pre b t = mode pre b t false true

-- a LeiosNotify phase that has not progressed past waiting for a Leios reply
J : PSt → Set
J x = x ≡ running ⊎ x ≡ waitEnv

-- the invariant: LeiosNotify is still running / waiting, and the peer is not Warm
Inv : St → Set
Inv s = J (ps s ln) × (gph s ≢ warmD)

-- a phase of J is never `ready`
J-no-ready : ∀ {x} → J x → eqP x ready ≡ true → ⊥
J-no-ready (inj₁ refl) ()
J-no-ready (inj₂ refl) ()

-- a succeeding stepIf means the phase matched and the successor is the given state
stepIf-inv : ∀ {x y s s′} → stepIf x y s ≡ just s′ → eqP x y ≡ true × s ≡ s′
stepIf-inv {x} {y} {s} h with eqP x y | h
... | true  | refl = refl , refl
... | false | ()

-- a succeeding guarded move means the guard held
if-just : ∀ {A : Set} (c : Bool) {x : Maybe A} {y} → (if c then x else nothing) ≡ just y → x ≡ just y
if-just true  h = h
if-just false ()

-- if the LeiosNotify phase is not fin, allFin is false
allFin-ln : ∀ s → isFin (ps s ln) ≡ false → allFin s ≡ false
allFin-ln s e rewrite e =
  trans (cong (isFin (ps s cs) ∧_) (trans (cong (isFin (ps s bf) ∧_) (trans (cong (isFin (ps s tx) ∧_) (z (isFin (ps s lf)))) (z (isFin (ps s tx))))) (z (isFin (ps s bf))))) (z (isFin (ps s cs)))
  where
  -- x ∧ false is false
  z : ∀ x → (x ∧ false) ≡ false
  z true  = refl
  z false = refl

-- a J phase is not fin
J-notFin : ∀ {x} → J x → isFin x ≡ false
J-notFin (inj₁ refl) = refl
J-notFin (inj₂ refl) = refl

-- the warm move is impossible while the invariant holds
warm-step : ∀ {b t s s′} → Inv s → sstep (GAct , gov) warm (Pre b t) s ≡ just s′ → ⊥
warm-step {s = mkSt hot f}      _ ()
warm-step {s = mkSt warmD f}    _ ()
warm-step {s = mkSt timedOut f} _ ()
warm-step {s = mkSt coldD f}    _ ()
warm-step {s = mkSt awaiting f} (j , _) h with allFin (mkSt awaiting f) | allFin-ln (mkSt awaiting f) (J-notFin j) | h
... | true  | () | _
... | false | _  | ()

-- every sstep move preserves the invariant
step-inv : ∀ {b t} s {s′} at a → Inv s → sstep at a (Pre b t) s ≡ just s′ → Inv s′
step-inv (mkSt hot f)      (_ , gov) demote i refl = inj₂ refl , λ ()
step-inv (mkSt hot f)      (_ , gov) warm   i ()
step-inv (mkSt hot f)      (_ , gov) tmo    i ()
step-inv (mkSt hot f)      (_ , gov) cold   i ()
step-inv (mkSt hot f)      (_ , rtn) p      i ()
step-inv (mkSt hot f)      (_ , env) e      i ()
step-inv (mkSt hot f)      (_ , int) a      i ()
step-inv (mkSt awaiting f) (_ , gov) demote i ()
step-inv {b} {t} (mkSt awaiting f) (_ , gov) warm   i h = ⊥-elim (warm-step {b} {t} i h)
step-inv (mkSt awaiting f) (_ , gov) tmo    (j , _) refl = j , λ ()
step-inv (mkSt awaiting f) (_ , gov) cold   i ()
step-inv (mkSt awaiting f) (_ , rtn) cs     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , rtn) bf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , rtn) tx     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , rtn) lf     (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , rtn) ln     (j , _) h = ⊥-elim (J-no-ready j (proj₁ (stepIf-inv h)))
step-inv {b} (mkSt awaiting f) (_ , env) block   (j , _) h with stepIf-inv (if-just b h)
... | _ , refl = j , λ ()
step-inv {b} {t} (mkSt awaiting f) (_ , env) txReq   (j , _) h with stepIf-inv (if-just t h)
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , env) lnReply i ()
step-inv (mkSt awaiting f) (_ , int) bfDrain    (j , _) h with stepIf-inv h
... | _ , refl = j , λ ()
step-inv (mkSt awaiting f) (_ , int) lnQuit     i ()
step-inv (mkSt awaiting f) (_ , int) lnQuitDone i ()
step-inv (mkSt warmD f)    (_ , gov) demote i ()
step-inv (mkSt warmD f)    (_ , gov) warm   i ()
step-inv (mkSt warmD f)    (_ , gov) tmo    i ()
step-inv (mkSt warmD f)    (_ , gov) cold   i ()
step-inv (mkSt warmD f)    (_ , rtn) p      i ()
step-inv (mkSt warmD f)    (_ , env) e      i ()
step-inv (mkSt warmD f)    (_ , int) a      i ()
step-inv (mkSt timedOut f) (_ , gov) demote i ()
step-inv (mkSt timedOut f) (_ , gov) warm   i ()
step-inv (mkSt timedOut f) (_ , gov) tmo    i ()
step-inv (mkSt timedOut f) (_ , gov) cold   (j , _) refl = j , λ ()
step-inv (mkSt timedOut f) (_ , rtn) p      i ()
step-inv (mkSt timedOut f) (_ , env) e      i ()
step-inv (mkSt timedOut f) (_ , int) a      i ()
step-inv (mkSt coldD f)    (_ , gov) demote i ()
step-inv (mkSt coldD f)    (_ , gov) warm   i ()
step-inv (mkSt coldD f)    (_ , gov) tmo    i ()
step-inv (mkSt coldD f)    (_ , gov) cold   i ()
step-inv (mkSt coldD f)    (_ , rtn) p      i ()
step-inv (mkSt coldD f)    (_ , env) e      i ()
step-inv (mkSt coldD f)    (_ , int) a      i ()

-- the invariant holds along every Steps run
steps-inv : ∀ {b t s w s′} → Steps (Pre b t) s w s′ → Inv s → Inv s′
steps-inv done i = i
steps-inv {s = s} (more {at = at} {a = a} eq ss) i = steps-inv ss (step-inv s at a i eq)

-- the invariant holds initially
inv₀ : Inv st₀
inv₀ = inj₁ refl , λ ()

-- the LeiosNotify phase never reaches ready/fin while lnLoad is false
pre-ln-stuck : ∀ {b t s w} → Steps (Pre b t) st₀ w s → ps s ln ≢ ready × ps s ln ≢ fin
pre-ln-stuck ss with proj₁ (steps-inv ss inv₀)
... | inj₁ e = (λ x → case trans (sym e) x of λ ()) , (λ x → case trans (sym e) x of λ ())
... | inj₂ e = (λ x → case trans (sym e) x of λ ()) , (λ x → case trans (sym e) x of λ ())

-- D1, run form: no reachable state is Warm
pre-endsCold : ∀ {b t w s} → Steps (Pre b t) st₀ w s → gph s ≢ warmD
pre-endsCold ss = proj₂ (steps-inv ss inv₀)

-- the timeout is always an escape while awaiting (Review Focus 2)
tmo-enabled : ∀ {m s w} → timer m ≡ true → Steps m st₀ w s → gph s ≡ awaiting
            → Σ[ s′ ∈ St ] (sstep (GAct , gov) tmo m s ≡ just s′)
tmo-enabled {m} {mkSt _ f} te _ refl rewrite te = _ , refl

-- no warm letter in any Steps run that starts in an invariant state
noWarm-steps : ∀ {b t s w s′} → Steps (Pre b t) s w s′ → Inv s → ¬ Any (_≡ GV warm) (lab w)
noWarm-steps done i ()
noWarm-steps {s = s} (more {at = _ , gov} {a = demote} eq ss) i (here ())
noWarm-steps {b} {t} {s = s} (more {at = _ , gov} {a = warm}   eq ss) i (here _) = warm-step {b} {t} i eq
noWarm-steps {s = s} (more {at = _ , gov} {a = tmo}    eq ss) i (here ())
noWarm-steps {s = s} (more {at = _ , gov} {a = cold}   eq ss) i (here ())
noWarm-steps {s = s} (more {at = _ , rtn} eq ss) i (here ())
noWarm-steps {s = s} (more {at = _ , env} eq ss) i (here ())
noWarm-steps {s = s} (more {at = _ , int} eq ss) i (here ())
noWarm-steps {s = s} (more {at = at} {a = a} eq ss) i (there p) = noWarm-steps ss (step-inv s at a i eq) p

-- a √ letter is not the warm letter
√-notWarm : ∀ {r : U} → ¬ Any (_≡ GV warm) (√ r ∷ [])
√-notWarm (here ())
√-notWarm (there ())

-- D1: no trace (√-ended or not) of the pre-PR system contains warm
pre-noWarm : ∀ {b t tr W} → Sys (Pre b t) ⟹⟨ tr ⟩ W → ¬ Any (_≡ GV warm) tr
pre-noWarm r with Sys-anyTrace r
... | w , s′ , ss , inj₁ (refl , _) = noWarm-steps ss inv₀
... | w , s′ , ss , inj₂ (rr , refl , _) = λ a → case ++⁻ _ a of λ where
  (inj₁ x) → noWarm-steps ss inv₀ x
  (inj₂ y) → √-notWarm y

-- vacuity guard (Review Focus 1): the pre-PR system reaches awaiting with all protocols but ln returned
pre-nearlyWarm : Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s ∈ St ]
                 (Steps (Pre true true) st₀ w s × gph s ≡ awaiting
                  × ps s cs ≡ fin × ps s bf ≡ fin × ps s tx ≡ fin × ps s lf ≡ fin)
pre-nearlyWarm =
  ( ((GAct , gov) , demote) ∷ ((IntAct , int) , bfDrain) ∷ ((EnvAct , env) , block) ∷ ((EnvAct , env) , txReq)
  ∷ ((Proto , rtn) , cs) ∷ ((Proto , rtn) , bf) ∷ ((Proto , rtn) , tx) ∷ ((Proto , rtn) , lf) ∷ [] )
  , _
  , more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl done)))))))
  , refl , refl , refl , refl , refl
