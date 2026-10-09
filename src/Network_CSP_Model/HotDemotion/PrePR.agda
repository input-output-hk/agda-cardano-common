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
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; +-monoʳ-≤; +-suc; m≤m+n; n≤1+n)
open import Data.List using (length)
open import Data.List.Properties using (length-++; ∷ʳ-injective; ∷-injectiveʳ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)

open import Process_Trees
open import HotDemotion.Model
open import HotDemotion.Lift
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_)
open import Semantics.Deadlock {E = Ev} {I = ExtI Ev} using (DeadlockFree; IsStuck; _⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)

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

-- D1, state form: no reachable state is Warm
pre-neverWarm : ∀ {b t w s} → Steps (Pre b t) st₀ w s → gph s ≢ warmD
pre-neverWarm ss = proj₂ (steps-inv ss inv₀)

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

-- ===================== D1 run form (fix round 1) =====================
-- Every maximal run of `Sys (Pre b t)` contains tmo and then cold, for all b t:
--  * (a) `pre-deadlockFree` / `pre-progress`: a reachable non-final state always has an enabled move
--    (hot: demote; awaiting: tmo, as `timer` is on whatever blocks/txReqs are; timedOut: cold), so a run
--    is never stuck before √;
--  * (b) `pre-bounded`: every trace has length ≤ 11, so runs are finite;
--  * (c) `pre-endsCold`: every trace ending in √ is  t₁ ++ GV tmo ∷ t₂  with cold in t₂.
-- Hence a maximal run is finite (b), cannot stop short of √ (a), and so is a √-run, which contains tmo
-- then cold (c).  Nothing depends on blocks/txReqs: if an env event is off its protocol just stays
-- waiting and tmo remains available.

-- a state that is not final always has an enabled move (needs only timer = true)
prog : ∀ {b t s} → final s ≡ false → Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] Σ[ s′ ∈ St ] (sstep at a (Pre b t) s ≡ just s′)
prog {s = mkSt hot f}      _ = (GAct , gov) , demote , _ , refl
prog {s = mkSt awaiting f} _ = (GAct , gov) , tmo , _ , refl
prog {s = mkSt timedOut f} _ = (GAct , gov) , cold , _ , refl
prog {s = mkSt warmD f}    ()
prog {s = mkSt coldD f}    ()

-- (a) progress form: every reachable non-final state has an enabled sstep move
pre-progress : ∀ {b t w s} → Steps (Pre b t) st₀ w s → final s ≡ false
             → Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] Σ[ s′ ∈ St ] (sstep at a (Pre b t) s ≡ just s′)
pre-progress _ fe = prog fe

-- a √-free run of SysAt is a Steps run
∖√-reach : ∀ {m s es t′} → SysAt m s ⟹∖√⟨ es ⟩ t′
         → Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s′ ∈ St ] (Steps m s w s′ × t′ ≡ SysAt m s′)
∖√-reach ∖√-refl = [] , _ , done , refl
∖√-reach (∖√-τ st _) = ⊥-elim (Sys-no-τ st)
∖√-reach {m} (∖√-ev {e = evLabel X ch a} st rest) with Sys-ev-inv st
... | s₁ , eq , refl with ∖√-reach rest
...   | w , s′ , ss , e = ((X , ch) , a) ∷ w , s′ , more eq ss , e

-- no SysAt state of Pre is stuck
not-stuck : ∀ {b t} s → IsStuck (SysAt (Pre b t) s) → ⊥
not-stuck (mkSt hot f)      st = st (Sys-ev-intro (GAct , gov) demote refl refl)
not-stuck (mkSt awaiting f) st = st (Sys-ev-intro (GAct , gov) tmo refl refl)
not-stuck (mkSt timedOut f) st = st (Sys-ev-intro (GAct , gov) cold refl refl)
not-stuck (mkSt warmD f)    st = st (sRet refl)
not-stuck (mkSt coldD f)    st = st (sRet refl)

-- (a) the pre-PR system is deadlock free (√ is not a deadlock)
pre-deadlockFree : ∀ {b t} → DeadlockFree (Sys (Pre b t))
pre-deadlockFree r st with ∖√-reach r
... | w , s′ , ss , refl = not-stuck s′ st

-- phase potentials: remaining moves of one protocol (LeiosNotify only counts a pending return,
-- since in Pre it can neither be answered nor quit)
pot : PSt → ℕ
pot running = 0
pot waitEnv = 2
pot needInt = 2
pot quitSent = 1
pot ready = 1
pot fin = 0

-- LeiosNotify potential: only `ready` can still move (to fin)
potLn : PSt → ℕ
potLn ready = 1
potLn _     = 0

-- sum of the five potentials
rk5 : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
rk5 a b c d e = a + (b + (c + (d + e)))

-- potential of a phase map
rk : (Proto → PSt) → ℕ
rk f = rk5 (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) (potLn (f ln))

-- the rank: demote (1) + [awaiting: bfDrain, block, txReq, 4 rtn (cs bf tx lf) = 7, tmo, cold = 2 + rk]
-- hot = 10, awaiting after demote = 2 + 7 = 9
rank : St → ℕ
rank (mkSt hot _)      = 10
rank (mkSt awaiting f) = 2 + rk f
rank (mkSt warmD _)    = 0
rank (mkSt timedOut _) = 1
rank (mkSt coldD _)    = 0

-- strictness is preserved under a left summand
lift1 : ∀ a {x y} → suc x ≤ y → suc (a + x) ≤ a + y
lift1 a h = ≤-trans (≤-reflexive (sym (+-suc a _))) (+-monoʳ-≤ a h)

-- a drop in the first summand
dropA : ∀ a a′ b c d e → suc a′ ≤ a → suc (rk5 a′ b c d e) ≤ rk5 a b c d e
dropA a a′ b c d e h = +-monoˡ-≤ (b + (c + (d + e))) h

-- a drop in the second summand
dropB : ∀ a b b′ c d e → suc b′ ≤ b → suc (rk5 a b′ c d e) ≤ rk5 a b c d e
dropB a b b′ c d e h = lift1 a (+-monoˡ-≤ (c + (d + e)) h)

-- a drop in the third summand
dropC : ∀ a b c c′ d e → suc c′ ≤ c → suc (rk5 a b c′ d e) ≤ rk5 a b c d e
dropC a b c c′ d e h = lift1 a (lift1 b (+-monoˡ-≤ (d + e) h))

-- a drop in the fourth summand
dropD : ∀ a b c d d′ e → suc d′ ≤ d → suc (rk5 a b c d′ e) ≤ rk5 a b c d e
dropD a b c d d′ e h = lift1 a (lift1 b (lift1 c (+-monoˡ-≤ e h)))

-- a drop in the fifth summand
dropE : ∀ a b c d e e′ → suc e′ ≤ e → suc (rk5 a b c d e′) ≤ rk5 a b c d e
dropE a b c d e e′ h = lift1 a (lift1 b (lift1 c (lift1 d h)))

-- a matched ready phase is ready
eqP-ready : ∀ x → eqP x ready ≡ true → x ≡ ready
eqP-ready ready _ = refl
eqP-ready running ()
eqP-ready waitEnv ()
eqP-ready needInt ()
eqP-ready quitSent ()
eqP-ready fin ()

-- a matched waitEnv phase is waitEnv
eqP-wait : ∀ x → eqP x waitEnv ≡ true → x ≡ waitEnv
eqP-wait waitEnv _ = refl
eqP-wait running ()
eqP-wait needInt ()
eqP-wait quitSent ()
eqP-wait ready ()
eqP-wait fin ()

-- a matched needInt phase is needInt
eqP-need : ∀ x → eqP x needInt ≡ true → x ≡ needInt
eqP-need needInt _ = refl
eqP-need running ()
eqP-need waitEnv ()
eqP-need quitSent ()
eqP-need ready ()
eqP-need fin ()

-- every sstep move of Pre strictly decreases the rank
step-rank : ∀ {b t} s {s′} at a → sstep at a (Pre b t) s ≡ just s′ → suc (rank s′) ≤ rank s
step-rank (mkSt hot f)      (_ , gov) demote refl = ≤-refl
step-rank (mkSt hot f)      (_ , gov) warm   ()
step-rank (mkSt hot f)      (_ , gov) tmo    ()
step-rank (mkSt hot f)      (_ , gov) cold   ()
step-rank (mkSt hot f)      (_ , rtn) p      ()
step-rank (mkSt hot f)      (_ , env) e      ()
step-rank (mkSt hot f)      (_ , int) a      ()
step-rank (mkSt awaiting f) (_ , gov) demote ()
step-rank (mkSt awaiting f) (_ , gov) warm   h with allFin (mkSt awaiting f) | h
... | true  | refl = s≤s z≤n
... | false | ()
step-rank (mkSt awaiting f) (_ , gov) tmo    refl = s≤s (s≤s z≤n)
step-rank (mkSt awaiting f) (_ , gov) cold   ()
step-rank (mkSt awaiting f) (_ , rtn) cs     h with stepIf-inv h
... | q , refl rewrite eqP-ready (f cs) q = lift1 2 (dropA 1 0 (pot (f bf)) (pot (f tx)) (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , rtn) bf     h with stepIf-inv h
... | q , refl rewrite eqP-ready (f bf) q = lift1 2 (dropB (pot (f cs)) 1 0 (pot (f tx)) (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , rtn) tx     h with stepIf-inv h
... | q , refl rewrite eqP-ready (f tx) q = lift1 2 (dropC (pot (f cs)) (pot (f bf)) 1 0 (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , rtn) lf     h with stepIf-inv h
... | q , refl rewrite eqP-ready (f lf) q = lift1 2 (dropD (pot (f cs)) (pot (f bf)) (pot (f tx)) 1 0 (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , rtn) ln     h with stepIf-inv h
... | q , refl rewrite eqP-ready (f ln) q = lift1 2 (dropE (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) 1 0 ≤-refl)
step-rank {b} (mkSt awaiting f) (_ , env) block   h with stepIf-inv (if-just b h)
... | q , refl rewrite eqP-wait (f cs) q = lift1 2 (dropA 2 1 (pot (f bf)) (pot (f tx)) (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank {b} {t} (mkSt awaiting f) (_ , env) txReq   h with stepIf-inv (if-just t h)
... | q , refl rewrite eqP-wait (f tx) q = lift1 2 (dropC (pot (f cs)) (pot (f bf)) 2 1 (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , env) lnReply ()
step-rank (mkSt awaiting f) (_ , int) bfDrain    h with stepIf-inv h
... | q , refl rewrite eqP-need (f bf) q = lift1 2 (dropB (pot (f cs)) 2 1 (pot (f tx)) (pot (f lf)) (potLn (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , int) lnQuit     ()
step-rank (mkSt awaiting f) (_ , int) lnQuitDone ()
step-rank (mkSt warmD f)    (_ , gov) demote ()
step-rank (mkSt warmD f)    (_ , gov) warm   ()
step-rank (mkSt warmD f)    (_ , gov) tmo    ()
step-rank (mkSt warmD f)    (_ , gov) cold   ()
step-rank (mkSt warmD f)    (_ , rtn) p      ()
step-rank (mkSt warmD f)    (_ , env) e      ()
step-rank (mkSt warmD f)    (_ , int) a      ()
step-rank (mkSt timedOut f) (_ , gov) demote ()
step-rank (mkSt timedOut f) (_ , gov) warm   ()
step-rank (mkSt timedOut f) (_ , gov) tmo    ()
step-rank (mkSt timedOut f) (_ , gov) cold   refl = ≤-refl
step-rank (mkSt timedOut f) (_ , rtn) p      ()
step-rank (mkSt timedOut f) (_ , env) e      ()
step-rank (mkSt timedOut f) (_ , int) a      ()
step-rank (mkSt coldD f)    (_ , gov) demote ()
step-rank (mkSt coldD f)    (_ , gov) warm   ()
step-rank (mkSt coldD f)    (_ , gov) tmo    ()
step-rank (mkSt coldD f)    (_ , gov) cold   ()
step-rank (mkSt coldD f)    (_ , rtn) p      ()
step-rank (mkSt coldD f)    (_ , env) e      ()
step-rank (mkSt coldD f)    (_ , int) a      ()

-- a Steps run's length plus the final rank is at most the initial rank
steps-len : ∀ {b t s w s′} → Steps (Pre b t) s w s′ → length w + rank s′ ≤ rank s
steps-len done = ≤-refl
steps-len {s = s} (more {at = at} {a = a} eq ss) = ≤-trans (s≤s (steps-len ss)) (step-rank s at a eq)

-- the label list has the length of the Steps list
lab-length : ∀ w → length (lab w) ≡ length w
lab-length []              = refl
lab-length (((X , ch) , a) ∷ w) = cong suc (lab-length w)

-- every Steps run from st₀ has at most 10 moves
steps-10 : ∀ {b t w s} → Steps (Pre b t) st₀ w s → length w ≤ 10
steps-10 ss = ≤-trans (m≤m+n _ _) (steps-len ss)

-- (b) N = 11: demote, 3 env/int moves (bfDrain, block, txReq), 4 rtn (cs bf tx lf; ln never returns),
-- tmo, cold = 10 moves, plus one final √
pre-bounded : ∀ {b t tr W} → Sys (Pre b t) ⟹⟨ tr ⟩ W → length tr ≤ 11
pre-bounded x with Sys-anyTrace x
... | w , s′ , ss , inj₁ (refl , _) = ≤-trans (≤-reflexive (lab-length w)) (≤-trans (steps-10 ss) (n≤1+n 10))
... | w , s′ , ss , inj₂ (r , refl , _) =
  ≤-trans (≤-reflexive (length-++ (lab w)))
          (+-monoˡ-≤ 1 (≤-trans (≤-reflexive (lab-length w)) (steps-10 ss)))

-- a trace ending in √ is not a list of evl letters
lab-last : ∀ tr (r : U) w → tr ++ √ r ∷ [] ≡ lab w → ⊥
lab-last []        r []                   ()
lab-last []        r (((X , ch) , a) ∷ w) ()
lab-last (_ ∷ _)   r []                   ()
lab-last (_ ∷ tr)  r (((X , ch) , a) ∷ w) e = lab-last tr r w (∷-injectiveʳ e)

-- the trace contains tmo and, after it, cold
TC : List (Event√ U) → Set₁
TC t = Σ[ t₁ ∈ List (Event√ U) ] Σ[ t₂ ∈ List (Event√ U) ] (t ≡ t₁ ++ GV tmo ∷ t₂ × Any (_≡ GV cold) t₂)

-- prepend a letter to a TC trace
TC-cons : ∀ {t} x → TC t → TC (x ∷ t)
TC-cons x (t₁ , t₂ , e , c) = x ∷ t₁ , t₂ , cong (x ∷_) e , c

-- the tmo letter followed by a trace containing cold
TC-tmo : ∀ {x t₂} → x ≡ GV tmo → Any (_≡ GV cold) t₂ → TC (x ∷ t₂)
TC-tmo l c = [] , _ , cong (_∷ _) l , c

-- a move from awaiting stays awaiting or is the tmo move
aw-move : ∀ {b t f s′} at a → Inv (mkSt awaiting f) → sstep at a (Pre b t) (mkSt awaiting f) ≡ just s′
        → (gph s′ ≡ awaiting) ⊎ (gph s′ ≡ timedOut × lbl at a ≡ GV tmo)
aw-move (_ , gov) demote i ()
aw-move {b} {t} (_ , gov) warm   i h = ⊥-elim (warm-step {b} {t} i h)
aw-move (_ , gov) tmo    i refl = inj₂ (refl , refl)
aw-move (_ , gov) cold   i ()
aw-move (_ , rtn) cs     i h with stepIf-inv h
... | _ , refl = inj₁ refl
aw-move (_ , rtn) bf     i h with stepIf-inv h
... | _ , refl = inj₁ refl
aw-move (_ , rtn) tx     i h with stepIf-inv h
... | _ , refl = inj₁ refl
aw-move (_ , rtn) lf     i h with stepIf-inv h
... | _ , refl = inj₁ refl
aw-move (_ , rtn) ln     (j , _) h = ⊥-elim (J-no-ready j (proj₁ (stepIf-inv h)))
aw-move {b} (_ , env) block   i h with stepIf-inv (if-just b h)
... | _ , refl = inj₁ refl
aw-move {b} {t} (_ , env) txReq   i h with stepIf-inv (if-just t h)
... | _ , refl = inj₁ refl
aw-move (_ , env) lnReply i ()
aw-move (_ , int) bfDrain    i h with stepIf-inv h
... | _ , refl = inj₁ refl
aw-move (_ , int) lnQuit     i ()
aw-move (_ , int) lnQuitDone i ()

-- from a timed-out state the run to a final state contains cold
run-to : ∀ {b t s w s′} → gph s ≡ timedOut → Steps (Pre b t) s w s′ → final s′ ≡ true → Any (_≡ GV cold) (lab w)
run-to {s = mkSt _ f} refl done ()
run-to {s = mkSt _ f} refl (more {at = _ , gov} {a = demote} () ss) _
run-to {s = mkSt _ f} refl (more {at = _ , gov} {a = warm}   () ss) _
run-to {s = mkSt _ f} refl (more {at = _ , gov} {a = tmo}    () ss) _
run-to {s = mkSt _ f} refl (more {at = _ , gov} {a = cold}   eq ss) _ = here refl
run-to {s = mkSt _ f} refl (more {at = _ , rtn} () ss) _
run-to {s = mkSt _ f} refl (more {at = _ , env} () ss) _
run-to {s = mkSt _ f} refl (more {at = _ , int} () ss) _

-- from an awaiting state (with the invariant) the run to a final state contains tmo then cold
run-aw : ∀ {b t s w s′} → gph s ≡ awaiting → Inv s → Steps (Pre b t) s w s′ → final s′ ≡ true → TC (lab w)
run-aw {s = mkSt _ f} refl i done ()
run-aw {s = mkSt _ f} refl i (more {at = at} {a = a} eq ss) fz with aw-move at a i eq
... | inj₁ g = TC-cons (lbl at a) (run-aw g (step-inv _ at a i eq) ss fz)
... | inj₂ (g , l) = TC-tmo l (run-to g ss fz)

-- from the hot start the run to a final state contains tmo then cold
run-hot : ∀ {b t s w s′} → gph s ≡ hot → Steps (Pre b t) s w s′ → final s′ ≡ true → TC (lab w)
run-hot {s = mkSt _ f} refl done ()
run-hot {s = mkSt _ f} refl (more {at = _ , gov} {a = demote} refl ss) fz =
  TC-cons (GV demote) (run-aw refl (inj₂ refl , λ ()) ss fz)
run-hot {s = mkSt _ f} refl (more {at = _ , gov} {a = warm}   () ss) _
run-hot {s = mkSt _ f} refl (more {at = _ , gov} {a = tmo}    () ss) _
run-hot {s = mkSt _ f} refl (more {at = _ , gov} {a = cold}   () ss) _
run-hot {s = mkSt _ f} refl (more {at = _ , rtn} () ss) _
run-hot {s = mkSt _ f} refl (more {at = _ , env} () ss) _
run-hot {s = mkSt _ f} refl (more {at = _ , int} () ss) _

-- (c) every trace of the pre-PR system that ends in √ is  t₁ ++ GV tmo ∷ t₂  with cold in t₂
-- (stronger than Any tmo × Any cold: it also orders tmo before cold)
pre-endsCold : ∀ {b t tr r W} → Sys (Pre b t) ⟹⟨ tr ++ √ r ∷ [] ⟩ W → TC tr
pre-endsCold {tr = tr} {r} x with Sys-anyTrace x
... | w , s′ , ss , inj₁ (e , _) = ⊥-elim (lab-last tr r w e)
... | w , s′ , ss , inj₂ (r′ , e , fz) with ∷ʳ-injective tr (lab w) e
...   | refl , _ = run-hot refl ss fz
