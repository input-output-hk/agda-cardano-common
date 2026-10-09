{-# OPTIONS --guardedness #-}

-- D2 (DESIGN.md §5): after ouroboros-consensus PR 2344, with no Leios load, the demotion can
-- always still end Warm (D2a), and with the timeout removed it always does, within 12 moves
-- (D2b and the bound).  Adaptations to the brief (as in PrePR): traces are arbitrary
-- `t : List (Event√ U)` (√-ended ones via `Sys-anyTrace`), so the trace bound is 13 = 12 moves
-- plus the final √; Steps entries are `((X , ch) , a)` pairs.
module HotDemotion.PostPR where

open import Level using (Lift) renaming (zero to lzero; suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (just)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-monoˡ-≤; m≤m+n; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees hiding (div)
open PTree
open import HotDemotion.Model
open import HotDemotion.Lift
open import HotDemotion.PrePR
  using (∖√-reach; stepIf-inv; if-just; lift1; dropA; dropB; dropC; dropD; dropE
        ; eqP-ready; eqP-wait; eqP-need; lab-length; rk5; pot)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
open import Semantics.Failures {E = Ev} {I = ExtI Ev} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)
open import Semantics.Deadlock {E = Ev} {I = ExtI Ev} using (DeadlockFree; IsStuck)
open import Semantics.DivergenceFree {E = Ev} {I = ExtI Ev} using (DivergenceFree; deadlock-no-τ)
open import Semantics.WeakBisim {E = Ev} {I = ExtI Ev} using (_═[_]═►_; wev; τ*-refl; τ*-step)
-- only definitions are used from Traces_Based; its two postulates (⟦G⟧⇒⟦G⟧⁺, ¬G⇒F¬) are not
open import Semantics.LTL.Traces_Based {E = Ev} {I = ExtI Ev}
  using (Trace; ∞Trace; step; done; stuck; div; FramePred; atom; ◇ᵗ; ◇ᵗ-now; ◇ᵗ-later)

-- the post-PR mode: env flags for blocks / txReqs, no Leios load, timer flag
Post : Bool → Bool → Bool → Mode
Post b t c = mode post b t false c

-- the timeout-free post-PR mode with blocks and tx requests offered (D2b, bound)
P : Mode
P = Post true true false

-- ===================== Review Focus 4 =====================

-- post-PR LeiosNotify finishes (MsgQuit, the server's answer, return) with no env event
post-ln-noEnv : ∀ {b t c}
              → Steps (Post b t c) (mkSt awaiting (afterTerm post))
                  (((IntAct , int) , lnQuit) ∷ ((IntAct , int) , lnQuitDone) ∷ ((Proto , rtn) , ln) ∷ [])
                  (mkSt awaiting (setP ln fin (setP ln ready (setP ln quitSent (afterTerm post)))))
post-ln-noEnv = more refl (more refl (more refl done))

-- ===================== invariant: every phase can still move =====================

-- the phases each protocol can be in once demoted (post-PR): each non-fin one has a move
Good : Proto → PSt → Set
Good cs waitEnv  = ⊤
Good cs ready    = ⊤
Good cs fin      = ⊤
Good bf needInt  = ⊤
Good bf ready    = ⊤
Good bf fin      = ⊤
Good tx waitEnv  = ⊤
Good tx ready    = ⊤
Good tx fin      = ⊤
Good lf ready    = ⊤
Good lf fin      = ⊤
Good ln needInt  = ⊤
Good ln quitSent = ⊤
Good ln ready    = ⊤
Good ln fin      = ⊤
Good _  _        = ⊥

-- the invariant: while awaiting, every protocol's phase is Good (nothing to say elsewhere)
Inv : St → Set
Inv (mkSt awaiting f) = ∀ p → Good p (f p)
Inv _                 = ⊤

-- fin is Good for every protocol
finGood : ∀ p → Good p fin
finGood cs = tt
finGood bf = tt
finGood tx = tt
finGood lf = tt
finGood ln = tt

-- the post-PR phases right after Terminate are Good
good₀ : ∀ p → Good p (afterTerm post p)
good₀ cs = tt
good₀ bf = tt
good₀ tx = tt
good₀ lf = tt
good₀ ln = tt

-- setting one protocol to a Good phase keeps every phase Good
upd : ∀ f p y → (∀ q → Good q (f q)) → Good p y → ∀ q → Good q (setP p y f q)
upd f cs y i g cs = g
upd f cs y i g bf = i bf
upd f cs y i g tx = i tx
upd f cs y i g lf = i lf
upd f cs y i g ln = i ln
upd f bf y i g cs = i cs
upd f bf y i g bf = g
upd f bf y i g tx = i tx
upd f bf y i g lf = i lf
upd f bf y i g ln = i ln
upd f tx y i g cs = i cs
upd f tx y i g bf = i bf
upd f tx y i g tx = g
upd f tx y i g lf = i lf
upd f tx y i g ln = i ln
upd f lf y i g cs = i cs
upd f lf y i g bf = i bf
upd f lf y i g tx = i tx
upd f lf y i g lf = g
upd f lf y i g ln = i ln
upd f ln y i g cs = i cs
upd f ln y i g bf = i bf
upd f ln y i g tx = i tx
upd f ln y i g lf = i lf
upd f ln y i g ln = g

-- every post-PR sstep move preserves the invariant
step-inv : ∀ {b t c} s {s′} at a → Inv s → sstep at a (Post b t c) s ≡ just s′ → Inv s′
step-inv (mkSt hot f)      (_ , gov) demote i refl = good₀
step-inv (mkSt hot f)      (_ , gov) warm   i ()
step-inv (mkSt hot f)      (_ , gov) tmo    i ()
step-inv (mkSt hot f)      (_ , gov) cold   i ()
step-inv (mkSt hot f)      (_ , rtn) p      i ()
step-inv (mkSt hot f)      (_ , env) e      i ()
step-inv (mkSt hot f)      (_ , int) a      i ()
step-inv (mkSt awaiting f) (_ , gov) demote i ()
step-inv (mkSt awaiting f) (_ , gov) warm   i h with allFin (mkSt awaiting f) | h
... | true  | refl = tt
... | false | ()
step-inv {c = true}  (mkSt awaiting f) (_ , gov) tmo i refl = tt
step-inv {c = false} (mkSt awaiting f) (_ , gov) tmo i ()
step-inv (mkSt awaiting f) (_ , gov) cold   i ()
step-inv (mkSt awaiting f) (_ , rtn) p      i h with stepIf-inv h
... | _ , refl = upd f p fin i (finGood p)
step-inv {b} (mkSt awaiting f) (_ , env) block i h with stepIf-inv (if-just b h)
... | _ , refl = upd f cs ready i tt
step-inv {t = t} (mkSt awaiting f) (_ , env) txReq i h with stepIf-inv (if-just t h)
... | _ , refl = upd f tx ready i tt
step-inv (mkSt awaiting f) (_ , env) lnReply i ()
step-inv (mkSt awaiting f) (_ , int) bfDrain i h with stepIf-inv h
... | _ , refl = upd f bf ready i tt
step-inv (mkSt awaiting f) (_ , int) lnQuit i h with stepIf-inv h
... | _ , refl = upd f ln quitSent i tt
step-inv (mkSt awaiting f) (_ , int) lnQuitDone i h with stepIf-inv h
... | _ , refl = upd f ln ready i tt
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
step-inv (mkSt timedOut f) (_ , gov) cold   i refl = tt
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
steps-inv : ∀ {b t c s w s′} → Steps (Post b t c) s w s′ → Inv s → Inv s′
steps-inv done i = i
steps-inv {s = s} (more {at = at} {a = a} eq ss) i = steps-inv ss (step-inv s at a i eq)

-- ===================== progress: a non-tmo move always exists while awaiting =====================

-- the successor of a chosen move is still awaiting, or Warm
Next : St → Set
Next s′ = gph s′ ≡ awaiting ⊎ gph s′ ≡ warmD

-- phase equality is reflexive
eqP-refl : ∀ x → eqP x x ≡ true
eqP-refl running  = refl
eqP-refl waitEnv  = refl
eqP-refl needInt  = refl
eqP-refl quitSent = refl
eqP-refl ready    = refl
eqP-refl fin      = refl

-- a guard on a matching phase succeeds
stepIf-ok : ∀ {x y} (s : St) → x ≡ y → stepIf x y s ≡ just s
stepIf-ok {y = y} s refl rewrite eqP-refl y = refl

-- all five phases fin makes allFin true
allFin-true : ∀ {f} → f cs ≡ fin → f bf ≡ fin → f tx ≡ fin → f lf ≡ fin → f ln ≡ fin → allFin (mkSt awaiting f) ≡ true
allFin-true a b c d e rewrite a | b | c | d | e = refl

-- with allFin the warm move succeeds
warm-ok : ∀ {m} f → allFin (mkSt awaiting f) ≡ true → sstep (GAct , gov) warm m (mkSt awaiting f) ≡ just (mkSt warmD f)
warm-ok f e rewrite e = refl

-- the enabled move type at an awaiting state (non-tmo: its successor is awaiting or Warm)
Move : Bool → (Proto → PSt) → Set₁
Move c f = Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] Σ[ s′ ∈ St ] (sstep at a (Post true true c) (mkSt awaiting f) ≡ just s′ × Next s′)

-- progress, forward declarations (cs first, then bf, tx, lf, ln, then warm): cs's move, else on to bf
prog   : ∀ {c} f → (∀ p → Good p (f p)) → Move c f
-- progress once cs is fin: bf's move, else on to tx
progBF : ∀ {c} f → (∀ p → Good p (f p)) → f cs ≡ fin → Move c f
-- progress once cs, bf are fin: tx's move, else on to lf
progTX : ∀ {c} f → (∀ p → Good p (f p)) → f cs ≡ fin → f bf ≡ fin → Move c f
-- progress once cs, bf, tx are fin: lf's move, else on to ln
progLF : ∀ {c} f → (∀ p → Good p (f p)) → f cs ≡ fin → f bf ≡ fin → f tx ≡ fin → Move c f
-- progress once cs, bf, tx, lf are fin: ln's move, else warm
progLN : ∀ {c} f → (∀ p → Good p (f p)) → f cs ≡ fin → f bf ≡ fin → f tx ≡ fin → f lf ≡ fin → Move c f

prog f i with f cs in e | i cs
... | waitEnv  | _ = (EnvAct , env) , block , _ , stepIf-ok _ e , inj₁ refl
... | ready    | _ = (Proto , rtn) , cs , _ , stepIf-ok _ e , inj₁ refl
... | fin      | _ = progBF f i e
... | running  | ()
... | needInt  | ()
... | quitSent | ()

progBF f i ecs with f bf in e | i bf
... | needInt  | _ = (IntAct , int) , bfDrain , _ , stepIf-ok _ e , inj₁ refl
... | ready    | _ = (Proto , rtn) , bf , _ , stepIf-ok _ e , inj₁ refl
... | fin      | _ = progTX f i ecs e
... | running  | ()
... | waitEnv  | ()
... | quitSent | ()

progTX f i ecs ebf with f tx in e | i tx
... | waitEnv  | _ = (EnvAct , env) , txReq , _ , stepIf-ok _ e , inj₁ refl
... | ready    | _ = (Proto , rtn) , tx , _ , stepIf-ok _ e , inj₁ refl
... | fin      | _ = progLF f i ecs ebf e
... | running  | ()
... | needInt  | ()
... | quitSent | ()

progLF f i ecs ebf etx with f lf in e | i lf
... | ready    | _ = (Proto , rtn) , lf , _ , stepIf-ok _ e , inj₁ refl
... | fin      | _ = progLN f i ecs ebf etx e
... | running  | ()
... | waitEnv  | ()
... | needInt  | ()
... | quitSent | ()

progLN {c} f i ecs ebf etx elf with f ln in e | i ln
... | needInt  | _ = (IntAct , int) , lnQuit , _ , stepIf-ok _ e , inj₁ refl
... | quitSent | _ = (IntAct , int) , lnQuitDone , _ , stepIf-ok _ e , inj₁ refl
... | ready    | _ = (Proto , rtn) , ln , _ , stepIf-ok _ e , inj₁ refl
... | fin      | _ = (GAct , gov) , warm , _ , warm-ok {Post true true c} f (allFin-true {f} ecs ebf etx elf e) , inj₂ refl
... | running  | ()
... | waitEnv  | ()

-- ===================== rank: every move lowers it =====================

-- post-PR LeiosNotify potential: lnQuit, lnQuitDone, rtn
potL : PSt → ℕ
potL needInt  = 3
potL quitSent = 2
potL ready    = 1
potL _        = 0

-- potential of a phase map (cs bf tx lf as in PrePR, ln post-PR)
rkP : (Proto → PSt) → ℕ
rkP f = rk5 (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) (potL (f ln))

-- governor moves still due while awaiting: warm (1), or with the timer also tmo, cold (2)
tw : Bool → ℕ
tw true  = 2
tw false = 1

-- the rank; for c = false: hot = 12 = demote + [bfDrain, block, txReq, lnQuit, lnQuitDone, 5 rtn] + warm
rank : Bool → St → ℕ
rank c (mkSt hot _)      = suc (tw c + 10)
rank c (mkSt awaiting f) = tw c + rkP f
rank c (mkSt timedOut _) = 1
rank c (mkSt warmD _)    = 0
rank c (mkSt coldD _)    = 0

-- a matched quitSent phase is quitSent
eqP-quit : ∀ x → eqP x quitSent ≡ true → x ≡ quitSent
eqP-quit quitSent _ = refl
eqP-quit running ()
eqP-quit waitEnv ()
eqP-quit needInt ()
eqP-quit ready ()
eqP-quit fin ()

-- the awaiting rank is positive
tw-pos : ∀ c n → suc zero ≤ tw c + n
tw-pos true  n = s≤s z≤n
tw-pos false n = s≤s z≤n

-- every post-PR sstep move strictly decreases the rank
step-rank : ∀ {b t c} s {s′} at a → sstep at a (Post b t c) s ≡ just s′ → suc (rank c s′) ≤ rank c s
step-rank (mkSt hot f)      (_ , gov) demote refl = ≤-refl
step-rank (mkSt hot f)      (_ , gov) warm   ()
step-rank (mkSt hot f)      (_ , gov) tmo    ()
step-rank (mkSt hot f)      (_ , gov) cold   ()
step-rank (mkSt hot f)      (_ , rtn) p      ()
step-rank (mkSt hot f)      (_ , env) e      ()
step-rank (mkSt hot f)      (_ , int) a      ()
step-rank (mkSt awaiting f) (_ , gov) demote ()
step-rank {c = c} (mkSt awaiting f) (_ , gov) warm h with allFin (mkSt awaiting f) | h
... | true  | refl = tw-pos c (rkP f)
... | false | ()
step-rank {c = true}  (mkSt awaiting f) (_ , gov) tmo refl = s≤s (s≤s z≤n)
step-rank {c = false} (mkSt awaiting f) (_ , gov) tmo ()
step-rank (mkSt awaiting f) (_ , gov) cold   ()
step-rank {c = c} (mkSt awaiting f) (_ , rtn) cs h with stepIf-inv h
... | q , refl rewrite eqP-ready (f cs) q = lift1 (tw c) (dropA 1 0 (pot (f bf)) (pot (f tx)) (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , rtn) bf h with stepIf-inv h
... | q , refl rewrite eqP-ready (f bf) q = lift1 (tw c) (dropB (pot (f cs)) 1 0 (pot (f tx)) (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , rtn) tx h with stepIf-inv h
... | q , refl rewrite eqP-ready (f tx) q = lift1 (tw c) (dropC (pot (f cs)) (pot (f bf)) 1 0 (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , rtn) lf h with stepIf-inv h
... | q , refl rewrite eqP-ready (f lf) q = lift1 (tw c) (dropD (pot (f cs)) (pot (f bf)) (pot (f tx)) 1 0 (potL (f ln)) ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , rtn) ln h with stepIf-inv h
... | q , refl rewrite eqP-ready (f ln) q = lift1 (tw c) (dropE (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) 1 0 ≤-refl)
step-rank {b} {c = c} (mkSt awaiting f) (_ , env) block h with stepIf-inv (if-just b h)
... | q , refl rewrite eqP-wait (f cs) q = lift1 (tw c) (dropA 2 1 (pot (f bf)) (pot (f tx)) (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank {t = t} {c = c} (mkSt awaiting f) (_ , env) txReq h with stepIf-inv (if-just t h)
... | q , refl rewrite eqP-wait (f tx) q = lift1 (tw c) (dropC (pot (f cs)) (pot (f bf)) 2 1 (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank (mkSt awaiting f) (_ , env) lnReply ()
step-rank {c = c} (mkSt awaiting f) (_ , int) bfDrain h with stepIf-inv h
... | q , refl rewrite eqP-need (f bf) q = lift1 (tw c) (dropB (pot (f cs)) 2 1 (pot (f tx)) (pot (f lf)) (potL (f ln)) ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , int) lnQuit h with stepIf-inv h
... | q , refl rewrite eqP-need (f ln) q = lift1 (tw c) (dropE (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) 3 2 ≤-refl)
step-rank {c = c} (mkSt awaiting f) (_ , int) lnQuitDone h with stepIf-inv h
... | q , refl rewrite eqP-quit (f ln) q = lift1 (tw c) (dropE (pot (f cs)) (pot (f bf)) (pot (f tx)) (pot (f lf)) 2 1 ≤-refl)
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
steps-len : ∀ {b t c s w s′} → Steps (Post b t c) s w s′ → length w + rank c s′ ≤ rank c s
steps-len done = ≤-refl
steps-len {s = s} (more {at = at} {a = a} eq ss) = ≤-trans (s≤s (steps-len ss)) (step-rank s at a eq)

-- ===================== D2a: Warm stays reachable =====================

-- the Warm-reaching run from an awaiting state
ToWarm : Bool → St → Set₁
ToWarm c s = Σ[ w ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s′ ∈ St ] (Steps (Post true true c) s w s′ × gph s′ ≡ warmD)

-- drive an awaiting state to Warm by progress moves (fuel n bounds the rank; forward declarations)
drive : ∀ {c} n f → rank c (mkSt awaiting f) ≤ n → (∀ p → Good p (f p)) → ToWarm c (mkSt awaiting f)
-- continue after one progress move: stop at Warm, else drive on with less fuel
cont  : ∀ {c} n {f} at a s′ → sstep at a (Post true true c) (mkSt awaiting f) ≡ just s′
      → suc (rank c s′) ≤ n → Next s′ → Inv s′ → ToWarm c (mkSt awaiting f)

drive n f le i with prog f i
... | at , a , s′ , eq , nx =
  cont n at a s′ eq (≤-trans (step-rank (mkSt awaiting f) at a eq) le) nx (step-inv (mkSt awaiting f) at a i eq)

cont n       at a s′ eq lt (inj₂ g) _ = (at , a) ∷ [] , s′ , more eq done , g
cont (suc n) at a (mkSt g f′) eq (s≤s lt) (inj₁ refl) i′ with drive n f′ lt i′
... | w , s″ , ss , g′ = (at , a) ∷ w , s″ , more eq ss , g′
cont zero    at a s′ eq () (inj₁ _) _

-- D2a: from every reachable awaiting state (so before tmo) a run to Warm exists; by construction
-- (prog) it uses only block, txReq, bfDrain, lnQuit, lnQuitDone, rtn and finally warm
post-warmReachable : ∀ {c w s} → Steps (Post true true c) st₀ w s → gph s ≡ awaiting
                   → Σ[ w′ ∈ List (Σ (AnyTypes Ev) proj₁) ] Σ[ s′ ∈ St ] (Steps (Post true true c) s w′ s′ × gph s′ ≡ warmD)
post-warmReachable {c} {s = mkSt _ f} ss refl = drive (rank c (mkSt awaiting f)) f ≤-refl (steps-inv ss tt)

-- ===================== bounded progress without the timeout =====================

-- no reachable SysAt state of P is stuck
not-stuck : ∀ s → Inv s → IsStuck (SysAt P s) → ⊥
not-stuck (mkSt hot f)      _ st = st (Sys-ev-intro (GAct , gov) demote refl refl)
not-stuck (mkSt awaiting f) i st with prog {false} f i
... | at , a , _ , eq , _ = st (Sys-ev-intro at a eq refl)
not-stuck (mkSt timedOut f) _ st = st (Sys-ev-intro (GAct , gov) cold refl refl)
not-stuck (mkSt warmD f)    _ st = st (sRet refl)
not-stuck (mkSt coldD f)    _ st = st (sRet refl)

-- the timeout-free post-PR system is deadlock free (√ is not a deadlock)
post-deadlockFree : DeadlockFree (Sys P)
post-deadlockFree r st with ∖√-reach r
... | w , s′ , ss , refl = not-stuck s′ (steps-inv ss tt) st

-- the system has no τ, so no reachable state diverges
post-divergenceFree : DivergenceFree (Sys P)
post-divergenceFree r d with ∖√-reach r
... | w , s′ , ss , refl = Sys-no-τ (Diverges.step d)

-- every Steps run of P from st₀ has at most 12 moves
steps-12 : ∀ {w s} → Steps P st₀ w s → length w ≤ 12
steps-12 ss = ≤-trans (m≤m+n _ _) (steps-len ss)

-- every trace has length ≤ 13: at most 12 moves (rank of st₀) plus one final √
post-traceBound : ∀ {tr W} → Sys P ⟹⟨ tr ⟩ W → length tr ≤ 13
post-traceBound x with Sys-anyTrace x
... | w , s′ , ss , inj₁ (refl , _) = ≤-trans (≤-reflexive (lab-length w)) (≤-trans (steps-12 ss) (n≤1+n 12))
... | w , s′ , ss , inj₂ (r , refl , _) =
  ≤-trans (≤-reflexive (length-++ (lab w)))
          (+-monoˡ-≤ 1 (≤-trans (≤-reflexive (lab-length w)) (steps-12 ss)))

-- bounded progress with the timeout removed: deadlock and divergence free, every trace ≤ 13 letters
-- (12 moves: demote, bfDrain, block, txReq, lnQuit, lnQuitDone, 5 rtn, warm; plus √)
post-bounded : DeadlockFree (Sys P) × DivergenceFree (Sys P) × (∀ {tr W} → Sys P ⟹⟨ tr ⟩ W → length tr ≤ 13)
post-bounded = post-deadlockFree , post-divergenceFree , post-traceBound

-- ===================== the bound is attained (Review Focus 5) =====================

-- the 12-move run to Warm
wT : List (Σ (AnyTypes Ev) proj₁)
wT = ((GAct , gov) , demote) ∷ ((IntAct , int) , bfDrain) ∷ ((EnvAct , env) , block) ∷ ((EnvAct , env) , txReq)
   ∷ ((IntAct , int) , lnQuit) ∷ ((IntAct , int) , lnQuitDone)
   ∷ ((Proto , rtn) , cs) ∷ ((Proto , rtn) , bf) ∷ ((Proto , rtn) , tx) ∷ ((Proto , rtn) , lf) ∷ ((Proto , rtn) , ln)
   ∷ ((GAct , gov) , warm) ∷ []

-- wT is a Steps run of P ending Warm
wT-steps : Σ[ s ∈ St ] (Steps P st₀ wT s × gph s ≡ warmD)
wT-steps = _ , more refl (more refl (more refl (more refl (more refl (more refl (more refl (more refl
             (more refl (more refl (more refl (more refl done))))))))))) , refl

-- extend a run by one last step
⟹-snoc : ∀ {p q q′ : Proc} {t e} → p ⟹⟨ t ⟩ q → q ─[ ev e ]─► q′ → p ⟹⟨ t ++ e ∷ [] ⟩ q′
⟹-snoc ⟹-refl     st = ⟹-ev st ⟹-refl
⟹-snoc (⟹-τ x r)  st = ⟹-τ x (⟹-snoc r st)
⟹-snoc (⟹-ev x r) st = ⟹-ev x (⟹-snoc r st)

-- the bound 13 is attained: the 12 letters of wT, ending warm, then √
post-tight : Σ[ tr ∈ List (Event√ U) ] Σ[ W ∈ Proc ] (Sys P ⟹⟨ tr ⟩ W × tr ≡ lab wT ++ √ _ ∷ [] × length tr ≡ 13)
post-tight with wT-steps
... | mkSt _ f , ss , refl = _ , _ , ⟹-snoc (Steps⇒traces ss) (sRet refl) , refl , refl

-- ===================== D2b: every maximal run reaches warm =====================
-- Runs are the library's maximal `Trace`s (finite √/stuck/div leaves or infinite), as in
-- LeiosNotifyQuitLive.  No fairness hypothesis is needed: the design's weak fairness for block
-- and txReq is vacuous here, since with blocks = txReqs = true the environment offers them in
-- every state where ChainSync / TxSubmission2 waits (same finding as quit-live-sys), and the
-- timer is off, so every move lowers the rank and the run cannot avoid warm.

-- the frame is a step on the warm event
WarmFired : FramePred (lsuc lzero) U
WarmFired (step _ e) = e ≡ GV warm
WarmFired (done _ _) = Lift (lsuc lzero) ⊥
WarmFired (stuck _)  = Lift (lsuc lzero) ⊥
WarmFired (div _)    = Lift (lsuc lzero) ⊥

-- warm has not happened yet: hot or awaiting
Pend : St → Set
Pend (mkSt hot _)      = ⊤
Pend (mkSt awaiting _) = ⊤
Pend _                 = ⊥

-- a pending state is not final
pend-nf : ∀ s → Pend s → final s ≡ false
pend-nf (mkSt hot _)      _ = refl
pend-nf (mkSt awaiting _) _ = refl
pend-nf (mkSt warmD _)    ()
pend-nf (mkSt timedOut _) ()
pend-nf (mkSt coldD _)    ()

-- a move of P from a pending state is warm or stays pending
move-cls : ∀ s {s′} at a → Pend s → sstep at a P s ≡ just s′ → lbl at a ≡ GV warm ⊎ Pend s′
move-cls (mkSt hot f)      (_ , gov) demote _ refl = inj₂ tt
move-cls (mkSt hot f)      (_ , gov) warm   _ ()
move-cls (mkSt hot f)      (_ , gov) tmo    _ ()
move-cls (mkSt hot f)      (_ , gov) cold   _ ()
move-cls (mkSt hot f)      (_ , rtn) p      _ ()
move-cls (mkSt hot f)      (_ , env) e      _ ()
move-cls (mkSt hot f)      (_ , int) a      _ ()
move-cls (mkSt awaiting f) (_ , gov) demote _ ()
move-cls (mkSt awaiting f) (_ , gov) warm   _ _ = inj₁ refl
move-cls (mkSt awaiting f) (_ , gov) tmo    _ ()
move-cls (mkSt awaiting f) (_ , gov) cold   _ ()
move-cls (mkSt awaiting f) (_ , rtn) p      _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt awaiting f) (_ , env) block  _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt awaiting f) (_ , env) txReq  _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt awaiting f) (_ , env) lnReply _ ()
move-cls (mkSt awaiting f) (_ , int) bfDrain _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt awaiting f) (_ , int) lnQuit _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt awaiting f) (_ , int) lnQuitDone _ h with stepIf-inv h
... | _ , refl = inj₂ tt
move-cls (mkSt warmD f)    at a () _
move-cls (mkSt timedOut f) at a () _
move-cls (mkSt coldD f)    at a () _

-- a weak visible step of the system is a single strong step (no τ anywhere)
weak1 : ∀ {m s e t′} → SysAt m s ═[ ev e ]═► t′ → SysAt m s ─[ ev e ]─► t′
weak1 (wev (τ*-step x _) _ _) = ⊥-elim (Sys-no-τ x)
weak1 (wev τ*-refl st τ*-refl) = st
weak1 {e = √ r} (wev τ*-refl (sRet _) (τ*-step x _)) = ⊥-elim (deadlock-no-τ x)
weak1 {e = evl (evLabel X ch a)} (wev τ*-refl st (τ*-step x _)) with Sys-ev-inv st
... | _ , _ , refl = ⊥-elim (Sys-no-τ x)

-- a non-final state does not return
noRet : ∀ {s r} → final s ≡ false → force (SysAt P s) ≡ ret r → ⊥
noRet {s} fe eq with force-false {P} {s} fe
... | v , feq with trans (sym eq) feq
... | ()

-- true is not false
t≢f : true ≡ false → ⊥
t≢f ()

-- the descent along a run (fuel n bounds the rank; forward declarations)
desc     : ∀ n {s} (tr : Trace U (SysAt P s)) → rank false s < n → Pend s → Inv s → ◇ᵗ (atom WarmFired) tr
-- one visible step of the run: warm fires now, or the descent continues on the tail
stepCase : ∀ n {s e t′} (w : SysAt P s ═[ ev e ]═► t′) (tr′ : ∞Trace U t′) → SysAt P s ─[ ev e ]─► t′
         → rank false s ≤ n → Pend s → Inv s → ◇ᵗ (atom WarmFired) (step w tr′)

desc zero          _           ()       _  _
desc (suc n)       (step w tr′) (s≤s lt) pd i = stepCase n w tr′ (weak1 w) lt pd i
desc (suc n) {s}   (done eq)    _        pd _ = ⊥-elim (noRet (pend-nf s pd) eq)
desc (suc n) {s}   (stuck stk)  _        _  i = ⊥-elim (not-stuck s i stk)
desc (suc n)       (div d)      _        _  _ = ⊥-elim (Sys-no-τ (Diverges.step d))

stepCase n {s} {e = √ r} w tr′ st lt pd i = ⊥-elim (t≢f (trans (sym (Sys-√ st)) (pend-nf s pd)))
stepCase n {s} {e = evl (evLabel X ch a)} w tr′ st lt pd i with Sys-ev-inv st
... | s′ , eq , refl with move-cls s (X , ch) a pd eq
...   | inj₁ isW = ◇ᵗ-now isW
...   | inj₂ pd′ = ◇ᵗ-later (desc n (∞Trace.force tr′) (≤-trans (step-rank s (X , ch) a eq) lt) pd′
                                  (step-inv s (X , ch) a i eq))

-- D2b (LTL): every maximal run of the timeout-free post-PR system reaches warm
post-warmLTL : (tr : Trace U (Sys P)) → ◇ᵗ (atom WarmFired) tr
post-warmLTL tr = desc 13 tr ≤-refl tt tt
