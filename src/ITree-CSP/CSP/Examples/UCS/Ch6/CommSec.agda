{-# OPTIONS --guardedness #-}

-- UCS chapter 6: commsec (commsec.csp, Bill Roscoe) — information-flow security
-- via noninterference: a system is SECURE iff LAbs(H)(System) is DETERMINISTIC
-- (abstracting the High actions leaves a deterministic Low view).  data = Bool;
-- the Low channel lois→leah is observed (sendL/recL), High (hugh→henry) abstracted.
--   System1 (naive shared Medium)  : INSECURE — hidden High occupies the shared
--     medium, so Low's sendL is nondeterministically available/blocked.
--   System2 (Medium2 prioritises Low): SECURE — Low view unaffected by High.
-- The abstracted Low views are modelled DIRECTLY (the observable behaviour of
-- LAbs(H)(System1/System2)); the literal (∥ … ∖{in,out}) [|H|] CHAOS(H) ∖H
-- composites, Systems 3/4, the BN buffer refinements, and the [FD] variants are
-- documented NON-GOALS.

module CSP.Examples.UCS.Ch6.CommSec where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

data LEv : Set → Set where
  sendL recL : LEv Bool       -- the Low channel (lois→leah); High abstracted away

LEv-≟ : (x y : AnyTypes LEv) → Dec (x ≡ y)
LEv-≟ (_ , sendL) (_ , sendL) = yes refl
LEv-≟ (_ , recL)  (_ , recL)  = yes refl
LEv-≟ (_ , sendL) (_ , recL)  = no (λ ())
LEv-≟ (_ , recL)  (_ , sendL) = no (λ ())

open import CSP.Operators LEv-≟
open EventSet
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()

LProc : Set₁
LProc = PTree LEv (ExtI LEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- LowView2 — System2's SECURE (deterministic) Low view: a plain Low 1-place buffer,
-- unaffected by High.  τ-free.
------------------------------------------------------------------------------------

LowView2  : LProc
LowView2o : Bool → LProc

force LowView2 = react
  (λ where (_ , sendL) x → just (LowView2o x)
           (_ , recL) _ → nothing)
  ∅t
force (LowView2o x) = react
  (λ where (_ , recL) y → case y B≟ x of λ where (yes _) → just LowView2 ; (no _) → nothing
           (_ , sendL) _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- LowView1 — System1's INSECURE (nondeterministic) Low view: a root internal choice
-- between accepting sendL (medium free) and being blocked, Stop (medium busy with
-- hidden High).  The ⊓ is inlined react ∅v with fin-branches
-- fzero → LowView1acc, fsuc fzero → Stop.
------------------------------------------------------------------------------------

LowView1    : LProc
LowView1acc : LProc          -- sendL?x → LowView1o x  (medium free)
LowView1o   : Bool → LProc   -- recL!x → LowView1

force LowView1 = react ∅v    -- (sendL?x → …) ⊓ Stop   (hidden-High internal choice)
  (λ where (_ , fin) (lift fzero)              → just LowView1acc
           (_ , fin) (lift (fsuc fzero))       → just Stop
           (_ , fin) (lift (fsuc (fsuc _)))    → nothing
           (_ , base _) _                      → nothing
           (_ , pair _ _) _                    → nothing)
force LowView1acc = react
  (λ where (_ , sendL) x → just (LowView1o x)
           (_ , recL) _ → nothing)
  ∅t
force (LowView1o x) = react
  (λ where (_ , recL) y → case y B≟ x of λ where (yes _) → just LowView1 ; (no _) → nothing
           (_ , sendL) _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §B-proof.  commsec-insecure : ¬ Deterministic LowView1  (System1 LEAKS).  The
-- hidden-High internal choice ⊓ sits at the ROOT: after the empty Low trace LowView1
-- silently commits either to LowView1acc (offers sendL) or to Stop (offers nothing).
-- So:
--   • ⟨sendL true⟩ IS a trace  (commit to LowView1acc, then sendL true);  AND
--   • after ⟨⟩ the stable state Stop REFUSES sendL true.
-- A trace s ∷ʳ a coexisting with a stable state reached by s that refuses a
-- contradicts Deterministic.  Here s = [], a = sendL true.  Trace + failures level
-- only — NO FailuresDivergences, NO postulate.  This is the SAME two-witness shape as
-- Ch5 Renaming §B `split'-nondet`, but simpler: the ⊓ is at the root, so s = [].
------------------------------------------------------------------------------------

open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)

import Semantics.LTS         {E = LEv} {I = ExtI LEv} as LL
import Semantics.Failures    {E = LEv} {I = ExtI LEv} as FL
import Semantics.Refusals    {E = LEv} {I = ExtI LEv} as RL
import Semantics.Determinism {E = LEv} {I = ExtI LEv} as DL

-- the Low event whose acceptance-vs-refusal after ⟨⟩ exposes the leak
sendL-ev : Bool → LL.Event√ (⊤poly {lzero})
sendL-ev b = LL.evl (LL.evLabel Bool sendL b)

-- the ⊓'s two τ-branches: accept (→ LowView1acc) and block (→ Stop)
lv1-accept : LowView1 LL.─[ LL.τ ]─► LowView1acc
lv1-accept = LL.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

lv1-block : LowView1 LL.─[ LL.τ ]─► Stop
lv1-block = LL.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- LowView1acc offers sendL (medium free)
acc-sendL : LowView1acc LL.─[ LL.ev (sendL-ev true) ]─► LowView1o true
acc-sendL = LL.sVis {at = Bool , sendL} {a = true} refl refl

-- witness 1: ⟨sendL true⟩ is a trace of LowView1 (accept branch, then sendL true)
tr : FL.traces LowView1 (sendL-ev true ∷ [])
tr = LowView1o true , FL.⟹-τ lv1-accept (FL.⟹-ev acc-sendL FL.⟹-refl)

-- Stop offers nothing, so it does not offer sendL true (its offer map is ∅v)
stop-no-offer : ¬ RL.Offers Stop (sendL-ev true)
stop-no-offer (_ , LL.sVis refl br) = case br of λ ()

-- witness 2: after ⟨⟩, the stable state Stop refuses sendL true (block branch)
fl : FL.failures LowView1 [] (λ e → e ≡ sendL-ev true)
fl = Stop
   , FL.⟹-τ lv1-block FL.⟹-refl
   , (λ i a → refl)                        -- Stop is stable (τc = ∅t)
   , (λ { e refl → stop-no-offer })         -- and refuses sendL true

-- the two witnesses contradict Deterministic:  ⟨sendL true⟩ ∈ traces, yet Stop
-- (reached by the empty trace) stably refuses sendL true.  System1 leaks.
commsec-insecure : ¬ DL.Deterministic LowView1
commsec-insecure det = det {s = []} {a = sendL-ev true} tr fl

------------------------------------------------------------------------------------
-- §C.  commsec-secure : Deterministic LowView2  (System2 is SECURE).
--
-- LowView2 / LowView2o x are τ-FREE (`react … ∅t`) with FUNCTIONAL visible offers
-- (sendL?x → LowView2o x ; LowView2o x's single pinned recL!x → LowView2).  Hence the
-- state reached by a visible run over `s` is UNIQUE (reached-state determinacy).  If
-- `s ∷ʳ a ∈ traces LowView2`, the state reached by `s` OFFERS `a`, so a stable state
-- reached by `s` cannot REFUSE `a` — no failure `(s, {a})`.  Trace + failures level
-- only, NO FailuresDivergences, NO postulate.  DIRECT PORT of Ch5 Renaming §B-det
-- (`split-det : Deterministic SPLIT`); LowView2 is simpler (single pinned output, no
-- parity split).
------------------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

-- reachable states of LowView2: LowView2 itself, and LowView2o x for x : Bool.
data Reach : LProc → Set₁ where
  r-lv2  :             Reach LowView2
  r-lv2o : (x : Bool) → Reach (LowView2o x)

-- no τ from any reachable state (LowView2 / LowView2o x are `react … ∅t`)
reach-noτ : ∀ {Q t} → Reach Q → Q LL.─[ LL.τ ]─► t → ⊥
reach-noτ r-lv2      (LL.sSil ())
reach-noτ r-lv2      (LL.sTau refl br) = case br of λ ()
reach-noτ (r-lv2o x) (LL.sSil ())
reach-noτ (r-lv2o x) (LL.sTau refl br) = case br of λ ()

-- no √ (termination) from any reachable state (their `force` is a `react`, never `ret`)
reach-no√ : ∀ {Q r t} → Reach Q → Q LL.─[ LL.ev (LL.√ r) ]─► t → ⊥
reach-no√ r-lv2      (LL.sRet ())
reach-no√ (r-lv2o x) (LL.sRet ())

-- the target of any visible step from a reachable state is again reachable
reach-step : ∀ {Q e q} → Reach Q → Q LL.─[ LL.ev e ]─► q → Reach q
reach-step r-lv2 (LL.sRet ())
reach-step r-lv2 (LL.sVis {at = _ , sendL} {a = x} refl br) = subst Reach (just-injective br) (r-lv2o x)
reach-step r-lv2 (LL.sVis {at = _ , recL}  refl br)         = case br of λ ()
reach-step (r-lv2o x) (LL.sRet ())
reach-step (r-lv2o x) (LL.sVis {at = _ , recL} {a = y} refl br) with y B≟ x
... | yes _ = subst Reach (just-injective br) r-lv2
... | no  _ = case br of λ ()
reach-step (r-lv2o x) (LL.sVis {at = _ , sendL} refl br)    = case br of λ ()

-- FUNCTIONAL offer: same source, same visible event ⇒ same target (react injectivity).
offer-fun : ∀ {A e a} {q1 q2 Q : LProc}
          → Q LL.─[ LL.ev (LL.evl (LL.evLabel A e a)) ]─► q1
          → Q LL.─[ LL.ev (LL.evl (LL.evLabel A e a)) ]─► q2
          → q1 ≡ q2
offer-fun s1 s2 with LL.ev-inv s1 | LL.ev-inv s2
... | v , τc , eq1 , br1 | v' , τc' , eq2 , br2 with trans (sym eq1) eq2
...   | refl = just-injective (trans (sym br1) br2)

-- a single visible step from a reachable state is deterministic (√ ruled out; evl functional)
step-det : ∀ {e} {q1 q2 Q : LProc} → Reach Q
         → Q LL.─[ LL.ev e ]─► q1 → Q LL.─[ LL.ev e ]─► q2 → q1 ≡ q2
step-det {e = LL.evl x} r  s1 s2 = offer-fun s1 s2
step-det {e = LL.√ r′}  r  s1 s2 = ⊥-elim (reach-no√ r s1)

-- REACHED-STATE DETERMINACY (the crux): the state reached by a visible run over `s` is
-- unique.  Every ⟹ from a reachable state is τ-free, and each visible step is functional.
det : ∀ {Q s P′ P″} → Reach Q → Q FL.⟹⟨ s ⟩ P′ → Q FL.⟹⟨ s ⟩ P″ → P′ ≡ P″
det r FL.⟹-refl            FL.⟹-refl            = refl
det r FL.⟹-refl            (FL.⟹-τ step _)      = ⊥-elim (reach-noτ r step)
det r (FL.⟹-τ step _)      _                     = ⊥-elim (reach-noτ r step)
det r (FL.⟹-ev step1 _)    (FL.⟹-τ step _)      = ⊥-elim (reach-noτ r step)
det r (FL.⟹-ev step1 rest1) (FL.⟹-ev step2 rest2) =
  det (reach-step r step1) rest1
      (subst (λ z → z FL.⟹⟨ _ ⟩ _) (sym (step-det r step1 step2)) rest2)

-- snoc-decomposition: a run over `s ∷ʳ a` factors as a run over `s` reaching a state
-- that OFFERS `a` (τ-free, so no leading τ before the final `a`).
snoc-split : ∀ {a : LL.Event√ (⊤poly {lzero})} {Q P₀ : LProc} {s}
           → Reach Q → Q FL.⟹⟨ s ∷ʳ a ⟩ P₀
           → Σ[ P″ ∈ LProc ] (Q FL.⟹⟨ s ⟩ P″ × RL.Offers P″ a)
snoc-split {s = []}     r (FL.⟹-τ step _)    = ⊥-elim (reach-noτ r step)
snoc-split {s = []}     r (FL.⟹-ev step _)    = _ , FL.⟹-refl , (_ , step)
snoc-split {s = x ∷ s′} r (FL.⟹-τ step _)    = ⊥-elim (reach-noτ r step)
snoc-split {s = x ∷ s′} r (FL.⟹-ev step rest) with snoc-split (reach-step r step) rest
... | P″ , run , off = P″ , FL.⟹-ev step run , off

-- LowView2 is deterministic: no trace `s ∷ʳ a` coexists with a stable state reached by
-- `s` that refuses `a` — the reached-by-`s` state uniquely offers `a`.  System2 is SECURE.
commsec-secure : DL.Deterministic LowView2
commsec-secure {s} {a} (P₀ , run) (P′ , runP′ , _ , refP′) with snoc-split {s = s} r-lv2 run
... | P″ , runP″ , offP″ =
      refP′ a refl (subst (λ z → RL.Offers z a) (sym (det r-lv2 runP′ runP″)) offP″)
