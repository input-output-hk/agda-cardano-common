{-# OPTIONS --guardedness #-}

-- UCS chapter 6: failures and divergences (faildiv.csp, Bill Roscoe; source
-- fdr-examples/ucs/chapter06/faildiv.csp), section 6.1 — the Q-family half.
--
--   Q1  = a -> STOP [] b -> STOP
--   Q2  = a -> STOP |~| b -> STOP
--   Q3  = STOP |~| Q1
--   DIV = let AS = a -> AS within AS \ {a}      -- a hidden event looping forever
--   Q4  = a -> STOP |~| b -> DIV
--
-- §A models the five processes, §B proves the six assertions FDR makes about them.
-- The payload is the LAST pair of assertions: failures refinement and
-- failures/divergences refinement point in OPPOSITE directions between Q2 and Q4,
-- because the FD model treats divergence as catastrophic.
--
--   Q2 [F=  Q4   TRUE   Q4 has FEWER refusals than Q2: after the trace <b> it sits
--                       inside DIV, which is never stable, so it refuses nothing.
--   Q4 [F=  Q2   FALSE  Q2 can refuse everything after <b>; Q4 cannot refuse anything.
--   Q4 [FD= Q2   TRUE   the FD model sees that same divergence and makes Q4 the
--                       bottom process after <b>, which does everything Q2 does.
--   Q2 [FD= Q4   FALSE  Q4 diverges after <b>, and Q2 never diverges at all.
--
-- Deferred (non-goals): the P1-P4 determinism half of faildiv.csp (channels c and d
-- and the [deterministic] assertions) — the determinism-vs-nondeterminism contrast is
-- already carried by CSP.Examples.UCS.Ch5.Renaming.  Only channels a and b are
-- declared here, since only those two are used by the Q-family.

module CSP.Examples.UCS.Ch6.FailDiv where

open import Level using (Lift; lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree

-- DecEq on the polymorphic unit return type, the instance `_□_` (√-aware) asks for
instance
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })

import CSP.Operators

------------------------------------------------------------------------------------
-- §A. The model.
------------------------------------------------------------------------------------

-- the two visible channels of the Q-family; both carry ⊤ (a ⊥-carried event never fires)
data QEv : Set → Set where
  a b : QEv ⊤

-- decidable equality on the event indices, as every CSP operator module needs
QEv-≟ : (x y : AnyTypes QEv) → Dec (x ≡ y)
QEv-≟ (_ , a) (_ , a) = yes refl
QEv-≟ (_ , b) (_ , b) = yes refl
QEv-≟ (_ , a) (_ , b) = no (λ ())
QEv-≟ (_ , b) (_ , a) = no (λ ())

module OpsQ = CSP.Operators QEv-≟
open OpsQ
open EventSet

-- the process type of this example: no data is returned, so R = ⊤
QProc : Set₁
QProc = PTree QEv (ExtI QEv) (⊤poly {lzero})

-- STOP at this example's process type (pins the return type R, which `Stop` leaves open)
STOP : QProc
STOP = Stop

-- a -> STOP
Pa : QProc
Pa = a ⟶₀ STOP

-- b -> STOP
Pb : QProc
Pb = b ⟶₀ STOP

-- Q1 = a -> STOP [] b -> STOP, the genuine external choice of the two prefixes.  Both
-- operands are stable pure-visible `react` nodes, so `force Q1` reduces to the merged
-- menu {a,b} paired with the `□-mt` τ-branch map; that map is only POINTWISE `nothing`,
-- so stability is obtained from `stable-□-join` instead of by matching on it.
Q1 : QProc
Q1 = Pa □ Pb

-- Q2 = a -> STOP |~| b -> STOP
Q2 : QProc
Q2 = Pa ⊓ Pb

-- Q3 = STOP |~| Q1
Q3 : QProc
Q3 = STOP ⊓ Q1

-- membership predicate of the hidden channel set {a}
isA : AnyTypes QEv → Set
isA (_ , a) = ⊤
isA (_ , b) = ⊥

-- …and its decision procedure
isA? : (at : AnyTypes QEv) → Dec (isA at)
isA? (_ , a) = yes tt
isA? (_ , b) = no (λ z → z)

-- the hidden channel set {a}
aSet : EventSet
aSet = chanSet isA isA?

-- AS = a -> AS, the visible a-loop (written as a raw react node so the corecursive
-- call sits syntactically under a constructor)
AS : QProc
force AS = react (λ where (_ , a) _ → just AS
                          (_ , b) _ → nothing)
                 ∅t

-- DIV = AS \ {a}: hiding the only event AS can do turns the loop into a τ-loop
DIV : QProc
DIV = AS ∖ aSet

-- b -> DIV
PbDiv : QProc
PbDiv = b ⟶₀ DIV

-- Q4 = a -> STOP |~| b -> DIV
Q4 : QProc
Q4 = Pa ⊓ PbDiv

-- Q3 |~| DIV, the left-hand side of the two divergence-strictness assertions
Q3⊓DIV : QProc
Q3⊓DIV = Q3 ⊓ DIV

------------------------------------------------------------------------------------
-- §B. The proofs.
--
-- §B.0 sets up the LTS/failures/divergences vocabulary and the one-step facts about
-- each state; §B.1 to §B.6 are the six FDR assertions.
------------------------------------------------------------------------------------

import Semantics.LTS                  {E = QEv} {I = ExtI QEv} as L
import Semantics.Refusals             {E = QEv} {I = ExtI QEv} as Rf
import Semantics.Failures             {E = QEv} {I = ExtI QEv} as F
import Semantics.FailuresDivergences  {E = QEv} {I = ExtI QEv} as FD

-- generic stability facts, and the one external-choice lemma this example needs:
-- P □ Q is stable when both operands are (its merged τ-part is pointwise `nothing`)
open import Semantics.Stability {E = QEv} {I = ExtI QEv} using (mk-stable; stable-no-τ)
open import CSP.Laws.FD.ExtChoiceAssoc QEv-≟ using (stable-□-join)

-- the two visible events, as labels of the LTS
aEv bEv : L.Event√ (⊤poly {lzero})
aEv = L.evl (L.evLabel ⊤ a tt)
bEv = L.evl (L.evLabel ⊤ b tt)

------------------------------------------------------------------------------------
-- §B.0.1  One-step transitions.
------------------------------------------------------------------------------------

-- Q2's internal choice picks the a-branch
q2-τa : Q2 L.─[ L.τ ]─► Pa
q2-τa = L.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

-- …or the b-branch
q2-τb : Q2 L.─[ L.τ ]─► Pb
q2-τb = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- Q3's internal choice picks STOP…
q3-τstop : Q3 L.─[ L.τ ]─► STOP
q3-τstop = L.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

-- …or Q1
q3-τq1 : Q3 L.─[ L.τ ]─► Q1
q3-τq1 = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- Q4's internal choice picks a -> STOP…
q4-τa : Q4 L.─[ L.τ ]─► Pa
q4-τa = L.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

-- …or b -> DIV
q4-τb : Q4 L.─[ L.τ ]─► PbDiv
q4-τb = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- (Q3 |~| DIV) can resolve to DIV
q3div-τdiv : Q3⊓DIV L.─[ L.τ ]─► DIV
q3div-τdiv = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- the visible step of a -> STOP
pa-a : Pa L.─[ L.ev aEv ]─► STOP
pa-a = L.sVis {at = ⊤ , a} refl refl

-- the visible step of b -> STOP
pb-b : Pb L.─[ L.ev bEv ]─► STOP
pb-b = L.sVis {at = ⊤ , b} refl refl

-- the visible step of b -> DIV
pbdiv-b : PbDiv L.─[ L.ev bEv ]─► DIV
pbdiv-b = L.sVis {at = ⊤ , b} refl refl

-- Q1's a-branch
q1-a : Q1 L.─[ L.ev aEv ]─► STOP
q1-a = L.sVis {at = ⊤ , a} refl refl

-- Q1's b-branch
q1-b : Q1 L.─[ L.ev bEv ]─► STOP
q1-b = L.sVis {at = ⊤ , b} refl refl

-- DIV's only move: the hidden a re-emerges as a τ back to DIV
DIV-τ : DIV L.─[ L.τ ]─► DIV
DIV-τ = L.sTau {i = _ , pair (fin {n = 2}) (base a)} {a = lift (fsuc fzero) , tt} refl refl

------------------------------------------------------------------------------------
-- §B.0.2  Stability, refusals and non-divergence of the τ-free states.
------------------------------------------------------------------------------------

-- a node whose τ-part is ∅t has no τ-step at all
∅t-noτ : ∀ {P t : QProc} {v} → force P ≡ react v ∅t → ¬ (P L.─[ L.τ ]─► t)
∅t-noτ eq (L.sSil e)     = sil≢react (trans (sym e) eq)
∅t-noτ eq (L.sTau e br) with react-injective (trans (sym eq) e)
... | _ , refl = case br of λ ()

-- …hence it cannot be the head of an infinite τ-path
∅t-noDiv : ∀ {P : QProc} {v} → force P ≡ react v ∅t → ¬ L.Diverges P
∅t-noDiv eq d = ∅t-noτ eq (d .L.Diverges.step)

-- STOP offers nothing
stop-no-vis : ∀ {e t} → ¬ (STOP L.─[ L.ev e ]─► t)
stop-no-vis (L.sRet ())
stop-no-vis (L.sVis refl br) = case br of λ ()

-- …so STOP refuses every event set (it is the maximally refusing process)
stop-refuses : ∀ {ℓx} {X : L.Event√ (⊤poly {lzero}) → Set ℓx} → Rf.Refuses STOP X
stop-refuses = (λ _ _ → refl) , λ _ _ (_ , st) → stop-no-vis st

-- a -> STOP is stable: a pure-visible react whose τ-part is literally ∅t
pa-stable : isStable Pa
pa-stable = mk-stable {t = Pa} refl (λ _ _ → refl)

-- and so is b -> STOP
pb-stable : isStable Pb
pb-stable = mk-stable {t = Pb} refl (λ _ _ → refl)

-- …hence Q1 = Pa □ Pb is stable too: □-mt merges two empty τ-parts into a pointwise
-- empty one, which is exactly what stable-□-join certifies
q1-stable : isStable Q1
q1-stable = stable-□-join {P = Pa} {Q = Pb} pa-stable pb-stable

-- Q2 is NOT stable: its internal choice offers a τ
q2-not-stable : ¬ (isStable Q2)
q2-not-stable st = case st (_ , fin {n = 2}) (lift fzero) of λ ()

-- neither is Q4
q4-not-stable : ¬ (isStable Q4)
q4-not-stable st = case st (_ , fin {n = 2}) (lift fzero) of λ ()

------------------------------------------------------------------------------------
-- §B.0.3  DIV: no visible move, every τ returns to DIV, hence a genuine divergence.
------------------------------------------------------------------------------------

-- DIV offers no visible event: a is hidden, and AS never offered b
DIV-no-vis : ∀ {e t} → ¬ (DIV L.─[ L.ev e ]─► t)
DIV-no-vis (L.sRet ())
DIV-no-vis (L.sVis {at = _ , a} refl br) = case br of λ ()
DIV-no-vis (L.sVis {at = _ , b} refl br) = case br of λ ()

-- every τ out of DIV leads straight back to DIV
DIV-τ-target : ∀ {t} → DIV L.─[ L.τ ]─► t → t ≡ DIV
DIV-τ-target (L.sSil ())
DIV-τ-target (L.sTau {i = _ , base _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , fin} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair (base _) _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair fin _} {a = lift fzero , _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair fin (base a)} {a = lift (fsuc fzero) , _} refl refl) = refl
DIV-τ-target (L.sTau {i = _ , pair fin (base b)} {a = lift (fsuc fzero) , _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair fin (pair _ _)} {a = lift (fsuc fzero) , _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair fin fin} {a = lift (fsuc fzero) , _} refl br) = case br of λ ()
DIV-τ-target (L.sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , _} refl br) = case br of λ ()

-- DIV diverges: the hidden a fires forever
DIV-diverges : L.Diverges DIV
DIV-diverges .L.Diverges.next = DIV
DIV-diverges .L.Diverges.step = DIV-τ
DIV-diverges .L.Diverges.rest = DIV-diverges

-- DIV is never stable, so it is never the endpoint of a (stable) failure
DIV-not-stable : ¬ (isStable DIV)
DIV-not-stable st =
  case st (_ , pair (fin {n = 2}) (base a)) (lift (fsuc fzero) , tt) of λ ()

-- every run of DIV is silent and stays at DIV
DIV-run : ∀ {s P'} → DIV F.⟹⟨ s ⟩ P' → (s ≡ []) × (P' ≡ DIV)
DIV-run F.⟹-refl = refl , refl
DIV-run (F.⟹-τ st rest) with DIV-τ-target st
... | refl = DIV-run rest
DIV-run (F.⟹-ev st _) = ⊥-elim (DIV-no-vis st)

-- DIV diverges immediately, so EVERY trace is one of its divergences (it is ⊥ in FD)
DIV-divergence-any : ∀ {s} → FD.divergences DIV s
DIV-divergence-any {s} = record
  { prefix = [] ; suffix = s ; split = refl
  ; witness = DIV ; reach = F.⟹-refl ; divwit = DIV-diverges }

------------------------------------------------------------------------------------
-- §B.0.4  Run inversions: which traces each process can perform, and where it ends.
------------------------------------------------------------------------------------

-- STOP cannot move, so its only run is the empty one
stop-run : ∀ {s P'} → STOP F.⟹⟨ s ⟩ P' → (s ≡ []) × (P' ≡ STOP)
stop-run F.⟹-refl = refl , refl
stop-run (F.⟹-τ (L.sSil ()) _)
stop-run (F.⟹-τ (L.sTau refl br) _) = case br of λ ()
stop-run (F.⟹-ev st _) = ⊥-elim (stop-no-vis st)

-- a -> STOP: either nothing has happened, or a has, leaving STOP
pa-run : ∀ {s P'} → Pa F.⟹⟨ s ⟩ P'
       → ((s ≡ []) × (P' ≡ Pa)) ⊎ ((s ≡ aEv ∷ []) × (P' ≡ STOP))
pa-run F.⟹-refl = inj₁ (refl , refl)
pa-run (F.⟹-τ (L.sSil ()) _)
pa-run (F.⟹-τ (L.sTau refl br) _) = case br of λ ()
pa-run (F.⟹-ev (L.sRet ()) _)
pa-run (F.⟹-ev (L.sVis {at = _ , b} refl br) _) = case br of λ ()
pa-run (F.⟹-ev (L.sVis {at = _ , a} refl refl) rest) with stop-run rest
... | refl , refl = inj₂ (refl , refl)

-- b -> STOP: symmetric
pb-run : ∀ {s P'} → Pb F.⟹⟨ s ⟩ P'
       → ((s ≡ []) × (P' ≡ Pb)) ⊎ ((s ≡ bEv ∷ []) × (P' ≡ STOP))
pb-run F.⟹-refl = inj₁ (refl , refl)
pb-run (F.⟹-τ (L.sSil ()) _)
pb-run (F.⟹-τ (L.sTau refl br) _) = case br of λ ()
pb-run (F.⟹-ev (L.sRet ()) _)
pb-run (F.⟹-ev (L.sVis {at = _ , a} refl br) _) = case br of λ ()
pb-run (F.⟹-ev (L.sVis {at = _ , b} refl refl) rest) with stop-run rest
... | refl , refl = inj₂ (refl , refl)

-- b -> DIV: after b the process is inside DIV and stays there
pbdiv-run : ∀ {s P'} → PbDiv F.⟹⟨ s ⟩ P'
          → ((s ≡ []) × (P' ≡ PbDiv)) ⊎ ((s ≡ bEv ∷ []) × (P' ≡ DIV))
pbdiv-run F.⟹-refl = inj₁ (refl , refl)
pbdiv-run (F.⟹-τ (L.sSil ()) _)
pbdiv-run (F.⟹-τ (L.sTau refl br) _) = case br of λ ()
pbdiv-run (F.⟹-ev (L.sRet ()) _)
pbdiv-run (F.⟹-ev (L.sVis {at = _ , a} refl br) _) = case br of λ ()
pbdiv-run (F.⟹-ev (L.sVis {at = _ , b} refl refl) rest) with DIV-run rest
... | refl , refl = inj₂ (refl , refl)

-- Q1 is stable, and its only visible steps are a and b, both leading to STOP
q1-run : ∀ {s P'} → Q1 F.⟹⟨ s ⟩ P'
       → ((s ≡ []) × (P' ≡ Q1))
       ⊎ (((s ≡ aEv ∷ []) × (P' ≡ STOP)) ⊎ ((s ≡ bEv ∷ []) × (P' ≡ STOP)))
q1-run F.⟹-refl = inj₁ (refl , refl)
q1-run (F.⟹-τ st _) = ⊥-elim (stable-no-τ q1-stable st)
q1-run (F.⟹-ev (L.sRet ()) _)
q1-run (F.⟹-ev (L.sVis {at = _ , a} refl refl) rest) with stop-run rest
... | refl , refl = inj₂ (inj₁ (refl , refl))
q1-run (F.⟹-ev (L.sVis {at = _ , b} refl refl) rest) with stop-run rest
... | refl , refl = inj₂ (inj₂ (refl , refl))

-- Q2: the empty trace leaves it at Q2 itself or at one of the two resolved prefixes;
-- the only non-empty traces are <a> and <b>, both ending at STOP
q2-run : ∀ {s P'} → Q2 F.⟹⟨ s ⟩ P'
       → ((s ≡ []) × ((P' ≡ Q2) ⊎ ((P' ≡ Pa) ⊎ (P' ≡ Pb))))
       ⊎ (((s ≡ aEv ∷ []) × (P' ≡ STOP)) ⊎ ((s ≡ bEv ∷ []) × (P' ≡ STOP)))
q2-run F.⟹-refl = inj₁ (refl , inj₁ refl)
q2-run (F.⟹-ev (L.sRet ()) _)
q2-run (F.⟹-ev (L.sVis refl br) _) = case br of λ ()
q2-run (F.⟹-τ (L.sSil ()) _)
q2-run (F.⟹-τ (L.sTau {i = _ , base _} refl br) _) = case br of λ ()
q2-run (F.⟹-τ (L.sTau {i = _ , pair _ _} refl br) _) = case br of λ ()
q2-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) _) = case br of λ ()
q2-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift fzero} refl refl) rest) with pa-run rest
... | inj₁ (refl , refl) = inj₁ (refl , inj₂ (inj₁ refl))
... | inj₂ (refl , refl) = inj₂ (inj₁ (refl , refl))
q2-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) rest) with pb-run rest
... | inj₁ (refl , refl) = inj₁ (refl , inj₂ (inj₂ refl))
... | inj₂ (refl , refl) = inj₂ (inj₂ (refl , refl))

-- Q4: as Q2, except that the b-branch ends inside DIV rather than at STOP
q4-run : ∀ {s P'} → Q4 F.⟹⟨ s ⟩ P'
       → ((s ≡ []) × ((P' ≡ Q4) ⊎ ((P' ≡ Pa) ⊎ (P' ≡ PbDiv))))
       ⊎ (((s ≡ aEv ∷ []) × (P' ≡ STOP)) ⊎ ((s ≡ bEv ∷ []) × (P' ≡ DIV)))
q4-run F.⟹-refl = inj₁ (refl , inj₁ refl)
q4-run (F.⟹-ev (L.sRet ()) _)
q4-run (F.⟹-ev (L.sVis refl br) _) = case br of λ ()
q4-run (F.⟹-τ (L.sSil ()) _)
q4-run (F.⟹-τ (L.sTau {i = _ , base _} refl br) _) = case br of λ ()
q4-run (F.⟹-τ (L.sTau {i = _ , pair _ _} refl br) _) = case br of λ ()
q4-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) _) = case br of λ ()
q4-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift fzero} refl refl) rest) with pa-run rest
... | inj₁ (refl , refl) = inj₁ (refl , inj₂ (inj₁ refl))
... | inj₂ (refl , refl) = inj₂ (inj₁ (refl , refl))
q4-run (F.⟹-τ (L.sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl) rest) with pbdiv-run rest
... | inj₁ (refl , refl) = inj₁ (refl , inj₂ (inj₂ refl))
... | inj₂ (refl , refl) = inj₂ (inj₂ (refl , refl))

-- Q2 never diverges: every state it can reach is τ-free or resolves to one that is
-- a divergence exposed as its first τ-step plus the divergence that follows it, with
-- the intermediate state a genuine variable (a record projection cannot be unified
-- against, so the step could not be case-split on in place)
div-step : ∀ {P : QProc}
         → L.Diverges P → Σ QProc (λ t → (P L.─[ L.τ ]─► t) × L.Diverges t)
div-step d = _ , d .L.Diverges.step , d .L.Diverges.rest

q2-self-noDiv : ¬ L.Diverges Q2
q2-self-noDiv d with div-step d
... | _ , L.sSil () , _
... | _ , L.sTau {i = _ , base _} refl br , _ = case br of λ ()
... | _ , L.sTau {i = _ , pair _ _} refl br , _ = case br of λ ()
... | _ , L.sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br , _ = case br of λ ()
... | _ , L.sTau {i = _ , fin} {a = lift fzero} refl refl , d' = ∅t-noDiv refl d'
... | _ , L.sTau {i = _ , fin} {a = lift (fsuc fzero)} refl refl , d' = ∅t-noDiv refl d'

-- …hence no state reachable from Q2 diverges
q2-reach-noDiv : ∀ {s w} → Q2 F.⟹⟨ s ⟩ w → ¬ L.Diverges w
q2-reach-noDiv run d with q2-run run
... | inj₁ (_ , inj₁ refl)        = q2-self-noDiv d
... | inj₁ (_ , inj₂ (inj₁ refl)) = ∅t-noDiv refl d
... | inj₁ (_ , inj₂ (inj₂ refl)) = ∅t-noDiv refl d
... | inj₂ (inj₁ (_ , refl))      = ∅t-noDiv refl d
... | inj₂ (inj₂ (_ , refl))      = ∅t-noDiv refl d

-- …so Q2 has no divergences at all
q2-noDivs : ∀ {s} → ¬ (FD.divergences Q2 s)
q2-noDivs dv =
  q2-reach-noDiv (dv .FD.IsDivergence.reach) (dv .FD.IsDivergence.divwit)

------------------------------------------------------------------------------------
-- §B.0.5  Offer transfer between states with the same visible menu.
------------------------------------------------------------------------------------

-- anything a -> STOP offers, Q1 offers (Q1's menu is {a,b})
pa-offer→q1 : ∀ {e} → Rf.Offers Pa e → Rf.Offers Q1 e
pa-offer→q1 (_ , L.sRet ())
pa-offer→q1 (_ , L.sVis {at = _ , b} refl br) = case br of λ ()
pa-offer→q1 (_ , L.sVis {at = _ , a} refl refl) = STOP , q1-a

-- so a state refusing Q1's menu also refuses a -> STOP's menu
q1-refuse→pa : ∀ {ℓx} {X : L.Event√ (⊤poly {lzero}) → Set ℓx}
             → Rf.Refuses Q1 X → Rf.Refuses Pa X
q1-refuse→pa (_ , noff) = (λ _ _ → refl) , λ e Xe off → noff e Xe (pa-offer→q1 off)

-- b -> STOP and b -> DIV offer exactly b, so their offers transfer both ways
pb-offer→pbdiv : ∀ {e} → Rf.Offers Pb e → Rf.Offers PbDiv e
pb-offer→pbdiv (_ , L.sRet ())
pb-offer→pbdiv (_ , L.sVis {at = _ , a} refl br) = case br of λ ()
pb-offer→pbdiv (_ , L.sVis {at = _ , b} refl refl) = DIV , pbdiv-b

pbdiv-offer→pb : ∀ {e} → Rf.Offers PbDiv e → Rf.Offers Pb e
pbdiv-offer→pb (_ , L.sRet ())
pbdiv-offer→pb (_ , L.sVis {at = _ , a} refl br) = case br of λ ()
pbdiv-offer→pb (_ , L.sVis {at = _ , b} refl refl) = STOP , pb-b

-- …hence their refusals transfer both ways too
pbdiv-refuse→pb : ∀ {ℓx} {X : L.Event√ (⊤poly {lzero}) → Set ℓx}
                → Rf.Refuses PbDiv X → Rf.Refuses Pb X
pbdiv-refuse→pb (_ , noff) = (λ _ _ → refl) , λ e Xe off → noff e Xe (pb-offer→pbdiv off)

pb-refuse→pbdiv : ∀ {ℓx} {X : L.Event√ (⊤poly {lzero}) → Set ℓx}
                → Rf.Refuses Pb X → Rf.Refuses PbDiv X
pb-refuse→pbdiv (_ , noff) = (λ _ _ → refl) , λ e Xe off → noff e Xe (pbdiv-offer→pb off)

------------------------------------------------------------------------------------
-- §B.1  assert Q3 [F= Q2 — TRUE.
--
-- Q3 = STOP |~| Q1 can always resolve to STOP, so at the empty trace it refuses
-- EVERY event set; after <a> or <b> it resolves to Q1, performs the event and
-- deadlocks.  Q2's traces are exactly <>, <a> and <b>, so every failure of Q2 is
-- matched by the STOP-resolved (or deadlocked) behaviour of Q3.
------------------------------------------------------------------------------------

q3-refines-q2 : Q3 F.⊑F Q2
q3-refines-q2 s X (P' , run , ref) with q2-run run
... | inj₁ (refl , inj₁ refl) = ⊥-elim (q2-not-stable (proj₁ ref))
... | inj₁ (refl , inj₂ (inj₁ refl)) = STOP , F.⟹-τ q3-τstop F.⟹-refl , stop-refuses
... | inj₁ (refl , inj₂ (inj₂ refl)) = STOP , F.⟹-τ q3-τstop F.⟹-refl , stop-refuses
... | inj₂ (inj₁ (refl , refl)) =
      STOP , F.⟹-τ q3-τq1 (F.⟹-ev q1-a F.⟹-refl) , stop-refuses
... | inj₂ (inj₂ (refl , refl)) =
      STOP , F.⟹-τ q3-τq1 (F.⟹-ev q1-b F.⟹-refl) , stop-refuses

------------------------------------------------------------------------------------
-- §B.2  assert Q2 [F= Q1 — TRUE.
--
-- Q1's only stable state at the empty trace is Q1 itself, whose menu is {a,b}; a set
-- Q1 refuses therefore contains neither a nor b, so the a-resolved state of Q2 (which
-- offers only a) refuses it as well.  After <a> or <b> both processes deadlock.
------------------------------------------------------------------------------------

q2-refines-q1 : Q2 F.⊑F Q1
q2-refines-q1 s X (P' , run , ref) with q1-run run
... | inj₁ (refl , refl) = Pa , F.⟹-τ q2-τa F.⟹-refl , q1-refuse→pa ref
... | inj₂ (inj₁ (refl , refl)) =
      STOP , F.⟹-τ q2-τa (F.⟹-ev pa-a F.⟹-refl) , stop-refuses
... | inj₂ (inj₂ (refl , refl)) =
      STOP , F.⟹-τ q2-τb (F.⟹-ev pb-b F.⟹-refl) , stop-refuses

------------------------------------------------------------------------------------
-- §B.3  assert Q3 |~| DIV [FD= DIV — TRUE.
--
-- An internal choice is refined by either of its branches: one τ takes Q3 |~| DIV to
-- DIV, and every failure or divergence of DIV is then reproduced verbatim.
------------------------------------------------------------------------------------

-- prepending a τ-step to a divergence keeps it a divergence of the earlier state
div-prepend-τ : ∀ {P Q : QProc} {s} → P L.─[ L.τ ]─► Q
              → FD.divergences Q s → FD.divergences P s
div-prepend-τ st dv = record
  { prefix  = dv .FD.IsDivergence.prefix
  ; suffix  = dv .FD.IsDivergence.suffix
  ; split   = dv .FD.IsDivergence.split
  ; witness = dv .FD.IsDivergence.witness
  ; reach   = F.⟹-τ st (dv .FD.IsDivergence.reach)
  ; divwit  = dv .FD.IsDivergence.divwit }

q3div-refines-div : Q3⊓DIV FD.⊑FD DIV
q3div-refines-div = fbot , div-prepend-τ q3div-τdiv
  where
  -- both a failure and a divergence of DIV survive the extra τ
  fbot : Q3⊓DIV FD.⊑F⊥ DIV
  fbot (inj₁ (P' , run , ref)) = inj₁ (P' , F.⟹-τ q3div-τdiv run , ref)
  fbot (inj₂ dv)               = inj₂ (div-prepend-τ q3div-τdiv dv)

------------------------------------------------------------------------------------
-- §B.4  assert DIV [FD= Q3 |~| DIV — TRUE (divergence strictness).
--
-- DIV diverges at the empty trace, so in the divergence-strict FD model every trace
-- is one of its divergences and every (trace, refusal) pair is one of its
-- divergence-strict failures.  DIV is the bottom of ⊑FD, so it refines everything.
------------------------------------------------------------------------------------

div-refines-q3div : DIV FD.⊑FD Q3⊓DIV
div-refines-q3div = (λ _ → inj₂ DIV-divergence-any) , (λ _ → DIV-divergence-any)

------------------------------------------------------------------------------------
-- §B.5  assert Q2 [F= Q4 — TRUE, and assert Q4 [F= Q2 — FALSE.
--
-- Q4 = a -> STOP |~| b -> DIV is a PROPER failures refinement of Q2: at the empty
-- trace the two have the same two stable resolutions (b -> DIV offers exactly what
-- b -> STOP offers), and after <a> both deadlock — but after <b> Q4 is inside DIV,
-- which is never stable, so Q4 has NO failure there while Q2 refuses everything.
------------------------------------------------------------------------------------

q2-refines-q4 : Q2 F.⊑F Q4
q2-refines-q4 s X (P' , run , ref) with q4-run run
... | inj₁ (refl , inj₁ refl) = ⊥-elim (q4-not-stable (proj₁ ref))
... | inj₁ (refl , inj₂ (inj₁ refl)) = Pa , F.⟹-τ q2-τa F.⟹-refl , ref
... | inj₁ (refl , inj₂ (inj₂ refl)) = Pb , F.⟹-τ q2-τb F.⟹-refl , pbdiv-refuse→pb ref
... | inj₂ (inj₁ (refl , refl)) =
      STOP , F.⟹-τ q2-τa (F.⟹-ev pa-a F.⟹-refl) , stop-refuses
... | inj₂ (inj₂ (refl , refl)) =
      STOP , F.⟹-τ q2-τb (F.⟹-ev pb-b F.⟹-refl) , stop-refuses

-- the refusal set of the counterexample: every event
allEv : L.Event√ (⊤poly {lzero}) → Set
allEv _ = ⊤

-- witness 1: after <b>, Q2 has deadlocked and refuses everything
q2-fail-b : F.failures Q2 (bEv ∷ []) allEv
q2-fail-b = STOP , F.⟹-τ q2-τb (F.⟹-ev pb-b F.⟹-refl) , stop-refuses

-- witness 2: after <b>, Q4 is inside DIV, which is never stable — so it has no failure
q4-nofail-b : ¬ (F.failures Q4 (bEv ∷ []) allEv)
q4-nofail-b (P' , run , ref) with q4-run run
... | inj₁ (() , _)
... | inj₂ (inj₁ (() , _))
... | inj₂ (inj₂ (_ , refl)) = DIV-not-stable (proj₁ ref)

-- the two witnesses refute the reverse failures refinement
q4-not-refines-q2 : ¬ (Q4 F.⊑F Q2)
q4-not-refines-q2 ref = q4-nofail-b (ref (bEv ∷ []) allEv q2-fail-b)

------------------------------------------------------------------------------------
-- §B.6  assert Q4 [FD= Q2 — TRUE, and assert Q2 [FD= Q4 — FALSE.
--
-- Exactly the opposite of §B.5.  The FD model notices Q4's divergence after <b> and
-- treats it as disastrous: Q4 becomes the bottom process there, so it reproduces
-- Q2's "refuse everything after <b>" failure as a DIVERGENCE.  In the other
-- direction Q2, which never diverges, cannot match Q4's divergence.
------------------------------------------------------------------------------------

-- Q4 diverges after the trace <b>
q4-div-b : FD.divergences Q4 (bEv ∷ [])
q4-div-b = record
  { prefix  = bEv ∷ [] ; suffix = [] ; split = refl
  ; witness = DIV
  ; reach   = F.⟹-τ q4-τb (F.⟹-ev pbdiv-b F.⟹-refl)
  ; divwit  = DIV-diverges }

q4-refines-q2-fd : Q4 FD.⊑FD Q2
q4-refines-q2-fd = fbot , λ dv → ⊥-elim (q2-noDivs dv)
  where
  -- Q2's failures are matched by Q4's own failures, except the one after <b>, which
  -- is matched by Q4's divergence there; Q2 contributes no divergences at all
  fbot : Q4 FD.⊑F⊥ Q2
  fbot (inj₂ dv) = ⊥-elim (q2-noDivs dv)
  fbot (inj₁ (P' , run , ref)) with q2-run run
  ... | inj₁ (refl , inj₁ refl) = ⊥-elim (q2-not-stable (proj₁ ref))
  ... | inj₁ (refl , inj₂ (inj₁ refl)) = inj₁ (Pa , F.⟹-τ q4-τa F.⟹-refl , ref)
  ... | inj₁ (refl , inj₂ (inj₂ refl)) =
        inj₁ (PbDiv , F.⟹-τ q4-τb F.⟹-refl , pb-refuse→pbdiv ref)
  ... | inj₂ (inj₁ (refl , refl)) =
        inj₁ (STOP , F.⟹-τ q4-τa (F.⟹-ev pa-a F.⟹-refl) , stop-refuses)
  ... | inj₂ (inj₂ (refl , refl)) = inj₂ q4-div-b

-- …but Q2 cannot refine Q4 in the FD model: it has no divergence to match Q4's
q2-not-refines-q4-fd : ¬ (Q2 FD.⊑FD Q4)
q2-not-refines-q4-fd (_ , d) = q2-noDivs (d q4-div-b)
