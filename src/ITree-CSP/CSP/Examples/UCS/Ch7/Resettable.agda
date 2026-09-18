{-# OPTIONS --guardedness #-}

-- UCS chapter 7 §7.2, "Illustrating interrupt and throw" (section7-2.csp, A.W.
-- Roscoe; source fdr-examples/ucs/chapter07/section7-2.csp) — the INTERRUPT half,
-- i.e. everything above that file's `--&&&&…` separator line.  The throw half of the
-- same file (R / RT / revivable / Divide) is a separate module.
--
--   channel a,b,c,lightning
--   resettable(P) = P /\ lightning -> resettable(P)
--   Q = a -> b -> c -> Q
--   RQ = lightning -> RQ
--        [] a -> (lightning -> RQ [] b -> (lightning -> RQ [] c -> RQ))
--
-- §A models the processes, §B proves the assertions FDR makes about them:
--
--   Q /\ (b -> STOP) :[deterministic]              FALSE  (§B.1)
--   resettable(Q) [FD= RQ                          TRUE   (§B.3, via §B.2)
--   resettable(Q) :[deterministic]                 TRUE   (§B.4)
--   resettable(Q) [FD= resettable(resettable(Q))   TRUE   (§B.6, via §B.5)
--   resettable(resettable(Q)) [FD= resettable(Q)   TRUE   (§B.6) — so `resettable`
--                                                         is FD-idempotent
--
-- WHY THE LAST TWO DIFFER — the point of Roscoe's pairing.  `_△_`'s both-offer rule
-- (`CSP/Operators.agda`: an event offered by BOTH operands yields `(P′ △ Q) ⊓ Q′`) is
-- the only source of nondeterminism an interrupt can introduce.  In `resettable(Q)`
-- the interrupt offers only `lightning`, which is disjoint from Q's alphabet
-- {a,b,c} ⇒ no overlap ever arises and the result stays deterministic.  In
-- `Q /\ (b -> STOP)` the interrupt offers `b`, which Q itself offers after ⟨a⟩ ⇒ the
-- overlap fires, and after ⟨a,b⟩ the process may be `c -> Q` OR `STOP`; `STOP`
-- stably refuses `c` although ⟨a,b,c⟩ is still a trace, which is exactly a violation
-- of `Deterministic`.
--
-- PRODUCTIVITY — WHY `resettable` IS NOT A DEFINITION HERE.  `resettable` is
-- corecursive THROUGH the operator under test, and Agda's `--guardedness` checker
-- CANNOT accept that, in any formulation.  Both honest shapes were tried and both are
-- rejected with [TerminationIssue]:
--
--   (1) the forward-declared pair, corecursive occurrence a DIRECT argument of `just`
--         resettable P = P △ lightningH P
--         force (lightningH P) = react (λ where (_ , lightning) _ → just (resettable P)
--                                               …                 → nothing) ∅t
--       ⇒ "Termination checking failed … resettable, lightningH.  Problematic calls:
--          lightningH P … resettable P"
--   (2) the single self-recursive handler with a named (non-extended-lambda)
--       continuation, the △-term itself under `just`
--         force (lightningH P) = react (lh-vis P) ∅t
--         lh-vis P (_ , lightning) _ = just (P △ lightningH P)
--       ⇒ "Termination checking failed … lightningH, lh-vis.  Problematic calls:
--          lh-vis P … lightningH P"
--
-- The reason is the one recorded in `CSP/Examples/UCS/Ch7/Counter.agda`'s header:
-- guardedness is LOST inside the arguments of a defined function, so a corecursive
-- occurrence reached through the call `_ △ _` is never seen as guarded — even when the
-- whole △-term sits under `just`, and even though the recursion is genuinely
-- productive (`_△_` forces each operand exactly once).  It works INSIDE
-- `CSP/Operators.agda` only because there `△-merge`'s `just (P′ △ Q)` and `_△_` are in
-- one mutual clique, so the checker sees `_△_`'s own constructor-guarded body.  A
-- client cannot join that clique.  Neither `NON_TERMINATING`/`TERMINATING`, nor sized
-- types, nor inlining `△` away, nor a postulate is used here (all four are excluded);
-- what WOULD be needed is either a guarded-fixpoint combinator for `PTree` (a `later`
-- modality / sized `_△_`) or `_△_` re-exported together with a clique-joining
-- fixpoint, neither of which exists in this development.
--
-- WHAT IS DONE INSTEAD — a CERTIFIED FIXPOINT, not an inlining.  Roscoe's recursion is
-- ported as its defining equation plus a witness for the recursive occurrence:
--
--   Hr = lightning ⟶₀ RQ            L1 = Q △ Hr             (§A)
--   §B.2   fix-L1 : RQ ≈DR L1
--
-- i.e. `L1` IS an application of the real `_△_` to the real prefix, and §B.2 proves
-- that the process its handler restarts (`RQ`) is behaviourally the whole of `L1` —
-- which is exactly the content of `resettable(Q) = Q /\ lightning -> resettable(Q)`.
-- So `L1` is `resettable(Q)` up to `≈DR` (hence up to the FD model), and §B.3/§B.4
-- state the book's assertions about it on the genuine △-term.  §B.5 does the same one
-- level up for `L2 = L1 △ Hr = resettable(resettable(Q))`, proving `RQ ≈DR L2`
-- independently of §B.2/§B.3 — the recursion `X = L1 /\ lightning -> X` is guarded and
-- so has a unique FD solution, and exhibiting one identifies it; nothing is assumed
-- about the level-1 result, so no question is begged.  `Q` and `RQ` are raw `react`
-- nodes: they contain no operator under test, so the codebase's standard inlined idiom
-- is fine for them and makes their step/inversion facts hold by `refl`.
--
-- CLASSICAL FOOTPRINT.  §B.1 and §B.4 are postulate-free (trace/failures level only).
-- §B.3 and §B.6 go through `Semantics.DRImpliesFD`'s `drbisim→⊑FD`, hence through the
-- development's single sanctioned classical postulate `¬-divergent→normal` — the
-- established route for FD facts obtained from a bisimulation (see the note at the
-- foot of `Semantics/DRImpliesFD.agda`).  No new postulate is introduced here.

module CSP.Examples.UCS.Ch7.Resettable where

open import Level using (Lift; lift) renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (DecEq; Irrelevant⇒DecEq)

open import Process_Trees
open PTree

-- DecEq on the polymorphic unit return type, which the √-aware operators ask for
instance
  DecEq-⊤poly : DecEq (⊤poly {lzero})
  DecEq-⊤poly = Irrelevant⇒DecEq (λ { (lift _) (lift _) → refl })

------------------------------------------------------------------------------------
-- §A. The model.
------------------------------------------------------------------------------------

-- the four channels of §7.2; all carry ⊤ (a ⊥-carried event could never fire)
data REv : Set → Set where
  a b c lightning : REv ⊤

-- decidable equality on the event indices, as every CSP operator module needs
REv-≟ : (x y : AnyTypes REv) → Dec (x ≡ y)
REv-≟ (_ , a)         (_ , a)         = yes refl
REv-≟ (_ , b)         (_ , b)         = yes refl
REv-≟ (_ , c)         (_ , c)         = yes refl
REv-≟ (_ , lightning) (_ , lightning) = yes refl
REv-≟ (_ , a)         (_ , b)         = no (λ ())
REv-≟ (_ , a)         (_ , c)         = no (λ ())
REv-≟ (_ , a)         (_ , lightning) = no (λ ())
REv-≟ (_ , b)         (_ , a)         = no (λ ())
REv-≟ (_ , b)         (_ , c)         = no (λ ())
REv-≟ (_ , b)         (_ , lightning) = no (λ ())
REv-≟ (_ , c)         (_ , a)         = no (λ ())
REv-≟ (_ , c)         (_ , b)         = no (λ ())
REv-≟ (_ , c)         (_ , lightning) = no (λ ())
REv-≟ (_ , lightning) (_ , a)         = no (λ ())
REv-≟ (_ , lightning) (_ , b)         = no (λ ())
REv-≟ (_ , lightning) (_ , c)         = no (λ ())

import CSP.Operators
module OpsR = CSP.Operators REv-≟
open OpsR

-- the process type of this example: no data is returned, so R = ⊤
RProc : Set₁
RProc = PTree REv (ExtI REv) (⊤poly {lzero})

-- STOP at this example's process type (pins the return type R, which `Stop` leaves open)
STOP : RProc
STOP = Stop

-- Q = a -> b -> c -> Q, as its three states.  `Qa`/`Qb`/`Qc` are raw `react` nodes:
-- no operator under test occurs in Q, and the inlined form makes every step and
-- inversion fact below hold by `refl`.
Qa Qb Qc : RProc

-- Qa = a -> (b -> c -> Qa)
force Qa = react (λ where (_ , a)         _ → just Qb
                          (_ , b)         _ → nothing
                          (_ , c)         _ → nothing
                          (_ , lightning) _ → nothing)
                 ∅t

-- Qb = b -> c -> Qa
force Qb = react (λ where (_ , b)         _ → just Qc
                          (_ , a)         _ → nothing
                          (_ , c)         _ → nothing
                          (_ , lightning) _ → nothing)
                 ∅t

-- Qc = c -> Qa
force Qc = react (λ where (_ , c)         _ → just Qa
                          (_ , a)         _ → nothing
                          (_ , b)         _ → nothing
                          (_ , lightning) _ → nothing)
                 ∅t

-- Q itself
Q : RProc
Q = Qa

-- RQ = lightning -> RQ [] a -> (lightning -> RQ [] b -> (lightning -> RQ [] c -> RQ)),
-- the book's hand-unrolled version of `resettable(Q)`, as its three states (again raw
-- `react`: RQ contains no operator under test).  §B.2 certifies that RQ SOLVES
-- `resettable`'s defining equation, which is what lets `L1` below carry the name.
RQa RQb RQc : RProc

-- RQ itself: lightning -> RQ [] a -> RQb
force RQa = react (λ where (_ , lightning) _ → just RQa
                           (_ , a)         _ → just RQb
                           (_ , b)         _ → nothing
                           (_ , c)         _ → nothing)
                  ∅t

-- lightning -> RQ [] b -> RQc
force RQb = react (λ where (_ , lightning) _ → just RQa
                           (_ , b)         _ → just RQc
                           (_ , a)         _ → nothing
                           (_ , c)         _ → nothing)
                  ∅t

-- lightning -> RQ [] c -> RQ
force RQc = react (λ where (_ , lightning) _ → just RQa
                           (_ , c)         _ → just RQa
                           (_ , a)         _ → nothing
                           (_ , b)         _ → nothing)
                  ∅t

-- RQ itself
RQ : RProc
RQ = RQa

-- lightning -> RQ, the lightning handler (the real prefix operator; no recursion, so
-- `_⟶₀_` can be used directly)
Hr : RProc
Hr = lightning ⟶₀ RQ

-- resettable(Q) = Q /\ (lightning -> resettable(Q)), through the REAL interrupt, with
-- RQ as the fixpoint witness for the recursive occurrence — §B.2 discharges exactly
-- that: `RQ ≈DR L1`, i.e. the handler really does restart a process DR-equal to the
-- whole of `L1`, so `L1` satisfies Roscoe's defining equation.
L1 : RProc
L1 = Q △ Hr

-- b -> STOP, the interrupt of the FALSE determinism assertion
Pb : RProc
Pb = b ⟶₀ STOP

-- Q /\ (b -> STOP): `b` lies in BOTH operands' alphabets, so the interrupt overlaps Q
QI : RProc
QI = Q △ Pb

-- the state Q /\ (b -> STOP) reaches after ⟨a⟩: `Qb` and `b -> STOP` both offer `b`
QIb : RProc
QIb = Qb △ Pb

-- …and after ⟨a,b⟩: the internal choice `(c -> Q /\ (b -> STOP)) |~| STOP` that
-- `△-merge`'s both-offer rule builds.  Its two τ-branches are `Qc △ Pb` (tag 0, Q
-- continues) and `STOP` (tag 1, the interrupt fired).
QIab : RProc
QIab = ptree (react ∅v (△-br2 Qc Pb STOP))

------------------------------------------------------------------------------------
-- §B. The proofs.
--
-- §B.0 sets up the LTS/failures vocabulary and the one-step facts; §B.1 is the FALSE
-- determinism assertion, §B.2 the fixpoint certification (and with it the
-- `resettable(Q) [FD= RQ` assertion), §B.3 the TRUE determinism assertion.
------------------------------------------------------------------------------------

import Semantics.LTS         {E = REv} {I = ExtI REv} as L
import Semantics.Refusals    {E = REv} {I = ExtI REv} as Rf
import Semantics.Failures    {E = REv} {I = ExtI REv} as F
import Semantics.Determinism {E = REv} {I = ExtI REv} as D

-- the four events of §7.2, as labels of the LTS (all carry the single value tt)
aEv bEv cEv lEv : L.Event√ (⊤poly {lzero})
aEv = L.evl (L.evLabel ⊤ a tt)
bEv = L.evl (L.evLabel ⊤ b tt)
cEv = L.evl (L.evLabel ⊤ c tt)
lEv = L.evl (L.evLabel ⊤ lightning tt)

------------------------------------------------------------------------------------
-- §B.0  STOP: no offers, hence a refusal of every set.
------------------------------------------------------------------------------------

-- STOP offers nothing
stop-no-vis : ∀ {e t} → ¬ (STOP L.─[ L.ev e ]─► t)
stop-no-vis (L.sRet ())
stop-no-vis (L.sVis refl br) = case br of λ ()

-- …so STOP refuses every event set (it is the maximally refusing process)
stop-refuses : ∀ {ℓx} {X : L.Event√ (⊤poly {lzero}) → Set ℓx} → Rf.Refuses STOP X
stop-refuses = (λ _ _ → refl) , λ _ _ (_ , st) → stop-no-vis st

------------------------------------------------------------------------------------
-- §B.1  assert Q /\ (b -> STOP) :[deterministic] — FALSE.
--
-- `b` is offered by BOTH operands after ⟨a⟩ (Q sits at `b -> c -> Q`, the interrupt
-- at `b -> STOP`), so `△-merge`'s both-offer rule turns the `b` into
-- `(c -> Q /\ (b -> STOP)) |~| STOP`.  After ⟨a,b⟩ the process may therefore be
-- `c -> Q /\ …` (so ⟨a,b,c⟩ is a trace) or `STOP` (which stably refuses `c`) —
-- exactly a violation of `Deterministic`.  Trace + failures level only, no
-- FailuresDivergences, no postulate.
------------------------------------------------------------------------------------

-- Q /\ (b -> STOP) offers `a` (only Q offers it), reaching `Qb △ Pb`
qi-a : QI L.─[ L.ev aEv ]─► QIb
qi-a = L.sVis {at = ⊤ , a} refl refl

-- after ⟨a⟩ the `b` is offered by both operands, so it leads to the internal choice
qib-b : QIb L.─[ L.ev bEv ]─► QIab
qib-b = L.sVis {at = ⊤ , b} refl refl

-- the internal choice can resolve to "Q continues" (△-br2's tag 0)…
qiab-τ-Q : QIab L.─[ L.τ ]─► (Qc △ Pb)
qiab-τ-Q = L.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

-- …or to "the interrupt fired" (tag 1), i.e. STOP
qiab-τ-stop : QIab L.─[ L.τ ]─► STOP
qiab-τ-stop = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- on the Q-continues branch the `c` is offered by Q alone, and the cycle restarts
qic-c : (Qc △ Pb) L.─[ L.ev cEv ]─► QI
qic-c = L.sVis {at = ⊤ , c} refl refl

-- witness 1: ⟨a,b,c⟩ is a trace of Q /\ (b -> STOP)
qi-trace : F.traces QI ((aEv ∷ bEv ∷ []) ∷ʳ cEv)
qi-trace = QI , F.⟹-ev qi-a (F.⟹-ev qib-b (F.⟹-τ qiab-τ-Q (F.⟹-ev qic-c F.⟹-refl)))

-- witness 2: after ⟨a,b⟩ the interrupt may have fired, leaving STOP, which stably
-- refuses `c`
qi-fail : F.failures QI (aEv ∷ bEv ∷ []) (λ e → e ≡ cEv)
qi-fail = STOP
        , F.⟹-ev qi-a (F.⟹-ev qib-b (F.⟹-τ qiab-τ-stop F.⟹-refl))
        , stop-refuses

-- the two witnesses refute determinism
qi-nondet : ¬ D.Deterministic QI
qi-nondet det = det {s = aEv ∷ bEv ∷ []} {a = cEv} qi-trace qi-fail

------------------------------------------------------------------------------------
-- §B.2  fix-L1 : RQ ≈DR L1 — RQ SOLVES `resettable`'s defining equation.
--
-- `L1 = Q △ (lightning ⟶₀ RQ)` is Roscoe's right-hand side with RQ standing in for
-- the recursive occurrence; this section proves that what the handler restarts (RQ) is
-- behaviourally the whole of `L1`, i.e. that `L1` really is a solution of
-- `X = Q /\ lightning -> X` and RQ is that solution.  Both processes are τ-free (the
-- interrupt offers only `lightning`, which Q never offers, so `△-merge`'s both-offer
-- rule — the sole source of τ in an interrupt of stable operands — never fires), so
-- the bisimulation is built from single visible steps only.
------------------------------------------------------------------------------------

open import Semantics.Stability {E = REv} {I = ExtI REv} using (nothing≢just)
open import Semantics.WeakBisim {E = REv} {I = ExtI REv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.DRBisim   {E = REv} {I = ExtI REv} using (_≈DR_)
open import Semantics.BisimFromRel {E = REv} {I = ExtI REv} using (module DRFromRel)

-- the τ-branch map of an interrupt whose two operands are τ-free `react` nodes is
-- everywhere `nothing`: every tag of `△-τ` reads one operand's (empty) τ-part
△-τ-∅ : ∀ {vP vQ : (at : AnyTypes REv) → ContinueType at (Maybe RProc)} {P Q : RProc}
        (i : AnyTypes (ExtI REv)) (x : proj₁ i)
      → △-τ (react vP ∅t) (react vQ ∅t) P Q i x ≡ nothing
△-τ-∅ (_ , base _)            x = refl
△-τ-∅ (_ , fin)               x = refl
△-τ-∅ (_ , pair (base _) _)   x = refl
△-τ-∅ (_ , pair (pair _ _) _) x = refl
△-τ-∅ (_ , pair fin _) (lift fzero               , y) = refl
△-τ-∅ (_ , pair fin _) (lift (fsuc fzero)        , y) = refl
△-τ-∅ (_ , pair fin _) (lift (fsuc (fsuc _))     , y) = refl

-- the three states of `L1`: Qₓ interrupted by the (fixed) lightning handler
S1 S2 S3 : RProc
S1 = Qa △ Hr
S2 = Qb △ Hr
S3 = Qc △ Hr

-- no state of L1 has a τ (both operands are τ-free reacts ⇒ △-τ-∅)
s1-noτ : ∀ {t} → ¬ (S1 L.─[ L.τ ]─► t)
s1-noτ (L.sSil ())
s1-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = Qa} {Q = Hr} i x)) br)

s2-noτ : ∀ {t} → ¬ (S2 L.─[ L.τ ]─► t)
s2-noτ (L.sSil ())
s2-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = Qb} {Q = Hr} i x)) br)

s3-noτ : ∀ {t} → ¬ (S3 L.─[ L.τ ]─► t)
s3-noτ (L.sSil ())
s3-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = Qc} {Q = Hr} i x)) br)

-- neither has any RQ state (their τ-part is literally ∅t)
rqa-noτ : ∀ {t} → ¬ (RQa L.─[ L.τ ]─► t)
rqa-noτ (L.sSil ())
rqa-noτ (L.sTau refl br) = case br of λ ()

rqb-noτ : ∀ {t} → ¬ (RQb L.─[ L.τ ]─► t)
rqb-noτ (L.sSil ())
rqb-noτ (L.sTau refl br) = case br of λ ()

rqc-noτ : ∀ {t} → ¬ (RQc L.─[ L.τ ]─► t)
rqc-noτ (L.sSil ())
rqc-noτ (L.sTau refl br) = case br of λ ()

-- visible-step inversion for the L1 states: `a`/`b`/`c` continues Q (wrapped in the
-- same interrupt), `lightning` fires the interrupt and restarts RQ
s1-ev : ∀ {l t} → S1 L.─[ L.ev l ]─► t
      → ((l ≡ aEv) × (t ≡ S2)) ⊎ ((l ≡ lEv) × (t ≡ RQ))
s1-ev (L.sRet ())
s1-ev (L.sVis {at = _ , a}         refl refl) = inj₁ (refl , refl)
s1-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
s1-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()
s1-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

s2-ev : ∀ {l t} → S2 L.─[ L.ev l ]─► t
      → ((l ≡ bEv) × (t ≡ S3)) ⊎ ((l ≡ lEv) × (t ≡ RQ))
s2-ev (L.sRet ())
s2-ev (L.sVis {at = _ , b}         refl refl) = inj₁ (refl , refl)
s2-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
s2-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
s2-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

s3-ev : ∀ {l t} → S3 L.─[ L.ev l ]─► t
      → ((l ≡ cEv) × (t ≡ S1)) ⊎ ((l ≡ lEv) × (t ≡ RQ))
s3-ev (L.sRet ())
s3-ev (L.sVis {at = _ , c}         refl refl) = inj₁ (refl , refl)
s3-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
s3-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
s3-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()

-- …and for the RQ states
rqa-ev : ∀ {l t} → RQa L.─[ L.ev l ]─► t
       → ((l ≡ aEv) × (t ≡ RQb)) ⊎ ((l ≡ lEv) × (t ≡ RQa))
rqa-ev (L.sRet ())
rqa-ev (L.sVis {at = _ , a}         refl refl) = inj₁ (refl , refl)
rqa-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
rqa-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()
rqa-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

rqb-ev : ∀ {l t} → RQb L.─[ L.ev l ]─► t
       → ((l ≡ bEv) × (t ≡ RQc)) ⊎ ((l ≡ lEv) × (t ≡ RQa))
rqb-ev (L.sRet ())
rqb-ev (L.sVis {at = _ , b}         refl refl) = inj₁ (refl , refl)
rqb-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
rqb-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
rqb-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

rqc-ev : ∀ {l t} → RQc L.─[ L.ev l ]─► t
       → ((l ≡ cEv) × (t ≡ RQa)) ⊎ ((l ≡ lEv) × (t ≡ RQa))
rqc-ev (L.sRet ())
rqc-ev (L.sVis {at = _ , c}         refl refl) = inj₁ (refl , refl)
rqc-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
rqc-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
rqc-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()

-- the visible steps of the L1 states (constructions, the duals of the inversions above)
s1-a : S1 L.─[ L.ev aEv ]─► S2
s1-a = L.sVis {at = ⊤ , a} refl refl

s1-l : S1 L.─[ L.ev lEv ]─► RQ
s1-l = L.sVis {at = ⊤ , lightning} refl refl

s2-b : S2 L.─[ L.ev bEv ]─► S3
s2-b = L.sVis {at = ⊤ , b} refl refl

s2-l : S2 L.─[ L.ev lEv ]─► RQ
s2-l = L.sVis {at = ⊤ , lightning} refl refl

s3-c : S3 L.─[ L.ev cEv ]─► S1
s3-c = L.sVis {at = ⊤ , c} refl refl

s3-l : S3 L.─[ L.ev lEv ]─► RQ
s3-l = L.sVis {at = ⊤ , lightning} refl refl

-- …and of the RQ states
rqa-a : RQa L.─[ L.ev aEv ]─► RQb
rqa-a = L.sVis {at = ⊤ , a} refl refl

rqa-l : RQa L.─[ L.ev lEv ]─► RQa
rqa-l = L.sVis {at = ⊤ , lightning} refl refl

rqb-b : RQb L.─[ L.ev bEv ]─► RQc
rqb-b = L.sVis {at = ⊤ , b} refl refl

rqb-l : RQb L.─[ L.ev lEv ]─► RQa
rqb-l = L.sVis {at = ⊤ , lightning} refl refl

rqc-c : RQc L.─[ L.ev cEv ]─► RQa
rqc-c = L.sVis {at = ⊤ , c} refl refl

rqc-l : RQc L.─[ L.ev lEv ]─► RQa
rqc-l = L.sVis {at = ⊤ , lightning} refl refl

-- the bisimulation relation: RQₓ against the matching L1 state, plus the diagonal on
-- the RQ states (which is where BOTH sides land after a `lightning`, since L1's
-- handler restarts RQ while RQ's own `lightning` loops back to RQ)
data RelL : RProc → RProc → Set₁ where
  rL1 : RelL RQa S1
  rL2 : RelL RQb S2
  rL3 : RelL RQc S3
  rD1 : RelL RQa RQa
  rD2 : RelL RQb RQb
  rD3 : RelL RQc RQc

-- forward: every visible step of the RQ side is matched on the L1 side
relL-fwdE : ∀ {p q} {l : L.Event√ (⊤poly {lzero})} {p′} → RelL p q → p L.─[ L.ev l ]─► p′
          → Σ[ q′ ∈ RProc ] ((q ═[ L.ev l ]═► q′) × RelL p′ q′)
relL-fwdE rL1 stp with rqa-ev stp
... | inj₁ (refl , refl) = S2  , wev τ*-refl s1-a  τ*-refl , rL2
... | inj₂ (refl , refl) = RQa , wev τ*-refl s1-l  τ*-refl , rD1
relL-fwdE rL2 stp with rqb-ev stp
... | inj₁ (refl , refl) = S3  , wev τ*-refl s2-b  τ*-refl , rL3
... | inj₂ (refl , refl) = RQa , wev τ*-refl s2-l  τ*-refl , rD1
relL-fwdE rL3 stp with rqc-ev stp
... | inj₁ (refl , refl) = S1  , wev τ*-refl s3-c  τ*-refl , rL1
... | inj₂ (refl , refl) = RQa , wev τ*-refl s3-l  τ*-refl , rD1
relL-fwdE rD1 stp with rqa-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , rD2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , rD1
relL-fwdE rD2 stp with rqb-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , rD3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , rD1
relL-fwdE rD3 stp with rqc-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , rD1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , rD1

-- backward: every visible step of the L1 side is matched on the RQ side
relL-bwdE : ∀ {p q} {l : L.Event√ (⊤poly {lzero})} {q′} → RelL p q → q L.─[ L.ev l ]─► q′
          → Σ[ p′ ∈ RProc ] ((p ═[ L.ev l ]═► p′) × RelL p′ q′)
relL-bwdE rL1 stp with s1-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , rL2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , rD1
relL-bwdE rL2 stp with s2-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , rL3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , rD1
relL-bwdE rL3 stp with s3-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , rL1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , rD1
relL-bwdE rD1 stp with rqa-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , rD2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , rD1
relL-bwdE rD2 stp with rqb-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , rD3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , rD1
relL-bwdE rD3 stp with rqc-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , rD1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , rD1

-- no related state on either side has a τ, so the two τ-obligations are vacuous…
relL-fwdT : ∀ {p q p′} → RelL p q → p L.─[ L.τ ]─► p′
          → Σ[ q′ ∈ RProc ] ((q ═[ L.τ ]═► q′) × RelL p′ q′)
relL-fwdT rL1 stp = ⊥-elim (rqa-noτ stp)
relL-fwdT rL2 stp = ⊥-elim (rqb-noτ stp)
relL-fwdT rL3 stp = ⊥-elim (rqc-noτ stp)
relL-fwdT rD1 stp = ⊥-elim (rqa-noτ stp)
relL-fwdT rD2 stp = ⊥-elim (rqb-noτ stp)
relL-fwdT rD3 stp = ⊥-elim (rqc-noτ stp)

relL-bwdT : ∀ {p q q′} → RelL p q → q L.─[ L.τ ]─► q′
          → Σ[ p′ ∈ RProc ] ((p ═[ L.τ ]═► p′) × RelL p′ q′)
relL-bwdT rL1 stp = ⊥-elim (s1-noτ stp)
relL-bwdT rL2 stp = ⊥-elim (s2-noτ stp)
relL-bwdT rL3 stp = ⊥-elim (s3-noτ stp)
relL-bwdT rD1 stp = ⊥-elim (rqa-noτ stp)
relL-bwdT rD2 stp = ⊥-elim (rqb-noτ stp)
relL-bwdT rD3 stp = ⊥-elim (rqc-noτ stp)

-- …and so are the two divergence obligations (a divergence starts with a τ)
relL-ndivL : ∀ {p q} → RelL p q → L.Diverges p → ⊥
relL-ndivL rL1 d = rqa-noτ (d .L.Diverges.step)
relL-ndivL rL2 d = rqb-noτ (d .L.Diverges.step)
relL-ndivL rL3 d = rqc-noτ (d .L.Diverges.step)
relL-ndivL rD1 d = rqa-noτ (d .L.Diverges.step)
relL-ndivL rD2 d = rqb-noτ (d .L.Diverges.step)
relL-ndivL rD3 d = rqc-noτ (d .L.Diverges.step)

relL-ndivR : ∀ {p q} → RelL p q → L.Diverges q → ⊥
relL-ndivR rL1 d = s1-noτ  (d .L.Diverges.step)
relL-ndivR rL2 d = s2-noτ  (d .L.Diverges.step)
relL-ndivR rL3 d = s3-noτ  (d .L.Diverges.step)
relL-ndivR rD1 d = rqa-noτ (d .L.Diverges.step)
relL-ndivR rD2 d = rqb-noτ (d .L.Diverges.step)
relL-ndivR rD3 d = rqc-noτ (d .L.Diverges.step)

-- the relation is a divergence-respecting weak bisimulation
module FixL1 = DRFromRel RelL relL-fwdE relL-fwdT relL-bwdE relL-bwdT relL-ndivL relL-ndivR

-- THE FIXPOINT CERTIFICATE: what L1's lightning handler restarts (RQ) is
-- behaviourally the whole of L1, i.e. L1 = Q /\ (lightning -> L1) up to ≈DR, which is
-- exactly Roscoe's `resettable(Q) = Q /\ lightning -> resettable(Q)`
fix-L1 : RQ ≈DR L1
fix-L1 = FixL1.rel→dr rL1

-- the same certificate the other way round
fix-L1′ : L1 ≈DR RQ
fix-L1′ = FixL1.rel→rd rL1

------------------------------------------------------------------------------------
-- §B.3  assert resettable(Q) [FD= RQ — TRUE.
--
-- Immediate from §B.2: RQ and `resettable(Q)` are divergence-respectingly weakly
-- bisimilar, and ≈DR is contained in FD-equivalence.  (The refinement holds in both
-- directions; FDR's assertion is the left-to-right one, with the spec on the left as
-- in `Spec [FD= Impl`.)
------------------------------------------------------------------------------------

open import Semantics.DRImpliesFD {E = REv} {I = ExtI REv} using (drbisim→⊑FD)
import Semantics.FailuresDivergences {E = REv} {I = ExtI REv} as FD

-- assert resettable(Q) [FD= RQ
L1-refines-RQ : L1 FD.⊑FD RQ
L1-refines-RQ = drbisim→⊑FD fix-L1′

-- …and the converse, so the two are FD-equivalent (RQ is a faithful unrolling)
RQ-refines-L1 : RQ FD.⊑FD L1
RQ-refines-L1 = drbisim→⊑FD fix-L1

------------------------------------------------------------------------------------
-- §B.4  assert resettable(Q) :[deterministic] — TRUE.
--
-- `lightning` is disjoint from Q's alphabet {a,b,c}, so `△-merge`'s both-offer rule —
-- the only way an interrupt can introduce nondeterminism — never fires: every state
-- reachable from L1 is τ-FREE and its visible offer map is a partial FUNCTION of the
-- event.  Hence the state reached by a visible run over `s` is UNIQUE, so if `s ∷ʳ a`
-- is a trace then the state reached by `s` OFFERS `a` and cannot stably REFUSE it.
-- Same shape as `CSP/Examples/UCS/Ch5/Renaming.agda`'s `split-det`; trace + failures
-- level only, NO FailuresDivergences and NO postulate.
------------------------------------------------------------------------------------

-- the states reachable from L1: the three interrupt states, and the three RQ states
-- the handler restarts into
data ReachL : RProc → Set₁ where
  rc-s1 : ReachL S1
  rc-s2 : ReachL S2
  rc-s3 : ReachL S3
  rc-r1 : ReachL RQa
  rc-r2 : ReachL RQb
  rc-r3 : ReachL RQc

-- no reachable state has a τ
reachL-noτ : ∀ {P t} → ReachL P → P L.─[ L.τ ]─► t → ⊥
reachL-noτ rc-s1 st = s1-noτ  st
reachL-noτ rc-s2 st = s2-noτ  st
reachL-noτ rc-s3 st = s3-noτ  st
reachL-noτ rc-r1 st = rqa-noτ st
reachL-noτ rc-r2 st = rqb-noτ st
reachL-noτ rc-r3 st = rqc-noτ st

-- no reachable state terminates (every one of them forces to a `react`)
reachL-no√ : ∀ {P r t} → ReachL P → P L.─[ L.ev (L.√ r) ]─► t → ⊥
reachL-no√ rc-s1 (L.sRet ())
reachL-no√ rc-s2 (L.sRet ())
reachL-no√ rc-s3 (L.sRet ())
reachL-no√ rc-r1 (L.sRet ())
reachL-no√ rc-r2 (L.sRet ())
reachL-no√ rc-r3 (L.sRet ())

-- the target of a visible step from a reachable state is again reachable
reachL-step : ∀ {P e q} → ReachL P → P L.─[ L.ev e ]─► q → ReachL q
reachL-step rc-s1 stp with s1-ev stp
... | inj₁ (refl , refl) = rc-s2
... | inj₂ (refl , refl) = rc-r1
reachL-step rc-s2 stp with s2-ev stp
... | inj₁ (refl , refl) = rc-s3
... | inj₂ (refl , refl) = rc-r1
reachL-step rc-s3 stp with s3-ev stp
... | inj₁ (refl , refl) = rc-s1
... | inj₂ (refl , refl) = rc-r1
reachL-step rc-r1 stp with rqa-ev stp
... | inj₁ (refl , refl) = rc-r2
... | inj₂ (refl , refl) = rc-r1
reachL-step rc-r2 stp with rqb-ev stp
... | inj₁ (refl , refl) = rc-r3
... | inj₂ (refl , refl) = rc-r1
reachL-step rc-r3 stp with rqc-ev stp
... | inj₁ (refl , refl) = rc-r1
... | inj₂ (refl , refl) = rc-r1

-- FUNCTIONAL offer: same source, same visible event ⇒ same target (react injectivity)
offer-fun : ∀ {A e x} {q1 q2 P : RProc}
          → P L.─[ L.ev (L.evl (L.evLabel A e x)) ]─► q1
          → P L.─[ L.ev (L.evl (L.evLabel A e x)) ]─► q2
          → q1 ≡ q2
offer-fun st1 st2 with L.ev-inv st1 | L.ev-inv st2
... | v , τc , eq1 , br1 | v′ , τc′ , eq2 , br2 with trans (sym eq1) eq2
...   | refl = just-injective (trans (sym br1) br2)

-- a single visible step from a reachable state is deterministic (√ is ruled out)
stepL-det : ∀ {e} {q1 q2 P : RProc} → ReachL P
          → P L.─[ L.ev e ]─► q1 → P L.─[ L.ev e ]─► q2 → q1 ≡ q2
stepL-det {e = L.evl x} r st1 st2 = offer-fun st1 st2
stepL-det {e = L.√ r′}  r st1 st2 = ⊥-elim (reachL-no√ r st1)

-- REACHED-STATE DETERMINACY: the state reached by a visible run over `s` is unique
-- (every run out of a reachable state is τ-free, and each visible step is functional)
detL : ∀ {P s P′ P″} → ReachL P → P F.⟹⟨ s ⟩ P′ → P F.⟹⟨ s ⟩ P″ → P′ ≡ P″
detL r F.⟹-refl            F.⟹-refl              = refl
detL r F.⟹-refl            (F.⟹-τ step _)        = ⊥-elim (reachL-noτ r step)
detL r (F.⟹-τ step _)      _                      = ⊥-elim (reachL-noτ r step)
detL r (F.⟹-ev step1 _)    (F.⟹-τ step _)        = ⊥-elim (reachL-noτ r step)
detL r (F.⟹-ev step1 rest1) (F.⟹-ev step2 rest2) =
  detL (reachL-step r step1) rest1
       (subst (λ z → z F.⟹⟨ _ ⟩ _) (sym (stepL-det r step1 step2)) rest2)

-- snoc-decomposition: a run over `s ∷ʳ a` factors as a run over `s` reaching a state
-- that OFFERS `a` (τ-free, so there is no leading τ before the final event)
snocL-split : ∀ {e : L.Event√ (⊤poly {lzero})} {P P₀ : RProc} {s}
            → ReachL P → P F.⟹⟨ s ∷ʳ e ⟩ P₀
            → Σ[ P″ ∈ RProc ] (P F.⟹⟨ s ⟩ P″ × Rf.Offers P″ e)
snocL-split {s = []}     r (F.⟹-τ step _)    = ⊥-elim (reachL-noτ r step)
snocL-split {s = []}     r (F.⟹-ev step _)    = _ , F.⟹-refl , (_ , step)
snocL-split {s = x ∷ s′} r (F.⟹-τ step _)    = ⊥-elim (reachL-noτ r step)
snocL-split {s = x ∷ s′} r (F.⟹-ev step rest) with snocL-split (reachL-step r step) rest
... | P″ , run , off = P″ , F.⟹-ev step run , off

-- assert resettable(Q) :[deterministic] — the state reached by `s` uniquely offers `a`
L1-det : D.Deterministic L1
L1-det {s} {a = e} (P₀ , run) (P′ , runP′ , _ , refP′) with snocL-split {s = s} rc-s1 run
... | P″ , runP″ , offP″ =
      refP′ e refl (subst (λ z → Rf.Offers z e) (sym (detL rc-s1 runP′ runP″)) offP″)

------------------------------------------------------------------------------------
-- §B.5  fix-L2 : RQ ≈DR L2 — RQ also solves the SECOND level's defining equation.
--
--   L2 = L1 △ (lightning ⟶₀ RQ)   is  resettable(resettable(Q))'s right-hand side.
--
-- The recursion `X = L1 /\ lightning -> X` is GUARDED (its recursive occurrence sits
-- under a prefix), so it has a unique solution in the FD model; this section exhibits
-- RQ as a solution, which identifies it.  Nothing from §B.2/§B.3 is assumed — the
-- bisimulation is verified against the term `L1 △ (lightning ⟶₀ RQ)` exactly as
-- written — so choosing RQ for the witness begs no question; it is the ordinary
-- "guess the fixpoint and verify" argument, and it is what makes §B.6 possible.
--
-- Unlike level 1, level 2 DOES exercise `△-merge`'s both-offer rule: `lightning` is
-- now offered by the inner interrupt as well as by the outer handler, so after a
-- `lightning` the process is the internal choice `M = (RQ △ Hr) ⊓ RQ`.  Its two
-- τ-branches lead to `RQ △ Hr` and to `RQ`, which are themselves DR-equal to RQ, so
-- the extra nondeterminism is only apparent — which is exactly why `resettable` is
-- idempotent, and why this bisimulation is weak where §B.2's was in effect strong.
------------------------------------------------------------------------------------

open import Semantics.DRBisim {E = REv} {I = ExtI REv} using (drbisim-trans; drbisim-sym)

-- resettable(resettable(Q)), with RQ as the witness for the recursive occurrence
L2 : RProc
L2 = L1 △ Hr

-- L2's three "inner Q still running" states…
U1 U2 U3 : RProc
U1 = S1 △ Hr
U2 = S2 △ Hr
U3 = S3 △ Hr

-- …its three "inner Q has been reset" states, reached once the inner interrupt fired…
V1 V2 V3 : RProc
V1 = RQa △ Hr
V2 = RQb △ Hr
V3 = RQc △ Hr

-- …and the internal choice the both-offer rule builds out of a `lightning`: either the
-- inner interrupt fired (leaving RQ inside the outer interrupt) or the outer one did
-- (leaving RQ alone)
M : RProc
M = ptree (react ∅v (△-br2 RQ Hr RQ))

-- the lightning handler has no τ of its own (it is a plain prefix)
hr-noτ : ∀ {t} → ¬ (Hr L.─[ L.τ ]─► t)
hr-noτ (L.sSil ())
hr-noτ (L.sTau refl br) = case br of λ ()

-- inversion of an interrupt's τ-branch map: a `just M` out of `△-τ` is one of the two
-- operands' own τ-moves.  Reused from the shared trace-laws module, instantiated at
-- this example's `REv-≟` (so its `_△_`/`△-τ` are literally the ones used here).
open import CSP.Laws.Traces.TraceLawsThrowInterrupt REv-≟ using (△-τ-source)

-- the U states are interrupts of two τ-free operands, hence τ-free themselves.  Their
-- inner operand is ITSELF an interrupt, so its τ-part is a `△-τ` rather than the
-- literal `∅t` and §B.2's `△-τ-∅` does not apply — the inversion above is used instead.
u1-noτ : ∀ {t} → ¬ (U1 L.─[ L.τ ]─► t)
u1-noτ (L.sSil ())
u1-noτ (L.sTau {i = i} {a = x} refl br)
  with △-τ-source (force S1) (force Hr) S1 Hr {i = i} {a = x} br
... | inj₁ (j , y , _ , veq , _) =
      nothing≢just (trans (sym (△-τ-∅ {P = Qa} {Q = Hr} j y)) veq)
... | inj₂ (_ , _ , _ , veq , _) = case veq of λ ()

u2-noτ : ∀ {t} → ¬ (U2 L.─[ L.τ ]─► t)
u2-noτ (L.sSil ())
u2-noτ (L.sTau {i = i} {a = x} refl br)
  with △-τ-source (force S2) (force Hr) S2 Hr {i = i} {a = x} br
... | inj₁ (j , y , _ , veq , _) =
      nothing≢just (trans (sym (△-τ-∅ {P = Qb} {Q = Hr} j y)) veq)
... | inj₂ (_ , _ , _ , veq , _) = case veq of λ ()

u3-noτ : ∀ {t} → ¬ (U3 L.─[ L.τ ]─► t)
u3-noτ (L.sSil ())
u3-noτ (L.sTau {i = i} {a = x} refl br)
  with △-τ-source (force S3) (force Hr) S3 Hr {i = i} {a = x} br
... | inj₁ (j , y , _ , veq , _) =
      nothing≢just (trans (sym (△-τ-∅ {P = Qc} {Q = Hr} j y)) veq)
... | inj₂ (_ , _ , _ , veq , _) = case veq of λ ()

-- the V states are interrupts of two literally τ-free reacts, so §B.2's lemma applies
v1-noτ : ∀ {t} → ¬ (V1 L.─[ L.τ ]─► t)
v1-noτ (L.sSil ())
v1-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = RQa} {Q = Hr} i x)) br)

v2-noτ : ∀ {t} → ¬ (V2 L.─[ L.τ ]─► t)
v2-noτ (L.sSil ())
v2-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = RQb} {Q = Hr} i x)) br)

v3-noτ : ∀ {t} → ¬ (V3 L.─[ L.τ ]─► t)
v3-noτ (L.sSil ())
v3-noτ (L.sTau {i = i} {a = x} refl br) =
  nothing≢just (trans (sym (△-τ-∅ {P = RQc} {Q = Hr} i x)) br)

-- M offers nothing visible (the both-offer node's visible map is ∅v)…
m-noev : ∀ {l t} → ¬ (M L.─[ L.ev l ]─► t)
m-noev (L.sRet ())
m-noev (L.sVis refl br) = case br of λ ()

-- …and its two τ's go to `RQ △ Hr` (the inner interrupt fired) and to `RQ` (the outer
-- one fired)
m-τ : ∀ {t} → M L.─[ L.τ ]─► t → (t ≡ V1) ⊎ (t ≡ RQ)
m-τ (L.sSil ())
m-τ (L.sTau {i = _ , base _}   refl br) = case br of λ ()
m-τ (L.sTau {i = _ , pair _ _} refl br) = case br of λ ()
m-τ (L.sTau {i = _ , fin} {a = lift fzero}               refl refl) = inj₁ refl
m-τ (L.sTau {i = _ , fin} {a = lift (fsuc fzero)}        refl refl) = inj₂ refl
m-τ (L.sTau {i = _ , fin} {a = lift (fsuc (fsuc _))}     refl br)   = case br of λ ()

-- the two τ-branches of M, as constructions
m-τ-V : M L.─[ L.τ ]─► V1
m-τ-V = L.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

m-τ-RQ : M L.─[ L.τ ]─► RQ
m-τ-RQ = L.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

-- visible-step inversion for L2's states: an event of the inner Q continues inside
-- BOTH interrupts, a `lightning` lands in the internal choice M
u1-ev : ∀ {l t} → U1 L.─[ L.ev l ]─► t
      → ((l ≡ aEv) × (t ≡ U2)) ⊎ ((l ≡ lEv) × (t ≡ M))
u1-ev (L.sRet ())
u1-ev (L.sVis {at = _ , a}         refl refl) = inj₁ (refl , refl)
u1-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
u1-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()
u1-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

u2-ev : ∀ {l t} → U2 L.─[ L.ev l ]─► t
      → ((l ≡ bEv) × (t ≡ U3)) ⊎ ((l ≡ lEv) × (t ≡ M))
u2-ev (L.sRet ())
u2-ev (L.sVis {at = _ , b}         refl refl) = inj₁ (refl , refl)
u2-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
u2-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
u2-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

u3-ev : ∀ {l t} → U3 L.─[ L.ev l ]─► t
      → ((l ≡ cEv) × (t ≡ U1)) ⊎ ((l ≡ lEv) × (t ≡ M))
u3-ev (L.sRet ())
u3-ev (L.sVis {at = _ , c}         refl refl) = inj₁ (refl , refl)
u3-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
u3-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
u3-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()

v1-ev : ∀ {l t} → V1 L.─[ L.ev l ]─► t
      → ((l ≡ aEv) × (t ≡ V2)) ⊎ ((l ≡ lEv) × (t ≡ M))
v1-ev (L.sRet ())
v1-ev (L.sVis {at = _ , a}         refl refl) = inj₁ (refl , refl)
v1-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
v1-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()
v1-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

v2-ev : ∀ {l t} → V2 L.─[ L.ev l ]─► t
      → ((l ≡ bEv) × (t ≡ V3)) ⊎ ((l ≡ lEv) × (t ≡ M))
v2-ev (L.sRet ())
v2-ev (L.sVis {at = _ , b}         refl refl) = inj₁ (refl , refl)
v2-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
v2-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
v2-ev (L.sVis {at = _ , c}         refl br)   = case br of λ ()

v3-ev : ∀ {l t} → V3 L.─[ L.ev l ]─► t
      → ((l ≡ cEv) × (t ≡ V1)) ⊎ ((l ≡ lEv) × (t ≡ M))
v3-ev (L.sRet ())
v3-ev (L.sVis {at = _ , c}         refl refl) = inj₁ (refl , refl)
v3-ev (L.sVis {at = _ , lightning} refl refl) = inj₂ (refl , refl)
v3-ev (L.sVis {at = _ , a}         refl br)   = case br of λ ()
v3-ev (L.sVis {at = _ , b}         refl br)   = case br of λ ()

-- the visible steps of L2's states, as constructions
u1-a : U1 L.─[ L.ev aEv ]─► U2
u1-a = L.sVis {at = ⊤ , a} refl refl

u1-l : U1 L.─[ L.ev lEv ]─► M
u1-l = L.sVis {at = ⊤ , lightning} refl refl

u2-b : U2 L.─[ L.ev bEv ]─► U3
u2-b = L.sVis {at = ⊤ , b} refl refl

u2-l : U2 L.─[ L.ev lEv ]─► M
u2-l = L.sVis {at = ⊤ , lightning} refl refl

u3-c : U3 L.─[ L.ev cEv ]─► U1
u3-c = L.sVis {at = ⊤ , c} refl refl

u3-l : U3 L.─[ L.ev lEv ]─► M
u3-l = L.sVis {at = ⊤ , lightning} refl refl

v1-a : V1 L.─[ L.ev aEv ]─► V2
v1-a = L.sVis {at = ⊤ , a} refl refl

v1-l : V1 L.─[ L.ev lEv ]─► M
v1-l = L.sVis {at = ⊤ , lightning} refl refl

v2-b : V2 L.─[ L.ev bEv ]─► V3
v2-b = L.sVis {at = ⊤ , b} refl refl

v2-l : V2 L.─[ L.ev lEv ]─► M
v2-l = L.sVis {at = ⊤ , lightning} refl refl

v3-c : V3 L.─[ L.ev cEv ]─► V1
v3-c = L.sVis {at = ⊤ , c} refl refl

v3-l : V3 L.─[ L.ev lEv ]─► M
v3-l = L.sVis {at = ⊤ , lightning} refl refl

-- a divergence, exposed as its first τ-step plus the divergence that follows (a record
-- projection cannot be unified against, so the step cannot be case-split on in place)
div-step : ∀ {P : RProc} → L.Diverges P
         → Σ[ t ∈ RProc ] ((P L.─[ L.τ ]─► t) × L.Diverges t)
div-step d = _ , d .L.Diverges.step , d .L.Diverges.rest

-- M does not diverge: both its τ's land on a τ-free state
m-noDiv : ¬ L.Diverges M
m-noDiv d with div-step d
... | _ , st , d′ with m-τ st
...   | inj₁ refl = v1-noτ  (d′ .L.Diverges.step)
...   | inj₂ refl = rqa-noτ (d′ .L.Diverges.step)

-- the level-2 bisimulation relation: RQ against each of L2's states, plus the diagonal
-- on the RQ states (reached on the "outer interrupt fired" τ-branch of M)
data RelI : RProc → RProc → Set₁ where
  iU1 : RelI RQa U1
  iU2 : RelI RQb U2
  iU3 : RelI RQc U3
  iM  : RelI RQa M
  iV1 : RelI RQa V1
  iV2 : RelI RQb V2
  iV3 : RelI RQc V3
  iD1 : RelI RQa RQa
  iD2 : RelI RQb RQb
  iD3 : RelI RQc RQc

-- forward: RQ's visible steps are matched by L2, WEAKLY — from M the match needs the
-- leading τ that resolves the internal choice
relI-fwdE : ∀ {p q} {l : L.Event√ (⊤poly {lzero})} {p′} → RelI p q → p L.─[ L.ev l ]─► p′
          → Σ[ q′ ∈ RProc ] ((q ═[ L.ev l ]═► q′) × RelI p′ q′)
relI-fwdE iU1 stp with rqa-ev stp
... | inj₁ (refl , refl) = U2  , wev τ*-refl u1-a  τ*-refl , iU2
... | inj₂ (refl , refl) = M   , wev τ*-refl u1-l  τ*-refl , iM
relI-fwdE iU2 stp with rqb-ev stp
... | inj₁ (refl , refl) = U3  , wev τ*-refl u2-b  τ*-refl , iU3
... | inj₂ (refl , refl) = M   , wev τ*-refl u2-l  τ*-refl , iM
relI-fwdE iU3 stp with rqc-ev stp
... | inj₁ (refl , refl) = U1  , wev τ*-refl u3-c  τ*-refl , iU1
... | inj₂ (refl , refl) = M   , wev τ*-refl u3-l  τ*-refl , iM
relI-fwdE iM stp with rqa-ev stp
... | inj₁ (refl , refl) = V2  , wev (τ*-step m-τ-V τ*-refl) v1-a τ*-refl , iV2
... | inj₂ (refl , refl) = M   , wev (τ*-step m-τ-V τ*-refl) v1-l τ*-refl , iM
relI-fwdE iV1 stp with rqa-ev stp
... | inj₁ (refl , refl) = V2  , wev τ*-refl v1-a  τ*-refl , iV2
... | inj₂ (refl , refl) = M   , wev τ*-refl v1-l  τ*-refl , iM
relI-fwdE iV2 stp with rqb-ev stp
... | inj₁ (refl , refl) = V3  , wev τ*-refl v2-b  τ*-refl , iV3
... | inj₂ (refl , refl) = M   , wev τ*-refl v2-l  τ*-refl , iM
relI-fwdE iV3 stp with rqc-ev stp
... | inj₁ (refl , refl) = V1  , wev τ*-refl v3-c  τ*-refl , iV1
... | inj₂ (refl , refl) = M   , wev τ*-refl v3-l  τ*-refl , iM
relI-fwdE iD1 stp with rqa-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , iD2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , iD1
relI-fwdE iD2 stp with rqb-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , iD3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , iD1
relI-fwdE iD3 stp with rqc-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , iD1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , iD1

-- backward: L2's visible steps are matched by RQ (M has no visible step at all)
relI-bwdE : ∀ {p q} {l : L.Event√ (⊤poly {lzero})} {q′} → RelI p q → q L.─[ L.ev l ]─► q′
          → Σ[ p′ ∈ RProc ] ((p ═[ L.ev l ]═► p′) × RelI p′ q′)
relI-bwdE iU1 stp with u1-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , iU2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , iM
relI-bwdE iU2 stp with u2-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , iU3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , iM
relI-bwdE iU3 stp with u3-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , iU1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , iM
relI-bwdE iM stp = ⊥-elim (m-noev stp)
relI-bwdE iV1 stp with v1-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , iV2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , iM
relI-bwdE iV2 stp with v2-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , iV3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , iM
relI-bwdE iV3 stp with v3-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , iV1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , iM
relI-bwdE iD1 stp with rqa-ev stp
... | inj₁ (refl , refl) = RQb , wev τ*-refl rqa-a τ*-refl , iD2
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqa-l τ*-refl , iD1
relI-bwdE iD2 stp with rqb-ev stp
... | inj₁ (refl , refl) = RQc , wev τ*-refl rqb-b τ*-refl , iD3
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqb-l τ*-refl , iD1
relI-bwdE iD3 stp with rqc-ev stp
... | inj₁ (refl , refl) = RQa , wev τ*-refl rqc-c τ*-refl , iD1
... | inj₂ (refl , refl) = RQa , wev τ*-refl rqc-l τ*-refl , iD1

-- RQ never has a τ, so the forward τ-obligation is vacuous
relI-fwdT : ∀ {p q p′} → RelI p q → p L.─[ L.τ ]─► p′
          → Σ[ q′ ∈ RProc ] ((q ═[ L.τ ]═► q′) × RelI p′ q′)
relI-fwdT iU1 stp = ⊥-elim (rqa-noτ stp)
relI-fwdT iU2 stp = ⊥-elim (rqb-noτ stp)
relI-fwdT iU3 stp = ⊥-elim (rqc-noτ stp)
relI-fwdT iM  stp = ⊥-elim (rqa-noτ stp)
relI-fwdT iV1 stp = ⊥-elim (rqa-noτ stp)
relI-fwdT iV2 stp = ⊥-elim (rqb-noτ stp)
relI-fwdT iV3 stp = ⊥-elim (rqc-noτ stp)
relI-fwdT iD1 stp = ⊥-elim (rqa-noτ stp)
relI-fwdT iD2 stp = ⊥-elim (rqb-noτ stp)
relI-fwdT iD3 stp = ⊥-elim (rqc-noτ stp)

-- the ONLY substantive τ-obligation: M's internal choice.  RQ matches both branches by
-- standing still — the "inner fired" branch lands on `RQ △ Hr`, the "outer fired" one
-- on RQ itself, and RQ is related to both.  THIS is where the idempotence lives.
relI-bwdT : ∀ {p q q′} → RelI p q → q L.─[ L.τ ]─► q′
          → Σ[ p′ ∈ RProc ] ((p ═[ L.τ ]═► p′) × RelI p′ q′)
relI-bwdT iU1 stp = ⊥-elim (u1-noτ stp)
relI-bwdT iU2 stp = ⊥-elim (u2-noτ stp)
relI-bwdT iU3 stp = ⊥-elim (u3-noτ stp)
relI-bwdT iM  stp with m-τ stp
... | inj₁ refl = RQa , wτ τ*-refl , iV1
... | inj₂ refl = RQa , wτ τ*-refl , iD1
relI-bwdT iV1 stp = ⊥-elim (v1-noτ stp)
relI-bwdT iV2 stp = ⊥-elim (v2-noτ stp)
relI-bwdT iV3 stp = ⊥-elim (v3-noτ stp)
relI-bwdT iD1 stp = ⊥-elim (rqa-noτ stp)
relI-bwdT iD2 stp = ⊥-elim (rqb-noτ stp)
relI-bwdT iD3 stp = ⊥-elim (rqc-noτ stp)

-- neither side diverges: RQ is τ-free, and L2's only τ's are M's two, each landing on
-- a τ-free state
relI-ndivL : ∀ {p q} → RelI p q → L.Diverges p → ⊥
relI-ndivL iU1 d = rqa-noτ (d .L.Diverges.step)
relI-ndivL iU2 d = rqb-noτ (d .L.Diverges.step)
relI-ndivL iU3 d = rqc-noτ (d .L.Diverges.step)
relI-ndivL iM  d = rqa-noτ (d .L.Diverges.step)
relI-ndivL iV1 d = rqa-noτ (d .L.Diverges.step)
relI-ndivL iV2 d = rqb-noτ (d .L.Diverges.step)
relI-ndivL iV3 d = rqc-noτ (d .L.Diverges.step)
relI-ndivL iD1 d = rqa-noτ (d .L.Diverges.step)
relI-ndivL iD2 d = rqb-noτ (d .L.Diverges.step)
relI-ndivL iD3 d = rqc-noτ (d .L.Diverges.step)

relI-ndivR : ∀ {p q} → RelI p q → L.Diverges q → ⊥
relI-ndivR iU1 d = u1-noτ  (d .L.Diverges.step)
relI-ndivR iU2 d = u2-noτ  (d .L.Diverges.step)
relI-ndivR iU3 d = u3-noτ  (d .L.Diverges.step)
relI-ndivR iM  d = m-noDiv d
relI-ndivR iV1 d = v1-noτ  (d .L.Diverges.step)
relI-ndivR iV2 d = v2-noτ  (d .L.Diverges.step)
relI-ndivR iV3 d = v3-noτ  (d .L.Diverges.step)
relI-ndivR iD1 d = rqa-noτ (d .L.Diverges.step)
relI-ndivR iD2 d = rqb-noτ (d .L.Diverges.step)
relI-ndivR iD3 d = rqc-noτ (d .L.Diverges.step)

-- the relation is a divergence-respecting weak bisimulation
module FixL2 = DRFromRel RelI relI-fwdE relI-fwdT relI-bwdE relI-bwdT relI-ndivL relI-ndivR

-- THE LEVEL-2 FIXPOINT CERTIFICATE: RQ solves X = L1 /\ lightning -> X, so
-- L2 = resettable(resettable(Q))
fix-L2 : RQ ≈DR L2
fix-L2 = FixL2.rel→dr iU1

-- …and the same the other way round
fix-L2′ : L2 ≈DR RQ
fix-L2′ = FixL2.rel→rd iU1

------------------------------------------------------------------------------------
-- §B.6  assert resettable(Q) [FD= resettable(resettable(Q)) — TRUE, and its converse
-- — TRUE.  `resettable` is FD-idempotent.
--
-- Both levels are DR-bisimilar to the same RQ (§B.2, §B.5), so they are DR-bisimilar
-- to each other, and ≈DR is contained in FD-equivalence.
------------------------------------------------------------------------------------

-- the two levels are divergence-respectingly weakly bisimilar
L1≈L2 : L1 ≈DR L2
L1≈L2 = drbisim-trans fix-L1′ fix-L2

-- assert resettable(Q) [FD= resettable(resettable(Q))
L1-refines-L2 : L1 FD.⊑FD L2
L1-refines-L2 = drbisim→⊑FD L1≈L2

-- assert resettable(resettable(Q)) [FD= resettable(Q)
L2-refines-L1 : L2 FD.⊑FD L1
L2-refines-L1 = drbisim→⊑FD (drbisim-sym L1≈L2)
