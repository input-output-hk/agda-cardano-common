{-# OPTIONS --guardedness #-}

-- UCS chapter 8: Ranko Lazić's determinism check (lazic.csp, Bill Roscoe; source
-- fdr-examples/ucs/chapter08/lazic.csp).
--
--   channel a,b,c,d          Sigma = {a,b,c,d}          channel clunk
--
--   D   = a -> D [] b -> a -> D'              -- deterministic
--   D'  = c -> D' [] d -> c -> D
--   ND  = a -> ND [] a -> b -> a -> ND        -- nondeterministic (ambiguous a)
--   ND2 = a -> ND2 |~| b -> a -> ND2          -- nondeterministic (internal choice)
--
--   Clunker     = [] x:Sigma @ x -> clunk -> Clunker
--   Clunking(P) = P [|Sigma|] Clunker
--   Repeat      = [] x:Sigma @ x -> x -> Repeat
--   RHS(P)      = ((Clunking(P) [|{clunk}|] Clunking(P)) [|Sigma|] Repeat) \ {clunk}
--   LHS         = STOP |~| ([] x:Sigma @ x -> x -> LHS)
--
--   assert LHS [F= RHS(D)     assert LHS [F= RHS(ND)     assert LHS [F= RHS(ND2)
--
-- Lazić's algorithm reduces "is P deterministic?" to the stable-failures refinement
-- LHS [F= RHS(P).  Two copies of P are run against each other through the
-- clunk-synchronised harness: `Repeat` forces the SAME visible event to be performed
-- twice in a row, once by each copy, and the (hidden) `clunk` keeps the two copies in
-- lockstep, one event apart.  If P can, after the same trace, both accept and refuse
-- some event x, then one copy may perform x while the other cannot follow — the
-- composite deadlocks in mid-pair, i.e. it has a failure (s ⌢ <x>, X) with x ∈ X.
-- LHS has no such failure: after an odd-length trace it MUST still offer the pending
-- event.  (After an even-length trace LHS's STOP branch refuses everything, so the
-- specification constrains only the mid-pair states.)
--
-- §A models the processes, §B proves the six results:
--
--   LHS [F= RHS(D)     TRUE     lazic-D      D is deterministic, so the second copy
--                                            can always follow the first.  Proved by a
--                                            weak simulation with refusal transfer over
--                                            the 26 reachable harness states (`SimR`).
--   LHS [F= RHS(ND)    FALSE    lazic-ND     after <a,a> one copy may sit in `b -> …`
--                                            and the other in `a -> …`; <a,a,b> then
--                                            deadlocks, so RHS(ND) refuses b there.
--   LHS [F= RHS(ND2)   FALSE    lazic-ND2    same, one step earlier: after <> the two
--                                            copies may resolve |~| differently, so
--                                            <a> already deadlocks.
--   Deterministic D                TRUE      D-det
--   Deterministic ND               FALSE     ND-nondet
--   Deterministic ND2              FALSE     ND2-nondet
--
-- §B-cal records the CALIBRATION: on all three subjects the Lazić verdict and the
-- direct `Semantics.Determinism.Deterministic` verdict agree.  That agreement is the
-- point of the port — the three refinement checks on their own are three arbitrary
-- facts.  (The general metatheorem  ∀ P → Deterministic P ↔ LHS ⊑F RHS(P)  is Lazić's
-- theorem proper; Roscoe's file does not assert it and it is NOT attempted here.)
--
-- WHY THIS IS THE ONLY CHAPTER-8 FILE PORTED.  The rest of fdr-examples/ucs/chapter08/
-- is FDR compression material: its asserts are all of the form  Spec [FD= compress(Impl)
-- for compress ∈ {sbisim, diamond, normal, chase, explicate}.  Those functions are
-- SEMANTICS-PRESERVING state-space reductions, so `Spec [FD= compress(Impl)` is
-- literally the same theorem as `Spec [FD= Impl` — they carry no proof obligation in a
-- theorem prover, only a tool-level speed-up (compression09.csp has no asserts at all).
-- lazic.csp is the exception: it is a statement ABOUT the failures model, not about the
-- tool, and its content survives the translation.
--
-- CLASSICAL FOOTPRINT: none.  No postulate, no LEM/`dne` seam, no FSim bridge — this
-- module lands on the same side as CSP.Examples.UCS.Ch6.FailDiv (postulate-free and
-- bridge-free), not on the sanctioned `Hide-fsim`/`αpar-fsim-df` seams that
-- CSP.Examples.UCS.Ch5.NCopyL rides.  Its whole local dependency closure (18 modules:
-- Process_Trees, CSP.Operators, the Semantics LTS/Refusals/Failures/Stability/
-- Determinism layer and the postulate-free CSP.Laws.Traces parallel/hide inversions)
-- carries no `postulate`, no NON_TERMINATING/TERMINATING and no sized types either.
-- No old-style mutual blocks (forward declarations only), no holes.
--
-- GUARDEDNESS NOTE: the recursive processes (D, D', ND, ND2, Clunker, Repeat, LHS) are
-- written as raw `react` nodes with copatterns — the inlined idiom of
-- CSP.Examples.UCS.Ch3.SyncIdentity's REPEAT and of Ch5.Renaming's SPLIT — because a
-- corecursive call underneath the `⟶₀`/`□`/`⊓` operators is not syntactically guarded.
-- Each node's offer map is exactly what the corresponding CSPM term denotes (in
-- particular ND's ambiguous `a` leads to the internal choice `ND ⊓ (b -> a -> ND)`,
-- which is what `□` computes for two same-event prefixes).  The NON-recursive
-- combinators — Clunking and RHS — do use the real CSP operators `Par⊤` and `_∖_`.

module CSP.Examples.UCS.Ch8.Lazic where

open import Level using (Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Process_Trees
open PTree

import CSP.Operators

------------------------------------------------------------------------------------
-- §A. The model.
------------------------------------------------------------------------------------

-- the five channels of lazic.csp; all carry ⊤ (a ⊥-carried event never fires)
data LEv : Set → Set where
  a b c d clunk : LEv ⊤

-- decidable equality on the event indices, as every CSP operator module needs
LEv-≟ : (x y : AnyTypes LEv) → Dec (x ≡ y)
LEv-≟ (_ , a)     (_ , a)     = yes refl
LEv-≟ (_ , a)     (_ , b)     = no (λ ())
LEv-≟ (_ , a)     (_ , c)     = no (λ ())
LEv-≟ (_ , a)     (_ , d)     = no (λ ())
LEv-≟ (_ , a)     (_ , clunk) = no (λ ())
LEv-≟ (_ , b)     (_ , a)     = no (λ ())
LEv-≟ (_ , b)     (_ , b)     = yes refl
LEv-≟ (_ , b)     (_ , c)     = no (λ ())
LEv-≟ (_ , b)     (_ , d)     = no (λ ())
LEv-≟ (_ , b)     (_ , clunk) = no (λ ())
LEv-≟ (_ , c)     (_ , a)     = no (λ ())
LEv-≟ (_ , c)     (_ , b)     = no (λ ())
LEv-≟ (_ , c)     (_ , c)     = yes refl
LEv-≟ (_ , c)     (_ , d)     = no (λ ())
LEv-≟ (_ , c)     (_ , clunk) = no (λ ())
LEv-≟ (_ , d)     (_ , a)     = no (λ ())
LEv-≟ (_ , d)     (_ , b)     = no (λ ())
LEv-≟ (_ , d)     (_ , c)     = no (λ ())
LEv-≟ (_ , d)     (_ , d)     = yes refl
LEv-≟ (_ , d)     (_ , clunk) = no (λ ())
LEv-≟ (_ , clunk) (_ , a)     = no (λ ())
LEv-≟ (_ , clunk) (_ , b)     = no (λ ())
LEv-≟ (_ , clunk) (_ , c)     = no (λ ())
LEv-≟ (_ , clunk) (_ , d)     = no (λ ())
LEv-≟ (_ , clunk) (_ , clunk) = yes refl

module OpsL = CSP.Operators LEv-≟
open OpsL
open EventSet

-- the process type of this example: no data is returned, so R = ⊤
LProc : Set₁
LProc = PTree LEv (ExtI LEv) (⊤poly {lzero})

-- the four Σ-events, used to index the `Repeat`/`LHS` "waiting for the second copy"
-- states (clunk is not among them — it is never repeated)
data Sig : Set where
  σa σb σc σd : Sig

-- control states of the deterministic subject D:
--   qD  = D  = a -> D [] b -> (a -> D')      qbA = a -> D'   (reached by b)
--   qD′ = D' = c -> D' [] d -> (c -> D)      qdC = c -> D    (reached by d)
data Dst : Set where
  qD qbA qD′ qdC : Dst

-- D and its three derivatives, one raw `react` node per control state (τ-free)
DP : Dst → LProc
force (DP qD) = react
  (λ where (_ , a)     _ → just (DP qD)
           (_ , b)     _ → just (DP qbA)
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (DP qbA) = react
  (λ where (_ , a)     _ → just (DP qD′)
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (DP qD′) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → just (DP qD′)
           (_ , d)     _ → just (DP qdC)
           (_ , clunk) _ → nothing) ∅t
force (DP qdC) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → just (DP qD)
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t

-- ND = a -> ND [] a -> b -> a -> ND: the `a`-offer is AMBIGUOUS, so (as `□` computes
-- for two prefixes on the same event) it leads to the internal choice ND ⊓ (b -> …).
NDp   : LProc   -- ND
NDamb : LProc   -- ND ⊓ (b -> a -> ND), the state after the ambiguous `a`
NDb   : LProc   -- b -> a -> ND
NDba  : LProc   -- a -> ND

force NDp = react
  (λ where (_ , a)     _ → just NDamb
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force NDamb = react ∅v
  (λ where (_ , base _)   _                   → nothing
           (_ , pair _ _) _                   → nothing
           (_ , fin)      (lift fzero)        → just NDp
           (_ , fin)      (lift (fsuc fzero)) → just NDb
           (_ , fin)      _                   → nothing)
force NDb = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → just NDba
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force NDba = react
  (λ where (_ , a)     _ → just NDp
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t

-- ND2 = a -> ND2 |~| b -> a -> ND2: the nondeterminism is an explicit internal choice
ND2p  : LProc   -- ND2
ND2a  : LProc   -- a -> ND2
ND2b  : LProc   -- b -> a -> ND2
ND2ba : LProc   -- a -> ND2  (the tail of the b-branch)

force ND2p = react ∅v
  (λ where (_ , base _)   _                   → nothing
           (_ , pair _ _) _                   → nothing
           (_ , fin)      (lift fzero)        → just ND2a
           (_ , fin)      (lift (fsuc fzero)) → just ND2b
           (_ , fin)      _                   → nothing)
force ND2a = react
  (λ where (_ , a)     _ → just ND2p
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force ND2b = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → just ND2ba
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force ND2ba = react
  (λ where (_ , a)     _ → just ND2p
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t

-- control states of the harness Clunker: kOff = ready for a Σ-event, kClk = owing clunk
data Kst : Set where
  kOff kClk : Kst

-- Clunker = [] x:Sigma @ x -> clunk -> Clunker
KP : Kst → LProc
force (KP kOff) = react
  (λ where (_ , a)     _ → just (KP kClk)
           (_ , b)     _ → just (KP kClk)
           (_ , c)     _ → just (KP kClk)
           (_ , d)     _ → just (KP kClk)
           (_ , clunk) _ → nothing) ∅t
force (KP kClk) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → just (KP kOff)) ∅t

-- Repeat = [] x:Sigma @ x -> x -> Repeat; `nothing` is the idle state, `just x` is the
-- state that has seen the first x of a pair and insists on the second.
RepP : Maybe Sig → LProc
force (RepP nothing) = react
  (λ where (_ , a)     _ → just (RepP (just σa))
           (_ , b)     _ → just (RepP (just σb))
           (_ , c)     _ → just (RepP (just σc))
           (_ , d)     _ → just (RepP (just σd))
           (_ , clunk) _ → nothing) ∅t
force (RepP (just σa)) = react
  (λ where (_ , a)     _ → just (RepP nothing)
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (RepP (just σb)) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → just (RepP nothing)
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (RepP (just σc)) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → just (RepP nothing)
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (RepP (just σd)) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → just (RepP nothing)
           (_ , clunk) _ → nothing) ∅t

-- STOP at this example's process type (pins the return type R, which `Stop` leaves open)
STOP : LProc
STOP = Stop

-- LHS = STOP |~| ([] x:Sigma @ x -> x -> LHS): the specification of Lazić's check.
LHS  : LProc         -- the internal choice itself (unstable: two τ-branches)
LHSm : LProc         -- the menu [] x:Sigma @ x -> x -> LHS
LHSw : Sig → LProc   -- x -> LHS, the mid-pair state that MUST still offer x

force LHS = react ∅v
  (λ where (_ , base _)   _                   → nothing
           (_ , pair _ _) _                   → nothing
           (_ , fin)      (lift fzero)        → just STOP
           (_ , fin)      (lift (fsuc fzero)) → just LHSm
           (_ , fin)      _                   → nothing)
force LHSm = react
  (λ where (_ , a)     _ → just (LHSw σa)
           (_ , b)     _ → just (LHSw σb)
           (_ , c)     _ → just (LHSw σc)
           (_ , d)     _ → just (LHSw σd)
           (_ , clunk) _ → nothing) ∅t
force (LHSw σa) = react
  (λ where (_ , a)     _ → just LHS
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (LHSw σb) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → just LHS
           (_ , c)     _ → nothing
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (LHSw σc) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → just LHS
           (_ , d)     _ → nothing
           (_ , clunk) _ → nothing) ∅t
force (LHSw σd) = react
  (λ where (_ , a)     _ → nothing
           (_ , b)     _ → nothing
           (_ , c)     _ → nothing
           (_ , d)     _ → just LHS
           (_ , clunk) _ → nothing) ∅t

-- membership predicate of Sigma = {a,b,c,d}
inΣ : AnyTypes LEv → Set
inΣ (_ , a)     = ⊤
inΣ (_ , b)     = ⊤
inΣ (_ , c)     = ⊤
inΣ (_ , d)     = ⊤
inΣ (_ , clunk) = ⊥

-- …and its decision procedure
inΣ? : (at : AnyTypes LEv) → Dec (inΣ at)
inΣ? (_ , a)     = yes tt
inΣ? (_ , b)     = yes tt
inΣ? (_ , c)     = yes tt
inΣ? (_ , d)     = yes tt
inΣ? (_ , clunk) = no (λ z → z)

-- the synchronisation alphabet Sigma
Σs : EventSet
Σs = chanSet inΣ inΣ?

-- membership predicate of {clunk}
inCl : AnyTypes LEv → Set
inCl (_ , a)     = ⊥
inCl (_ , b)     = ⊥
inCl (_ , c)     = ⊥
inCl (_ , d)     = ⊥
inCl (_ , clunk) = ⊤

-- …and its decision procedure
inCl? : (at : AnyTypes LEv) → Dec (inCl at)
inCl? (_ , a)     = no (λ z → z)
inCl? (_ , b)     = no (λ z → z)
inCl? (_ , c)     = no (λ z → z)
inCl? (_ , d)     = no (λ z → z)
inCl? (_ , clunk) = yes tt

-- the hidden channel set {clunk}
Cls : EventSet
Cls = chanSet inCl inCl?

-- Clunking(P) = P [|Sigma|] Clunker
Clunking : LProc → LProc
Clunking P = Par⊤ Σs P (KP kOff)

-- RHS(P) = ((Clunking(P) [|{clunk}|] Clunking(P)) [|Sigma|] Repeat) \ {clunk}
RHS : LProc → LProc
RHS P = Par⊤ Σs (Par⊤ Cls (Clunking P) (Clunking P)) (RepP nothing) ∖ Cls

------------------------------------------------------------------------------------
-- §B. Proofs.  Semantics layers, opened unqualified (only one event type here).
------------------------------------------------------------------------------------

open import Semantics.LTS         {E = LEv} {I = ExtI LEv}
open import Semantics.Refusals    {E = LEv} {I = ExtI LEv}
open import Semantics.Failures    {E = LEv} {I = ExtI LEv}
open import Semantics.Determinism {E = LEv} {I = ExtI LEv}
open import Semantics.Stability   {E = LEv} {I = ExtI LEv} using (react-no-τ→stable; stable-no-τ)
open import CSP.Laws.Traces.TraceLawsParallel     LEv-≟
  using (Par-sync; Par-soloL; Par-soloR; Par-τ-L; Par-τ-R)
open import CSP.Laws.Traces.TraceLawsParallelElim LEv-≟
  using (Par-τ-elim; ParτR; τL; τR; Par-ev-elim; ParevR; evSync; evL; evR; evBoth; ev√)
open import CSP.Laws.Traces.TraceLawsHide         LEv-≟
  using (Hide-keep; Hide-hidden; Hide-τ; Hide-τ-elim; HideτR; hτP; hτH)

-- the five visible events as `Event√` labels
evA evB evC evD evK : Event√ (⊤poly {lzero})
evA = evl (evLabel ⊤ a tt)
evB = evl (evLabel ⊤ b tt)
evC = evl (evLabel ⊤ c tt)
evD = evl (evLabel ⊤ d tt)
evK = evl (evLabel ⊤ clunk tt)

------------------------------------------------------------------------------------
-- §B-det.  The DIRECT determinism verdicts, over Semantics.Determinism.
------------------------------------------------------------------------------------

-- the reachable states of D: exactly the four control states (D is τ-free)
data DReach : LProc → Set₁ where
  dr : (q : Dst) → DReach (DP q)

-- no τ from any reachable state (every DP q is `react … ∅t`)
dreach-noτ : ∀ {Q t} → DReach Q → Q ─[ τ ]─► t → ⊥
dreach-noτ (dr qD)  (sSil ())
dreach-noτ (dr qbA) (sSil ())
dreach-noτ (dr qD′) (sSil ())
dreach-noτ (dr qdC) (sSil ())
dreach-noτ (dr qD)  (sTau refl br) = case br of λ ()
dreach-noτ (dr qbA) (sTau refl br) = case br of λ ()
dreach-noτ (dr qD′) (sTau refl br) = case br of λ ()
dreach-noτ (dr qdC) (sTau refl br) = case br of λ ()

-- no √ (termination) from any reachable state (their `force` is a `react`, never `ret`)
dreach-no√ : ∀ {Q t} {r : ⊤poly {lzero}} → DReach Q → Q ─[ ev (√ r) ]─► t → ⊥
dreach-no√ (dr qD)  (sRet ())
dreach-no√ (dr qbA) (sRet ())
dreach-no√ (dr qD′) (sRet ())
dreach-no√ (dr qdC) (sRet ())

-- the target of any visible step from a reachable state is again reachable
dreach-step : ∀ {Q e q} → DReach Q → Q ─[ ev e ]─► q → DReach q
dreach-step (dr qD)  (sRet ())
dreach-step (dr qD)  (sVis {at = _ , a}     refl br) = subst DReach (just-injective br) (dr qD)
dreach-step (dr qD)  (sVis {at = _ , b}     refl br) = subst DReach (just-injective br) (dr qbA)
dreach-step (dr qD)  (sVis {at = _ , c}     refl br) = case br of λ ()
dreach-step (dr qD)  (sVis {at = _ , d}     refl br) = case br of λ ()
dreach-step (dr qD)  (sVis {at = _ , clunk} refl br) = case br of λ ()
dreach-step (dr qbA) (sRet ())
dreach-step (dr qbA) (sVis {at = _ , a}     refl br) = subst DReach (just-injective br) (dr qD′)
dreach-step (dr qbA) (sVis {at = _ , b}     refl br) = case br of λ ()
dreach-step (dr qbA) (sVis {at = _ , c}     refl br) = case br of λ ()
dreach-step (dr qbA) (sVis {at = _ , d}     refl br) = case br of λ ()
dreach-step (dr qbA) (sVis {at = _ , clunk} refl br) = case br of λ ()
dreach-step (dr qD′) (sRet ())
dreach-step (dr qD′) (sVis {at = _ , a}     refl br) = case br of λ ()
dreach-step (dr qD′) (sVis {at = _ , b}     refl br) = case br of λ ()
dreach-step (dr qD′) (sVis {at = _ , c}     refl br) = subst DReach (just-injective br) (dr qD′)
dreach-step (dr qD′) (sVis {at = _ , d}     refl br) = subst DReach (just-injective br) (dr qdC)
dreach-step (dr qD′) (sVis {at = _ , clunk} refl br) = case br of λ ()
dreach-step (dr qdC) (sRet ())
dreach-step (dr qdC) (sVis {at = _ , a}     refl br) = case br of λ ()
dreach-step (dr qdC) (sVis {at = _ , b}     refl br) = case br of λ ()
dreach-step (dr qdC) (sVis {at = _ , c}     refl br) = subst DReach (just-injective br) (dr qD)
dreach-step (dr qdC) (sVis {at = _ , d}     refl br) = case br of λ ()
dreach-step (dr qdC) (sVis {at = _ , clunk} refl br) = case br of λ ()

-- FUNCTIONAL offer: same source, same visible event ⇒ same target (react injectivity)
doffer-fun : ∀ {A e a} {q1 q2 Q : LProc}
           → Q ─[ ev (evl (evLabel A e a)) ]─► q1
           → Q ─[ ev (evl (evLabel A e a)) ]─► q2
           → q1 ≡ q2
doffer-fun s1 s2 with ev-inv s1 | ev-inv s2
... | v , τc , eq1 , br1 | v' , τc' , eq2 , br2 with trans (sym eq1) eq2
...   | refl = just-injective (trans (sym br1) br2)

-- a single visible step from a reachable state is deterministic (√ ruled out)
dstep-det : ∀ {e} {q1 q2 Q : LProc} → DReach Q
          → Q ─[ ev e ]─► q1 → Q ─[ ev e ]─► q2 → q1 ≡ q2
dstep-det {e = evl x} r s1 s2 = doffer-fun s1 s2
dstep-det {e = √ r′}  r s1 s2 = ⊥-elim (dreach-no√ r s1)

-- REACHED-STATE DETERMINACY: the state reached by a visible run over `s` is unique
ddet : ∀ {Q s P′ P″} → DReach Q → Q ⟹⟨ s ⟩ P′ → Q ⟹⟨ s ⟩ P″ → P′ ≡ P″
ddet r ⟹-refl            ⟹-refl            = refl
ddet r ⟹-refl            (⟹-τ step _)      = ⊥-elim (dreach-noτ r step)
ddet r (⟹-τ step _)      _                  = ⊥-elim (dreach-noτ r step)
ddet r (⟹-ev step1 _)    (⟹-τ step _)      = ⊥-elim (dreach-noτ r step)
ddet r (⟹-ev step1 rest1) (⟹-ev step2 rest2) =
  ddet (dreach-step r step1) rest1
       (subst (λ z → z ⟹⟨ _ ⟩ _) (sym (dstep-det r step1 step2)) rest2)

-- snoc-decomposition: a run over `s ∷ʳ a` factors as a run over `s` reaching a state
-- that OFFERS `a` (τ-free, so no leading τ before the final `a`)
dsnoc-split : ∀ {e : Event√ (⊤poly {lzero})} {Q P₀ : LProc} {s}
            → DReach Q → Q ⟹⟨ s ∷ʳ e ⟩ P₀
            → Σ[ P″ ∈ LProc ] (Q ⟹⟨ s ⟩ P″ × Offers P″ e)
dsnoc-split {s = []}     r (⟹-τ step _)   = ⊥-elim (dreach-noτ r step)
dsnoc-split {s = []}     r (⟹-ev step _)   = _ , ⟹-refl , (_ , step)
dsnoc-split {s = x ∷ s′} r (⟹-τ step _)   = ⊥-elim (dreach-noτ r step)
dsnoc-split {s = x ∷ s′} r (⟹-ev step rest) with dsnoc-split (dreach-step r step) rest
... | P″ , run , off = P″ , ⟹-ev step run , off

-- D IS DETERMINISTIC: no trace `s ∷ʳ e` coexists with a stable state reached by `s`
-- that refuses `e` — the state reached by `s` is unique and offers `e`.
D-det : Deterministic (DP qD)
D-det {s} {e} (P₀ , run) (P′ , runP′ , _ , refP′) with dsnoc-split {s = s} (dr qD) run
... | P″ , runP″ , offP″ =
      refP′ e refl (subst (λ z → Offers z e) (sym (ddet (dr qD) runP′ runP″)) offP″)

-- ND's `a` leads to NDamb, whose left τ-branch returns to NDp
ND-a : NDp ─[ ev evA ]─► NDamb
ND-a = sVis {at = ⊤ , a} {a = tt} refl refl

-- NDamb's left τ-branch (the `a -> ND` reading of the ambiguous a)
ND-τl : NDamb ─[ τ ]─► NDp
ND-τl = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl

-- NDamb's right τ-branch (the `a -> b -> a -> ND` reading)
ND-τr : NDamb ─[ τ ]─► NDb
ND-τr = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

-- witness 1: ⟨a,b⟩ is a trace of ND
ND-tr : traces NDp (evA ∷ evB ∷ [])
ND-tr = NDba , ⟹-ev ND-a (⟹-τ ND-τr (⟹-ev (sVis {at = ⊤ , b} {a = tt} refl refl) ⟹-refl))

-- NDp offers only `a`, so it does not offer `b`
NDp-no-b : ¬ Offers NDp evB
NDp-no-b (_ , sVis refl br) = case br of λ ()

-- witness 2: after ⟨a⟩, the stable state NDp refuses b
ND-fl : failures NDp (evA ∷ []) (λ e → e ≡ evB)
ND-fl = NDp , ⟹-ev ND-a (⟹-τ ND-τl ⟹-refl)
      , (λ i x → refl)
      , (λ { e refl → NDp-no-b })

-- ND IS NOT DETERMINISTIC: ⟨a,b⟩ is a trace, yet a stable state reached by ⟨a⟩ refuses b
ND-nondet : ¬ Deterministic NDp
ND-nondet det = det {s = evA ∷ []} {a = evB} ND-tr ND-fl

-- ND2's left τ-branch (the `a -> ND2` operand of |~|)
ND2-τl : ND2p ─[ τ ]─► ND2a
ND2-τl = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl

-- ND2's right τ-branch (the `b -> a -> ND2` operand of |~|)
ND2-τr : ND2p ─[ τ ]─► ND2b
ND2-τr = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

-- witness 1: ⟨a⟩ is a trace of ND2
ND2-tr : traces ND2p (evA ∷ [])
ND2-tr = ND2p , ⟹-τ ND2-τl (⟹-ev (sVis {at = ⊤ , a} {a = tt} refl refl) ⟹-refl)

-- ND2b offers only `b`, so it does not offer `a`
ND2b-no-a : ¬ Offers ND2b evA
ND2b-no-a (_ , sVis refl br) = case br of λ ()

-- witness 2: after ⟨⟩, the stable state ND2b refuses a
ND2-fl : failures ND2p [] (λ e → e ≡ evA)
ND2-fl = ND2b , ⟹-τ ND2-τr ⟹-refl
       , (λ i x → refl)
       , (λ { e refl → ND2b-no-a })

-- ND2 IS NOT DETERMINISTIC: ⟨a⟩ is a trace, yet a stable initial state refuses a
ND2-nondet : ¬ Deterministic ND2p
ND2-nondet det = det {s = []} {a = evA} ND2-tr ND2-fl

------------------------------------------------------------------------------------
-- §B-spec.  What LHS can and cannot refuse.
--
-- LHS is unstable: its two τ-branches go to STOP (which refuses everything) and to
-- the menu.  After an ODD-length trace it sits in `LHSw x`, which is stable and MUST
-- still offer x — that is the only constraint the specification imposes, and it is the
-- one Lazić's construction turns into a determinism check.
------------------------------------------------------------------------------------

-- the singleton refusal set {a}.  `_⊑F_` pins the refusal-set level to that of the
-- return type (here `lzero`), so these have to be Set₀-valued — propositional
-- equality on `Event√` lives one level up and cannot be used.
⟦a⟧ : Event√ (⊤poly {lzero}) → Set
⟦a⟧ (evl (evLabel _ a _))     = ⊤
⟦a⟧ (evl (evLabel _ b _))     = ⊥
⟦a⟧ (evl (evLabel _ c _))     = ⊥
⟦a⟧ (evl (evLabel _ d _))     = ⊥
⟦a⟧ (evl (evLabel _ clunk _)) = ⊥
⟦a⟧ (√ _)                     = ⊥

-- the singleton refusal set {b}
⟦b⟧ : Event√ (⊤poly {lzero}) → Set
⟦b⟧ (evl (evLabel _ a _))     = ⊥
⟦b⟧ (evl (evLabel _ b _))     = ⊤
⟦b⟧ (evl (evLabel _ c _))     = ⊥
⟦b⟧ (evl (evLabel _ d _))     = ⊥
⟦b⟧ (evl (evLabel _ clunk _)) = ⊥
⟦b⟧ (√ _)                     = ⊥

-- a `react … ∅t` node performs no τ at all
noτ-react : ∀ {P : LProc} {v : (at : AnyTypes LEv) → ContinueType at (Maybe LProc)}
          → force P ≡ react v ∅t → ∀ {t} → P ─[ τ ]─► t → ⊥
noτ-react eq (sSil eqs) = case trans (sym eq) eqs of λ ()
noτ-react eq (sTau eqr br) with react-injective (trans (sym eq) eqr)
... | _ , refl = case br of λ ()

-- LHS's only moves are its two τ-branches: to STOP, or to the menu
LHS-τ-inv : ∀ {t} → LHS ─[ τ ]─► t → (t ≡ STOP) ⊎ (t ≡ LHSm)
LHS-τ-inv (sSil ())
LHS-τ-inv (sTau {i = _ , base _}   refl br) = case br of λ ()
LHS-τ-inv (sTau {i = _ , pair _ _} refl br) = case br of λ ()
LHS-τ-inv (sTau {i = _ , fin} {a = lift fzero}           refl br) = inj₁ (sym (just-injective br))
LHS-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl br) = inj₂ (sym (just-injective br))
LHS-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) = case br of λ ()

-- LHS itself offers no visible event (its visible map is empty)
LHS-no-ev : ∀ {e t} → LHS ─[ ev e ]─► t → ⊥
LHS-no-ev (sRet ())
LHS-no-ev (sVis refl br) = case br of λ ()

-- STOP is dead: no run over a non-empty trace can leave it
stop-stuck : ∀ {e s P′} → STOP ⟹⟨ e ∷ s ⟩ P′ → ⊥
stop-stuck (⟹-τ (sSil ()) _)
stop-stuck (⟹-τ (sTau refl br) _) = case br of λ ()
stop-stuck (⟹-ev (sRet ()) _)
stop-stuck (⟹-ev (sVis refl br) _) = case br of λ ()

-- a run out of LHS over a NON-EMPTY trace must go through the menu (the STOP branch
-- is dead, and LHS has no visible move of its own)
lhs-step : ∀ {e s P′} → LHS ⟹⟨ e ∷ s ⟩ P′ → LHSm ⟹⟨ e ∷ s ⟩ P′
lhs-step (⟹-ev step _) = ⊥-elim (LHS-no-ev step)
lhs-step (⟹-τ step rest) with LHS-τ-inv step
... | inj₁ eq = ⊥-elim (stop-stuck (subst (λ z → z ⟹⟨ _ ⟩ _) eq rest))
... | inj₂ eq = subst (λ z → z ⟹⟨ _ ⟩ _) eq rest

-- the menu and the mid-pair states are stable
LHSm-noτ : ∀ {t} → LHSm ─[ τ ]─► t → ⊥
LHSm-noτ = noτ-react refl
LHSw-noτ : ∀ {x t} → LHSw x ─[ τ ]─► t → ⊥
LHSw-noτ {σa} = noτ-react refl
LHSw-noτ {σb} = noτ-react refl
LHSw-noτ {σc} = noτ-react refl
LHSw-noτ {σd} = noτ-react refl

-- the menu's `a`-offer leads to the mid-pair state `a -> LHS`
LHSm-a-inv : ∀ {t} → LHSm ─[ ev evA ]─► t → t ≡ LHSw σa
LHSm-a-inv (sVis refl br) = sym (just-injective br)

-- …and its `b`-offer to `b -> LHS`
LHSm-b-inv : ∀ {t} → LHSm ─[ ev evB ]─► t → t ≡ LHSw σb
LHSm-b-inv (sVis refl br) = sym (just-injective br)

-- the mid-pair state `a -> LHS` closes the pair and returns to LHS
LHSwa-a-inv : ∀ {t} → LHSw σa ─[ ev evA ]─► t → t ≡ LHS
LHSwa-a-inv (sVis refl br) = sym (just-injective br)

-- a run from the stable menu over `a ∷ s` starts with the visible `a`
lhsm-a : ∀ {s P′} → LHSm ⟹⟨ evA ∷ s ⟩ P′ → LHSw σa ⟹⟨ s ⟩ P′
lhsm-a (⟹-τ step _)      = ⊥-elim (LHSm-noτ step)
lhsm-a (⟹-ev step rest)  = subst (λ z → z ⟹⟨ _ ⟩ _) (LHSm-a-inv step) rest

-- …and over `b ∷ s` with the visible `b`
lhsm-b : ∀ {s P′} → LHSm ⟹⟨ evB ∷ s ⟩ P′ → LHSw σb ⟹⟨ s ⟩ P′
lhsm-b (⟹-τ step _)      = ⊥-elim (LHSm-noτ step)
lhsm-b (⟹-ev step rest)  = subst (λ z → z ⟹⟨ _ ⟩ _) (LHSm-b-inv step) rest

-- a run from the stable mid-pair state over `a ∷ s` closes the pair
lhswa-a : ∀ {s P′} → LHSw σa ⟹⟨ evA ∷ s ⟩ P′ → LHS ⟹⟨ s ⟩ P′
lhswa-a (⟹-τ step _)     = ⊥-elim (LHSw-noτ step)
lhswa-a (⟹-ev step rest) = subst (λ z → z ⟹⟨ _ ⟩ _) (LHSwa-a-inv step) rest

-- a mid-pair state is stable, so an empty run leaves it where it is
lhsw-nil : ∀ {x P′} → LHSw x ⟹⟨ [] ⟩ P′ → P′ ≡ LHSw x
lhsw-nil ⟹-refl        = refl
lhsw-nil (⟹-τ step _)  = ⊥-elim (LHSw-noτ step)

-- after ⟨a⟩ LHS is exactly in the mid-pair state `a -> LHS`
lhs-after-a : ∀ {P′} → LHS ⟹⟨ evA ∷ [] ⟩ P′ → P′ ≡ LHSw σa
lhs-after-a run = lhsw-nil (lhsm-a (lhs-step run))

-- after ⟨a,a,b⟩ LHS is exactly in the mid-pair state `b -> LHS`
lhs-after-aab : ∀ {P′} → LHS ⟹⟨ evA ∷ evA ∷ evB ∷ [] ⟩ P′ → P′ ≡ LHSw σb
lhs-after-aab run = lhsw-nil (lhsm-b (lhs-step (lhswa-a (lhsm-a (lhs-step run)))))

-- the mid-pair states do offer their pending event
LHSwa-offers-a : Offers (LHSw σa) evA
LHSwa-offers-a = LHS , sVis {at = ⊤ , a} {a = tt} refl refl
LHSwb-offers-b : Offers (LHSw σb) evB
LHSwb-offers-b = LHS , sVis {at = ⊤ , b} {a = tt} refl refl

-- LHS has NO failure (⟨a⟩, {a}): the state it reaches by ⟨a⟩ still offers a
lhs-no-fail-a : ¬ failures LHS (evA ∷ []) ⟦a⟧
lhs-no-fail-a (P′ , run , _ , ref) =
  ref evA tt (subst (λ z → Offers z evA) (sym (lhs-after-a run)) LHSwa-offers-a)

-- LHS has NO failure (⟨a,a,b⟩, {b}) either
lhs-no-fail-aab : ¬ failures LHS (evA ∷ evA ∷ evB ∷ []) ⟦b⟧
lhs-no-fail-aab (P′ , run , _ , ref) =
  ref evB tt (subst (λ z → Offers z evB) (sym (lhs-after-aab run)) LHSwb-offers-b)

------------------------------------------------------------------------------------
-- §B-harness.  Named states of RHS(P), and the step lemmas that move between them.
------------------------------------------------------------------------------------

-- one copy of the subject under test: P [|Sigma|] Clunker with Clunker in state k
Cp : LProc → Kst → LProc
Cp P k = Par⊤ Σs P (KP k)

-- the two copies side by side, synchronised on clunk only
Pr : LProc → LProc → LProc
Pr c₁ c₂ = Par⊤ Cls c₁ c₂

-- the harness around an already-built copy-pair: against Repeat, with clunk hidden
SyP : LProc → Maybe Sig → LProc
SyP p r = Par⊤ Σs p (RepP r) ∖ Cls

-- the harness around two copies in given states (RHS P = Sy (Cp P kOff) (Cp P kOff) nothing)
Sy : LProc → LProc → Maybe Sig → LProc
Sy c₁ c₂ r = SyP (Pr c₁ c₂) r

-- the "both copies offered the same Σ-event" intermediate node the clunk-layer
-- parallel builds when neither copy has to synchronise: an UNSTABLE node whose two
-- τ-branches record which copy actually moved
BothN : LProc → LProc → LProc → LProc → LProc
BothN c₁ c₂ c₁′ c₂′ = ptree (react ∅v (par-brBoth Cls (λ _ _ → lift tt) c₁ c₂ c₁′ c₂′))

-- resolving that node in favour of the LEFT copy
both-τL : ∀ {c₁ c₂ c₁′ c₂′} → BothN c₁ c₂ c₁′ c₂′ ─[ τ ]─► Pr c₁′ c₂
both-τL = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl

-- the Clunker's own steps: any Σ-event puts it in debt, the clunk clears the debt
kOff-a : KP kOff ─[ ev evA ]─► KP kClk
kOff-a = sVis {at = ⊤ , a} {a = tt} refl refl
kOff-b : KP kOff ─[ ev evB ]─► KP kClk
kOff-b = sVis {at = ⊤ , b} {a = tt} refl refl
kClk-k : KP kClk ─[ ev evK ]─► KP kOff
kClk-k = sVis {at = ⊤ , clunk} {a = tt} refl refl

-- Repeat's steps: the first half of a pair, and the matching second half
rep-a : RepP nothing ─[ ev evA ]─► RepP (just σa)
rep-a = sVis {at = ⊤ , a} {a = tt} refl refl
rep-b : RepP nothing ─[ ev evB ]─► RepP (just σb)
rep-b = sVis {at = ⊤ , b} {a = tt} refl refl
rep-a2 : RepP (just σa) ─[ ev evA ]─► RepP nothing
rep-a2 = sVis {at = ⊤ , a} {a = tt} refl refl

-- a τ of the subject is a τ of its copy
cp-τ : ∀ {P P′ k} → P ─[ τ ]─► P′ → Cp P k ─[ τ ]─► Cp P′ k
cp-τ {P} {P′} {k} st = Par-τ-L Σs _ P (KP k) st

-- a copy performs a Σ-event: subject and Clunker move together
cp-ev : ∀ {P P′} {X : Set} {e : LEv X} {x : X}
      → inΣ (X , e)
      → P ─[ ev (evl (evLabel X e x)) ]─► P′
      → KP kOff ─[ ev (evl (evLabel X e x)) ]─► KP kClk
      → Cp P kOff ─[ ev (evl (evLabel X e x)) ]─► Cp P′ kClk
cp-ev {P} {P′} cs sp sk = Par-sync Σs _ P (KP kOff) cs sp sk

-- a copy in debt pays its clunk (the subject does not move: clunk ∉ Sigma)
cp-clunk : ∀ {P} → viewV (force P) (⊤ , clunk) tt ≡ nothing
         → Cp P kClk ─[ ev evK ]─► Cp P kOff
cp-clunk {P} np = Par-soloR Σs _ P (KP kClk) (λ z → z) kClk-k np

-- a τ inside the LEFT copy is a τ of the whole harness
sy-τ-L : ∀ {c₁ c₁′ c₂ r} → c₁ ─[ τ ]─► c₁′ → Sy c₁ c₂ r ─[ τ ]─► Sy c₁′ c₂ r
sy-τ-L {c₁} {c₁′} {c₂} {r} st =
  Hide-τ Cls (Par⊤ Σs (Pr c₁ c₂) (RepP r))
    (Par-τ-L Σs _ (Pr c₁ c₂) (RepP r) (Par-τ-L Cls _ c₁ c₂ st))

-- …and symmetrically for the RIGHT copy
sy-τ-R : ∀ {c₁ c₂ c₂′ r} → c₂ ─[ τ ]─► c₂′ → Sy c₁ c₂ r ─[ τ ]─► Sy c₁ c₂′ r
sy-τ-R {c₁} {c₂} {c₂′} {r} st =
  Hide-τ Cls (Par⊤ Σs (Pr c₁ c₂) (RepP r))
    (Par-τ-L Σs _ (Pr c₁ c₂) (RepP r) (Par-τ-R Cls _ c₁ c₂ st))

-- a τ inside an intermediate both-offer pair is a τ of the harness
syp-τ : ∀ {p p′ r} → p ─[ τ ]─► p′ → SyP p r ─[ τ ]─► SyP p′ r
syp-τ {p} {p′} {r} st = Hide-τ Cls (Par⊤ Σs p (RepP r)) (Par-τ-L Σs _ p (RepP r) st)

-- the LEFT copy performs a Σ-event while the right copy cannot follow it
sy-ev-L : ∀ {c₁ c₁′ c₂ r r′} {X : Set} {e : LEv X} {x : X}
        → inΣ (X , e) → ¬ inCl (X , e)
        → c₁ ─[ ev (evl (evLabel X e x)) ]─► c₁′
        → viewV (force c₂) (X , e) x ≡ nothing
        → RepP r ─[ ev (evl (evLabel X e x)) ]─► RepP r′
        → Sy c₁ c₂ r ─[ ev (evl (evLabel X e x)) ]─► Sy c₁′ c₂ r′
sy-ev-L {c₁} {c₁′} {c₂} {r} cs ncl s1 n2 sr =
  Hide-keep Cls (Par⊤ Σs (Pr c₁ c₂) (RepP r)) ncl
    (Par-sync Σs _ (Pr c₁ c₂) (RepP r) cs (Par-soloL Cls _ c₁ c₂ ncl s1 n2) sr)

-- …and symmetrically, the RIGHT copy moving while the left one cannot
sy-ev-R : ∀ {c₁ c₂ c₂′ r r′} {X : Set} {e : LEv X} {x : X}
        → inΣ (X , e) → ¬ inCl (X , e)
        → c₂ ─[ ev (evl (evLabel X e x)) ]─► c₂′
        → viewV (force c₁) (X , e) x ≡ nothing
        → RepP r ─[ ev (evl (evLabel X e x)) ]─► RepP r′
        → Sy c₁ c₂ r ─[ ev (evl (evLabel X e x)) ]─► Sy c₁ c₂′ r′
sy-ev-R {c₁} {c₂} {c₂′} {r} cs ncl s2 n1 sr =
  Hide-keep Cls (Par⊤ Σs (Pr c₁ c₂) (RepP r)) ncl
    (Par-sync Σs _ (Pr c₁ c₂) (RepP r) cs (Par-soloR Cls _ c₁ c₂ ncl s2 n1) sr)

-- both copies pay their clunk together; hiding turns that into a τ
sy-clunk : ∀ {c₁ c₁′ c₂ c₂′ r}
         → c₁ ─[ ev evK ]─► c₁′ → c₂ ─[ ev evK ]─► c₂′
         → viewV (force (RepP r)) (⊤ , clunk) tt ≡ nothing
         → Sy c₁ c₂ r ─[ τ ]─► Sy c₁′ c₂′ r
sy-clunk {c₁} {c₁′} {c₂} {c₂′} {r} s1 s2 nr =
  Hide-hidden Cls (Par⊤ Σs (Pr c₁ c₂) (RepP r)) tt
    (Par-soloL Σs _ (Pr c₁ c₂) (RepP r) (λ z → z) (Par-sync Cls _ c₁ c₂ tt s1 s2) nr)

-- a parallel composite of two τ-free operands is τ-free
par-noτ : (A : EventSet) (mg : ⊤poly {lzero} → ⊤poly {lzero} → ⊤poly {lzero})
          (P Q : LProc)
        → (∀ {t} → P ─[ τ ]─► t → ⊥) → (∀ {t} → Q ─[ τ ]─► t → ⊥)
        → ∀ {t} → Par A mg P Q ─[ τ ]─► t → ⊥
par-noτ A mg P Q nP nQ st with Par-τ-elim A mg P Q st
... | τL P' Pτ _ = nP Pτ
... | τR Q' Qτ _ = nQ Qτ

-- hiding {clunk} over a τ-free process that offers no clunk keeps it τ-free
hide-noτ : (P : LProc)
         → (∀ {t} → P ─[ τ ]─► t → ⊥)
         → (∀ {t} → P ─[ ev evK ]─► t → ⊥)
         → ∀ {t} → (P ∖ Cls) ─[ τ ]─► t → ⊥
hide-noτ P nτ nk st with Hide-τ-elim Cls P st
... | hτP P' Pτ _            = nτ Pτ
... | hτH {e = a}     P' () _ _
... | hτH {e = b}     P' () _ _
... | hτH {e = c}     P' () _ _
... | hτH {e = d}     P' () _ _
... | hτH {e = clunk} P' _ Pev _ = nk Pev

------------------------------------------------------------------------------------
-- §B-lazic-neg.  LHS [F= RHS(ND) and LHS [F= RHS(ND2) are FALSE.
------------------------------------------------------------------------------------

-- the deadlocked state of RHS(ND2): copy 1 has done its `a` and owes a clunk, copy 2
-- resolved |~| the other way and only offers b, so nobody can supply Repeat's second a
F2 : LProc
F2 = Sy (Cp ND2a kClk) (Cp ND2b kOff) (just σa)

-- ND2's `a`-branch performs a and comes back to ND2
ND2a-a : ND2a ─[ ev evA ]─► ND2p
ND2a-a = sVis {at = ⊤ , a} {a = tt} refl refl

-- the run: copy 2 picks the b-branch, copy 1 picks the a-branch and fires it, and
-- copy 1 then resolves its next |~| — the visible trace is ⟨a⟩
F2-run : RHS ND2p ⟹⟨ evA ∷ [] ⟩ F2
F2-run = ⟹-τ (sy-τ-R (cp-τ ND2-τr))
        (⟹-τ (sy-τ-L (cp-τ ND2-τl))
        (⟹-ev (sy-ev-L tt (λ z → z) (cp-ev tt ND2a-a kOff-a) refl rep-a)
        (⟹-τ (sy-τ-L (cp-τ ND2-τl)) ⟹-refl)))

-- F2 offers no clunk (only copy 1 owes one, and clunk is synchronised)
F2-no-clunk : ∀ {t} → Par⊤ Σs (Pr (Cp ND2a kClk) (Cp ND2b kOff)) (RepP (just σa))
                        ─[ ev evK ]─► t → ⊥
F2-no-clunk (sVis refl br) = case br of λ ()

-- F2 is stable: every leaf is τ-free and no clunk is on offer to be hidden
F2-stable : isStable F2
F2-stable = react-no-τ→stable refl
  (hide-noτ (Par⊤ Σs (Pr (Cp ND2a kClk) (Cp ND2b kOff)) (RepP (just σa)))
     (par-noτ Σs _ (Pr (Cp ND2a kClk) (Cp ND2b kOff)) (RepP (just σa))
        (par-noτ Cls _ (Cp ND2a kClk) (Cp ND2b kOff)
           (par-noτ Σs _ ND2a (KP kClk) (noτ-react refl) (noτ-react refl))
           (par-noτ Σs _ ND2b (KP kOff) (noτ-react refl) (noτ-react refl)))
        (noτ-react refl))
     F2-no-clunk)

-- …and it refuses a: copy 1 is in clunk-debt and copy 2 offers only b
F2-no-a : ¬ Offers F2 evA
F2-no-a (_ , sVis refl br) = case br of λ ()

-- so (⟨a⟩, {a}) IS a failure of RHS(ND2)
F2-fail : failures (RHS ND2p) (evA ∷ []) ⟦a⟧
F2-fail = F2 , F2-run , F2-stable
        , (λ { (evl (evLabel _ a _))     _ → F2-no-a
             ; (evl (evLabel _ b _))     ()
             ; (evl (evLabel _ c _))     ()
             ; (evl (evLabel _ d _))     ()
             ; (evl (evLabel _ clunk _)) ()
             ; (√ _)                     () })

-- LHS [F= RHS(ND2) is FALSE: RHS(ND2) refuses a after ⟨a⟩, LHS never does
lazic-ND2 : ¬ (LHS ⊑F RHS ND2p)
lazic-ND2 ref = lhs-no-fail-a (ref (evA ∷ []) ⟦a⟧ F2-fail)

-- the state RHS(ND) reaches after ⟨a,a⟩ with both copies committed the SAME way is
-- irrelevant; what matters is that they may commit DIFFERENTLY.  ND's `a` reaches the
-- ambiguous state, whose two τ-branches disagree about what comes next.
ND-b : NDb ─[ ev evB ]─► NDba
ND-b = sVis {at = ⊤ , b} {a = tt} refl refl

-- the both-offer intermediate reached by the very first `a` (both copies offer it)
NDboth : LProc
NDboth = BothN (Cp NDp kOff) (Cp NDp kOff) (Cp NDamb kClk) (Cp NDamb kClk)

-- the clunk-layer step into that intermediate node
ND-pr-a : Pr (Cp NDp kOff) (Cp NDp kOff) ─[ ev evA ]─► NDboth
ND-pr-a = sVis {at = ⊤ , a} {a = tt} refl refl

-- …lifted through Repeat and the hide
ND-sy-a : RHS NDp ─[ ev evA ]─► SyP NDboth (just σa)
ND-sy-a =
  Hide-keep Cls (Par⊤ Σs (Pr (Cp NDp kOff) (Cp NDp kOff)) (RepP nothing)) (λ z → z)
    (Par-sync Σs _ (Pr (Cp NDp kOff) (Cp NDp kOff)) (RepP nothing) tt ND-pr-a rep-a)

-- the deadlocked state of RHS(ND): copy 1 committed to `b -> a -> ND` and has just
-- fired its b, copy 2 committed to `a -> ND` and cannot supply Repeat's second b
FN : LProc
FN = Sy (Cp NDba kClk) (Cp NDp kOff) (just σb)

-- the run: first a (both copies offer it, then copy 1 is chosen), second a by copy 2,
-- the joint clunk, the two copies resolving the ambiguity DIFFERENTLY, then b by copy 1
FN-run : RHS NDp ⟹⟨ evA ∷ evA ∷ evB ∷ [] ⟩ FN
FN-run =
  ⟹-ev ND-sy-a
 (⟹-τ (syp-τ both-τL)
 (⟹-ev (sy-ev-R tt (λ z → z) (cp-ev tt ND-a kOff-a) refl rep-a2)
 (⟹-τ (sy-clunk (cp-clunk refl) (cp-clunk refl) refl)
 (⟹-τ (sy-τ-L (cp-τ ND-τr))
 (⟹-τ (sy-τ-R (cp-τ ND-τl))
 (⟹-ev (sy-ev-L tt (λ z → z) (cp-ev tt ND-b kOff-b) refl rep-b) ⟹-refl))))))

-- FN offers no clunk (only copy 1 owes one)
FN-no-clunk : ∀ {t} → Par⊤ Σs (Pr (Cp NDba kClk) (Cp NDp kOff)) (RepP (just σb))
                        ─[ ev evK ]─► t → ⊥
FN-no-clunk (sVis refl br) = case br of λ ()

-- FN is stable
FN-stable : isStable FN
FN-stable = react-no-τ→stable refl
  (hide-noτ (Par⊤ Σs (Pr (Cp NDba kClk) (Cp NDp kOff)) (RepP (just σb)))
     (par-noτ Σs _ (Pr (Cp NDba kClk) (Cp NDp kOff)) (RepP (just σb))
        (par-noτ Cls _ (Cp NDba kClk) (Cp NDp kOff)
           (par-noτ Σs _ NDba (KP kClk) (noτ-react refl) (noτ-react refl))
           (par-noτ Σs _ NDp  (KP kOff) (noτ-react refl) (noτ-react refl)))
        (noτ-react refl))
     FN-no-clunk)

-- …and it refuses b: neither copy can perform the b that Repeat insists on
FN-no-b : ¬ Offers FN evB
FN-no-b (_ , sVis refl br) = case br of λ ()

-- so (⟨a,a,b⟩, {b}) IS a failure of RHS(ND)
FN-fail : failures (RHS NDp) (evA ∷ evA ∷ evB ∷ []) ⟦b⟧
FN-fail = FN , FN-run , FN-stable
        , (λ { (evl (evLabel _ a _))     ()
             ; (evl (evLabel _ b _))     _ → FN-no-b
             ; (evl (evLabel _ c _))     ()
             ; (evl (evLabel _ d _))     ()
             ; (evl (evLabel _ clunk _)) ()
             ; (√ _)                     () })

-- LHS [F= RHS(ND) is FALSE: RHS(ND) refuses b after ⟨a,a,b⟩, LHS never does
lazic-ND : ¬ (LHS ⊑F RHS NDp)
lazic-ND ref = lhs-no-fail-aab (ref (evA ∷ evA ∷ evB ∷ []) ⟦b⟧ FN-fail)

------------------------------------------------------------------------------------
-- §B-lazic-pos.  LHS [F= RHS(D) is TRUE.
--
-- The proof is a WEAK SIMULATION from RHS(D) to LHS with a refusal-transfer clause —
-- exactly the three obligations a stable-failures refinement needs, discharged over an
-- explicit enumeration of the reachable states of the harness (`SimR` below).  D is
-- deterministic, so after the first event of a pair the copy that has NOT moved yet is
-- in the same control state the mover came from and can always follow: the mid-pair
-- states `M1`/`M2` offer exactly the pending event, which is precisely what `LHSw x`
-- allows.  The even states are matched by LHS's STOP branch, which refuses everything.
------------------------------------------------------------------------------------

-- the visible event a Σ-tag stands for
sigEv : Sig → Event√ (⊤poly {lzero})
sigEv σa = evA
sigEv σb = evB
sigEv σc = evC
sigEv σd = evD

-- D's transition table, as a relation on control states
data DStep : Dst → Sig → Dst → Set where
  st-aa : DStep qD  σa qD
  st-ab : DStep qD  σb qbA
  st-ba : DStep qbA  σa qD′
  st-cc : DStep qD′  σc qD′
  st-cd : DStep qD′  σd qdC
  st-dc : DStep qdC  σc qD

-- REACHABLE STATES of RHS(D), and the LHS state each is matched against.

-- both copies idle in control state q, Repeat idle: the state after an EVEN number of
-- visible events (RHS D = E qD)
E : Dst → LProc
E q = Sy (Cp (DP q) kOff) (Cp (DP q) kOff) nothing

-- the first event of a pair has fired, but which copy performed it is not yet resolved
B : Dst → Sig → Dst → LProc
B q x q′ = SyP (BothN (Cp (DP q) kOff) (Cp (DP q) kOff) (Cp (DP q′) kClk) (Cp (DP q′) kClk)) (just x)

-- copy 1 performed the pair's first event and now owes a clunk
M1 : Dst → Sig → Dst → LProc
M1 q x q′ = Sy (Cp (DP q′) kClk) (Cp (DP q) kOff) (just x)

-- copy 2 performed it
M2 : Dst → Sig → Dst → LProc
M2 q x q′ = Sy (Cp (DP q) kOff) (Cp (DP q′) kClk) (just x)

-- both copies have performed the pair's event and owe their clunks
Cc : Dst → LProc
Cc q = Sy (Cp (DP q) kClk) (Cp (DP q) kClk) nothing

-- the simulation relation: which LHS state each reachable harness state answers to
data SimR : LProc → LProc → Set₁ where
  simE  : (q : Dst) → SimR (E q) LHS
  simB  : ∀ {q x q′} → DStep q x q′ → SimR (B q x q′) (LHSw x)
  simM1 : ∀ {q x q′} → DStep q x q′ → SimR (M1 q x q′) (LHSw x)
  simM2 : ∀ {q x q′} → DStep q x q′ → SimR (M2 q x q′) (LHSw x)
  simC  : (q : Dst) → SimR (Cc q) LHS

-- τ-freeness of the leaves
noτ-DP : ∀ {q t} → DP q ─[ τ ]─► t → ⊥
noτ-DP {qD} = noτ-react refl
noτ-DP {qbA} = noτ-react refl
noτ-DP {qD′} = noτ-react refl
noτ-DP {qdC} = noτ-react refl
noτ-KP : ∀ {k t} → KP k ─[ τ ]─► t → ⊥
noτ-KP {kOff} = noτ-react refl
noτ-KP {kClk} = noτ-react refl
noτ-RepP : ∀ {r t} → RepP r ─[ τ ]─► t → ⊥
noτ-RepP {nothing} = noτ-react refl
noτ-RepP {just σa} = noτ-react refl
noτ-RepP {just σb} = noτ-react refl
noτ-RepP {just σc} = noτ-react refl
noτ-RepP {just σd} = noτ-react refl

-- Repeat never offers the clunk (it is not in Repeat's alphabet)
RepP-no-clunk : ∀ {r t} → RepP r ─[ ev evK ]─► t → ⊥
RepP-no-clunk {nothing} (sVis refl br) = case br of λ ()
RepP-no-clunk {just σa} (sVis refl br) = case br of λ ()
RepP-no-clunk {just σb} (sVis refl br) = case br of λ ()
RepP-no-clunk {just σc} (sVis refl br) = case br of λ ()
RepP-no-clunk {just σd} (sVis refl br) = case br of λ ()

-- a copy of D is τ-free (both its components are)
noτ-Cp : ∀ {q k t} → Cp (DP q) k ─[ τ ]─► t → ⊥
noτ-Cp {q} {k} = par-noτ Σs _ (DP q) (KP k) noτ-DP noτ-KP

-- an event outside {clunk} is inside Sigma (the alphabet has no other channels)
notCl→inΣ : ∀ {X : Set} {e : LEv X} → ¬ inCl (X , e) → inΣ (X , e)
notCl→inΣ {e = a} ncl = tt
notCl→inΣ {e = b} ncl = tt
notCl→inΣ {e = c} ncl = tt
notCl→inΣ {e = d} ncl = tt
notCl→inΣ {e = clunk} ncl = ⊥-elim (ncl tt)

-- a τ of the harness is either a τ of the copy-pair or the pair's HIDDEN clunk
syp-τ-elim : ∀ {p r M} → SyP p r ─[ τ ]─► M
           → (Σ[ p′ ∈ LProc ] (p ─[ τ ]─► p′ × M ≡ SyP p′ r))
           ⊎ (Σ[ p′ ∈ LProc ] (p ─[ ev evK ]─► p′ × M ≡ SyP p′ r))
syp-τ-elim {p} {r} st with Hide-τ-elim Cls (Par⊤ Σs p (RepP r)) st
... | hτP m mτ eq with Par-τ-elim Σs _ p (RepP r) mτ
...   | τL p′ s′ eq2 = inj₁ (p′ , s′ , trans eq (cong (_∖ Cls) eq2))
...   | τR _  s′ _   = ⊥-elim (noτ-RepP s′)
syp-τ-elim {p} {r} st | hτH {e = a} m () _ _
syp-τ-elim {p} {r} st | hτH {e = b} m () _ _
syp-τ-elim {p} {r} st | hτH {e = c} m () _ _
syp-τ-elim {p} {r} st | hτH {e = d} m () _ _
syp-τ-elim {p} {r} st | hτH {e = clunk} m _ pev eq with Par-ev-elim Σs _ p (RepP r) pev
... | evSync () _ _
... | evL _ s′      = inj₂ (_ , s′ , eq)
... | evR _ s′      = ⊥-elim (RepP-no-clunk s′)
... | evBoth _ _ s′ = ⊥-elim (RepP-no-clunk s′)

-- …so when BOTH copies are τ-free, the harness's only τ is the joint clunk
sy-τ-elim : ∀ {c₁ c₂ r M}
          → (∀ {u} → c₁ ─[ τ ]─► u → ⊥) → (∀ {u} → c₂ ─[ τ ]─► u → ⊥)
          → Sy c₁ c₂ r ─[ τ ]─► M
          → Σ[ c₁′ ∈ LProc ] Σ[ c₂′ ∈ LProc ]
              (c₁ ─[ ev evK ]─► c₁′ × c₂ ─[ ev evK ]─► c₂′ × M ≡ Sy c₁′ c₂′ r)
sy-τ-elim {c₁} {c₂} n1 n2 st with syp-τ-elim st
... | inj₁ (p′ , pτ , eq) with Par-τ-elim Cls _ c₁ c₂ pτ
...   | τL _ s _ = ⊥-elim (n1 s)
...   | τR _ s _ = ⊥-elim (n2 s)
sy-τ-elim {c₁} {c₂} n1 n2 st | inj₂ (p′ , pev , eq) with Par-ev-elim Cls _ c₁ c₂ pev
... | evSync _ s1 s2 = _ , _ , s1 , s2 , eq
... | evL ¬cs _      = ⊥-elim (¬cs tt)
... | evR ¬cs _      = ⊥-elim (¬cs tt)
... | evBoth ¬cs _ _ = ⊥-elim (¬cs tt)

-- an idle copy owes no clunk, so it cannot supply one
cp-off-no-clunk : ∀ {q t} → Cp (DP q) kOff ─[ ev evK ]─► t → ⊥
cp-off-no-clunk {qD} (sVis refl br) = case br of λ ()
cp-off-no-clunk {qbA} (sVis refl br) = case br of λ ()
cp-off-no-clunk {qD′} (sVis refl br) = case br of λ ()
cp-off-no-clunk {qdC} (sVis refl br) = case br of λ ()

-- a copy in debt pays exactly its clunk and nothing else changes
cp-clk-clunk-inv : ∀ {q t} → Cp (DP q) kClk ─[ ev evK ]─► t → t ≡ Cp (DP q) kOff
cp-clk-clunk-inv {qD} (sVis refl br) = sym (just-injective br)
cp-clk-clunk-inv {qbA} (sVis refl br) = sym (just-injective br)
cp-clk-clunk-inv {qD′} (sVis refl br) = sym (just-injective br)
cp-clk-clunk-inv {qdC} (sVis refl br) = sym (just-injective br)

-- the both-offer node's two τ-branches: copy 1 moved, or copy 2 moved
both-τ-inv : ∀ {c₁ c₂ c₁′ c₂′ t} → BothN c₁ c₂ c₁′ c₂′ ─[ τ ]─► t
           → (t ≡ Pr c₁′ c₂) ⊎ (t ≡ Pr c₁ c₂′)
both-τ-inv (sSil ())
both-τ-inv (sTau {i = _ , base _}   refl br) = case br of λ ()
both-τ-inv (sTau {i = _ , pair _ _} refl br) = case br of λ ()
both-τ-inv (sTau {i = _ , fin} {a = lift fzero}           refl br) = inj₁ (sym (just-injective br))
both-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl br) = inj₂ (sym (just-injective br))
both-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl br) = case br of λ ()

-- the both-offer node offers nothing visible (it only records the pending choice)
both-no-ev : ∀ {c₁ c₂ c₁′ c₂′ e t} → BothN c₁ c₂ c₁′ c₂′ ─[ ev e ]─► t → ⊥
both-no-ev (sRet ())
both-no-ev (sVis refl br) = case br of λ ()

-- the clunk that takes a `both copies in debt` state back to an even state
cc-τ : (q : Dst) → Cc q ─[ τ ]─► E q
cc-τ qD = sy-clunk (cp-clunk refl) (cp-clunk refl) refl
cc-τ qbA = sy-clunk (cp-clunk refl) (cp-clunk refl) refl
cc-τ qD′ = sy-clunk (cp-clunk refl) (cp-clunk refl) refl
cc-τ qdC = sy-clunk (cp-clunk refl) (cp-clunk refl) refl

-- LHS's τ-branch into the menu, and into STOP
LHS-τ-menu : LHS ─[ τ ]─► LHSm
LHS-τ-menu = sTau {i = Lift lzero (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl
LHS-τ-stop : LHS ─[ τ ]─► STOP
LHS-τ-stop = sTau {i = Lift lzero (Fin 2) , fin} {a = lift fzero} refl refl

-- LHS matches the FIRST event of a pair by resolving into the menu and offering it
lhs-first : (x : Sig) → LHS ⟹⟨ sigEv x ∷ [] ⟩ LHSw x
lhs-first σa = ⟹-τ LHS-τ-menu (⟹-ev (sVis {at = _ , a} {a = tt} refl refl) ⟹-refl)
lhs-first σb = ⟹-τ LHS-τ-menu (⟹-ev (sVis {at = _ , b} {a = tt} refl refl) ⟹-refl)
lhs-first σc = ⟹-τ LHS-τ-menu (⟹-ev (sVis {at = _ , c} {a = tt} refl refl) ⟹-refl)
lhs-first σd = ⟹-τ LHS-τ-menu (⟹-ev (sVis {at = _ , d} {a = tt} refl refl) ⟹-refl)

-- …and the SECOND event of the pair from the mid-pair state
lhs-second : (x : Sig) → LHSw x ⟹⟨ sigEv x ∷ [] ⟩ LHS
lhs-second σa = ⟹-ev (sVis {at = _ , a} {a = tt} refl refl) ⟹-refl
lhs-second σb = ⟹-ev (sVis {at = _ , b} {a = tt} refl refl) ⟹-refl
lhs-second σc = ⟹-ev (sVis {at = _ , c} {a = tt} refl refl) ⟹-refl
lhs-second σd = ⟹-ev (sVis {at = _ , d} {a = tt} refl refl) ⟹-refl

-- a mid-pair LHS state offers its pending event and nothing else
LHSw-offer-inv : ∀ {x e t} → LHSw x ─[ ev e ]─► t → e ≡ sigEv x
LHSw-offer-inv {σa} (sRet ())
LHSw-offer-inv {σa} (sVis {at = _ , a} refl br) = refl
LHSw-offer-inv {σa} (sVis {at = _ , b} refl br) = case br of λ ()
LHSw-offer-inv {σa} (sVis {at = _ , c} refl br) = case br of λ ()
LHSw-offer-inv {σa} (sVis {at = _ , d} refl br) = case br of λ ()
LHSw-offer-inv {σa} (sVis {at = _ , clunk} refl br) = case br of λ ()
LHSw-offer-inv {σb} (sRet ())
LHSw-offer-inv {σb} (sVis {at = _ , a} refl br) = case br of λ ()
LHSw-offer-inv {σb} (sVis {at = _ , b} refl br) = refl
LHSw-offer-inv {σb} (sVis {at = _ , c} refl br) = case br of λ ()
LHSw-offer-inv {σb} (sVis {at = _ , d} refl br) = case br of λ ()
LHSw-offer-inv {σb} (sVis {at = _ , clunk} refl br) = case br of λ ()
LHSw-offer-inv {σc} (sRet ())
LHSw-offer-inv {σc} (sVis {at = _ , a} refl br) = case br of λ ()
LHSw-offer-inv {σc} (sVis {at = _ , b} refl br) = case br of λ ()
LHSw-offer-inv {σc} (sVis {at = _ , c} refl br) = refl
LHSw-offer-inv {σc} (sVis {at = _ , d} refl br) = case br of λ ()
LHSw-offer-inv {σc} (sVis {at = _ , clunk} refl br) = case br of λ ()
LHSw-offer-inv {σd} (sRet ())
LHSw-offer-inv {σd} (sVis {at = _ , a} refl br) = case br of λ ()
LHSw-offer-inv {σd} (sVis {at = _ , b} refl br) = case br of λ ()
LHSw-offer-inv {σd} (sVis {at = _ , c} refl br) = case br of λ ()
LHSw-offer-inv {σd} (sVis {at = _ , d} refl br) = refl
LHSw-offer-inv {σd} (sVis {at = _ , clunk} refl br) = case br of λ ()

-- STOP is stable and refuses every event set — it is what LHS's even states offer
STOP-refuses : ∀ {X : Event√ (⊤poly {lzero}) → Set} → Refuses STOP X
STOP-refuses = (λ i x → refl) , (λ { e _ (_ , sVis refl br) → case br of λ () })

-- the mid-pair harness states DO offer the pending event: that is determinism at work
m1-offers : ∀ {q x q′} → DStep q x q′ → Offers (M1 q x q′) (sigEv x)
m1-offers st-aa = _ , sVis {at = _ , a} {a = tt} refl refl
m1-offers st-ab = _ , sVis {at = _ , b} {a = tt} refl refl
m1-offers st-ba = _ , sVis {at = _ , a} {a = tt} refl refl
m1-offers st-cc = _ , sVis {at = _ , c} {a = tt} refl refl
m1-offers st-cd = _ , sVis {at = _ , d} {a = tt} refl refl
m1-offers st-dc = _ , sVis {at = _ , c} {a = tt} refl refl
m2-offers : ∀ {q x q′} → DStep q x q′ → Offers (M2 q x q′) (sigEv x)
m2-offers st-aa = _ , sVis {at = _ , a} {a = tt} refl refl
m2-offers st-ab = _ , sVis {at = _ , b} {a = tt} refl refl
m2-offers st-ba = _ , sVis {at = _ , a} {a = tt} refl refl
m2-offers st-cc = _ , sVis {at = _ , c} {a = tt} refl refl
m2-offers st-cd = _ , sVis {at = _ , d} {a = tt} refl refl
m2-offers st-dc = _ , sVis {at = _ , c} {a = tt} refl refl

-- OBLIGATION 1: every visible step of the harness is matched by LHS
sim-ev : ∀ {R L R′} {e : Event√ (⊤poly {lzero})} → SimR R L → R ─[ ev e ]─► R′
       → Σ[ L′ ∈ LProc ] (L ⟹⟨ e ∷ [] ⟩ L′ × SimR R′ L′)
sim-ev (simE qD) (sRet ())
sim-ev (simE qD) (sVis {at = _ , a} refl br) =
  LHSw σa , lhs-first σa , subst (λ z → SimR z (LHSw σa)) (just-injective br) (simB st-aa)
sim-ev (simE qD) (sVis {at = _ , b} refl br) =
  LHSw σb , lhs-first σb , subst (λ z → SimR z (LHSw σb)) (just-injective br) (simB st-ab)
sim-ev (simE qD) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simE qD) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simE qD) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simE qbA) (sRet ())
sim-ev (simE qbA) (sVis {at = _ , a} refl br) =
  LHSw σa , lhs-first σa , subst (λ z → SimR z (LHSw σa)) (just-injective br) (simB st-ba)
sim-ev (simE qbA) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simE qbA) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simE qbA) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simE qbA) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simE qD′) (sRet ())
sim-ev (simE qD′) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simE qD′) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simE qD′) (sVis {at = _ , c} refl br) =
  LHSw σc , lhs-first σc , subst (λ z → SimR z (LHSw σc)) (just-injective br) (simB st-cc)
sim-ev (simE qD′) (sVis {at = _ , d} refl br) =
  LHSw σd , lhs-first σd , subst (λ z → SimR z (LHSw σd)) (just-injective br) (simB st-cd)
sim-ev (simE qD′) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simE qdC) (sRet ())
sim-ev (simE qdC) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simE qdC) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simE qdC) (sVis {at = _ , c} refl br) =
  LHSw σc , lhs-first σc , subst (λ z → SimR z (LHSw σc)) (just-injective br) (simB st-dc)
sim-ev (simE qdC) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simE qdC) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-aa) (sRet ())
sim-ev (simB st-aa) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-aa) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-aa) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-aa) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-aa) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-ab) (sRet ())
sim-ev (simB st-ab) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-ab) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-ab) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-ab) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-ab) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-ba) (sRet ())
sim-ev (simB st-ba) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-ba) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-ba) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-ba) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-ba) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-cc) (sRet ())
sim-ev (simB st-cc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-cc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-cc) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-cc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-cc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-cd) (sRet ())
sim-ev (simB st-cd) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-cd) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-cd) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-cd) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-cd) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simB st-dc) (sRet ())
sim-ev (simB st-dc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simB st-dc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simB st-dc) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simB st-dc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simB st-dc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-aa) (sRet ())
sim-ev (simM1 st-aa) (sVis {at = _ , a} refl br) =
  LHS , lhs-second σa , subst (λ z → SimR z LHS) (just-injective br) (simC qD)
sim-ev (simM1 st-aa) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM1 st-aa) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM1 st-aa) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM1 st-aa) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-ab) (sRet ())
sim-ev (simM1 st-ab) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM1 st-ab) (sVis {at = _ , b} refl br) =
  LHS , lhs-second σb , subst (λ z → SimR z LHS) (just-injective br) (simC qbA)
sim-ev (simM1 st-ab) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM1 st-ab) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM1 st-ab) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-ba) (sRet ())
sim-ev (simM1 st-ba) (sVis {at = _ , a} refl br) =
  LHS , lhs-second σa , subst (λ z → SimR z LHS) (just-injective br) (simC qD′)
sim-ev (simM1 st-ba) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM1 st-ba) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM1 st-ba) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM1 st-ba) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-cc) (sRet ())
sim-ev (simM1 st-cc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM1 st-cc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM1 st-cc) (sVis {at = _ , c} refl br) =
  LHS , lhs-second σc , subst (λ z → SimR z LHS) (just-injective br) (simC qD′)
sim-ev (simM1 st-cc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM1 st-cc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-cd) (sRet ())
sim-ev (simM1 st-cd) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM1 st-cd) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM1 st-cd) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM1 st-cd) (sVis {at = _ , d} refl br) =
  LHS , lhs-second σd , subst (λ z → SimR z LHS) (just-injective br) (simC qdC)
sim-ev (simM1 st-cd) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM1 st-dc) (sRet ())
sim-ev (simM1 st-dc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM1 st-dc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM1 st-dc) (sVis {at = _ , c} refl br) =
  LHS , lhs-second σc , subst (λ z → SimR z LHS) (just-injective br) (simC qD)
sim-ev (simM1 st-dc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM1 st-dc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-aa) (sRet ())
sim-ev (simM2 st-aa) (sVis {at = _ , a} refl br) =
  LHS , lhs-second σa , subst (λ z → SimR z LHS) (just-injective br) (simC qD)
sim-ev (simM2 st-aa) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM2 st-aa) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM2 st-aa) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM2 st-aa) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-ab) (sRet ())
sim-ev (simM2 st-ab) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM2 st-ab) (sVis {at = _ , b} refl br) =
  LHS , lhs-second σb , subst (λ z → SimR z LHS) (just-injective br) (simC qbA)
sim-ev (simM2 st-ab) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM2 st-ab) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM2 st-ab) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-ba) (sRet ())
sim-ev (simM2 st-ba) (sVis {at = _ , a} refl br) =
  LHS , lhs-second σa , subst (λ z → SimR z LHS) (just-injective br) (simC qD′)
sim-ev (simM2 st-ba) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM2 st-ba) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM2 st-ba) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM2 st-ba) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-cc) (sRet ())
sim-ev (simM2 st-cc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM2 st-cc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM2 st-cc) (sVis {at = _ , c} refl br) =
  LHS , lhs-second σc , subst (λ z → SimR z LHS) (just-injective br) (simC qD′)
sim-ev (simM2 st-cc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM2 st-cc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-cd) (sRet ())
sim-ev (simM2 st-cd) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM2 st-cd) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM2 st-cd) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simM2 st-cd) (sVis {at = _ , d} refl br) =
  LHS , lhs-second σd , subst (λ z → SimR z LHS) (just-injective br) (simC qdC)
sim-ev (simM2 st-cd) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simM2 st-dc) (sRet ())
sim-ev (simM2 st-dc) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simM2 st-dc) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simM2 st-dc) (sVis {at = _ , c} refl br) =
  LHS , lhs-second σc , subst (λ z → SimR z LHS) (just-injective br) (simC qD)
sim-ev (simM2 st-dc) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simM2 st-dc) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simC qD) (sRet ())
sim-ev (simC qD) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simC qD) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simC qD) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simC qD) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simC qD) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simC qbA) (sRet ())
sim-ev (simC qbA) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simC qbA) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simC qbA) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simC qbA) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simC qbA) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simC qD′) (sRet ())
sim-ev (simC qD′) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simC qD′) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simC qD′) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simC qD′) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simC qD′) (sVis {at = _ , clunk} refl br) = case br of λ ()
sim-ev (simC qdC) (sRet ())
sim-ev (simC qdC) (sVis {at = _ , a} refl br) = case br of λ ()
sim-ev (simC qdC) (sVis {at = _ , b} refl br) = case br of λ ()
sim-ev (simC qdC) (sVis {at = _ , c} refl br) = case br of λ ()
sim-ev (simC qdC) (sVis {at = _ , d} refl br) = case br of λ ()
sim-ev (simC qdC) (sVis {at = _ , clunk} refl br) = case br of λ ()

-- OBLIGATION 2: every τ of the harness is matched by a (possibly empty) τ-run of LHS
sim-τ : ∀ {R L R′} → SimR R L → R ─[ τ ]─► R′
      → Σ[ L′ ∈ LProc ] (L ⟹⟨ [] ⟩ L′ × SimR R′ L′)
sim-τ (simE q) st with sy-τ-elim noτ-Cp noτ-Cp st
... | _ , _ , s1 , _ , _ = ⊥-elim (cp-off-no-clunk s1)
sim-τ (simB {q} {x} {q′} dst) st with syp-τ-elim st
... | inj₂ (_ , pev , _) = ⊥-elim (both-no-ev pev)
... | inj₁ (p′ , pτ , eq) with both-τ-inv pτ
...   | inj₁ e1 = LHSw x , ⟹-refl
                , subst (λ z → SimR z (LHSw x)) (sym (trans eq (cong (λ z → SyP z (just x)) e1))) (simM1 dst)
...   | inj₂ e2 = LHSw x , ⟹-refl
                , subst (λ z → SimR z (LHSw x)) (sym (trans eq (cong (λ z → SyP z (just x)) e2))) (simM2 dst)
sim-τ (simM1 dst) st with sy-τ-elim noτ-Cp noτ-Cp st
... | _ , _ , _ , s2 , _ = ⊥-elim (cp-off-no-clunk s2)
sim-τ (simM2 dst) st with sy-τ-elim noτ-Cp noτ-Cp st
... | _ , _ , s1 , _ , _ = ⊥-elim (cp-off-no-clunk s1)
sim-τ (simC q) st with sy-τ-elim noτ-Cp noτ-Cp st
... | _ , _ , s1 , s2 , eq =
      LHS , ⟹-refl
    , subst (λ z → SimR z LHS)
        (sym (trans eq (cong₂ (λ u v → Sy u v nothing) (cp-clk-clunk-inv s1) (cp-clk-clunk-inv s2))))
        (simE q)

-- OBLIGATION 3: every stable refusal of the harness is a refusal LHS can reach
sim-ref : ∀ {R L} {X : Event√ (⊤poly {lzero}) → Set} → SimR R L → Refuses R X
        → Σ[ L′ ∈ LProc ] (L ⟹⟨ [] ⟩ L′ × Refuses L′ X)
sim-ref (simE q) rf = STOP , ⟹-τ LHS-τ-stop ⟹-refl , STOP-refuses
sim-ref (simC q) rf = ⊥-elim (stable-no-τ (proj₁ rf) (cc-τ q))
sim-ref (simB dst) rf = ⊥-elim (stable-no-τ (proj₁ rf) (syp-τ both-τL))
sim-ref {X = X} (simM1 st-aa) rf = LHSw σa , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σa) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-aa))
sim-ref {X = X} (simM1 st-ab) rf = LHSw σb , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σb) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-ab))
sim-ref {X = X} (simM1 st-ba) rf = LHSw σa , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σa) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-ba))
sim-ref {X = X} (simM1 st-cc) rf = LHSw σc , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σc) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-cc))
sim-ref {X = X} (simM1 st-cd) rf = LHSw σd , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σd) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-cd))
sim-ref {X = X} (simM1 st-dc) rf = LHSw σc , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σc) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m1-offers st-dc))
sim-ref {X = X} (simM2 st-aa) rf = LHSw σa , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σa) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-aa))
sim-ref {X = X} (simM2 st-ab) rf = LHSw σb , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σb) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-ab))
sim-ref {X = X} (simM2 st-ba) rf = LHSw σa , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σa) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-ba))
sim-ref {X = X} (simM2 st-cc) rf = LHSw σc , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σc) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-cc))
sim-ref {X = X} (simM2 st-cd) rf = LHSw σd , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σd) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-cd))
sim-ref {X = X} (simM2 st-dc) rf = LHSw σc , ⟹-refl , (λ i y → refl)
  , (λ e Xe off → proj₂ rf (sigEv σc) (subst X (LHSw-offer-inv (proj₂ off)) Xe) (m2-offers st-dc))

-- prepending a τ-only run to a run
⟹-preτ : ∀ {p q r : LProc} {s : List (Event√ (⊤poly {lzero}))}
       → p ⟹⟨ [] ⟩ q → q ⟹⟨ s ⟩ r → p ⟹⟨ s ⟩ r
⟹-preτ ⟹-refl t = t
⟹-preτ (⟹-τ st rest) t = ⟹-τ st (⟹-preτ rest t)

-- prepending a single-event run to a run
⟹-preev : ∀ {p q r : LProc} {e : Event√ (⊤poly {lzero})} {s : List (Event√ (⊤poly {lzero}))}
        → p ⟹⟨ e ∷ [] ⟩ q → q ⟹⟨ s ⟩ r → p ⟹⟨ e ∷ s ⟩ r
⟹-preev (⟹-τ st rest) t = ⟹-τ st (⟹-preev rest t)
⟹-preev (⟹-ev st rest) t = ⟹-ev st (⟹-preτ rest t)

-- appending a τ-only run to a run
⟹-postτ : ∀ {p q r : LProc} {s : List (Event√ (⊤poly {lzero}))}
        → p ⟹⟨ s ⟩ q → q ⟹⟨ [] ⟩ r → p ⟹⟨ s ⟩ r
⟹-postτ ⟹-refl t = t
⟹-postτ (⟹-τ st rest) t = ⟹-τ st (⟹-postτ rest t)
⟹-postτ (⟹-ev st rest) t = ⟹-ev st (⟹-postτ rest t)

-- the simulation lifts from single steps to whole runs
sim-run : ∀ {R L s R′} → SimR R L → R ⟹⟨ s ⟩ R′
        → Σ[ L′ ∈ LProc ] (L ⟹⟨ s ⟩ L′ × SimR R′ L′)
sim-run sim ⟹-refl = _ , ⟹-refl , sim
sim-run sim (⟹-τ step rest) with sim-τ sim step
... | L′ , lr , sim′ with sim-run sim′ rest
...   | L″ , lr′ , sim″ = L″ , ⟹-preτ lr lr′ , sim″
sim-run sim (⟹-ev step rest) with sim-ev sim step
... | L′ , lr , sim′ with sim-run sim′ rest
...   | L″ , lr′ , sim″ = L″ , ⟹-preev lr lr′ , sim″

-- LHS [F= RHS(D): every failure of the harness is a failure of the specification
lazic-D : LHS ⊑F RHS (DP qD)
lazic-D s X (P′ , run , rf) with sim-run (simE qD) run
... | L′ , lr , sim′ with sim-ref sim′ rf
...   | L″ , lr′ , rf′ = L″ , ⟹-postτ lr lr′ , rf′

------------------------------------------------------------------------------------
-- §B-cal.  The CALIBRATION.
--
-- Lazić's construction is only worth anything if its verdict AGREES with the direct
-- notion of determinism.  It does, on all three subjects: each pair below holds the
-- direct verdict and the Lazić verdict at the same polarity.  Without this the three
-- refinement checks would be three isolated facts about three particular processes.
------------------------------------------------------------------------------------

-- D: deterministic, and LHS [F= RHS(D) holds
cal-D : Deterministic (DP qD) × (LHS ⊑F RHS (DP qD))
cal-D = D-det , lazic-D

-- ND: not deterministic, and LHS [F= RHS(ND) fails
cal-ND : (¬ Deterministic NDp) × (¬ (LHS ⊑F RHS NDp))
cal-ND = ND-nondet , lazic-ND

-- ND2: not deterministic, and LHS [F= RHS(ND2) fails
cal-ND2 : (¬ Deterministic ND2p) × (¬ (LHS ⊑F RHS ND2p))
cal-ND2 = ND2-nondet , lazic-ND2
