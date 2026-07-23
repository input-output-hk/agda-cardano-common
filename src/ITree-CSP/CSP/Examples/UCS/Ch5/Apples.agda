{-# OPTIONS --guardedness #-}

-- UCS chapter 5: apples (apples.csp, Bill Roscoe; source
-- fdr-examples/ucs/chapter05/apples.csp).  Many-way, context-dependent renaming:
--   apple is renamed to BOTH braeburn and cox ([[apple<-cox, apple<-braeburn]]),
--   and a regulator Reg (in parallel) picks which is enabled by whether adam/eve
--   happened last.  Reg enables braeburn before eve, cox after eve; People does
--   adam then eve once.  So braeburn all precede cox.
--     assert Before({braeburn},{cox}) [T= RelP   -- HOLDS
--     assert Before({cox},{braeburn}) [T= RelP   -- FAILS
-- MODELLING NOTE: the fan-OUT rename's trace laws are unbuilt (general relational
-- rename is "future" in TraceLawsRename).  Since Reg+People resolve the fan-out
-- into a clean phased behaviour, RelP is modelled DIRECTLY as that regulated
-- observable process; the literal P[[…]] [|…|] Reg composite is a NON-GOAL.
-- All events valueless; apple is renamed away (not an AEv constructor).

module CSP.Examples.UCS.Ch5.Apples where

open import Level renaming (zero to lzero)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. Event type + decidable equality; `AProc`.
------------------------------------------------------------------------------------

data AEv : Set → Set where
  adam eve braeburn cox : AEv ⊤

AEv-≟ : (x y : AnyTypes AEv) → Dec (x ≡ y)
AEv-≟ (_ , adam)     (_ , adam)     = yes refl
AEv-≟ (_ , eve)      (_ , eve)      = yes refl
AEv-≟ (_ , braeburn) (_ , braeburn) = yes refl
AEv-≟ (_ , cox)      (_ , cox)      = yes refl
AEv-≟ (_ , adam)     (_ , eve)      = no (λ ())
AEv-≟ (_ , adam)     (_ , braeburn) = no (λ ())
AEv-≟ (_ , adam)     (_ , cox)      = no (λ ())
AEv-≟ (_ , eve)      (_ , adam)     = no (λ ())
AEv-≟ (_ , eve)      (_ , braeburn) = no (λ ())
AEv-≟ (_ , eve)      (_ , cox)      = no (λ ())
AEv-≟ (_ , braeburn) (_ , adam)     = no (λ ())
AEv-≟ (_ , braeburn) (_ , eve)      = no (λ ())
AEv-≟ (_ , braeburn) (_ , cox)      = no (λ ())
AEv-≟ (_ , cox)      (_ , adam)     = no (λ ())
AEv-≟ (_ , cox)      (_ , eve)      = no (λ ())
AEv-≟ (_ , cox)      (_ , braeburn) = no (λ ())

open import CSP.Operators AEv-≟
open EventSet

AProc : Set₁
AProc = PTree AEv (ExtI AEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §2. `RelP` — the regulated observable behaviour.
--   Phases: 0a (before adam) — braeburn/adam ; 0b (after adam, before eve) —
--   braeburn/eve ; 1 (after eve) — cox only.  `braeburn` only in 0a/0b (before
--   `eve`); `cox` only in 1 (after `eve`); `adam` exactly once (0a→0b); `eve`
--   exactly once (0b→1).  Faithful to `Apples ||| (adam→eve→STOP)` gated by `Reg`.
------------------------------------------------------------------------------------

RelP0a : AProc   -- before adam: braeburn (apple-as-braeburn) or adam
RelP0b : AProc   -- after adam, before eve: braeburn or eve
RelP1  : AProc   -- after eve: cox (apple-as-cox)

force RelP0a = react
  (λ where
     (_ , braeburn) _ → just RelP0a
     (_ , adam)     _ → just RelP0b
     (_ , eve)      _ → nothing
     (_ , cox)      _ → nothing)
  ∅t
force RelP0b = react
  (λ where
     (_ , braeburn) _ → just RelP0b
     (_ , eve)      _ → just RelP1
     (_ , adam)     _ → nothing
     (_ , cox)      _ → nothing)
  ∅t
force RelP1 = react
  (λ where
     (_ , cox)      _ → just RelP1
     (_ , adam)     _ → nothing
     (_ , eve)      _ → nothing
     (_ , braeburn) _ → nothing)
  ∅t

RelP : AProc
RelP = RelP0a

------------------------------------------------------------------------------------
-- §3. `Before` / `RUN` specs.
--   BeforeBC = Before({braeburn},{cox}): any non-cox event → stay; cox → RUNac
--   (loops {adam,eve,cox}, refuses braeburn).
--   BeforeCB = Before({cox},{braeburn}): any non-braeburn → stay; braeburn → RUNaeb
--   (loops {adam,eve,braeburn}, refuses cox).
------------------------------------------------------------------------------------

BeforeBC RUNac BeforeCB RUNaeb : AProc

force BeforeBC = react
  (λ where
     (_ , adam)     _ → just BeforeBC
     (_ , eve)      _ → just BeforeBC
     (_ , braeburn) _ → just BeforeBC
     (_ , cox)      _ → just RUNac)
  ∅t
force RUNac = react
  (λ where
     (_ , adam)     _ → just RUNac
     (_ , eve)      _ → just RUNac
     (_ , cox)      _ → just RUNac
     (_ , braeburn) _ → nothing)
  ∅t
force BeforeCB = react
  (λ where
     (_ , adam)     _ → just BeforeCB
     (_ , eve)      _ → just BeforeCB
     (_ , cox)      _ → just BeforeCB
     (_ , braeburn) _ → just RUNaeb)
  ∅t
force RUNaeb = react
  (λ where
     (_ , adam)     _ → just RUNaeb
     (_ , eve)      _ → just RUNaeb
     (_ , braeburn) _ → just RUNaeb
     (_ , cox)      _ → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §B. apples-holds :  BeforeBC ⊑T RelP   (Before({braeburn},{cox}) [T= RelP).
--
--   assert Before({braeburn},{cox}) [T= RelP   -- HOLDS  (braeburn all precede cox).
--
-- `_⊑T_` is `traces RelP ⊆ traces BeforeBC`.  Via `wsim→⊑T : WSim R Q P → P ⊑T Q`,
-- with P = BeforeBC, Q = RelP, this needs a weak simulation `WSim R RelP BeforeBC`
-- (RelP simulated by BeforeBC), built by `WSimFromRel` from the 4-class relation `RR`
-- + `fwdE`/`fwdT`.  Both sides are τ-free `react … ∅t`, so every RelP visible move is
-- matched by a single strong BeforeBC/RUNac move (`wev τ*-refl <step> τ*-refl`).
--
-- The four `RR` classes (left = RelP-side, right = BeforeBC-side):
--   rr-0a  RelP0a ↔ BeforeBC   (before adam)
--   rr-0b  RelP0b ↔ BeforeBC   (after adam, before eve)
--   rr-1B  RelP1  ↔ BeforeBC   (RelP1 reached by eve, before its first cox)
--   rr-1R  RelP1  ↔ RUNac      (RelP1 after a cox — BeforeBC has moved to RUNac)
-- braeburn from RelP0a/RelP0b keeps BeforeBC put (BeforeBC offers braeburn), and the
-- FIRST cox drives BeforeBC into RUNac (which then also loops on cox) — so braeburn
-- never occurs after a cox, exactly matching BeforeBC's guarantee.
------------------------------------------------------------------------------------

open import Data.Product using (Σ; Σ-syntax; _×_; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Function.Base using (case_of_)
open import Relation.Binary.PropositionalEquality using (subst)

open import Semantics.LTS        {E = AEv} {I = ExtI AEv}
open import Semantics.WeakBisim  {E = AEv} {I = ExtI AEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures   {E = AEv} {I = ExtI AEv} using (_⊑T_; traces)
open import Semantics.WeakSim    {E = AEv} {I = ExtI AEv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = AEv} {I = ExtI AEv}

-- §B.1 The 4-class weak-simulation relation.
data RR : AProc → AProc → Set where
  rr-0a : RR RelP0a BeforeBC
  rr-0b : RR RelP0b BeforeBC
  rr-1B : RR RelP1  BeforeBC   -- RelP1 reached by eve, before its first cox
  rr-1R : RR RelP1  RUNac      -- RelP1 after a cox

-- §B.2 BeforeBC / RUNac visible step lemmas (all events valueless; the offers reduce,
-- so each holds by `refl refl`).  These are the moves matching RelP's steps.
bc-adam     : ∀ a → BeforeBC ─[ ev (evl (evLabel ⊤ adam     a)) ]─► BeforeBC
bc-adam     a = sVis {at = ⊤ , adam}     {a = a} refl refl
bc-eve      : ∀ a → BeforeBC ─[ ev (evl (evLabel ⊤ eve      a)) ]─► BeforeBC
bc-eve      a = sVis {at = ⊤ , eve}      {a = a} refl refl
bc-braeburn : ∀ a → BeforeBC ─[ ev (evl (evLabel ⊤ braeburn a)) ]─► BeforeBC
bc-braeburn a = sVis {at = ⊤ , braeburn} {a = a} refl refl
bc-cox      : ∀ a → BeforeBC ─[ ev (evl (evLabel ⊤ cox      a)) ]─► RUNac
bc-cox      a = sVis {at = ⊤ , cox}      {a = a} refl refl
ru-cox      : ∀ a → RUNac    ─[ ev (evl (evLabel ⊤ cox      a)) ]─► RUNac
ru-cox      a = sVis {at = ⊤ , cox}      {a = a} refl refl

-- §B.3 Forward matching of a RelP visible move by a BeforeBC weak step.
fwdE : ∀ {p q} {lb : Event√ (⊤poly {lzero})} {p′}
     → RR p q → p ─[ ev lb ]─► p′
     → Σ[ q′ ∈ AProc ] ((q ═[ ev lb ]═► q′) × RR p′ q′)
-- rr-0a (RelP0a): braeburn → RelP0a, adam → RelP0b; eve/cox are non-offers.
fwdE rr-0a (sVis {at = _ , braeburn} {a = a} refl br) =
  BeforeBC , wev τ*-refl (bc-braeburn a) τ*-refl
           , subst (λ z → RR z BeforeBC) (just-injective br) rr-0a
fwdE rr-0a (sVis {at = _ , adam} {a = a} refl br) =
  BeforeBC , wev τ*-refl (bc-adam a) τ*-refl
           , subst (λ z → RR z BeforeBC) (just-injective br) rr-0b
fwdE rr-0a (sVis {at = _ , eve} refl br) = case br of λ ()
fwdE rr-0a (sVis {at = _ , cox} refl br) = case br of λ ()
fwdE rr-0a (sRet ())
-- rr-0b (RelP0b): braeburn → RelP0b, eve → RelP1; adam/cox are non-offers.
fwdE rr-0b (sVis {at = _ , braeburn} {a = a} refl br) =
  BeforeBC , wev τ*-refl (bc-braeburn a) τ*-refl
           , subst (λ z → RR z BeforeBC) (just-injective br) rr-0b
fwdE rr-0b (sVis {at = _ , eve} {a = a} refl br) =
  BeforeBC , wev τ*-refl (bc-eve a) τ*-refl
           , subst (λ z → RR z BeforeBC) (just-injective br) rr-1B
fwdE rr-0b (sVis {at = _ , adam} refl br) = case br of λ ()
fwdE rr-0b (sVis {at = _ , cox} refl br) = case br of λ ()
fwdE rr-0b (sRet ())
-- rr-1B (RelP1 ↔ BeforeBC): cox → RelP1, matched by BeforeBC's cox → RUNac (first cox);
-- adam/eve/braeburn are non-offers of RelP1.
fwdE rr-1B (sVis {at = _ , cox} {a = a} refl br) =
  RUNac , wev τ*-refl (bc-cox a) τ*-refl
        , subst (λ z → RR z RUNac) (just-injective br) rr-1R
fwdE rr-1B (sVis {at = _ , adam} refl br)     = case br of λ ()
fwdE rr-1B (sVis {at = _ , eve} refl br)      = case br of λ ()
fwdE rr-1B (sVis {at = _ , braeburn} refl br) = case br of λ ()
fwdE rr-1B (sRet ())
-- rr-1R (RelP1 ↔ RUNac): cox → RelP1, matched by RUNac's cox → RUNac (later cox);
-- adam/eve/braeburn are non-offers of RelP1.
fwdE rr-1R (sVis {at = _ , cox} {a = a} refl br) =
  RUNac , wev τ*-refl (ru-cox a) τ*-refl
        , subst (λ z → RR z RUNac) (just-injective br) rr-1R
fwdE rr-1R (sVis {at = _ , adam} refl br)     = case br of λ ()
fwdE rr-1R (sVis {at = _ , eve} refl br)      = case br of λ ()
fwdE rr-1R (sVis {at = _ , braeburn} refl br) = case br of λ ()
fwdE rr-1R (sRet ())

-- §B.4 Forward matching of a τ move.  Every RelP-side state is `react … ∅t` (τ-free),
-- so every τ-step is impossible (`sSil` needs a `sil`; `sTau` feeds `∅t i a = nothing`).
fwdT : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ AProc ] ((q ═[ τ ]═► q′) × RR p′ q′)
fwdT rr-0a (sSil ())
fwdT rr-0a (sTau refl br) = case br of λ ()
fwdT rr-0b (sSil ())
fwdT rr-0b (sTau refl br) = case br of λ ()
fwdT rr-1B (sSil ())
fwdT rr-1B (sTau refl br) = case br of λ ()
fwdT rr-1R (sSil ())
fwdT rr-1R (sTau refl br) = case br of λ ()

module M = WSimFromRel RR fwdE fwdT

-- assert  Before({braeburn},{cox}) [T= RelP   (traces RelP ⊆ traces BeforeBC).
-- Seed: rr-0a : RR RelP0a BeforeBC = RR RelP BeforeBC  (RelP = RelP0a, Spec = BeforeBC).
apples-holds : BeforeBC ⊑T RelP
apples-holds = wsim→⊑T (M.rel→wsim rr-0a)

------------------------------------------------------------------------------------
-- §B-fails.  apples-fails :  ¬ (BeforeCB ⊑T RelP)   (Before({cox},{braeburn}) [T= RelP).
--
--   assert Before({cox},{braeburn}) [T= RelP   -- FAILS  (cox occurs AFTER braeburn).
--
-- `BeforeCB ⊑T RelP = ∀ s → traces RelP s → traces BeforeCB s`.  Instantiate at the
-- RelP trace  s = ⟨braeburn, adam, eve, cox⟩  (a genuine run of RelP: RelP0a --braeburn-->
-- RelP0a --adam--> RelP0b --eve--> RelP1 --cox--> RelP1).  If BeforeCB refined RelP, this
-- would be a trace of BeforeCB too — but it is NOT: BeforeCB's braeburn drives it into
-- RUNaeb, which then loops on adam/eve/braeburn and REFUSES cox (its cox-branch is
-- `nothing`).  So the final cox step from RUNaeb is impossible → ⊥.  BeforeCB / RUNaeb are
-- τ-free (`react … ∅t`), so the run is pure `⟹-ev` (any `⟹-τ` is killed by the no-τ
-- lemmas).  Trace level only — NO FailuresDivergences, NO postulate.
------------------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (sym)
open import Semantics.Failures {E = AEv} {I = ExtI AEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev)

-- the four valueless (⊤) events of the failing trace
braeburn-ev adam-ev eve-ev cox-ev : Event√ (⊤poly {lzero})
braeburn-ev = evl (evLabel ⊤ braeburn tt)
adam-ev     = evl (evLabel ⊤ adam     tt)
eve-ev      = evl (evLabel ⊤ eve      tt)
cox-ev      = evl (evLabel ⊤ cox      tt)

-- the four visible steps of the RelP run (each holds by `refl refl`, all events valueless)
st-br   : RelP0a ─[ ev braeburn-ev ]─► RelP0a
st-br   = sVis {at = ⊤ , braeburn} {a = tt} refl refl
st-adam : RelP0a ─[ ev adam-ev ]─► RelP0b
st-adam = sVis {at = ⊤ , adam}     {a = tt} refl refl
st-eve  : RelP0b ─[ ev eve-ev ]─► RelP1
st-eve  = sVis {at = ⊤ , eve}      {a = tt} refl refl
st-cox  : RelP1  ─[ ev cox-ev ]─► RelP1
st-cox  = sVis {at = ⊤ , cox}      {a = tt} refl refl

-- ⟨braeburn, adam, eve, cox⟩ IS a trace of RelP.
relp-tr : traces RelP (braeburn-ev ∷ adam-ev ∷ eve-ev ∷ cox-ev ∷ [])
relp-tr = RelP1
        , ⟹-ev st-br (⟹-ev st-adam (⟹-ev st-eve (⟹-ev st-cox ⟹-refl)))

-- BeforeCB / RUNaeb are τ-free (`react … ∅t`): no τ move is possible.
beforeCB-noτ : ∀ {t′ : AProc} → BeforeCB ─[ τ ]─► t′ → ⊥
beforeCB-noτ (sSil ())
beforeCB-noτ (sTau refl br) = case br of λ ()
runaeb-noτ : ∀ {t′ : AProc} → RUNaeb ─[ τ ]─► t′ → ⊥
runaeb-noτ (sSil ())
runaeb-noτ (sTau refl br) = case br of λ ()

-- Invert the BeforeCB run along the FIXED trace, phase by phase.  Forward declarations
-- (no `mutual`): each invRunaeb* strips τ via the no-τ lemma, then consumes its head
-- event landing back in RUNaeb — until the final cox from RUNaeb is refused (`case br`).
invRunaeb3 : ∀ {P′ : AProc} → RUNaeb ⟹⟨ cox-ev ∷ [] ⟩ P′ → ⊥
invRunaeb2 : ∀ {P′ : AProc} → RUNaeb ⟹⟨ eve-ev ∷ cox-ev ∷ [] ⟩ P′ → ⊥
invRunaeb  : ∀ {P′ : AProc} → RUNaeb ⟹⟨ adam-ev ∷ eve-ev ∷ cox-ev ∷ [] ⟩ P′ → ⊥
invBefore  : ∀ {P′ : AProc}
           → BeforeCB ⟹⟨ braeburn-ev ∷ adam-ev ∷ eve-ev ∷ cox-ev ∷ [] ⟩ P′ → ⊥

-- final cox from RUNaeb: RUNaeb's cox-branch is `nothing`, so `br : nothing ≡ just _`.
invRunaeb3 (⟹-τ pτ rest) = ⊥-elim (runaeb-noτ pτ)
invRunaeb3 (⟹-ev (sVis {at = _ , cox} refl br) _) = case br of λ ()
-- eve from RUNaeb → RUNaeb (its eve-branch is `just RUNaeb`).
invRunaeb2 (⟹-τ pτ rest) = ⊥-elim (runaeb-noτ pτ)
invRunaeb2 (⟹-ev (sVis {at = _ , eve} refl br) rest) =
  invRunaeb3 (subst (λ z → z ⟹⟨ cox-ev ∷ [] ⟩ _) (sym (just-injective br)) rest)
-- adam from RUNaeb → RUNaeb (its adam-branch is `just RUNaeb`).
invRunaeb (⟹-τ pτ rest) = ⊥-elim (runaeb-noτ pτ)
invRunaeb (⟹-ev (sVis {at = _ , adam} refl br) rest) =
  invRunaeb2 (subst (λ z → z ⟹⟨ eve-ev ∷ cox-ev ∷ [] ⟩ _) (sym (just-injective br)) rest)
-- braeburn from BeforeCB → RUNaeb (its braeburn-branch is `just RUNaeb`).
invBefore (⟹-τ pτ rest) = ⊥-elim (beforeCB-noτ pτ)
invBefore (⟹-ev (sVis {at = _ , braeburn} refl br) rest) =
  invRunaeb (subst (λ z → z ⟹⟨ adam-ev ∷ eve-ev ∷ cox-ev ∷ [] ⟩ _) (sym (just-injective br)) rest)

-- assert  Before({cox},{braeburn}) [T= RelP   FAILS: the RelP trace ⟨braeburn,…,cox⟩
-- is not a trace of BeforeCB (cox is refused after a braeburn).
apples-fails : ¬ (BeforeCB ⊑T RelP)
apples-fails ref with ref (braeburn-ev ∷ adam-ev ∷ eve-ev ∷ cox-ev ∷ []) relp-tr
... | (_ , run) = invBefore run
