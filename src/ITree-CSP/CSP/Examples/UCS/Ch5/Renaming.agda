{-# OPTIONS --guardedness #-}

-- UCS chapter 5: renaming (renaming.csp, Bill Roscoe; source
-- fdr-examples/ucs/chapter05/renaming.csp).  T = Bool.  Two parts:
--   §A  COPY[[left<-aa,right<-bb]] =T COPY'(aa,bb): injective renaming = relabel.
--       Modelled with the injective `renameInv` operator; RenCOPY = renameInv COPY inv.
--   §B  SPLIT :[deterministic] (holds) / SPLIT' :[deterministic] (fails):
--       SPLIT = in?x -> (x odd: out1.x else out2.x) -> SPLIT  (deterministic)
--       SPLIT' = in' -> (out1' -> SPLIT' |~| out2' -> SPLIT')  (nondeterministic)
-- Deferred (non-goals): the non-injective RenSPLIT =T SPLIT' (general fan-in rename
-- trace laws are unbuilt); the [FD= asserts (Chapter 6).

module CSP.Examples.UCS.Ch5.Renaming where

open import Level using (Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

import CSP.Operators

------------------------------------------------------------------------------------
-- §A. Injective renaming: COPY[[left<-aa,right<-bb]] =T COPY'(aa,bb).
------------------------------------------------------------------------------------

data REv : Set → Set where
  left right aa bb : REv Bool

REv-≟ : (x y : AnyTypes REv) → Dec (x ≡ y)
REv-≟ (_ , left)  (_ , left)  = yes refl
REv-≟ (_ , right) (_ , right) = yes refl
REv-≟ (_ , aa)    (_ , aa)    = yes refl
REv-≟ (_ , bb)    (_ , bb)    = yes refl
REv-≟ (_ , left)  (_ , right) = no (λ ())
REv-≟ (_ , left)  (_ , aa)    = no (λ ())
REv-≟ (_ , left)  (_ , bb)    = no (λ ())
REv-≟ (_ , right) (_ , left)  = no (λ ())
REv-≟ (_ , right) (_ , aa)    = no (λ ())
REv-≟ (_ , right) (_ , bb)    = no (λ ())
REv-≟ (_ , aa)    (_ , left)  = no (λ ())
REv-≟ (_ , aa)    (_ , right) = no (λ ())
REv-≟ (_ , aa)    (_ , bb)    = no (λ ())
REv-≟ (_ , bb)    (_ , left)  = no (λ ())
REv-≟ (_ , bb)    (_ , right) = no (λ ())
REv-≟ (_ , bb)    (_ , aa)    = no (λ ())

module OpsR = CSP.Operators REv-≟
open OpsR

RProc : Set₁
RProc = PTree REv (ExtI REv) (⊤poly {lzero})

-- injective, same-alphabet rename (identity ι), exactly as RenameSanity:
open import CSP.Rename {E₁ = REv} {E₂ = REv} (λ e → e) (λ e → just e) (λ _ → refl)

COPY  : RProc         -- left?x → COPYh x
COPYh : Bool → RProc  -- right!x → COPY
COPY'  : RProc        -- aa?x → COPYh' x
COPYh' : Bool → RProc -- bb!x → COPY'

force COPY = react
  (λ where (_ , left) x → just (COPYh x)
           (_ , right) _ → nothing ; (_ , aa) _ → nothing ; (_ , bb) _ → nothing)
  ∅t
force (COPYh x) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just COPY ; (no _) → nothing
           (_ , left) _ → nothing ; (_ , aa) _ → nothing ; (_ , bb) _ → nothing)
  ∅t
force COPY' = react
  (λ where (_ , aa) x → just (COPYh' x)
           (_ , left) _ → nothing ; (_ , right) _ → nothing ; (_ , bb) _ → nothing)
  ∅t
force (COPYh' x) = react
  (λ where (_ , bb) y → case y B≟ x of λ where (yes _) → just COPY' ; (no _) → nothing
           (_ , left) _ → nothing ; (_ , right) _ → nothing ; (_ , aa) _ → nothing)
  ∅t

-- target→source preimage: aa↦left, bb↦right, left/right↦nothing.
inv : (bt : AnyTypes REv) → proj₁ bt → Maybe ConcEvent₁
inv (_ , aa)    x = just ((Bool , left)  , x)
inv (_ , bb)    x = just ((Bool , right) , x)
inv (_ , left)  _ = nothing
inv (_ , right) _ = nothing

RenCOPY : RProc
RenCOPY = renameInv COPY inv

------------------------------------------------------------------------------------
-- §B. SPLIT (deterministic) vs SPLIT' (nondeterministic) — the determinism contrast.
------------------------------------------------------------------------------------

data DEv : Set → Set where
  inp out1 out2    : DEv Bool
  inp' out1' out2' : DEv ⊤

DEv-≟ : (x y : AnyTypes DEv) → Dec (x ≡ y)
DEv-≟ (_ , inp)    (_ , inp)    = yes refl
DEv-≟ (_ , out1)   (_ , out1)   = yes refl
DEv-≟ (_ , out2)   (_ , out2)   = yes refl
DEv-≟ (_ , inp')   (_ , inp')   = yes refl
DEv-≟ (_ , out1')  (_ , out1')  = yes refl
DEv-≟ (_ , out2')  (_ , out2')  = yes refl
DEv-≟ (_ , inp)    (_ , out1)   = no (λ ())
DEv-≟ (_ , inp)    (_ , out2)   = no (λ ())
DEv-≟ (_ , inp)    (_ , inp')   = no (λ ())
DEv-≟ (_ , inp)    (_ , out1')  = no (λ ())
DEv-≟ (_ , inp)    (_ , out2')  = no (λ ())
DEv-≟ (_ , out1)   (_ , inp)    = no (λ ())
DEv-≟ (_ , out1)   (_ , out2)   = no (λ ())
DEv-≟ (_ , out1)   (_ , inp')   = no (λ ())
DEv-≟ (_ , out1)   (_ , out1')  = no (λ ())
DEv-≟ (_ , out1)   (_ , out2')  = no (λ ())
DEv-≟ (_ , out2)   (_ , inp)    = no (λ ())
DEv-≟ (_ , out2)   (_ , out1)   = no (λ ())
DEv-≟ (_ , out2)   (_ , inp')   = no (λ ())
DEv-≟ (_ , out2)   (_ , out1')  = no (λ ())
DEv-≟ (_ , out2)   (_ , out2')  = no (λ ())
DEv-≟ (_ , inp')   (_ , inp)    = no (λ ())
DEv-≟ (_ , inp')   (_ , out1)   = no (λ ())
DEv-≟ (_ , inp')   (_ , out2)   = no (λ ())
DEv-≟ (_ , inp')   (_ , out1')  = no (λ ())
DEv-≟ (_ , inp')   (_ , out2')  = no (λ ())
DEv-≟ (_ , out1')  (_ , inp)    = no (λ ())
DEv-≟ (_ , out1')  (_ , out1)   = no (λ ())
DEv-≟ (_ , out1')  (_ , out2)   = no (λ ())
DEv-≟ (_ , out1')  (_ , inp')   = no (λ ())
DEv-≟ (_ , out1')  (_ , out2')  = no (λ ())
DEv-≟ (_ , out2')  (_ , inp)    = no (λ ())
DEv-≟ (_ , out2')  (_ , out1)   = no (λ ())
DEv-≟ (_ , out2')  (_ , out2)   = no (λ ())
DEv-≟ (_ , out2')  (_ , inp')   = no (λ ())
DEv-≟ (_ , out2')  (_ , out1')  = no (λ ())

module OpsD = CSP.Operators DEv-≟   -- qualified: avoids clashing with OpsR's ∅t/∅v/etc.

DProc : Set₁
DProc = PTree DEv (ExtI DEv) (⊤poly {lzero})

SPLIT  : DProc          -- inp?x → SPLITo x
SPLITo : Bool → DProc   -- (x ? out1!x : out2!x) → SPLIT
SPLIT'   : DProc        -- inp'? → SPLIT'br
SPLIT'br : DProc        -- (out1'? → SPLIT') ⊓ (out2'? → SPLIT')   [inlined react ∅v]
SPLIT'o1 : DProc        -- out1'? → SPLIT'
SPLIT'o2 : DProc        -- out2'? → SPLIT'

force SPLIT = react
  (λ where (_ , inp) x → just (SPLITo x)
           (_ , out1) _ → nothing ; (_ , out2) _ → nothing
           (_ , inp') _ → nothing ; (_ , out1') _ → nothing ; (_ , out2') _ → nothing)
  OpsD.∅t
-- x = true (odd) → out1!x ; x = false (even) → out2!x  (PINNED)
force (SPLITo x) = react
  (λ where
     (_ , out1) y → case x of λ where
         true  → case y B≟ x of λ where (yes _) → just SPLIT ; (no _) → nothing
         false → nothing
     (_ , out2) y → case x of λ where
         false → case y B≟ x of λ where (yes _) → just SPLIT ; (no _) → nothing
         true  → nothing
     (_ , inp) _ → nothing ; (_ , inp') _ → nothing
     (_ , out1') _ → nothing ; (_ , out2') _ → nothing)
  OpsD.∅t

force SPLIT' = react
  (λ where (_ , inp') _ → just SPLIT'br
           (_ , inp) _ → nothing ; (_ , out1) _ → nothing ; (_ , out2) _ → nothing
           (_ , out1') _ → nothing ; (_ , out2') _ → nothing)
  OpsD.∅t
-- inlined internal choice: fin-branch 0 → SPLIT'o1, fin-branch 1 → SPLIT'o2.
force SPLIT'br = react OpsD.∅v
  (λ where
     (_ , base _)   _                      → nothing
     (_ , pair _ _) _                      → nothing
     (_ , fin)      (lift fzero)           → just SPLIT'o1
     (_ , fin)      (lift (fsuc fzero))    → just SPLIT'o2
     (_ , fin)      (lift (fsuc (fsuc _))) → nothing)
force SPLIT'o1 = react
  (λ where (_ , out1') _ → just SPLIT'
           (_ , inp) _ → nothing ; (_ , out1) _ → nothing ; (_ , out2) _ → nothing
           (_ , inp') _ → nothing ; (_ , out2') _ → nothing)
  OpsD.∅t
force SPLIT'o2 = react
  (λ where (_ , out2') _ → just SPLIT'
           (_ , inp) _ → nothing ; (_ , out1) _ → nothing ; (_ , out2) _ → nothing
           (_ , inp') _ → nothing ; (_ , out1') _ → nothing)
  OpsD.∅t

------------------------------------------------------------------------------------
-- §A-proof.  RenCOPY = renameInv COPY inv  =T  COPY'   (injective rename = relabel).
--
-- `inv` is injective (each target aa/bb has a SINGLETON source preimage left/right,
-- no fan-in), so RenCOPY is a pure 1-1 relabel of COPY': NO τ is introduced.  Two
-- weak simulations (`WSimFromRel` + `wsim→⊑T`) discharge both trace inclusions.
--
-- How a RenCOPY step reduces (cf. RenameSanity check 4 `renameInv`).  RenCOPY's node
-- is  `react (λ bt b → rnFan _ _ (rnCollect vCOPY (invPreimg inv bt b)))
--             (extBranch _ _ ∅t)`.  The visible offer at target aa?x collects COPY's
-- `left` continuation through the singleton `invPreimg inv (Bool,aa) x`, so it reduces
-- (rnCollect → [COPYh x]; rnFan singleton) to  `just (renameInv (COPYh x) inv)` — the
-- offered continuation shape, no fan-in τ.  Likewise `renameInv (COPYh x) inv` offers
-- bb!x → `just (renameInv COPY inv)`.  The τ-part `extBranch _ _ ∅t` is everywhere
-- `nothing` (both `with extBwd` branches collapse: the `just` branch feeds `∅t`).
------------------------------------------------------------------------------------

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (sym; trans; subst)

open import Semantics.LTS        {E = REv} {I = ExtI REv}
open import Semantics.WeakBisim  {E = REv} {I = ExtI REv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures   {E = REv} {I = ExtI REv} using (_⊑T_; traces)
open import Semantics.WeakSim    {E = REv} {I = ExtI REv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = REv} {I = ExtI REv}

-- §A-proof.1  The τ-part of any `renameInv _ inv` node (whose inner τc is ∅t) is
-- everywhere `nothing`.  `extBranch` is stuck on the abstract index (its `with extBwd`
-- cannot commit), so we replay the split ourselves: BOTH branches collapse to nothing
-- (the `just eι₁` branch feeds `∅t (_ , eι₁) a = nothing` into `rnMc _ _ nothing`).
extBranch-empty : ∀ (i : AnyTypes (ExtI REv)) (a : proj₁ i)
                → extBranch (invRel inv) (invPreimg inv) (∅t {R = ⊤poly {lzero}}) i a ≡ nothing
extBranch-empty (A , eι) a with extBwd eι
... | just eι₁ = refl
... | nothing  = refl

renCOPY-noτ : ∀ {t′ : RProc} → renameInv COPY inv ─[ τ ]─► t′ → ⊥
renCOPY-noτ (sSil ())
renCOPY-noτ (sTau {i = i} {a = a} refl br) =
  case trans (sym (extBranch-empty i a)) br of λ ()

renHld-noτ : ∀ x {t′ : RProc} → renameInv (COPYh x) inv ─[ τ ]─► t′ → ⊥
renHld-noτ x (sSil ())
renHld-noτ x (sTau {i = i} {a = a} refl br) =
  case trans (sym (extBranch-empty i a)) br of λ ()

-- §A-proof.2  Step lemmas.  RenCOPY / renameInv (COPYh x) offers reduce as above;
-- the bb!x guard needs the Bool value concrete, hence the true/false split.
renCOPY-aa : ∀ x → renameInv COPY inv ─[ ev (evl (evLabel Bool aa x)) ]─► renameInv (COPYh x) inv
renCOPY-aa x = sVis {at = Bool , aa} {a = x} refl refl

renHold-bb : ∀ x → renameInv (COPYh x) inv ─[ ev (evl (evLabel Bool bb x)) ]─► renameInv COPY inv
renHold-bb true  = sVis {at = Bool , bb} {a = true}  refl refl
renHold-bb false = sVis {at = Bool , bb} {a = false} refl refl

copy'-aa : ∀ x → COPY' ─[ ev (evl (evLabel Bool aa x)) ]─► COPYh' x
copy'-aa x = sVis {at = Bool , aa} {a = x} refl refl

copyh'-bb : ∀ x → COPYh' x ─[ ev (evl (evLabel Bool bb x)) ]─► COPY'
copyh'-bb true  = sVis {at = Bool , bb} {a = true}  refl refl
copyh'-bb false = sVis {at = Bool , bb} {a = false} refl refl

------------------------------------------------------------------------------------
-- §A-proof.3  rename-safe : COPY' ⊑T RenCOPY.  Needs WSim R RenCOPY COPY' (RenCOPY
-- simulated by COPY').  Relation: renameInv COPY inv ↔ COPY', renameInv (COPYh x) inv
-- ↔ COPYh' x.  RenCOPY has no τ, so fwdT is discharged by `renCOPY-noτ`/`renHld-noτ`.
------------------------------------------------------------------------------------
data RelR : RProc → RProc → Set₁ where
  rel-rdy :        RelR (renameInv COPY inv)      COPY'
  rel-hld : ∀ x  → RelR (renameInv (COPYh x) inv) (COPYh' x)

fwdE₁ : ∀ {p q} {lb : Event√ (⊤poly {lzero})} {p′}
      → RelR p q → p ─[ ev lb ]─► p′
      → Σ[ q′ ∈ RProc ] ((q ═[ ev lb ]═► q′) × RelR p′ q′)
fwdE₁ rel-rdy (sVis {at = _ , left}  refl br) = case br of λ ()
fwdE₁ rel-rdy (sVis {at = _ , right} refl br) = case br of λ ()
fwdE₁ rel-rdy (sVis {at = _ , aa} {a = a} refl br) =
  COPYh' a , wev τ*-refl (copy'-aa a) τ*-refl
           , subst (λ z → RelR z (COPYh' a)) (just-injective br) (rel-hld a)
fwdE₁ rel-rdy (sVis {at = _ , bb}    refl br) = case br of λ ()
fwdE₁ rel-rdy (sRet ())
fwdE₁ (rel-hld x) (sVis {at = _ , left}  refl br) = case br of λ ()
fwdE₁ (rel-hld x) (sVis {at = _ , right} refl br) = case br of λ ()
fwdE₁ (rel-hld x) (sVis {at = _ , aa}    refl br) = case br of λ ()
fwdE₁ (rel-hld x) (sVis {at = _ , bb} {a = a} refl br) with a B≟ x
... | yes refl = COPY' , wev τ*-refl (copyh'-bb x) τ*-refl
                       , subst (λ z → RelR z COPY') (just-injective br) rel-rdy
... | no _     = case br of λ ()
fwdE₁ (rel-hld x) (sRet ())

fwdT₁ : ∀ {p q p′} → RelR p q → p ─[ τ ]─► p′
      → Σ[ q′ ∈ RProc ] ((q ═[ τ ]═► q′) × RelR p′ q′)
fwdT₁ rel-rdy     stp = ⊥-elim (renCOPY-noτ stp)
fwdT₁ (rel-hld x) stp = ⊥-elim (renHld-noτ x stp)

module M₁ = WSimFromRel RelR fwdE₁ fwdT₁

rename-safe : COPY' ⊑T RenCOPY
rename-safe = wsim→⊑T (M₁.rel→wsim rel-rdy)

------------------------------------------------------------------------------------
-- §A-proof.4  rename-live : RenCOPY ⊑T COPY'.  Needs WSim R COPY' RenCOPY (COPY'
-- simulated by RenCOPY).  COPY' has only ∅t as its τ-part, so fwdT is immediate.
------------------------------------------------------------------------------------
data RelR2 : RProc → RProc → Set₁ where
  rel2-rdy :        RelR2 COPY'      (renameInv COPY inv)
  rel2-hld : ∀ x  → RelR2 (COPYh' x) (renameInv (COPYh x) inv)

fwdE₂ : ∀ {p q} {lb : Event√ (⊤poly {lzero})} {p′}
      → RelR2 p q → p ─[ ev lb ]─► p′
      → Σ[ q′ ∈ RProc ] ((q ═[ ev lb ]═► q′) × RelR2 p′ q′)
fwdE₂ rel2-rdy (sVis {at = _ , aa} {a = a} refl br) =
  renameInv (COPYh a) inv , wev τ*-refl (renCOPY-aa a) τ*-refl
    , subst (λ z → RelR2 z (renameInv (COPYh a) inv)) (just-injective br) (rel2-hld a)
fwdE₂ rel2-rdy (sVis {at = _ , left}  refl br) = case br of λ ()
fwdE₂ rel2-rdy (sVis {at = _ , right} refl br) = case br of λ ()
fwdE₂ rel2-rdy (sVis {at = _ , bb}    refl br) = case br of λ ()
fwdE₂ rel2-rdy (sRet ())
fwdE₂ (rel2-hld x) (sVis {at = _ , bb} {a = a} refl br) with a B≟ x
... | yes refl = renameInv COPY inv , wev τ*-refl (renHold-bb x) τ*-refl
                         , subst (λ z → RelR2 z (renameInv COPY inv)) (just-injective br) rel2-rdy
... | no _     = case br of λ ()
fwdE₂ (rel2-hld x) (sVis {at = _ , left}  refl br) = case br of λ ()
fwdE₂ (rel2-hld x) (sVis {at = _ , right} refl br) = case br of λ ()
fwdE₂ (rel2-hld x) (sVis {at = _ , aa}    refl br) = case br of λ ()
fwdE₂ (rel2-hld x) (sRet ())

fwdT₂ : ∀ {p q p′} → RelR2 p q → p ─[ τ ]─► p′
      → Σ[ q′ ∈ RProc ] ((q ═[ τ ]═► q′) × RelR2 p′ q′)
fwdT₂ rel2-rdy     (sSil ())
fwdT₂ rel2-rdy     (sTau refl br)   = case br of λ ()
fwdT₂ (rel2-hld x) (sSil ())
fwdT₂ (rel2-hld x) (sTau refl br)   = case br of λ ()

module M₂ = WSimFromRel RelR2 fwdE₂ fwdT₂

rename-live : RenCOPY ⊑T COPY'
rename-live = wsim→⊑T (M₂.rel→wsim rel2-rdy)

------------------------------------------------------------------------------------
-- §A-proof.5  Combined:  RenCOPY =T COPY'  (injective renaming is a pure relabelling).
------------------------------------------------------------------------------------
rename-≡T : (COPY' ⊑T RenCOPY) × (RenCOPY ⊑T COPY')
rename-≡T = rename-safe , rename-live

------------------------------------------------------------------------------------
-- §B-proof.  split'-nondet : ¬ Deterministic SPLIT'  (the |~| internal choice
-- destroys determinism).  After the trace ⟨inp'⟩ the process can silently commit to
-- either SPLIT'o1 (offers only out1') or SPLIT'o2 (offers only out2').  So:
--   • ⟨inp', out2'⟩ IS a trace  (commit to o2, then out2');  AND
--   • after ⟨inp'⟩ the stable state SPLIT'o1 REFUSES out2'  (its out2'-branch is
--     nothing) — a stable refusal of a still-possible event.
-- These two witnesses contradict Deterministic (= no trace s ∷ʳ a together with a
-- stable state reached by s that refuses a).  Trace + failures level only — NO
-- FailuresDivergences, NO postulate.
------------------------------------------------------------------------------------

open import Data.List using (List; []; _∷_; _∷ʳ_)

import Semantics.LTS         {E = DEv} {I = ExtI DEv} as LD
import Semantics.Failures    {E = DEv} {I = ExtI DEv} as FD
import Semantics.Refusals    {E = DEv} {I = ExtI DEv} as RD
import Semantics.Determinism {E = DEv} {I = ExtI DEv} as DD

-- the two valueless (⊤) events used in the contradiction
inp'-ev out2'-ev : LD.Event√ (⊤poly {lzero})
inp'-ev  = LD.evl (LD.evLabel ⊤ inp' tt)
out2'-ev = LD.evl (LD.evLabel ⊤ out2' tt)

-- the visible / silent steps of the SPLIT' cycle
split'-inp' : SPLIT' LD.─[ LD.ev inp'-ev ]─► SPLIT'br
split'-inp' = LD.sVis {at = ⊤ , inp'} {a = tt} refl refl

br-o1 : SPLIT'br LD.─[ LD.τ ]─► SPLIT'o1       -- internal choice picks out1'-branch
br-o1 = LD.sTau {i = _ , fin {n = 2}} {a = lift fzero} refl refl

br-o2 : SPLIT'br LD.─[ LD.τ ]─► SPLIT'o2       -- internal choice picks out2'-branch
br-o2 = LD.sTau {i = _ , fin {n = 2}} {a = lift (fsuc fzero)} refl refl

o2-out2' : SPLIT'o2 LD.─[ LD.ev out2'-ev ]─► SPLIT'
o2-out2' = LD.sVis {at = ⊤ , out2'} {a = tt} refl refl

-- witness 1: ⟨inp', out2'⟩ is a trace of SPLIT'
split'-tr : FD.traces SPLIT' (inp'-ev ∷ out2'-ev ∷ [])
split'-tr = SPLIT'
          , FD.⟹-ev split'-inp' (FD.⟹-τ br-o2 (FD.⟹-ev o2-out2' FD.⟹-refl))

-- SPLIT'o1 offers only out1', so it does not offer out2' (its out2'-branch is nothing)
o1-no-out2' : ¬ RD.Offers SPLIT'o1 out2'-ev
o1-no-out2' (_ , LD.sVis refl br) = case br of λ ()

-- witness 2: after ⟨inp'⟩, the stable state SPLIT'o1 refuses out2'
split'-fl : FD.failures SPLIT' (inp'-ev ∷ []) (λ e → e ≡ out2'-ev)
split'-fl = SPLIT'o1
          , FD.⟹-ev split'-inp' (FD.⟹-τ br-o1 FD.⟹-refl)
          , (λ i a → refl)                       -- SPLIT'o1 is stable (τc = ∅t)
          , (λ { e refl → o1-no-out2' })          -- and refuses out2'

-- the two witnesses contradict Deterministic:  ⟨inp', out2'⟩ ∈ traces, yet SPLIT'o1
-- (reached by ⟨inp'⟩) stably refuses out2'.
split'-nondet : ¬ DD.Deterministic SPLIT'
split'-nondet det = det {s = inp'-ev ∷ []} {a = out2'-ev} split'-tr split'-fl

------------------------------------------------------------------------------------
-- §B-det.  split-det : Deterministic SPLIT  (SPLIT is deterministic).
--
-- SPLIT is τ-FREE (SPLIT / SPLITo x are `react … OpsD.∅t`) and every visible offer is
-- a partial FUNCTION of the event (inp?x → SPLITo x; SPLITo x's single output → SPLIT).
-- Hence the state reached by a visible run over `s` is UNIQUE (reached-state
-- determinacy).  If `s ∷ʳ a ∈ traces SPLIT`, the state reached by `s` OFFERS `a`, so a
-- stable state reached by `s` cannot REFUSE `a` — no failure `(s, {a})`.  Trace +
-- failures level only, NO FailuresDivergences, NO postulate.
------------------------------------------------------------------------------------

-- reachable states of SPLIT: SPLIT itself, and SPLITo x for x : Bool.
data Reach : DProc → Set₁ where
  r-split  :            Reach SPLIT
  r-splito : (x : Bool) → Reach (SPLITo x)

-- no τ from any reachable state (SPLIT / SPLITo x are `react … OpsD.∅t`)
reach-noτ : ∀ {Q t} → Reach Q → Q LD.─[ LD.τ ]─► t → ⊥
reach-noτ r-split      (LD.sSil ())
reach-noτ r-split      (LD.sTau refl br) = case br of λ ()
reach-noτ (r-splito x) (LD.sSil ())
reach-noτ (r-splito x) (LD.sTau refl br) = case br of λ ()

-- no √ (termination) from any reachable state (their `force` is a `react`, never `ret`)
reach-no√ : ∀ {Q r t} → Reach Q → Q LD.─[ LD.ev (LD.√ r) ]─► t → ⊥
reach-no√ r-split      (LD.sRet ())
reach-no√ (r-splito x) (LD.sRet ())

-- the target of any visible step from a reachable state is again reachable
reach-step : ∀ {Q e q} → Reach Q → Q LD.─[ LD.ev e ]─► q → Reach q
reach-step r-split (LD.sRet ())
reach-step r-split (LD.sVis {at = _ , inp}   {a = x} refl br) = subst Reach (just-injective br) (r-splito x)
reach-step r-split (LD.sVis {at = _ , out1}  refl br)         = case br of λ ()
reach-step r-split (LD.sVis {at = _ , out2}  refl br)         = case br of λ ()
reach-step r-split (LD.sVis {at = _ , inp'}  refl br)         = case br of λ ()
reach-step r-split (LD.sVis {at = _ , out1'} refl br)         = case br of λ ()
reach-step r-split (LD.sVis {at = _ , out2'} refl br)         = case br of λ ()
reach-step (r-splito true)  (LD.sRet ())
reach-step (r-splito true)  (LD.sVis {at = _ , out1} {a = y} refl br) with y B≟ true
... | yes _ = subst Reach (just-injective br) r-split
... | no  _ = case br of λ ()
reach-step (r-splito true)  (LD.sVis {at = _ , out2}  refl br) = case br of λ ()
reach-step (r-splito true)  (LD.sVis {at = _ , inp}   refl br) = case br of λ ()
reach-step (r-splito true)  (LD.sVis {at = _ , inp'}  refl br) = case br of λ ()
reach-step (r-splito true)  (LD.sVis {at = _ , out1'} refl br) = case br of λ ()
reach-step (r-splito true)  (LD.sVis {at = _ , out2'} refl br) = case br of λ ()
reach-step (r-splito false) (LD.sRet ())
reach-step (r-splito false) (LD.sVis {at = _ , out2} {a = y} refl br) with y B≟ false
... | yes _ = subst Reach (just-injective br) r-split
... | no  _ = case br of λ ()
reach-step (r-splito false) (LD.sVis {at = _ , out1}  refl br) = case br of λ ()
reach-step (r-splito false) (LD.sVis {at = _ , inp}   refl br) = case br of λ ()
reach-step (r-splito false) (LD.sVis {at = _ , inp'}  refl br) = case br of λ ()
reach-step (r-splito false) (LD.sVis {at = _ , out1'} refl br) = case br of λ ()
reach-step (r-splito false) (LD.sVis {at = _ , out2'} refl br) = case br of λ ()

-- FUNCTIONAL offer: same source, same visible event ⇒ same target (react injectivity).
offer-fun : ∀ {A e a} {q1 q2 Q : DProc}
          → Q LD.─[ LD.ev (LD.evl (LD.evLabel A e a)) ]─► q1
          → Q LD.─[ LD.ev (LD.evl (LD.evLabel A e a)) ]─► q2
          → q1 ≡ q2
offer-fun s1 s2 with LD.ev-inv s1 | LD.ev-inv s2
... | v , τc , eq1 , br1 | v' , τc' , eq2 , br2 with trans (sym eq1) eq2
...   | refl = just-injective (trans (sym br1) br2)

-- a single visible step from a reachable state is deterministic (√ ruled out; evl functional)
step-det : ∀ {e} {q1 q2 Q : DProc} → Reach Q
         → Q LD.─[ LD.ev e ]─► q1 → Q LD.─[ LD.ev e ]─► q2 → q1 ≡ q2
step-det {e = LD.evl x} r  s1 s2 = offer-fun s1 s2
step-det {e = LD.√ r′}  r  s1 s2 = ⊥-elim (reach-no√ r s1)

-- REACHED-STATE DETERMINACY (the crux): the state reached by a visible run over `s` is
-- unique.  Every ⟹ from a reachable state is τ-free, and each visible step is functional.
det : ∀ {Q s P′ P″} → Reach Q → Q FD.⟹⟨ s ⟩ P′ → Q FD.⟹⟨ s ⟩ P″ → P′ ≡ P″
det r FD.⟹-refl          FD.⟹-refl          = refl
det r FD.⟹-refl          (FD.⟹-τ step _)     = ⊥-elim (reach-noτ r step)
det r (FD.⟹-τ step _)     _                   = ⊥-elim (reach-noτ r step)
det r (FD.⟹-ev step1 _)   (FD.⟹-τ step _)     = ⊥-elim (reach-noτ r step)
det r (FD.⟹-ev step1 rest1) (FD.⟹-ev step2 rest2) =
  det (reach-step r step1) rest1
      (subst (λ z → z FD.⟹⟨ _ ⟩ _) (sym (step-det r step1 step2)) rest2)

-- snoc-decomposition: a run over `s ∷ʳ a` factors as a run over `s` reaching a state
-- that OFFERS `a` (τ-free, so no leading τ before the final `a`).
snoc-split : ∀ {a : LD.Event√ (⊤poly {lzero})} {Q P₀ : DProc} {s}
           → Reach Q → Q FD.⟹⟨ s ∷ʳ a ⟩ P₀
           → Σ[ P″ ∈ DProc ] (Q FD.⟹⟨ s ⟩ P″ × RD.Offers P″ a)
snoc-split {s = []}     r (FD.⟹-τ step _)    = ⊥-elim (reach-noτ r step)
snoc-split {s = []}     r (FD.⟹-ev step _)    = _ , FD.⟹-refl , (_ , step)
snoc-split {s = x ∷ s′} r (FD.⟹-τ step _)    = ⊥-elim (reach-noτ r step)
snoc-split {s = x ∷ s′} r (FD.⟹-ev step rest) with snoc-split (reach-step r step) rest
... | P″ , run , off = P″ , FD.⟹-ev step run , off

-- SPLIT is deterministic: no trace `s ∷ʳ a` coexists with a stable state reached by `s`
-- that refuses `a` — the reached-by-`s` state uniquely offers `a`.
split-det : DD.Deterministic SPLIT
split-det {s} {a} (P₀ , run) (P′ , runP′ , _ , refP′) with snoc-split {s = s} r-split run
... | P″ , runP″ , offP″ =
      refP′ a refl (subst (λ z → RD.Offers z a) (sym (det r-split runP′ runP″)) offP″)
