{-# OPTIONS --guardedness #-}

-- UCS chapter 5: ncopy — chaining COPY cells is an N-place buffer (ncopyh.csp,
-- Bill Roscoe; source fdr-examples/ucs/chapter05/ncopyh.csp).  Reduced N = 2,
-- T = Bool.  Two cells COPY(0),COPY(1) over channels c.0,c.1,c.2; the alphabetised
-- parallel synchronises on the shared internal c.1, which is HIDDEN; the result is
-- a 2-place buffer:  assert Spec [T= CCH  and  CCH [T= Spec  (i.e. Spec =T CCH).
-- (The [FD= asserts are for Chapter 6; the ncopyl link-parallel variant is deferred.)

module CSP.Examples.UCS.Ch5.NCopy where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Nat using (ℕ; zero; suc)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. Event type: one channel event carrying (index , value).
data NEv : Set → Set where
  c : NEv (Fin 3 × Bool)

NEv-≟ : (x y : AnyTypes NEv) → Dec (x ≡ y)
NEv-≟ (_ , c) (_ , c) = yes refl

open import CSP.Operators NEv-≟
open EventSet

-- Fin 3 indices: fz / fs fz / fs (fs fz)  are  c.0 / c.1 / c.2.
SProc : Set₁
SProc = PTree NEv (ExtI NEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §2. The COPY cell (PINNED), parameterised by input/output channel index.
Cell  : Fin 3 → Fin 3 → SProc          -- ready: c.cin?x → holding x
Cell′ : Fin 3 → Fin 3 → Bool → SProc   -- holding x: c.cout!x → ready

-- ready at input channel cin: accept c.cin?x (any x), go to holding.
force (Cell cin cout) = react
  (λ where
     (_ , c) (i , x) → case i F≟ cin of λ where
         (yes _) → just (Cell′ cin cout x)
         (no  _) → nothing)
  ∅t

-- holding x: emit the PINNED output c.cout!x, return to ready.
force (Cell′ cin cout x) = react
  (λ where
     (_ , c) (i , y) → case i F≟ cout of λ where
         (yes _) → case y B≟ x of λ where
             (yes _) → just (Cell cin cout)
             (no  _) → nothing
         (no  _) → nothing)
  ∅t

------------------------------------------------------------------------------------
-- §3. Alphabets, the composed chain, hiding.
--   AC0 = {c.0, c.1}  (cell 0's alphabet); AC1 = {c.1, c.2} (cell 1's);
--   Hset = {c.1}      (the internal channel to hide).
-- Each is an EventSet whose .mem/.dec gate on the channel index `i` in the value
-- `(i , _)` (cf. ABP's adES/bcES shape, value-dependent here on the Fin 3 index).

AC0 AC1 Hset : EventSet
-- AC0: i ∈ {0,1}  (c.0, c.1)
AC0 .mem (_ , c) (fz , _)            = ⊤poly {lzero}
AC0 .mem (_ , c) (fs fz , _)         = ⊤poly {lzero}
AC0 .mem (_ , c) (fs (fs fz) , _)    = ⊥
AC0 .dec (_ , c) (fz , _)            = yes tt
AC0 .dec (_ , c) (fs fz , _)         = yes tt
AC0 .dec (_ , c) (fs (fs fz) , _)    = no (λ z → z)
-- AC1: i ∈ {1,2}  (c.1, c.2)
AC1 .mem (_ , c) (fz , _)            = ⊥
AC1 .mem (_ , c) (fs fz , _)         = ⊤poly {lzero}
AC1 .mem (_ , c) (fs (fs fz) , _)    = ⊤poly {lzero}
AC1 .dec (_ , c) (fz , _)            = no (λ z → z)
AC1 .dec (_ , c) (fs fz , _)         = yes tt
AC1 .dec (_ , c) (fs (fs fz) , _)    = yes tt
-- Hset: i = 1  (c.1)
Hset .mem (_ , c) (fz , _)           = ⊥
Hset .mem (_ , c) (fs fz , _)        = ⊤poly {lzero}
Hset .mem (_ , c) (fs (fs fz) , _)   = ⊥
Hset .dec (_ , c) (fz , _)           = no (λ z → z)
Hset .dec (_ , c) (fs fz , _)        = yes tt
Hset .dec (_ , c) (fs (fs fz) , _)   = no (λ z → z)

-- `_⟦_∥_⟧_` is the product-return alphabetised parallel (see CSP.Operators): it
-- returns `PTree NEv (ExtI NEv) (⊤poly × ⊤poly)`, NOT `SProc` (the plain `⊤poly`
-- CSP-instance return type) — cf. `NonBlockingRingTBuff`'s `BProc` for the same
-- pattern.  `CC2Proc` names that composed-pair type so `CC`/`CCH` can be stated
-- explicitly (a deviation from the brief's `CC : SProc`, forced by `_⟦_∥_⟧_`'s
-- signature; hiding `_∖_` is return-type generic so `CCH` keeps the same type).
CC2Proc : Set₁
CC2Proc = PTree NEv (ExtI NEv) (⊤poly {lzero} × ⊤poly {lzero})

CC : CC2Proc
CC = Cell fz (fs fz) ⟦ AC0 ∥ AC1 ⟧ Cell (fs fz) (fs (fs fz))

CCH : CC2Proc
CCH = CC ∖ Hset

------------------------------------------------------------------------------------
-- §4. The 2-place buffer spec (PINNED output).
-- `Buf s` holds the in-flight list `s` (head = next output).  Accept `c.0?x` when
-- `length s < 2`; output `c.2!(head s)` when `s` non-empty.
Buf : List Bool → CC2Proc
force (Buf [])            = react     -- empty: only accept on c.0
  (λ where (_ , c) (i , x) → case i F≟ fz of λ where
       (yes _) → just (Buf (x ∷ []))
       (no  _) → nothing)
  ∅t
force (Buf (x₀ ∷ []))     = react     -- one item x₀: accept c.0 (→ 2) or output c.2!x₀
  (λ where (_ , c) (i , y) → case i F≟ fz of λ where
       (yes _) → just (Buf (x₀ ∷ y ∷ []))
       (no  _) → case i F≟ (fs (fs fz)) of λ where
           (yes _) → case y B≟ x₀ of λ where
               (yes _) → just (Buf [])
               (no  _) → nothing
           (no  _) → nothing)
  ∅t
force (Buf (x₀ ∷ x₁ ∷ _)) = react     -- full (2 items): only output c.2!x₀
  (λ where (_ , c) (i , y) → case i F≟ (fs (fs fz)) of λ where
       (yes _) → case y B≟ x₀ of λ where
           (yes _) → just (Buf (x₁ ∷ []))
           (no  _) → nothing
       (no  _) → nothing)
  ∅t

Spec : CC2Proc
Spec = Buf []

------------------------------------------------------------------------------------
-- §B. ncopy-safe :  Spec ⊑T CCH   (the COPY-chain is a safe 2-place buffer).
--
-- The chain has exactly FOUR reachable shape-classes (× the Bool value(s)):
--   e     both cells ready                        contents []
--   l x   cell0 holds x, cell1 ready              contents (x ∷ [])   — τ-handoff only
--   r y   cell0 ready, cell1 holds y              contents (y ∷ [])
--   f x y both cells hold (x in 0, y in 1)        contents (y ∷ x ∷ [])
-- Transitions (verified below by the composite's `.force` reductions):
--   e   --c.0?x-->  l x         (kept visible, c.0 ∉ Hset)
--   l x --τ(c.1)--> r x         (HIDDEN c.1 handoff; contents [x] preserved)
--   r y --c.0?x-->  f x y        r y --c.2!y--> e
--   f x y --c.2!y--> l x
-- Matched by a weak simulation onto `Buf`: the τ handoff is matched by `Buf`
-- staying put (contents preserved); each visible c.0/c.2 by the matching `Buf` step.
------------------------------------------------------------------------------------

open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import Semantics.LTS        {E = NEv} {I = ExtI NEv}
open import Semantics.WeakBisim  {E = NEv} {I = ExtI NEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures   {E = NEv} {I = ExtI NEv} using (_⊑T_; traces)
open import Semantics.WeakSim    {E = NEv} {I = ExtI NEv} using (WSim; wsim→⊑T)
open import Semantics.BisimFromRel {E = NEv} {I = ExtI NEv}
open import CSP.Laws.AlphaParallel NEv-≟
  using ( αVisR; vSync; vSoloL; vSoloR; v√
        ; αpar-vis-step-inv; αpar-τ-step-inv; αpar-√-step-inv )
open import CSP.Laws.Traces.TraceLawsHide NEv-≟
  using ( Hide-ev-elim; Hide-τ-elim; HideevR; heV; he√; HideτR; hτP; hτH
        ; Hide-keep; Hide-hidden )

-- §B.1 Per-cell reachable states and their decode.  Each cell is `ready` (at its
-- input channel) or `holding v` (about to emit on its output channel).
data St0 : Set where rdy0 :        St0 ; hld0 : Bool → St0
data St1 : Set where rdy1 :        St1 ; hld1 : Bool → St1

nd0 : St0 → SProc
nd0 rdy0     = Cell fz (fs fz)          -- ready: c.0?x
nd0 (hld0 x) = Cell′ fz (fs fz) x       -- holding x: c.1!x

nd1 : St1 → SProc
nd1 rdy1     = Cell (fs fz) (fs (fs fz))     -- ready: c.1?y
nd1 (hld1 y) = Cell′ (fs fz) (fs (fs fz)) y  -- holding y: c.2!y

Chain : St0 → St1 → CC2Proc
Chain s0 s1 = nd0 s0 ⟦ AC0 ∥ AC1 ⟧ nd1 s1

-- §B.2 The reachable-config machinery (SHARED — reused by Task 3).
data Cfg : Set where
  e : Cfg
  l : Bool → Cfg
  r : Bool → Cfg
  f : Bool → Bool → Cfg

⟦_⟧ : Cfg → CC2Proc
⟦ e     ⟧ = Chain rdy0     rdy1     ∖ Hset
⟦ l x   ⟧ = Chain (hld0 x) rdy1     ∖ Hset
⟦ r y   ⟧ = Chain rdy0     (hld1 y) ∖ Hset
⟦ f x y ⟧ = Chain (hld0 x) (hld1 y) ∖ Hset

contents : Cfg → List Bool
contents e       = []
contents (l x)   = x ∷ []
contents (r y)   = y ∷ []
contents (f x y) = y ∷ x ∷ []          -- head = nearer-output cell (cell 1)

cc≡ : CCH ≡ ⟦ e ⟧
cc≡ = refl

-- §B.3 Event helper and per-cell stability / step-characterisation.
cL : (Fin 3 × Bool) → Event
cL p = evLabel (Fin 3 × Bool) c p

noRet0 : ∀ s0 {r} → PTree.force (nd0 s0) ≡ ret r → ⊥
noRet0 rdy0     () ; noRet0 (hld0 _) ()
noRet1 : ∀ s1 {r} → PTree.force (nd1 s1) ≡ ret r → ⊥
noRet1 rdy1     () ; noRet1 (hld1 _) ()

noτ0 : ∀ s0 {t′} → nd0 s0 ─[ τ ]─► t′ → ⊥
noτ0 rdy0     (sSil eq) = case eq of λ () ; noτ0 rdy0     (sTau refl br) = case br of λ ()
noτ0 (hld0 _) (sSil eq) = case eq of λ () ; noτ0 (hld0 _) (sTau refl br) = case br of λ ()
noτ1 : ∀ s1 {t′} → nd1 s1 ─[ τ ]─► t′ → ⊥
noτ1 rdy1     (sSil eq) = case eq of λ () ; noτ1 rdy1     (sTau refl br) = case br of λ ()
noτ1 (hld1 _) (sSil eq) = case eq of λ () ; noτ1 (hld1 _) (sTau refl br) = case br of λ ()

noComp√ : ∀ s0 s1 {r} → (Chain s0 s1) .force ≡ ret r → ⊥
noComp√ s0 s1 eqf = case αpar-√-step-inv eqf of λ { (v√ p0 _) → noRet0 s0 p0 }

-- Per-cell visible-step characterisations (cf. TBuff's `T0`/`T1` + `inv0`/`inv1`).
data T0 : St0 → SProc → Event → Set₁ where
  t0-in  : ∀ x → T0 rdy0     (nd0 (hld0 x)) (cL (fz , x))       -- accept c.0?x
  t0-out : ∀ x → T0 (hld0 x) (nd0 rdy0)     (cL (fs fz , x))    -- emit c.1!x
data T1 : St1 → SProc → Event → Set₁ where
  t1-in  : ∀ y → T1 rdy1     (nd1 (hld1 y)) (cL (fs fz , y))        -- accept c.1?y
  t1-out : ∀ y → T1 (hld1 y) (nd1 rdy1)     (cL (fs (fs fz) , y))   -- emit c.2!y

inv0 : ∀ s0 {t′ ev0} → nd0 s0 ─[ ev (evl ev0) ]─► t′ → T0 s0 t′ ev0
inv0 rdy0 (sVis {at = _ , c} {a = fz , x} refl br) =
  subst (λ z → T0 rdy0 z _) (just-injective br) (t0-in x)
inv0 rdy0 (sVis {at = _ , c} {a = fs fz , x} refl br) = case br of λ ()
inv0 rdy0 (sVis {at = _ , c} {a = fs (fs fz) , x} refl br) = case br of λ ()
inv0 (hld0 x) (sVis {at = _ , c} {a = fz , y} refl br) = case br of λ ()
inv0 (hld0 x) (sVis {at = _ , c} {a = fs fz , y} refl br) with y B≟ x
... | yes refl = subst (λ z → T0 (hld0 x) z _) (just-injective br) (t0-out x)
... | no  _    = case br of λ ()
inv0 (hld0 x) (sVis {at = _ , c} {a = fs (fs fz) , y} refl br) = case br of λ ()

inv1 : ∀ s1 {t′ ev1} → nd1 s1 ─[ ev (evl ev1) ]─► t′ → T1 s1 t′ ev1
inv1 rdy1 (sVis {at = _ , c} {a = fz , y} refl br) = case br of λ ()
inv1 rdy1 (sVis {at = _ , c} {a = fs fz , y} refl br) =
  subst (λ z → T1 rdy1 z _) (just-injective br) (t1-in y)
inv1 rdy1 (sVis {at = _ , c} {a = fs (fs fz) , y} refl br) = case br of λ ()
inv1 (hld1 y) (sVis {at = _ , c} {a = fz , z} refl br) = case br of λ ()
inv1 (hld1 y) (sVis {at = _ , c} {a = fs fz , z} refl br) = case br of λ ()
inv1 (hld1 y) (sVis {at = _ , c} {a = fs (fs fz) , z} refl br) with z B≟ y
... | yes refl = subst (λ w → T1 (hld1 y) w _) (just-injective br) (t1-out y)
... | no  _    = case br of λ ()

-- §B.4 `Buf` forward steps (its react offers reduce, so these hold by `refl`;
-- the c.2 output guard `y B≟ x₀` needs the Bool concrete, hence the split).
buf-c0-empty : ∀ x → Buf [] ─[ ev (evl (cL (fz , x))) ]─► Buf (x ∷ [])
buf-c0-empty x = sVis {at = _ , c} {a = fz , x} refl refl
buf-c0-one : ∀ y x → Buf (y ∷ []) ─[ ev (evl (cL (fz , x))) ]─► Buf (y ∷ x ∷ [])
buf-c0-one y x = sVis {at = _ , c} {a = fz , x} refl refl
buf-c2-one : ∀ y → Buf (y ∷ []) ─[ ev (evl (cL (fs (fs fz) , y))) ]─► Buf []
buf-c2-one true  = sVis {at = _ , c} {a = fs (fs fz) , true}  refl refl
buf-c2-one false = sVis {at = _ , c} {a = fs (fs fz) , false} refl refl
buf-c2-two : ∀ y x → Buf (y ∷ x ∷ []) ─[ ev (evl (cL (fs (fs fz) , y))) ]─► Buf (x ∷ [])
buf-c2-two true  x = sVis {at = _ , c} {a = fs (fs fz) , true}  refl refl
buf-c2-two false x = sVis {at = _ , c} {a = fs (fs fz) , false} refl refl


-- §B.5 The abstract weak-simulation relation.  Reachable configs are enumerated by
-- `Reach` (4 shape-classes × Bool values); `RR` keeps the per-cell states s0/s1
-- ABSTRACT (so the composite's `.force` stays stuck on `nd0 s0`/`nd1 s1`, which lets
-- the α-parallel inversion infer the alphabets AC0/AC1) — pinned only via the `Reach`
-- witness, which is split AFTER the inversion (cf. TokenRingTBuff's `Reach`/`RR`).
data Reach : St0 → St1 → List Bool → Set where
  reach-e :         Reach rdy0     rdy1     []
  reach-l : ∀ x   → Reach (hld0 x) rdy1     (x ∷ [])
  reach-r : ∀ y   → Reach rdy0     (hld1 y) (y ∷ [])
  reach-f : ∀ x y → Reach (hld0 x) (hld1 y) (y ∷ x ∷ [])

data RR : CC2Proc → CC2Proc → Set₁ where
  rr : ∀ s0 s1 cs → Reach s0 s1 cs → RR (Chain s0 s1 ∖ Hset) (Buf cs)

-- The `Reach`↔`Cfg` correspondence (documentation; `⟦_⟧`/`contents` agree with `RR`):
--   reach-e ↔ e,  reach-l x ↔ l x,  reach-r y ↔ r y,  reach-f x y ↔ f x y.

-- §B.6 Forward matching of a KEPT (observed) visible move of CCH.
fwdE : ∀ {p q} {lb : Event√ (⊤poly {lzero} × ⊤poly {lzero})} {p′}
     → RR p q → p ─[ ev lb ]─► p′
     → Σ[ q′ ∈ CC2Proc ] ((q ═[ ev lb ]═► q′) × RR p′ q′)
fwdE (rr s0 s1 cs rc) stp with Hide-ev-elim Hset (Chain s0 s1) stp
... | he√ eqf = ⊥-elim (noComp√ s0 s1 eqf)
... | heV P′ ¬c pstp with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
-- VISIBLE SYNC : the only sync channel is c.1 (hidden) → killed by ¬c, or the solo
-- node fires c.0 which is not in AC1.
...     | vSync pA pB p0s p1s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reach-l x
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬c tt)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSync pA pB p0s p1s | reach-f x y
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬c tt)
-- VISIBLE SOLO-LEFT : c.0?x (cell 0 ready) is kept → advances; c.1!x (cell 0 holding)
-- is in AC1, contradicting solo.
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = _ , wev τ*-refl (buf-c0-empty x) τ*-refl
                          , rr (hld0 x) rdy1 (x ∷ []) (reach-l x)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-l x
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = _ , wev τ*-refl (buf-c0-one y x) τ*-refl
                          , rr (hld0 x) (hld1 y) (y ∷ x ∷ []) (reach-f x y)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-f x y
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
-- VISIBLE SOLO-RIGHT : c.2!y (cell 1 holding) is kept → advances; c.1?y (cell 1 ready)
-- is in AC0, contradicting solo.
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s with rc
...       | reach-e with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-l x
      with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-r y
      with inv1 (hld1 y) p1s
...         | t1-out y = _ , wev τ*-refl (buf-c2-one y) τ*-refl , rr rdy0 rdy1 [] reach-e
fwdE (rr s0 s1 cs rc) stp | heV P′ ¬c pstp | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-f x y
      with inv1 (hld1 y) p1s
...         | t1-out y = _ , wev τ*-refl (buf-c2-two y x) τ*-refl
                          , rr (hld0 x) rdy1 (x ∷ []) (reach-l x)

-- §B.7 Forward matching of a τ move.  The only real τ is the HIDDEN c.1 handoff of
-- `l x` (→ r x), matched by `Buf` staying put (contents [x] preserved).
fwdT : ∀ {p q p′} → RR p q → p ─[ τ ]─► p′
     → Σ[ q′ ∈ CC2Proc ] ((q ═[ τ ]═► q′) × RR p′ q′)
fwdT (rr s0 s1 cs rc) stp with Hide-τ-elim Hset (Chain s0 s1) stp
-- the composite's own τ: both cells are stable, so impossible.
... | hτP P′ pτ refl with αpar-τ-step-inv pτ
...   | inj₁ (_ , t0τ , _) = ⊥-elim (noτ0 s0 t0τ)
...   | inj₂ (_ , t1τ , _) = ⊥-elim (noτ1 s1 t1τ)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl with ev-inv pstp
...   | v , τc , feq , br with αpar-vis-step-inv feq br
-- HIDDEN SOLO-LEFT : c.0 is kept (csat absurd); c.1!x is in AC1 (¬pB absurd).
...     | vSoloL pA ¬pB p0s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = case csat of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-l x
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = case csat of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloL pA ¬pB p0s | reach-f x y
      with inv0 (hld0 x) p0s
...         | t0-out x = ⊥-elim (¬pB tt)
-- HIDDEN SOLO-RIGHT : c.2 is kept (csat absurd); c.1?y is in AC0 (¬pA absurd).
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s with rc
...       | reach-e with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-l x
      with inv1 rdy1 p1s
...         | t1-in y = ⊥-elim (¬pA tt)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-r y
      with inv1 (hld1 y) p1s
...         | t1-out y = case csat of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSoloR ¬pA pB p1s | reach-f x y
      with inv1 (hld1 y) p1s
...         | t1-out y = case csat of λ ()
-- HIDDEN SYNC : the real c.1 handoff (l x → r x); the other configs cannot sync on c.1.
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s with rc
...       | reach-e with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reach-l x
      with inv0 (hld0 x) p0s | inv1 rdy1 p1s
...         | t0-out x | t1-in y = _ , wτ τ*-refl , rr rdy0 (hld1 y) (y ∷ []) (reach-r y)
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reach-r y
      with inv0 rdy0 p0s
...         | t0-in x = case pB of λ ()
fwdT (rr s0 s1 cs rc) stp | hτH P′ csat pstp refl | v , τc , feq , br | vSync pA pB p0s p1s | reach-f x y
      with inv0 (hld0 x) p0s | inv1 (hld1 y) p1s
...         | t0-out x | ()

module M = WSimFromRel RR fwdE fwdT

-- assert  Spec [T= CCH   (traces CCH ⊆ traces (Buf [])): the chain is a safe 2-place buffer.
-- Seed: CCH = Chain rdy0 rdy1 ∖ Hset = ⟦ e ⟧ (cc≡), Spec = Buf [] = Buf (contents e).
ncopy-safe : Spec ⊑T CCH
ncopy-safe = wsim→⊑T (M.rel→wsim (rr rdy0 rdy1 [] reach-e))

------------------------------------------------------------------------------------
-- §C. ncopy-live :  CCH ⊑T Spec   (the COPY-chain realises every 2-place-buffer trace).
--
-- The REVERSE weak simulation:  wsim→⊑T needs `WSim R Spec CCH` (Spec simulated by CCH),
-- so every `Buf` visible offer must be matched by a CCH WEAK step (τ*-padded).  We relate
-- each reachable `Buf` list to the CCH representative whose `contents` equal it, choosing
-- reps that DIRECTLY offer `Buf`'s moves — `e` / `r x` / `f y x` (NEVER `l x`, which only
-- offers the hidden handoff τ) — so any padding lands in the STEP TARGET, never a leading τ:
--     Buf []            ↦  ⟦ e ⟧
--     Buf (x ∷ [])      ↦  ⟦ r x ⟧          (offers both c.0?x' and c.2!x directly)
--     Buf (x ∷ y ∷ [])  ↦  ⟦ f y x ⟧        (contents (f y x) = x ∷ y ∷ [])
-- The two `Buf` moves whose successor is a singleton (`Buf [] --c.0?x-->` and
-- `Buf [x,y] --c.2!x-->`) reach an intermediate `l · ` config; a trailing HIDDEN c.1
-- handoff τ (`⟦ l z ⟧ ─[τ]─► ⟦ r z ⟧`) carries them to the chosen `r`-representative.

-- §C.1 CCH forward steps, built from the α-parallel step lemmas + Hide intro lemmas
-- (the CONVERSES of §B's `Hide-*-elim`/`αpar-*-step-inv`).  c.0 is solo-left & kept;
-- c.2 is solo-right & kept; c.1 is a sync AND hidden (→ the handoff τ).
cch-e-c0 : ∀ x → (⟦ e ⟧) ─[ ev (evl (cL (fz , x))) ]─► (⟦ l x ⟧)
cch-e-c0 x =
  Hide-keep Hset (Chain rdy0 rdy1) {a = fz , x} (λ ())
    (αpar-soloL-step {A = AC0} {B = AC1} {at = _ , c} {a = fz , x}
       tt (λ ()) refl refl refl)

cch-r-c0 : ∀ x x′ → (⟦ r x ⟧) ─[ ev (evl (cL (fz , x′))) ]─► (⟦ f x′ x ⟧)
cch-r-c0 x x′ =
  Hide-keep Hset (Chain rdy0 (hld1 x)) {a = fz , x′} (λ ())
    (αpar-soloL-step {A = AC0} {B = AC1} {at = _ , c} {a = fz , x′}
       tt (λ ()) refl refl refl)

cch-r-c2 : ∀ x → (⟦ r x ⟧) ─[ ev (evl (cL (fs (fs fz) , x))) ]─► (⟦ e ⟧)
cch-r-c2 true  =
  Hide-keep Hset (Chain rdy0 (hld1 true)) {a = fs (fs fz) , true} (λ ())
    (αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , true}
       (λ ()) tt refl refl refl)
cch-r-c2 false =
  Hide-keep Hset (Chain rdy0 (hld1 false)) {a = fs (fs fz) , false} (λ ())
    (αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , false}
       (λ ()) tt refl refl refl)

cch-f-c2 : ∀ y x → (⟦ f y x ⟧) ─[ ev (evl (cL (fs (fs fz) , x))) ]─► (⟦ l y ⟧)
cch-f-c2 y true  =
  Hide-keep Hset (Chain (hld0 y) (hld1 true)) {a = fs (fs fz) , true} (λ ())
    (αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , true}
       (λ ()) tt refl refl refl)
cch-f-c2 y false =
  Hide-keep Hset (Chain (hld0 y) (hld1 false)) {a = fs (fs fz) , false} (λ ())
    (αpar-soloR-step {A = AC0} {B = AC1} {at = _ , c} {a = fs (fs fz) , false}
       (λ ()) tt refl refl refl)

-- the hidden c.1 handoff:  ⟦ l x ⟧ ─[τ]─► ⟦ r x ⟧  (cell0 emits c.1!x, cell1 accepts).
handoff : ∀ x → (⟦ l x ⟧) ─[ τ ]─► (⟦ r x ⟧)
handoff true  =
  Hide-hidden Hset (Chain (hld0 true) rdy1) {a = fs fz , true} tt
    (αpar-sync-step {A = AC0} {B = AC1} {at = _ , c} {a = fs fz , true}
       tt tt refl refl refl refl)
handoff false =
  Hide-hidden Hset (Chain (hld0 false) rdy1) {a = fs fz , false} tt
    (αpar-sync-step {A = AC0} {B = AC1} {at = _ , c} {a = fs fz , false}
       tt tt refl refl refl refl)

-- §C.2 The reverse relation.  Each reachable `Buf` list is related to its chosen CCH
-- representative (contents-matching, `l`-free).  `p` (the simulated side) is the `Buf`
-- state; `q` (the simulator) is the CCH config.
data RR₂ : CC2Proc → CC2Proc → Set₁ where
  rr-e :         RR₂ (Buf [])            (⟦ e ⟧)
  rr-r : ∀ x   → RR₂ (Buf (x ∷ []))      (⟦ r x ⟧)
  rr-f : ∀ x y → RR₂ (Buf (x ∷ y ∷ []))  (⟦ f y x ⟧)

-- §C.3 Forward matching of a `Buf` visible move by a CCH weak step.
fwdE₂ : ∀ {p q} {lb : Event√ (⊤poly {lzero} × ⊤poly {lzero})} {p′}
      → RR₂ p q → p ─[ ev lb ]─► p′
      → Σ[ q′ ∈ CC2Proc ] ((q ═[ ev lb ]═► q′) × RR₂ p′ q′)
-- Buf [] : only accept c.0?x  (→ l x, then handoff τ to the rep r x).
fwdE₂ rr-e (sVis {at = _ , c} {a = fz , x} refl br) =
  ⟦ r x ⟧ , wev τ*-refl (cch-e-c0 x) (τ*-step (handoff x) τ*-refl)
          , subst (λ z → RR₂ z (⟦ r x ⟧)) (just-injective br) (rr-r x)
fwdE₂ rr-e (sVis {at = _ , c} {a = fs fz , x} refl br)      = case br of λ ()
fwdE₂ rr-e (sVis {at = _ , c} {a = fs (fs fz) , x} refl br) = case br of λ ()
fwdE₂ rr-e (sRet ())
-- Buf (x ∷ []) : accept c.0?y (→ f y x, strong) OR output c.2!x (→ e, strong).
fwdE₂ (rr-r x) (sVis {at = _ , c} {a = fz , y} refl br) =
  ⟦ f y x ⟧ , wev τ*-refl (cch-r-c0 x y) τ*-refl
            , subst (λ z → RR₂ z (⟦ f y x ⟧)) (just-injective br) (rr-f x y)
fwdE₂ (rr-r x) (sVis {at = _ , c} {a = fs fz , y} refl br) = case br of λ ()
fwdE₂ (rr-r x) (sVis {at = _ , c} {a = fs (fs fz) , y} refl br) with y B≟ x
... | yes refl = ⟦ e ⟧ , wev τ*-refl (cch-r-c2 x) τ*-refl
                       , subst (λ z → RR₂ z (⟦ e ⟧)) (just-injective br) rr-e
... | no  _    = case br of λ ()
fwdE₂ (rr-r x) (sRet ())
-- Buf (x ∷ y ∷ []) : only output c.2!x  (→ l y, then handoff τ to the rep r y).
fwdE₂ (rr-f x y) (sVis {at = _ , c} {a = fz , z} refl br)    = case br of λ ()
fwdE₂ (rr-f x y) (sVis {at = _ , c} {a = fs fz , z} refl br) = case br of λ ()
fwdE₂ (rr-f x y) (sVis {at = _ , c} {a = fs (fs fz) , z} refl br) with z B≟ x
... | yes refl = ⟦ r y ⟧ , wev τ*-refl (cch-f-c2 y x) (τ*-step (handoff y) τ*-refl)
                         , subst (λ w → RR₂ w (⟦ r y ⟧)) (just-injective br) (rr-r y)
... | no  _    = case br of λ ()
fwdE₂ (rr-f x y) (sRet ())

-- §C.4 `Buf` has no τ (its τ-map is `∅t`), so every τ-step is impossible.
fwdT₂ : ∀ {p q p′} → RR₂ p q → p ─[ τ ]─► p′
      → Σ[ q′ ∈ CC2Proc ] ((q ═[ τ ]═► q′) × RR₂ p′ q′)
fwdT₂ rr-e     (sSil ())
fwdT₂ rr-e     (sTau refl br)   = case br of λ ()
fwdT₂ (rr-r x) (sSil ())
fwdT₂ (rr-r x) (sTau refl br)   = case br of λ ()
fwdT₂ (rr-f x y) (sSil ())
fwdT₂ (rr-f x y) (sTau refl br) = case br of λ ()

module M₂ = WSimFromRel RR₂ fwdE₂ fwdT₂

-- assert  CCH [T= Spec   (traces (Buf []) ⊆ traces CCH): the chain realises the buffer.
-- Seed: Spec = Buf [] = Buf (contents e), CCH = ⟦ e ⟧ (cc≡).
ncopy-live : CCH ⊑T Spec
ncopy-live = wsim→⊑T (M₂.rel→wsim rr-e)

-- Combined:  Spec =T CCH  (both refinements).
ncopy-≡T : (Spec ⊑T CCH) × (CCH ⊑T Spec)
ncopy-≡T = ncopy-safe , ncopy-live
