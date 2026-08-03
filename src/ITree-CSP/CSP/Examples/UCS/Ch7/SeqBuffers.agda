{-# OPTIONS --guardedness #-}

-- UCS chapter 7 §7.1: sequential composition & iteration (section7-1.csp, Roscoe). T = Bool.
--   Iter(P) = P;Iter(P)
--   COPY = left?x -> right!x -> COPY                     ;  COPY ≈FD Iter(left?x->right!x->SKIP)
--   TB = left?x -> TB'(x) ; TB'(x) = right!x->SKIP [] left?y->right!x->TB'(y)
--   IterBuff2 = Iter(TB) ; BN(N,s) = #s<N & left?x->BN(N,s^<x>) [] #s>0 & right!head->BN(N,tail)
--                                                         ;  IterBuff2 ≈FD BN(2,<>)
-- Iter = loop0 (sil-guarded loop-back). The loop-back τ ⇒ weak/DR (not strong) bisim.

module CSP.Examples.UCS.Ch7.SeqBuffers where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using () renaming (_<?_ to _ℕ<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. Event type + decidable equality.
data BEv : Set → Set where
  left right : BEv Bool

BEv-≟ : (x y : AnyTypes BEv) → Dec (x ≡ y)
BEv-≟ (_ , left)  (_ , left)  = yes refl
BEv-≟ (_ , right) (_ , right) = yes refl
BEv-≟ (_ , left)  (_ , right) = no (λ ())
BEv-≟ (_ , right) (_ , left)  = no (λ ())

open import CSP.Operators BEv-≟
open EventSet

BProc : Set₁
BProc = PTree BEv (ExtI BEv) (⊤poly {lzero})

------------------------------------------------------------------------------------
-- §2. COPY (PINNED output) — templated off Ch6/Buffers.agda.
COPY    : BProc
COPYout : Bool → BProc

force COPY = react
  (λ where (_ , left) x → just (COPYout x)
           (_ , right) _ → nothing)
  ∅t
force (COPYout x) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just COPY ; (no _) → nothing
           (_ , left) _ → nothing)
  ∅t

-- Iter(left?x -> right!x -> SKIP)
copyBody    : BProc                 -- = left?x -> right!x -> SKIP
copyBodyOut : Bool → BProc

force copyBody = react
  (λ where (_ , left) x → just (copyBodyOut x)
           (_ , right) _ → nothing)
  ∅t
force (copyBodyOut x) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just Skip ; (no _) → nothing
           (_ , left) _ → nothing)
  ∅t

IterCOPY : BProc
IterCOPY = loop0 copyBody

------------------------------------------------------------------------------------
-- §3. TB / IterBuff2 — the stable (non-nondeterministic) sliding buffer body.
--   TB = left?x -> TB'(x) ; TB'(x) = right!x->SKIP [] left?y->right!x->TB'(y)
TB     : BProc                       -- TB  = left?x -> TB'(x)
TBhold : Bool → BProc                -- TB'(x) = right!x->SKIP [] left?y->right!x->TB'(y)
TBout  : Bool → Bool → BProc         -- right!x -> TB'(y)  (the inner accept-then-output)

force TB = react
  (λ where (_ , left) x → just (TBhold x)
           (_ , right) _ → nothing)
  ∅t
force (TBhold x) = react
  (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just Skip ; (no _) → nothing
           (_ , left) y → just (TBout x y))
  ∅t
force (TBout x y) = react              -- right!x -> TB'(y)
  (λ where (_ , right) z → case z B≟ x of λ where (yes _) → just (TBhold y) ; (no _) → nothing
           (_ , left) _ → nothing)
  ∅t

IterBuff2 : BProc
IterBuff2 = loop0 TB

------------------------------------------------------------------------------------
-- §4. BN(N,s) — the DETERMINISTIC section7-1 guarded buffer.
--   BN(N,s): #s<N & left?x -> BN(N,s^<x>)  []  #s>0 & right!head(s) -> BN(N,tail(s))
-- The not-full non-empty state is a plain STABLE □ node (no τ-branches) — unlike the
-- ch6 most-nondeterministic BUFN (which had a fused STOP/accept sliding node).
BN : ℕ → List Bool → BProc

force (BN n []) = react              -- empty: #s>0 fails ⇒ only left (if 0<n)
  (λ where (_ , left) x → just (BN n (x ∷ []))
           (_ , right) _ → nothing)
  ∅t
force (BN n (x ∷ cs)) with length (x ∷ cs) ℕ<? n
... | yes _ = react                  -- NOT full: offer BOTH right!x (head) and left?y (stable □)
      (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BN n cs) ; (no _) → nothing
               (_ , left) y → just (BN n ((x ∷ cs) ∷ʳ y)))
      ∅t
... | no  _ = react                  -- FULL: only right!x (head)
      (λ where (_ , right) y → case y B≟ x of λ where (yes _) → just (BN n cs) ; (no _) → nothing
               (_ , left) _ → nothing)
      ∅t

BN2 : BProc
BN2 = BN 2 []

------------------------------------------------------------------------------------
-- §G2. COPY ≈FD IterCOPY   (iteration = tail recursion).
--
-- IterCOPY = loop0 copyBody carries a once-per-cycle loop-back τ (the `sil` that
-- `iter-bind` inserts on `ret (inj₁ tt)`) that COPY lacks, so the two are NOT
-- strongly bisimilar — but they ARE divergence-respecting weak bisimilar: COPY
-- matches the loop-back τ by staying put, and the τ never runs forever (it is
-- always preceded by a visible `right`).  Route: hand-build a step-matching,
-- divergence-free `Rel` and feed it to `DRFromRel` (⇒ ≈DR), then `drbisim→≈FD`.
--
-- The IterCOPY reduction (Operators.agda ~1028-1051), with
--   wrap = λ a′ → Ret (inj₁ a′)   and   step = copyK  (definitionally):
--   I0     = IterCOPY                = iter-bind (copyBody      >>= wrap) copyK
--   Iout x = I0's `left x` residual  = iter-bind (copyBodyOut x >>= wrap) copyK
--   Iloop  = Iout x's `right x` res. = iter-bind (Skip          >>= wrap) copyK
-- and `force Iloop = sil I0` — the loop-back τ.  So the three IterCOPY states are:
--   I0     ─[left x]─► Iout x   (no τ)
--   Iout x ─[right x]─► Iloop   (no τ)
--   Iloop  ─[τ]─► I0            (sil)
------------------------------------------------------------------------------------

-- `Diverges` is hidden here because `Semantics.DRBisim` re-exports the very same LTS
-- `Diverges`; importing both unqualified would make the name ambiguous.
open import Semantics.LTS       {E = BEv} {I = ExtI BEv} hiding (Diverges)
open import Semantics.WeakBisim {E = BEv} {I = ExtI BEv}
  using (_═[_]═►_; wev; wτ; _─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.DRBisim             {E = BEv} {I = ExtI BEv} using (Diverges; _≈DR_)
open import Semantics.DRImpliesFD         {E = BEv} {I = ExtI BEv} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = BEv} {I = ExtI BEv} using (_≈FD_)
open import Semantics.BisimFromRel        {E = BEv} {I = ExtI BEv}

open import CSP.Laws.Traces.PrefixInversion BEv-≟
  using (sil-no-ev; sil-τ-uniq; divergesSil)

-- event labels
lblL lblR : Bool → Event√ (⊤poly {lzero})
lblL x = evl (evLabel Bool left  x)
lblR x = evl (evLabel Bool right x)

-- the IterCOPY intermediate states (definitional unfoldings of loop0 copyBody)
copyK : ⊤poly {lzero} → PTree BEv (ExtI BEv) (⊤poly {lzero} ⊎ ⊤poly {lzero})
copyK _ = copyBody >>= (λ a′ → Ret (inj₁ a′))

I0 : BProc
I0 = IterCOPY

Iout : Bool → BProc
Iout x = iter-bind (copyBodyOut x >>= (λ a′ → Ret (inj₁ a′))) copyK

Iloop : BProc
Iloop = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) copyK

------------------------------------------------------------------------------------
-- Concrete strong steps.
copy-in  : ∀ x → COPY      ─[ ev (lblL x) ]─► COPYout x
copy-in  x = sVis {at = Bool , left} {a = x} refl refl

copyout-fire : ∀ x → viewV (PTree.force (COPYout x)) (Bool , right) x ≡ just COPY
copyout-fire x with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

copy-out : ∀ x → COPYout x ─[ ev (lblR x) ]─► COPY
copy-out x = sVis {at = Bool , right} {a = x} refl (copyout-fire x)

iter-in  : ∀ x → I0     ─[ ev (lblL x) ]─► Iout x
iter-in  x = sVis {at = Bool , left} {a = x} refl refl

iterout-fire : ∀ x → viewV (PTree.force (Iout x)) (Bool , right) x ≡ just Iloop
iterout-fire x with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

iter-out : ∀ x → Iout x ─[ ev (lblR x) ]─► Iloop
iter-out x = sVis {at = Bool , right} {a = x} refl (iterout-fire x)

iter-loop : Iloop ─[ τ ]─► I0
iter-loop = sSil refl

------------------------------------------------------------------------------------
-- Step views (complete strong-step characterisations of each state).
COPY-ev : ∀ {l M} → COPY ─[ ev l ]─► M
        → Σ[ x ∈ Bool ] ((l ≡ lblL x) × (M ≡ COPYout x))
COPY-ev (sRet eq) = case eq of λ ()
COPY-ev (sVis {at = _ , left}  {a = x} refl br) = x , refl , sym (just-injective br)
COPY-ev (sVis {at = _ , right} {a = y} refl br) = case br of λ ()

COPYout-ev : ∀ x {l M} → COPYout x ─[ ev l ]─► M → (l ≡ lblR x) × (M ≡ COPY)
COPYout-ev x (sRet eq) = case eq of λ ()
COPYout-ev x (sVis {at = _ , left}  {a = y} refl br) = case br of λ ()
COPYout-ev x (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes q  = cong lblR q , sym (just-injective br)
... | no  ¬p = case br of λ ()

COPY-no-τ : ∀ {M} → COPY ─[ τ ]─► M → ⊥
COPY-no-τ (sSil eq)      = case eq of λ ()
COPY-no-τ (sTau refl br) = case br of λ ()

COPYout-no-τ : ∀ x {M} → COPYout x ─[ τ ]─► M → ⊥
COPYout-no-τ x (sSil eq)      = case eq of λ ()
COPYout-no-τ x (sTau refl br) = case br of λ ()

I0-ev : ∀ {l M} → I0 ─[ ev l ]─► M
      → Σ[ x ∈ Bool ] ((l ≡ lblL x) × (M ≡ Iout x))
I0-ev (sRet eq) = case eq of λ ()
I0-ev (sVis {at = _ , left}  {a = x} refl br) = x , refl , sym (just-injective br)
I0-ev (sVis {at = _ , right} {a = y} refl br) = case br of λ ()

Iout-ev : ∀ x {l M} → Iout x ─[ ev l ]─► M → (l ≡ lblR x) × (M ≡ Iloop)
Iout-ev x (sRet eq) = case eq of λ ()
Iout-ev x (sVis {at = _ , left}  {a = y} refl br) = case br of λ ()
Iout-ev x (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes q  = cong lblR q , sym (just-injective br)
... | no  ¬p = case br of λ ()

I0-no-τ : ∀ {M} → I0 ─[ τ ]─► M → ⊥
I0-no-τ (sSil eq)      = case eq of λ ()
I0-no-τ (sTau refl br) = case br of λ ()

Iout-no-τ : ∀ x {M} → Iout x ─[ τ ]─► M → ⊥
Iout-no-τ x (sSil eq)      = case eq of λ ()
Iout-no-τ x (sTau refl br) = case br of λ ()

Iloop-no-ev : ∀ {l M} → Iloop ─[ ev l ]─► M → ⊥
Iloop-no-ev stp = sil-no-ev refl stp

Iloop-τ : ∀ {M} → Iloop ─[ τ ]─► M → M ≡ I0
Iloop-τ stp = sil-τ-uniq refl stp

------------------------------------------------------------------------------------
-- Non-divergence:  every state is either τ-free, or reaches a τ-free state in one τ.
¬div-COPY : Diverges COPY → ⊥
¬div-COPY d = COPY-no-τ (d .Diverges.step)

¬div-COPYout : ∀ x → Diverges (COPYout x) → ⊥
¬div-COPYout x d = COPYout-no-τ x (d .Diverges.step)

¬div-I0 : Diverges I0 → ⊥
¬div-I0 d = I0-no-τ (d .Diverges.step)

¬div-Iout : ∀ x → Diverges (Iout x) → ⊥
¬div-Iout x d = Iout-no-τ x (d .Diverges.step)

¬div-Iloop : Diverges Iloop → ⊥
¬div-Iloop d = ¬div-I0 (divergesSil refl d)

------------------------------------------------------------------------------------
-- The relation:  COPY ↔ I0, COPYout x ↔ Iout x, and COPY ↔ Iloop (across the τ).
data Rel : BProc → BProc → Set₁ where
  rC  : Rel COPY I0
  rCO : ∀ x → Rel (COPYout x) (Iout x)
  rL  : Rel COPY Iloop

------------------------------------------------------------------------------------
-- The four step-matching obligations + the two non-divergence obligations.
R-fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′} → Rel p q → p ─[ ev l ]─► p′
       → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × Rel p′ q′)
R-fwdE rC stp with COPY-ev stp
... | x , refl , refl = Iout x , wev τ*-refl (iter-in x) τ*-refl , rCO x
R-fwdE (rCO x) stp with COPYout-ev x stp
... | refl , refl = Iloop , wev τ*-refl (iter-out x) τ*-refl , rL
R-fwdE rL stp with COPY-ev stp
... | x , refl , refl =
      Iout x , wev (τ*-step iter-loop τ*-refl) (iter-in x) τ*-refl , rCO x

R-fwdT : ∀ {p q p′} → Rel p q → p ─[ τ ]─► p′
       → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × Rel p′ q′)
R-fwdT rC       stp = ⊥-elim (COPY-no-τ stp)
R-fwdT (rCO x)  stp = ⊥-elim (COPYout-no-τ x stp)
R-fwdT rL       stp = ⊥-elim (COPY-no-τ stp)

R-bwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {q′} → Rel p q → q ─[ ev l ]─► q′
       → Σ[ p′ ∈ BProc ] ((p ═[ ev l ]═► p′) × Rel p′ q′)
R-bwdE rC stp with I0-ev stp
... | x , refl , refl = COPYout x , wev τ*-refl (copy-in x) τ*-refl , rCO x
R-bwdE (rCO x) stp with Iout-ev x stp
... | refl , refl = COPY , wev τ*-refl (copy-out x) τ*-refl , rL
R-bwdE rL stp = ⊥-elim (Iloop-no-ev stp)

R-bwdT : ∀ {p q q′} → Rel p q → q ─[ τ ]─► q′
       → Σ[ p′ ∈ BProc ] ((p ═[ τ ]═► p′) × Rel p′ q′)
R-bwdT rC      stp = ⊥-elim (I0-no-τ stp)
R-bwdT (rCO x) stp = ⊥-elim (Iout-no-τ x stp)
R-bwdT rL      stp with Iloop-τ stp
... | refl = COPY , wτ τ*-refl , rC

R-ndivL : ∀ {p q} → Rel p q → Diverges p → ⊥
R-ndivL rC      = ¬div-COPY
R-ndivL (rCO x) = ¬div-COPYout x
R-ndivL rL      = ¬div-COPY

R-ndivR : ∀ {p q} → Rel p q → Diverges q → ⊥
R-ndivR rC      = ¬div-I0
R-ndivR (rCO x) = ¬div-Iout x
R-ndivR rL      = ¬div-Iloop

------------------------------------------------------------------------------------
-- Assembly:  DRFromRel ⇒ ≈DR, then drbisim→≈FD ⇒ ≈FD.
module MCI = DRFromRel Rel R-fwdE R-fwdT R-bwdE R-bwdT R-ndivL R-ndivR

copy-iter-DR : COPY ≈DR IterCOPY
copy-iter-DR = MCI.rel→dr rC

copy-iter : COPY ≈FD IterCOPY
copy-iter = drbisim→≈FD copy-iter-DR

------------------------------------------------------------------------------------
-- §G3. IterBuff2 ≈FD BN2   (the 2-place Iter-buffer, via the ≈DR bridge).
--
-- IterBuff2 = loop0 TB and BN2 = BN 2 [] are both DETERMINISTIC 2-place buffers.
-- As in §G2, the `loop0` inserts a once-per-cycle loop-back τ (fired after the
-- `right` output flows through `Skip = Ret tt`) that BN2 lacks — so they are NOT
-- strongly bisimilar, but ARE divergence-respecting weak bisimilar.  The state
-- correspondence, across the loop-back τ (four states):
--   IB0     = IterBuff2                            ↔ BN 2 []          (offer left only)
--   IBhold x = iter-bind (TBhold x >>= wrap) TBK   ↔ BN 2 [x]  (1<2 ⇒ not full: right!x □ left?y)
--   IBout x y = iter-bind (TBout x y >>= wrap) TBK ↔ BN 2 [x,y] (¬2<2 ⇒ FULL: right!x only)
--   IBloop  = iter-bind (Skip >>= wrap) TBK        ↔ BN 2 []   (loop-back τ; `force IBloop = sil IB0`)
-- and  ((x∷[]) ∷ʳ y = x ∷ y ∷ [])  /  (tail (x ∷ y ∷ []) = y ∷ []).  The reductions
-- read off Operators.agda ~1028-1051 exactly as §G2 did for IterCOPY.
------------------------------------------------------------------------------------

-- the IterBuff2 intermediate states (definitional unfoldings of loop0 TB)
TBK : ⊤poly {lzero} → PTree BEv (ExtI BEv) (⊤poly {lzero} ⊎ ⊤poly {lzero})
TBK _ = TB >>= (λ a′ → Ret (inj₁ a′))

IB0 : BProc
IB0 = IterBuff2

IBhold : Bool → BProc
IBhold x = iter-bind (TBhold x >>= (λ a′ → Ret (inj₁ a′))) TBK

IBout : Bool → Bool → BProc
IBout x y = iter-bind (TBout x y >>= (λ a′ → Ret (inj₁ a′))) TBK

IBloop : BProc
IBloop = iter-bind (Skip >>= (λ a′ → Ret (inj₁ a′))) TBK

------------------------------------------------------------------------------------
-- Concrete strong steps — IterBuff2 side.
ib-in : ∀ x → IB0 ─[ ev (lblL x) ]─► IBhold x
ib-in x = sVis {at = Bool , left} {a = x} refl refl

ibhold-out-fire : ∀ x → viewV (PTree.force (IBhold x)) (Bool , right) x ≡ just IBloop
ibhold-out-fire x with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

ibhold-out : ∀ x → IBhold x ─[ ev (lblR x) ]─► IBloop
ibhold-out x = sVis {at = Bool , right} {a = x} refl (ibhold-out-fire x)

ibhold-in : ∀ x y → IBhold x ─[ ev (lblL y) ]─► IBout x y
ibhold-in x y = sVis {at = Bool , left} {a = y} refl refl

ibout-out-fire : ∀ x y → viewV (PTree.force (IBout x y)) (Bool , right) x ≡ just (IBhold y)
ibout-out-fire x y with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

ibout-out : ∀ x y → IBout x y ─[ ev (lblR x) ]─► IBhold y
ibout-out x y = sVis {at = Bool , right} {a = x} refl (ibout-out-fire x y)

ib-loop : IBloop ─[ τ ]─► IB0
ib-loop = sSil refl

------------------------------------------------------------------------------------
-- Concrete strong steps — BN side.
bn-in : ∀ x → BN 2 [] ─[ ev (lblL x) ]─► BN 2 (x ∷ [])
bn-in x = sVis {at = Bool , left} {a = x} refl refl

bnhold-out-fire : ∀ x → viewV (PTree.force (BN 2 (x ∷ []))) (Bool , right) x ≡ just (BN 2 [])
bnhold-out-fire x with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

bnhold-out : ∀ x → BN 2 (x ∷ []) ─[ ev (lblR x) ]─► BN 2 []
bnhold-out x = sVis {at = Bool , right} {a = x} refl (bnhold-out-fire x)

bnhold-in : ∀ x y → BN 2 (x ∷ []) ─[ ev (lblL y) ]─► BN 2 (x ∷ y ∷ [])
bnhold-in x y = sVis {at = Bool , left} {a = y} refl refl

bnout-out-fire : ∀ x y → viewV (PTree.force (BN 2 (x ∷ y ∷ []))) (Bool , right) x ≡ just (BN 2 (y ∷ []))
bnout-out-fire x y with x B≟ x
... | yes _  = refl
... | no  ¬p = ⊥-elim (¬p refl)

bnout-out : ∀ x y → BN 2 (x ∷ y ∷ []) ─[ ev (lblR x) ]─► BN 2 (y ∷ [])
bnout-out x y = sVis {at = Bool , right} {a = x} refl (bnout-out-fire x y)

------------------------------------------------------------------------------------
-- Step views — IterBuff2 side (complete strong-step characterisations).
IB0-ev : ∀ {l M} → IB0 ─[ ev l ]─► M
       → Σ[ x ∈ Bool ] ((l ≡ lblL x) × (M ≡ IBhold x))
IB0-ev (sRet eq) = case eq of λ ()
IB0-ev (sVis {at = _ , left}  {a = x} refl br) = x , refl , sym (just-injective br)
IB0-ev (sVis {at = _ , right} {a = y} refl br) = case br of λ ()

IBhold-ev : ∀ x {l M} → IBhold x ─[ ev l ]─► M
          → (Σ[ y ∈ Bool ] ((l ≡ lblL y) × (M ≡ IBout x y)))
          ⊎ ((l ≡ lblR x) × (M ≡ IBloop))
IBhold-ev x (sRet eq) = case eq of λ ()
IBhold-ev x (sVis {at = _ , left}  {a = y} refl br) = inj₁ (y , refl , sym (just-injective br))
IBhold-ev x (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes q  = inj₂ (cong lblR q , sym (just-injective br))
... | no  ¬p = case br of λ ()

IBout-ev : ∀ x y {l M} → IBout x y ─[ ev l ]─► M → (l ≡ lblR x) × (M ≡ IBhold y)
IBout-ev x y (sRet eq) = case eq of λ ()
IBout-ev x y (sVis {at = _ , left}  {a = z} refl br) = case br of λ ()
IBout-ev x y (sVis {at = _ , right} {a = z} refl br) with z B≟ x
... | yes q  = cong lblR q , sym (just-injective br)
... | no  ¬p = case br of λ ()

IB0-no-τ : ∀ {M} → IB0 ─[ τ ]─► M → ⊥
IB0-no-τ (sSil eq)      = case eq of λ ()
IB0-no-τ (sTau refl br) = case br of λ ()

IBhold-no-τ : ∀ x {M} → IBhold x ─[ τ ]─► M → ⊥
IBhold-no-τ x (sSil eq)      = case eq of λ ()
IBhold-no-τ x (sTau refl br) = case br of λ ()

IBout-no-τ : ∀ x y {M} → IBout x y ─[ τ ]─► M → ⊥
IBout-no-τ x y (sSil eq)      = case eq of λ ()
IBout-no-τ x y (sTau refl br) = case br of λ ()

IBloop-no-ev : ∀ {l M} → IBloop ─[ ev l ]─► M → ⊥
IBloop-no-ev stp = sil-no-ev refl stp

IBloop-τ : ∀ {M} → IBloop ─[ τ ]─► M → M ≡ IB0
IBloop-τ stp = sil-τ-uniq refl stp

------------------------------------------------------------------------------------
-- Step views — BN side.
BN2-ev : ∀ {l M} → BN 2 [] ─[ ev l ]─► M
       → Σ[ x ∈ Bool ] ((l ≡ lblL x) × (M ≡ BN 2 (x ∷ [])))
BN2-ev (sRet eq) = case eq of λ ()
BN2-ev (sVis {at = _ , left}  {a = x} refl br) = x , refl , sym (just-injective br)
BN2-ev (sVis {at = _ , right} {a = y} refl br) = case br of λ ()

BNhold-ev : ∀ x {l M} → BN 2 (x ∷ []) ─[ ev l ]─► M
          → (Σ[ y ∈ Bool ] ((l ≡ lblL y) × (M ≡ BN 2 (x ∷ y ∷ []))))
          ⊎ ((l ≡ lblR x) × (M ≡ BN 2 []))
BNhold-ev x (sRet eq) = case eq of λ ()
BNhold-ev x (sVis {at = _ , left}  {a = y} refl br) = inj₁ (y , refl , sym (just-injective br))
BNhold-ev x (sVis {at = _ , right} {a = y} refl br) with y B≟ x
... | yes q  = inj₂ (cong lblR q , sym (just-injective br))
... | no  ¬p = case br of λ ()

BNout-ev : ∀ x y {l M} → BN 2 (x ∷ y ∷ []) ─[ ev l ]─► M → (l ≡ lblR x) × (M ≡ BN 2 (y ∷ []))
BNout-ev x y (sRet eq) = case eq of λ ()
BNout-ev x y (sVis {at = _ , left}  {a = z} refl br) = case br of λ ()
BNout-ev x y (sVis {at = _ , right} {a = z} refl br) with z B≟ x
... | yes q  = cong lblR q , sym (just-injective br)
... | no  ¬p = case br of λ ()

BN2-no-τ : ∀ {M} → BN 2 [] ─[ τ ]─► M → ⊥
BN2-no-τ (sSil eq)      = case eq of λ ()
BN2-no-τ (sTau refl br) = case br of λ ()

BNhold-no-τ : ∀ x {M} → BN 2 (x ∷ []) ─[ τ ]─► M → ⊥
BNhold-no-τ x (sSil eq)      = case eq of λ ()
BNhold-no-τ x (sTau refl br) = case br of λ ()

BNout-no-τ : ∀ x y {M} → BN 2 (x ∷ y ∷ []) ─[ τ ]─► M → ⊥
BNout-no-τ x y (sSil eq)      = case eq of λ ()
BNout-no-τ x y (sTau refl br) = case br of λ ()

------------------------------------------------------------------------------------
-- Non-divergence.
¬div-IB0 : Diverges IB0 → ⊥
¬div-IB0 d = IB0-no-τ (d .Diverges.step)

¬div-IBhold : ∀ x → Diverges (IBhold x) → ⊥
¬div-IBhold x d = IBhold-no-τ x (d .Diverges.step)

¬div-IBout : ∀ x y → Diverges (IBout x y) → ⊥
¬div-IBout x y d = IBout-no-τ x y (d .Diverges.step)

¬div-IBloop : Diverges IBloop → ⊥
¬div-IBloop d = ¬div-IB0 (divergesSil refl d)

¬div-BN2 : Diverges (BN 2 []) → ⊥
¬div-BN2 d = BN2-no-τ (d .Diverges.step)

¬div-BNhold : ∀ x → Diverges (BN 2 (x ∷ [])) → ⊥
¬div-BNhold x d = BNhold-no-τ x (d .Diverges.step)

¬div-BNout : ∀ x y → Diverges (BN 2 (x ∷ y ∷ [])) → ⊥
¬div-BNout x y d = BNout-no-τ x y (d .Diverges.step)

------------------------------------------------------------------------------------
-- The relation:  IterBuff2 ↔ BN2 across the loop-back τ (four states).
data RelB : BProc → BProc → Set₁ where
  rB0    : RelB IB0 (BN 2 [])
  rBhold : ∀ x   → RelB (IBhold x)  (BN 2 (x ∷ []))
  rBout  : ∀ x y → RelB (IBout x y) (BN 2 (x ∷ y ∷ []))
  rBloop : RelB IBloop (BN 2 [])

------------------------------------------------------------------------------------
-- The four step-matching obligations + the two non-divergence obligations.
RB-fwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {p′} → RelB p q → p ─[ ev l ]─► p′
        → Σ[ q′ ∈ BProc ] ((q ═[ ev l ]═► q′) × RelB p′ q′)
RB-fwdE rB0 stp with IB0-ev stp
... | x , refl , refl = BN 2 (x ∷ []) , wev τ*-refl (bn-in x) τ*-refl , rBhold x
RB-fwdE (rBhold x) stp with IBhold-ev x stp
... | inj₁ (y , refl , refl) = BN 2 (x ∷ y ∷ []) , wev τ*-refl (bnhold-in x y) τ*-refl , rBout x y
... | inj₂ (refl , refl)     = BN 2 [] , wev τ*-refl (bnhold-out x) τ*-refl , rBloop
RB-fwdE (rBout x y) stp with IBout-ev x y stp
... | refl , refl = BN 2 (y ∷ []) , wev τ*-refl (bnout-out x y) τ*-refl , rBhold y
RB-fwdE rBloop stp = ⊥-elim (IBloop-no-ev stp)

RB-fwdT : ∀ {p q p′} → RelB p q → p ─[ τ ]─► p′
        → Σ[ q′ ∈ BProc ] ((q ═[ τ ]═► q′) × RelB p′ q′)
RB-fwdT rB0        stp = ⊥-elim (IB0-no-τ stp)
RB-fwdT (rBhold x) stp = ⊥-elim (IBhold-no-τ x stp)
RB-fwdT (rBout x y) stp = ⊥-elim (IBout-no-τ x y stp)
RB-fwdT rBloop     stp with IBloop-τ stp
... | refl = BN 2 [] , wτ τ*-refl , rB0

RB-bwdE : ∀ {p q} {l : Event√ (⊤poly {lzero})} {q′} → RelB p q → q ─[ ev l ]─► q′
        → Σ[ p′ ∈ BProc ] ((p ═[ ev l ]═► p′) × RelB p′ q′)
RB-bwdE rB0 stp with BN2-ev stp
... | x , refl , refl = IBhold x , wev τ*-refl (ib-in x) τ*-refl , rBhold x
RB-bwdE (rBhold x) stp with BNhold-ev x stp
... | inj₁ (y , refl , refl) = IBout x y , wev τ*-refl (ibhold-in x y) τ*-refl , rBout x y
... | inj₂ (refl , refl)     = IBloop , wev τ*-refl (ibhold-out x) τ*-refl , rBloop
RB-bwdE (rBout x y) stp with BNout-ev x y stp
... | refl , refl = IBhold y , wev τ*-refl (ibout-out x y) τ*-refl , rBhold y
RB-bwdE rBloop stp with BN2-ev stp
... | x , refl , refl =
      IBhold x , wev (τ*-step ib-loop τ*-refl) (ib-in x) τ*-refl , rBhold x

RB-bwdT : ∀ {p q q′} → RelB p q → q ─[ τ ]─► q′
        → Σ[ p′ ∈ BProc ] ((p ═[ τ ]═► p′) × RelB p′ q′)
RB-bwdT rB0        stp = ⊥-elim (BN2-no-τ stp)
RB-bwdT (rBhold x) stp = ⊥-elim (BNhold-no-τ x stp)
RB-bwdT (rBout x y) stp = ⊥-elim (BNout-no-τ x y stp)
RB-bwdT rBloop     stp = ⊥-elim (BN2-no-τ stp)

RB-ndivL : ∀ {p q} → RelB p q → Diverges p → ⊥
RB-ndivL rB0        = ¬div-IB0
RB-ndivL (rBhold x) = ¬div-IBhold x
RB-ndivL (rBout x y) = ¬div-IBout x y
RB-ndivL rBloop     = ¬div-IBloop

RB-ndivR : ∀ {p q} → RelB p q → Diverges q → ⊥
RB-ndivR rB0        = ¬div-BN2
RB-ndivR (rBhold x) = ¬div-BNhold x
RB-ndivR (rBout x y) = ¬div-BNout x y
RB-ndivR rBloop     = ¬div-BN2

------------------------------------------------------------------------------------
-- Assembly:  DRFromRel ⇒ ≈DR, then drbisim→≈FD ⇒ ≈FD.
module MCIB = DRFromRel RelB RB-fwdE RB-fwdT RB-bwdE RB-bwdT RB-ndivL RB-ndivR

iterbuff2-bn2-DR : IterBuff2 ≈DR BN2
iterbuff2-bn2-DR = MCIB.rel→dr rB0

iterbuff2-bn2 : IterBuff2 ≈FD BN2
iterbuff2-bn2 = drbisim→≈FD iterbuff2-bn2-DR
